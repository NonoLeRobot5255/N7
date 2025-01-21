/**
 * @file virtio.c
 *
 * WARNING : on utilise ici en fait les spécifications v0.9.5,
 * qualifiées de "legacy" dans la v1.0. J'utiliserai autant que
 * possible des macros/variables du genre VIRTIO_HIST... pour faire la
 * différence chaque fois que possible. Attention !! Il y a des
 * petites différences entre la v0.9.5 et la version dite legacy dans
 * la v1 !! Apparemment une typo dans la v1 sur l'ordre des champs de
 * contrôle ...
 *
 * Sources intéressantes 
 *   [1] http://docs.oasis-open.org/virtio/virtio/v1.0/csprd01/virtio-v1.0-csprd01.html 
 *   [2] https://www.redhat.com/en/blog/virtqueues-and-virtio-ring-how-data-travels    
 *   [3] http://ozlabs.org/~rusty/virtio-spec/virtio-0.9.5.pdf
 */

#define min(a, b)   (((a)<(b))?(a):(b))

#include <manux/virtio.h>
#include <manux/debug.h>
#include <manux/memoire.h> // allouerPages
#include <manux/string.h>  // memcpy
#include <manux/i386.h>    // barriereMemoire
#include <manux/errno.h>
#include <manux/io.h>      // outb

static int nbFournis =0;
static int nbAcceptes =0;
static int nbRendus =0;

/**
 * Affichage de l état d'une file, à des fins de debug
 */
void virtioAfficherFile(VirtioFileVirtuelle * fv)
{
   printk("[7]File 0x%x (lg %d nxt %d), used idx %d, dispo idx %d fr %d %d/%d/%d\n",
		fv,
		fv->taille,
                fv->prochainDescripteur,
		fv->buffersUtilises->indice,
	  fv->buffersDisponibles->indice,
	  fv->nbDescripteursLibres,
	  nbFournis, nbAcceptes, nbRendus
	  );
   /*
   printk("[7]Desc [@/l f n] : [%llx %ld %d %d][%llx %ld %d %d][%llx %ld %d %d]\n",
		fv->tableDescripteurs[0].adresse,
		fv->tableDescripteurs[0].longueur,
		fv->tableDescripteurs[0].flags,
		fv->tableDescripteurs[0].suivant,
	  
		fv->tableDescripteurs[1].adresse,
		fv->tableDescripteurs[1].longueur,
		fv->tableDescripteurs[1].flags,
		fv->tableDescripteurs[1].suivant,
	  
		fv->tableDescripteurs[2].adresse,
		fv->tableDescripteurs[2].longueur,
		fv->tableDescripteurs[2].flags,
		fv->tableDescripteurs[2].suivant
		);
   printk("[7]Used fl 0x%x, idx %d (i/l) : [%d/%ld][%d/%ld][%d/%ld]\n",
		fv->buffersUtilises->flags,
		fv->buffersUtilises->indice,
		fv->buffersUtilises->elementsUtilises[0].indiceBuffer,
                fv->buffersUtilises->elementsUtilises[0].longueur, 
		fv->buffersUtilises->elementsUtilises[1].indiceBuffer,
                fv->buffersUtilises->elementsUtilises[1].longueur,
		fv->buffersUtilises->elementsUtilises[2].indiceBuffer,
		fv->buffersUtilises->elementsUtilises[2].longueur
		);
   printk("[7]Dispo fl 0x%x, idx %d (i) : [%d][%d][%d]\n",
		fv->buffersDisponibles->flags,
		fv->buffersDisponibles->indice,
		fv->buffersDisponibles->indicesDesBuffer[0],
		fv->buffersDisponibles->indicesDesBuffer[1],
		fv->buffersDisponibles->indicesDesBuffer[2]
		);
   */
}

/**
 * Création d'une file de communication.
 *
 * D'après [3] (section 2.3), une file est constituée d'une zone
 * mémoire contigüe contenant 
 *   . Une table des descripteurs de buffer (alignée sur une page)
 *   . Une structure de description des buffers disponibles
 *   . Une structure de description des buffers usagers (alignée sur
 * une page)
 * 
 * On va donc calculer la taille de chacune de ces deux parties
 * (alignées sur une page).
 */
int virtioCreerFileVirtuelle(VirtioFileVirtuelle * fileVirtuelle,
                             uint16_t tailleFile)
{
   uint32_t taillePartie1; // Buffers + disponibles
   uint32_t taillePartie2; // Utilisés
   uint32_t nbTotalPages;  // Combien de pages pour stocker ça ?
   char *   pointeur;      // Pour les allocations

   // La taille est fournie
   fileVirtuelle->taille = tailleFile;

   // Pour le moment, ils sont tous libres
   fileVirtuelle->nbDescripteursLibres = tailleFile;
   
   // La première partie est composée des descripteurs de buffer
   taillePartie1 = tailleFile * sizeof(VirtioDescripteurBuffer);

   // Suivis des descripteurs de buffers disponibles
   taillePartie1 += 3 * sizeof(uint16_t) + tailleFile * sizeof(uint16_t);

   // La seconde partie est composée des buffers utilisés
   taillePartie2 =  3 * sizeof(uint16_t) + tailleFile * sizeof(VirtioElementUtilise);

   // Combien faut-il de pages avec les contraintes d'alignement ?
   nbTotalPages = NB_PAGES(taillePartie1) + NB_PAGES(taillePartie2);

   // Allocation des pages nécessaires
   pointeur = allouerPages(nbTotalPages);

   // En cas d'échec, on remonte l'erreur
   if (pointeur == NULL) {
      return ENOMEM;
   }

   // La spécification insiste sur une initialisation à 0
   memset(pointeur, 0, nbTotalPages * MANUX_TAILLE_PAGE);
   
   // On peut enfin initialiser les pointeurs
   fileVirtuelle->tableDescripteurs = (VirtioDescripteurBuffer *)pointeur;

   // Les buffers disponibles sont collés derrière le dernier buffer
   fileVirtuelle->buffersDisponibles =
     (VirtioBufferDisponible *)&(fileVirtuelle->tableDescripteurs[tailleFile]);

   // Les buffers utilisés sont au début de la page suivante
   fileVirtuelle->buffersUtilises =
     (VirtioBufferUtilise*) (pointeur + NB_PAGES(taillePartie1) * MANUX_TAILLE_PAGE);

   fileVirtuelle->prochainDescripteur = 0;

   // Pour savoir où on en est des récupérations de buffer
   fileVirtuelle->dernierIndiceUtilise = 0;

   printk_debug(DBG_KERNEL_VIRTIO, "%d elts, %d+%d octets, %d pages, desc=0x%x, dis=0x%x, uti=0x%x,\n",
		tailleFile,
		taillePartie1,
		taillePartie2,
		nbTotalPages,
		fileVirtuelle->tableDescripteurs,
		fileVirtuelle->buffersDisponibles,
		fileVirtuelle->buffersUtilises);

   return ESUCCES;
}

/**
 * Initialisation d'un périphérique de type virtio accédé en PCI.
 * L'essentiel de ce qui suit est conforme à la v0.9.5 a priori,
 * (voir [3] section 2.2.1), mais pas à la v1.0
 *
 * @param vp      pointeur sur une structure déjà allouée (ou statique)
 * @param PCINum  l'identifiant PCI
 * @param masque  les caractéristiques à *ne pas* utiliser
 */
int virtioInitPeripheriquePCI(VirtioPeripherique * vp,
	                      int PCINum,
		              uint32_t masque)
{
   uint16_t adresseES;  // L'adresse d'E/S pour dialoguer avec lui
   uint16_t tailleFile; // Pour lire les tailles de files virtio
   uint8_t  etat;       // Etat du périphérique   
   int      numFile;    // Pour boucler sur les files
   
   printk_debug(DBG_KERNEL_VIRTIO, "IN\n");

   // On va chercher un pointeur vers la description PCI
   vp->pciEquipement = PCIEquipementNumero(PCINum);

   // Un raccourci sur l'adresse pour alléger le code
   adresseES = vp->pciEquipement->adresseES;

   // On reset le périphérique  (1)
   outb((uint16_t)(adresseES + VIRTIO_HIST_ETAT), (uint8_t)VIRTIO_RESET);
   
   // On lui dit qu'on l'a vu (2)
   outb((uint16_t)(adresseES + VIRTIO_HIST_ETAT), (uint8_t)VIRTIO_ACKNOWLEDGE);
   
   // On lui dit qu'on va le gérer (3)
   outb((uint16_t)(adresseES + VIRTIO_HIST_ETAT), (uint16_t)VIRTIO_ACKNOWLEDGE|VIRTIO_DRIVER);

   // Lecture de ses caractéristiques (4)
   inl((uint16_t)(adresseES + VIRTIO_HIST_CAPA_EQUIP), vp->caracteristiques);

   // Un petit message de debug
   printk_debug(DBG_KERNEL_VIRTIO, "Caract : 0x%x\n",
		vp->caracteristiques);

   // C'est donc la phase de "négociation", on va supprimer ce qu'on
   // ne sait pas gérer
   masque |= VIRTIO_F_RING_EVENT_IDX
          | VIRTIO_F_RING_INDIRECT_DESC
     ;
   printk_debug(DBG_KERNEL_VIRTIO, "Masque : 0x%x\n",
		masque);
   
   // On désélectionne les caractéristiques qui ne nous intéressent pas
   vp->caracteristiques &= ~masque ;

   printk_debug(DBG_KERNEL_VIRTIO, "Caract : 0x%x\n",
		vp->caracteristiques);

   // Négociation de ces caractéristiques (5)
   outl((uint16_t)(adresseES + VIRTIO_HIST_CAPA_PILOTE), vp->caracteristiques);

   // On acte définitivement ces caractéristiques
   outb((uint16_t)(adresseES + VIRTIO_HIST_ETAT),
	(uint8_t)VIRTIO_ACKNOWLEDGE | VIRTIO_DRIVER | VIRTIO_FEATURES_OK);

   // On vérifie qu'il est OK (6)
   inb((uint16_t)(adresseES + VIRTIO_HIST_ETAT), etat);

   if ((etat & VIRTIO_FEATURES_OK) == 0) {
      printk(PRINTK_ERREUR, "Le device virtio net refuse les caract. !\n");
      return EINVAL;
   }
   printk_debug(DBG_KERNEL_VIRTIO, "Les files\n");

   // Construction des files (7) comme décrit dans [3] section 2.3
   for (numFile = 0 ; numFile < MANUX_VIRTIO_NB_MAX_FILES; numFile++) {
      printk_debug(DBG_KERNEL_VIRTIO, "Creation file %d : \n", numFile);

      // Lecture de la taille (1)(2)
      outw((uint16_t)(adresseES + VIRTIO_HIST_FILE_SEL), numFile);
      inw((uint16_t)(adresseES + VIRTIO_HIST_TAILLE_FILE), tailleFile);
      printk_debug(DBG_KERNEL_VIRTIO, "   . Taille : %d\n", tailleFile);

      if (tailleFile) {
         // Création des fameuses files (3)
         virtioCreerFileVirtuelle(&(vp->filesVirtuelles[numFile]),   
	                          tailleFile);
         printk_debug(DBG_KERNEL_VIRTIO, "   . Creation ok\n");

         // On donne l'adresse à l'équipement (3)
         outw((uint16_t)(adresseES + VIRTIO_HIST_FILE_SEL), numFile);
         outl((uint16_t)(adresseES + VIRTIO_HIST_ADDRESS_FILE),
         ((uint32_t)vp->filesVirtuelles[numFile].tableDescripteurs)/MANUX_TAILLE_PAGE);
         printk_debug(DBG_KERNEL_VIRTIO, "   . @     %d\n",
		      ((uint32_t)vp->filesVirtuelles[numFile].tableDescripteurs)/MANUX_TAILLE_PAGE);
      }     
   }
   printk_debug(DBG_KERNEL_VIRTIO, "voila\n");
   
   // On dit au périphérique qu'on est bon, ...
   outb((uint16_t)(adresseES + VIRTIO_HIST_ETAT),
	VIRTIO_ACKNOWLEDGE
	| VIRTIO_DRIVER
	| VIRTIO_FEATURES_OK
	| VIRTIO_DRIVER_OK);

   printk_debug(DBG_KERNEL_VIRTIO, "OUT\n");

   return ESUCCES;
}

/**
 * @brief Fourniture d'un buffer au périphérique.
 *
 * @param vp   le périphérique concerné
 * @param id   numéro de la file sur le périphérique
 * @param bu   le buffer (pointeur sur les données/la place)
 * @param lg   la taille du buffer
 * @param fl   lecture/écriture (VRING_DESC_F_WRITE ou 0)
 *
 */
int virtioFournirBuffer(VirtioPeripherique * vp,
                        uint16_t id,
                        void * bu, int lg,
                        uint16_t fl)
{
   return virtioFournirBuffers(vp, id, &bu, &lg, 1, fl);
}

/**
 * @brief Fournir plusieurs buffers au périphérique.
 *
 * @param vp   le périphérique virtio concerné
 * @param id   index de la file
 * @param bu   les buffers (tableau de pointeurs sur les données/la place)
 * @param lg   la taille des buffers
 * @param nb   le nombre de buffers
 * @param fl   lecture/écriture (VRING_DESC_F_WRITE ou 0)
 * @return     le nombre de buffers réellement fournis
 * 
 * L'idée est de fournir une chaîne de buffers . WARNING pas d'erreur gérée !
 */
int virtioFournirBuffers(VirtioPeripherique * vp,
                         uint16_t id,
			 void * bu[], int lg[], int nb,
			 uint16_t fl)
{
   int                       n;
   VirtioFileVirtuelle     * fv = &(vp->filesVirtuelles[id]);
   VirtioDescripteurBuffer * vb;
   int                       prochainDesc = fv->prochainDescripteur;
   uint32_t                  ad;
   
   nbFournis+=nb;
   
   for (n = 0 ; (n < nb) && (fv->nbDescripteursLibres); n++) {
      // On va chercher un descripteur de buffer (2.4.1.1 (a))
      // on sait qu'il en reste puisqu'on les compte
      vb = &(fv->tableDescripteurs[(prochainDesc + n)%fv->taille]);

      //      printk("[7](0x%x) ", vb);
      
      // L'adresse des données (2.4.1.1 (b))
      ad = (uint32_t)bu[n];
      vb->adresse = (uint64_t)ad;
      
      // La longueur des données (2.4.1.1 (c))
      vb->longueur = lg[n]; 
   
      // On l'initialise en lecture/écriture (2.4.1.1 (d))
      vb->flags = fl;

      // On chaîne (2.4.1.1 (e))
      if ((n < nb -1) && (fv->nbDescripteursLibres > 1)) {
         vb->flags |= VRING_DESC_F_NEXT;
         vb->suivant = (fv->prochainDescripteur + n + 1)%fv->taille;
      } else {
         vb->suivant = 0;
      }
      
      // On le met dans les disponibles (2.4.1.2)
      if (n == 0) {   // WARNING pour moi il y a doute ici !
         fv->buffersDisponibles->indicesDesBuffer
           [(fv->buffersDisponibles->indice+n)%fv->taille] =
            prochainDesc;
      }

      // Un de moins qui soit disponible
      fv->nbDescripteursLibres--;
   }

   if (n == 0) {
     //printk("[7]x");
      return n;
   }
   
   barriereMemoire();  // WARNING, c'est là ?

   // On incremente le nombre de dispo (2.4.1.3)
   fv->buffersDisponibles->indice = fv->buffersDisponibles->indice + 1;

   // On a utilisé n buffers
   fv->prochainDescripteur = (fv->prochainDescripteur + n) % fv->taille;
   
   barriereMemoire();
   
   // On prévient l'équipement
   outw((uint16_t)(vp->pciEquipement->adresseES + VIRTIO_HIST_FILE_NOTIF), id);
   nbAcceptes += n;
   
   return n;
}

/**
 * @brief on va récupérer des buffers
 * 
 * @return Le nombre de pointeurs initialisés
 *
 * Voir [3] section 2.4.2 "Receiving Used Buffers From The Device"
 *
 * On fait au plus simple : on renvoie un(e chaîne de) buffer(s) tel
 * que fourni par le périphérique.
 */
int virtioFileRecupererBuffers(VirtioFileVirtuelle * fv,
			       void * bu[], int lg[], int nb)
{
   uint16_t indiceBuffer;
   uint32_t longueur;     // du buffer en cours de traitement
   int      result = 0;
   int      finDeChaine;
   uint32_t ad;

   // Ai-je vraiment des choses à récupérer ?
   if (fv->dernierIndiceUtilise == fv->buffersUtilises->indice) {
      return result;
   }

   while ((fv->dernierIndiceUtilise != fv->buffersUtilises->indice) && (result < nb)) {
      // Récupération de l'indice du descripteur libéré
      indiceBuffer = fv->buffersUtilises->elementsUtilises
	                      [fv->dernierIndiceUtilise % fv->taille].indiceBuffer;
      do {
         // On récupère les données et leur longueur
         longueur = fv->tableDescripteurs[indiceBuffer].longueur;
         ad = (uint32_t)fv->tableDescripteurs[indiceBuffer].adresse;
         bu[result] = (void *) ad;
	 lg[result] = longueur; 

	 result++;  // Ca en fait un de plus !

	 // Cela peut être le premier d'une chaîne
	 finDeChaine = !(fv->tableDescripteurs[indiceBuffer].flags & VRING_DESC_F_NEXT);
	 indiceBuffer = fv->tableDescripteurs[indiceBuffer].suivant;

	 // On continue tant qu'il y en a et qu'on a de la place pour
	 // les fournir
      } while ((result < nb)
	       && (!finDeChaine));
      if (!finDeChaine) {
	printk("[7] Ca pue du cul !\n");
      } else {
	//	printk("[7] Ouf !\n");
      }
      // On vient de traiter un buffer (peut-être une chaîne)
      fv->dernierIndiceUtilise++;  
   }
   // On a donc récupérer result descripteurs
   fv->nbDescripteursLibres += result;
   nbRendus += result;

   //   virtioAfficherFile(fv);
   //printk("[7] f %d, a %d, r %d\n", nbFournis, nbAcceptes, nbRendus);
   return result;
}

void virtioFileInterdireInterruption(VirtioFileVirtuelle * fv)
{
  //  fv->buffersUtilises->flags = 1;
  fv->buffersDisponibles->flags = 1;
}

void virtioFileAutoriserInterruption(VirtioFileVirtuelle * fv)
{
  fv->buffersUtilises->flags = 0;
  fv->buffersDisponibles->flags = 0;
}
