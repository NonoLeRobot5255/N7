/*----------------------------------------------------------------------------*/
/*      Implantation des fichiers de Manux.                                   */
/*                                                                            */
/*                                                  (C) Manu Chaput 2002-2023 */
/*----------------------------------------------------------------------------*/
#include <manux/fichier.h>
#include <manux/debug.h>
#include <manux/string.h>       // bcopy
#include <manux/scheduler.h>    // tacheEnCours
#include <manux/errno.h>
#ifdef MANUX_KMALLOC
#   include <manux/kmalloc.h>
#endif

#define MANUX_DEBUG_FS_BASE

/**
 * @brief Lecture dans un fichier
 * @param f le fichier doit être != NULL
 */
int fichierLire(Fichier * f, void * buffer, int nbOctets)
{
   int result = -EBADF;

   if (f->fanions & O_RDONLY) {
      printk_debug(DBG_KERNEL_SYSFI, "on invoque 0x%x\n", f->iNoeud->methodesFichier->lire);
   
      // On invoque la méthode associée
      result = f->iNoeud->methodesFichier->lire(f, buffer, nbOctets);
   }
   
   printk_debug(DBG_KERNEL_SYSFI, "on renvoie %d\n", result);

   return result;
}

int fichierEcrire(Fichier * f, void * buffer, int nbOctets)
{
   int result = -EBADF;

   if (f->fanions & O_WRONLY) {
      printk_debug(DBG_KERNEL_SYSFI, "on invoque 0x%x\n", f->iNoeud->methodesFichier->ecrire);

      // On invoque la méthode associée
      result = f->iNoeud->methodesFichier->ecrire(f, buffer, nbOctets);
   }
   printk_debug(DBG_KERNEL_SYSFI, "on renvoie %d\n", result);
   
   return result;
}

#ifdef MANUX_APPELS_SYSTEME
/**
 * @brief L'appel système permettant de fermer un fichier ouvert
 */
int sys_fermer(ParametreAS as, int fd)
{
   Fichier * f;
   int result = EBADF;

   printk_debug(DBG_KERNEL_SYSFI, "in\n");
   
   if (tacheEnCours == NULL) {
      printk_debug(DBG_KERNEL_SYSFI, "pas de tache en cours !\n");
      result = EINVAL;
   } else if (tacheEnCours->fichiers[fd] == NULL) {
      printk_debug(DBG_KERNEL_SYSFI, "pas de fichier %d !\n", fd);
      result = EPASDEF;
   } else {
      f = tacheEnCours->fichiers[fd]; 
      result = fichierFermer(f);

      // WARNING : libérer l'emplacement dans les fichiers de la tâche
   }
   
   return result;
   
}

int sys_ecrire(ParametreAS as, int fd, void * buffer, int nbOctets)
{
   Fichier * f;
   int result;

   printk_debug(DBG_KERNEL_SYSFI, "sys_ecrire fd = %d, b = %d, nb = %d IN\n", fd, buffer, nbOctets);

   if (tacheEnCours == NULL) {
      printk_debug(DBG_KERNEL_SYSFI, "pas de tache en cours !\n");
      result = -EINVAL;
   } else if (tacheEnCours->fichiers[fd] == NULL) {
      printk_debug(DBG_KERNEL_SYSFI, "pas de fichier %d !\n", fd);
      result = -EPASDEF;
   } else {
      f = tacheEnCours->fichiers[fd]; 
      printk_debug(DBG_KERNEL_SYSFI, "sys_ecrire : fd=%d, file=%x\n", fd, f);
      result = fichierEcrire(f, buffer, nbOctets);
      printk_debug(DBG_KERNEL_SYSFI, "sys_ecrire : res = %d\n", result);
   }
   
   return result;
}

int sys_lire(ParametreAS as, int fd, void * buffer, int nbOctets)
{
   Fichier * f;
   int result;

   printk_debug(DBG_KERNEL_SYSFI, "sys_lire fd = %d, b = %d, nb = %d IN\n", fd, buffer, nbOctets);

   if (tacheEnCours == NULL) {
      printk_debug(DBG_KERNEL_SYSFI, "pas de tache en cours !\n");
      result = -EINVAL;
   } else if (tacheEnCours->fichiers[fd] == NULL) {
      printk_debug(DBG_KERNEL_SYSFI, "pas de fichier %d !\n", fd);
      result = -EPASDEF;
   } else {
      f = tacheEnCours->fichiers[fd]; 
      printk_debug(DBG_KERNEL_SYSFI, "sys_lire : fd=%d, file=%x\n", fd, f);
      result = fichierLire(f, buffer, nbOctets);
      printk_debug(DBG_KERNEL_SYSFI, "sys_lire : res = %d\n", result);
   }
   
   return result;
}
#endif //MANUX_APPELS_SYSTEME

void sfInitialiser()
{
#ifdef MANUX_APPELS_SYSTEME
   definirAppelSysteme(NBAS_FERMER, sys_fermer);
   definirAppelSysteme(NBAS_ECRIRE, sys_ecrire);
   definirAppelSysteme(NBAS_LIRE, sys_lire);
#endif
}

/**
 * @brief : Ouverture d'un fichier. 
 * @param iNoeud : le noeud à ouvrir (in)
 * @param f : le fichier ouvert (out)
 *
 * On utilise la fonction d'ouverture du type de périphérique correspondant
 */
int fichierOuvrir(INoeud * iNoeud, Fichier * f, uint16_t fanions, uint16_t mode)
{
   int result = ESUCCES;
  
   printk_debug(DBG_KERNEL_SYSFI, "IN");

   // WARNING, plein de précautions à prendre !

   f->iNoeud = iNoeud;
   f->fanions = fanions;
   f->mode = mode;

   if (iNoeud->methodesFichier->ouvrir) {
      result = iNoeud->methodesFichier->ouvrir(iNoeud, f, fanions, mode);
   }

   //printk_debug(DBG_KERNEL_SYSFI, "OUT");
   return result;
}

/**
 * @brief Fermeture d'un fichier
 */
int fichierFermer(Fichier * f)
{
   int result = EBADF;
  
   printk_debug(DBG_KERNEL_SYSFI, "IN");

   if (f->iNoeud->methodesFichier->fermer) {
      result = f->iNoeud->methodesFichier->fermer(f);
   }

   //printk_debug(DBG_KERNEL_SYSFI, "OUT");
   return result;
}

#ifdef MANUX_KMALLOC
/**
 * @brief Copie d'un fichier ouvert
 * 
 * Par exemple pour faire hériter un processus fils, ou pour un appel
 * de type dup 
 */
Fichier * fichierDupliquer(Fichier * f)
{
   int res;
   Fichier * result;

   result = kmalloc(sizeof(Fichier));

   if (result == NULL) {
      paniqueNoyau("Plus de memoire !\n");
   } else {
      // On fait une coie simple, ...
      bcopy(f, result, sizeof(Fichier));

      // ... et on invoque la méthdode d'ouverture, si elle a des
      // décomptes à faire, par exemple
      if (f->iNoeud->methodesFichier->ouvrir != NULL) {
 	 res = f->iNoeud->methodesFichier->ouvrir(f->iNoeud, result, f->fanions, f->mode);
	 if (res != ESUCCES) {
            kfree(result);
 	    result = NULL;
	 }
      }
   }
   
   return result;
}

/**
 * @brief : création et ouverture d'un fichier
 */
Fichier * fichierCreer(INoeud * iNoeud, uint16_t fanions, uint16_t mode)
{
   Fichier * result = kmalloc(sizeof(Fichier));

   //   printk_debug(DBG_KERNEL_SYSFI, "IN");
   if (fichierOuvrir(iNoeud, result, fanions, mode) == ESUCCES) {
      return result;
   } else {
      kfree(result);
      return NULL;
   }
}
#endif // MANUX_KMALLOC
