#ifndef COMPLEX_H
#define COMPLEX_H

// Type utilisateur complexe_t
struct complexe_t{
   double reelle;
   double imaginaire;
};

typedef struct complexe_t complexe_t;


// Fonctions reelle et imaginaire
/**
 * reelle
 * renvoie la partie reelle d'un nombre imaginaire
 *
 * precondition:
 * aucune 
 *
 * postcondition : 
 * retourn la partie reel
 */
double reelle(complexe_t c);

/**
 * imaginaire
 * renvoie la partie imaginaire d'un nombre imaginaire
 *
 * precondition:
 * aucune 
 *
 * postcondition : 
 * retourn la partie reel
 */
double imaginaire(complexe_t c);

// Procédures set_reelle, set_imaginaire et init
/**
 * set_reelle
 * change la partie relle d'un nombre complexe
 * 
 * paramètres : 
 *	-c      [in out] Complexe dans lequel copier la composante
 * precondition : 
 * c non nul
 *
 * postcondition : 
 * reelle(c)==reelle
 */
void set_reelle(complexe_t* c, double reelle);

/**
 * set_imaginaire
 * change la partie imaginaire d'un nombre complexe
 * 
 * paramètres : 
 *	-c      [in out] Complexe dans lequel copier la composante
 * precondition : 
 * c non nul
 *
 * postcondition : 
 * imaginaire(c)==reelle
 */
void set_imaginaire(complexe_t* c, double reelle );

/**
 * init
 * change la partie imaginaire et reelle d'un nombre complexe
 * 
 * paramètres : 
 *	-c      [in out] Complexe dans lequel copier la composante
 * precondition : 
 * c non nul
 *
 * postcondition : 
 * imaginaire(c)==imaginaire
 * reelle(c)==reelle
 */
void init(complexe_t* c,double relle,double imaginaire);

// Procédure copie
/**
 * copie
 * Copie les composantes du complexe donné en second argument dans celles du premier
 * argument
 *
 * Paramètres :
 *   resultat       [out] Complexe dans lequel copier les composantes
 *   autre          [in]  Complexe à copier
 *
 * Pré-conditions : resultat non null
 * Post-conditions : resultat et autre ont les mêmes composantes
 */
void copie(complexe_t* resultat, complexe_t autre);

// Algèbre des nombres complexes
/**
 * conjugue
 * Calcule le conjugué du nombre complexe op et le sotocke dans resultat.
 *
 * Paramètres :
 *   resultat       [out] Résultat de l'opération
 *   op             [in]  Complexe dont on veut le conjugué
 *
 * Pré-conditions : resultat non-null
 * Post-conditions : reelle(*resultat) = reelle(op), complexe(*resultat) = - complexe(op)
 */
void conjugue(complexe_t* resultat, complexe_t op);

/**
 * ajouter
 * Réalise l'addition des deux nombres complexes gauche et droite et stocke le résultat
 * dans resultat.
 *
 * Paramètres :
 *   resultat       [out] Résultat de l'opération
 *   gauche         [in]  Opérande gauche
 *   droite         [in]  Opérande droite
 *
 * Pré-conditions : resultat non-null
 * Post-conditions : *resultat = gauche + droite
 */
void ajouter(complexe_t* resultat, complexe_t gauche, complexe_t droite);

/**
 * soustraire
 * Réalise la soustraction des deux nombres complexes gauche et droite et stocke le résultat
 * dans resultat.
 *
 * Paramètres :
 *   resultat       [out] Résultat de l'opération
 *   gauche         [in]  Opérande gauche
 *   droite         [in]  Opérande droite
 *
 * Pré-conditions : resultat non-null
 * Post-conditions : *resultat = gauche - droite
 */
void soustraire(complexe_t* resultat, complexe_t gauche, complexe_t droite);

/**
 * multiplier
 * Réalise le produit des deux nombres complexes gauche et droite et stocke le résultat
 * dans resultat.
 *
 * Paramètres :
 *   resultat       [out] Résultat de l'opération
 *   gauche         [in]  Opérande gauche
 *   droite         [in]  Opérande droite
 *
 * Pré-conditions : resultat non-null
 * Post-conditions : *resultat = gauche * droite
 */
void multiplier(complexe_t* resultat, complexe_t gauche, complexe_t droite);

/**
 * echelle
 * Calcule la mise à l'échelle d'un nombre complexe avec le nombre réel donné (multiplication
 * de op par le facteur réel facteur).
 *
 * Paramètres :
 *   resultat       [out] Résultat de l'opération
 *   op             [in]  Complexe à mettre à l'échelle
 *   facteur        [in]  Nombre réel à multiplier
 *
 * Pré-conditions : resultat non-null
 * Post-conditions : *resultat = op * facteur
 */
void echelle(complexe_t* resultat, complexe_t op, double facteur);

/**
 * puissance
 * Calcule la puissance entière du complexe donné et stocke le résultat dans resultat.
 *
 * Paramètres :
 *   resultat       [out] Résultat de l'opération
 *   op             [in]  Complexe dont on veut la puissance
 *   exposant       [in]  Exposant de la puissance
 *
 * Pré-conditions : resultat non-null, exposant >= 0
 * Post-conditions : *resultat = op * op * ... * op
 *                                 { n fois }
 */
void puissance(complexe_t* resultat, complexe_t op, int exposant);

// Module et argument
/**
 * module_carre
 * calcul du module caré d'un complexe 
 *
 * paramètres :  
 *   op   [in out] Résultat de l'opération et complexe à faire le module au carré
 *
 * précondition : 
 * op/=0
 *
 * postcondition : 
 * res == reelle(op)²+imaginaire(op)²
 *
 */
double module_carre(complexe_t op);

/**
 * module
 * calcule du module d'un nombre complexe 
 *    
 * paramètres :
 *      op   [in out] Résultat de l'opération et complexe à faire le module 
 *
 * precondition : 
 * op /= 0 
 *
 * postcondition : 
 * res == sqrt(module_carre(op))
 *
 */
double module(complexe_t op);

/**
 * argument
 * retourne l'argument (l'angle avec l'axe des reelles) d'un nombre complexe.
 *
 * paramètres : 
 * op [in] complexe dont on veut l'argument 
 *
 * précondition : 
 * op /= 0
 *
 * postcondition : 
 * res == acos( reelle(op) / module(op) )
 * 
 */
double argument( complexe_t op);


#endif // COMPLEXE_H



