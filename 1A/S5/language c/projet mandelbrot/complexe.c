#include "complexe.h"
#include <math.h>           // Pour certaines fonctions trigo notamment

// Implantations de reelle et imaginaire


double reelle(complexe_t c){
    return c.reelle;
}


double imaginaire(complexe_t c){
    return c.imaginaire;
}
// Implantations de set_reelle et set_imaginaire


void set_reelle(complexe_t* c, double reelle){
    c->reelle=reelle;
    
}


void set_imaginaire(complexe_t* c, double imaginaire ){
    c->imaginaire = imaginaire;
}

void init(complexe_t* c, double reelle,double imaginaire){
    set_reelle(c,reelle);
    set_imaginaire(c,imaginaire);
    
    
}

// Implantation de copie
void copie(complexe_t* resultat, complexe_t autre){
        resultat->reelle = autre.reelle;
        resultat->imaginaire = autre.imaginaire;
}

// Implantations des fonctions algébriques sur les complexes

void conjugue(complexe_t* resultat, complexe_t op){
    resultat->reelle = op.reelle;
    resultat->imaginaire = -op.imaginaire;
}
    

void ajouter(complexe_t* resultat, complexe_t gauche, complexe_t droite){
    resultat->imaginaire = gauche.imaginaire + droite.imaginaire;
    resultat->reelle = gauche.reelle + droite.reelle;      
}
    

void soustraire(complexe_t* resultat, complexe_t gauche, complexe_t droite){
    resultat->imaginaire = gauche.imaginaire - droite.imaginaire;
    resultat->reelle = gauche.reelle - droite.reelle;
}

void multiplier(complexe_t* resultat, complexe_t gauche, complexe_t droite){
    resultat->reelle = gauche.reelle * droite.reelle - gauche.imaginaire * droite.imaginaire;
    resultat->imaginaire = gauche.reelle * droite.imaginaire + gauche.imaginaire * droite.reelle;
}

void echelle(complexe_t* resultat, complexe_t op, double facteur){
    resultat->reelle = op.reelle * facteur;
    resultat -> imaginaire = op.imaginaire * facteur;
}


void puissance(complexe_t* resultat, complexe_t op, int exposant){
    if (exposant==0){
    init(resultat, 1,0);
    }
     else {  	
    resultat->reelle = op.reelle;
    resultat->imaginaire = op.imaginaire;
    
    for (int i=1; i<exposant;i++){
    	complexe_t temp = *resultat;
        multiplier(resultat,temp,op);
        }
    }
    
}

// Implantations du module et de l'argument

double module_carre( complexe_t op){
    return reelle(op) * reelle(op) + imaginaire(op) * imaginaire(op);
}

double module(complexe_t op){
    return sqrt( module_carre(op) );
    
    
}

double argument( complexe_t op){
    return acos( reelle(op) / module(op) );
    
    
}

