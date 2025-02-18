package pack;

import java.util.Collection;
import java.util.ArrayList;

public class Personne {
    String nom;
    String prenom;
    Collection<Adresse> adresses = new ArrayList<Adresse>();
    int id;



    public Personne(String nom, String prenom, Collection<Adresse> adresses, int id) {
        this.nom = nom;
        this.prenom = prenom;
        this.adresses = adresses;
        this.id = id;
    }





    public String getNom() {
        return nom;
    }

    public void setNom(String nom) {
        this.nom = nom;
    }


    public String getPrenom() {
        return prenom;
    }

    public void setPrenom(String prenom) {
        this.prenom = prenom;
    }


    public Collection<Adresse> getAdresses() {
        return adresses;
    }
    public void setAdresses(Collection<Adresse> adresse) {
        this.adresses = adresse;
    }





    public int getId() {
        return id;
    }





    public void setId(int id) {
        this.id = id;
    }

}