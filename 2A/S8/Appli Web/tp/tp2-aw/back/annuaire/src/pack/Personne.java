package pack;

import java.util.ArrayList;
import java.util.Collection;

public class Personne {
	String nom;
	String prenom;
	Collection <Adresse> adresses = new ArrayList<>( );
	int id;

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

    public int getId() {
        return id;
    }

    public void setId(int id) {
        this.id = id;
    }

    public Collection<Adresse> getAdresses( ){
		return adresses;
	}

	public void setAdresses(Collection <Adresse> a){
	adresses = a;
	}

}