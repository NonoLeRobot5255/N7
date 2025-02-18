package pack;

import java.util.HashMap;
import java.util.Collection;


public class Facade{
	int indexP = 0;
	int indexA = 0;
	public int getIndexP() {
        return indexP;
    }
    public void setIndexP(int indexP) {
        this.indexP = indexP;
    }
    public int getIndexA() {
        return indexA;
    }
    public void setIndexA(int indexA) {
        this.indexA = indexA;
    }
    public HashMap<Integer, Personne> getPersonnes() {
        return personnes;
    }
    public void setPersonnes(HashMap<Integer, Personne> personnes) {
        this.personnes = personnes;
    }
    public HashMap<Integer, Adresse> getAdresses() {
        return adresses;
    }
    public void setAdresses(HashMap<Integer, Adresse> adresses) {
        this.adresses = adresses;
    }

    HashMap<Integer, Personne> personnes = new HashMap<Integer, Personne> ( );
	HashMap<Integer, Adresse> adresses = new HashMap<Integer, Adresse> ( );

	public void ajouterPersonne(String nom, String prenom){
		Personne p=new Personne( );
		p.setId(indexP);
		p.setNom(nom);
		p.setPrenom(prenom);
		personnes.put(indexP, p);
		indexP ++;
	}
    public void ajouterAdresse(String rue, String ville){
        Adresse a=new Adresse( );
        a.setId(indexA);
        a.setRue(rue);
        a.setVille(ville);
        adresses.put(indexA, a);
        indexA ++;
    }
	public Collection<Personne> ListePersonne(){
		return personnes.values();
	}

	public Collection<Adresse> ListeAdresse(){
		return adresses.values();
	}

	public void associer(int idp, int ida){
		Personne p = personnes.get(idp);
		p.adresses.add(adresses.get(ida));
	}
}
