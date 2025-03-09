package pack;

import java.util.Collection;
import java.util.HashMap;

public class Facade {
	
	int indexP = 0;
	int indexA = 0;
	HashMap<Integer,Personne> personnes = new HashMap<Integer,Personne>();
	HashMap<Integer,Adresse> adresses = new HashMap<Integer,Adresse>();

	public void ajoutPersonne(String nom, String prenom) {
		Personne p = new Personne();
		p.setId(indexP++);
		p.setNom(nom);
		p.setPrenom(prenom);
		personnes.put(p.getId(), p);
	}
	
	public void ajoutAdresse(String rue, String ville) {
		Adresse a = new Adresse();
		a.setId(indexA++);
		a.setRue(rue);
		a.setVille(ville);
		adresses.put(a.getId(), a);
	}
		
	public Collection<Personne> listePersonnes() {
		return personnes.values();
	}
	
	public Collection<Adresse> listeAdresses() {
		return adresses.values();
	}
	
	public void associer(int personneId, int adresseId) {
		Personne p = personnes.get(personneId);
		Adresse a = adresses.get(adresseId);
		p.getAdresses().add(a);
	}
	
}
