package pack;

import java.util.HashMap;

public class Facade {
    int indexP = 0;
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
    int indexA = 0;

    HashMap<Integer, Personne> personnes = new HashMap<Integer, Personne>();
    HashMap<Integer, Adresse> adresses = new HashMap<Integer, Adresse>();
    
}
