<body>
    <form>
        <method="post" action="Serv"></method>
        <!-- Choisir la personne -->
        <Collection<Personne> personnes = request getAttributes("ListePersonnes")></Personne>
        for (Personne p : personnes) {
            int idp = p.getId();
            String np = p.getNom() + p.getPrenom(); 
        }
        <input type="radio" name="idpersonne" value=idp>np</input>
        <Collection<Adresse> adresses = request getAttributes("ListeAdresses")></Adresse>
        for (Adresse a: adresses) {
            int ida = a.getId();
            String rv = a.getRue() + a.getVille();
        }
        <input type="radio" name="idadresse" value=ida>rv</input>
        <input type="submit" value="ok"></input>
    </form>

</body>