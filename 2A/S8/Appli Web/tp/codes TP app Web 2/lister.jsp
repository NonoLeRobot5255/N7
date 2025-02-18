<body>
    <Collection<Personnes> personnes = request getAttribute("ListePersonnes");
        for (Personne p : personnes) {
            out.println(p.getNom() + " " + p.getPrenom());
        
            for (Adresse a : p.getAdresses()) {
                out.println(a.getRue() + " " + a.getVille());
                out.println(" || " + a.getRue() + " " + a.getVille());
            }
        }
    </Personnes>
</body>