<body>
    <%
    // Récupération de la liste des personnes
    Collection<Personne> personnes = (Collection<Personne>) request.getAttribute("ListePersonnes");

    // Vérification que la liste n'est pas vide
    if (personnes != null) {
        for (Personne p : personnes) {
            out.println(p.getNom() + " " + p.getPrenom() + "<br>");

            // Vérification des adresses associées à la personne
            Collection<Adresse> adresses = p.getAdresses();
            if (adresses != null) {
                for (Adresse a : adresses) {
                    out.println("&nbsp;&nbsp;Adresse : " + a.getRue() + " " + a.getVille() + "<br>");
                }
            }
        }
    } else {
        out.println("Aucune personne trouvée.");
    }
    %>
</body>
