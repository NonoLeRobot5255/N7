<body>
    <form method="post" action="Serv">
        choisir la personne
        <%
        Collection<Personne> personnes = (Collection<Personne>) request.getAttribute("listePersonnes");
        if (personnes != null) {
            for (Personne p : personnes) {
                int idp = p.getId();
                String np = p.getNom() + " " + p.getPrenom();
        %>
                <input type="radio" name="idpersonne" value="<%= idp %>"> <%= np %><br>
        <%
            }
        }
        %>

        choisir l'adresse
        <%
        Collection<Adresse> adresses = (Collection<Adresse>) request.getAttribute("listeAdresses");
        if (adresses != null) {
            for (Adresse a : adresses) {
                int ida = a.getId();
                String rv = a.getRue() + " " + a.getVille();
        %>
                <input type="radio" name="idadresse" value="<%= ida %>"> <%= rv %><br>
        <%
            }
        }
        %>

        <input type="submit" value="ok">
        <input type="hidden" name="op" value="choix">
    </form>
</body>
