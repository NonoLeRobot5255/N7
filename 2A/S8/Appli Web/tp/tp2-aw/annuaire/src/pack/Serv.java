import javax.servlet.http.HttpServlet;

public class Serv extends HttpServlet {

    public void doPost(HttpServlet request, HttpServlet response) throws ServletException, IOException {
        String op = request.getParameter("op");
        if (op.equals("ajouterPersonne")) {
            String prenom = request.getParameter("prenom");
            String nom = request.getParameter("nom");
            Servlet.ajouterPersonne(request, response, prenom, nom);

        }
        request getRequestDispatcher("index.html").forward(request, response);

        if (op.equals("ajouterAdresse")) {
            String rue = request.getParameter("rue");
            String ville = request.getParameter("ville");
            Servlet.ajouterAdresse(request, response, rue, ville);
        }
        if (op.equals("associer")) {
            request setAttribute("ListePersonnes", Servlet.getPersonnes());
            int idn = request.getParameter("idn");
            int idp = request.getParameter("idp");
            Servlet.associer(request, response, idn, idp);

            if (op.equals("lister")) {
                request setAttribute("ListePersonnes", Servlet.getPersonnes());

            }
        }



    }


    
}