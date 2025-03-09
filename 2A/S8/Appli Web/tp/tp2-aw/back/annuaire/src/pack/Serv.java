package pack;

import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;

import java.io.IOException;

@WebServlet("/Serv")
public class Serv extends HttpServlet {
    private final Facade facade = new Facade();
    
    public void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        String op = request.getParameter("op");

        if (op.equals("ajoutPersonne")) {
            String nom = request.getParameter("nom");
            String prenom = request.getParameter("prenom");

            facade.ajouterPersonne(nom, prenom);

            request.getRequestDispatcher("index.html").forward(request, response);
            return;
        }

        if (op.equals("ajoutAdresse")) {
            String rue = request.getParameter("rue");
            String ville = request.getParameter("ville");

            facade.ajouterAdresse(rue, ville);

            request.getRequestDispatcher("index.html").forward(request, response);
            return;
        }

        if (op.equals("choix")) {
            request.setAttribute("listePersonnes", facade.getPersonnes());
            request.setAttribute("listeAdresses", facade.getAdresses());
            request.getRequestDispatcher("associer.jsp").forward(request, response);
        }

        
    }
    
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        String op = request.getParameter("op");
        if (op.equals("lister")) {
            request.setAttribute("lister", facade.getPersonnes());
            request.getRequestDispatcher("lister.jsp").forward(request, response);
        }

        if (op.equals("associer")) {
            int ida = Integer.parseInt(request.getParameter("ida"));
            int idp = Integer.parseInt(request.getParameter("idp"));

            facade.associer(idp, ida);

            request.getRequestDispatcher("index.html").forward(request, response);
        }   
    }
}
