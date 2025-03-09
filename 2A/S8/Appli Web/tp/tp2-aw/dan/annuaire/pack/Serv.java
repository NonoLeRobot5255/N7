package pack;

import java.io.IOException;

import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;

/**
 * Servlet implementation class Serv
 */
@WebServlet("/Serv")
public class Serv extends HttpServlet {
	private static final long serialVersionUID = 1L;
       
	Facade facade = new Facade();
	
    /**
     * @see HttpServlet#HttpServlet()
     */
    public Serv() {
        super();
    }

	protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
		doPost(request,response);
	}

	
	protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {

		String op =  request.getParameter("op");
		
		if (op.equals("ajoutpersonne")) {
			String nom = request.getParameter("nom");
			String prenom = request.getParameter("prenom");
			facade.ajoutPersonne(nom, prenom);
			request.getRequestDispatcher("index.html").forward(request, response);
		}
		if (op.equals("ajoutadresse")) {
			String rue = request.getParameter("rue");
			String ville = request.getParameter("ville");
			facade.ajoutAdresse(rue, ville);
			request.getRequestDispatcher("index.html").forward(request, response);
		}
		if (op.equals("associer")) {
			request.setAttribute("listepersonnes", facade.listePersonnes());
			request.setAttribute("listeadresses", facade.listeAdresses());
			request.getRequestDispatcher("choix.jsp").forward(request, response);
		}
		if (op.equals("choix")) {
			String idpersonne = request.getParameter("idpersonne");
			String idadresse = request.getParameter("idadresse");
			facade.associer(Integer.parseInt(idpersonne), Integer.parseInt(idadresse));
			request.getRequestDispatcher("index.html").forward(request, response);
		}
		if (op.equals("lister")) {
			request.setAttribute("listepersonnes", facade.listePersonnes());
			request.getRequestDispatcher("liste.jsp").forward(request, response);
		}
	}

}
