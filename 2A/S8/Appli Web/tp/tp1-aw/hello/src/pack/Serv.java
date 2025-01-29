package pack;

import java.io.IOException;

import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;

@WebServlet("/Serv")
public class Serv extends HttpServlet {
 
    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        String s1 = request.getParameter("op1");
        String s2 = request.getParameter("op2");
        response.getWriter().println("<html><body>La somme de</body></html>");
    int nb1 = Integer.parseInt(s1);
    int nb2 = Integer.parseInt(s2);
    int sum = nb1 + nb2;
    response.getWriter().println(nb1 + " et " + nb2 + " est " + sum);
    }

    @Override
    protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {

    }
}