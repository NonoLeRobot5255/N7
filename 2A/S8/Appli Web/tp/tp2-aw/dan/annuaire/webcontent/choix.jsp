<%@ page language="java" contentType="text/html; charset=UTF-8"
    pageEncoding="UTF-8"%>
<%@ page import="java.util.*, pack.*" %>
<!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">
<html>
<head>
<meta http-equiv="Content-Type" content="text/html; charset=UTF-8">
<title>Insert title here</title>
</head>
<body>

<form method="post" action="Serv">

Choisir la personne:<br>
<% 
Collection<Personne> listepersonnes = (Collection<Personne>)request.getAttribute("listepersonnes");
for (Personne p : listepersonnes) {
	int id = p.getId();
	String s = p.getNom() + " " + p.getPrenom();
%>
<input type="radio" name="idpersonne" value="<%=id %>"> <%=s %><br>
<%
}
%>
<br>
	

Choisir l'adresse:<br>
<% 
Collection<Adresse> listeadresses = (Collection<Adresse>)request.getAttribute("listeadresses");
for (Adresse a : listeadresses) {
	int id = a.getId();
	String s = a.getRue() + " " + a.getVille();
%>
<input type="radio" name="idadresse" value="<%=id %>"> <%=s %><br>
<%
}
%>
<br>
<input type="submit" value="OK">
<input type="hidden" name="op" value="choix">
</form>

</body>
</html>