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

<% 
Collection<Personne> listepersonnes = (Collection<Personne>)request.getAttribute("listepersonnes");
for (Personne p : listepersonnes) {
	out.println(p.getNom() + " " + p.getPrenom()+"<br>");
	for (Adresse a : p.getAdresses()) {
		out.println("&nbsp;&nbsp;"+a.getRue()+" "+a.getVille()+"<br>");
}}
%>

</body>
</html>
