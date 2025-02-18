<%@ page language="java" contentType="text/html; charset=UTF-8"
    pageEncoding="UTF-8"%>
<!DOCTYPE html>
<html>
<head>
<meta charset="UTF-8">
<title>Insert title here</title>
</head>
<body>

<form method="post" action="Serv">
nb1 : <input type="text" name="nb1"><br>
nb2 : <input type="text" name="nb2"><br>
<input type="submit" value="compute"><br>
</form>
Resultat: <%=request.getAttribute("resultat") %>

</body>
</html>