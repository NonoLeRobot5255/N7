with Ada.Text_IO;       use Ada.Text_IO;
with Ada.Float_Text_IO; use Ada.Float_Text_IO;
with Vecteurs_Creux;    use Vecteurs_Creux;

-- Exemple d'utilisation des vecteurs creux.
procedure Exemple_Vecteurs_Creux is

	V : T_Vecteur_Creux;
	Epsilon: constant Float := 1.0e-5;
begin
	Put_Line ("Début du scénario");
    Initialiser(V);
    modifier(V, 2 , 3.0);
    Afficher(V);
    New_Line;
   if Est_Nul(V) then
        Put("c'est vide");
        New_Line;
   end if;
    Detruire(V);
    Afficher(V);
    New_Line;
	Put_Line ("Fin du scénario");
end Exemple_Vecteurs_Creux;
