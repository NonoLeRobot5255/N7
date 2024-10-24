with Ada.Text_IO;  use Ada.Text_IO;

with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with LCA;



procedure lca_sujet is
   package  LCA1 is
     new LCA(T_Cle=> Unbounded_String ,T_Valeur=>Integer);
   use LCA1;
   Sda : T_LCA;

begin
   Put_Line("debut du scenario");
   Initialiser(Sda);
   Enregistrer(Sda,To_Unbounded_String("un"),1);
   Enregistrer(Sda,To_Unbounded_String("deux"),2);
   Detruire(Sda);

   Put("fin du scenario");
end lca_sujet;
