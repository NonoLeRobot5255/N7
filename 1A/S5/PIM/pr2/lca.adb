with Ada.Text_IO;            use Ada.Text_IO;
with SDA_Exceptions;         use SDA_Exceptions;

with Ada.Unchecked_Deallocation;

package body LCA is

	procedure Free is
		new Ada.Unchecked_Deallocation (Object => T_Cellule, Name => T_LCA);


	procedure Initialiser(Sda: out T_LCA) is
	begin
      Sda:=null;
	end Initialiser;


	procedure Detruire (Sda : in out T_LCA) is
	begin

      if not Est_Vide(Sda) then
         Detruire (Sda.All.Suivant);
         Free(Sda);
      end if;
	end Detruire;


   procedure Afficher_Debug (Sda : in T_LCA) is

   begin

      if Sda = null then
         Put("--E");
         return;
      else
         Put("-->[");
         Afficher_Cle(Sda.all.Cle);
         put(" : ");
         Afficher_Donnee(Sda.all.Valeur);
         put("]");
         Afficher_Debug(Sda.all.Suivant);
      end if;


	end Afficher_Debug;


	function Est_Vide (Sda : T_LCA) return Boolean is
	begin
      if Sda=null then
         return True;
      else
         return False;
      end if;
	end;


    function Taille (Sda : in T_LCA) return Integer is
    begin
      if Sda=null then
         return 0;
      else
         return 1+Taille(Sda.all.Suivant);
      end if;

    end Taille;


	procedure Enregistrer (Sda : in out T_LCA ; Cle : in T_Cle ; Valeur : in T_Valeur) is
	begin
      if Sda=null then
         Sda:= new T_Cellule'(Cle,Valeur,null);
      else
         if Sda.all.Cle=Cle then
            Sda.all.Valeur:=Valeur;
         else
             Enregistrer(Sda.all.Suivant, Cle,Valeur);
         end if;
      end if;


	end Enregistrer;


	function Cle_Presente (Sda : in T_LCA ; Cle : in T_Cle) return Boolean is
	begin
   if Sda=null then
      return False;
   else
      if Sda.all.Cle=Cle then
         return True;
      else
         return Cle_Presente(Sda.all.suivant, Cle);
      end if;
   end if;
	end;


	function La_Valeur (Sda : in T_LCA ; Cle : in T_Cle) return T_Valeur is
	begin
      if Sda=null then
         raise Cle_Absente_Exception;
      else
         if Sda.all.Cle=Cle then
            return Sda.all.Valeur;
         else
            return La_Valeur(Sda.all.Suivant,Cle);
         end if;
      end if;

	end La_Valeur;


   procedure Supprimer (Sda : in out T_LCA ; Cle : in T_Cle) is
      temp: T_LCA;
   begin
      if sda=Null then
         raise Cle_Absente_Exception;
      else
         if Sda.all.Cle=Cle then
            Sda:=Sda.all.suivant;
         else

            if Sda.all.suivant /= Null and then Sda.all.suivant.Cle=Cle then
               if sda.all.suivant.all.suivant /= Null then
                  temp:=Sda.all.suivant.all.suivant;
                  Free(sda.all.Suivant);
                  Sda.all.suivant:=temp;
               else
                  Free(Sda.all.Suivant);
               end if;
            else
               if Sda.all.suivant/=null then
                  Supprimer(Sda.all.suivant,Cle);
               else
                  raise Cle_Absente_Exception;
               end if;
            end if;
         end if;
      end if;
	end Supprimer;


   procedure Pour_Chaque (Sda : in T_LCA) is


   begin

      if Sda=null then
         return;
      else
         begin
            traiter(Sda.all.Cle,Sda.all.Valeur);
         exception
            when others => null;
         end;
      end if;


         Pour_Chaque(Sda.all.suivant);


	end Pour_Chaque;


end LCA;
