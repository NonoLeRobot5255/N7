with ada.Text_IO; use ada.Text_IO;
with ada.Integer_Text_IO; use ada.Integer_Text_IO;
procedure exo_2 is
    borneinff : Integer;
    bornesupp : Integer;
    proposition : Integer;
    reponse : Character;
begin
    bornesupp := 999;
    borneinff := 0;
    proposition := 500;
    reponse := 'm';
    
    while (reponse /= 't' or reponse /= 'T') loop
        Put("est ce que ");
        Put(proposition, Width => 1);
        Put(" est le bon nombre?");
        Get(reponse);
        New_Line;
 
        
        case reponse is
            when 'g'  | 'G' => borneinff := proposition;
            when 'p' | 'P' => bornesupp := proposition;
            when 't' | 'T' => return;
            when others => null;
        end case; 
        
        put (proposition, Width => 1);
        New_Line;
        if (((bornesupp-borneinff) mod 2) = 0) then 
            proposition := ((bornesupp-borneinff)/2);
            
        else 
            proposition := (bornesupp-borneinff+1)/2;
        end if;
     
        
    end loop;
    
    
    
    --if (proposition> bornesupp or proposition<borneinff) then
        --Put_Line("bien tenter mais j'ai vu que tu as triché");
    if (reponse = 't' or reponse = 'T') then
            Put_Line("J'ai trouvé ton nombre je suis trop fort !");
       
    end if;
    
end exo_2;
