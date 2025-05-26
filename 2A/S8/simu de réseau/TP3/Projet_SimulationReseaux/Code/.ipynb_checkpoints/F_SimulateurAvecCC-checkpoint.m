function [ThroughputSlots,Stats] = F_SimulateurAvecCC(ProfilTrafic,PhyParam,MACParam,CCParam,idxSlotStats)
% ProfilTrafic : Profil de trafic, nombre de nouveaux utilisateurs par time slot
% PhyParam : Parametres de couche physique
% MACParam : Parametres de couche MAC
% CCParam : Parameters de controle de charge
% idxSlotStats : indice des slots ou on calcule les stats.
NbSlots = length(ProfilTrafic); % Nombre de time slots simules.
Utilisateurs = zeros(sum(ProfilTrafic),6); % Matrice Utilisateurs, attention differente de la precedente..
idxArriveeUtilisateurs = 1; % Pour remplir la matrice utilisateurs.
% Colonne numero 1 - Time slot actuel
% Colonne numero 2 - Flag Stats
% Colonne numero 3 - Time slot d'arrivee dans le systeme
% Colonne numero 4 - Time slot sortie du systeme
% Colonne numero 5 - Nombre de transmissions
% Colonne numero 6 - Bool Reussite Transmission


for Slot = 1:NbSlots
    
    if min(abs(idxSlotStats-Slot)) == 0
        FlagStats = 1;
    else
        FlagStats = 0;
    end
    
    % Arrivee des nouveaux utilisateurs
    Utilisateurs(idxArriveeUtilisateurs:(idxArriveeUtilisateurs+ProfilTrafic(Slot)-1),1) = Slot;
    Utilisateurs(idxArriveeUtilisateurs:(idxArriveeUtilisateurs+ProfilTrafic(Slot)-1),2) = FlagStats;
    Utilisateurs(idxArriveeUtilisateurs:(idxArriveeUtilisateurs+ProfilTrafic(Slot)-1),3) = Slot;
    idxArriveeUtilisateurs = idxArriveeUtilisateurs + ProfilTrafic(Slot);
    
    % Controle de charge
    
    if % Condition activation controle de charge
        Utilisateurs = ApplicationControleDeCharge(Utilisateurs,Slot,CCParam);
    end
    
    % Simulation des transmissions
    
    [Utilisateurs, ThroughputSlots(Slot)] = SimulationTransmission(Utilisateurs,Slot,PhyParam,MACParam);
    
    
    % ---- Stats ---- %
    
end

    function [Utilisateurs, ThroughputSlot] = SimulationTransmission(Utilisateurs,Slot,PhyParam,MACParam)
        
        IdxUtilisateursEnTransmission = find((Utilisateurs(:,1)-Slot) == 0);
        NbRequeteTransmisesDurantSlot = length(IdxUtilisateursEnTransmission);
        PLRSlot = 1 - exp(-NbRequeteTransmisesDurantSlot/PhyParam.Ncodes);
        
        ThroughputSlot = 0;
        
        for k = 1:length(IdxUtilisateursEnTransmission)
            % ---- A remplir ----
        end
        
    end

    function Utilisateurs = ApplicationControleDeCharge(Utilisateurs,Slot,CCParam)
        
        IdxUtilisateursEnTransmission = find((Utilisateurs(:,1)-Slot) == 0);
        for k = 1:length(IdxUtilisateursEnTransmission)
            
            % ---- A remplir ----
            
        end
    end