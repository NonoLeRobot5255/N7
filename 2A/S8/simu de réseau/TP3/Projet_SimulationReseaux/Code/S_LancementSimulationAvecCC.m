%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Script Simulation %%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
clear
close all

%% Parametres simulation
% Parametres abstraction de la couche physique
PhyParam.Ncodes = 54; % Nombre de codes

% Parametres de l'abstraction de couche MAC 
MACParam.Traitement = 5; % Duree de traitement.
MACParam.Rand = 3; %  % Rand maximum - d_rand.
MACParam.NMaxTransmission = 10; %  Nombre max de transmission possible. 

% Scenario de traffic

ChargeAvantOverload = 10; % Nombre de nouveaux utilisateurs par time slot avant la surcharge.
ChargePendantOverload = 30; % Nombre de nouveaux utilisateurs par time slot durant la surcharge.
ChargeApresOverload = 15; % Nombre de nouveaux utilisateurs par time slot apres la surcharge. 
dureeOverload = 200; % Duree en nombre de slots de la surcharge. 
ProfilTrafic = [ChargeAvantOverload*ones(1,100) ChargePendantOverload*ones(1,dureeOverload) ChargeApresOverload*ones(1,300)]; % Generation du profil de trafic. 
idxSlotStats = 101:(101+dureeOverload); % indice des slots ou on calcule les stats. 
NbSlots = length(ProfilTrafic);

% Parametres du controle de charge
CCParam.paccess = 0.5; % Probabilite d'acces 
CCParam.NslotBarringMax = 200; % Nombre de slots max ou l'utilisateur est bloque. 

% MonteCarlo
MonteCarlo = 10; % Nombre iteration de MonteCarlo
SaveThroughputSimulation = nan(MonteCarlo,NbSlots); %Throughput simulations
%---- A remplir ------
% metriques etudiees.... 
%----------------------

%% Simulateur

for k = 1:MonteCarlo
    fprintf('Iter : %d \n',k);
    [SaveThroughputSimulation(k,:),Stats] = F_SimulateurAvecCC(ProfilTrafic,PhyParam,MACParam,CCParam,idxSlotStats);

end
%% Plot

AverageThroughput = mean(SaveThroughputSimulation,1);

figure
plot(AverageThroughput);
xlabel('Time slots','interpreter','latex');
ylabel('Throughput station de base','interpreter','latex');
grid on;