%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Script Simulation %%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
clear
close all

%% Parametres simulation
% Parametres abstraction de la couche physique
PhyParam.Ncodes = 54; % Nombre de codes (orthogonaux) 

% Parametres de l'abstraction de couche MAC 
MACParam.Traitement = 5; % Duree de traitement - d_traitement.
MACParam.Rand = 3; % Rand maximum - d_rand.
MACParam.NMaxTransmission = 10; % Nombre max de transmission possible. 

% Scenario de traffic
NbSlots = 1000; % Nombre de slots simules.
ChargeConstante = 20; % Nombre de nouveaux utilisateurs par time slots. 
ProfilTrafic = ChargeConstante*ones(1,NbSlots); % Generation du profil de trafic 

% MonteCarlo
MonteCarlo = 10; % Nombre d'iteration de MonteCarlo
SaveThroughputSimulation = nan(MonteCarlo,NbSlots); % Sauvegarde Throughput simulations

%% Simulateur

for k = 1:MonteCarlo
    fprintf('Iter : %d/%d \n',k,MonteCarlo);
    SaveThroughputSimulation(k,:) = F_SimulateurSansCC(ProfilTrafic,PhyParam,MACParam);

end
%% Plot

AverageThroughput = mean(SaveThroughputSimulation,1);

figure
plot(AverageThroughput);
xlabel('Time slots','interpreter','latex');
ylabel('Throughput station de base','interpreter','latex');
grid on;
axis([0 NbSlots 0 PhyParam.Ncodes]);
