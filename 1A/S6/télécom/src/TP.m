Fe = 24000;
Te = 1/Fe;
Rb = 3000;
Tb = 1/Rb;
n=1;
M = 2^n;
Ts = log2(M)*Tb;
Rs = Rb/log2(M);
nb_bits = 100;
S = randi([0 1],nb_bits,1);



%% modulateur 1 :
% Mapping

Ns = Fe * Ts; % Nombre d'échantillons par bits

SE = (2*S - 1)';
At = kron(SE, [1, zeros(1, Ns-1)]);

% Filtre
T1 = 0:Te:(nb_bits*Ns-1)*Te; % Echelle temporelle
h1 = ones(1, Ns); % Reponse impulsionnelle du filtre
y = filter(h1, 1, At);

% Tracés
figure('name', 'Modulateur 1')

    % Signal généré
    nexttile
    stem(T1,At)
    ylim([-1.5, 1.5])
    xlabel("temps (s)")
    ylabel("Signal temporel")
    title('Tracé du signal temporel');
    
    nexttile
    plot(T1,y)
    ylim([-1.5, 1.5])
    xlabel("temps (s)")
    ylabel("Signal filtré")
    title('Tracé du signal temporel filtré')
    
    % Tracer la DSP par rapport à l'axe des fréquences
    DSP = abs(fft(y,1024));
    axe_frequences = linspace(0, Fe, length(DSP));
    nexttile
    stem(axe_frequences,DSP)
    xlabel('Fréquence (Hz)');
    ylabel('DSP');
    title('tracé de la DSP par rapport a la fréquence');


%% modulateur 2 :
% Mapping
Ns = Fe * 2*Ts; % Nombre d'échantillons par bits

S2 = reshape(S',2,nb_bits/2);
S2E = [1, nb_bits/2];
Choix = [-3 -1; 1 3];
for i=1:size(S2,2)
    S2E(i) = Choix(S2(1,i)+1,S2(2,i)+1);
end
At = kron(S2E, [1, zeros(1, Ns-1)]);

% Filtre
T2 = 0:Te:(nb_bits*Ns-1)*Te/2; % Echelle temporelle
h2 = ones(1, Ns); % Reponse impulsionnelle du filtre
y = filter(h2, 1, At);

% Tracés
figure('name', 'Modulateur 2')

    % Signal généré
    nexttile
    stem(T2,At)
    ylim([-4,4])
    xlabel("temps (s)")
    ylabel("Signal temporel")
    title('Tracé du signal temporel');
    
    nexttile
    plot(T2,y)
    ylim([-4,4])
    xlabel("temps (s)")
    ylabel("Signal filtré")
    title('Tracé du signal temporel filtré')
    
    % Tracer la DSP par rapport à l'axe des fréquences
    DSP = abs(fft(y,1024));
    axe_frequences = linspace(0, Fe, length(DSP));
    nexttile
    stem(axe_frequences,DSP)
    xlabel('Fréquence (Hz)');
    ylabel('DSP');
    title('tracé de la DSP par rapport a la fréquence');
%% modulateur 3
% Mapping

Ns = Fe * Ts; % Nombre d'échantillons par bits

SE = (2*S - 1)';
At = kron(SE, [1, zeros(1, Ns-1)]);
