Fe = 24000;
Te = 1/Fe;
Rb = 3000;
Tb = 1/Rb;
n=1;
M = 2^n;
Ts = log2(M)*Tb;
Rs = Rb/log2(M);
nb_bits = 20;
S = randi([0 1],nb_bits,1);



%% modulateur :
% Mapping

Ns = Fe * Ts; % Nombre d'échantillons! par bits

SE = (2*S - 1)';
At = kron(SE, [1 zeros(1, Ns-1)]);

% Filtre
T1 = 0:Te:(nb_bits*Ns-1)*Te; % Echelle temporelle
h1 = ones(1, Ns); % Reponse impulsionnelle du filtre
y = filter(h1, 1, At);

% Tracés
figure('name', 'Modulateur ')

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
    DSP1 = pwelch(y, [],[],Fe,'twosided');
    axe_frequences = linspace(-Fe/2, Fe/2, length(DSP1));
    nexttile
    semilogy(axe_frequences,fftshift(DSP1))
    xlabel('Fréquence (Hz)');
    ylabel('DSP');
    title('tracé de la DSP par rapport a la fréquence');
% filtre récéption
y = filter(h1,1,y);
    plot(T1,y)
    ylim([-10,10]);
    xlabel("temps (s)")
    ylabel("Signal filtré")
    title('Tracé du signal temporel filtré à la récéption')
% réponse globale impulsion

g = conv(h1,h1);
t_g = linspace(0,2*Ns,length(g));
figure ('name','réponse impulsionelle globale')
plot(t_g,g)
    ylim([-10,10])
    xlabel("temps (s)")
    ylabel("g(t)")
    title('réponse impulsionelle globale')

% Diagramme de l'oeil
oeil = reshape(y,Ns,length(y)/Ns);
to= linspace(0,Ns,size(oeil,1));
figure 
plot(to,oeil)
xlabel('temps')
ylabel('amplitude')
title('diagramme de l''oeil')

N0=floor(Ts*Fe)
N0=3;
xe = y(N0:Ns:length(y));
xr = zeros(1,length(S));
xr(xe>0)=1;
xr(xe<0)=0;

S'
xr
TEB = mean(S' ~= xr)


    
