Fe = 24000;
Te = 1/Fe;
Rb = 3000;
Tb = 1/Rb;
n=1;
M = 2^n;
Ts = log2(M)*Tb;
Rs = Rb/log2(M);
Ns = Ts/Te;
nb_bits = 100;

t = linspace(0,nb_bits * Ts-Te,nb_bits);


%modulateur 1 :
S = randi([0 1],1,nb_bits);
SE = 2*S-1;




ht = ones(1,Ns);
pDirac = kron(SE,[1 zeros(1,Ns-1)]);
y = filter(ht,1,pDirac);
dsp = fft(SE,1024);

figure
ech_freq = linspace(0,Fe,length(dsp));

plot(ech_freq,dsp);
grid
xlabel('Temps (s)')
ylabel('signal')
title('Modulateur 1');

%modulateur 2 :
S2 = randi([0 1],1,nb_bits);
S2 = reshape(S2,2,nb_bits/2);
S2E = [1, nb_bits/2];
Choix = [-3 -1; 1 3];
for i=1:size(S2,2)
    S2E(i) = Choix(S2(1,i)+1,S2(2,i)+1);
end



dsp = fft(S2E,1024);

figure
ech_freq = linspace(0,Fe,length(dsp));
plot(ech_freq,dsp);
grid
xlabel('Temps (s)')
ylabel('signal')
title('Modulateur 2');


