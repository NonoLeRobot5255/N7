%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%               TP1 de Traitement Numérique du Signal
%                   SCIENCES DU NUMERIQUE 1A
%                       Fevrier 2024 
%                        Nolann MARTIN
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

clear all
close all

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%PARAMETRES GENERAUX
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
A=1;        %amplitude du cosinus
f0=1100;       %fr�quence du cosinus en Hz
T0=1/f0;       %p�riode du cosinus en secondes
N=90;        %nombre d'�chantillons souhait�s pour le cosinus
Fe1=10000;%fr�quence d'�chantillonnage en Hz
Fe2 = 1000;
Te2 = 1/Fe2;
Te1=1/Fe1;       %p�riode d'�chantillonnage en secondes
SNR="feur";      %SNR souhait� en dB pour le cosinus bruit�


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%GENERATION DU COSINUS NUMERIQUE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%D�finition de l'�chelle temporelle
t1 = linspace(0,(N-1)*Te1,N);
t2 = linspace(0,(N-1)*Te2,N);
%G�n�ration de N �chantillons de cosinus � la fr�quence f0
x=A*cos(2*pi*f0*t1);
x2 = A*cos(2*pi*f0*t1);
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%TRACE DU COSINUS NUMERIQUE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Sans se pr�occuper de l'�chelle temporelle
figure
plot(x)

%Trac� avec une �chelle temporelle en secondes
%des labels sur les axes et un titre (utilisation de xlabel, ylabel et
%title)
figure
plot(x2);
grid
xlabel('Temps (s)')
ylabel('signal')
title(['Tracé d''un cosinus numérique de fréquence ' num2str(f0) 'Hz']);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%CALCUL DE LA TRANSFORMEE DE FOURIER NUMERIQUE (TFD) DU COSINUS NUMERIQUE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Sans zero padding 
X=fft(x);
%Avec zero padding (ZP : param�tre de zero padding � d�finir)         
X_ZP=fft(x2,1024);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%TRACE DU MODULE DE LA TFD DU COSINUS NUMERIQUE EN ECHELLE LOG
%SANS PUIS AVEC ZERO PADDING
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Avec une �chelle fr�quentielle en Hz
%des labels sur les axes et des titres
%Trac�s en utilisant plusieurs zones de la figure (utilisation de subplot) 
figure('name',['Tracé du module de la TFD d''un cosinus numérique de fréquence ' num2str(f0) 'Hz'])

subplot(2,1,1)
echelle_frequentielle=linspace(0,Fe1,length(X));
semilogy(echelle_frequentielle,X);
grid
title('Sans zero padding')
xlabel('Fréquence (Hz)')
ylabel('|TFD|')

subplot(2,1,2)
echelle_frequentielle=linspace(0,Fe1,length(X_ZP));
semilogy(echelle_frequentielle,X_ZP);
grid
title('Avec zero padding')
xlabel('Fréquence (Hz)')
ylabel('|TFD|')

%Avec une �chelle fr�quentielle en Hz
%des labels sur les axes et des titres
%Trac�s superpos�s sur une m�me figure 
% (utilisation de hold, de couleurs diff�rentes et de legend)
% !! UTILISER ICI fftshit POUR LE TRACE !!
figure
echelle_frequentielle=linspace(0,Fe1,length(X));
semilogy(echelle_frequentielle,fftshift(abs(X)),'b');    %Trac� en bleu : 'b'
hold on
echelle_frequentielle=linspace(0,Fe1,length(X_ZP));
semilogy(echelle_frequentielle,fftshift(abs(X_ZP)),'r'); %Trac� en rouge : 'r'
grid
legend('Sans zero padding','Avec zero padding')
xlabel('Fréquence (Hz)')
ylabel('|TFD|')
title(['Tracé du module de la TFD d''un cosinus numérique de fréquence ' num2str(f0) 'Hz'])

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%CALCUL DE LA TFD DU COSINUS NUMERIQUE AVEC FENETRAGE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Application de la fen�tre de pond�ration de Hamming
x_fenetre_hamming=x.*hamming(length(x)).';
%Calcul de la TFD pond�r�e, avec zeros padding
X_ZP_hamming=fft(x_fenetre_hamming);
%Application de la fen�tre de pond�ration de Blackman
x_fenetre_blackman=x.*blackman(length(x)).';
%Calcul de la TFD pond�r�e, avec zeros padding
X_ZP_blackman=fft(x_fenetre_blackman);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%TRACE DU MODULE DE LA TFD DU COSINUS NUMERIQUE AVEC FENETRAGE EN ECHELLE LOG
%POUR DIFFERENTES FENETRES
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
"� r�aliser : trac�s superpos�s sur la m�me figure de la TFD non fen�tr�e, " + ...
    "de la TFD avec fen�trage de Hamming, de la TFD avec fen�trage de Blackman" + ...
    "Le tout avec une �chelle fr�quentielle en Hz, un titre, des labels sur les axes, " + ...
    "une l�gende et en utilisant fftshift"

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%CALCUL DE LA DENSITE SPECTRALE DE PUISSANCE (DSP) DU COSINUS NUMERIQUE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Estimation par p�riodogramme
Sx_periodogramme="� completer";

%Estimation par p�riodogramme de Welch
Sx_Welch=pwelch(x, [],[],[],Fe1,'twosided');

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%TRACE DE LA DENSITE SPECTRALE DE PUISSANCE (DSP) DU COSINUS NUMERIQUE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Trac�s superpos�s sur une m�me figure en utilisant fftshift
%Avec une �chelle fr�quentielle en Hz
%des labels sur les axes, un titre, une l�gende
figure
echelle_frequentielle="� completer";
semilogy("� completer",'b')
hold on
echelle_frequentielle="a completer";
semilogy("� completer",'r')
legend('Periodogramme','Periodogramme de Welch')
xlabel('Fr�quences (Hz)')
ylabel('DSP')
title('Trac�s de la DSP d''un cosinus num�rique de fr�quence 1100 Hz');

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%CALCUL ET TRACE DE LA FONCTION D'AUTOCORRELATION DU COSINUS BRUITE AVEC LE
%BON SNR
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%       

%Calcul de la puissance du signal
P_signal=mean(abs(x).^2);
%Calcul de la puissance du bruit pour obtenir le SNR souhait�
P_bruit="� completer";

%G�n�ration du bruit gaussien � la puissance Pb
bruit=sqrt(P_bruit)*randn(1,length(x));
%Ajout du bruit sur le signal
x_bruite=x+bruit;

%Calcul de la fonction d'autocorr�lation du signal bruite
%attention pas le 1/N quand on utilise xcorr => � rajouter
Rx=(1/length(x_bruite))*xcorr(x_bruite); 

%Trac� du signal bruit� avec une �chelle temporelle en secondes
figure
plot("� completer")
grid
xlabel('Temps (s)')
ylabel('Signal')
title('Trac� du cosinus bruit�');

%Trac� de la fonction d'autocorr�lation du signal bruite avec une �chelle 
%temporelle en secondes
figure
echelle_tau="� completer";
plot("� completer")
grid
xlabel('\tau (s)')
ylabel('R_x(\tau)')
title('Trac� de la fonction d''autocorr�lation du cosinus bruit�');

