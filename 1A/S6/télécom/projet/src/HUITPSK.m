clear all;
close all;

Fe = 6000;
Te = 1/Fe;
Rb = 3000;
Tb = 1/Rb;
n=3;
M = 2^n;
Ts = log2(M)*Tb;
Rs = Rb/log2(M);
nb_bits = 90000 ;
Ns = Fe * Ts; % Nombre d'échantillons par bits

EbN0dB = [0:6];
EbN0=10.^(EbN0dB./10);
L= 8;
h1 = rcosdesign(0.2,L,Ns); % Reponse impulsionnelle du filtre
hr = fliplr(h1);

figure('Name','constellation')
for k=1:length(EbN0)

    %% modulateur :
    % Mapping
    S = randi([0 1],1,nb_bits);
    S3 = reshape(S',3,nb_bits/3);
    S3E = [1, nb_bits/3];
    Choix = [0 3;1 2];
    Choix(:,:,2) = [7 4;6 5];
    for j=1:size(S3,2)
        S3E(j) = Choix(S3(1,j)+1,S3(2,j)+1,S3(3,j)+1);
    end
    dk = pskmod(S3E,8,pi/8,'gray');

    At = [kron(dk, [1, zeros(1, Ns-1)]) zeros(1,length(h1))];
    
    % Filtre
    % Echelle temporelle
    
    y = filter(h1, 1, At);
    T1 = ([0:length(y)-1] * Te);
   
    %bruit
    Px = mean(abs(y).^2);
    sigma2 = ((Px*Ns)/(2*log2(M)*EbN0(k)));
    
    recu=y+sqrt(sigma2)*randn(1,length(y));
    recu = recu  + 1i *sqrt(sigma2)*randn(1,length(y));
    
    
    %filtre de récéption
    z= filter(hr,1,recu);

    
    %echantillonage et démapping 
    xe = z(length(h1):Ns:length(z)-1);

    %tracé de la constellation
    nexttile
    plot(real(xe),imag(xe),'linestyle','none','marker','o')
    grid on
    xlabel('partie réél')
    ylabel('partie imaginaire')
    title(['Eb/N0 = ' num2str(EbN0dB(k)) ])
    
    
    xr_temp = pskdemod(xe,8,pi/8,'gray');
    xr = [];
    for j=1:length(S)/3
        if xr_temp(j)== 0
            xr = [xr 0 0 0];
        elseif xr_temp(j)== 1
            xr = [xr 1 0 0];
        elseif xr_temp(j)== 2
            xr = [xr 1 1 0];
        elseif xr_temp(j)== 3
            xr = [xr 0 1 0];
        elseif xr_temp(j)== 4
            xr = [xr 0 1 1];
        elseif xr_temp(j)== 5
            xr = [xr 1 1 1];
        elseif xr_temp(j)== 6
            xr = [xr 1 0 1];
        else
            xr = [xr 0 0 1];
        end
    end

    TEB (k) = mean(S ~= xr);
end

figure
%TEB théorique
semilogy(EbN0dB,qfunc(sqrt(6*EbN0)*sin(pi/8)),'g')
hold on
%TEB simulé
semilogy(EbN0dB,TEB,'pr')
xlabel('Eb/N0')
ylabel('TEB')
legend('TEB théorique', 'TEB simulé')