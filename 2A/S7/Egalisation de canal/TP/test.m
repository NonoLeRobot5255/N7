
% Script for computing the BER for BPSK/QPSK modulation in ISI Channels
% 
close all;
clear all;

%% Simulation parameters
% On dï¿½crit ci-aprï¿½s les paramï¿½tres gï¿½nï¿½raux de la simulation

%Frame length
M=4; %2:BPSK, 4: QPSK
N  = 1000000; % Number of transmitted bits or symbols
Es_N0_dB = [0:3:30]; % Eb/N0 values
%Multipath channel parameters
hc=[1 0.8*exp(1i*pi/3) 0.3*exp(1i*pi/6) ];%0.1*exp(1i*pi/12)];%ISI channel
%hc=[0.04, -0.05, 0.07, -0.21, -0.5, 0.72, 0.36, 0, 0.21, 0.03, 0.07];
% a=1.2;
% hc=[1 -a];
Lc=length(hc);%Channel length
ChannelDelay=0; %delay is equal to number of non causal taps
figure()
%Preallocations
nErr_zfinf=zeros(1,length(Es_N0_dB));
for ii = 1:length(Es_N0_dB)

   % BPSK symbol generations
%    bits = rand(1,N)>0.5; % generating 0,1 with equal probability
%    s = 1-2*bits; % BPSK modulation following: {0 -> +1; 1 -> -1} 
   
    % QPSK symbol generations
   bits = rand(2,N)>0.5; % generating 0,1 with equal probability
   s = 1/sqrt(2)*((1-2*bits(1,:))+1j*(1-2*bits(2,:))); % QPSK modulation following the BPSK rule for each quadatrure component: {0 -> +1; 1 -> -1} 
   sigs2=var(s);
   
   % Channel convolution: equivalent symbol based representationï¿½&
   z = conv(hc,s);
  
   %Generating noise
   sig2b=10^(-Es_N0_dB(ii)/10);
   %n = sqrt(sig2b)*randn(1,N+Lc-1); % white gaussian noise, BPSK Case
    n = sqrt(sig2b/2)*randn(1,N+Lc-1)+1j*sqrt(sig2b/2)*randn(1,N+Lc-1); % white gaussian noise, QPSK case
   
   % Adding Noise
   y = z + n; % additive white gaussian noise

   %% zero forcing equalization
   % We now study ZF equalization
   
   %Unconstrained ZF equalization, only if stable inverse filtering
   
   
   %%
   % 
   %  The unconstrained ZF equalizer, when existing is given by 
   % 
   % $w_{,\infty,zf}=\frac{1}{h(z)}$
   % 
   %%
   % 
    

    % J'AI AJOUTE CA ET LE PLOT DU TEB EN BAS
    signal_nonegalise = zeros(2,length(bits));
    signal_nonegalise(1,:)= real(y(1:N)) < 0;
    signal_nonegalise(2,:)= imag(y(1:N)) < 0;
    erreurs_nonegalise(1,ii) = size(find([bits(:)- signal_nonegalise(:)]),1);
    %
   
    s_zf=filter(1,hc,y);%if stable causal filter is existing
    bhat_zf = zeros(2,length(bits));
    bhat_zf(1,:)= real(s_zf(1:N)) < 0;
    bhat_zf(2,:)= imag(s_zf(1:N)) < 0;
    nErr_zfinfdirectimp(1,ii) = size(find([bits(:)- bhat_zf(:)]),1);



    %Otherwise, to handle the non causal case
    %ZF
    Nzf=200;
    [r, p, k]=residuez(1, hc);
    [w_zfinf]=ComputeRI( Nzf, r, p, k );
    s_zf=conv(w_zfinf,y);


    %MMSE
    deltac= zeros( 1 , 2 * Lc-1 ) ;
    deltac ( Lc ) = 1 ;
    Nmmse = 200 ;%c a u s a l p a r t
    [ r , p , k ] = residuez(fliplr(conj(hc)),(conv(hc,fliplr(conj(hc)))+(sig2b/sigs2)*deltac)) ;
    [ w_mmseinf ] = ComputeRI (Nmmse,r,p,k );
    s_mmse = conv(w_mmseinf,y);

    bhat_zf = zeros(2,length(bits));
    bhat_zf(1,:)= real(s_zf(Nzf:N+Nzf-1)) < 0;
    bhat_zf(2,:)= imag(s_zf(Nzf:N+Nzf-1)) < 0;

    bhat_mmse = zeros(2,length(bits));
    bhat_mmse(1,:)= real(s_mmse(Nmmse:N+Nmmse-1)) < 0;
    bhat_mmse(2,:)= imag(s_mmse(Nmmse:N+Nmmse-1)) < 0;
    nErr_mmseinfdirectimp(1,ii) = size(find([bits(:)- bhat_mmse(:)]),1);

    nErr_zf(1,ii) = size(find([bits(:)- bhat_zf(:)]),1);
    nErr_mmse(1,ii) = size(find([bits(:)- bhat_mmse(:)]),1);
    %% tracï¿½ de la DSP
    nexttile
    [dsp,f] = pwelch(s_mmse,[],[],[],'twosided');
    plot(f,10*log(dsp))
    title('dsp')
    xlabel('frï¿½quence')
    ylabel('dsp')
    
    
    %% FIR
    Nw=16;
    d = 5;
    H = toeplitz([hc(1) zeros(1,Nw-1)]',[hc, zeros(1,Nw-1)]);
    Ry = (conj(H)*H.');
    p = zeros(Nw+Lc-1,1);

    P= (H.'*inv((Ry))*conj(H));
    [alpha,dopt]=max(diag(abs(P)));
    %p(d+1)=1;
    p(dopt)=1;
    Gamma = conj(H)*p;
    w_zf_fir = (inv(Ry)*Gamma).';

    sig_e_opt = sigs2 -conj(w_zf_fir)*Gamma;
    bias = 1-sig_e_opt/sigs2;
    shat = conv(w_zf_fir,y);
    shat = shat(dopt:end);

    bHat = zeros(2,length(bits));
    bHat(1,:)=real(shat(1:N))<0;
    bHat(2,:)=imag(shat(1:N))<0;

    nErr_Hatinfdirectimp(1,ii) = size(find([bits(:)- bHat(:)]),1);
    nErr_Hat(1,ii) = size(find([bits(:)- bHat(:)]),1);

    %% FIR
    d = 5;
    H = toeplitz([hc(1) zeros(1,Nw-1)]',[hc, zeros(1,Nw-1)]);
    Ry = sigs2 * (conj(H)*H.')+sig2b*eye(Nw);
    p = zeros(Nw+Lc-1,1);

    P= 1/sigs2 * (H.'*inv((Ry/sigs2))*conj(H));
    [alpha,dopt]=max(diag(abs(P)));
    %p(d+1)=1;
    p(dopt)=1;
    Gamma = conj(H)*p;
    w_zf_fir = (inv(Ry)*Gamma).';

    sig_e_opt = sigs2 -conj(w_zf_fir)*Gamma;
    bias = 1-sig_e_opt/sigs2;
    shat = conv(w_zf_fir,y);
    shat = shat(dopt:end);

    bHat = zeros(2,length(bits));
    bHat(1,:)=real(shat(1:N))<0;
    bHat(2,:)=imag(shat(1:N))<0;

    nErr_Hat1infdirectimp(1,ii) = size(find([bits(:)- bHat(:)]),1);
    nErr_Hat1(1,ii) = size(find([bits(:)- bHat(:)]),1);

end
simBer_zfinfdirectimp = nErr_zfinfdirectimp/N/log2(M); % simulated ber
simBer_zfinf = nErr_zfinf/N/log2(M); % simulated ber

simBer_mmseinfdirectimp = nErr_mmseinfdirectimp/N/log2(M); % simulated ber
simBer_mmseinf = nErr_mmse/N/log2(M); % simulated ber

simBer_Hatinfdirectimp = nErr_Hatinfdirectimp/N/log2(M); % simulated ber
simBer_Hatinf = nErr_Hat/N/log2(M); % simulated ber

simBer_Hat1infdirectimp = nErr_Hat1infdirectimp/N/log2(M); % simulated ber
simBer_Hat1inf = nErr_Hat1/N/log2(M); % simulated ber

%
TEB_nonegalise = erreurs_nonegalise/N/log2(M);  % simulated ber
%

% plot
s_ml = mlseeq(y, hc,[1+i -1+i 1-i -1-i], 5, 'rst', 1, [], []);

figure
semilogy(Es_N0_dB,simBer_zfinfdirectimp(1,:),'bs-','Linewidth',2);
hold on
semilogy(Es_N0_dB,TEB_nonegalise(1,:),'Linewidth',2);
% semilogy(Es_N0_dB,simBer_zfinf(1,:),'rs-','Linewidth',2);
% hold on
semilogy(Es_N0_dB,simBer_mmseinfdirectimp(1,:),'p-','Linewidth',2);
hold on
semilogy(Es_N0_dB,simBer_Hatinfdirectimp(1,:),'p-','Linewidth',2);
hold on
semilogy(Es_N0_dB,simBer_Hat1infdirectimp(1,:),'p-','Linewidth',2);
hold on 
% semilogy(Es_N0_dB,s_ml(1,:),'bs-','Linewidth',2)
% semilogy(Es_N0_dB,simBer_mmseinf(1,:),'gr-','Linewidth',2);
axis([0 50 10^-6 0.5])
grid on
legend('sim-zf-inf/direct','signal non Ã©galisÃ©','sim-mmse-inf/direct','hat','hat1');
xlabel('E_s/N_0, dB');
ylabel('Bit Error Rate');
title('Bit error probability curve for QPSK in ISI with ZF equalizers')

figure
title('Impulse response')
stem(real(w_mmseinf))
%stem(real(w_zfinf))
hold on
%stem(real(w_zfinf),'r-')
stem(real(w_mmseinf),'r-')
ylabel('Amplitude');
xlabel('time index')


