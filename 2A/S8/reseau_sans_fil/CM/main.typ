#import "template.typ": *

#show: project.with(
  title :  "Réseaux sans Fils/ Wireless Networks",
  generalites: (),
  definition:("SNIR", "Signal to Noise and Interference Ratio","ARF","Auto Rate Fallback","ToF","Time of Flight","IoT","Inernet of Things")
)


= Waht is WI-FI ?

== Last Year recall

=== Generalities

Standard 802.11 standard.

2 types of architecture:
+ WLAN
  - Connected to internet via Acess Point (with wires) ;
  - Clients can move ;
  - Clients communicate with AP wirelessly with Multiple Acess CHannel.
+ Ad-hoc (peer to peer)

Uses carrier sensing with Collision Avoidance.

ARQ : Automatic Request Acknowledgment

Truncated binary exponential backoff for handling congestion


=== Backoff 

*Backoff value* Random() x SlotTime
- Random() : Pseudo-rand int from [O,CW] where $"CW"_("min") < "CW" < "CW"_("max")$



=== QOS in WIFI (ou ==?)

- provide different priorities depending on app, user, data flow
- guarantee a certain level of performance to a data flow


We use a higher Data rate when we want less errors
  - Donc pourquoi juste pas prendre le + haut débit si on a que des bénèfs?  
- To adjust the rate based on the SNIR (if low ration: low Signal Noise, so we take lower bit rate)

diapo 44 : A peut detecter la qualité du signal, pour la distance avec le AP c'est compliqué. Le débit basé sur la distance peut être trompeur car il peut y avoir une distance faible mais des obstacles.


=== Auto-Rate Fallback (ARF)
- ARF initial bit rate: max available
- adjusts the bit rate for the destination based on critera
  - if packet is dropped => lowers rate
  - 10 sucessive transmitted packets => increases rate
- ARF adjust the rate base on :
  - move to a lowest if there is a drop
  - move to a higher if there is 10 success in a row
  - else we continue to the same

*Weakness* Does not react to retries


why Wi-fi drops packet ?
- If there is $cases(4,7)$ ressend of packet, you drop it;
- We prefer A 24 bit rate with 1 try rather than 48 bit rate with 3 tries. as the effective rate for 48 is not 48, but $48/3$

=== Small Exercice (s 52):

*We suppose 1 packet=24Mb* 
- Solution 1:

Half of the time you send a packet at 24Mbps.

The other half, you send a packet at 8Mbps.

So with 2 packets like this:

The 1st packet takes 1 second, and the second takes 3.

So in 4 seconds we sent 48Mbps, that's equal to 12Mbps on average.

- Other solution :

1/24 + 1/8 = 4/24 = 1/6 (2 packets)

So 2 packets recieved 1/6 of the time.

12 packets recieved on average



=== Small ex 2 s 58

There are 4 failures for the bit rate of 11 despite 16 tries, that's because for each packet, we try 4 times before dropping it. That means if all fails, you have 4x more tries than fails.

After 4 fails, the bit rate is lowered.


==== For the 2nd destination:

The bit rate of 11 has a to try twice before the packet is acknowledged, so there is a need of 2 packets to effectively transmit 1. As such, the effective bit rate is: $11/2= 5.5$. And for the bit rate of 5.5, the effective bit rate is: $5.5 dot 46/50$, which is slightly worse than the one above. That is why the higher bit rate is better despite lower ack rate.



Cumulative Fraction of Links (CDF : Cumulative Distribution Function of the links = fonction de répartition)



== Wifi Based Indoor Localisation
GPS is paid by the US gov. So we need to scale the GPS to work indoors: Possible solution use wifi.

Using signal power to determine the position is not efficient: *We will have difficulties due to the numerous walls.*

Using the time of flight: *at these distances, a slight error leads to big localisation differences*
And also, in case of multiple paths, longer paths can lead to 

TWR: Two Way Ranging

$"ToF" = ((t_4 - t_1) - (t_3 - t_2))/2$

= IoT 

== What is IOT
Bluetooth uses frequency hopping - freq changed every slot
channel access ; TDD (1 master(odd-numbered slot) for up tp 7 slaves(even-numbered slot)). The freq hopping pattern is determined by the master

1. inquiry
2. paging


== Next gen IoT







