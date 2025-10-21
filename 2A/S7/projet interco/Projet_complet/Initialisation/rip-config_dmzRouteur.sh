#!/bin/bash

# Activer le forwarding IP
echo 1 > /proc/sys/net/ipv4/ip_forward

# Création des fichiers de configuration FRR pour RIP
cat <<EOF > /etc/frr/frr.conf
frr defaults traditional
hostname $(hostname)
service integrated-vtysh-config
!
router rip
 network 120.0.23.0/24
 network 192.0.2.0/24
 networt 120.0.18.0/29
!
log stdout
EOF

# Redémarrer les services FRR pour appliquer la configuration
service frr start

ip route add default via 120.0.23.5
ip route add 120.0.20.0/24 via 120.0.23.5


iptables -P FORWARD DROP

# Autoriser le trafic entrant dans la DMZ depuis l'extérieur (par exemple, Internet)
iptables -A FORWARD -d 192.168.2.0/24 -j ACCEPT

# Autoriser les réponses du trafic initié depuis la DMZ
iptables -A FORWARD -s 192.168.2.0/24 -m state --state ESTABLISHED,RELATED -j ACCEPT

# Autoriser l'accès restreint depuis le réseau interne vers la DMZ (par exemple, pour maintenance)
iptables -A FORWARD -s 120.0.23.0/24 -d 192.0.2.0/24 -j ACCEPT

iptables -A INPUT -p icmp --icmp-type echo-request -j ACCEPT
iptables -A OUTPUT -p icmp --icmp-type echo-reply -j ACCEPT


# Autoriser les pings ICMP depuis l'extérieur vers la DMZ
iptables -A FORWARD -p icmp --icmp-type echo-request -d 192.168.2.0/24 -j ACCEPT


#pour le dns
iptables -A FORWARD -s 192.168.2.0/24 -d 120.0.23.10 -p udp --dport 53 -j ACCEPT
iptables -A FORWARD -s 192.168.2.0/24 -d 120.0.23.10 -p tcp --dport 53 -j ACCEPT


# Garde le conteneur actif
sleep infinity
