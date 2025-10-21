#!/bin/sh

echo "Initialisation des règles iptables..."

# Définir les politiques par défaut sur DROP
iptables -P INPUT DROP
iptables -P FORWARD DROP
iptables -P OUTPUT DROP

# Autoriser les connexions établies et les paquets liés
iptables -A INPUT -m state --state ESTABLISHED,RELATED -j ACCEPT
iptables -A OUTPUT -m state --state ESTABLISHED,RELATED -j ACCEPT

# --- Autorisations spécifiques ---

# Autoriser le ping (ICMP)
iptables -A INPUT -p icmp --icmp-type echo-request -j ACCEPT
iptables -A OUTPUT -p icmp --icmp-type echo-reply -j ACCEPT

# Autoriser DHCP (ports 67 et 68 en UDP)
iptables -A INPUT -p udp --sport 67 --dport 68 -j ACCEPT
iptables -A OUTPUT -p udp --sport 68 --dport 67 -j ACCEPT

# Autoriser OSPF (protocole 89 IP)
iptables -A INPUT -p 89 -j ACCEPT
iptables -A OUTPUT -p 89 -j ACCEPT

# Autoriser DNS (port 53 TCP et UDP)
iptables -A INPUT -p tcp --dport 53 -j ACCEPT
iptables -A INPUT -p udp --dport 53 -j ACCEPT
iptables -A OUTPUT -p tcp --dport 53 -j ACCEPT
iptables -A OUTPUT -p udp --dport 53 -j ACCEPT

# Autoriser HTTP et HTTPS (ports 80 et 443 TCP)
iptables -A INPUT -p tcp --dport 80 -j ACCEPT
iptables -A INPUT -p tcp --dport 443 -j ACCEPT
iptables -A OUTPUT -p tcp --dport 80 -j ACCEPT
iptables -A OUTPUT -p tcp --dport 443 -j ACCEPT

# Autoriser VPN GRE (protocole GRE, numéro 47)
iptables -A INPUT -p gre -j ACCEPT
iptables -A OUTPUT -p gre -j ACCEPT

echo "Règles iptables appliquées avec succès."
