#!/bin/sh

ip route del default

ip route add default via 120.0.19.10

# Adresse IP du réseau source
SOURCE_SUBNET="192.0.30.0/24"

# Interface réseau utilisée pour la sortie (vers internet)
OUT_INTERFACE="eth1"

# Activer l'IP forwarding
sysctl -w net.ipv4.ip_forward=1

# Ajouter une règle iptables pour masquer les IPs sortantes avec MASQUERADE
iptables -t nat -A POSTROUTING -s "$SOURCE_SUBNET" -o "$OUT_INTERFACE" -j MASQUERADE

# Afficher les règles NAT configurées pour vérification
#iptables -t nat -L -n -v

# Garder le script en exécution (utile pour les conteneurs Docker)
tail -f /dev/null
