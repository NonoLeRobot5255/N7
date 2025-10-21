#!/bin/sh

# Activer le forwarding IP
echo 1 > /proc/sys/net/ipv4/ip_forward

# Configuration du tunnel GRE
ip tunnel add tnl1 mode gre local 120.0.21.20 remote 120.0.21.30
ip link set dev tnl1 up
ip addr add 10.0.0.2/24 dev tnl1  # Spécifier correctement le masque

# Route pour atteindre le réseau 120.0.23.0/24 via le tunnel
ip route add 120.0.23.0/24 via 10.0.0.3 dev tnl1

# Garde le conteneur actif
sleep infinity
