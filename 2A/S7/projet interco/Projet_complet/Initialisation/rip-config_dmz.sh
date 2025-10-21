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
 network 192.0.2.0/24
!
log stdout
EOF

# Redémarrer les services FRR pour appliquer la configuration
service frr start

ip route add default via 192.0.2.6

# Garde le conteneur actif
sleep infinity
