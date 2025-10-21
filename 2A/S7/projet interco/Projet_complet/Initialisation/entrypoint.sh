#!/bin/bash

# Activer le routage IP
sysctl -w net.ipv4.ip_forward=1

# Démarrer Quagga
echo "Starting Quagga..."

# Activer les interfaces réseau
ip link set dev eth0 up
ip link set dev lo up

# Créer le répertoire /var/log/quagga si il n'existe pas
mkdir -p /var/log/quagga

# Supprimer les fichiers PID existants pour éviter les conflits
rm -f /run/quagga/zebra.pid
rm -f /run/quagga/ospfd.pid

# Donner les bonnes permissions aux répertoires et fichiers
chmod -R 777 /run/quagga && \
chmod 777 /run/quagga/*.pid /run/quagga/*.vty && \
chmod 777 /var/log/quagga/*.log

# Assurer que les processus ne sont pas déjà en cours
pkill zebra
pkill ospfd

# Démarrer Zebra (Quagga)
echo "Starting Zebra..."
/usr/sbin/zebra -d -f /etc/quagga/zebra.conf

# Démarrer OSPF daemon (Quagga)
echo "Starting OSPF daemon..."
/usr/sbin/ospfd -d -f /etc/quagga/ospfd.conf

# Garder le conteneur actif avec une boucle infinie ou bash
echo "Router is running. Access the container using: docker exec -it <container_name> /bin/bash"
exec /bin/bash