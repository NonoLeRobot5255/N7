#!/bin/bash

# Activer le forwarding IP
echo 1 > /proc/sys/net/ipv4/ip_forward


ip route del default
ip route add default via 120.0.17.10

# Garde le conteneur actif
sleep infinity