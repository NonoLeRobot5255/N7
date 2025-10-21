#!/bin/sh

# Activer le forwarding IP
echo 1 > /proc/sys/net/ipv4/ip_forward

# Routage
ip route del default
ip route add default via 120.0.19.10
