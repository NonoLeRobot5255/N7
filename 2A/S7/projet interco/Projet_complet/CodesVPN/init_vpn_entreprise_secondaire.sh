#!/bin/sh

# Configuration du tunnel GRE
ip tunnel add tnl1 mode gre local 120.0.21.30 remote 120.0.21.20
ip link set dev tnl1 up
ip a a 10.0.0.3/24 dev tnl1
ip route add 120.0.22.0/24 via 10.0.0.2 dev tnl1
