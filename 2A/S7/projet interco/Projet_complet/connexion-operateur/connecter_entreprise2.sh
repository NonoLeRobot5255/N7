#!/bin/bash

# Vérifier si un paramètre a été fourni
if [ -z "$1" ]; then
    echo "Aucun paramètre spécifié. Veuillez fournir le nom du conteneur."
    exit 1
fi

# Conteneur passé en paramètre
container_name=$1

# Connecter le conteneur au réseau projet_reseau_net_routeur_acces_entreprises_2
docker network connect projet_reseau_net_routeur_acces_entreprises_2 $container_name

# Vérifier si la connexion a réussi
if [ $? -eq 0 ]; then
    echo "Conteneur $container_name connecté au réseau projet_reseau_net_routeur_acces_entreprises_2"
else
    echo "Échec de la connexion du conteneur $container_name au réseau."
fi
