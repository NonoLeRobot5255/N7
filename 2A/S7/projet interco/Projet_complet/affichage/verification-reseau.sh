#!/bin/bash

# Fichier de sortie
output_file="rapport-architecture.txt"

# Effacer le contenu du fichier s'il existe déjà
> "$output_file"

# Fonction pour lister les réseaux, subnets et conteneurs connectés
echo "Liste des réseaux Docker et leurs détails :" >> "$output_file"
echo "-------------------------------------------" >> "$output_file"

# Boucle sur chaque réseau Docker
docker network ls --format "{{.Name}}" | while read -r network_name; do
  echo "Réseau : $network_name" >> "$output_file"
  
  # Obtenir les détails du réseau (dont le subnet)
  subnet=$(docker network inspect "$network_name" --format '{{(index .IPAM.Config 0).Subnet}}')
  echo "  Subnet : $subnet" >> "$output_file"
  
  # Liste des conteneurs dans ce réseau
  echo "  Conteneurs connectés :" >> "$output_file"
  docker network inspect "$network_name" --format '{{range .Containers}}{{.Name}}: {{.IPv4Address}}{{"\n"}}{{end}}' | while read -r container_info; do
    # Vérification pour éviter les lignes vides
    [ -n "$container_info" ] && echo "    - $container_info" >> "$output_file"
  done

  echo "" >> "$output_file"
done

# Message de fin
echo "Rapport généré dans le fichier : $output_file"
