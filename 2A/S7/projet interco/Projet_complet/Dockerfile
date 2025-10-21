# Utiliser Ubuntu 20.04 comme image de base
FROM ubuntu:20.04

# Installer les outils nécessaires
RUN apt-get update && apt-get install -y \
    iproute2 \
    iputils-ping \
    quagga \
    net-tools \
    nano \
    && rm -rf /var/lib/apt/lists/*

# Créer les répertoires nécessaires pour les logs et PID (quagga)
RUN mkdir -p /var/log/quagga && \
    mkdir -p /run/quagga

# Donner les bonnes permissions au répertoire et aux fichiers de log
RUN chmod -R 777 /run/quagga && \
    chmod 777 /var/log/quagga

# Copier le fichier d'entrée (entrypoint.sh) dans le conteneur
COPY Initialisation/entrypoint.sh /entrypoint.sh
COPY Initialisation/securite.sh /securite.sh

# Donner les bonnes permissions au script d'entrée
RUN chmod +x /entrypoint.sh
RUN chmod +x /securite.sh

# Définir le script comme point d'entrée
ENTRYPOINT ["/entrypoint.sh", "/securite.sh"]

# Garder le conteneur actif
CMD ["/bin/bash"]