#!/bin/bash

# Créer un environnement virtuel nommé "tpGraphes"
python -m venv tpGraphes

# Activer l'environnement virtuel
source tpGraphes/bin/activate

# Mettre à jour pip
pip install --upgrade pip

# Installer Manim et ses dépendances
pip install manim

# Installer Jupyter Notebook et ses dépendances
pip install notebook

# Installer le kernel MATLAB pour Jupyter
pip install jupyter-matlab-proxy

# Désactiver l'environnement virtuel
deactivate

echo "Configuration terminée. Pour activer l'environnement virtuel, utilisez 'source tpGraphes/bin/activate'."

