#!/usr/bin/bash

fichident="IDENT.txt"
filename="rendu"
fichiers=("liste_noeud.h" "liste_noeud.c" "dijkstra.h" "dijkstra.c" "${fichident}")
td=""

demander_td() {
    first=1
    while [[ "$td" != "AB" && "$td" != "CD" && "$td" != "EF" && "$td" != "GH" && "$td" != "IJ" && "$td" != "KL" ]]; do
        if [[ $first -eq 0 ]]; then
            echo "Erreur : le groupe de TD est invalide"
        else
            first=0
        fi
        echo -n "Groupe de TD : "
        read td
        td=${td^^}
    done
}

oui_non() {
    choix=""
    while [[ $choix != "oui" && $choix != "non" ]]; do
        if [[ $choix != "" ]]; then
            echo "Erreur : réponse attendue = oui ou non"
        fi

        echo -n "$1 [oui/non]"
        read choix
        choix=${choix,,}
    done

    if [[ $choix == "oui" ]]; then
        return 0
    else
        return 1
    fi
}

demander_infos() {
    if [[ -f ${fichident} ]]; then
        echo "Un fichier d'identification existe déjà dans le répertoire."
        echo "Voici son contenu :"
        cat ${fichident}
        oui_non "Voulez-vous le conserver et continuer ?"

        if [[ $? -eq 0 ]]; then
            return 0
        fi
    fi

    echo "Configuration de l'archive de rendu"
    echo "Merci de suivre les étapes suivantes"
    ok=1
    while [[ $ok -eq 1 ]]; do
        demander_td
        echo "Membres du binômes :"
        echo -n "  NOM 1 : "
        read nom1
        nom1=$(echo ${nom1^^} | sed -e 's/^(\s)*//' -e 's/(\s)*$//' -e 's/  / /g')
        echo -n "  Prénom 1 : "
        read prenom1
        prenom1=$(echo $prenom1 | sed -e 's/^(\s)*//' -e 's/(\s)*$//' -e 's/  / /g')
        echo -n "  NOM 2 (laisser vide si pas de binôme) : "
        read nom2
        nom2=$(echo ${nom2^^} | sed -e 's/^(\s)*//' -e 's/(\s)*$//' -e 's/  / /g')
        echo -n "  Prénom 2 (laisser vide si pas de binôme) : "
        read prenom2
        prenom2=$(echo $prenom2 | sed -e 's/^(\s)*//' -e 's/(\s)*$//' -e 's/  / /g')

        echo ""
        echo "Voici le résumé de ce que vous avez rentré : "
        echo "  Membre 1 : $nom1 $prenom1, Membre 2 : $nom2 $prenom2, Groupe : $td"
        
        oui_non "Est-ce correct ?"
        ok=$?
    done

    echo "Constitution du fichier d'identification"
    echo "Horodatage : $(date)" > ${fichident}
    echo "Groupe : $td" > ${fichident}
    echo "NOM 1 : $nom1" > ${fichident}
    echo "Prénom 1 : $prenom1" > ${fichident}

    if [[ $nom2 != "" ]]; then
        echo "NOM 2 : $nom2" > ${fichident}
        echo "Prénom 2 : $prenom2" > ${fichident}
    fi

    return 0
}

check_existance () {
    if [ ! -f "$2" ]; then
        echo "Erreur : il manque le fichier $2 !"
        return 1
    else
        return $1
    fi
}

demander_infos

err=0
for f in ${fichiers[@]}; do
    check_existance $err $f
    err=$?
done

if [ $err -eq 0 ]; then
    num=($(sed -E '/^Nom\s*[[:digit:]]\s*:\s*([[:alpha:]].*)$/!d' < "${fichident}" | wc -l))
    hdt=($(sed -E '/^Horodatage/!d' < "${fichident}" | wc -l))

    if [ $num -lt 1 || $hdt -ne 1 ]; then
        echo "Erreur : le fichier d'identification n'est pas conforme"
        err=2
    fi
fi

if [ $err -ne 0 ]; then
    echo "Interruption du script"
    exit -1
fi

if [ -e "${filename}" ]; then
    rm -rf "${filename}"
fi

echo "Création de l'archive ${filename}.tar.gz"
tar zcvf "${filename}.tar.gz" "${fichiers[@]}"

if [ -f "${filename}.tar.gz" ]; then
    echo "Le fichier ${filename}.tar.gz a bien été créé."
    echo "Vous pouvez le déposer sur Moodle !"
else
    echo "Le fichier ${filename}.tar.gz n'a pas pu être créé :("
    exit -1
fi



