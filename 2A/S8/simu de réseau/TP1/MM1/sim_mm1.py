import subprocess
import os

# Paramètres de simulation (en format float)
lambda_val = 20.0
mu = 33.0
duration = 710.8  # sec

print("Lancement de la simulation")
subprocess.run(["ns", "mm1.tcl", str(lambda_val), str(mu), str(duration)], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

print("Traitement du temps de reponse (tr)")
os.chdir("trace_Response")
subprocess.run(["perl", "response.pl", "../out_mm1.tr", "1"], stdout=open("response.out", "w"))
subprocess.run(["perl", "avr_response.pl", "response.out"], stdout=open("avr_response.out", "w"))

# Affichage entete (pour decrire les champs resultats)
print(f"{'nb_pkt':>10}{'tr_instant':>13}{'tr_mean':>13}{'int_conf':>13}{'borne_inf':>13}{'borne_sup':>13}")
# Affichage resultat moyen tr (la derniere valeur calculee est la meilleure estimation du tr)
subprocess.run("tail -1 avr_response.out | cut -c14-", shell=True)

os.chdir("..")

print("Traitement de la taille des files d'attente (fa)")
os.chdir("trace_Length")
subprocess.run(["perl", "length.pl", "../out_mm1.tr", "1"], stdout=open("length.out", "w"))

# Affichage entete (pour decrire les champs resultats)
print(f"{'':>10}{'fa_instant':>13}{'fa_mean':>13}{'int_conf':>13}{'borne_inf':>13}{'borne_sup':>13}")
# Affichage resultat moyen taille des fa (la derniere valeur calculee est la meilleure estimation de la taille des fa)
subprocess.run("tail -1 length.out | cut -c14-", shell=True)

os.chdir("..")

print("Affichage des graphes tr & fa")
subprocess.run(["./trace_Length/plot.sh", str(duration), "M/M/1"])
subprocess.run(["./trace_Response/plot.sh", str(duration), "M/M/1"])
