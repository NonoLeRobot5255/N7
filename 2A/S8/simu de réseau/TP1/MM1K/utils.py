import subprocess
import os
from concurrent.futures import ThreadPoolExecutor, as_completed

import matplotlib.pyplot as plt

def run_simulation(lambda_val, mu, duration1, duration2):
    # Déplacer le répertoire de travail
    # os.chdir("MM1K")

    def run_script(script_name, duration):
        result = subprocess.run(["perl", script_name, str(lambda_val), str(mu), str(duration)], capture_output=True, text=True)
        return result.stdout

    # Utilisation de ThreadPoolExecutor pour exécuter les scripts en parallèle
    with ThreadPoolExecutor() as executor:
        futures = []
        futures.append(executor.submit(run_script, "rejet.pl", duration1))
        futures.append(executor.submit(run_script, "rejetMD1K.pl", duration2))
        results = [future.result() for future in as_completed(futures)]

    print("Capa. file\tTx analy.\tTx simu.")
    print(results[0])
    print("-----------------------")
    print(results[1])

    lines, lines2 = list(map(lambda listi : list(filter(lambda y: y.strip() != "", listi)) ,list(map(lambda x: x.replace("\t", " ").split("\n"), results))))

    # Traiter la sortie du premier script
    x_rej, y1_rej, y2_rej = zip(*[map(float, line.split(" ")) for line in lines])

    # Traiter la sortie du deuxième script
    x_rej2, y1_rej2, y2_rej2 = zip(*[map(float, line.split(" ")) for line in lines2])

    # Plot des résultats 
    plt.xlabel("Capacité K")
    plt.ylabel("Taux de rejet")
    plt.yscale("log")
    plt.title("Taux de rejet en fonction de la capacité K")
    plt.plot(x_rej, y1_rej, label="Analytique MM1K")
    plt.plot(x_rej, y2_rej, label="Simulation MM1K")
    plt.plot(x_rej2, y2_rej2, label="Simulation MD1K")
    plt.legend()
    plt.show()

    # Revenir au répertoire précédent
    # os.chdir("..")

if __name__ == "__main__":
    # Valeurs initiales
    lambda_val, mu, duration1, duration2 = 20, 33, 5000, 15000  # msec

    # Appeler la fonction avec les valeurs initiales
    run_simulation(lambda_val, mu, duration1, duration2)