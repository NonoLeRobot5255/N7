import numpy as np
import matplotlib.pyplot as plt
import csv
from scipy.optimize import curve_fit

# Read CSV data
csv_file = 'mesure_RSSI - Feuille 1.csv'
distances = []
rssi_values = []
with open(csv_file, 'r') as f:
    reader = csv.reader(f)
    for row in reader:
        if len(row) == 2:
            distances.append(float(row[0]))
            rssi_values.append(float(row[1]))

distances = np.array(distances)
rssi_values = np.array(rssi_values)

# Theoretical curve from plot.py
x_theory = np.linspace(1, 220, 500)
y_theory = -12.30 * np.log(x_theory) - 9.67


plt.figure(figsize=(8, 5))
plt.scatter(distances, rssi_values, color='red', label='Measured Data')
plt.plot(x_theory, y_theory, label=r"$-12.30 \cdot \ln(distance) - 9.67$", color='blue')
plt.xlabel('Distance (cm)')
plt.ylabel('RSSI (dBm)')
plt.title('RSSI vs Distance (cm)')
plt.legend()
plt.grid(True)
plt.tight_layout()
plt.show()