import numpy as np
import matplotlib.pyplot as plt

distances_cm = np.linspace(1, 1000, 1000)  # from 1 cm to 1000 cm
rssi = -12.30 * np.log(distances_cm) + -66.27

plt.figure(figsize=(8, 5))
plt.plot(distances_cm, rssi, label=r"$-12.30 \cdot \ln(distance) - 66.27$")
plt.xlabel('Distance (cm)')
plt.ylabel('RSSI (dBm)')
plt.title('RSSI vs Distance (cm)')
plt.legend()
plt.grid(True)
plt.tight_layout()
plt.show()