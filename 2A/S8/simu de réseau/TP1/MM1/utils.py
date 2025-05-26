import matplotlib.pyplot as plt


# calc ρ(2-ρ)/2*(1-ρ)
def calc(ρ):
    return ρ*(2-ρ)/(2*(1-ρ))


print(calc(0.3))
print(calc(0.6))
print(calc(0.9))
print("---")

print(calc(0.3)/9.9)
print(calc(0.6)/19.8)
print(calc(0.9)/29.7)

import matplotlib.pyplot as plt


# Fonction pour tracer les graphes de longueur de file d'attente
def plot_length(duration, title):
    data = {
        "time": [],
        "instantaneous_length": [],
        "average": [],
        "confidence_interval_inf": [],
        "confidence_interval_sup": []
    }

    with open("trace_Length/length.out") as f:
        for line in f:
            parts = line.split()
            if len(parts) >= 6:
                data["time"].append(float(parts[0]))
                data["instantaneous_length"].append(float(parts[1]))
                data["average"].append(float(parts[2]))
                data["confidence_interval_inf"].append(float(parts[4]))
                data["confidence_interval_sup"].append(float(parts[5]))

    plt.figure()
    plt.title(title)
    plt.plot(data["time"], data["instantaneous_length"], "+", label="instantaneous length")
    plt.plot(data["time"], data["average"], label="average")
    plt.plot(data["time"], data["confidence_interval_inf"], label="confidence interval-inf")
    plt.plot(data["time"], data["confidence_interval_sup"], label="confidence interval-sup")
    plt.xlim(0, duration)
    plt.xlabel("Time")
    plt.ylabel("Queue Length")
    plt.legend()
    plt.show()

# Fonction pour tracer les graphes de temps de réponse
def plot_response(duration, title):
    data = {
        "time": [],
        "instantaneous_response_time": [],
        "average": [],
        "confidence_interval_inf": [],
        "confidence_interval_sup": []
    }

    with open("trace_Response/avr_response.out") as f:
        for line in f:
            parts = line.split()
            if len(parts) >= 7:
                data["time"].append(float(parts[0]))
                data["instantaneous_response_time"].append(float(parts[2]))
                data["average"].append(float(parts[3]))
                data["confidence_interval_inf"].append(float(parts[5]))
                data["confidence_interval_sup"].append(float(parts[6]))

    plt.figure()
    plt.title(title)
    plt.plot(data["time"], data["instantaneous_response_time"], "+", label="instantaneous response time")
    plt.plot(data["time"], data["average"], label="average")
    plt.plot(data["time"], data["confidence_interval_inf"], label="confidence interval-inf")
    plt.plot(data["time"], data["confidence_interval_sup"], label="confidence interval-sup")
    plt.xlim(0, duration)
    plt.xlabel("Time")
    plt.ylabel("Response Time")
    plt.legend()
    plt.show()
