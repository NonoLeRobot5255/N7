
import matplotlib.pyplot as plt

def plot_response(file_name, duration, title, yerr_idx=None, confidence_intervals=None):

    data = {
        "time": [],
        "instantaneous_response_time": [],
        "average": [],
        "confidence_interval_inf": [],
        "confidence_interval_sup": []
    }
    y_max = 0.1
    y_min = 0

    with open(file_name) as f:
        for line in f:
            parts = line.split()
            if len(parts) >= 7:
                if float(parts[2]) > y_max:
                    y_max = float(parts[2])
                if float(parts[2]) < y_min:
                    y_min = float(parts[2])
                
                data["time"].append(float(parts[0]))
                data["instantaneous_response_time"].append(float(parts[2]))
                data["average"].append(float(parts[3]))
                if yerr_idx:
                    data["confidence_interval_inf"].append(float(parts[4]))
                if confidence_intervals:
                    data["confidence_interval_inf"].append(float(parts[5]))
                    data["confidence_interval_sup"].append(float(parts[6]))

    plt.figure(figsize=(10, 5))
    plt.title(title)
    plt.plot(data["time"], data["instantaneous_response_time"], "+", label="instantaneous response time")
    plt.plot(data["time"], data["average"], label="average")

    if yerr_idx:
        plt.errorbar(data["time"], data["average"], yerr=data["confidence_interval_inf"], fmt='o', label='error bars')
    if confidence_intervals:
        plt.plot(data["time"], data["confidence_interval_inf"], label="confidence interval-inf")
        plt.plot(data["time"], data["confidence_interval_sup"], label="confidence interval-sup")

    plt.xlim(0, duration)
    plt.ylim([y_min, y_max])
    plt.xlabel("Time")
    plt.ylabel("Response Time")
    plt.legend()
    plt.savefig(f"{title}.png")
    plt.show()
