# import numpy as np

import matplotlib.pyplot as plt


def plot_rejet(lines):    
    #print(data)
    print(lines)
    x_rej = []
    y1_rej = []
    y2_rej = []
    
    x_rej, y1_rej, y2_rej = zip(*[map(float, line.split(" ")) for line in lines])


    # Plot the data
    plt.xlabel("k")
    plt.ylabel("P[rejet]")
    plt.yscale("log")
    plt.plot(x_rej, y1_rej, label="Analytique")
    plt.plot(x_rej, y2_rej, label="Simulation")
    plt.legend()

    # Save the plot to a file
    plt.savefig("out.png")

    # Show the plot
    plt.show()
    
"""
if (__name__ == "__main__"):
    data = "1\t0.377358490566038\t1\n2\t0.186133085155886\t0.142045454545455 +3\t0.101372327888795\t0.0625\n4\t0.0578816544457995\t0.0170454545454545\n5\t0.0338909047328468\t0.00568181818181818\n6\t0.0201265442063919\t0\n7\t0.0120509097207096\t0\n8\t0.00725062610912116\t0\n9\t0.00437509329904079\t0\n10\t0.00264455945738175\t0\n11\t0.00160019856795465\t0\n12\t0.000968877679563206\t0\n13\t0.000586853993834798\t0\n14\t0.000355542631649355\t0\n15\t0.000215433961025397\t0\n16\t0.000130548991720608\t0\n17\t7.91143414685446e-05\t0\n18\t4.79457868298142e-05\t0\n19\t2.90572082782425e-05\t0\n20\t1.76101191377836e-05\t0"
    plot_rejet(data)
"""

