#!/usr/bin/env python3
# filepath: /home/nono/Documents/Ecole/N7/2A/S8/reseau_sans_fil/TP/plot.py

import matplotlib.pyplot as plt
import csv
import re
import os
import sys

# Function to parse the CSV file and extract data for two datasets
def parse_csv(filename):
    x_values1 = []
    y_values1 = []
    x_values2 = []
    y_values2 = []
    
    try:
        with open(filename, 'r') as csvfile:
            lines = csvfile.readlines()
            
            # Skip the header line if it contains filepath
            start_idx = 0
            if lines and "filepath" in lines[0]:
                start_idx = 1
            
            # Skip the first data point (it's an outlier)
            start_idx += 1
            
            for line in lines[start_idx:]:
                line = line.strip()
                if line:
                    # Extract two pairs of values
                    # Format: "x1,xxx  y1,yyy","x2,xxx  y2,yyy"
                    pairs = line.split('","')
                    
                    # Process first dataset
                    if len(pairs) > 0:
                        # Clean up the first pair (remove leading quote)
                        pair1 = pairs[0].lstrip('"')
                        match1 = re.search(r'(\d+,\d+)\s+(\d+,\d+)', pair1)
                        if match1:
                            # Convert European format (comma as decimal separator) to float
                            x_str1 = match1.group(1).replace(',', '.')
                            y_str1 = match1.group(2).replace(',', '.')
                            
                            x_values1.append(float(x_str1))
                            y_values1.append(float(y_str1))
                    
                    # Process second dataset
                    if len(pairs) > 1:
                        # Clean up the second pair (remove trailing quote)
                        pair2 = pairs[1].rstrip('"')
                        match2 = re.search(r'(\d+,\d+)\s+(\d+,\d+)', pair2)
                        if match2:
                            # Convert European format (comma as decimal separator) to float
                            x_str2 = match2.group(1).replace(',', '.')
                            y_str2 = match2.group(2).replace(',', '.')
                            
                            x_values2.append(float(x_str2))
                            y_values2.append(float(y_str2))
    except Exception as e:
        print(f"Error parsing file: {e}")
    
    print(f"Extracted {len(x_values1)} data points for dataset 1 from {filename}")
    print(f"Extracted {len(x_values2)} data points for dataset 2 from {filename}")
    
    return x_values1, y_values1, x_values2, y_values2

# Main function
def main():
    # Use the provided CSV file or default to res.csv
    csv_file = 'res.csv'
    if len(sys.argv) > 1:
        csv_file = sys.argv[1]
    
    # Parse the CSV file
    x_values1, y_values1, x_values2, y_values2 = parse_csv(csv_file)
    
    if not x_values1 or not y_values1:
        print("No data to plot for dataset 1. Exiting.")
        return
    
    # Create a plot with improved styling
    plt.figure(figsize=(14, 10))
    
    # Plot both datasets - CORRECTED LABELS
    plt.plot(x_values1, y_values1, 'b-o', linewidth=2.5, markersize=6, alpha=0.8, 
             label='Without RTS/CTS')
    
    if x_values2 and y_values2:
        plt.plot(x_values2, y_values2, 'r-s', linewidth=2.5, markersize=6, alpha=0.8, 
                 label='With RTS/CTS (RTSThreshold = 100)')
    
    # Calculate average values for annotation
    if y_values1:
        avg_y1 = sum(y_values1) / len(y_values1)
        plt.axhline(y=avg_y1, color='b', linestyle='--', alpha=0.5)
        plt.annotate(f'Avg: {avg_y1:.4f} Mbps', xy=(x_values1[-1], avg_y1),
                    xytext=(x_values1[-1] + 2, avg_y1 + 0.02),
                    arrowprops=dict(facecolor='blue', shrink=0.05, alpha=0.5),
                    fontsize=10)
    
    if y_values2:
        avg_y2 = sum(y_values2) / len(y_values2)
        plt.axhline(y=avg_y2, color='r', linestyle='--', alpha=0.5)
        plt.annotate(f'Avg: {avg_y2:.4f} Mbps', xy=(x_values2[-1], avg_y2),
                    xytext=(x_values2[-1] + 2, avg_y2 - 0.04),
                    arrowprops=dict(facecolor='red', shrink=0.05, alpha=0.5),
                    fontsize=10)
    
    # Add labels and title with better formatting
    plt.xlabel('Time (seconds)', fontsize=14, fontweight='bold')
    plt.ylabel('Throughput (Mbps)', fontsize=14, fontweight='bold')
    plt.title('Hidden Terminal Problem: Performance Comparison\nWith and Without RTS/CTS Mechanism', 
              fontsize=18, fontweight='bold', pad=20)
    
    # Add a grid and customize its appearance
    plt.grid(True, linestyle='--', alpha=0.7)
    
    # Add minor grid lines
    plt.minorticks_on()
    plt.grid(which='minor', linestyle=':', alpha=0.4)
    
    # Set y-axis limits to better visualize the data
    y_min = min(min(y_values1), min(y_values2)) * 0.9 if y_values2 else min(y_values1) * 0.9
    y_max = max(max(y_values1), max(y_values2)) * 1.1 if y_values2 else max(y_values1) * 1.1
    plt.ylim(y_min, y_max)
    
    # Add legend with better formatting
    plt.legend(fontsize=12, loc='lower right', framealpha=0.8, edgecolor='black')
    
    # Add text explaining the setup
    plt.figtext(0.12, 0.02, 
                "NS-2 Simulation of Hidden Terminal Problem\nFrom hiddenTerminal.tcl", 
                fontsize=10, ha='left')
    
    # Add a box with statistics - CORRECTED LABELS
    stats_text = f"""
    Statistics:
    Without RTS/CTS: Min={min(y_values1):.4f}, Max={max(y_values1):.4f}, Avg={avg_y1:.4f} Mbps
    With RTS/CTS: Min={min(y_values2):.4f}, Max={max(y_values2):.4f}, Avg={avg_y2:.4f} Mbps
    Improvement: {(avg_y2-avg_y1)*100/avg_y1:.2f}%
    """ if y_values2 else ""
    
    plt.figtext(0.7, 0.25, stats_text, bbox=dict(facecolor='white', alpha=0.8, edgecolor='gray'), fontsize=10)
    
    # Improve the plot's appearance
    plt.tight_layout()
    
    # Save the plot as an image with higher DPI
    output_file = os.path.splitext(csv_file)[0] + '_comparison_plot.png'
    plt.savefig(output_file, dpi=300)
    print(f"Plot saved as {output_file}")
    
    # Show the plot if running in interactive mode
    plt.show()

if __name__ == "__main__":
    main()