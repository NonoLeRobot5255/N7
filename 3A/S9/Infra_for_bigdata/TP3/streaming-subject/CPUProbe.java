import java.io.*;
import java.net.*;
import java.util.*;

public class CPUProbe {

    static final int PORT = 9999;
    static final int NODES = 5;

    // Base CPU load (%)
    static final float[] base = {
        10, 20, 30, 40, 50
    };

    // Overload frequency (seconds): 1, 2 or 3 minutes
    static final int[] frequence = {
        60, 120, 180, 60, 120
    };

    // Overload amplitude (%)
    static final float[] amplitude = {
        40, 50, 30, 40, 30
    };

    // Overload duration (seconds)
    static final int DURATION = 30;
    static final int RISE_TIME = 10;

    // Random noise: +/- 10%
    static final float NOISE = 10;

    public static void main(String args[]) {

        Random rand = new Random();
        int tick = 0;

        try (ServerSocket ss = new ServerSocket(PORT)) {

            while (true) {

                try (Socket s = ss.accept()) {

                    System.out.println("received connection");

                    PrintWriter pw = new PrintWriter(
                        s.getOutputStream(), true);

                    while (true) {

                        for (int i = 0; i < NODES; i++) {

                            float cpu = base[i];

                            // Position in the overload cycle
                            int phase = tick % frequence[i];

                            // First overload after 'frequence[i]' seconds
                            if (tick >= frequence[i] && phase < DURATION) {

                                if (phase < RISE_TIME) {
                                    // Progressive increase
                                    cpu += amplitude[i] *
                                           phase / RISE_TIME;
                                } else {
                                    // Progressive decrease
                                    cpu += amplitude[i] *
                                           (DURATION - phase) /
                                           (DURATION - RISE_TIME);
                                }
                            }

                            // Add random noise
                            cpu += (rand.nextFloat() - 0.5f) * 2 * NOISE;

                            // Keep CPU load between 0 and 100
                            cpu = Math.max(0, Math.min(100, cpu));

                            pw.printf(Locale.US,
                                "node%d %.2f%n", i, cpu);
                        }

                        if (pw.checkError()) {
                            break;
                        }

                        Thread.sleep(1000);
                        tick++;
                    }
                }
            }

        } catch (IOException e) {
            e.printStackTrace();
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
        }
    }
}
