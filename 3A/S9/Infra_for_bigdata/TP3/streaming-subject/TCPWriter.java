import java.io.*;
import java.net.*;
import java.util.*;

import org.apache.spark.api.java.JavaPairRDD;

public class TCPWriter {

    public static void write(
            JavaPairRDD<String, Float> rdd,
            String type,
            long timestamp) {

        try (Socket socket = new Socket("localhost", 9998);
             PrintWriter pw = new PrintWriter(
                 socket.getOutputStream(), true)) {

            for (scala.Tuple2<String, Float> t : rdd.collect()) {
                pw.printf(Locale.US, "%s %s %.2f %.3f%n",
                    type, t._1, t._2, timestamp / 1000.0);
            }

            if (pw.checkError()) {
                System.err.println("TCP display write failed");
            }

        } catch (IOException e) {
            System.err.println("Display server unavailable: "
                               + e.getMessage());
        }
    }
}