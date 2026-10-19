
import java.util.Arrays;

import org.apache.spark.SparkConf;

import org.apache.spark.api.java.JavaRDD;
import org.apache.spark.api.java.JavaSparkContext;

public class TempSuperieur {
    public static void main(String[] args) {
        String inputFile = "meteosample.txt";
        String outputFile = "result";
        SparkConf conf = new SparkConf().setAppName("MaxTemperature");
        JavaSparkContext sc = new JavaSparkContext(conf);
        long t1 = System.currentTimeMillis();
        JavaRDD<String> temperatures = sc.textFile(inputFile).filter(ligne -> {
            String[] parts = ligne.split(" : ");
            return Integer.parseInt(parts[3]) > 20;

        });
        long counts = temperatures.count();
        JavaRDD<String> outputRdd = sc
                .parallelize(Arrays.asList("Total mois > " + 20 + " : " + counts));
        outputRdd.saveAsTextFile(outputFile);
        long t2 = System.currentTimeMillis();
        System.out.println("======================");
        System.out.println("time in ms :" + (t2 - t1));
        System.out.println("======================");
    }
}
