import java.util.Arrays;

import org.apache.spark.SparkConf;
import org.apache.spark.api.java.JavaPairRDD;
import org.apache.spark.api.java.JavaRDD;
import org.apache.spark.api.java.JavaSparkContext;

import scala.Tuple2;

public class MaxTemperature {
    public static void main(String[] args) {
        String inputFile = "meteosample.txt";
        String outputFile = "result";
        SparkConf conf = new SparkConf().setAppName("MaxTemperature");
        JavaSparkContext sc = new JavaSparkContext(conf);
        long t1 = System.currentTimeMillis();
        JavaPairRDD<String, Integer> temperatures = sc.textFile(inputFile).mapToPair(ligne -> {
            String[] parts = ligne.split(" : ");
            return new Tuple2<String, Integer>(parts[2], Integer.parseInt(parts[3]));
        });
        JavaPairRDD<String, Integer> counts = temperatures.reduceByKey((c1, c2) -> Math.max(c1, c2));
        counts.saveAsTextFile(outputFile);
        long t2 = System.currentTimeMillis();
        System.out.println("======================");
        System.out.println("time in ms :" + (t2 - t1));
        System.out.println("======================");
    }
}
