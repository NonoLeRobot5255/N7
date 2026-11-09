
hdfs dfs -rm /output/*
hdfs dfs -rmdir /output
spark-submit --class WordCount --master spark://master:7077 wc.jar hdfs://master:9000/input hdfs://master:9000/output
