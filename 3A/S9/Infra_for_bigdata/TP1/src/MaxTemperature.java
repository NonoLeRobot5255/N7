import java.io.IOException;
import org.apache.hadoop.conf.Configuration;
import org.apache.hadoop.fs.Path;
import org.apache.hadoop.io.IntWritable;
import org.apache.hadoop.io.Text;
import org.apache.hadoop.mapreduce.Job;
import org.apache.hadoop.mapreduce.Mapper;
import org.apache.hadoop.mapreduce.Reducer;
import org.apache.hadoop.mapreduce.lib.input.FileInputFormat;
import org.apache.hadoop.mapreduce.lib.output.FileOutputFormat;

public class MaxTemperature {
    public static class TokenizerMapper extends Mapper<Object, Text, Text, IntWritable> {

        private Text yearText = new Text();
        private IntWritable tempWritable = new IntWritable();

        public void map(Object key, Text value, Context context)
                throws IOException, InterruptedException {
            String tokens[] = value.toString().split(":");
            String annee = tokens[2];
            int temp = Integer.parseInt(tokens[3].trim());
            yearText.set(annee);
            tempWritable.set(temp);

            context.write(yearText, tempWritable);
        }
    }

    public static class IntSumReducer extends Reducer<Text, IntWritable, Text, IntWritable> {
        private IntWritable result = new IntWritable();

        public void reduce(Text key, Iterable<IntWritable> values, Context context)
                throws IOException, InterruptedException {
            int max = Integer.MIN_VALUE;
            for (IntWritable val : values) {
                max = Math.max(max, val.get());
            }
            result.set(max);
            context.write(key, result);
        }
    }

    public static void main(String[] args) throws Exception {
        Configuration conf = new Configuration();
        Job job = Job.getInstance(conf, "word count");
        job.setJarByClass(WordCount.class);
        job.setMapperClass(TokenizerMapper.class);
        job.setCombinerClass(IntSumReducer.class);
        job.setReducerClass(IntSumReducer.class);
        job.setOutputKeyClass(Text.class);
        job.setOutputValueClass(IntWritable.class);
        FileInputFormat.addInputPath(job, new Path(args[0]));
        FileOutputFormat.setOutputPath(job, new Path(args[1]));
        long t1 = System.currentTimeMillis();
        int res = job.waitForCompletion(true) ? 0 : 1;
        long t2 = System.currentTimeMillis();
        System.out.println("time in ms =" + (t2 - t1));
        System.exit(res);
    }
}