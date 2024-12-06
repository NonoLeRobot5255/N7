import java.util.Random;
import java.net.*;
import java.io.InputStream;
import java.io.OutputStream;

public class LoadBalancer extends Thread {
    static String hosts[] = { "localhost", "localhost" };
    static int ports[] = { 8081, 8082 };
    static int nbHosts = 2;
    static Random rand = new Random();
    Socket socketclient;

    public LoadBalancer(Socket s) {
        this.socketclient = s;
    }

    public static void main(String[] args) throws Exception {
        try {
            ServerSocket s = new ServerSocket(Integer.parseInt(args[0]));
            while (true) {
                Thread t = new LoadBalancer(s.accept());
                t.start();
                System.out.println("New connection");
            }
        } catch (Exception e) {
            System.out.println("Error (dans la ligne de commande) : " + e);
        }

    }

    public void run() {
        int index_server = rand.nextInt(nbHosts);
        try {
            Socket s = new Socket(hosts[index_server], ports[index_server]);
            InputStream client_in = socketclient.getInputStream();
            byte buffer[] = new byte[1024];
            int nb_read = client_in.read(buffer);
            OutputStream server_out = s.getOutputStream();
            server_out.write(buffer, 0, nb_read);
            InputStream server_in = s.getInputStream();
            byte buffer2[] = new byte[1024];
            nb_read = server_in.read(buffer2);
            OutputStream client_out = socketclient.getOutputStream();
            client_out.write(buffer2, 0, nb_read);

            client_in.close();
            client_out.close();
            server_in.close();
            server_out.close();
            s.close();
        } catch (Exception e) {
            System.out.println(e);
        }
    }

}
