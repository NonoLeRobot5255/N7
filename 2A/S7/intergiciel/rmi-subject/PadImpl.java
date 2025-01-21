import java.rmi.*;
import java.rmi.server.UnicastRemoteObject;
import java.util.List;
import java.util.ArrayList;


public class PadImpl extends UnicastRemoteObject implements Pad {

    private List<RRecord> records = new ArrayList<RRecord>();


    public PadImpl() throws RemoteException {
        super();
    }
    
    
    public void add(SRecord sr) throws RemoteException {
        try {
            records.add(new RRecordImpl(sr.getName(), sr.getEmail()));
        } catch (Exception e) {
            System.out.println("Erreur lors de l'ajout");
        }
    }


    public RRecord consult(String n, boolean forward) throws RemoteException{
        try {
            for (RRecord record : records) {
                if (record.getName().equals(n)) {
                    return record;
                }
            }
        } catch (Exception e) {
            System.out.println("Erreur lors de la consultation");
        }
        return null;
    }


}