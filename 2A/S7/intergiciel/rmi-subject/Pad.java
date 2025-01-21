import java.rmi.*;

public interface Pad extends Remote {
	public void add(SRecord sr) throws RemoteException;
	public RRecord consult(String n, boolean forward) throws RemoteException;

	
}

