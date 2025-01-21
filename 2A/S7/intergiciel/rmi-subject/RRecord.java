import java.rmi.*;

public interface RRecord extends Remote {
	public String getName () throws RemoteException;
	public String getEmail () throws RemoteException;
}



