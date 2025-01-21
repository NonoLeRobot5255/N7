public class RRecordImpl implements  RRecord {
    
    private String name;
    private String email;
    
    public RRecordImpl(String name, String email) {
        this.name = name;
        this.email = email;
    }
    
    public String getName() {
        return name;
    }
    
    public String getEmail() {
        return email;
    }
    
}
