public class SRecordImpl implements SRecord {
    
    private String name;
    private String email;
    
    public SRecordImpl(String name, String email) {
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
