public class Integer {
    private int value; 
    
    public Integer(int value) { 
	this.value = value;
    }
    
    public Integer(String s) { 
	this.value = java.lang.Integer.parseInt(s);
    }

    public static int parseInt(String s) { 
	return java.lang.Integer.parseInt(s);
    }
}