//(1)
//#9: DD( ) has private access in 'DD'.
public class DD {
    private DD() { }
}

public class EE {
    public void foo() {
	DD dd = new DD();
    }
}