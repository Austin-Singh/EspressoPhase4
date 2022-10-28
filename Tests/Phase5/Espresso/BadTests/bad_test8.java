//(1)
//#7: Cannot assign a value to final field 'a'.
public class Y {
    public final int a = 0;
    
    public void foo(Y y) {
	y.a = 12;

    }
}
    