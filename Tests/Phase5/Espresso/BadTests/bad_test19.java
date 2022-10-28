//(1)
//#7: Cannot assign a value to final field 'a'.
public class I {
    public final int a = 9;
    
    public void f() {
	a = a + 1;
    }
}
