//(1)
//#7: Cannot assign a value to final field 'i'.
public class JJ {
    public final int i=9;

    public void foo() {
	++i;
    }
}