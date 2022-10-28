public interface INTERFACE10 {
    boolean bar(int a, int b, boolean q);
}
public interface INTERFACE11 {}
public interface INTERFACE1 {}
public interface INTERFACE2 extends INTERFACE10, INTERFACE11 {}

public abstract class SUPERCLASS {
  abstract int bar(int aa, int bb, boolean z);
}


public abstract class CLASS extends SUPERCLASS implements INTERFACE1, INTERFACE2 {
    abstract void foo();
    abstract int bar(int aa, int bb, boolean z);

    void bar(int aa) {
	int a;
	a = 9;
    }

}
