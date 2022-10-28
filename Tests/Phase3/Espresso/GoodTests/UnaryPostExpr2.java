// UnaryPostExpr2.java
// -------------------
// Error msg:  "UnaryPostExpr2.java:15: Variable expected, found value."

public class Assignment1 {
    void mm() {
	int aa;
	aa++;
    }

    void main() {
	int a;
	boolean b;
	
	a = 5++;   // the problem is here
    }
}
