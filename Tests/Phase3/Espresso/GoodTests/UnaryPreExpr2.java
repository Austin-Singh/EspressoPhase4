// UnaryPreExpr2.java
// ------------------
// Error msg:  "UnaryPreExpr2.java:15: Cannot apply operator '!' to something of type int."

public class UnaryPreExpr2 {
    void mm() {
	int aa;
	aa++;
    }

    void main() {
	int a;
	boolean b;
	
	a = !a;   // the problem is here
    }
}
