// UnaryPreExpr3.java
// ------------------
// Error msg:  "UnaryPreExpr3.java:15: Cannot apply operator '~' to something of type boolean."

public class UnaryPreExpr3 {
    void mm() {
	int aa;
	aa++;
    }

    void main() {
	int a;
	boolean b;
	
	a = ~b;   // the problem is here
    }
}
