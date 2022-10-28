// UnaryPreExpr1.java
// ------------------
// Error msg:  "UnaryPreExpr1.java:15: Cannot apply operator '-' to something of type boolean."

public class Assignment1 {
    void mm() {
	int aa;
	aa++;
    }

    void main() {
	int a;
	boolean b;
	
	a = -b;   // the problem is here
    }
}
