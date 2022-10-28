// BinaryExpr2.java
// ----------------
// Error msg:  "BinaryExpr2.java:11: Operator '!=' requires operands of the same type."

public class BinaryExpr2 {
    void main() {
	int a;
	boolean b;
	
	a = 21; // this assignment is ok
	if (a != foo()) a = 1;  // this assignment is not ok
    }

    void foo()
    {
	int ab;
	ab = 2;
    }
}
