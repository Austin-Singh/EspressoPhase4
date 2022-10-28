// BinaryExpr3.java
// ----------------
// Error msg:  "BinaryExpr3.java:11: Operator '||' requires operands of boolean type."

public class BinaryExpr3 {
    void main() {
	int a;
	boolean b;
	
	a = 21; // this assignment is ok
	if ( (a != 2) || foo() ) a = 1;  // this assignment is not ok
    }

    void foo()
    {
	int ab;
	ab = 2;
    }
}
