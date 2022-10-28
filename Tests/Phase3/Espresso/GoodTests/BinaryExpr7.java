// BinaryExpr7.java
// ----------------
// Error msg:  "BinaryExpr7.java:11: Operator '>>' requires right operand of integral type."

public class BinaryExpr7 {
    void main() {
	int a;
	boolean b;
	
	a = 21;  // this assignment is ok
	a = (5 >> "c");  // this assignment is not ok
    }

    void foo()
    {
	int ab;
	ab = 2;
    }
}
