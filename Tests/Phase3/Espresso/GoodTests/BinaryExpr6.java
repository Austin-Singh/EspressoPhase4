// BinaryExpr6.java
// ----------------
// Error msg:  "BinaryExpr6.java:11: Operator '>>' requires left operand of integral type."

public class BinaryExpr6 {
    void main() {
	int a;
	boolean b;
	
	a = 21;  // this assignment is ok
	a = (b >> 2);  // this assignment is not ok
    }

    void foo()
    {
	int ab;
	ab = 2;
    }
}
