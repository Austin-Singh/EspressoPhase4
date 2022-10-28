// ReturnStat2.java
// ----------------
// Error msg:  "ReturnStat1.java:8: Return statement of a void function cannot return a value."

public class Assignment1 {

    int add(int a, int b) {
	float dd;
	dd = a+b;

	return dd;
    }

    void main() {
	int a,b,c;
	
	c = add(a,b);  // the problem is here
    }
}
