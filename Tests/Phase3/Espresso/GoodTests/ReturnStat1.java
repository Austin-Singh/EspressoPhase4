// ReturnStat1.java
// ----------------
// Error msg:  "ReturnStat1.java:8: Return statement of a void function cannot return a value."

public class Assignment1 {

    void add(int a, int b) {
	return a+b;
    }

    void main() {
	int a,b,c;
	
	c = add(a,b);  // the problem is here
    }
}
