// THe purpose here is to test assignments, in particular
// the x= operators, like += etc.
// this file should type check.
public class Assign {
    
    public int main() {
	int i1 = 0;
	int i2 = 0;
	boolean b1 = false;
	boolean b2 = true;
	float f1 = 0.00f;
	float f2 = 0;
	
	i1 += 1;
	i1 >>= 2;
	i1 >>= 1;
	b1 &= b2;
	i1 &= i2 >>=6;
	//i1 += f1;
	//i1 = f2;
	f2 = i1;
	i1 &= i2;
	return 0;
    }
}
