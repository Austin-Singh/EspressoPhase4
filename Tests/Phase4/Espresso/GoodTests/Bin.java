//Output:
// 6
// 10
// 21
// Result:0
import System;

class Bin {
    int b(int n, int m) {
	if ((m<0) || (n<m))
	    return -1;
	if ((m==0) || (n==m))
	    return 1;
	return b(n-1,m)+b(n-1,m-1);
    }
}


class Main {
    int main() {
	Bin bin = new Bin();
	System.out.println(bin.b(4,2));
	System.out.println(bin.b(5,3));
	System.out.println(bin.b(7,2));
    }
}
