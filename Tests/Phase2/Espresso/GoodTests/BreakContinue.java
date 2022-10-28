// Output: 
// Result: 12544 

class Main {
    Main() {
    }
    int main() {
	int i,a;
	a=0;
	for (i=0;i<1000;i++) {
	    if (i%2 == 0) 
	    	continue;
	    a=a+i;
	    if (a>12345)
	    	break;
	    
	}
	return a;
    }
}
