// Output:
// Result: 49950

class Main {
    int main() {
	int c = 0;
	for (int i=0; i<100; i++) {
	    for (int j=0; j<100; j=j+1, j=j-1, j++) {
		int k = 10;
		while (k > 0) {
		    k = (k--) - 1;
		    c = c - k;
		}
		c = c + j;
	    }
	    c=c+i;
	}
	return c;
    }
}
