// Enter an integer: 2
// Enter an integer: 5
// Enter an integer: 2
// Enter an integer: 100
// Output:
// 2
// 3
// 9
// 4
// 16
// 5
// 25
// Result:0

class Io {
    void out(int n) {}
    int in() {}
}
    
class Fermat {
    int n;
    int x=0,y=0,z=0;
    boolean solved = false;
    Fermat next = null;

    Fermat(int n) {
	this.n = n;
    }

    boolean isSolved() {
	return (x!=0 && y!=0 && z!=0);
    }

    int getx() {
	return x;
    }

    int gety() {
	return y;
    }
	
    int getz() {
	return z;
    }

    void setNext(Fermat next) {
	this.next = next;
    }


    int power(int x, int n) {
	if (n==0) 
	    return 1;
	else 
	    return x*power(x,n-1);
    }

    void solve(int lower, int upper) {
	solved = true;
	for (int i=lower; i<= upper; i++) 
	    for (int j=lower; j<= upper; j++) 
		for (int k=lower; k<= upper; k++) {
		    if (power(i,n)+power(j,n)==power(k,n)) {
			x=i;
			y=j;
			z=k;
			return;
		    }
		}
    }

}

class Main {
    int main() {
	int lowern=0;
	int uppern=0;
	int lower=0;
	int upper=0;
	Fermat queue = null,f;
		
	lowern = Io.readInt();
	uppern = Io.readInt();
	lower  = Io.readInt();
	upper  = Io.readInt();
	
	for (int n=lowern; n<=uppern; n++) {
	    f = new Fermat(n);
	    f.solve(lower,upper);
	    if (queue != null) 
		f.setNext(queue);
	    queue = f;	    
	}
	
	for (Fermat nf=queue; nf!=null; nf=nf.next) {
	    if (nf.isSolved()) {
		Io.println(nf.n);
		Io.println(nf.getx());
		Io.println(nf.power(nf.getx(),nf.n));
		Io.println(nf.gety());
		Io.println(nf.power(nf.gety(),nf.n));
		Io.println(nf.getz());
		Io.println(nf.power(nf.getz(),nf.n));
	    }
	}
    }
}


