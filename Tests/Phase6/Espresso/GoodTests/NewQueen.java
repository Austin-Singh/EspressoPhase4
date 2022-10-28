//(16)
//7
//Enter the size of the board: Solved
//+---+---+---+---+---+---+---+
//|   |   |   |   |   | Q |   |
//+---+---+---+---+---+---+---+
//|   |   | Q |   |   |   |   |
//+---+---+---+---+---+---+---+
//|   |   |   |   |   |   | Q |
//+---+---+---+---+---+---+---+
//|   |   |   | Q |   |   |   |
//+---+---+---+---+---+---+---+
//| Q |   |   |   |   |   |   |
//+---+---+---+---+---+---+---+
//|   |   |   |   | Q |   |   |
//+---+---+---+---+---+---+---+
//|   | Q |   |   |   |   |   |
//+---+---+---+---+---+---+---+
import System;

class Element {
    IntVector val;
    int       key;

    public Element() { }

    Element(IntVector val, int key) {
	this.val   = val;
	this.key   = key;
    }

}
	
class Elist {
    Elist next = null;
    Element e;
    
    Elist() { }

    Elist(int n) {
	e = null;
	if (n != 0) {
	    next = new Elist(n-1);
	}
    }

    Element get(int n) {
	if (n == 0)
	    return e;
	else
	    return next.get(n-1);
    }
    
    void put(int n, Element value) {
	if (n == 0)
	    this.e = value;
	else {
	    next.put(n-1,value);
	}
    }
}
	
class IntVector {
    int value;
    
    IntVector next_element = null;
    
    public IntVector() { }

    IntVector(int initial_size) {
	if (initial_size != 0)
	    next_element = new IntVector(initial_size - 1);
    }

    int get(int n) {
	if (n == 0)
	    return value;
	else
	    return next_element.get(n-1);
    }

    void put(int n, int value) {
	if (n == 0)
	    this.value = value;
	else {
	    if (next_element == null) {
		next_element = new IntVector(n-1);
	    }
	    next_element.put(n-1,value);
	}
    }

    int size() {
	if (next_element == null)
	    return 0;
	else 
	    return 1 + next_element.size();
    }
}
	
class IntVectorPri {

    Queue init(int n) {
	Queue q = new Queue(n);
	return q;
    }


    boolean empty(Queue Q) {
	return (Q.size == 0);
    }

    void up(Queue Q, int n) {
	int father;
	
	father = (n-1)/2;

	if ((n>0) && (Q.data.get(father).key < Q.data.get(n).key)) {
	    Element e = Q.data.get(father);
	    Q.data.put(father, Q.data.get(n));
	    Q.data.put(n, e);
	    up(Q, father);
	}
    }

    void insert(Queue Q, IntVector val, int key) {
	if (Q.size < Q.max) {
	    Q.data.put(Q.size, new Element(val, key));
	    Q.size = Q.size + 1;
	    up(Q,Q.size-1);
	}
    }

    void down(Queue Q, int n) {
	int son;
	son = 2*n + 1;
	if (son < Q.size) {
	    if (son < Q.size - 1 && Q.data.get(son+1).key < Q.data.get(son).key) 
		son ++ ;
	    if (Q.data.get(son).key < Q.data.get(n).key) {
		Element e = Q.data.get(n);
		Q.data.put(n, Q.data.get(son));
		Q.data.put(son, e);
		down(Q, son);
	    }
	}
    }
    
    Element deleteBest(Queue Q) {
	if (Q.size > 0) {
	    Element e = Q.data.get(0);
	    
	    Q.size--;
	    if (Q.size > 0) {
		Element e1 = Q.data.get(0);
		Q.data.put(0, Q.data.get(Q.size));
		Q.data.put(Q.size, null);
		down(Q,0);
	    }
	    return e;
	}
	return null;
    }
}

class Queue {
    int size;
    int max;
    Elist data;

    public Queue() { }

    Queue(int n) {
	size = 0;
	max = n;
	data = new Elist(n);
    }
}
class Main {

    public static boolean peace(IntVector k, int p) {
	int i = 1;
	while (i <= k.size()) {
	    if (k.get(k.size()-i) == p || 
		k.get(k.size()-i) == p-i ||
		k.get(k.size()-i) == p+i)
		return false;
	    i++;
	}
	return true;
    }

    public static void printBoard(int n, String r, String s) {
	for (int i=0;i<n; i++)
	    System.out.print(r);
	if (s!="")
	    System.out.println(s);
	else 
	    System.out.print(s);
    }


    public static void main(String args[]) {
	Queue Q;
	IntVectorPri PQ = new IntVectorPri();
	int n;
	boolean solved = false;
	IntVector iv = new IntVector(0);
	System.out.print("Enter the size of the board: ");
	n = System.out.readInt();
       
	Q = PQ.init(n*n*n);
	PQ.insert(Q,iv,0);

	IntVector k = null;
	while (!PQ.empty(Q) && !solved) {
	    
	    int p;
	    Element e;
	    e = PQ.deleteBest(Q);
	    
	    k = e.val;
	    p = e.key;

	    if (k.size() == n) {
		//for (int i =0;i<k.size();i++) 
		//    System.out.println(k.get(i));
		solved = true;
	    }
	    else {
		int p1 = 0;
		
		while (p1 != n) {
		    if (peace(k,p1)) {
			int i;
			IntVector newk = new IntVector(1+k.size());
			for(i = 0; i<k.size(); i++) 
			    newk.put(i,k.get(i));
			newk.put(i,p1);
			PQ.insert(Q, newk, k.size()+1);
		    }
		    p1++;
		}
	    }
	}
	if (solved) {
	    System.out.println("Solved");
	    int m = k.size();
	    for (int i=0; i<m; i++) {
		printBoard(m,"+---","+");
		printBoard(k.get(i),"|   ","");
		System.out.print("| Q "); 
		printBoard(m-k.get(i)-1,"|   ","|");
	    }
	    printBoard(m,"+---","+");

	}
	else
	    System.out.println("Not Solved");
    }
}

	
