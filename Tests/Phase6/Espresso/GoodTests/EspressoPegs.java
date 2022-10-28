//(48)
//3
//How many Discs (Max 10)?           =|=                     |                      |           
//         ==|==                    |                      |           
//        ===|===                   |                      |           
// ----------+----------  ----------+----------  ----------+---------- 
//           1                      2                      3
//Move one disc from peg 1 to 2.
//           |                      |                      |           
//         ==|==                    |                      |           
//        ===|===                  =|=                     |           
// ----------+----------  ----------+----------  ----------+---------- 
//           1                      2                      3
//Move one disc from peg 1 to 3.
//           |                      |                      |           
//           |                      |                      |           
//        ===|===                  =|=                   ==|==         
// ----------+----------  ----------+----------  ----------+---------- 
//           1                      2                      3
//Move one disc from peg 2 to 3.
//           |                      |                      |           
//           |                      |                     =|=          
//        ===|===                   |                    ==|==         
// ----------+----------  ----------+----------  ----------+---------- 
//           1                      2                      3
//Move one disc from peg 1 to 2.
//           |                      |                      |           
//           |                      |                     =|=          
//           |                   ===|===                 ==|==         
// ----------+----------  ----------+----------  ----------+---------- 
//           1                      2                      3
//Move one disc from peg 3 to 1.
//           |                      |                      |           
//           |                      |                      |           
//          =|=                  ===|===                 ==|==         
// ----------+----------  ----------+----------  ----------+---------- 
//           1                      2                      3
//Move one disc from peg 3 to 2.
//           |                      |                      |           
//           |                    ==|==                    |           
//          =|=                  ===|===                   |           
// ----------+----------  ----------+----------  ----------+---------- 
//           1                      2                      3
//Move one disc from peg 1 to 2.
//           |                     =|=                     |           
//           |                    ==|==                    |           
//           |                   ===|===                   |           
// ----------+----------  ----------+----------  ----------+---------- 
//           1                      2                      3
//Number of moves: 7
import System;

public class VectorElement {
    private int value;
    private VectorElement next;
    private VectorElement previous;

    public VectorElement(int value) {
	this.value = value;
	next = null;
	previous = null;
    }
    

    public void setNext(VectorElement next) {
	this.next = next;
    }
    
    public void setPrevious(VectorElement previous) {
	this.previous = previous;
    }

    public VectorElement getNext() {
	return next;
    }

    public VectorElement getPrevious() {
	return previous;
    }

    public int getValue() {
	return value;
    }

}

 
public class IntVector {

    private int size, id;
    private VectorElement head;
    private VectorElement tail;

    public IntVector(int id) {
	size = 0;
	this.id = id;
    }

    public int getId() {
	return id;
    }

    public int size() { 
	return size;
    }

    public int elementAt(int index) { 
	VectorElement ve = head;
	while (index > 0) {
	    ve = ve.getNext();
	    index--;
	}
	return ve.getValue();
    }

    public void remove(int index) { 
	if (index < size) {
	    if (index == 0) {
		head = null;
		tail = null;
	    } else if (index == size-1) {
		tail = tail.getPrevious();
		tail.setNext(null);
	    } else {
		VectorElement ve = head;
		while (index > 0) {
		    ve = ve.getNext();
		    index--;
		}
		ve.getPrevious().setNext(ve.getNext());
		ve.getNext().setPrevious(ve.getPrevious());
	    }
	    size--;
	}
    }


    public void addElement(int value) { 
	VectorElement ve = new VectorElement(value);
	if (size == 0) {
	    head = ve;
	    tail = ve;
	} else {
	    ve.setPrevious(tail);
	    tail.setNext(ve);
	    tail = ve;
	}
	size++;
    }
    


}
   

public class Pegs {
    public static IntVector peg1, peg2, peg3;
    public static int moves = 0;

    public static void move (int count, 
			     IntVector from, IntVector to, IntVector via) {
	if (count == 1) {
	    System.out.print("Move one disc from peg ");
	    System.out.print(from.getId());
	    System.out.print(" to ");
	    System.out.print(to.getId());
	    System.out.println(".");
	    int s1 = from.size();
	    int disc = from.elementAt(s1-1);
	    from.remove(s1-1);
	    to.addElement(disc);
	    print();
	    moves++;
	}
	else {
	    move(count-1, from, via, to);
	    move(1, from, to, via);
	    move(count-1, via, to, from);
	}
    }

    public static void printDisc(int width) {
	System.out.print(" ");
	for (int i=0; i<10-width; i++)
	    System.out.print(" ");
	for (int i=0; i<width; i++)
	    System.out.print("=");
	System.out.print("|");
	for (int i=0; i<width; i++)
	    System.out.print("=");
	for (int i=0; i<10-width; i++)
	    System.out.print(" ");
	System.out.print(" ");
    }

    public static void print() {
	int s1 = peg1.size();
	int s2 = peg2.size();
	int s3 = peg3.size();
	
	for (int i=noDiscs-1; i>=0; i--) {
	    if (s1>i)
		printDisc(peg1.elementAt(i));
	    else
		System.out.print("           |           ");
	    if (s2>i)
		printDisc(peg2.elementAt(i));
	    else
		System.out.print("           |           ");
	    if (s3>i)
		printDisc(peg3.elementAt(i));
	    else
		System.out.print("           |           ");
	    System.out.println("");
	}
	System.out.println(" ----------+----------  ----------+----------  ----------+---------- ");
	System.out.println("           1                      2                      3");
    }

    static int noDiscs;

    public static void main(String args[]) {
	peg1 = new IntVector(1);
	peg2 = new IntVector(2);
	peg3 = new IntVector(3);
	System.out.print("How many Discs (Max 10)? ");
	noDiscs = System.in.readInt();
	for (int i=noDiscs;i>0;i--)
	    peg1.addElement(i);
	print();
	move(noDiscs,peg1, peg2, peg3);
	System.out.print("Number of moves: ");
	System.out.println(moves);
    }
}