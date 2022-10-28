//(10)
//10\r\n18\r\n16\r\n14\r\n8\r\n9\r\n61\r\n2\r\n1\r\n0\r\n6\r\n
//Please enter the number of elements you wish to sort: Enter element number 0: Enter element number 1: Enter element number 2: Enter element number 3: Enter element number 4: Enter element number 5: Enter element number 6: Enter element number 7: Enter element number 8: Enter element number 9: 0
//1
//2
//6
//8
//9
//14
//16         
//18
//61
import System;

class Tree {
    int value;
    Tree left, right;
    Tree() {}
    Tree(int value) {
	this.value = value;
	left = right = null;
    }

    Tree insert(int value) {
	if (this.value < value) {
	    if (right == null) 
		right = new Tree(value);
	    else
		right = right.insert(value);
	} else if (this.value > value) {
	    if (left == null) 
		left = new Tree(value);
	    else
		left = left.insert(value);
	}
	return this;
    }

    void traverse() {
	if (left != null)
	    left.traverse();
	System.out.println(value);
	if (right != null)
	    right.traverse();
    }
}

class Main {
    public static void main(String args[]) {
	int no,temp;
	Tree t = null;
	System.out.print("Please enter the number of elements you wish to sort: ");
	no = System.out.readInt();
	
	for (int i=0;i<no;i++) {
	    System.out.print("Enter element number ");
	    System.out.print(i);
	    System.out.print(": ");
	    temp = System.out.readInt();
	    if (t == null) 
		t = new Tree(temp);
	    else
		t = t.insert(temp);
	}
	t.traverse();
    }
}
