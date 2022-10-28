//Usage: Enter the number of elements you want to sort. then enter the elements.
//Output: The entered elements in sorted order:
//Enter an integer: 10
//Enter an integer: 10
//Enter an integer: 9
//Enter an integer: 8
//Enter an integer: 7
//Enter an integer: 1
//Enter an integer: 4
//Enter an integer: 2
//Enter an integer: 6
//Enter an integer: 5
//Enter an integer: 3
//1
//2
//3
//4
//5
//6
//7
//8
//9
//10         
//Result: 0

class Io {
    static public void print(byte b) { }
    static public void print(short s) { }
    static public void print(char c) { }
    static public void print(int i) { }
    static public void print(long l) { }
    static public void print(float f) { }
    static public void print(double d){ }
    static public void print(String s){ }
    static public void print(boolean b){ }
    static public void println(byte b) { }
    static public void println(short s){ }
    static public void println(char c) { }
    static public void println(int i) { }
    static public void println(long l) { }
    static public void println(float f){ }
    static public void println(double d){ }
    static public void println(String s){ }
    static public void println(boolean b){ }

    static public int readInt() { }
    static public long readLong() { }
    static public float readFloat() { }
    static public double readDouble() { }
    static public String readString() { }
}

class Tree {
    int value;
    Tree left, right;
    
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
	Io.println(value);
	if (right != null)
	    right.traverse();
    }
}

class Main {
    int main() {
	int no,temp;
	Tree t = null;
       
	no = Io.readInt();
	
	for (int i=0;i<no;i++) {
	    temp = Io.readInt();
	    if (t == null) 
		t = new Tree(temp);
	    else
		t = t.insert(temp);
	}
	t.traverse();
    }
}
