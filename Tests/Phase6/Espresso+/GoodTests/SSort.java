//(8)
//
//Hello
//-7
//-6.199999809265137
//0
//0.0010000000474974513
//5
//5.5
//6
import System;

class Main {

    public static void BubbleSort(MyList l, Comparator c)
    {
	System.out.println("Hello");
	int len = l.size();
	for(int x = 0; x < len; x++)
	    {
		int lim = len - x;//the part already sorted
		for (int y = 1; y < lim; y++)
		    {
			if (c.compare(l.get(y - 1), l.get(y)) > 0)
			    {
				MyObject back = l.get(y - 1);
				l.set(y - 1, l.get(y));
				l.set(y, back);
			    }
		    }
	    }
	
    }

    public static void main(String args[])
    {
	MyList l = new LinkedMyList();
	
	l.add(new MyDouble(5.5));
	l.add(new MyDouble(-6.2));
	l.add(new MyInteger(0));
	l.add(new MyDouble(0.001));
	l.add(new MyInteger(5));
	l.add(new MyInteger(6));
	l.add(new MyInteger (-7));
	
	BubbleSort(l, NumberComparator.getInstance());
	
	for (int x = 0; x < l.size(); x++)
	{
	    	    Number curr = (Number)l.get(x);
	    if (curr instanceof MyInteger)
		System.out.println(curr.getInt());
	    else
	    System.out.println(curr.getMyDouble());
	}
    return;
    }
}

class MyObject
{
}


abstract class Number extends MyObject
{
    public Number() {}
    public byte getByte(){return (byte)getMyDouble();}
    public short getShort(){return (short)getMyDouble();}
    public int getInt(){return (int)getMyDouble();}
    public long getLong() {return (long)getMyDouble();}
    public float getFloat() {return (float)getMyDouble();}
    public abstract double getMyDouble();
}

class MyInteger extends Number
{

    private int val;
    public MyInteger() {}
    public MyInteger(int v)
    {
	val = v;
    }

    public double getMyDouble(){return (double)val;}

}


class MyDouble extends Number
{
    private double val;
    public MyDouble(){}
    public MyDouble (double v)
    {
	val = v;
    }

    public double getMyDouble(){return val;}

}

// return value > 0 if a > b, = 0 if a = b, < 0 if a < b
interface Comparator
{
    public abstract int compare(MyObject a, MyObject b);
}

//An example of a singleton class
class NumberComparator implements Comparator
{
    private static Comparator inst;

    static
    {
	inst = new NumberComparator();
    }

    public static Comparator getInstance(){return inst;}

    private NumberComparator(){}

    public int compare(MyObject a, MyObject b)
    {
	Number n1 = (Number)a;
	Number n2 = (Number)b;

	if (n1.getMyDouble() < n2.getMyDouble())
	    return -1;
	if (n1.getMyDouble() > n2.getMyDouble())
	    return 1;
	return 0;
    }

}



public interface MyList
{
    public abstract int size();
    public abstract MyObject get(int x);
    public abstract void set(int x, MyObject o);
    public abstract void add(MyObject o);
}


class LinkedMyList implements MyList
{
    private int sz;
    private MyListNode first;
    private MyListNode last;

    LinkedMyList()
    {
	sz = 0;
	last = first = null;
    }

    public int size()
    {
	return sz;
    }

    private MyListNode getIndex(int ind)
    {
	if (ind >= sz)
	   return null;
	
	MyListNode current = first;
	for (int x = 0; x < ind; x++)
	{
	    current = current.next;
	}
	

	return current;
    }

    

    public MyObject get(int ind)
    {	
	return getIndex(ind).value;
    }

    public void set(int ind, MyObject o)
    {
	getIndex(ind).value = o;
    }

    public void add(MyObject o)
    {
	if (last != null)
	{
	    last.next = new MyListNode(o);
	    last = last.next;
	}
	else
	{
	    first = last = new MyListNode(o);
	}
	sz++;
    }

}

class MyListNode
{
    public MyObject value;
    public MyListNode next;
    public MyListNode() {}
    public MyListNode(MyObject v)
    {
	value = v;
	next = null;
    }

}
