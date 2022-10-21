package AST;
import Utilities.Visitor;

public class Name extends AST {
	private String id;
	private int arrayDepth = 0; // somewhat of a hack - we keep track of 
	// whether this name is an id in a variable declaration with [] on. 

	public Name(Token p_id) {
		super(p_id);
		nchildren = 0;
		this.id = p_id.text;
		this.arrayDepth = 0;
	}

	public Name(Name n, int arrayDepth) {
		super(n);
		this.id = n.getname(); 
		this.arrayDepth = arrayDepth;	
	}

	public String getname() {
		return this.id;
	}

	public void setName(String na) {
		id = na;
	}
	
	public String toString() {
		return this.id;
	}

	public int getArrayDepth() {
		return this.arrayDepth;
	}
	public void setArrayDepth(int d) {
		this.arrayDepth = d;
	}
	/* *********************************************************** */
	/* **                                                       ** */
	/* ** Generic Visitor Stuff                                 ** */
	/* **                                                       ** */
	/* *********************************************************** */

	public Object visit(Visitor v) {
		return v.visitName(this);
	}



}




