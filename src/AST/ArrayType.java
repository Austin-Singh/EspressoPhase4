package AST;

import Utilities.Visitor;

public class ArrayType extends Type {

	private int depth = 0; // How many set of [ ] were there?

	public ArrayType(Type baseType, int depth) {
		super(baseType);
		nchildren = 1;
		this.depth = depth;
		children = new AST[] { baseType };		
	}

	public Type baseType() { 
		return (Type) children[0]; 
	}

	public int getDepth() { 
		return depth; 
	}

	public String toString() {
		return "(ArrayType: " + typeName() + ")";
	}

	public String signature() {
		String s = "";
		for (int i=0;i<depth; i++)
			s += "[";				
		return s + baseType().signature();
	}

	public String typeName() {
		String s = baseType().typeName();
		for (int i=0; i<depth; i++)
			s = s + "[]";
		return s;
	}

	/* *********************************************************** */
	/* **                                                       ** */
	/* ** Generic Visitor Stuff                                 ** */
	/* **                                                       ** */
	/* *********************************************************** */

	public Object visit(Visitor v) {
		return v.visitArrayType(this);
	}
}             








