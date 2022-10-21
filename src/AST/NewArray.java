package AST;

import Utilities.Visitor;

public class NewArray extends Expression {

	public NewArray(Type type, Sequence dimsExpr, Sequence dims, ArrayLiteral init) {
		super(type);
		nchildren = 4;
		children = new AST[] { type, dimsExpr, dims, init};
	}


	public Type baseType()         { return (Type)children[0]; }
	public Sequence dimsExpr() { return (Sequence)children[1]; }
	public Sequence dims()     { return (Sequence)children[2]; }
	public ArrayLiteral init()     { return (ArrayLiteral)children[3]; }

	public String toString() {
		return "" + baseType() + " " + dimsExpr() + " " + dims();
	}


	/* *********************************************************** */
	/* **                                                       ** */
	/* ** Generic Visitor Stuff                                 ** */
	/* **                                                       ** */
	/* *********************************************************** */

	public Object visit(Visitor v) {
		return v.visitNewArray(this);
	}

}
