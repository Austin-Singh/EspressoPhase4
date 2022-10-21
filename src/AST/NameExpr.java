package AST;
import Utilities.Visitor;

public class NameExpr extends Expression {    

	// A name expression can represent a variable name (local, parameter or field) or
	// it can be a class name as well.
	// if it is a variable name myDecl contains a VarDecl object
	// if it is a class name    myDecl contains a ClassDecl object 

	public AST myDecl = null;

	public NameExpr(Name name) {
		super(name);
		nchildren = 1;
		children = new AST[] { name };
	}

	public Name name() { return (Name)children[0]; }

	public boolean isConstant() {
		if (myDecl instanceof ClassDecl) 
			return true;
		else if (myDecl instanceof FieldDecl) {
			FieldDecl fd = (FieldDecl) myDecl;
			return fd.modifiers.isStatic() && fd.modifiers.isFinal() && fd.var().init().isConstant(); 
		}
		else
			return false;
	}

	public Object constantValue() {
		if (myDecl instanceof FieldDecl)
			return ((FieldDecl)myDecl).var().init().constantValue();
		return null;
	}


	/* *********************************************************** */
	/* **                                                       ** */
	/* ** Generic Visitor Stuff                                 ** */
	/* **                                                       ** */
	/* *********************************************************** */

	public Object visit(Visitor v) {
		return v.visitNameExpr(this);
	}


}









