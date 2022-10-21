package AST;
import Utilities.Visitor;

public class FieldRef extends Expression {

	public Type targetType; // needed for code generation and modifier checking
	public FieldDecl myDecl;
	public boolean rewritten = false; // lets keep track of which nodes were generated 
	// from rewriting so that we can produce errors messages that make more sense


	public FieldRef(Expression target, Name fieldName) {
		super(fieldName);
		nchildren = 2;
		children = new AST[] { target, fieldName };
	}

	public Expression target()    { return (Expression)children[0]; }
	public Name fieldName()       { return (Name)children[1]; }

	public boolean isConstant() {
		return target().isConstant() && 
				myDecl.modifiers.isStatic() && 
				myDecl.modifiers.isFinal();
	}

	public Object constantValue() {
		return myDecl.var().init().constantValue();
	}

	/* *********************************************************** */
	/* **                                                       ** */
	/* ** Generic Visitor Stuff                                 ** */
	/* **                                                       ** */
	/* *********************************************************** */

	public Object visit(Visitor v) {
		return v.visitFieldRef(this);
	}


}
