package AST;
import Utilities.Visitor;

public class ClassType extends Type {

	public ClassDecl myDecl; // Point to the class representing this class type

	public ClassType(Name className) { 
		super(className);
		nchildren = 1;
		children = new AST[] { className };
	}

	public Name name() { 
		return (Name)children[0]; 
	}

	public String toString() {
		return "(ClassType: " + name() + ")";
	}

	public String typeName() {
		return name().getname();
	}

	public String signature() {
		return "L"+typeName()+";";
	}


	/* *********************************************************** */
	/* **                                                       ** */
	/* ** Generic Visitor Stuff                                 ** */
	/* **                                                       ** */
	/* *********************************************************** */

	public Object visit(Visitor v) {
		return v.visitClassType(this);
	}


}             




