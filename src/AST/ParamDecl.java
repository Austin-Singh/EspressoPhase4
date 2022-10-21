package AST;
import Utilities.Visitor;

public class ParamDecl extends AST implements VarDecl  {

	public int address = -1;

	public ParamDecl(Type type, Name name) {
		super(type);
		nchildren = 2;
		children = new AST[] { type, name };
	}

	public Type type()      { return (Type)children[0]; }
	public Name paramName() { return (Name)children[1]; }

	public String name() {
		return paramName().getname();
	}

	public String toString() {
		return "ParamDecl>(Type:" + type() + " " + "Name:" + name() + ")";
	}

	public boolean isClassType() {
		return (type() instanceof ClassType);
	}

	public int address() {
		return address;
	}


	/* *********************************************************** */
	/* **                                                       ** */
	/* ** Generic Visitor Stuff                                 ** */
	/* **                                                       ** */
	/* *********************************************************** */

	public Object visit(Visitor v) {
		return v.visitParamDecl(this);
	}
}
