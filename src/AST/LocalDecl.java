package AST;
import Utilities.Visitor;

public class LocalDecl extends Statement implements VarDecl  {

	public int address = -1;

	public LocalDecl(Type type, Var var) {
		super(type);
		nchildren = 2;
		children = new AST[] { type, var };
	}

	public Type type() { return (Type)children[0]; }
	public Var  var()  { return (Var)children[1];  }

	public String name() {
		return var().name().getname();
	}

	public String toString() {
		return "LocalDecl>(Type:" + type() + " " + "Name:" + var() + ")";
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
		return v.visitLocalDecl(this);
	}
}

