package AST;
import Utilities.Visitor;

public class New extends Expression {

	private ConstructorDecl constructor = null; // This is needed in the code generation phase.

	public New(ClassType typeName,  Sequence /* of Expressions */ args) {
		super(typeName);
		nchildren = 2;
		children = new AST[] { typeName, args };
	}

	public ClassType type() { return (ClassType)children[0];     }
	public Sequence  args() { return (Sequence)children[1]; }

	public void setConstructorDecl(ConstructorDecl cd) {
		this.constructor = cd;
	}
	public ConstructorDecl getConstructorDecl() {
		return this.constructor;
	}

	/* *********************************************************** */
	/* **                                                       ** */
	/* ** Generic Visitor Stuff                                 ** */
	/* **                                                       ** */
	/* *********************************************************** */

	public Object visit(Visitor v) {
		return v.visitNew(this);
	}
}
