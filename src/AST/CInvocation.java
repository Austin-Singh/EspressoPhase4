package AST;
import Utilities.Visitor;

public class CInvocation extends Expression {

	public ConstructorDecl constructor; // This one is needed in the code generation phase
	public ClassDecl targetClass; // This one is needed for modifier checking

	private boolean superInv, thisInv;

	public CInvocation(Token cl, Sequence /* of Expression */ args) {
		super(cl);
		nchildren = 1;
		superInv = (cl.text.equals("super")); //(cl.sym == sym.SUPER);
		thisInv  = !superInv;
		children = new AST [] { args };
	}

	public Sequence args() { return (Sequence)children[0]; }

	public boolean superConstructorCall() {
		return superInv;
	}

	public boolean thisConstructorCall() {
		return thisInv;
	}

	/* *********************************************************** */
	/* **                                                       ** */
	/* ** Generic Visitor Stuff                                 ** */
	/* **                                                       ** */
	/* *********************************************************** */

	public Object visit(Visitor v) {
		return v.visitCInvocation(this);
	}

}

