package AST;
import Utilities.Visitor;

public class Compilation extends AST {

	public Compilation(Sequence types) {
		super(types);
		nchildren = 1;
		children = new AST[] { types };
	}

	public Sequence types() { return (Sequence)children[0]; }

	/* *********************************************************** */
	/* **                                                       ** */
	/* ** Generic Visitor Stuff                                 ** */
	/* **                                                       ** */
	/* *********************************************************** */

	public Object visit(Visitor v) {
		return v.visitCompilation(this);
	}

}
