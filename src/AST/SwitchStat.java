package AST;
import Utilities.Visitor;

public class SwitchStat extends Statement {

	public SwitchStat(Expression expr,
			Sequence /* SwitchGroup */ switchBlocks) {
		super(expr);
		nchildren = 2;
		children = new AST[] { expr, switchBlocks };
	}

	public Expression expr()       { return (Expression)children[0]; }
	public Sequence switchBlocks() { return (Sequence)children[1]; }

	/* *********************************************************** */
	/* **                                                       ** */
	/* ** Generic Visitor Stuff                                 ** */
	/* **                                                       ** */
	/* *********************************************************** */

	public Object visit(Visitor v) {
		return v.visitSwitchStat(this);
	}

}

