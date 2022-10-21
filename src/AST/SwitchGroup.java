package AST;
import Utilities.Visitor;

public class SwitchGroup extends AST {

	private String label; // used in the code generation phase.    

	public SwitchGroup(Sequence /* SwitchLabels */ labels, 
			Sequence /* Statement */ stmts) {
		super(labels);
		nchildren = 2;
		children = new AST[] { labels, stmts };
	}

	public Sequence labels()     { return (Sequence)children[0]; }
	public Sequence statements() { return (Sequence)children[1]; }

	public void setLabel(String label) {
		this.label = label;
	}
	public String getLabel() {
		return this.label;
	}

	/* *********************************************************** */
	/* **                                                       ** */
	/* ** Generic Visitor Stuff                                 ** */
	/* **                                                       ** */
	/* *********************************************************** */

	public Object visit(Visitor v) {
		return v.visitSwitchGroup(this);
	}

}

