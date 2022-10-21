package AST;
import Utilities.Visitor;

public class Sequence extends AST {

	public Sequence() {
		super(0, 0);
		nchildren = 0;
	}

	public Sequence(AST element) {
		super(element);
		nchildren = 1;
		children = new AST[10];
		children[0] = element;
	}

	public Sequence append(AST element) {
		int length = children == null ? 0 : children.length;
		//if (element == null) return this;
		if (nchildren >= length) {
			AST[] c = new AST[(length + 1) * 2];
			int i;
			for (i = 0; i < length; i++) {
				c[i] = children[i];
			}
			children = c;
		}
		children[nchildren] = element;
		nchildren ++;
		return this;
	}

	public Sequence merge(Sequence others) {
		if (others == null || others.nchildren == 0) return this;
		int i;
		for (i = 0; i < others.nchildren; i++) {
			this.append(others.children[i]);
		}
		return this;
	}

	public Sequence merge(AST other) {
		if (other == null) return this;
		this.append(other);
		return this;
	}

	/* *********************************************************** */
	/* **                                                       ** */
	/* ** Generic Visitor Stuff                                 ** */
	/* **                                                       ** */
	/* *********************************************************** */

	public Object visit(Visitor v) {
		return v.visitSequence(this);
	}
}

