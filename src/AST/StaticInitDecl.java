package AST;
import Utilities.Visitor;

public class StaticInitDecl extends ClassBodyDecl {

	public StaticInitDecl(Block init) {
		super(init);
		nchildren = 1;
		children = new AST[] { init };
	}

	public Block initializer() { return (Block)children[0]; }

	public String getname() {
		return "";
	}

	public boolean isStatic() {
		return true;
	}

	/* *********************************************************** */
	/* **                                                       ** */
	/* ** Generic Visitor Stuff                                 ** */
	/* **                                                       ** */
	/* *********************************************************** */

	public Object visit(Visitor v) {
		return v.visitStaticInitDecl(this);
	}
}

