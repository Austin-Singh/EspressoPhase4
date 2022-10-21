package AST;
import Utilities.Visitor;

public class NullType extends Type {

	/** This type does not occur in the parse tree! it is
	for type checking purposes only */

	public NullType(Literal li) {
		super(li);
	}

	public String typeName() {
		return "(NullType:)";
	}

	public String signature() {
		return "";
	}

    public String toString() {
	return "(NullType)";
    }

	/* *********************************************************** */
	/* **                                                       ** */
	/* ** Generic Visitor Stuff                                 ** */
	/* **                                                       ** */
	/* *********************************************************** */

	public Object visit(Visitor v) {
		return v.visitNullType(this);
	}



}
