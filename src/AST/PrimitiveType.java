package AST;

import Utilities.Visitor;

public class PrimitiveType extends Type {

	public final static int BooleanKind = Literal.BooleanKind;
	public final static int CharKind = Literal.CharKind;
	public final static int ByteKind = Literal.ByteKind;
	public final static int ShortKind = Literal.ShortKind;
	public final static int IntKind = Literal.IntKind;
	public final static int LongKind = Literal.LongKind;
	public final static int FloatKind = Literal.FloatKind;
	public final static int DoubleKind = Literal.DoubleKind;
	public final static int StringKind = Literal.StringKind;
	public final static int VoidKind = Literal.NullKind;

	public static String[] names = { "Junk", "boolean", "byte", "short",
									  "char", "int", "long", "float", "double", 
									  "String", "void" };
	private int kind;

	public PrimitiveType(Token p_t, int kind) {
		super(p_t);
		this.kind = kind;
	}

	public PrimitiveType(int kind) {
		super((AST) null);
		this.kind = kind;
	}

	
	public static int ceiling(PrimitiveType p1, PrimitiveType p2) {
		if (p1.kind < p2.kind)
			return p2.kind;
		return p1.kind;
	}

	public static PrimitiveType ceilingType(PrimitiveType p1, PrimitiveType p2) {
		if (p1.kind < IntKind && p2.kind < IntKind)
			return new PrimitiveType(IntKind);

		if (p1.kind < p2.kind)
			return p2;
		return p1;
	}

	public String toString() {
		return "(PrimitiveType: " + names[kind] + ")";
	}

	public String typeName() {
		return names[kind];
	}

    public String typeNameCodeGenerator() {
	if (kind == StringKind)
	    return "Ljava/lang/String;";
	else
	    return typeName();
    }

	public int getKind() {
		return kind;
	}

	public String signature() {
		switch (kind) {
		case BooleanKind:
			return "Z";
		case ByteKind:
			return "B";
		case ShortKind:
			return "S";
		case CharKind:
			return "C";
		case IntKind:
			return "I";
		case LongKind:
			return "J";
		case FloatKind:
			return "F";
		case DoubleKind:
			return "D";
		case StringKind:
			return "Ljava/lang/String;";
		case VoidKind:
			return "V";
		default:
			return "UNKNOWN TYPE";
		}
	}

	/* *********************************************************** */
	/* ** Generic Visitor Stuff                                 ** */
	/* *********************************************************** */

	public Object visit(Visitor v) {
		return v.visitPrimitiveType(this);
	}

}
