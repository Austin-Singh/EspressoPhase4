package AST;
import Utilities.Visitor;

public class BinOp extends AST {

    public int kind;

    public static final int PLUS       = 1;
    public static final int MINUS      = 2;
    public static final int MULT       = 3;
    public static final int DIV        = 4;
    public static final int MOD        = 5;
    public static final int LSHIFT     = 6;
    public static final int RSHIFT     = 7;
    public static final int RRSHIFT    = 8;
    public static final int LT         = 9;
    public static final int GT         = 10;
    public static final int LTEQ       = 11;
    public static final int GTEQ       = 12;
    public static final int INSTANCEOF = 13;
    public static final int EQEQ       = 14;
    public static final int NOTEQ      = 15;
    public static final int AND        = 16;
    public static final int OR         = 17;
    public static final int XOR        = 18;
    public static final int ANDAND     = 19;
    public static final int OROR       = 20;
   

    public static final String [] opSyms = {
	"", "+", "-", "*", "/", "%", "<<", ">>", ">>>", "<", ">",
	"<=", ">=", "instanceof", "==", "!=", "&", "|", "^",
	"&&", "||" };

    public BinOp(Token t, int kind) {
	super(t);
	this.kind = kind;
    }
    
    public BinOp(int kind) {
	super(0,0);
	this.kind = kind;
    }


    public String operator() { return opSyms[kind]; }

    /* *********************************************************** */
    /* **                                                       ** */
    /* ** Generic Visitor Stuff                                 ** */
    /* **                                                       ** */
    /* *********************************************************** */
    
    public Object visit(Visitor v) {
        return v.visitBinOp(this);
    }


}
