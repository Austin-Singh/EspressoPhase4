package AST;
import Utilities.Visitor;

public class BreakStat extends Statement {

    public BreakStat(Token b) {
	super(b);
	nchildren = 0;
    }

    /* *********************************************************** */
    /* **                                                       ** */
    /* ** Generic Visitor Stuff                                 ** */
    /* **                                                       ** */
    /* *********************************************************** */
    
    public Object visit(Visitor v) {
        return v.visitBreakStat(this);
    }

    
}
