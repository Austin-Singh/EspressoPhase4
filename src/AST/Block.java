package AST;
import Utilities.Visitor;

public class Block extends Statement {
    
    public Block(Sequence /* of Statements */ stats) {
	super(stats);
	nchildren = 1;
	children = new AST[] { stats };
    }

    public Sequence stats() { return (Sequence)children[0]; }

    /* *********************************************************** */
    /* **                                                       ** */
    /* ** Generic Visitor Stuff                                 ** */
    /* **                                                       ** */
    /* *********************************************************** */
    
    
    public Object visit(Visitor v) {
        return v.visitBlock(this);
    }
    
    
}
