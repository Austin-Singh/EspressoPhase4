package AST;
import Utilities.Visitor;

public class Assignment extends Expression {
    
    public Assignment(Expression /* Name, FieldRef or ArrayAccess only */ left, Expression right,
	       AssignmentOp op) {
	super(left);
	nchildren = 3;
	children = new AST[] { left, right, op};
    }
    
    public Expression left()  { return (Expression)children[0];   }
    public Expression right() { return (Expression)children[1];   }
    public AssignmentOp op()  { return (AssignmentOp)children[2]; }

    /* *********************************************************** */
    /* **                                                       ** */
    /* ** Generic Visitor Stuff                                 ** */
    /* **                                                       ** */
    /* *********************************************************** */
    
    public Object visit(Visitor v) {
        return v.visitAssignment(this);
    }    
}
