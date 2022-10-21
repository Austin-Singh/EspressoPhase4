package Utilities;
import AST.*;

/** Abstract class for the visitor pattern. This abstract class
 *  must be re-implemented for each traversal through the tree.
 * 
 * @author Matt Pedersen
 *
 */
public abstract class Visitor {

	// The 'debug' field should be set in the constructor of the 
	// extending class.
	protected static boolean debug;

	public static void print(String info) {
		if (debug)
			System.out.print(info);
	}

	public static void println(String info) {
		if (debug) 
			System.out.println(info);
	}
	public Object visitArrayAccessExpr(ArrayAccessExpr ae) {
		return ae.visitChildren(this);
	}
	public Object visitArrayLiteral(ArrayLiteral al) {
		return al.visitChildren(this);
	}
	public Object visitArrayType(ArrayType at) {
		return at.visitChildren(this);
	}
	public Object visitAssignment(Assignment as) {
		return as.visitChildren(this);
	}
	public Object visitAssignmentOp(AssignmentOp ao) {
		return ao.visitChildren(this);
	}
	public Object visitBinaryExpr(BinaryExpr be) {
		return be.visitChildren(this);
	}
	public Object visitBinOp(BinOp bo) {
		return bo.visitChildren(this);
	}
	public Object visitBlock(Block bl) {
		return bl.visitChildren(this);
	}
	public Object visitBreakStat(BreakStat bs) {
		return null;
	}
	public Object visitCastExpr(CastExpr ce) {
		return ce.visitChildren(this);
	}
	public Object visitCInvocation(CInvocation ci) {
		return ci.visitChildren(this);
	}
	public Object visitClassDecl(ClassDecl cd) {
		return cd.visitChildren(this);
	}
	public Object visitClassType(ClassType ct) {
		return ct.visitChildren(this);
	}
	public Object visitCompilation(Compilation co) {
		return co.visitChildren(this);
	}
	public Object visitConstructorDecl(ConstructorDecl cd) {
		return cd.visitChildren(this);
	}
	public Object visitContinueStat(ContinueStat cs) {
		return null;
	}
	public Object visitDoStat(DoStat ds) {
		return ds.visitChildren(this);
	}
	public Object visitExprStat(ExprStat es) {
		return es.visitChildren(this);
	}
	public Object visitFieldDecl(FieldDecl fd) {
		return fd.visitChildren(this);
	}
	public Object visitFieldRef(FieldRef fr) {
		return fr.visitChildren(this);
	}
	public Object visitForStat(ForStat fs) {
		return fs.visitChildren(this);
	}
	public Object visitIfStat(IfStat is) {
		return is.visitChildren(this);
	}
	public Object visitInvocation(Invocation in) {
		return in.visitChildren(this);
	}
	public Object visitLiteral(Literal li) {
		return null;
	}
	public Object visitLocalDecl(LocalDecl ld) {
		return ld.visitChildren(this);
	}
	public Object visitMethodDecl(MethodDecl md) {
		return md.visitChildren(this);
	}
	public Object visitModifier(Modifier mo) {
		return null;
	}
	public Object visitName(Name na) {
		return null;
	}
	public Object visitNameExpr(NameExpr ne) {
		return ne.visitChildren(this);
	}
	public Object visitNew(New ne) {
		return ne.visitChildren(this);
	}
	public Object visitNewArray(NewArray ne) {
		return ne.visitChildren(this);
	}
	public Object visitNullType(NullType nt) {
		return nt.visitChildren(this);
	}
	public Object visitParamDecl(ParamDecl pd) {
		return pd.visitChildren(this);
	}
	public Object visitPostOp(PostOp po) {
		return po.visitChildren(this);
	}
	public Object visitPreOp(PreOp po) {
		return po.visitChildren(this);
	}
	public Object visitPrimitiveType(PrimitiveType py) {
		return null;
	}
	public Object visitReturnStat(ReturnStat rs) {
		return rs.visitChildren(this);
	}
	public Object visitSequence(Sequence se) {
		return se.visitChildren(this);
	}
	public Object visitStaticInitDecl(StaticInitDecl si) {
		return si.visitChildren(this);
	}
	public Object visitSuper(Super su) {
		return null;
	}
	public Object visitSwitchGroup(SwitchGroup sg) {
		return sg.visitChildren(this);
	}
	public Object visitSwitchLabel(SwitchLabel sl) {
		return sl.visitChildren(this);
	}
	public Object visitSwitchStat(SwitchStat st) {
		return st.visitChildren(this);
	}
	public Object visitTernary(Ternary te) {
		return te.visitChildren(this);
	}
	public Object visitThis(This th) {
		return null;
	}
	public Object visitUnaryPostExpr(UnaryPostExpr up) {
		return up.visitChildren(this);
	}
	public Object visitUnaryPreExpr(UnaryPreExpr up) {
		return up.visitChildren(this);
	}
	public Object visitVar(Var va) {
		return va.visitChildren(this);
	}
	public Object visitWhileStat(WhileStat ws) {
		return ws.visitChildren(this);
	}
}

