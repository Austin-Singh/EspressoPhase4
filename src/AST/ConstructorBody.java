package AST;

public class ConstructorBody {

	// This class does not appear in the Syntax Tree.
	// We just use it for an intermidiate representation
	// of the body of a constructor.

	public CInvocation ci;
	public Sequence st;

	public ConstructorBody(CInvocation ci, Sequence /* of Statements */ st) {
		this.ci = ci;
		this.st = st;
	}

}
