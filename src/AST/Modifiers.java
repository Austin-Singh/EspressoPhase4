package AST;
import Utilities.Error;

public class Modifiers {
	// This class is not part of the Abstract Syntax Hierarchy, it just makes
	// life easier when it comes to dealing with modifiers.

	// ------------------------------------------------------------------------
	// Fields

	private boolean mStatic    = false;
	private boolean mFinal     = false;
	private boolean mPublic    = false;
	private boolean mPrivate   = false;
	private boolean mAbstract  = false;

	// -------------------------------------------------------------------------
	// Constructor

	public Modifiers() {
	}

	// -------------------------------------------------------------------------
	// Accessors

	public boolean isStatic() {
		return mStatic;
	}

	public boolean isFinal() {
		return mFinal;
	}

	public boolean isPublic() {
		return mPublic;
	}

	public boolean isPrivate() {
		return mPrivate;
	}

	public boolean isAbstract() {
		return mAbstract;
	}


	/* We have the following rules for modifiers:

       +------------+-------+--------+-------+-------------+
       |            | Class | Method | Field | Constructor |
       +------------+-------+--------+-------+-------------+ 
       | Private    |  No   |   Yes  |  Yes  |    Yes      |
       | Public     |  Yes  |   Yes  |  Yes  |    Yes      |
       | Static     |  No   |   Yes  |  Yes  |    No       |
       | Final      |  Yes  |   Yes  |  Yes  |    No       |
       | Abstract   |  Yes  |   Yes  |  No   |    No       |
       +------------+-------+--------+-------+-------------+

       Private and Public cannot be combined.

       If a class is Final it cannot be subclassed.
       If a field is Final it cannot be assigned.
       If a field is Final it is a class variable.
       If a method is Static is it a class method.
       If a method is Static it cannot call other non-static methods 
        in the same class, it can call other static methods in other 
        classes as object.method or class.method and it can call other
        non-static methods as object.method.
       Static methods can be called by anyone, either as object.method or as
        class.method.
       Static fields can be accessed (if they are public) by anyone either by
        object.field or class.field.
       If a Method, Field or Constructor is private it can be accessed from
        within the class ONLY!

       Abstract methods cannot be final or static. 

       Interface Fields are automtically final.

	See Documentation.txt section 1) for an example. */

	public void set(boolean isClass, boolean isConstructor, Sequence seq) {
		for (int i=0; i<seq.nchildren; i++) {
			set(isClass, isConstructor, (Modifier)seq.children[i]);
		}
	}

	public void set(boolean isClass, boolean isConstructor, Modifier m) {
		switch(m.getModifier()) {
		case Modifier.Public: {
			if (isPrivate())
				Error.error("'private' and 'public' modifiers cannot be used together.");
			else if (isPublic())
				Error.error("'public' modifier repeated.");
			else
				mPublic = true;
			break;
		}
		case Modifier.Private: {
			if (isPublic())
				Error.error("'private' and 'public' modifiers cannot be used together.");
			else if (isPrivate())
				Error.error("'private' modifier repeated.");
			else if (isClass) 
				Error.error("Class cannot be declared 'private'.");
			else
				mPrivate = true;
			break;
		}
		case Modifier.Final: {
			if (isFinal()) 
				Error.error("'final' modifier repeated.");
			else if (isAbstract())
				Error.error("Illegal combination of modifiers: abstract and final");
			else if (isConstructor)
				Error.error("Constructors cannot be declared 'final'.");
			else
				mFinal = true;
			break;
		}
		case Modifier.Static: {
			if (isStatic())
				Error.error("'static' modifier repeated.");
			else if (isClass) 
				Error.error("Class cannot be declared 'static'.");
			else if (isConstructor) 
				Error.error("Constructors cannot be declared 'static'.");
			else if (isAbstract())
				Error.error("'static' and 'abstract' modifiers cannot be used together");
			else
				mStatic = true;
			break;
		}
		case Modifier.Abstract: {
			if (isConstructor)
				Error.error("Constructors cannot be declared 'abstract'");
			if (isFinal())
				Error.error("Illegal combination of modifiers: abstract and final");
			if (isStatic())
				Error.error("Illegal combination of modifiers: abstract and static");
			mAbstract = true;
			break;
		}
		default:
			Error.error("Unknown modifier.");
		}
	}

	public String toString() {
		String s = "";
		if (isPublic()) 
			s += "public ";
		if (isPrivate())
			s += "private ";
		if (isStatic())
			s += "static ";
		if (isFinal())
			s += "final ";
		if (isAbstract()) 
			s += "abstract ";
		return s;
	}

}



