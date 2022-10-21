package AST;
import Utilities.Error;

public abstract class Type extends AST {

	public Type(AST a) {
		super(a);
	}

	public Type(Token t) {
		super(t);
	}

	public abstract String typeName() ;

	public abstract String signature() ;

	public String getTypePrefix() {
		if (this.isClassType() || this.isNullType() || isStringType() || isArrayType())
			return "a";
		else if (this.isIntegerType() || this.isShortType() ||
				this.isByteType()    || this.isCharType() || this.isBooleanType())
			return "i";
		else if (this.isFloatType())
			return "f";
		else if (this.isStringType()) 
			return "a";
		else if (this.isLongType())
			return "l";
		else if (this.isDoubleType())
			return "d";
		else 
			Error.error("Type.java:getTypePrefix(): no prefix for type: " + typeName());
		return "";
	}

	public boolean identical(Type other) {
		// TODO this was changed 3/29/12 from typename() to signature()
		if (signature().equals(other.signature()))	    
			return true;
		else if ((this instanceof ClassType) && (other instanceof NullType))
			return true;
		else if ((this instanceof NullType) && (other instanceof ClassType))
			return true;
		else
			return false;
	}

	public boolean assignable() {
		return (!typeName().equals("null") && !typeName().equals("void"));
	}

	public static boolean assignmentCompatible(Type var, Type val) {
		if (var.identical(val)) // Same type
			return true;
		else if (var.isNumericType() && val.isNumericType()) {
			// Both are numeric (primitive) types.
			PrimitiveType pvar = (PrimitiveType)var;
			PrimitiveType pval = (PrimitiveType)val;

			// double :> float :> long :> int :> short :> byte
			if (pvar.getKind() == PrimitiveType.CharKind)
			    return false; // do not allow assignment of numeric values to chars
			if (pval.getKind() == PrimitiveType.CharKind)
				return (pvar.getKind() != PrimitiveType.ByteKind &&
					pvar.getKind() != PrimitiveType.ShortKind);
			return (pvar.getKind() >= pval.getKind()); // ok to assign char value to none byte/short var
		} else if ((var instanceof ClassType) && (val instanceof ClassType)) {
			// Both are of class type.
			// super :> sub.
			return isSuper((ClassType)var, (ClassType)val);
		} else if ((var instanceof ClassType) && (val instanceof NullType)) 		 
			return true;
		else if ((var instanceof ArrayType) && (val instanceof NullType))
		    return true;
		return false;
	}

	public boolean isIntegerType() {
		return (this instanceof PrimitiveType && ((PrimitiveType)this).getKind() == PrimitiveType.IntKind);
	}

	public boolean isArrayType() {
		return (this instanceof ArrayType);
	}

	public boolean isBooleanType() {
		return (this instanceof PrimitiveType && ((PrimitiveType)this).getKind() == PrimitiveType.BooleanKind);
	}

	public boolean isByteType() {
		return (this instanceof PrimitiveType && ((PrimitiveType)this).getKind() == PrimitiveType.ByteKind);
	}

	public boolean isShortType() {
		return (this instanceof PrimitiveType && ((PrimitiveType)this).getKind() == PrimitiveType.ShortKind);
	}

	public boolean isCharType() {
		return (this instanceof PrimitiveType && ((PrimitiveType)this).getKind() == PrimitiveType.CharKind);
	}

	public boolean isLongType() {
		return (this instanceof PrimitiveType && ((PrimitiveType)this).getKind() == PrimitiveType.LongKind);
	}

	public boolean isClassType() {
		return (this instanceof ClassType);
	}

	public boolean isVoidType() {
		return (typeName().equals("void"));
	}

	public boolean isNullType() {
		return (this instanceof NullType);
	}

	public boolean isStringType() {
		return (typeName().equals(PrimitiveType.names[PrimitiveType.StringKind]));
	}

	public boolean isFloatType() {
		return (this instanceof PrimitiveType && ((PrimitiveType)this).getKind() == PrimitiveType.FloatKind);
	}

	public boolean isDoubleType() {
		return (this instanceof PrimitiveType && ((PrimitiveType)this).getKind() == PrimitiveType.DoubleKind);
	}

	public boolean isNumericType() {
		return (isFloatType() || isDoubleType() || isIntegralType());
	}

	public boolean isIntegralType() {
		return (isIntegerType() || isShortType() || isByteType() || isCharType() || isLongType());
	}

	public boolean isPrimitiveType() {
		return isNumericType() || isVoidType() || isNullType() || isStringType() || isBooleanType();
	} 


	public static String parseSignature(String sig) {
		String s = "";
		for (int i=0; i<sig.length(); i++) {
			switch(sig.charAt(i)) {
			case 'B': s = s + " byte"; break;
			case 'C': s = s + " char"; break;
			case 'S': s = s + " short"; break;
			case 'I': s = s + " int"; break;
			case 'J': s = s + " long"; break;
			case 'Z': s = s + " boolean"; break;
			case 'F': s = s + " float"; break;
			case 'D': s = s + " double"; break;
			case 'V': s = s + " void"; break;
			case 'L': {
				int j=i;
				while (sig.charAt(j) != ';') 
					j++;
				String cl = sig.substring(i+1,j);
				i = j;
				s = cl.equals("java/lang/String") ? s + " String" : s + " " + cl;
				break;
			}
			case '[': s = s + " ["; break;
			}
		}
		return s;
	}

	/** Returns the number of stack words a value of this type takes up (always 1 or 2).
	 * 
	 * @return 1 or 2 - the number of stack words a value of this type takes up.
	 */
	public int width() {
		if (isDoubleType() || isLongType())
			return 2;
		return 1;
	}
	
	public static boolean isSuper(ClassType sup, ClassType sub) {
		ClassDecl supd = sup.myDecl;
		ClassDecl subd = sub.myDecl;

		if (supd.name().equals(subd.name()))
			return true;

		// Take the sub classes super class
		ClassType subdsuper = subd.superClass();
		boolean found = false;
		if (subdsuper != null) 
			found = isSuper(sup, subdsuper);
		for (int i=0; i<subd.interfaces().nchildren; i++) {
			found = found || isSuper(sup, (ClassType)subd.interfaces().children[i]);
		}
		return found;

	}

}             




