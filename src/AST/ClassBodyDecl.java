package AST;
import java.util.*;

public abstract class ClassBodyDecl extends AST {
        
    public int localsUsed = 1;

    public ClassBodyDecl(AST a) {
	super(a);
    }

    public abstract boolean isStatic() ;

    public abstract String getname() ;
}
