//(4)
//#10: Syntax error:
//
//        int b = (name) long
//                       ^
public class CastTest1 {
    private long name=0;
    
    public void f() {
        int b = (name) long;
    }
}
