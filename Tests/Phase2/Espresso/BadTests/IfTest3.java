//(4)
//#18: Syntax error:
//
//        else
//        ^
public class IfTest3 {
    public int f() {
        int a=0;
        int b=0;
        if (a==0) {
            
        }
        if (b==1) {
            a++;
        } else {
            b++;        
        }
        else {
            a+=b;
        }
        return 0;
    }
}
