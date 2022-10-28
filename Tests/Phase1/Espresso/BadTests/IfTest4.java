//(4)
//#11: Syntax error:
//
//        } else (a==1){
//                     ^
public class IfTest4 {
    int a=0;
    public void f() {
        if (a==0) {
            a--;
        } else (a==1){
                a++;
            }
    }
}
