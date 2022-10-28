//(4)
//#13: Syntax error:
//
//                else
//                ^
public class IfTest2 {
    void f() {
        int a, b, c, d;
        a = b = c = d = 0;
        if (a == b || c == d - 1) {
            a++;
        } else {
                else {
                    a--;
                }
        }
    }
}
