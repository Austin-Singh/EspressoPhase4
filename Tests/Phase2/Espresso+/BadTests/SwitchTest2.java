//(4)
//#11: Syntax error:
//
//                case
//                ^
public class SwitchTest2 {
    void f() {
        int a=0;
        if (a>0) {
            switch(a)
                case 1 : a++;
        }
    }
}
