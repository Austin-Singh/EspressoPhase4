//(4)
//#8: Syntax error:
//
//        for (int i=0;i<=10,
//                          ^
public class ForTest1 {
    int f() {
        for (int i=0;i<=10,i++) {
            i++;
        }
        return 0;
    }
}
