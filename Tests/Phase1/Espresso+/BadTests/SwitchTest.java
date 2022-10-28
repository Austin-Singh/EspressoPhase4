//(4)
//#11: Syntax error:
//
//        case 2: case 3;
//                      ^
public class SwitchTest {
    public void f() {
        int a=0;
        switch(a){ 
        case 1: break;
        case 2: case 3;
        default: a++;
            break;
        }
        
    }
}
