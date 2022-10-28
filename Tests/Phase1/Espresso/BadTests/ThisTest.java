//(4)
//#11: Syntax error:
//
//        this;
//            ^
public class ThisTest {
    ThisTest() {
        
    }
    ThisTest(int a) {
        this;
    }
}