//(1)
//#7: Cannot instantiate interface 'i'.
interface i {
}
class test {
    public static void main() {
	i ii = new i();
    }
}
