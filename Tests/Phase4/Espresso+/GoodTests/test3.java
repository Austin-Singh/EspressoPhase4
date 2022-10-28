interface A1{
    public static int five = 5;
    public double myFunc();
    public byte anotherFunc();
}
class B2 implements A1{
    

    public double myFunc(){return (double)five + 7 + anotherFunc() * 'c';}
    private byte anotherFunc(){return (byte)1;}

}



class TernaryMadness
{
    private static final String unk = "unknown";
    
    public static String getUnknown() {return unk;}

    public static double TestFunc(A1 a){return 0.0f;}
    public static int TestFunc(B2 b){return 'q';}

    public static String DigitConvert(int x)
    {

	return x == 0 ? "0": x == 1 ? "1": x == 2 ? "2" : x == 3 ? "3" : x 
== 4 ? "4" : x==5 ? "5": x == 6 ? "6" : x == 7 ? "7" : x == 8 ? "8" : x == 
9 ? "9" : getUnknown();

    }

    public void InterTest()
    {
	((A1)new B2()).myFunc();
	A1 myB = new B2();
	if (myB instanceof B2)
	{
	    TestFunc((B2)myB);
	    
	    if (((B2)myB) instanceof A1){
		TestFunc(myB);
		double d = !true ? TestFunc((B2)myB): (int)myB.anotherFunc();

		this.DigitConvert(A1.five);
		return;
	    }
	}

	return;

    }

    public static void NastySwitch()
    {
	
	switch (5 + 7)
	{
	    
	case 'a': break;
	case 5: break;
	default:
	    new TernaryMadness().InterTest();
	    break;

	}

    }


}

