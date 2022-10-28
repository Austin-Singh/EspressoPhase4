//(114)
//
//1234567890
//---
//2469135780
//3703703670
//4938271560
//6172839450
//0: 0
//1: 1
//2: 1
//3: 2
//4: 3
//5: 5
//6: 8
//7: 13
//8: 21
//9: 34
//10: 55
//11: 89
//12: 144
//13: 233
//14: 377
//15: 610
//16: 987
//17: 1,597
//18: 2,584
//19: 4,181
//20: 6,765
//21: 10,946
//22: 17,711
//23: 28,657
//24: 46,368
//25: 75,025
//26: 121,393
//27: 196,418
//28: 317,811
//29: 514,229
//30: 832,040
//31: 1,346,269
//32: 2,178,309
//33: 3,524,578
//34: 5,702,887
//35: 9,227,465
//36: 14,930,352
//37: 24,157,817
//38: 39,088,169
//39: 63,245,986
//40: 102,334,155
//41: 165,580,141
//42: 267,914,296
//43: 433,494,437
//44: 701,408,733
//45: 1,134,903,170
//46: 1,836,311,903
//47: 2,971,215,073
//48: 4,807,526,976
//49: 7,778,742,049
//50: 12,586,269,025
//51: 20,365,011,074
//52: 32,951,280,099
//53: 53,316,291,173
//54: 86,267,571,272
//55: 139,583,862,445
//56: 225,851,433,717
//57: 365,435,296,162
//58: 591,286,729,879
//59: 956,722,026,041
//60: 1,548,008,755,920
//61: 2,504,730,781,961
//62: 4,052,739,537,881
//63: 6,557,470,319,842
//64: 10,610,209,857,723
//65: 17,167,680,177,565
//66: 27,777,890,035,288
//67: 44,945,570,212,853
//68: 72,723,460,248,141
//69: 117,669,030,460,994
//70: 190,392,490,709,135
//71: 308,061,521,170,129
//72: 498,454,011,879,264
//73: 806,515,533,049,393
//74: 1,304,969,544,928,657
//75: 2,111,485,077,978,050
//76: 3,416,454,622,906,707
//77: 5,527,939,700,884,757
//78: 8,944,394,323,791,464
//79: 14,472,334,024,676,221
//80: 23,416,728,348,467,685
//81: 37,889,062,373,143,906
//82: 61,305,790,721,611,591
//83: 99,194,853,094,755,497
//84: 160,500,643,816,367,088
//85: 259,695,496,911,122,585
//86: 420,196,140,727,489,673
//87: 679,891,637,638,612,258
//88: 1,100,087,778,366,101,931
//89: 1,779,979,416,004,714,189
//90: 2,880,067,194,370,816,120
//91: 4,660,046,610,375,530,309
//92: 7,540,113,804,746,346,429
//93: 12,200,160,415,121,876,738
//94: 19,740,274,219,868,223,167
//95: 31,940,434,634,990,099,905
//96: 51,680,708,854,858,323,072
//97: 83,621,143,489,848,422,977
//98: 135,301,852,344,706,746,049
//99: 218,922,995,834,555,169,026
//100: 354,224,848,179,261,915,075
//0
//354,224,848,179,261,915,075
//125475243067621153271396401396356512255625
//2178
//9876543120
//125,475,243,067,621,153,271,396,401,396,356,512,255,625
//354224848179261915075
import Integer;
import System;

public class BigInt {
    
    private boolean negative = false;
    private int[] digits;
    private int size;

    private int howManyDigits(long l) {
	int c = 0;
	if (l == 0)
	    return 1;  
	while (l>0) {
	    c++;
	    l >>= 2;
	}       
	return c;
    }

    public BigInt(long l) {
	this(""+l);
    }

    public BigInt(String s) {
	digits = new int[s.length()];
	for (int i=0; i<s.length(); i++)
	    digits[i]=Integer.parseInt(""+s.charAt(s.length()-i-1));
	size = s.length();
    }

    public String toString() {
	String s = "";
	for (int i=0; i<digits.length; i++)
	    s = digits[i] + s;
	return s;
    }

    public void print() {
	String s = "";
	for (int i=0; i<digits.length; i++)
	    s = digits[i] + s;
	System.out.println(s);
    }
    
    public String format() {
	String s = "";
	int j=0;
	for (int i=0; i<digits.length; i++) {
	    s = digits[i] + s;
	    if ((i+1)%3 == 0 && i!=digits.length-1)
		s = "," + s;
	}
	return s;
    }

    private void trim() {
	int i=0;
	while (digits[digits.length-1-i] == 0 && i < digits.length-1) 
	    i++;
	int newsize = digits.length-i;
	int digits2[] = new int[newsize];
	for (int j=0; j<newsize; j++)
	    digits2[j] = digits[j];
	digits = digits2;
	size=digits.length;
    }
	    
    public int digitAt(int i) {
	return digits[i];
    }

    public void setDigitAt(int i, int val) {
	digits[i] = val;
    }

    public int size() {
	return size;
    }


    public BigInt(BigInt bi, int size) {
	digits = new int[size];
	for (int i=0; i<size; i++)
	    if (i<bi.size())
		digits[i] = bi.digitAt(i);
	    else
		digits[i] = 0;
	this.size=size;
    }

    private int min(int x, int y) {
	return (x<y)?x:y;
    }
    private int max(int x, int y) {
	return (x>y)?x:y;
    }

    public BigInt pad(int zeros) {
	BigInt bi = new BigInt(new BigInt("0"),size()+zeros);
	for (int i=0; i< zeros; i++)
	    bi.setDigitAt(i,0);
	for (int i=0; i<size(); i++)
	    bi.setDigitAt(i+zeros,digits[i]);
	bi.trim();
	return bi;
    }

    public BigInt multiplyByDigit(int d) {
	BigInt bi = new BigInt(new BigInt("0"), size()+1);
	int carry = 0;
	int i=0;
	for (i=0;i<size(); i++) {
	    int prod = d*digits[i] + carry;
	    if (prod > 10) {
		carry = prod / 10;
		prod = prod % 10;
	    } else
		carry = 0;
	    bi.setDigitAt(i,prod);
	}
	bi.setDigitAt(i,carry);
	bi.trim();
	return bi;
    }

    public BigInt multiply(BigInt i1) {
	BigInt bi = new BigInt(new BigInt("0"), (i1.size()*size)-1);
	BigInt temp = null;
	for (int j=0;j<i1.size(); j++) {
	    temp = this.multiplyByDigit(i1.digitAt(j));
	    temp = temp.pad(j);
	    bi = bi.add(temp);
	}
	bi.trim();
	return bi;
    }

    public BigInt add(BigInt i1) {
	BigInt bi = new BigInt(i1, max(i1.size(),size)+1);
	int carry = 0;
	int sum =0;
	int i;
	for (i=0; i< min(size(), i1.size()); i++) {
	    sum = digits[i] + i1.digitAt(i) + carry;
	    
	    if (sum > 9) {
		sum = sum - 10;
		carry = 1;
	    } else
		carry = 0;
	    bi.setDigitAt(i, sum);
	}
	for (int j=i;j<size();j++) {
	    sum = digits[j] + carry;
	    if (sum > 9) {
		sum = sum - 10;
		carry = 1;
	    } else
		carry = 0;
	    bi.setDigitAt(j, sum);
	}
	for (int j=i;j<i1.size();j++) {
	    sum = i1.digitAt(j) + carry;
	    if (sum > 9) {
		sum = sum - 10;
		carry = 1;
	    } else
		carry = 0;
	    bi.setDigitAt(j, sum);
	}
	if (carry == 1)
	    bi.setDigitAt(bi.size()-1, 1);
	bi.trim();
	return bi;
    }

}

public class Assignment5 {

    public static void main(String args[]) {
	BigInt bi  = new BigInt("1234567890");
	BigInt bi3;

	bi.print();
	System.out.println("---");
	bi3 = bi.add(bi);
	System.out.println(bi3);
	bi3 = bi3.add(bi);
	System.out.println(bi3);
	bi3 = bi3.add(bi);
	System.out.println(bi3);
	bi3 = bi3.add(bi);
	System.out.println(bi3);
	
	BigInt i1 = new BigInt("1");
	BigInt i2 = new BigInt("1");
	System.out.println("0: 0");
	System.out.println("1: " + i1);
	System.out.println("2: " + i2);
	BigInt i3 = null;
	for (int i=3; i<= 100; i++) {
	    i3 = i1.add(i2);
	    i1=i2;
	    i2=i3;
	    System.out.println(i + ": " + i3.format());
	}
	BigInt ii = new BigInt("0");
	System.out.println(ii);
	System.out.println(i3.add(ii).format());
	System.out.println(i3.multiply(i3));

	System.out.println(new BigInt("363").multiplyByDigit(6));

	System.out.println(new BigInt("1234567890").multiply(new BigInt("8")));
	System.out.println(i3.multiply(i3).format());
	System.out.println(i3);
    }
    
    

}

