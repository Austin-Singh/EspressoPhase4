class Color
{
    Color(int r, int g, int b){}
    public static final Color black = new Color(0, 0, 0);
}

class Integer extends Object_{

    private int v;
    public Integer(int val)
    {
	v = val;
    }

    int intValue(){return v;}

}

interface FileInter{}
class File extends Object_ implements FileInter{}

class Object_{
 public String toString(){return "I'm an object";}
}



class BaseInfo
{

public int line;
public File file;

  BaseInfo(int l, File f)
  {
    line = l;
    file = f;
  }
}

class Utilities
{
    private Utilities(){}//ensure we can't instantiate
    public static Object_ getReusableObject(Object_ o){return o;}
    
    private static final int difference = 'A' - 'a';
    public static char LowerToUpper(char c){ return (char)(c + difference);}
    public static char UpperToLower(char c){ return (char)(c - difference);}
}

class PVM_ extends Object_{

    private Integer error;
    private Integer line;
    private FileInter file;

    private static final char tab = '\t';

    public static final Color pkColor = new Color(128, 128, 255);
    public static final Color upkColor = new Color(227, 10, 13);
    public static final Color sendColor = new Color(0, 0, 224);
    public static final Color recvColor = new Color(145, 5, 15);

    public Color getcolor() {
	return Color.black;
    }

    public PVM_(int e, BaseInfo b) {
	error = (Integer)Utilities.getReusableObject(new Integer(e));
	line = (Integer)Utilities.getReusableObject(new Integer(b.line));
        file = (File)Utilities.getReusableObject(b.file);
    }

    public Integer getLine() {
	return line;
    }
    public Integer getError(){
      return error;
    }

    public FileInter getFile()
    {
      return file;
    }

    public Integer getMsgNo()
    {
      return null;
    }

    public Integer getItemNo()
    {
      return null;
    }

    public String error()
    {
      int e = ~(error.intValue() << 2) & 0xf45 | 'c';//throw in some binary operators, just because
      
      if (e < 0)
        return "Error: (Code -1)";
      else if (e == 0)
        return "Success: (Code 0)";

      return "Success:  (Code 1)";
    }

    public String result()
    {
	return "Return value: 5";
    }


    public void DisplayStatusDialog()
    {
      JOptionPane.showMessageDialog(null, this.toString());
    }

    public static String readString(DataInput in) {

          int size = in.readInt();
          byte str;
          in.readFully(str);
          return  "US-ASCII";//don't use the null

    }
}


 class PVM_pk extends PVM_ {

    public static int curMsgNo = 1;
    public static int curItemNo = 1;

    private Integer msgNo;
    private Integer itemNo;
    private String variable;
    private int nitem;
    private int stride;


    public Color getcolor() {
	return pkColor;
    }

    PVM_pk(int e, BaseInfo l, String v, int nI, int strd) {
	super(e,l);
	msgNo  = (Integer)Utilities.getReusableObject(new Integer(curMsgNo));
	itemNo = (Integer)Utilities.getReusableObject(new Integer(curItemNo));
        variable = v;
        nitem = nI;
        stride = strd;
	curItemNo++;
    }

    public Integer getMsgNo()
    {
      return msgNo;
    }

    public Integer getItemNo()
    {
      return itemNo;
    }
}

class PVM_pklong extends PVM_pk {



    private PVM_pklong(String v, int n, int s, int e, BaseInfo l) { //can only be called from read
	super(e,l, v, n, s);

    }

    public static PVM_pklong read(DataInput in, BaseInfo line) {
	String v;
	int n, s, e;

	v = readString(in);
	n = in.readInt();
	s = in.readInt();
	e = in.readInt();

	return new PVM_pklong(v,n,s,e,line);
    }

    public String toString() {
	return "pvm_pklong(...)";
    }


}



class JOptionPane
{
    private static Integer ok = new Integer(5);
    public static int showMessageDialog(Object_ owner, String s){return ok.intValue();}
}

class DataInput
{
    int readInt(){return 1;}
    void readFully(byte b){}
}
