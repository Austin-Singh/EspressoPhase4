package Utilities;
public class Version {
    public static String version = "%1.3%";

    public static String changes[] = new String[]{
	"1.0: 2012 November 28th Version",
        "1.1: Fri Nov 30 00:19:36 PST 2012: Versioning added",
        "1.2: Tue Dec  4 21:18:23 PST 2012: Fixed issues with invokestatic",
	"1.3: Sat Apr 18 20:34:00 PST 2015: Fixed issues with arrays of strings, proper check for implementation of abstracts.",
        "@"
    };
    
    public static String getVersion() {
	return version.substring(1,version.length()-1);
    }
	
    public static void versionHistory() {
	for (int i=0;i<changes.length-1; i++)
	    System.out.println(changes[i]);
    }

    public static void main(String args[]) {
	System.out.println("Version: " + getVersion());
	versionHistory();
    }


}
