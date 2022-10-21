public class Thread extends java.lang.Thread {
    private java.lang.Runnable runnable = null;
    public Thread() { }
    public Thread(Runnable runnable) {
	super(runnable);
	this.runnable = runnable;
    }
    public void run() { }
    public void start() {
	if (runnable != null)
	    new java.lang.Thread(runnable).start();
	else
	    super.start();
    }
    public static void sleep(long millis) {
	try {
	    java.lang.Thread.sleep(millis);
	} catch (Exception e) { }
    }
}