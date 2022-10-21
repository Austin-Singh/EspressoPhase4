import Runnable;

public class Thread implements Runnable {
    private Runnable runnable = null;
    public Thread(Runnable runnable) { 
	this.runnable = runnable;
    }
    public Thread() { }
    public void run() { }
    public final void start() {
	if (runnable != null)
	    runnable.run();
	else
	    this.run();
    }
}
