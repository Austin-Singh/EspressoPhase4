class CleanThread extends Thread
{
    
    public void run()
    {
         
      

       while (ProcessWrapper.processList.size() > 0)
       {
	   ((ProcessWrapper)ProcessWrapper.processList.lastElement()).destroy();
       }

      

       System.out.println("Cleaned up processes");
   }

}


class ProcessWrapper extends Process{

    private Process proc;

    public static final Vector processList = new Vector(); //for thread safety

    private static final Thread cleanupThread = new CleanThread();
    
    static
    {
	Runtime.getRuntime().addShutdownHook(cleanupThread);
    }

    ProcessWrapper(Process p) {
      proc = p;
      processList.add(this);
    }

    public void destroy()
    {
      proc.destroy();
      processList.remove(this);
    }

    public int exitValue()
    {
      return proc.exitValue();
    }

    public int waitFor()
    {
      return proc.waitFor();
    }

    public InputStream getErrorStream()
    {
      return proc.getErrorStream();
    }

    public InputStream getInputStream()
    {
      return proc.getInputStream();
    }

    public OutputStream getOutputStream()
    {
      return proc.getOutputStream();
    }

}


//CLASSES BELOW HERE ARE DUMMY IMPLEMENTATIONS OF THE STANDARD CLASSES


class System
{
    public static final OutputStream out = new OutputStream();
}

class OutputStream extends Object{public void println(String s){}}
class InputStream extends Object{}

abstract class Thread extends Object{public abstract void run();}


abstract class Runtime{
    private static final Runtime inst = new BetterRuntime();
    public static Runtime getRuntime(){return inst;}
    public abstract void addShutdownHook(Thread t);

}

class GoodRuntime extends Runtime
{
    public void addShutdownHook(Thread t){}
}

class BetterRuntime extends GoodRuntime
{
    public void addShutdownHook(Thread t){super.addShutdownHook(t);}
}

class Vector extends Object
{
    public int size(){return 0;}
    public boolean add(Object o){return true;}
    public Object remove(Object o){return o;}
    public Object lastElement(){return null;}
}


class Process extends Object
{
    public OutputStream getOutputStream(){return null;}
    public InputStream getInputStream(){return null;}
    public InputStream getErrorStream(){return null;}
    public int waitFor(){return 0;}
    public int exitValue(){return 0;}
    public void destroy(){}

}


