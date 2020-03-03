import java.lang.*;
import java.util.LinkedList;

class Logger implements LoggerInterface {

  Dst dst;

  Logger() {
    dst = new Logger.Dst();
    dst.start();
  }

  public void log(Level lvl, String msg) {
    dst.add(lvl.toString() + ": " + msg);
  }

  class Dst extends Thread {
    LinkedList<String> buffer;
    Dst() { this.buffer = new LinkedList<String>(); }

    private String getMessage() throws InterruptedException {
      while (buffer.size() == 0)
        wait();
      return buffer.pop();
    }
    public synchronized void run() {
      try {
        while (true) {
          String msg = getMessage();

          System.out.println(msg);
        }
      } catch (InterruptedException e) {
      }
    };
    synchronized void add(String stuff) {
      buffer.add(stuff);
      notify();
    }
  };
};
