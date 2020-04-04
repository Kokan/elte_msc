import java.lang.*;
import java.io.*;

class Stuff {

  class Middle extends Thread {
    PipedOutputStream out;
    PipedInputStream in;
  public
    Middle(PipedInputStream in, PipedOutputStream out) {
      this.out = out;
      this.in = in;
    }
  public
    void run() {

      try {
        int data = in.read();
          System.out.println("data " + data);
        while (data != -1) {

          data = in.read();
          System.out.println("data " + data);
          out.write(data); out.flush();
        }
        in.close();
      } catch (IOException e) {
          System.out.println("throw " + e);
      };
    }
  }

  class End extends Thread {
    PipedOutputStream out;
    PipedInputStream in;
  public
    End(PipedInputStream in, PipedOutputStream out) {
      this.out = out;
      this.in = in;
    }
  public
    void run() {

      try {
        in.read();

        while (true) {
          int data = in.read();
          System.out.println("data " + data);
          out.write(data);
        }
      } catch (IOException e) {
          System.out.println("throw " + e);
      };
      try {
        in.close();
        out.write(-1);
      } catch (IOException e) {
          System.out.println("throw " + e);
      };
    }
  }

  public void
  Main() {
    try {
      PipedOutputStream out = new PipedOutputStream();
      PipedInputStream in = new PipedInputStream(out);
      PipedOutputStream mout = new PipedOutputStream();

      (new Middle(in, out)).start();

      //PipedInputStream min = new PipedInputStream(mout);
      //(new End(in, out)).start();

      for (int i = 1; i < 3; ++i)
          out.write(i);
      out.flush();


      try {
      Thread.sleep(10);
       } catch (InterruptedException e) {}

    } catch (IOException e) {
          System.out.println("throw " + e);
    }
  }

public
  static void main(String[] args) { (new Stuff()).Main(); }
};
