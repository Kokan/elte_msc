import java.lang.*;

class Task01 {
  static class RandomThread implements Runnable {
    RandomThread() {}

  public
    void run() {
      for (;;)
      try {
      Thread.sleep(1000);
       } catch (InterruptedException e) {}
    }
  }

  public static void
  main(String[] args) {
    System.out.print("start");

    for (;;) {
       Runnable runnable = new RandomThread();
       Thread thread = new Thread(runnable);

       thread.start();
    }
  }
}
