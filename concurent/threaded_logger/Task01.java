

class Task01 {

  class DummyThread extends Thread {
    LoggerInterface logger;
    int thread_id;
    DummyThread(Logger logger, int i) {
      this.logger = logger;
      thread_id = i;
    };
    public void run() {
      for (;;)
        logger.warning("DummyThread(" + thread_id + ")");
    }
  };

  public static void main(String[] args) { (new Task01()).Main(args); }

  public void Main(String[] args) {

    Logger logger = new Logger();

    for (int i = 0; i < 5; ++i)
      (new DummyThread(logger, i)).start();

    for (;;) {
      logger.error("msg#1");
      logger.warning("msg#1");
      logger.debug("msg#1");
    }
  }
}
