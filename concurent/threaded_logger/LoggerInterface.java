import java.lang.*;

public interface LoggerInterface {
  public static enum Level { ERR, WARN, DEBUG }
  ;
  default void error(String message) { log(Level.ERR, message); }
  default void warning(String message) { log(Level.WARN, message); }
  default void debug(String message) { log(Level.WARN, message); }

  public void log(Level lvl, String msg);
}
;
