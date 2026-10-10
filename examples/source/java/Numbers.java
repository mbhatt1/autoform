public class Numbers {
  public static long add(long a, long b) { return a + b; }
  public static long div(long a, long b) { return a / b; }
  public static int shift(int a, int b) { return a << b; }
  public static long unsigned(long a, int b) { return a >>> b; }
  public static long inc(long a) { a += 1; return a; }
  public static byte bump(byte a) { a++; return a; }
  public static byte compound(byte a, int b) { a += b; return a; }
}