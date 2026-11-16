public class Box {
    static boolean intBox(Integer a, Integer b) { return a == b; }
    static boolean intBoxNe(Integer a, Integer b) { return a != b; }
    static boolean boxPrim(Integer a, int b) { return a == b; }
    static boolean primBox(int a, Integer b) { return a == b; }
    static boolean boxPrimNe(Integer a, int b) { return a != b; }
    static boolean litBox(Integer a) { return a == 5; }
    static boolean longPrim(Long a, long b) { return a == b; }
    static boolean charPrim(Character a, char b) { return a == b; }
    static boolean boolPrim(Boolean a, boolean b) { return a == b; }
    static boolean plain(int a, int b) { return a == b; }
    static boolean longBox(Long a, Long b) { return a == b; }
    static boolean boolBox(Boolean a, Boolean b) { return a == b; }
    static boolean charBox(Character a, Character b) { return a == b; }
    static boolean strBox(String a, String b) { return a == b; }
    static boolean nullBox(Integer a) { return a == null; }
    static int unboxAssign(Integer a) { int x = a; return x + 1; }
    static boolean callRes() { return getI() == getI(); }
    static boolean callPrim() { return getI() == 5; }
    static Integer getI() { return 1; }
    static boolean dblBox(Double a, Double b) { return a == b; }
    static boolean dblPrim(Double a, double b) { return a == b; }
    static boolean rightBox(Integer a) { return getP() == a; }
    static boolean leftPrelude(Integer a, int x) { return a == (x += 1); }
    static boolean argBox(Integer a, int b) { return id(a == b); }
    static boolean id(boolean x) { return x; }
    static int getP() { return 1; }
}
