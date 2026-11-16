package org.example.api;

class LimitsTest {
    void clamp() {
        if (Limits.clamp(5, 3) != 3) throw new AssertionError();
    }
}
