package org.example.api;

public final class Limits {
    private Limits() {}

    public static int clamp(int value, int max) {
        return value > max ? max : value;
    }
}
