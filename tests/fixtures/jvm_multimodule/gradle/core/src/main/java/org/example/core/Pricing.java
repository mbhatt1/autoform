package org.example.core;

public final class Pricing {
    private Pricing() {}

    public static long total(long unitPrice, int quantity) {
        return unitPrice * quantity;
    }
}
