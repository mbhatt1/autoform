package org.example.core;

class PricingTest {
    void total() {
        if (Pricing.total(3, 4) != 12) throw new AssertionError();
    }
}
