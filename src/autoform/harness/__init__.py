"""Neural-symbolic formalization harness.

    Program → CPIR → evidence → generator (templates / LLM) → critic
            → SemIf judge (selection, routing) → obligation compiler → Lean
            → counterexample → SemIf judge (classification, repair ranking) → reverify

Generators and the judge propose and rank; only the Lean kernel and the
deterministic structural checker certify. See docs/harness.md.
"""
