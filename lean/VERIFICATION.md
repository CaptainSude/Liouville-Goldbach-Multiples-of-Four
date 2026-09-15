# Verification record

Checked on 15 September 2026.

- Lean: `v4.34.0-rc2`, compiler commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`.
- Mathlib: `de2ef68216c6074f338c8e61890ee0a379ddfb9b`.
- Every dependency checkout matched its revision in `lake-manifest.json`.
- The delivered project sources were built afresh with `lake build`, using the pinned dependency cache. Result: **success**, including `Audit.lean` (1204 build jobs).
- Full output is in `BUILD-LOG.txt`.
- No `sorry`, `admit`, `native_decide`, unsafe declaration, or project axiom occurs in the three proof modules.
- The final theorem's logical axiom dependencies are exactly `propext`, `Classical.choice`, and `Quot.sound`. The build includes a `#guard_msgs` check of this list.

The final theorem still has the explicit parameter `hM : MangerelNonextremality`. Its type is printed by the audit. This parameter expresses the published unconditional Theorem 1.2 of Mangerel (2024), whose proof is outside this formalization. The audit's axiom list does not discharge that hypothesis.

The three mathematical modules contain 310 lines including comments and blank lines. They verify the actual Liouville-function conclusion for every positive multiple of four, including 4. No assertion about the full conjecture or publication novelty is part of this verification.

The archive contains source, pinned build configuration, license, documentation, and this build record. It omits downloaded dependencies and generated compiled files; the README explains how to rebuild them.
