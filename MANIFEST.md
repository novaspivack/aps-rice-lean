# aps-rice-lean — manifest

**Toolchain:** `leanprover/lean4:v4.29.0-rc3`  
**Mathlib:** v4.29.0-rc3 (via `lakefile.lean` / `lake-manifest.json`)  
**Build:** `lake build` from this directory  
**Root import:** `APS.lean`  
**Last verified:** 2026-03-22 — matches pinned toolchain; abstract Rice / halting / recursion formalization for representability-restricted APS.

---

## Sorry / axiom policy

- **Target:** no `sorry` in proof terms on the shipped modules (`README.md`); check with `rg '\bsorry\b' APS/` from repo root.
- **Custom axioms:** interface axioms may appear as documented in `APS/Core.lean`; see `README.md`.
