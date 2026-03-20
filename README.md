# aps-rice-lean

Abstract Lean 4 formalization of recursion, Rice's theorem, and halting undecidability for a **representability-restricted** Acceptable Programming System (APS).

## What this is

This is an abstract formalization of computability-theoretic results (recursion theorem, Rice's theorem, halting undecidability) for a representability-restricted APS interface. The current interface is intended as a **workable honest abstraction**, not necessarily the final canonical acceptable-numbering interface. The project evolved through axiom/interface refinement guided by theorem-proving failures.

## What this is not

- **Not** "We proved a new version of Rice's theorem."
- **Not** "This is the definitive minimal APS abstraction."
- **Not** "Evolution discovered a breakthrough in computability theory."

The value here is: clean formalization, abstraction repair, theorem engineering, and a good benchmark/example

## Interface caution

The current APS interface is deliberately representability-restricted and avoids the earlier overpowered quantification over all functions. A future refinement may further minimize or canonicalize the closure assumptions (`diag_rep`, `smn_rep`, etc.).

## Structure

| Module | Contents |
|--------|----------|
| `APS/Core.lean` | APS structure, representability predicates, extensionality, nontriviality |
| `APS/Recursion.lean` | Recursion theorem |
| `APS/Rice.lean` | Rice's theorem, halting undecidability |
| `APS/Corollaries.lean` | `rice_theorem_not`, `extensional_not`, `nontrivial_not` |

## Build

```bash
lake update
lake build
```

Requires Lean 4 (v4.29.0-rc3) and Mathlib v4.29.0-rc3.

## License

MIT (or as specified in the repo)
