import Mathlib.Data.Part
import Mathlib.Data.PFun
import Mathlib.Data.Nat.Pairing

/-!
# Acceptable Programming System — Core Interface

Abstract formalization of computability-theoretic results (recursion theorem, Rice's theorem,
halting undecidability) for a **representability-restricted** Acceptable Programming System (APS).

The interface deliberately restricts quantification to representable/computable functions,
avoiding the overpowered quantification over all total functions typical of classical
acceptable numberings.

## Interface Disclaimer

The current APS interface is intended as a **workable honest abstraction**, not necessarily
the final canonical acceptable-numbering interface. This project evolved through axiom/interface
refinement guided by theorem-proving failures. A future refinement may further minimize or
canonicalize the closure assumptions (`diag_rep`, `smn_rep`, etc.).
-/

open Nat (pair unpair)
open Classical

/-! ## Acceptable Programming System -/

structure AcceptableProgrammingSystem where
  /-- The partial recursive function interpreter: φ_e(n). -/
  φ : ℕ → ℕ →. ℕ
  /-- The s-m-n function: partial application. -/
  smn : ℕ → ℕ → ℕ
  smn_spec : ∀ e x n, φ (smn e x) n = φ e (pair x n)

/-! ## Representability Predicates -/

/-- A total function h : ℕ → ℕ is "representable" if there exists an index whose partial function agrees with h everywhere. -/
def RepresentableUnary (aps : AcceptableProgrammingSystem) (h : ℕ → ℕ) : Prop :=
  ∃ e, ∀ n, aps.φ e n = Part.some (h n)

/-- A Bool-valued function d is "representable" if there exists an index computing it. -/
def RepresentableBool (aps : AcceptableProgrammingSystem) (d : ℕ → Bool) : Prop :=
  ∃ e, ∀ n, aps.φ e n = Part.some (if d n then 1 else 0)

/-! ## Composition Axiom (restricted to representable functions) -/

class HasRepresentableComp (aps : AcceptableProgrammingSystem) where
  comp : ∀ (h : ℕ → ℕ), RepresentableUnary aps h →
    ∃ k, ∀ x n, aps.φ k (pair x n) = aps.φ (h x) n

/-! ## Extensionality and Nontriviality -/

def Extensional (aps : AcceptableProgrammingSystem) (P : (ℕ →. ℕ) → Prop) : Prop :=
  ∀ e₁ e₂, (∀ n, aps.φ e₁ n = aps.φ e₂ n) → (P (aps.φ e₁) ↔ P (aps.φ e₂))

def NontrivialProp (aps : AcceptableProgrammingSystem) (P : (ℕ →. ℕ) → Prop) : Prop :=
  (∃ e_yes, P (aps.φ e_yes)) ∧ (∃ e_no, ¬ P (aps.φ e_no))
