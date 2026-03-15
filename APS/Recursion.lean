import APS.Core
import Mathlib.Data.Part
import Mathlib.Data.PFun
import Mathlib.Data.Nat.Pairing

/-! For every representable total function h, there exists a fixed point e such that φ_e = φ_{h(e)}. -/

open Nat (pair unpair)
open Classical

theorem recursion_theorem (aps : AcceptableProgrammingSystem) [HasRepresentableComp aps]
  (h : ℕ → ℕ) (h_smn_rep : RepresentableUnary aps (fun x => h (aps.smn x x))) :
  ∃ e, ∀ n, aps.φ e n = aps.φ (h e) n := by
  obtain ⟨k, hk⟩ := HasRepresentableComp.comp (fun x => h (aps.smn x x)) h_smn_rep
  use aps.smn k k
  intro n
  rw [aps.smn_spec k k n]
  exact hk k n
