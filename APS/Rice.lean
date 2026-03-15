import APS.Core
import APS.Recursion
import Mathlib.Data.Part
import Mathlib.Data.PFun
import Mathlib.Data.Nat.Pairing

/-! Rice's Theorem and halting undecidability. -/

open Nat (pair unpair)
open Classical

theorem rice_theorem (aps : AcceptableProgrammingSystem) [HasRepresentableComp aps]
  (P : (ℕ →. ℕ) → Prop) (p_ext : Extensional aps P) (p_non : NontrivialProp aps P)
  (diag_rep : ∀ (d : ℕ → Bool) (e_yes e_no : ℕ), RepresentableBool aps d →
    RepresentableUnary aps (fun x => (if d x then e_no else e_yes)))
  (smn_rep : ∀ (h : ℕ → ℕ), RepresentableUnary aps h → RepresentableUnary aps (fun x => h (aps.smn x x))) :
  ¬ ∃ (d : ℕ → Bool), RepresentableBool aps d ∧ ∀ e, (d e = true ↔ P (aps.φ e)) := by
  rintro ⟨d, d_rep, hd⟩
  obtain ⟨e_yes, h_yes⟩ := p_non.1
  obtain ⟨e_no, h_no⟩ := p_non.2
  let h (x : ℕ) : ℕ := if d x then e_no else e_yes
  have h_rep : RepresentableUnary aps h := diag_rep d e_yes e_no d_rep
  have h_smn_rep : RepresentableUnary aps (fun x => h (aps.smn x x)) := smn_rep h h_rep
  obtain ⟨e, he⟩ := recursion_theorem aps h h_smn_rep
  have h_iff : P (aps.φ e) ↔ P (aps.φ (h e)) := p_ext e (h e) he
  cases h_de : d e
  · have h_d : ¬ (d e = true) := by intro contra; rw [h_de] at contra; contradiction
    have h_pe : ¬ P (aps.φ e) := fun contra => h_d ((hd e).mpr contra)
    have h_he : h e = e_yes := by
      change (if d e then e_no else e_yes) = e_yes
      rw [h_de]
      rfl
    rw [h_he] at h_iff
    have h_pe_yes : ¬ P (aps.φ e_yes) := fun contra => h_pe (h_iff.mpr contra)
    exact h_pe_yes h_yes
  · have h_d : d e = true := h_de
    have h_pe : P (aps.φ e) := (hd e).mp h_d
    have h_he : h e = e_no := by
      change (if d e then e_no else e_yes) = e_no
      rw [h_de]
      rfl
    rw [h_he] at h_iff
    have h_pe_no : P (aps.φ e_no) := h_iff.mp h_pe
    exact h_no h_pe_no

theorem halting_undecidable (aps : AcceptableProgrammingSystem) [HasRepresentableComp aps]
  (diverge_halt_rep : ∀ (d : ℕ → Bool), RepresentableBool aps d →
    ∃ e, ∀ x, (aps.φ e x).Dom ↔ ¬ (d (pair x x) = true)) :
  ¬ ∃ (d : ℕ → Bool), RepresentableBool aps d ∧ ∀ e n, (d (pair e n) = true ↔ (aps.φ e n).Dom) := by
  rintro ⟨d, d_rep, hd⟩
  obtain ⟨e, he⟩ := diverge_halt_rep d d_rep
  have h_dom_imp_false : (aps.φ e e).Dom → False := fun h_dom =>
    have h1 : d (pair e e) = true := (hd e e).mpr h_dom
    have h2 : ¬ (d (pair e e) = true) := (he e).mp h_dom
    h2 h1
  have h_not_dom : ¬ (aps.φ e e).Dom := h_dom_imp_false
  have h_d_false : ¬ (d (pair e e) = true) := fun h_d => h_not_dom ((hd e e).mp h_d)
  have h_dom : (aps.φ e e).Dom := (he e).mpr h_d_false
  exact h_not_dom h_dom
