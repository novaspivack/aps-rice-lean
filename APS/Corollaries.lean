import APS.Core
import APS.Rice

/-! The complement of any nontrivial extensional property is also undecidable. -/

theorem extensional_not (aps : AcceptableProgrammingSystem) (P : (ℕ →. ℕ) → Prop)
  (hP : Extensional aps P) : Extensional aps (fun f => ¬ P f) := by
  intro e₁ e₂ h
  have h_iff := hP e₁ e₂ h
  exact Iff.intro (fun hn hp2 => hn (h_iff.mpr hp2)) (fun hn hp1 => hn (h_iff.mp hp1))

theorem nontrivial_not (aps : AcceptableProgrammingSystem) (P : (ℕ →. ℕ) → Prop)
  (hP : NontrivialProp aps P) : NontrivialProp aps (fun f => ¬ P f) := by
  obtain ⟨e_yes, h_yes⟩ := hP.1
  obtain ⟨e_no, h_no⟩ := hP.2
  exact ⟨⟨e_no, h_no⟩, ⟨e_yes, fun contra => contra h_yes⟩⟩

/-- The complement of any nontrivial extensional property is also undecidable. -/
theorem rice_theorem_not (aps : AcceptableProgrammingSystem) [HasRepresentableComp aps]
  (P : (ℕ →. ℕ) → Prop) (p_ext : Extensional aps P) (p_non : NontrivialProp aps P)
  (diag_rep : ∀ (d : ℕ → Bool) (e_yes e_no : ℕ), RepresentableBool aps d →
    RepresentableUnary aps (fun x => (if d x then e_no else e_yes)))
  (smn_rep : ∀ (h : ℕ → ℕ), RepresentableUnary aps h → RepresentableUnary aps (fun x => h (aps.smn x x))) :
  ¬ ∃ (d : ℕ → Bool), RepresentableBool aps d ∧ ∀ e, (d e = true ↔ ¬ P (aps.φ e)) := by
  have h1 := extensional_not aps P p_ext
  have h2 := nontrivial_not aps P p_non
  exact rice_theorem aps (fun f => ¬ P f) h1 h2 diag_rep smn_rep
