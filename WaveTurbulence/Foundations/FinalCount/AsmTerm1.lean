/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmClSharp
public import WaveTurbulence.Foundations.FinalCount.AsmComp
public import WaveTurbulence.Foundations.FinalCount.G3Ghost
public import WaveTurbulence.Foundations.FinalCount.G3Op5c
/-! **FINALCOUNT-ASSEMBLY, `hterm` part 1: the generic count chain.**
`𝔄(M) ≤ I · ∏_{a ∈ R} 𝔄(component a of M₅)` where `M₅ = restrictP (eraseSet M E) (keepS)` is the Operation-5 molecule, `I` the cluster
deviation of the family and `R` representatives of the components of `M₅`.  Also `exists_compRep`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- Every molecule has a set of component representatives. -/
theorem exists_compRep [Nonempty V] (N : Molecule V D) : ∃ R : Finset V, CompRep N R := by
  let P : V → V → Prop := fun v a => a ∈ N.atoms ∧ N.SameComponent a v
  let rep : V → V := fun v => Classical.epsilon (P v)
  have hex : ∀ v ∈ N.atoms, ∃ a, P v a := fun v hv => ⟨v, hv, Relation.EqvGen.refl _⟩
  have hspec : ∀ v ∈ N.atoms, P v (rep v) := fun v hv => Classical.epsilon_spec (hex v hv)
  refine ⟨N.atoms.image rep, ⟨?_, ?_, ?_⟩⟩
  · intro a ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 ha
    exact (hspec v hv).1
  · intro v hv
    exact ⟨rep v, Finset.mem_image.2 ⟨v, hv, rfl⟩, (hspec v hv).2⟩
  · intro a ha b hb hab
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hb
    have h1 := (hspec u hu).2
    have h2 := (hspec v hv).2
    have huv : N.SameComponent u v :=
      Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h1) (Relation.EqvGen.trans _ _ _ hab h2)
    have : P u = P v := by
      funext a
      apply propext
      constructor
      · rintro ⟨h, hs⟩; exact ⟨h, Relation.EqvGen.trans _ _ _ hs huv⟩
      · rintro ⟨h, hs⟩; exact ⟨h, Relation.EqvGen.trans _ _ _ hs (Relation.EqvGen.symm _ _ huv)⟩
    show Classical.epsilon (P u) = Classical.epsilon (P v)
    rw [this]

/-- The atoms kept by Operation 5 (those that still have a bond; `keepS` of G3). -/
def keepM (M : Molecule V D) (E : Finset V) : V → Prop := fun a => 1 ≤ (eraseSet M E).deg a

theorem keepM_closed (M : Molecule V D) (E : Finset V) : PClosed (eraseSet M E) (keepM M E) := by
  intro x hx
  show 1 ≤ (eraseSet M E).deg _
  exact Finset.card_pos.2 ⟨(eraseSet M E).mate x, by simp [Molecule.dartsAt]⟩

/-- The inherited admissible class of the Operation-5 molecule. -/
def adm5 (Adm : (D → (Fin d → ℤ)) → Prop) (M : Molecule V D) (E : Finset V) :
    (PDart (eraseSet M E) (keepM M E) → (Fin d → ℤ)) → Prop :=
  fun κ' => ∃ κ'' : EDartS M E → (Fin d → ℤ), resAdm Adm M E κ'' ∧ κ' = fun x => κ'' x.1


/-- **The count chain.** -/
theorem terminal_chain [Nonempty V] (M : Molecule V D) (E : Finset V) (L γ δ C₁ : ℝ) (w : Mom d) (hL : 0 < L) (hδ : 0 < δ)
    (hC : 0 < C₁) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ)
    (hX : ∀ S, 0 ≤ Molecule.ladderWeight L γ δ (P S)) {I : ℝ≥0∞}
    (hdev : IsDeviation (M.countA L γ δ C₁ w Adm P) ((eraseSet M E).countA L γ δ C₁ w (resAdm Adm M E) P) I) :
    ∃ R : Finset V, CompRep (restrictP (eraseSet M E) (keepM M E) (keepM_closed M E)) R ∧
      M.countA L γ δ C₁ w Adm P ≤ I * ∏ a ∈ R,
        (compMol (restrictP (eraseSet M E) (keepM M E) (keepM_closed M E)) a).countA L γ δ C₁ w
          (projAdm (restrictP (eraseSet M E) (keepM M E) (keepM_closed M E))
            (compP (restrictP (eraseSet M E) (keepM M E) (keepM_closed M E)) a) (adm5 Adm M E)) P := by
  obtain ⟨R, hR⟩ := exists_compRep (restrictP (eraseSet M E) (keepM M E) (keepM_closed M E))
  refine ⟨R, hR, ?_⟩
  have hno : ∀ x : EDartS M E, keepM M E ((eraseSet M E).atom x) := fun x =>
    Finset.card_pos.2 ⟨x, by simp [Molecule.dartsAt]⟩
  have h1 := countA_restrict_dartless (eraseSet M E) (keepM M E) (keepM_closed M E) hno L γ δ C₁ w hL hδ hC (resAdm Adm M E)
    (adm5 Adm M E) (fun κ hκ => ⟨κ, hκ, rfl⟩) P hX
  have h2 := hR.countA_le_prod L γ δ C₁ w hL hδ hC (adm5 Adm M E) P hX
  unfold IsDeviation at hdev h1
  calc M.countA L γ δ C₁ w Adm P ≤ I * (eraseSet M E).countA L γ δ C₁ w (resAdm Adm M E) P := hdev
    _ ≤ I * (1 * (restrictP (eraseSet M E) (keepM M E) (keepM_closed M E)).countA L γ δ C₁ w (adm5 Adm M E) P) := by gcongr
    _ ≤ _ := by rw [one_mul]; gcongr

end WaveTurbulence.FinalCountAsm
