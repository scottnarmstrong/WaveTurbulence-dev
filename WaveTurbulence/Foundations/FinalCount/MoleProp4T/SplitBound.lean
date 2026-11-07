/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.YLem2SecondAdm
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.YLem2NotRemoved
import Mathlib.Tactic

/-! # The decoration split of Prop 10.4(2)′

DH23 Prop 10.4(2) (L1840): "either `𝔄(𝕄) ≲ L^{−η/4}`, or `𝔄(𝕄 ∖ ℓ) ≲ L^{−γ₀−η/4}` (note that the exact case may depend on
assumptions we impose on the decoration)". It is consumed at L1883 (Prop 9.6, case (4)) by splitting the decorations of
`𝕄₁`: one class is counted on `𝕄₁` (operation (d) route), the other on `𝕄₁ ∖ ℓ` (operation (c) route, as in Theorem A).

**The form chosen** (`SplitBound`): a condition `Q` on the decorations of `𝕄`, independent of the scales, with
* `𝔄(𝕄; lgAdm ∧ ¬Q) ≤ ε₁` for every scale function `P ≥ 0` on the cells of `𝕄`, and
* `𝔄(𝕄 ∖ ℓ; lgAdm ∧ [restriction of an LG decoration of 𝕄 with Q]) ≤ ε₂` for every `P ≥ 0` on the cells of `𝕄 ∖ ℓ`.
The second count keeps `𝕄 ∖ ℓ`'s own cell restriction; the extension to `𝕄` is only required to be LG with `Q`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **The decoration split of Prop 10.4(2)′.** -/
def SplitBound (M : Molecule V D) (e : D) (d : ℕ) (L γ δ η C1 ε₁ ε₂ : ℝ) : Prop :=
  ∃ Q : (D → (Fin d → ℤ)) → Prop,
    (∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells M, 0 ≤ P S) →
      MoleProp.countAFree M L γ δ C1 (0 : Mom d) (fun κ => lgAdm M L γ η P κ ∧ ¬ Q κ) P ≤ ENNReal.ofReal ε₁) ∧
    (∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells (MoleProp.eraseBond M e), 0 ≤ P S) →
      MoleProp.countAFree (MoleProp.eraseBond M e) L γ δ C1 (0 : Mom d)
        (fun κ => lgAdm (MoleProp.eraseBond M e) L γ η P κ ∧
          MoleProp.erasedBondAdmissibility M e (fun κ0 => MoleProp.LargeGap M L γ η 0 κ0 ∧ Q κ0) κ) P ≤
        ENNReal.ofReal ε₂)

/-- Counts are monotone in the admissibility. -/
theorem countAFree_mono_adm (M : Molecule V D) {d : ℕ} {L γ δ C1 : ℝ} {P : Finset V → ℝ}
    {A B : (D → (Fin d → ℤ)) → Prop} (h : ∀ κ, A κ → B κ) :
    MoleProp.countAFree M L γ δ C1 (0 : Mom d) A P ≤ MoleProp.countAFree M L γ δ C1 (0 : Mom d) B P := by
  unfold MoleProp.countAFree
  exact mul_le_mul_of_nonneg_right (ENat.toENNReal_mono (MoleProp.countEFree_mono _ L γ δ 0 h)) bot_le

/-- An empty admissibility counts nothing. -/
theorem countAFree_of_false (M : Molecule V D) {d : ℕ} {L γ δ C1 : ℝ} {P : Finset V → ℝ}
    {A : (D → (Fin d → ℤ)) → Prop} (h : ∀ κ, ¬ A κ) : MoleProp.countAFree M L γ δ C1 (0 : Mom d) A P = 0 := by
  have h0 : MoleProp.countEFree M L γ δ (0 : Mom d) A = 0 := by
    refine le_antisymm ?_ bot_le
    unfold MoleProp.countEFree
    refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun _ => ?_
    have hemp : {κ | M.IsDecoration L 0 c κ ∧ M.IsRestricted L γ δ 0 β k0 κ ∧ A κ} = (∅ : Set (D → (Fin d → ℤ))) :=
      Set.eq_empty_of_forall_notMem fun κ hκ => h κ hκ.2.2
    rw [hemp, Set.encard_empty]
  rw [MoleProp.countAFree_eq_normalization, h0]
  simp

/-- **The first alternative for every decoration** (`Q = ⊥`). -/
theorem splitBound_of_first (M : Molecule V D) (e : D) {d : ℕ} {L γ δ η C1 ε₁ ε₂ : ℝ}
    (h : ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells M, 0 ≤ P S) →
      MoleProp.countAFree M L γ δ C1 (0 : Mom d) (lgAdm M L γ η P) P ≤ ENNReal.ofReal ε₁) :
    SplitBound M e d L γ δ η C1 ε₁ ε₂ := by
  refine ⟨fun _ => False, fun P hP => (countAFree_mono_adm M fun κ h => h.1).trans (h P hP), fun P _ => ?_⟩
  rw [countAFree_of_false]
  · exact bot_le
  · rintro κ ⟨_, κ0, ⟨_, hf⟩, _⟩; exact hf

/-- **The second alternative for every decoration** (`Q = ⊤`). -/
theorem splitBound_of_second (M : Molecule V D) (e : D) {d : ℕ} {L γ δ η C1 ε₁ ε₂ : ℝ}
    (h : ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells (MoleProp.eraseBond M e), 0 ≤ P S) →
      MoleProp.countAFree (MoleProp.eraseBond M e) L γ δ C1 (0 : Mom d) (lgAdm (MoleProp.eraseBond M e) L γ η P) P ≤
        ENNReal.ofReal ε₂) :
    SplitBound M e d L γ δ η C1 ε₁ ε₂ := by
  refine ⟨fun _ => True, fun P _ => ?_, fun P hP => (countAFree_mono_adm _ fun κ h => h.1).trans (h P hP)⟩
  rw [countAFree_of_false]
  · exact bot_le
  · rintro κ ⟨_, hf⟩; exact hf trivial

end WaveTurbulence.MoleProp4
