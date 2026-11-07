/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmClass
public import WaveTurbulence.Foundations.FinalCount.AsmCountAlg
/-! **FINALCOUNT-ASSEMBLY (garden wrapper, class split).**  Every decoration `κ` lies in the class `(Z, g)` of its tame set `Z` and the
values `g` (a point of `kFix` or `none`) of the common momentum at the tame atoms of degree `< 4` (`exists_classLabel`).  The label set has at
most `2^n (2R+1)^{2R}` elements (`labelSet_card_le`); `countA_classes_le` bounds the count by the sum over the labels. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCountG3

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}

theorem latticePoint_injective' {L : ℝ} (hL : L ≠ 0) : Function.Injective (latticePoint (d := d) L) := by
  intro a b h
  funext j
  have := congrArg (fun v : Mom d => v j) h
  simp only [latticePoint] at this
  have h' : (a j : ℝ) / L = (b j : ℝ) / L := this
  rw [div_left_inj' hL] at h'
  exact_mod_cast h'

theorem kvec_injective {L : ℝ} (hL : L ≠ 0) (w : Mom d) (κ : D → (Fin d → ℤ)) {x y : D}
    (h : Molecule.kvec L w κ x = Molecule.kvec L w κ y) : κ x = κ y := by
  unfold Molecule.kvec at h
  exact latticePoint_injective' hL (add_left_cancel h)

/-- The atoms of degree `< 4`. -/
def lowAtoms (M : Molecule V D) : Finset V := M.atoms.filter fun a => M.deg a < 4

/-- The class of the labels `(Z, g)`: tame set `Z`, and the common vector `g v` at the tame low-degree atoms. -/
def InClass (M : Molecule V D) (L : ℝ) (w : Mom d) (kFix : Finset (Mom d)) (Z : Finset V)
    (g : lowAtoms M → Option (Mom d)) (κ : D → (Fin d → ℤ)) : Prop :=
  (∀ v ∈ M.atoms, M.IsTame L w kFix κ v ↔ v ∈ Z) ∧
    ∀ v : lowAtoms M, v.1 ∈ Z → ∀ x, M.atom x = v.1 → g v = some (Molecule.kvec L w κ x)

/-- The label set. -/
noncomputable def labelSet (M : Molecule V D) (kFix : Finset (Mom d)) : Finset (Finset V × (lowAtoms M → Option (Mom d))) :=
  M.atoms.powerset ×ˢ Fintype.piFinset (fun _ : lowAtoms M => insert none (kFix.image some))

theorem labelSet_card_le {R : ℕ} {M : Molecule V D} (hS : SubHyp R M) (kFix : Finset (Mom d)) (hk : kFix.card ≤ 2 * R) :
    (labelSet M kFix).card ≤ 2 ^ M.atoms.card * (2 * R + 1) ^ (2 * R) := by
  unfold labelSet
  rw [Finset.card_product, Finset.card_powerset, Fintype.card_piFinset]
  refine Nat.mul_le_mul_left _ ?_
  have h1 : (insert none (kFix.image some) : Finset (Option (Mom d))).card ≤ 2 * R + 1 :=
    (Finset.card_insert_le _ _).trans (by have := Finset.card_image_le (s := kFix) (f := (some : Mom d → Option (Mom d))); omega)
  calc ∏ _i : lowAtoms M, (insert none (kFix.image some) : Finset (Option (Mom d))).card
      ≤ ∏ _i : lowAtoms M, (2 * R + 1) := Finset.prod_le_prod' fun _ _ => h1
    _ = (2 * R + 1) ^ Fintype.card (lowAtoms M) := by simp
    _ ≤ (2 * R + 1) ^ (2 * R) := by
        apply Nat.pow_le_pow_right (by omega)
        rw [Fintype.card_coe]
        exact card_lowdeg_le hS

/-- Every decoration lies in a class of the label set. -/
theorem exists_classLabel {R : ℕ} {M : Molecule V D} (hS : SubHyp R M) (L : ℝ) (w : Mom d) (kFix : Finset (Mom d))
    (κ : D → (Fin d → ℤ)) (hmate : ∀ x, κ (M.mate x) = κ x) (hL : L ≠ 0) :
    ∃ lab ∈ labelSet M kFix, InClass M L w kFix lab.1 lab.2 κ := by
  let Z : Finset V := M.atoms.filter fun v => M.IsTame L w kFix κ v
  have hdart : ∀ v ∈ M.atoms, ∃ x, M.atom x = v := by
    intro v hv
    have h3 := hS.deg3 v hv
    have : 0 < (M.dartsAt v).card := by unfold Molecule.deg at h3; omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp this
    exact ⟨x, (Mole.mem_dartsAt M v x).mp hx⟩
  refine ⟨(Z, fun v => if v.1 ∈ Z then some (Molecule.kvec L w κ (Classical.choose (hdart v.1 (Finset.mem_filter.1 v.2).1))) else none),
    ?_, ?_, ?_⟩
  · unfold labelSet
    refine Finset.mem_product.2 ⟨Finset.mem_powerset.2 (Finset.filter_subset _ _), ?_⟩
    rw [Fintype.mem_piFinset]
    intro v
    by_cases hv : v.1 ∈ Z
    · have hlow := (Finset.mem_filter.1 v.2).2
      have hT := (Finset.mem_filter.1 hv).2
      have hx := Classical.choose_spec (hdart v.1 (Finset.mem_filter.1 v.2).1)
      simp only [hv, if_true]
      exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨_, hT.2 hlow _ hx, rfl⟩)
    · simp [hv]
  · intro v hv
    simp [Z, hv]
  · intro v hv x hx
    simp only [hv, if_true]
    have hT := (Finset.mem_filter.1 hv).2
    have hx' := Classical.choose_spec (hdart v.1 (Finset.mem_filter.1 v.2).1)
    rw [hT.1 _ _ hx' hx]

theorem countA_classes_le {R : ℕ} {M : Molecule V D} (hS : SubHyp R M) (L γ δ C₁ : ℝ) (w : Mom d) (kFix : Finset (Mom d))
    (hL : L ≠ 0) {Adm : (D → (Fin d → ℤ)) → Prop} (hAdm : ∀ κ, Adm κ → ∀ x, κ (M.mate x) = κ x) (P : Finset V → ℝ) :
    M.countA L γ δ C₁ w Adm P ≤
      ∑ lab ∈ labelSet M kFix, M.countA L γ δ C₁ w (fun κ => Adm κ ∧ InClass M L w kFix lab.1 lab.2 κ) P := by
  refine countA_union_le M L γ δ C₁ w (labelSet M kFix) (fun lab κ => Adm κ ∧ InClass M L w kFix lab.1 lab.2 κ) ?_ P
  intro κ hκ
  obtain ⟨lab, hl, hc⟩ := exists_classLabel hS L w kFix κ (hAdm κ hκ) hL
  exact ⟨lab, hl, hκ, hc⟩

end WaveTurbulence.FinalCountAsm
