/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.CountABridge
public import WaveTurbulence.Foundations.FinalCount.GapScalesCopy
import Mathlib.Tactic

/-! # Bridge 3: the admissibility side of `countE ≤ countEFree`

A B2 admissibility `Adm` carries the ladder-gap restriction `R (P S) ‖r‖` of every source maximal ladder `S`.
For decorations with `c_v = 0` at degree-four atoms (the B2 `countE`), the gap norm is the same along a ladder
(`Degen.sourceLadder_contained_gap_norm_eq`), so the restriction passes to every length-one cell with the scale of
its maximal parent: `countE M Adm ≤ countEFree M (Adm ∧ CellGapRestriction (P ∘ parent))`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The ladder-gap restriction carried by a B2 admissibility (maximal ladders, scale `P`, relation `R`). -/
def MaxLadderGapAdm (M : Molecule V D) {d : ℕ} (L : ℝ) (w : Mom d) (P : Finset V → ℝ) (R : ℝ → ℝ → Prop)
    (Adm : (D → (Fin d → ℤ)) → Prop) : Prop :=
  ∀ κ, Adm κ → ∀ (m : ℕ) (u v : Fin (m + 1) → V) (hL : Degen.SourceLadder M u v),
    Molecule.ladderAtoms u v ∈ Degen.sourceMaximalLadders M →
    ∀ r, M.IsLadderGap L w κ u v hL.1 r → R (P (Molecule.ladderAtoms u v)) ‖r‖

theorem cellGap_of_maxLadderGap (M : Molecule V D) (hM : M.IsMolecule) {d : ℕ} {L : ℝ} {w : Mom d}
    {P : Finset V → ℝ} {R : ℝ → ℝ → Prop} {Adm : (D → (Fin d → ℤ)) → Prop}
    (hA : MaxLadderGapAdm M L w P R Adm) {c : V → Mom d} (hc : ∀ a ∈ M.atoms, M.deg a = 4 → c a = 0)
    {κ : D → (Fin d → ℤ)} (hd : M.IsDecoration L w c κ) (hκ : Adm κ) :
    MoleProp.CellGapRestriction M L w (fun S => P (Mole.appbLinkParent M S)) R κ := by
  classical
  intro p q hNew s hs
  have hlink : Mole.AppbLink M (Molecule.ladderAtoms p q) := ⟨p, q, hNew, rfl⟩
  obtain ⟨hmax, hsub⟩ := Mole.appbLinkParent_spec hlink
  have hmax' := hmax
  unfold Degen.sourceMaximalLadders at hmax'
  obtain ⟨m, u, v, hOld, hEq⟩ := (mem_filter.mp hmax').2.1
  have hsub' : Molecule.ladderAtoms p q ⊆ Molecule.ladderAtoms u v := hEq ▸ hsub
  obtain ⟨r, hr⟩ : ∃ r, M.IsLadderGap L w κ u v hOld.1 r := by
    have hm : 0 < m := by have := hOld.1; omega
    obtain ⟨q', hq'⟩ := Degen.sourceLadder_exists_railGapAt M L w κ hOld ⟨0, hm⟩
    exact ⟨q', (Degen.isLadderGap_iff_railGapAt_zero M L w κ u v hOld.1 q').mpr hq'⟩
  have hn := Degen.sourceLadder_contained_gap_norm_eq M hM hd hc hOld hNew hsub' hr hs
  have := hA κ hκ m u v hOld (hEq ▸ hmax) r hr
  show R (P (Mole.appbLinkParent M _)) ‖s‖
  rw [← hn, ← hEq]
  exact this

theorem countE_le_countEFree_cell (M : Molecule V D) (hM : M.IsMolecule) {d : ℕ} (L γ δ : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) (R : ℝ → ℝ → Prop)
    (hA : MaxLadderGapAdm M L w P R Adm) :
    M.countE L γ δ w Adm ≤
      MoleProp.countEFree M L γ δ w (fun κ => Adm κ ∧
        MoleProp.CellGapRestriction M L w (fun S => P (Mole.appbLinkParent M S)) R κ) := by
  conv_lhs => unfold Molecule.countE
  refine iSup_le fun c => iSup_le fun hc => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  refine le_trans (Set.encard_mono ?_) (MoleProp.encard_le_countEFree M L γ δ w _ c β k0 hk0)
  intro κ hκ
  exact ⟨hκ.1, hκ.2.1, hκ.2.2, cellGap_of_maxLadderGap M hM hA hc hκ.1 hκ.2.2⟩

/-- `countA` with a B2 admissibility is bounded by the relaxed count with the cell restriction. -/
theorem countA_le_countAFree_cell (M : Molecule V D) (hM : M.IsMolecule) {d : ℕ} (L γ δ C₁ : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) (R : ℝ → ℝ → Prop)
    (hA : MaxLadderGapAdm M L w P R Adm) :
    M.countA L γ δ C₁ w Adm P ≤
      MoleProp.countAFree M L γ δ C₁ w (fun κ => Adm κ ∧
        MoleProp.CellGapRestriction M L w (fun S => P (Mole.appbLinkParent M S)) R κ)
        (fun S => P (Mole.appbLinkParent M S)) := by
  unfold Molecule.countA MoleProp.countAFree
  refine mul_le_mul' ?_ ?_
  · exact_mod_cast countE_le_countEFree_cell M hM L γ δ w Adm P R hA
  · refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    congr 1
    have h := Mole.appbLinkProduct_eq_sourceLadderProduct M hM L γ δ P
    rw [maximalLadders_eq_source]
    exact h.symm

end WaveTurbulence.FinalCountG8
