/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.Main5
public import WaveTurbulence.Foundations.Vine.B.Fold8
public import WaveTurbulence.Foundations.Vine.B.Src5
import Mathlib.Tactic

/-!
# VINE-B♯: the export for `G_sb = (stSt S σ).G` (S2's `hval`, `src`, `src_dart`, `src_root`)
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineB
open TTree WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory

variable {w d : ℕ} {S : Garden w}

/-- The hinge membership transported to `(stSt S σ).hinges` (= `(collectionChoices S σ).hinges`). -/
theorem stSt_hinges_mem (hM : S.molecule.IsMolecule) (σ : Prescription S) (c : GBranch (stSt S σ).G.tree) :
    c ∈ (stSt S σ).hinges ↔ c ∈ (stShape hM σ).hinges (unitBlk_disj hM σ) := by
  rw [stShape_hinges]

/-- B1a: `stSt_hinges_mem` for every marked vine set. -/
theorem stSt_hinges_memMk (hM : S.molecule.IsMolecule) (σ : Prescription S) (Mk : Set (Stage1.CLVine S))
    (c : GBranch (stSt S σ Mk).G.tree) :
    c ∈ (stSt S σ Mk).hinges ↔ c ∈ (stShape hM σ Mk).hinges (unitBlkMk_disj hM σ Mk) := by
  rw [stShape_hingesMk]

/-- **G3.** The hinge dart (or root) giving the momentum of `hmom j i`, for the units of `σ`.  B1a: for the marked
vine set `Mk`, inferred from `hSb`. -/
noncomputable def stSrc (hM : S.molecule.IsMolecule) (σ : Prescription S) {Mk : Set (Stage1.CLVine S)}
    (hSb : (stSt S σ Mk).G.IsPlain) (j : Fin (unitBlocks S σ Mk).length) (i : Fin 4) :
    HingeDarts (stSt S σ Mk).G (stSt S σ Mk).hinges ⊕ Fin w :=
  (stShape hM σ Mk).src (unitBlkMk_disj hM σ Mk) hSb (stSt S σ Mk).hinges (stSt_hinges_memMk hM σ Mk) j i

theorem stSrc_dart (hM : S.molecule.IsMolecule) (σ : Prescription S) (hSb : (stSt S σ).G.IsPlain)
    (j : Fin (unitBlocks S σ).length) (i : Fin 4) (x : HingeDarts (stSt S σ).G (stSt S σ).hinges)
    (hx : stSrc hM σ hSb j i = Sum.inl x) (roots : Fin w → (Fin d → ℤ))
    (z : GenDecoration (stSt S σ).G d roots 0) :
    bondIndex (stSt S σ).G z.1 x.1 = z.1 ((stShape hM σ).hmom (unitBlk_disj hM σ) j i) :=
  (stShape hM σ).src_dart (unitBlk_disj hM σ) hSb _ (stSt_hinges_mem hM σ) j i x hx d roots z

theorem stSrc_root (hM : S.molecule.IsMolecule) (σ : Prescription S) (hSb : (stSt S σ).G.IsPlain)
    (j : Fin (unitBlocks S σ).length) (i : Fin 4) (r : Fin w)
    (hr : stSrc hM σ hSb j i = Sum.inr r) (roots : Fin w → (Fin d → ℤ))
    (z : GenDecoration (stSt S σ).G d roots 0) :
    z.1 ((stShape hM σ).hmom (unitBlk_disj hM σ) j i) = roots r :=
  (stShape hM σ).src_root (unitBlk_disj hM σ) hSb _ (stSt_hinges_mem hM σ) j i r hr d roots z

open scoped Classical in
/-- **The per-mode single-state factorization for `G_sb = (stSt S σ).G`** (the `hval` shape of S2's
`representsIntA_of_vineModes`): `Φ = stShape hM σ`, `hinges = (stSt S σ).hinges`, layer of `stage1PieceOf`. -/
theorem stSt_skelVal_modal_eq_outerValM (hM : S.molecule.IsMolecule) (σ : Prescription S)
    (hS : S.IsPlain) (hSb : (stSt S σ).G.IsPlain) {L : ℝ} (hL : L ≠ 0)
    (γ δ : ℝ) (base : Mom d) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (h : ℕ → Fin w → Fin w → Mom d → ℝ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot (stSt S σ).G → Mom d → ℂ) (frq : ReplacementSlot (stSt S σ).G → Fin 2 → ℤ)
    (selSk : GenDecoration S d roots 0 → Prop) (Zw : GenDecoration (stSt S σ).G d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S d roots 0, (if selSk κ then (1 : ℝ) else 0) =
      Zw ((stShape hM σ).resDec hS (unitBlk_disj hM σ) κ))
    (hF : ∀ j, HF D hS L (unitProfile (unitBlk hM σ) h j) layer base)
    (hsum : Summable fun z : GenDecoration (stSt S σ).G d roots 0 => ampBound hSb L base amp z) :
    skelVal D hS L γ δ base roots tt layer selSk
      ((stShape hM σ).modalFn hS hSb D L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) h) layer hLayer amp frq) =
    outerValM (stSt S σ).G L γ δ base roots tt
      ((stSt S σ).layer (RegRed.coreLayer (layeredReconstruction D hS layer hLayer) D hS (D.garden_decodes hS)))
      (stSt S σ).hinges Zw hSb amp frq ((stShape hM σ).route hS hSb)
      ((stShape hM σ).hclk (unitBlk_disj hM σ)) ((stShape hM σ).hmom (unitBlk_disj hM σ))
      (unitKernelM (unitBlk hM σ) D hS L γ δ h layer hLayer base) := by
  have := (stShape hM σ).skelVal_modal_eq_outerValM (unitBlk_disj hM σ) hS hSb hL γ δ base D layer hLayer h tt amp frq
    selSk Zw hZ hF hsum
  rw [stShape_hinges] at this
  exact this

end WaveTurbulence.VineB
