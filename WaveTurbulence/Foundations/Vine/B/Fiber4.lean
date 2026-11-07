/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.Fiber3
import Mathlib.Tactic

/-!
# VINE-B♯: Fubini on `(τ', (τ_j))` and the product over the units

`inner_psiInt`: the integral of `psiInt` over the interior times is `fibInt` (the units factor, by
`integral_fintype_prod_volume_eq_prod`).  `integral_psiInt`: Fubini (`integral_prod`).
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

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}

namespace SpliceShape
variable (Φ : SpliceShape blk Gsb)

/-- The recentering factor of unit `j` at the `G_sb` times `τ'` and the decoration `z`. -/
noncomputable def recJ (L γ δ : ℝ) (base : Mom d) {roots : Fin w → (Fin d → ℤ)} (z : GenDecoration Gsb d roots 0)
    (τ' : GBranch Gsb.tree → ℝ) (j : J) : ℂ :=
  recExp L γ δ (S.sign (blk j).upper.toNode) (Φ.clocks τ' j 0) (Φ.bdry L base z.1 j)

/-- The interior time integral of the modulated summand of unit `j` (a term of V5's modulated kernel). -/
noncomputable def unitI (D : ReconstructionData S) (hS : S.IsPlain) (hSb : Gsb.IsPlain) (L γ δ : ℝ)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (base : Mom d) {roots : Fin w → (Fin d → ℤ)}
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (z : GenDecoration Gsb d roots 0) (τ' : GBranch Gsb.tree → ℝ) (j : J)
    (κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) : ℂ :=
  ∫ τ : CLInternalTime (regionOf (blk j)),
    gUnit D hS L γ δ h layer hLayer base j (modLam frq (Φ.route hS hSb) j : ℝ) (Φ.bdry L base z.1 j)
      (Φ.clocks τ' j) κ τ

/-- The fiber integrand over `G_sb` times. -/
noncomputable def fibInt (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (L γ δ : ℝ) (base : Mom d) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j))
    (τ' : GBranch Gsb.tree → ℝ) : ℂ :=
  (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) *
    (openSb Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt).indicator
      (fun τ' => Φ.sbInt hS hSb L γ δ base tt amp frq z τ' *
        ∏ j, (Φ.recJ L γ δ base z τ' j * Φ.unitI D hS hSb L γ δ h layer hLayer base frq z τ' j (κs j))) τ'

theorem inner_psiInt (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (L γ δ : ℝ) (base : Mom d) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j))
    (τ' : GBranch Gsb.tree → ℝ) :
    ∫ τs : (∀ j, CLInternalTime (regionOf (blk j))),
      Φ.psiInt hd D hS hSb L γ δ base h layer hLayer tt amp frq z κs (τ', τs) =
    Φ.fibInt hd D hS hSb L γ δ base h layer hLayer tt amp frq z κs τ' := by
  unfold psiInt fibInt
  by_cases hp : τ' ∈ openSb Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt
  · simp only [Set.indicator_of_mem hp]
    rw [integral_const_mul, integral_const_mul]
    congr 2
    have := integral_fintype_prod_volume_eq_prod (𝕜 := ℂ) (ι := J)
      (E := fun j => CLInternalTime (regionOf (blk j)))
      (fun j (τ : CLInternalTime (regionOf (blk j))) =>
        Φ.unitInt D hS L γ δ h layer hLayer base frq hSb z τ' j (κs j) τ)
    rw [this]
    refine Finset.prod_congr rfl fun j _ => ?_
    unfold unitInt recJ unitI
    rw [integral_const_mul]
  · simp only [Set.indicator_of_notMem hp]
    simp

theorem integral_psiInt (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (L γ δ : ℝ) (base : Mom d) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (hF : ∀ j, HF D hS L (unitProfile blk h j) layer base)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    ∫ p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))),
      Φ.psiInt hd D hS hSb L γ δ base h layer hLayer tt amp frq z κs p =
    ∫ τ' : GBranch Gsb.tree → ℝ, Φ.fibInt hd D hS hSb L γ δ base h layer hLayer tt amp frq z κs τ' := by
  rw [Measure.volume_eq_prod, integral_prod _ (Φ.integrable_psiInt hd D hS hSb L γ δ base h layer hLayer tt amp frq hF z κs)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun τ' =>
    Φ.inner_psiInt hd D hS hSb L γ δ base h layer hLayer tt amp frq z κs τ')

end SpliceShape

end WaveTurbulence.VineB
