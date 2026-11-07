/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.Modal
public import WaveTurbulence.Foundations.VineEst.VineEstS4.AbsConvLocal
import Mathlib.Tactic

/-!
# VINE-B♯: the pointwise integrand factorization

For a glued decoration `κ = glue(z, (κ_j))` and glued times `τ = glue(τ', (τ_j))`, the integrand of `skelVal` with the
modal slot family is the `G_sb` integrand times, for every unit, the recentering factor and V5's modulated summand
`lowModC · clLocalSummand` at the exterior clocks `clocks τ' j` (`integrand_glue`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineB
open TTree WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont MeasureTheory

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S}
  {Gsb : Garden w}

/-- The profile of unit `j`: `h(·, j₁, j₁)` with `j₁` the root tree of its upper joint (P* lemma 1). -/
def unitProfile (blk : J → CLBlock S) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (j : J) : ℕ → Mom d → ℝ :=
  fun q => h q (blk j).upper.1.1 (blk j).upper.1.1

/-- The modulated native summand of unit `j`: `e^{πiλτ_b} ·` V5's `clLocalSummand`. -/
noncomputable def gUnit (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ) (h : ℕ → Fin w → Fin w → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (base : Mom d) (j : J) (lam : ℝ)
    (β : Fin 4 → Mom d) (t : Fin 3 → ℝ) (κ : CLLocalDecoration (regionOf (blk j)) L base β)
    (τ : CLInternalTime (regionOf (blk j))) : ℂ :=
  lowModC (regionOf (blk j)) lam t τ *
    clLocalSummand D hS (regionOf (blk j)) L γ δ (unitProfile blk h j) layer hLayer base β t κ τ

namespace SpliceShape
variable (Φ : SpliceShape blk Gsb)

/-- The `G_sb` factor of the factorized integrand. -/
noncomputable def sbInt (hS : S.IsPlain) (hSb : Gsb.IsPlain) (L γ δ : ℝ) (base : Mom d)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ)
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (z : GenDecoration Gsb d roots 0) (τ' : GBranch Gsb.tree → ℝ) : ℂ :=
  phaseProd L γ δ Gsb (cosetDecoration Gsb L base z.1) τ' *
    (∏ s', amp s' (base + latticePoint L (z.1 (slotNode hSb s')))) * routedPhase frq (Φ.route hS hSb) tt τ'

/-- The unit factor of the factorized integrand (recentering factor times modulated summand). -/
noncomputable def unitInt (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (base : Mom d) {roots : Fin w → (Fin d → ℤ)}
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (hSb : Gsb.IsPlain) (z : GenDecoration Gsb d roots 0)
    (τ' : GBranch Gsb.tree → ℝ) (j : J)
    (κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j))
    (τ : CLInternalTime (regionOf (blk j))) : ℂ :=
  recExp L γ δ (S.sign (blk j).upper.toNode) (Φ.clocks τ' j 0) (Φ.bdry L base z.1 j) *
    gUnit D hS L γ δ h layer hLayer base j (modLam frq (Φ.route hS hSb) j : ℝ) (Φ.bdry L base z.1 j)
      (Φ.clocks τ' j) κ τ

/-- **The pointwise factorization.** -/
theorem integrand_glue (hd : Disj blk) (hS : S.IsPlain) (hSb : Gsb.IsPlain) {L : ℝ} (hL : L ≠ 0) (γ δ : ℝ)
    (base : Mom d) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (h : ℕ → Fin w → Fin w → Mom d → ℝ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j))
    (τ' : GBranch Gsb.tree → ℝ) (τs : ∀ j, CLInternalTime (regionOf (blk j))) :
    (epsDec S (Φ.glueDec hS hd hL base z κs).1 : ℂ) *
      (coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt).indicator
        (fun τ => phaseProd L γ δ S (cosetDecoration S L base (Φ.glueDec hS hd hL base z κs).1) τ *
          ∏ s, Φ.modalFn hS hSb D L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) h) layer hLayer amp
            frq s (slotTs hS tt τ s) (base + latticePoint L ((Φ.glueDec hS hd hL base z κs).1 (slotNode hS s))))
        (Φ.glueTime hd τ' τs) =
    (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) *
      (openSb Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt).indicator
        (fun τ' => Φ.sbInt hS hSb L γ δ base tt amp frq z τ' *
          ∏ j, Φ.unitInt D hS L γ δ h layer hLayer base frq hSb z τ' j (κs j) (τs j)) τ' := by
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = Φ.glueDec hS hd hL base z κs := ⟨_, rfl⟩
  obtain ⟨τ, hτdef⟩ : ∃ τ, τ = Φ.glueTime hd τ' τs := ⟨_, rfl⟩
  rw [← hκ, ← hτdef]
  by_cases hτ : τ ∈ coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt
  · subst hτdef
    obtain ⟨hsb, hloc⟩ := (Φ.dom_iff hd _ tt τ' τs).mp hτ
    rw [Set.indicator_of_mem hτ, Set.indicator_of_mem hsb]
    have hκv : κ.1 = Φ.glueFun z.1 (fun j => (κs j).1) := by rw [hκ]; exact Φ.glueDec_val hS hd hL base z κs
    set H := typeProfiles (layeredReconstruction D hS layer hLayer) h
    rw [hκv]
    rw [Φ.prod_modalFn hd hS hSb D L γ δ H layer hLayer amp frq tt (Φ.glueTime hd τ' τs)
      (fun x => base + latticePoint L (Φ.glueFun z.1 (fun j => (κs j).1) x))]
    rw [Φ.amp_glue hS hSb L base z.1 (fun j => (κs j).1) amp, Φ.modes_glue hd hS hSb tt frq τ' τs]
    have hreg := Finset.prod_congr (s₁ := (Finset.univ : Finset J)) rfl
      (fun j _ => Φ.regional_glue hd hS hL γ δ base D layer hLayer h tt z κs τ' τs j)
    rw [hreg]
    rw [Φ.eps_glue hd hL base z κs, Φ.phase_glue hd hL γ δ base z κs τ' τs]
    unfold sbInt unitInt gUnit clLocalSummand unitProfile
    simp only [Set.indicator_of_mem (hloc _), Finset.prod_mul_distrib, Complex.ofReal_mul, Complex.ofReal_prod]
    ring
  · rw [Set.indicator_of_notMem hτ, mul_zero]
    rw [hτdef, (Φ.dom_iff hd _ tt τ' τs).not] at hτ
    by_cases hsb : τ' ∈ openSb Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt
    · have : ∃ j, τs j ∉ clLocalTimeDomain (regionOf (blk j)) (fun b => layer (D.coreBranch hS b).toNode)
          (Φ.clocks τ' j) := by
        by_contra hc
        push Not at hc
        exact hτ ⟨hsb, hc⟩
      obtain ⟨j, hj⟩ := this
      rw [Set.indicator_of_mem hsb]
      have h0 : Φ.unitInt D hS L γ δ h layer hLayer base frq hSb z τ' j (κs j) (τs j) = 0 := by
        unfold unitInt gUnit clLocalSummand
        rw [Set.indicator_of_notMem hj]
        simp
      rw [Finset.prod_eq_zero (Finset.mem_univ j) h0]
      simp
    · rw [Set.indicator_of_notMem hsb]
      simp

end SpliceShape

end WaveTurbulence.VineB
