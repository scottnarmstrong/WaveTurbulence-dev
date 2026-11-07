/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.SlotMap
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.Cont.ModKernel
import Mathlib.Tactic

/-!
# VINE-B: the pointwise factorization, part A (glued data, `ε`, phases, regional slots)

For a glued skeleton decoration `κ = glue(z, (κ_j))` and glued times `τ = glue(τ', (τ_j))`:
* the local decorations are restrictions of `κ` (`locDec_eq`), the exterior clocks of unit `j` are V5's
  `clExternalTimes` of `τ` and the interior times are `clRestrictTime` (`clocks_eq_external`, `restrict_glueTime`);
* hence V5's restriction lemmas apply: `eps_glue`, `phase_glue` (with the recentering factor of (vineest1) cancelling
  the hinge phase of `G_sb`, TARGET L1957), `regional_glue` (the regional slots of unit `j` are V5's
  `clLocalStarProduct` with `F = h(·, j₁, j₁)`, P* lemma 1).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineB
open TTree WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S}
  {Gsb : Garden w}

/-- The recentering factor `e^{-πiδL^{2γ} t Γ}` of (vineest1). -/
noncomputable def recExp (L γ δ : ℝ) (ζ : ℤˣ) (t : ℝ) (m : Fin 4 → Mom d) : ℂ :=
  Complex.exp (((-(Real.pi * δ * L ^ (2 * γ)) * t * boundaryEnergyFromMomenta ζ (m 0) (m 1) (m 2) (m 3) : ℝ) : ℂ) *
    Complex.I)

namespace SpliceShape
variable (Φ : SpliceShape blk Gsb)

theorem locDec_eq (hd : Disj blk) {L : ℝ} (hL : L ≠ 0) (base : Mom d) {roots : Fin w → (Fin d → ℤ)}
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) (j : J) :
    (κs j).1 = fun x => Φ.glueFun z.1 (fun j => (κs j).1) x.1 := by
  funext x
  rw [Φ.glue_support hd hL base z.1 (fun j => (κs j).1) j (κs j).2.2.2 x.2]
  exact (clExtendIndices_apply _ _ _ x.2).symm

theorem glue_node (z : GNode Gsb.tree → (Fin d → ℤ))
    (κs : ∀ j, ↥(clLocalSupport (regionOf (blk j))) → (Fin d → ℤ)) (y : GNode Gsb.tree) :
    Φ.glueFun z κs (Φ.node y) = z y := by
  rw [Φ.glue_ret z κs (Φ.ret_node y), Φ.ext_node]

theorem clocks_eq_external (hd : Disj blk) (τ' : GBranch Gsb.tree → ℝ)
    (τs : ∀ j, CLInternalTime (regionOf (blk j))) (j : J) :
    Φ.clocks τ' j = clExternalTimes (regionOf (blk j)) (Φ.glueTime hd τ' τs) := by
  have hcb : ∀ x : GNode S.tree, Ret blk x →
      clBranchClock (Φ.extTime τ') x = clBranchClock (Φ.glueTime hd τ' τs) x := by
    intro x hx
    unfold clBranchClock
    split_ifs with hb
    · exact (Φ.glueTime_ret hd τ' τs (v := ⟨x.1, hb⟩) hx).symm
    · rfl
  unfold clocks clExternalTimes
  congr 1
  · exact (Φ.glueTime_ret hd τ' τs (ret_upper hd j)).symm
  · congr 1
    · exact hcb _ (ret_crown hd j (Or.inr (Or.inl rfl)))
    · congr 1
      exact hcb _ (ret_crown hd j (Or.inr (Or.inr rfl)))

theorem restrict_glueTime (hd : Disj blk) (τ' : GBranch Gsb.tree → ℝ)
    (τs : ∀ j, CLInternalTime (regionOf (blk j))) (j : J) :
    clRestrictTime (regionOf (blk j)) (Φ.glueTime hd τ' τs) = τs j := by
  funext x
  exact Φ.glueTime_inter hd τ' τs j x

/-- `ε` of a glued decoration. -/
theorem eps_glue (hd : Disj blk) {L : ℝ} (hL : L ≠ 0) (base : Mom d) {roots : Fin w → (Fin d → ℤ)}
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    epsDec S (Φ.glueFun z.1 (fun j => (κs j).1)) =
      splicedEpsilon Gsb (Φ.hinges hd) z.1 *
        ∏ j, clRegionalEpsilon S (blk j).atoms (clExtendIndices (regionOf (blk j)) (κs j).1) := by
  rw [Φ.eps_split hd]
  congr 1
  · congr 1; funext y; exact Φ.glue_node _ _ y
  · refine Finset.prod_congr rfl fun j _ => ?_
    rw [Φ.locDec_eq hd hL base z κs j, clRegionalEpsilon_restrict (blk j).isBlock]

/-- The phases of a glued decoration at glued times: the `G_sb` phases times, per unit, the recentering factor and
the regional phases at the local clocks. -/
theorem phase_glue (hd : Disj blk) {L : ℝ} (hL : L ≠ 0) (γ δ : ℝ) (base : Mom d) {roots : Fin w → (Fin d → ℤ)}
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j))
    (τ' : GBranch Gsb.tree → ℝ) (τs : ∀ j, CLInternalTime (regionOf (blk j))) :
    phaseProd L γ δ S (cosetDecoration S L base (Φ.glueFun z.1 (fun j => (κs j).1))) (Φ.glueTime hd τ' τs) =
      phaseProd L γ δ Gsb (cosetDecoration Gsb L base z.1) τ' *
        ∏ j, (recExp L γ δ (S.sign (blk j).upper.toNode) (Φ.clocks τ' j 0) (Φ.bdry L base z.1 j) *
          clRegionalPhase S (blk j).atoms L γ δ
            (cosetDecoration S L base (clExtendIndices (regionOf (blk j)) (κs j).1))
            (clLocalClock (regionOf (blk j)) (Φ.clocks τ' j) (τs j))) := by
  have hz : cosetDecoration Gsb L base z.1 =
      fun y => cosetDecoration S L base (Φ.glueFun z.1 (fun j => (κs j).1)) (Φ.node y) := by
    funext y
    unfold cosetDecoration
    rw [Φ.glue_node]
  have hb : ∀ j i, cosetDecoration S L base (Φ.glueFun z.1 (fun j => (κs j).1))
      (clBoundaryNodes (regionOf (blk j)) i) = Φ.bdry L base z.1 j i := by
    intro j i
    unfold cosetDecoration bdry
    rw [Φ.glue_ret _ _ (ret_bdryNode Φ hd j i)]
  rw [hz, Φ.phase_split hd, Φ.phaseProd_sb hd, mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  · refine Finset.prod_congr rfl fun c _ => ?_
    rw [Φ.glueTime_br]
  · refine Finset.prod_congr rfl fun j _ => ?_
    have hreg : clRegionalPhase S (blk j).atoms L γ δ
        (cosetDecoration S L base (clExtendIndices (regionOf (blk j)) (κs j).1))
        (clLocalClock (regionOf (blk j)) (Φ.clocks τ' j) (τs j)) =
        clRegionalPhase S (blk j).atoms L γ δ (cosetDecoration S L base (Φ.glueFun z.1 (fun j => (κs j).1)))
          (Φ.glueTime hd τ' τs) := by
      rw [Φ.locDec_eq hd hL base z κs j, Φ.clocks_eq_external hd τ' τs j, ← Φ.restrict_glueTime hd τ' τs j,
        clRegionalPhase_restrict (blk j).isBlock]
    have hrec : recExp L γ δ (S.sign (blk j).upper.toNode) (Φ.clocks τ' j 0) (Φ.bdry L base z.1 j) =
        Complex.exp (((-(Real.pi * δ * L ^ (2 * γ)) * τ' (Φ.hinge hd j) *
          boundaryEnergyFromMomenta (S.sign (blk j).upper.toNode)
            (cosetDecoration S L base (Φ.glueFun z.1 (fun j => (κs j).1)) (blk j).upper.toNode)
            (cosetDecoration S L base (Φ.glueFun z.1 (fun j => (κs j).1))
              ((blk j).upper.child (regionOf (blk j)).excluded))
            (cosetDecoration S L base (Φ.glueFun z.1 (fun j => (κs j).1))
              ((blk j).lower.child (regionOf (blk j)).positive))
            (cosetDecoration S L base (Φ.glueFun z.1 (fun j => (κs j).1))
              ((blk j).lower.child (regionOf (blk j)).negative)) : ℝ) : ℂ) * Complex.I) := by
      unfold recExp
      rw [Φ.clocks_zero hd, ← hb j 0, ← hb j 1, ← hb j 2, ← hb j 3]
      rfl
    have key : ∀ (a t b : ℝ), Complex.exp (((a * t * b : ℝ) : ℂ) * Complex.I + ((-a * t * b : ℝ) : ℂ) * Complex.I) = 1 := by
      intro a t b
      rw [← add_mul, ← Complex.ofReal_add, show a * t * b + -a * t * b = 0 by ring]
      simp
    rw [hreg, hrec, Φ.hinge_phase hd L γ δ _ j, ← mul_assoc, ← Complex.exp_add, key, one_mul]

end SpliceShape

end WaveTurbulence.VineB
