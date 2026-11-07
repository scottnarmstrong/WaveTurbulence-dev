/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepH6
public import WaveTurbulence.Foundations.Stage1.Represents.RepH7

/-!
# S2 REPRESENTS, VINE-D (8): the summand of the assembled expansion with vine factors

`gIH ξh κ τ`: the summand at the assembled mode `ξh = ⟨ξ, ζ⟩` of the expansion of the outer integrand at the decoration
`κ` and the times `τ`: selection and spliced epsilon, the constant weight, the bond amplitudes, the hinge amplitude at the
bond momenta, and the phases.  `tsum_gIH`: summed over the modes it is the outer integrand (slot kernels times vine
factors).  On the support of the slot part, the hinge amplitude at the bond momenta is the product of the vine
amplitudes at the hinge momenta (`hingeAmp_dec`): the unit-ball cut-off is inactive there.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RepAnalytic
  WaveTurbulence.VineEstS3.FS MeasureTheory
open scoped ENNReal

variable {w d : ℕ} {S : Garden w}

namespace AsmCtxH
variable (A : AsmCtxH S d)

theorem hmomOf_dec (κ : GenDecoration S d A.roots 0) (j : A.J) (i : Fin 4) :
    A.hmomOf j (fun x => A.base + latticePoint A.L (bondIndex S κ.1 x.1)) i =
      A.base + latticePoint A.L (κ.1 (A.hmom j i)) := by
  unfold hmomOf
  rcases h : A.src j i with x | r
  · simp only
    rw [A.src_dart j i x h κ]
  · simp only
    rw [A.src_root j i r h κ]

open scoped Classical in
theorem hingeAmp_dec (ξh : A.Xi) (κ : GenDecoration S d A.roots 0)
    (h0 : constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξh.1 * A.E ξh.1 κ ≠ 0) :
    A.hingeAmp ξh (fun x => A.base + latticePoint A.L (bondIndex S κ.1 x.1)) =
      ∏ j, A.H.a j _ (ξh.2 j) (fun i => A.base + latticePoint A.L (κ.1 (A.hmom j i))) := by
  have hz : ∀ ℓ : GLeaf S.tree, κ.1 ℓ.toNode = κ.1 (S.pair ℓ).toNode := κ.2.1.2
  have hin : ∀ x : HingeDarts S A.hinges,
      ‖(A.base + latticePoint A.L (bondIndex S κ.1 x.1)) - cenS A.fam ξh.1 (slotOfDart A.hS x.1)‖ ≤ 1 := by
    intro x
    rw [bondIndex_eq_slotNode A.hS κ.1 hz x.1]
    exact slot_near A.fam A.hS A.Cχ A.L A.base A.roots A.tt κ ξh.1 h0 _
  unfold hingeAmp
  rw [if_pos hin, mul_one]
  exact Finset.prod_congr rfl fun j _ => by
    congr 1
    funext i
    exact A.hmomOf_dec κ j i

open scoped Classical in
/-- The summand of the assembled expansion with vine factors. -/
noncomputable def gIH (ξh : A.Xi) (κ : GenDecoration S d A.roots 0) (τ : GBranch S.tree → ℝ) : ℂ :=
  (if A.selSk κ then ((splicedEpsilon S A.hinges κ.1 : ℝ) : ℂ) else 0) *
    (A.constWH ξh * A.E ξh.1 κ * A.hingeAmp ξh (fun x => A.base + latticePoint A.L (bondIndex S κ.1 x.1))) *
    (splicedTimeDomain S A.layer0 A.tt).indicator (fun τ =>
      phaseProd A.L A.γ A.δ S (cosetDecoration S A.L A.base κ.1) τ * A.timeFacH ξh τ) τ

/-- The vine factors of the outer integrand at `κ`, `τ`. -/
noncomputable def hk (κ : GenDecoration S d A.roots 0) (τ : GBranch S.tree → ℝ) : ℂ :=
  ∏ j, A.Hk j (fun i => clockOf S A.tt τ (A.hclk j i)) (fun i => A.base + latticePoint A.L (κ.1 (A.hmom j i)))

theorem slotTerm_mul_hingeTerm (ξh : A.Xi) (κ : GenDecoration S d A.roots 0) (τ : GBranch S.tree → ℝ) :
    slotTerm A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξh.1 κ.1 τ *
        hingeTerm A.fam A.hS A.H A.hmom A.hclk A.L A.base A.tt ξh κ.1 τ =
      A.constWH ξh * A.E ξh.1 κ * A.hingeAmp ξh (fun x => A.base + latticePoint A.L (bondIndex S κ.1 x.1)) *
        A.timeFacH ξh τ := by
  by_cases h0 : constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξh.1 * A.E ξh.1 κ = 0
  · have hl : slotTerm A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξh.1 κ.1 τ = 0 := by
      unfold slotTerm
      have : constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξh.1 *
          (∏ x ∈ S.molecule.bonds, edgeS A.fam A.hS A.Cχ ξh.1 x (A.base + latticePoint A.L (bondIndex S κ.1 x))) = 0 :=
        h0
      rw [this, zero_mul]
    have hr : A.constWH ξh * A.E ξh.1 κ = 0 := by
      unfold constWH
      rw [show constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξh.1 * (∏ j, ((A.H.w j _ (ξh.2 j) : ℝ) : ℂ)) *
          A.rootHPhase ξh * A.E ξh.1 κ =
          (constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξh.1 * A.E ξh.1 κ) *
            ((∏ j, ((A.H.w j _ (ξh.2 j) : ℝ) : ℂ)) * A.rootHPhase ξh) by ring, h0, zero_mul]
    rw [hl, zero_mul, hr, zero_mul, zero_mul]
  · rw [A.hingeAmp_dec ξh κ h0]
    unfold slotTerm hingeTerm constWH
    have hph := A.timeFac_mul_hinge_phase ξh τ
    have hsplit : (∏ j, ((A.H.w j _ (ξh.2 j) : ℂ) *
        A.H.a j _ (ξh.2 j) (fun c => A.base + latticePoint A.L (κ.1 (A.hmom j c))) *
        fsPhase (A.H.m j _ (ξh.2 j)) (fun c => clockOf S A.tt τ (A.hclk j c)))) =
        (∏ j, ((A.H.w j _ (ξh.2 j) : ℝ) : ℂ)) *
          (∏ j, A.H.a j _ (ξh.2 j) (fun c => A.base + latticePoint A.L (κ.1 (A.hmom j c)))) *
          ∏ j, fsPhase (A.H.m j _ (ξh.2 j)) (fun c => clockOf S A.tt τ (A.hclk j c)) := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    rw [hsplit]
    have hE : (∏ x ∈ S.molecule.bonds, edgeS A.fam A.hS A.Cχ ξh.1 x (A.base + latticePoint A.L (bondIndex S κ.1 x))) =
        A.E ξh.1 κ := rfl
    rw [hE]
    linear_combination (constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξh.1 * A.E ξh.1 κ *
      (∏ j, ((A.H.w j _ (ξh.2 j) : ℝ) : ℂ)) *
      (∏ j, A.H.a j _ (ξh.2 j) (fun c => A.base + latticePoint A.L (κ.1 (A.hmom j c))))) * hph

open scoped Classical in
theorem hasSum_gIH (κ : GenDecoration S d A.roots 0) (τ : GBranch S.tree → ℝ) :
    HasSum (fun ξh => A.gIH ξh κ τ) ((if A.selSk κ then ((splicedEpsilon S A.hinges κ.1 : ℝ) : ℂ) else 0) *
      (splicedTimeDomain S A.layer0 A.tt).indicator (fun τ =>
        phaseProd A.L A.γ A.δ S (cosetDecoration S A.L A.base κ.1) τ * (A.skel κ τ * A.hk κ τ)) τ) := by
  by_cases hτ : τ ∈ splicedTimeDomain S A.layer0 A.tt
  · by_cases hsel : A.selSk κ
    · simp only [Set.indicator_of_mem hτ, if_pos hsel]
      have hs := hasSum_assembledH A.fam A.hS A.hd A.Cχ A.hC A.hCpos A.L A.base A.roots A.tt A.Fn κ τ
        (fun s => A.hFn s _ (A.hbox τ hτ s) _) A.H A.hmom A.hclk A.Hk A.Mh A.hMh
        (fun j c hc => A.hHk κ hsel τ hτ j c hc)
      have h2 := hs.mul_left (((splicedEpsilon S A.hinges κ.1 : ℝ) : ℂ) *
        phaseProd A.L A.γ A.δ S (cosetDecoration S A.L A.base κ.1) τ)
      convert h2 using 1
      · funext ξh
        simp only [gIH, if_pos hsel, Set.indicator_of_mem hτ]
        rw [mul_assoc (((splicedEpsilon S A.hinges κ.1 : ℝ) : ℂ)) (phaseProd _ _ _ _ _ _),
          A.slotTerm_mul_hingeTerm ξh κ τ]
        ring
      · unfold AsmCtx.skel AsmCtxH.hk; ring
    · simp only [gIH, if_neg hsel, zero_mul]
      exact hasSum_zero
  · simp only [gIH, Set.indicator_of_notMem hτ, mul_zero]
    exact hasSum_zero

end AsmCtxH
end WaveTurbulence.Represents
