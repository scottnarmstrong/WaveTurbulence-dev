/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVB3
public import WaveTurbulence.Foundations.Stage1.Represents.RepH4
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-B♯ integration: the glued skeleton term as a mode series

`hasSum_modeG`: pointwise in the time, the skeleton integrand with the true slot kernels is the `HasSum` over the modes of
the weighted modal integrands.  `hasSum_skelTerm_modes`: the same for the integrated term `skelTerm` at a glued decoration
(Fubini in the mode, dominated by `ampBound · ∏ unitLb` with `∫‖·‖` from `integral_norm_modeG_le`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.LGSpine
  WaveTurbulence.VineB WaveTurbulence.VineEstS3.FS WaveTurbulence.RegRed WaveTurbulence.RedSplice
  WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS4 MeasureTheory

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}
variable (Φ : SpliceShape blk Gsb)

open scoped Classical in
theorem hasSum_modeG (hd : Disj blk) (hS : S.IsPlain) (hSb : Gsb.IsPlain) (L γ δ : ℝ) (base : Mom d)
    (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (fam : SlotFam Gsb d) (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (hexp : ∀ s', ∀ ts ∈ Box s', ∀ x, HasSum (fun l => (fam.w s' l : ℂ) * fam.a s' l x * fsPhase (fam.m s' l) ts)
      (slotFn D hS L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) h) layer hLayer
        (Φ.iota hS hSb s') ts x))
    (hbox : ∀ τ ∈ coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt, ∀ s',
      slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s')
    (κ : GenDecoration S d roots 0) (τ : GBranch S.tree → ℝ) :
    HasSum (fun ξ : ∀ s, fam.Λ s => ((modeWt fam ξ : ℝ) : ℂ) *
      modeG (Φ.modalFn hS hSb D L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) h) layer hLayer
        (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s'))) D hS L γ δ base tt layer κ τ)
      (modeG (slotFn D hS L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) h) layer hLayer)
        D hS L γ δ base tt layer κ τ) := by
  by_cases hτ : τ ∈ coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt
  · have hm := hasSum_modal_prod Φ hd hS hSb D L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) h) layer
      hLayer fam tt τ (fun x => base + latticePoint L (κ.1 x)) Box hexp (hbox τ hτ)
    have h2 := hm.mul_left ((epsDec S κ.1 : ℂ) * phaseProd L γ δ S (cosetDecoration S L base κ.1) τ)
    unfold modeG
    simp only [Set.indicator_of_mem hτ]
    convert h2 using 1
    · funext ξ; ring
    · ring
  · unfold modeG
    simp only [Set.indicator_of_notMem hτ, mul_zero]
    exact hasSum_zero

open scoped Classical in
theorem hasSum_skelTerm_modes (hd : Disj blk) (hS : S.IsPlain) (hSb : Gsb.IsPlain) {L : ℝ} (hL : L ≠ 0) (γ δ : ℝ)
    (base : Mom d) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (h : ℕ → Fin w → Fin w → Mom d → ℝ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (selSk : GenDecoration S d roots 0 → Prop)
    (hF : ∀ j, HF D hS L (unitProfile blk h j) layer base)
    (fam : SlotFam Gsb d) (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (hexp : ∀ s', ∀ ts ∈ Box s', ∀ x, HasSum (fun l => (fam.w s' l : ℂ) * fam.a s' l x * fsPhase (fam.m s' l) ts)
      (slotFn D hS L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) h) layer hLayer
        (Φ.iota hS hSb s') ts x))
    (hbox : ∀ τ ∈ coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt, ∀ s',
      slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s')
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    HasSum (fun ξ : ∀ s, fam.Λ s => ((modeWt fam ξ : ℝ) : ℂ) *
      skelTerm D hS L γ δ base roots tt layer selSk
        (Φ.modalFn hS hSb D L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) h) layer hLayer
          (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s'))) (Φ.glueDec hS hd hL base z κs))
      (skelTerm D hS L γ δ base roots tt layer selSk
        (slotFn D hS L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) h) layer hLayer)
        (Φ.glueDec hS hd hL base z κs)) := by
  by_cases hs : selSk (Φ.glueDec hS hd hL base z κs)
  · set κ := Φ.glueDec hS hd hL base z κs with hκ
    simp only [skelTerm_eq_integral, hs, ite_true]
    have : ∀ s, Countable (fam.Λ s) := fam.cnt
    set M : ℝ := ∏ j, unitLb (blk := blk) D hS L γ δ h layer hLayer base j (κs j) with hM
    have hM0 : 0 ≤ M := Finset.prod_nonneg fun j _ => unitLb_nonneg _ _ _ _ _ _ _ _ _ _ _
    have hwt : Summable (modeWt fam) :=
      (hasSum_prod_real (fun s l => fam.w s l) (fun s l => fam.w_nn s l) (fun s => fam.w_sum s)).summable
    let G : (∀ s, fam.Λ s) → (GBranch S.tree → ℝ) → ℂ := fun ξ τ => ((modeWt fam ξ : ℝ) : ℂ) *
      modeG (Φ.modalFn hS hSb D L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) h) layer hLayer
        (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s'))) D hS L γ δ base tt layer κ τ
    have hint : ∀ ξ, Integrable (G ξ) := fun ξ =>
      (integrable_modeG Φ hd hS hSb hL γ δ base D layer hLayer h tt (fun s' x => fam.a s' (ξ s') x)
        (fun s' => fam.m s' (ξ s')) hF z κs).const_mul _
    have hnorm : Summable fun ξ => ∫ τ, ‖G ξ τ‖ := by
      refine Summable.of_nonneg_of_le (fun ξ => integral_nonneg fun τ => norm_nonneg _) (fun ξ => ?_) (hwt.mul_right M)
      have e1 : ∫ τ, ‖G ξ τ‖ = modeWt fam ξ * ∫ τ, ‖modeG
          (Φ.modalFn hS hSb D L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) h) layer hLayer
            (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s'))) D hS L γ δ base tt layer κ τ‖ := by
        simp only [G, norm_mul, Complex.norm_real, Real.norm_of_nonneg (modeWt_nonneg fam ξ)]
        rw [integral_const_mul]
      rw [e1]
      refine mul_le_mul_of_nonneg_left
        ((integral_norm_modeG_le Φ hd hS hSb hL γ δ base D layer hLayer h tt (fun s' x => fam.a s' (ξ s') x)
          (fun s' => fam.m s' (ξ s')) hF z κs).trans ?_) (modeWt_nonneg fam ξ)
      have hab : ampBound hSb L base (fun s' x => fam.a s' (ξ s') x) z ≤ 1 :=
        Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun s _ => fam.a_one _ _ _
      calc _ ≤ 1 * M := mul_le_mul_of_nonneg_right hab hM0
        _ = M := one_mul _
    have key := hasSum_integral_of_summable_integral_norm hint hnorm
    have hpt : ∀ τ, ∑' ξ, G ξ τ = modeG
        (slotFn D hS L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) h) layer hLayer)
        D hS L γ δ base tt layer κ τ :=
      fun τ => (hasSum_modeG Φ hd hS hSb L γ δ base D layer hLayer h tt fam Box hexp hbox κ τ).tsum_eq
    simp only [hpt] at key
    refine key.congr_fun fun ξ => ?_
    simp only [G]
    rw [integral_const_mul]
  · simp only [skelTerm_eq_integral, hs, ite_false, mul_zero]
    exact hasSum_zero

end WaveTurbulence.Represents
