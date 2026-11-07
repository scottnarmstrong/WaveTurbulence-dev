/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepAsm6
import Mathlib.Tactic

/-!
# S2 REPRESENTS: the assembly context and the per-decoration / per-mode identities
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.LGSpine
  WaveTurbulence.VineEstS3.FS MeasureTheory Set
open scoped ENNReal

variable {w : ℕ}

open scoped Classical in
/-- All the data and typing hypotheses of the assembly of the skeleton integrand (vine-free case). -/
structure AsmCtx (S : Garden w) (d : ℕ) where
  hS : S.IsPlain
  hd : 1 ≤ d
  L : ℝ
  hL : 0 < L
  γ : ℝ
  δ : ℝ
  η : ℝ
  base : Mom d
  roots : Fin w → Fin d → ℤ
  tt : Fin w → ℝ
  layer0 : GBranch S.tree → ℕ
  gs : (v : GBranch S.tree) → Option (LocalGapSpecification S v)
  selSk : GenDecoration S d roots 0 → Prop
  hgs : ∀ D : SplicedKernelData S d, D.gapSpecification = gs → ∀ z : GenDecoration S d roots 0,
    splicedGapIndicator S D L γ η base z.1 = if selSk z then 1 else 0
  fam : SlotFam S d
  Cχ : ℝ
  hCpos : 0 < Cχ
  hC : ∀ H : Mom d → ℂ, ContDiff ℝ (30 * d) H → ∀ n : Fin d → ℤ,
    SNorm (30 * d) 0 (fun k => chiC d n k * H k) ≤ ENNReal.ofReal Cχ * SNorm (30 * d) 0 H
  Fn : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ
  Box : ReplacementSlot S → Set (Fin 2 → ℝ)
  hFn : ∀ s, ∀ ts ∈ Box s, ∀ k, HasSum (fun l => (fam.w s l : ℂ) * fam.a s l k *
    fsPhase (fam.m s l) ts) (Fn s ts k)
  hbox : ∀ τ ∈ splicedTimeDomain S layer0 tt, ∀ s, slotTs hS tt τ s ∈ Box s

namespace AsmCtx
variable {d : ℕ} {S : Garden w} (A : AsmCtx S d)

/-- The kernel data of the assembled mode `ξ`. -/
noncomputable def D (ξ : XiT A.fam) : SplicedKernelData S d :=
  asmData A.fam A.hS A.Cχ A.layer0 A.gs A.tt ξ

/-- The product of the slot kernels at decoration `κ` and times `τ`. -/
noncomputable def skel (κ : GenDecoration S d A.roots 0) (τ : GBranch S.tree → ℝ) : ℂ :=
  ∏ s, A.Fn s (slotTs A.hS A.tt τ s) (A.base + latticePoint A.L (κ.1 (slotNode A.hS s)))

/-- The bond product of the assembled mode. -/
noncomputable def E (ξ : XiT A.fam) (κ : GenDecoration S d A.roots 0) : ℂ :=
  ∏ x ∈ S.molecule.bonds, edgeS A.fam A.hS A.Cχ ξ x (A.base + latticePoint A.L (bondIndex S κ.1 x))

open scoped Classical in
/-- The summand of the assembled expansion of the skeleton integrand. -/
noncomputable def gI (ξ : XiT A.fam) (κ : GenDecoration S d A.roots 0) (τ : GBranch S.tree → ℝ) : ℂ :=
  (if A.selSk κ then ((epsDec S κ.1 : ℝ) : ℂ) else 0) *
    (constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξ * A.E ξ κ) *
    (splicedTimeDomain S A.layer0 A.tt).indicator (fun τ =>
      phaseProd A.L A.γ A.δ S (cosetDecoration S A.L A.base κ.1) τ * timeFac A.fam A.hS ξ τ) τ

open scoped Classical in
theorem tsum_gI (κ : GenDecoration S d A.roots 0) (τ : GBranch S.tree → ℝ) :
    ∑' ξ, A.gI ξ κ τ = (if A.selSk κ then ((epsDec S κ.1 : ℝ) : ℂ) else 0) *
      (splicedTimeDomain S A.layer0 A.tt).indicator (fun τ =>
        phaseProd A.L A.γ A.δ S (cosetDecoration S A.L A.base κ.1) τ * A.skel κ τ) τ := by
  by_cases hτ : τ ∈ splicedTimeDomain S A.layer0 A.tt
  · simp only [Set.indicator_of_mem hτ]
    have hs := hasSum_assembled A.fam A.hS A.Cχ A.hCpos.ne' A.L A.base A.roots A.tt A.Fn κ τ
      (fun s => A.hFn s _ (A.hbox τ hτ s) _)
    have h2 := (hs.mul_left ((if A.selSk κ then ((epsDec S κ.1 : ℝ) : ℂ) else 0) *
      phaseProd A.L A.γ A.δ S (cosetDecoration S A.L A.base κ.1) τ))
    have h3 : HasSum (fun ξ => A.gI ξ κ τ) ((if A.selSk κ then ((epsDec S κ.1 : ℝ) : ℂ) else 0) *
        (phaseProd A.L A.γ A.δ S (cosetDecoration S A.L A.base κ.1) τ * A.skel κ τ)) := by
      convert h2 using 1
      · funext ξ
        simp only [gI, E, Set.indicator_of_mem hτ]
        ring
      · unfold skel; ring
    exact h3.tsum_eq
  · simp only [Set.indicator_of_notMem hτ, mul_zero, gI]
    exact tsum_zero

end AsmCtx
end WaveTurbulence.Represents
