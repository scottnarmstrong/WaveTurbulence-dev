/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepAsm11
public import WaveTurbulence.Foundations.Stage1.Represents.RepSup1
public import WaveTurbulence.Foundations.XChain.SNormPointwise
import Mathlib.Tactic

/-!
# S2 REPRESENTS: an assembly context from per-slot superpositions

`SlotRep`: for each replacement slot a kernel `Fn s` on a time box `Box s` which is a centred superposition
(couples) or a superposition (trees) of unit amplitudes of total mass `μ s`, the boxes containing the slot times
of the spliced time domain.  `exists_asm` assembles the context `AsmCtx` with `fam` built by `choose`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.LGSpine
  WaveTurbulence.VineEstS3.FS MeasureTheory Set WaveTurbulence.RegRedLeaf
open scoped ENNReal

variable {w d : ℕ}

/-- Per-slot superpositions. -/
structure SlotRep (S : Garden w) (hS : S.IsPlain) (d : ℕ) (layer0 : GBranch S.tree → ℕ) (tt : Fin w → ℝ) where
  Fn : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ
  Box : ReplacementSlot S → Set (Fin 2 → ℝ)
  μ : ReplacementSlot S → ℝ≥0∞
  cp : ∀ p, CenSup (30 * d) (Box (Sum.inl p)) (Fn (Sum.inl p)) (μ (Sum.inl p))
  tr : ∀ b, Sup (30 * d) (Box (Sum.inr b)) (Fn (Sum.inr b)) (μ (Sum.inr b))
  hbox : ∀ τ ∈ splicedTimeDomain S layer0 tt, ∀ s, slotTs hS tt τ s ∈ Box s

theorem snorm_le_one_pointwise {d : ℕ} (A : ℕ) (a : Mom d → ℂ) (h : SNorm A 0 a ≤ 1) (k : Mom d) :
    ‖a k‖ ≤ 1 := by
  have := SNorm_pointwise (A := A) (B := 0) a 1 zero_le_one (by simpa using h) k
  simpa using this

open scoped Classical in
theorem exists_fam {S : Garden w} {hS : S.IsPlain} {layer0 : GBranch S.tree → ℕ} {tt : Fin w → ℝ}
    (R : SlotRep S hS d layer0 tt) :
    ∃ fam : SlotFam S d, (∀ s, ∀ ts ∈ R.Box s, ∀ k, HasSum (fun l => (fam.w s l : ℂ) * fam.a s l k *
      fsPhase (fam.m s l) ts) (R.Fn s ts k)) ∧ (∏ s, ∑' l, ENNReal.ofReal (fam.w s l)) ≤ ∏ s, R.μ s := by
  choose Λc cntc wc mc nc ac hc1 hc2 hc3 hc4 hc5 hc6 using R.cp
  choose Λt cntt wt mt at' ht1 ht2 ht3 ht4 ht5 using R.tr
  let fam : SlotFam S d :=
    { Λ := fun s => match s with | Sum.inl p => Λc p | Sum.inr b => Λt b
      cnt := fun s => by cases s with | inl p => exact cntc p | inr b => exact cntt b
      w := fun s => match s with | Sum.inl p => wc p | Sum.inr b => wt b
      m := fun s => match s with | Sum.inl p => mc p | Sum.inr b => mt b
      n := fun s => match s with | Sum.inl p => nc p | Sum.inr b => fun _ _ => 0
      a := fun s => match s with | Sum.inl p => ac p | Sum.inr b => at' b
      w_nn := fun s => by cases s with | inl p => exact hc1 p | inr b => exact ht1 b
      w_sum := fun s => by cases s with | inl p => exact hc2 p | inr b => exact ht2 b
      a_one := fun s l k => by
        cases s with
        | inl p => exact snorm_le_one_pointwise _ _ (hc3 p l) k
        | inr b => exact snorm_le_one_pointwise _ _ (ht3 b l) k
      a_snorm := fun s => by cases s with | inl p => exact hc3 p | inr b => exact ht3 b
      a_supp := fun p l k => hc4 p l k }
  refine ⟨fam, ?_, ?_⟩
  · intro s ts hts k
    cases s with
    | inl p => exact hc5 p ts hts k
    | inr b => exact ht4 b ts hts k
  · refine Finset.prod_le_prod fun s _ => ?_
    cases s with
    | inl p => exact hc6 p
    | inr b => exact ht5 b

open scoped Classical in
/-- The assembly context of per-slot superpositions (all scalar data definitionally the given ones). -/
noncomputable def asmOf {S : Garden w} (hS : S.IsPlain) (hd : 1 ≤ d) (L : ℝ) (hL : 0 < L) (γ δ η : ℝ)
    (base : Mom d) (roots : Fin w → Fin d → ℤ) (tt : Fin w → ℝ) (layer0 : GBranch S.tree → ℕ)
    (gs : (v : GBranch S.tree) → Option (LocalGapSpecification S v))
    (selSk : GenDecoration S d roots 0 → Prop)
    (hgs : ∀ D : SplicedKernelData S d, D.gapSpecification = gs → ∀ z : GenDecoration S d roots 0,
      splicedGapIndicator S D L γ η base z.1 = if selSk z then 1 else 0)
    (Cχ : ℝ) (hCpos : 0 < Cχ)
    (hC : ∀ H : Mom d → ℂ, ContDiff ℝ (30 * d) H → ∀ n : Fin d → ℤ,
      SNorm (30 * d) 0 (fun k => chiC d n k * H k) ≤ ENNReal.ofReal Cχ * SNorm (30 * d) 0 H)
    (R : SlotRep S hS d layer0 tt) : AsmCtx S d :=
  { hS := hS, hd := hd, L := L, hL := hL, γ := γ, δ := δ, η := η, base := base, roots := roots,
    tt := tt, layer0 := layer0, gs := gs, selSk := selSk, hgs := hgs, fam := Classical.choose (exists_fam R),
    Cχ := Cχ, hCpos := hCpos, hC := hC, Fn := R.Fn, Box := R.Box,
    hFn := (Classical.choose_spec (exists_fam R)).1, hbox := R.hbox }

open scoped Classical in
theorem asmOf_mass {S : Garden w} (hS : S.IsPlain) (hd : 1 ≤ d) (L : ℝ) (hL : 0 < L) (γ δ η : ℝ)
    (base : Mom d) (roots : Fin w → Fin d → ℤ) (tt : Fin w → ℝ) (layer0 : GBranch S.tree → ℕ)
    (gs : (v : GBranch S.tree) → Option (LocalGapSpecification S v))
    (selSk : GenDecoration S d roots 0 → Prop)
    (hgs : ∀ D : SplicedKernelData S d, D.gapSpecification = gs → ∀ z : GenDecoration S d roots 0,
      splicedGapIndicator S D L γ η base z.1 = if selSk z then 1 else 0)
    (Cχ : ℝ) (hCpos : 0 < Cχ)
    (hC : ∀ H : Mom d → ℂ, ContDiff ℝ (30 * d) H → ∀ n : Fin d → ℤ,
      SNorm (30 * d) 0 (fun k => chiC d n k * H k) ≤ ENNReal.ofReal Cχ * SNorm (30 * d) 0 H)
    (R : SlotRep S hS d layer0 tt) :
    (∏ s, ∑' l, ENNReal.ofReal ((asmOf hS hd L hL γ δ η base roots tt layer0 gs selSk hgs Cχ hCpos hC R).fam.w s l))
      ≤ ∏ s, R.μ s :=
  (Classical.choose_spec (exists_fam R)).2

end WaveTurbulence.Represents
