/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVD4
public import WaveTurbulence.Foundations.Stage1.Represents.RepVB10
public import WaveTurbulence.Foundations.Stage1.Represents.RepVB11
public import WaveTurbulence.Foundations.Stage1.Represents.RepVB12
public import WaveTurbulence.Foundations.Stage1.Represents.RepVB16
public import WaveTurbulence.Foundations.Stage1.Represents.RepVB8
import Mathlib.Tactic

/-!
# S2 REPRESENTS, session 12: 0/1-valued gap indicator, member points

`splicedGapIndicator_01`, `gap_value_01`: the gap functional is `{0,1}`-valued, so the common selection
`selSkC z := (gap.value z = 1)` satisfies `gap.value z = if selSkC z then 1 else 0`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA
  WaveTurbulence.VineEstS4 WaveTurbulence.VineC WaveTurbulence.LFTwist WaveTurbulence.VineAlign
  WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic MeasureTheory

variable {w p : ℕ} {kind : Bool}

theorem prod_01 {ι : Type*} [Fintype ι] (f : ι → ℝ) (h : ∀ i, f i = 0 ∨ f i = 1) :
    ∏ i, f i = 0 ∨ ∏ i, f i = 1 := by
  by_cases hz : ∃ i, f i = 0
  · obtain ⟨i, hi⟩ := hz
    exact Or.inl (Finset.prod_eq_zero (Finset.mem_univ i) hi)
  · push_neg at hz
    exact Or.inr (Finset.prod_eq_one fun i _ => (h i).resolve_left (hz i))

open scoped Classical in
theorem splicedGapIndicator_01 {d : ℕ} (G : Garden w) (D : SplicedKernelData G d) (L γ η : ℝ) (base : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) :
    splicedGapIndicator G D L γ η base z = 0 ∨ splicedGapIndicator G D L γ η base z = 1 := by
  unfold splicedGapIndicator
  refine prod_01 _ fun v => ?_
  rcases D.gapSpecification v with _ | q
  · exact Or.inr rfl
  · dsimp only
    by_cases h : Molecule.gapKind L γ η
        (base + latticePoint L (bondIndex G z q.first) - (base + latticePoint L (bondIndex G z q.second))) = q.kind
    · exact Or.inr (if_pos h)
    · exact Or.inl (if_neg h)

open scoped Classical in
theorem gap_value_01 {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) {d : ℕ} {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d)
    (roots : Fin (2 * R) → (Fin d → ℤ)) (z : GenDecoration a.fullProfile.piece.gap.garden d roots 0) :
    a.fullProfile.piece.gap.value d L γ η hL base roots z = 0 ∨
      a.fullProfile.piece.gap.value d L γ η hL base roots z = 1 := by
  let D' : SplicedKernelData (stSt a.prime.skeleton a.totalSigma).G d :=
    ⟨fun _ => 0, ∅, fun _ => 0, fun _ _ => 0, fun _ => 0, NormalizedSplice.gapSpecification a.prime.skeleton a.totalSigma,
      fun _ => 0, fun _ => 0⟩
  have h := NormalizedSplice.gapValue_eq_indicator a.totalSigma D' rfl L γ η base z.1
  change NormalizedSplice.gapValue a.prime.skeleton a.totalSigma L γ η base z.1 = 0 ∨
    NormalizedSplice.gapValue a.prime.skeleton a.totalSigma L γ η base z.1 = 1
  rw [h]
  exact splicedGapIndicator_01 _ D' L γ η base z.1


open scoped Classical in
/-- `valueSel_modes` together with the summability of the mode series (from `hasSum_skelVal_outerValM`). -/
theorem member_modes {P : WTParams} {R : ℕ} (U : TypeFamily P (2 * R)) {S : Garden (2 * R)} {J : Type}
    [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden (2 * R)} (Φ : SpliceShape blk Gsb)
    (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (hctrl : U.toLF.Controlled (layeredReconstruction D hS layer hLayer)) (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (selSk : GenDecoration S P.d roots 0 → Prop) (Zw : GenDecoration Gsb P.d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S P.d roots 0, (if selSk κ then (1 : ℝ) else 0) = Zw (Φ.resDec hS hd κ))
    (hF : ∀ i j, HF D hS P.L (unitProfile blk (U.h i) j) layer base)
    (fam : U.ι → SlotFam Gsb P.d) (Box : U.ι → ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (hexp : ∀ i s', ∀ ts ∈ Box i s', ∀ x, HasSum
      (fun l => ((fam i).w s' l : ℂ) * (fam i).a s' l x * fsPhase ((fam i).m s' l) ts)
      (slotFn D hS P.L P.γ P.δ (typeProfiles (layeredReconstruction D hS layer hLayer) (U.h i)) layer hLayer
        (Φ.iota hS hSb s') ts x))
    (hbox : ∀ i, ∀ τ ∈ coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt, ∀ s',
      slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box i s') :
    U.toLF.valueSel tt base roots (layeredReconstruction D hS layer hLayer)
        (fun κ => selSk (collapseGenDecoration D hS κ)) =
      @Finset.sum U.ι ℂ _ (@Finset.univ _ U.fin) (fun i =>
        ((U.sign i : ℝ) : ℂ) * ∑' ξ : (∀ s, (fam i).Λ s), ((modeWt (fam i) ξ : ℝ) : ℂ) *
          outerValM Gsb P.L P.γ P.δ base roots tt (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)
            (Φ.hinges hd) Zw hSb (fun s' => (fam i).a s' (ξ s')) (fun s' => (fam i).m s' (ξ s'))
            (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd) (unitKernelM blk D hS P.L P.γ P.δ (U.h i) layer hLayer base)) ∧
    ∀ i, Summable (fun ξ : (∀ s, (fam i).Λ s) => ((modeWt (fam i) ξ : ℝ) : ℂ) *
          outerValM Gsb P.L P.γ P.δ base roots tt (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)
            (Φ.hinges hd) Zw hSb (fun s' => (fam i).a s' (ξ s')) (fun s' => (fam i).m s' (ξ s'))
            (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd) (unitKernelM blk D hS P.L P.γ P.δ (U.h i) layer hLayer base)) := by
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one hL1
  refine ⟨valueSel_modes U Φ hd D hS hSb layer hLayer hctrl hd1 hL1 tt base roots selSk Zw hZ hF fam Box hexp hbox,
    fun i => ?_⟩
  exact (hasSum_skelVal_outerValM Φ hd hS hSb hL0 P.γ P.δ base D layer hLayer (U.h i) tt selSk Zw hZ (hF i)
    (fam i) (Box i) (hexp i) (hbox i)).summable

end WaveTurbulence.Represents
