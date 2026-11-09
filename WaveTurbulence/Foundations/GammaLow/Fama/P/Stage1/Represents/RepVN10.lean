/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Stage1.Represents.RepVN10` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVN7
public import WaveTurbulence.Foundations.Stage1.Represents.RepVN9
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVN5
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Represents.RepVN10
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Amend7
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Deg
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Desig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Final
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceFlowKind
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Gap
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Greg
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Group
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVC
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.IP
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Ingr
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj3
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Pairs
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Rev
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Runs
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Skip
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Split
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.SurvData
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Top
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.TripleDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.TripleHinge
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.V0
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.VC
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.SubproGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.SubproIso2
public import WaveTurbulence.Foundations.GammaLow.Famb.Molecule.TwistSourceFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainFlows
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Spine.VineDelObjects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepH13
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepH16
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNV2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNV3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNV4
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepRep1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepRep3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVN2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVN3


/-!
# S2 REPRESENTS, VINE-D: `RepresentsInt` of a vine piece from the mode form (F-CONST numerics)

`representsIntA_of_vineModes`: the final glue of the VINE-D engine.  The mode form of the value (VINE-B♯ + VINE-C), the
per-slot moment bounds (`slots_existM`), the hinge data (`exists_hinge_data_mod` from VINEEST(λ), G1, G2) and the
exponent bookkeeping (`hexp`, `hg`, `hb`, `hh`: step 4) give `π.RepresentsInt`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
namespace WaveTurbulence.GammaLow.Fama.Represents
open WaveTurbulence.Represents WaveTurbulence.GammaLow.FinalCount
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RepAnalytic WaveTurbulence.GammaLow.FinalCount
  WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS

variable {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]
open scoped ENNReal WaveTurbulence.GammaLow.FinalCount

open scoped Classical in
theorem representsIntA_of_vineModes {P : WTParams} {R : ℕ} (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L) (hη0 : 0 ≤ P.η) (π : Stage1PieceG P R)
    (hS : π.Gsb.IsPlain) (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (selSk : GenDecoration π.Gsb P.d roots 0 → Prop)
    (hgsp : ∀ D' : SplicedKernelData π.Gsb P.d, D'.gapSpecification = π.gapSpecification →
      ∀ z : GenDecoration π.Gsb P.d roots 0,
        splicedGapIndicator π.Gsb D' P.L P.γ P.η base z.1 = if selSk z then 1 else 0)
    {J : Type} [Fintype J] [DecidableEq J]
    (route : ReplacementSlot π.Gsb → Fin 2 → ClkSrc π.Gsb ⊕ J)
    (hroute : ∀ s i, route s i = Sum.inl (argSrc hS s i) ∨ ∃ j, route s i = Sum.inr j)
    (hclk : J → Fin 3 → ClkSrc π.Gsb) (hmom : J → Fin 4 → GNode π.Gsb.tree)
    (src : J → Fin 4 → HingeDarts π.Gsb π.Cs.hinges ⊕ Fin (2 * R))
    (src_dart : ∀ j i x, src j i = Sum.inl x → ∀ z : GenDecoration π.Gsb P.d roots 0,
      bondIndex π.Gsb z.1 x.1 = z.1 (hmom j i))
    (src_root : ∀ j i r, src j i = Sum.inr r → ∀ z : GenDecoration π.Gsb P.d roots 0, z.1 (hmom j i) = roots r)
    {I : Type} [Fintype I] (sgn : I → ℂ) (hsgn : ∀ i, ‖sgn i‖ ≤ 1)
    (fam : I → SlotFam π.Gsb P.d) (μ : I → ReplacementSlot π.Gsb → ℝ≥0∞)
    (HkM : I → J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ) {c θ : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hcθ : 2 * c ≤ θ)
    (hμ : ∀ i s, ∑' l, maxBracketPow θ (half ((fam i).m s l)) * ENNReal.ofReal ((fam i).w s l) ≤ μ i s)
    -- numerics data
    (x K Ch : ℝ) (hx : x = P.C₁ * Real.sqrt P.δ) (hK : 1 ≤ K) (hCh : 1 ≤ Ch)
    (hC : Cchi P.d * (nodeBallCard P.d : ℝ) * (9 * K) ^ 2 * Ch ≤ P.C₁)
    (sz g : ReplacementSlot π.Gsb → ℕ) (lf : I → ReplacementSlot π.Gsb → ℝ) (hlf : ∀ i s, 0 ≤ lf i s)
    (hμb : ∀ i s, μ i s ≤ ENNReal.ofReal (K * x ^ (sz s) * P.L ^ (-(P.η ^ 8) * (g s : ℝ)) * lf i s))
    (M0 : I → J → ℝ) (cl2 gj nj : J → ℕ) (lfj : I → J → ℝ) (hlfj : ∀ i j, 0 ≤ lfj i j)
    (hM : ∀ i j, 0 ≤ M0 i j ∧ M0 i j ≤ x ^ (cl2 j) *
      P.L ^ (-(P.η ^ 8) * (gj j : ℝ) - P.η ^ 2 / 2 * (nj j : ℝ) + P.η ^ 7) * lfj i j)
    (hhinge : ∀ i (ξ : ∀ s, (fam i).Λ s), ∃ (H : HingeFam J P.d) (Mh : J → ℝ),
      (∀ j c', ∑' l, H.w j c' l ≤ Mh j) ∧
      HHkProp π tt base roots selSk hclk hmom
        (fun j => HkM i j (modLam (fun s => (fam i).m s (ξ s)) route j)) H ∧
      ∏ j, Mh j ≤ (∏ j, (Ch * M0 i j)) *
        ∏ j, (1 + |((modLam (fun s => (fam i).m s (ξ s)) route j : ℤ) : ℝ)|) ^ c)
    (n : ℕ) (s : ℝ) (hs : ∑ i, ‖sgn i‖ * ((∏ t, lf i t) * ∏ j, lfj i j) ≤ s)
    (hexp : (∑ t, sz t) + ∑ j, cl2 j = n - π.Gsb.order)
    (hg : π.gsk ≤ (∑ t, g t) + ∑ j, gj j) (hb : π.bsk ≤ ∑ j, nj j) (hh : Fintype.card J ≤ π.Cs.hinges.card)
    (hJ : Fintype.card J ≤ π.Gsb.order) (val : ℂ)
    (hval : val = ∑ i, sgn i * ∑' ξ : ∀ t, (fam i).Λ t, (((∏ t, (fam i).w t (ξ t) : ℝ)) : ℂ) *
        outerValM π.Gsb P.L P.γ P.δ base roots tt π.layer π.Cs.hinges (fun z => if selSk z then 1 else 0) hS
          (fun t => (fam i).a t (ξ t)) (fun t => (fam i).m t (ξ t)) route hclk hmom (HkM i)) :
    π.RepresentsInt n tt base roots s val := by
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one hL1
  obtain ⟨hCge, -⟩ := Cchi_spec hd1
  have hb1 : (1 : ℝ) ≤ nodeBallCard P.d := by exact_mod_cast nodeBallCard_pos P.d
  have hx0 : 0 ≤ x := by
    rw [hx]
    have hC1 : 0 ≤ P.C₁ := by
      have : 1 ≤ Cchi P.d * (nodeBallCard P.d : ℝ) * (9 * K) ^ 2 * Ch := by
        have h1 := one_le_mul_of_one_le_of_one_le hCge hb1
        have h2 : 1 ≤ (9 * K) ^ 2 := by nlinarith
        exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 h2) hCh
      linarith
    exact mul_nonneg hC1 (Real.sqrt_nonneg _)
  have hbr : Fintype.card (GBranch π.Gsb.tree) = π.Gsb.order := WaveTurbulence.Mole.card_gbranch π.Gsb.tree
  have hpairs := sourcePair_card_twice π.Gsb hS
  have hslotsc : Fintype.card (ReplacementSlot π.Gsb) = 2 * π.Gsb.order + R := by
    unfold ReplacementSlot
    rw [Fintype.card_sum, hbr]
    omega
  have hord : ∑ j, (π.Gsb.tree j).order = π.Gsb.order := rfl
  set T : ℝ := x ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
    P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ)) with hT
  have hT0 : 0 ≤ T := by
    have hC1 : 0 ≤ P.C₁ := by
      have : 1 ≤ Cchi P.d * (nodeBallCard P.d : ℝ) * (9 * K) ^ 2 * Ch := by
        have h1 := one_le_mul_of_one_le_of_one_le hCge hb1
        have h2 : 1 ≤ (9 * K) ^ 2 := by nlinarith
        exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 h2) hCh
      linarith
    have := Real.rpow_nonneg hL0.le (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) +
      P.η ^ 7 * (π.Cs.hinges.card : ℝ))
    positivity
  rw [hval]
  have hKh0 : ∀ i, 0 ≤ ∏ j, (Ch * M0 i j) := fun i =>
    Finset.prod_nonneg fun j _ => mul_nonneg (by linarith) (hM i j).1
  refine RepIntC.toRepresentsInt (repIntC_vine_modes hd1 hL0 π hS tt base roots selSk hgsp route hroute hclk hmom
    src src_dart src_root sgn fam μ HkM hc hc1 hcθ hμ (fun i => ∏ j, (Ch * M0 i j)) hKh0 hhinge
    (fun i => T * ((∏ t, lf i t) * ∏ j, lfj i j))
    (fun i => mul_nonneg hT0 (mul_nonneg (Finset.prod_nonneg fun t _ => hlf i t)
      (Finset.prod_nonneg fun j _ => hlfj i j))) ?_) n s ?_
  · intro i
    have hne : ∀ t, μ i t ≠ ⊤ := fun t => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hμb i t)
    have hμr : ∀ t, 0 ≤ (μ i t).toReal ∧ (μ i t).toReal ≤ K * x ^ (sz t) *
        P.L ^ (-(P.η ^ 8) * (g t : ℝ)) * lf i t := fun t =>
      ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal (by
        have := hlf i t
        have : 0 ≤ P.L ^ (-(P.η ^ 8) * (g t : ℝ)) := Real.rpow_nonneg hL0.le _
        have : 0 ≤ x ^ (sz t) := pow_nonneg hx0 _
        have : 0 ≤ K := by linarith
        positivity) (hμb i t)⟩
    have hreal := vine_mass_le_repBound (nsb := π.Gsb.order) (R := R)
      (ιs := ReplacementSlot π.Gsb) (ιj := J) hslotsc hJ x P.L K (Cchi P.d) (nodeBallCard P.d : ℝ) Ch P.C₁
      (P.η ^ 8) (P.η ^ 2 / 2) (P.η ^ 7) hx0 hL1 hK hCge hb1 hCh hC (by positivity) (by positivity) (by positivity)
      (fun t => (μ i t).toReal) sz g (lf i) (hlf i) hμr (M0 i) cl2 gj nj (lfj i) (hlfj i) (hM i)
      n π.Gsb.order π.gsk π.bsk π.Cs.hinges.card hexp rfl hg hb hh
    have hmu : ∏ t, (9 * μ i t) = ENNReal.ofReal (9 ^ (2 * π.Gsb.order + R) * ∏ t, (μ i t).toReal) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_prod_of_nonneg (fun t _ => ENNReal.toReal_nonneg)]
      simp_rw [ENNReal.ofReal_toReal (hne _)]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hslotsc]
      congr 1
      rw [ENNReal.ofReal_pow (by norm_num)]
      simp
    rw [hmu, hbr, hord, ← ENNReal.ofReal_mul (by
      have := hKh0 i; have := Cchi_spec hd1; positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hCχ0 : 0 ≤ Cchi P.d := by linarith
    calc _ = Cchi P.d ^ π.Gsb.order * (9 ^ (2 * π.Gsb.order + R) * ∏ t, (μ i t).toReal) *
          (nodeBallCard P.d : ℝ) ^ π.Gsb.order * ∏ j, (Ch * M0 i j) := by
          push_cast; ring
      _ ≤ _ := hreal
      _ = _ := by simp only [hT]
  · calc ∑ i, ‖sgn i‖ * (T * ((∏ t, lf i t) * ∏ j, lfj i j))
        = T * ∑ i, ‖sgn i‖ * ((∏ t, lf i t) * ∏ j, lfj i j) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ T * s := mul_le_mul_of_nonneg_left hs hT0
      _ = repBoundA P π n s := by simp only [hT, repBoundA, hx]

end WaveTurbulence.GammaLow.Fama.Represents
