/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.EngDRep
public import WaveTurbulence.Foundations.Flower.MkSlots.EngVN

/-! # B3s-HELPER3 B3 (3): `RepresentsIntMK` of a pinned vine piece from the mode form, on a general time domain

`representsIntMK_of_vineModesFixD`: `MkSlots.representsIntMK_of_vineModesFix` (EngVN) with the per-mode outer forms
`outerValMμD … Dom …` on an arbitrary time domain `Dom` against `fixMeasure π.fix`. Changes against EngVN:
* `hslice` is replaced by `hsliceD` (on the pinned slice, `Dom` is the relaxed `splicedTimeDomainFix`);
* NEW `hD : MeasurableSet Dom` and `hμD : fixMeasure π.fix Dom ≤ 1` (replacing `fixMeasure_splicedTimeDomain_le`);
* NEW conjunct `HHkPropD … Dom …` in `hhinge`: the hinge HasSum at the points of `Dom` whose pinned coordinates are the
  pins (main's `HHkProp`, kept, builds main's `AsmCtxH`; `HHkPropD` covers the domain of integration). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.Induct WaveTurbulence.LGSpine WaveTurbulence.Represents
  WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton TTree
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlots
open scoped ENNReal

namespace WaveTurbulence.Flower.MkSlotsB

open scoped Classical in
/-- **`RepresentsIntMK` of a pinned vine piece from the mode form, on a general time domain `Dom`** (EngVN's
`representsIntMK_of_vineModesFix` with `outerValMμD … Dom …`, `hsliceD`, `hD`, `hμD` and `HHkPropD`). -/
theorem representsIntMK_of_vineModesFixD {P : WTParams} {R : ℕ} (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L) (hη0 : 0 ≤ P.η)
    (π : Stage1PieceMK P.d R) (hS : π.Gsb.IsPlain) (tt : Fin (2 * R) → ℝ) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (selSk : GenDecoration π.Gsb P.d roots 0 → Prop)
    (hgsp : ∀ D' : SplicedKernelData π.Gsb P.d, D'.gapSpecification = π.gapSpecification →
      ∀ z : GenDecoration π.Gsb P.d roots 0,
        splicedGapIndicator π.Gsb D' P.L P.γ P.η base z.1 = if selSk z then 1 else 0)
    -- the time domain `Dom`: measurable, of pinned mass `≤ 1`, the relaxed pinned domain on the pinned slice
    (Dom : Set (GBranch π.Gsb.tree → ℝ)) (hD : MeasurableSet Dom) (hμD : fixMeasure π.fix Dom ≤ 1)
    (hsliceD : ∀ τ : {b : GBranch π.Gsb.tree // π.fix b = none} → ℝ,
      π.Gsb.extendFix π.fix τ ∈ Dom ↔ π.Gsb.extendFix π.fix τ ∈ splicedTimeDomainFix π.Gsb π.layer tt π.fix ∩ splicedLBDomain π.lb)
    (hfilt : ∀ a q, π.filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) (hind : ∀ k, 0 ≤ π.ind k ∧ π.ind k ≤ 1)
    (cP : ℝ) (hcP : 0 ≤ cP)
    {J : Type} [Fintype J] [DecidableEq J]
    (route : ReplacementSlot π.Gsb → Fin 2 → ClkSrc π.Gsb ⊕ J)
    (hroute : ∀ s i, route s i = Sum.inl (argSrc hS s i) ∨ ∃ j, route s i = Sum.inr j)
    (hclk : J → Fin 3 → ClkSrc π.Gsb) (hmom : J → Fin 4 → GNode π.Gsb.tree)
    (src : J → Fin 4 → HingeDarts π.Gsb π.Cs.hinges ⊕ Fin (2 * R))
    (src_dart : ∀ j i x, src j i = Sum.inl x → ∀ z : GenDecoration π.Gsb P.d roots 0,
      bondIndex π.Gsb z.1 x.1 = z.1 (hmom j i))
    (src_root : ∀ j i r, src j i = Sum.inr r → ∀ z : GenDecoration π.Gsb P.d roots 0, z.1 (hmom j i) = roots r)
    {I : Type} [Fintype I] (sgn : I → ℂ) (hsgn : ∀ i, ‖sgn i‖ ≤ 1)
    (fam : I → SlotFam π.Gsb P.d) (μs : I → ReplacementSlot π.Gsb → ℝ≥0∞)
    (HkM : I → J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ) {c θ : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hcθ : 2 * c ≤ θ)
    (hμ : ∀ i s, ∑' l, maxBracketPow θ (half ((fam i).m s l)) * ENNReal.ofReal ((fam i).w s l) ≤ μs i s)
    -- numerics data
    (x K Ch : ℝ) (hx : x = P.C₁ * Real.sqrt P.δ) (hK : 1 ≤ K) (hCh : 1 ≤ Ch)
    (hC : Cchi P.d * (nodeBallCard P.d : ℝ) * (9 * K) ^ 2 * Ch ≤ P.C₁)
    (sz g : ReplacementSlot π.Gsb → ℕ) (lf : I → ReplacementSlot π.Gsb → ℝ) (hlf : ∀ i s, 0 ≤ lf i s)
    (hμb : ∀ i s, μs i s ≤ ENNReal.ofReal (K * x ^ (sz s) * P.L ^ (-(P.η ^ 8) * (g s : ℝ)) * lf i s))
    (M0 : I → J → ℝ) (cl2 gj nj : J → ℕ) (lfj : I → J → ℝ) (hlfj : ∀ i j, 0 ≤ lfj i j)
    (hM : ∀ i j, 0 ≤ M0 i j ∧ M0 i j ≤ x ^ (cl2 j) *
      P.L ^ (-(P.η ^ 8) * (gj j : ℝ) - P.η ^ 2 / 2 * (nj j : ℝ) + P.η ^ 7) * lfj i j)
    (hhinge : ∀ i (ξ : ∀ s, (fam i).Λ s), ∃ (H : HingeFam J P.d) (Mh : J → ℝ),
      (∀ j c', ∑' l, H.w j c' l ≤ Mh j) ∧
      HHkProp π.toStage1PieceD tt base roots selSk hclk hmom
        (fun j => HkM i j (modLam (fun s => (fam i).m s (ξ s)) route j)) H ∧
      HHkPropD π tt base roots selSk Dom hclk hmom
        (fun j => HkM i j (modLam (fun s => (fam i).m s (ξ s)) route j)) H ∧
      ∏ j, Mh j ≤ (∏ j, (Ch * M0 i j)) *
        ∏ j, (1 + |((modLam (fun s => (fam i).m s (ξ s)) route j : ℤ) : ℝ)|) ^ c)
    (n : ℕ) (s : ℝ) (hs : ∑ i, ‖sgn i‖ * ((∏ t, lf i t) * ∏ j, lfj i j) ≤ s)
    (hexp : (∑ t, sz t) + ∑ j, cl2 j = n - π.Gsb.order)
    (hg : π.gsk ≤ (∑ t, g t) + ∑ j, gj j) (hb : π.bsk ≤ ∑ j, nj j) (hh : Fintype.card J ≤ π.Cs.hinges.card)
    (hJ : Fintype.card J ≤ π.Gsb.order) (val : ℂ)
    (hval : val = ∑ i, sgn i * ∑' ξ : ∀ t, (fam i).Λ t, (((∏ t, (fam i).w t (ξ t) : ℝ)) : ℂ) *
        outerValMμD π.Gsb P.L P.γ P.δ base roots tt Dom π.Cs.hinges
          (fun z => pieceAtomW π (cosetDecoration π.Gsb P.L base z.1) * (if selSk z then 1 else 0)) hS
          (fixMeasure π.fix)
          (fun t => (fam i).a t (ξ t)) (fun t => (fam i).m t (ξ t)) route hclk hmom (HkM i)) :
    π.RepresentsIntMK n cP tt base roots s val := by
  -- as in main, `‖sgn i‖ ≤ 1` is not needed: the mass bound carries the factors `‖sgn i‖`
  have _ := hsgn
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one hL1
  obtain ⟨hCge, -⟩ := Cchi_spec hd1
  have hb1 : (1 : ℝ) ≤ nodeBallCard P.d := by exact_mod_cast nodeBallCard_pos P.d
  have hC1 : 0 ≤ P.C₁ := by
    have : 1 ≤ Cchi P.d * (nodeBallCard P.d : ℝ) * (9 * K) ^ 2 * Ch := by
      have h1 := one_le_mul_of_one_le_of_one_le hCge hb1
      have h2 : 1 ≤ (9 * K) ^ 2 := by nlinarith
      exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 h2) hCh
    linarith
  have hx0 : 0 ≤ x := by
    rw [hx]
    exact mul_nonneg hC1 (Real.sqrt_nonneg _)
  have hbr : Fintype.card (GBranch π.Gsb.tree) = π.Gsb.order := WaveTurbulence.Mole.card_gbranch π.Gsb.tree
  have hslotsc : Fintype.card (ReplacementSlot π.Gsb) = 2 * π.Gsb.order + R := by
    have hpairs := sourcePair_card_twice π.Gsb hS
    unfold ReplacementSlot
    rw [Fintype.card_sum, hbr]
    omega
  have hord : ∑ j, (π.Gsb.tree j).order = π.Gsb.order := rfl
  set T : ℝ := x ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
    P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ)) with hT
  have hT0 : 0 ≤ T := by
    have := Real.rpow_nonneg hL0.le (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) +
      P.η ^ 7 * (π.Cs.hinges.card : ℝ))
    positivity
  have hs0 : 0 ≤ s := le_trans (Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _)
    (mul_nonneg (Finset.prod_nonneg fun t _ => hlf i t) (Finset.prod_nonneg fun j _ => hlfj i j))) hs
  have hLc : 1 ≤ P.L ^ (cP * P.d * (π.nProt : ℝ)) := Real.one_le_rpow hL1 (by positivity)
  rw [hval]
  have hKh0 : ∀ i, 0 ≤ ∏ j, (Ch * M0 i j) := fun i =>
    Finset.prod_nonneg fun j _ => mul_nonneg (by linarith) (hM i j).1
  refine RepIntCMK.toRepresentsIntMK (repIntCMK_vine_modesD hd1 hL0 π hS tt base roots selSk hgsp Dom hD hμD hsliceD
    hfilt hind route hroute hclk hmom src src_dart src_root sgn fam μs HkM hc hc1 hcθ hμ (fun i => ∏ j, (Ch * M0 i j))
    hKh0 hhinge (fun i => T * ((∏ t, lf i t) * ∏ j, lfj i j))
    (fun i => mul_nonneg hT0 (mul_nonneg (Finset.prod_nonneg fun t _ => hlf i t)
      (Finset.prod_nonneg fun j _ => hlfj i j))) ?_) n cP s ?_
  · intro i
    have hne : ∀ t, μs i t ≠ ⊤ := fun t => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hμb i t)
    have hμr : ∀ t, 0 ≤ (μs i t).toReal ∧ (μs i t).toReal ≤ K * x ^ (sz t) *
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
      (fun t => (μs i t).toReal) sz g (lf i) (hlf i) hμr (M0 i) cl2 gj nj (lfj i) (hlfj i) (hM i)
      n π.Gsb.order π.gsk π.bsk π.Cs.hinges.card hexp rfl hg hb hh
    have hmu : ∏ t, (9 * μs i t) = ENNReal.ofReal (9 ^ (2 * π.Gsb.order + R) * ∏ t, (μs i t).toReal) := by
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
    calc _ = Cchi P.d ^ π.Gsb.order * (9 ^ (2 * π.Gsb.order + R) * ∏ t, (μs i t).toReal) *
          (nodeBallCard P.d : ℝ) ^ π.Gsb.order * ∏ j, (Ch * M0 i j) := by
          push_cast; ring
      _ ≤ _ := hreal
      _ = _ := by simp only [hT]
  · calc ∑ i, ‖sgn i‖ * (T * ((∏ t, lf i t) * ∏ j, lfj i j))
        = T * ∑ i, ‖sgn i‖ * ((∏ t, lf i t) * ∏ j, lfj i j) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ T * s := mul_le_mul_of_nonneg_left hs hT0
      _ ≤ T * P.L ^ (cP * P.d * (π.nProt : ℝ)) * s :=
          mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hT0 hLc) hs0
      _ = repBoundMK P π n cP s := by simp only [hT, repBoundMK, hx]

end WaveTurbulence.Flower.MkSlotsB
