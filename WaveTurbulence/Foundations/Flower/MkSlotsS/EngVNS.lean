/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsS.EngRepS

/-! # B3s-HELPER4 (δ) S1: the selected engine (domain-generic)

**`representsIntMKSel_of_vineModesFixD`**: the twin of B3s's `MkSlots.representsIntMK_of_vineModesFix`
(`MkSlots/EngVN.lean`) with
* (i) the per-mode outer forms `outerValMμD … Dom …` on an arbitrary time domain `Dom` that agrees with the pinned
  kernel domain `fixLB π.Gsb π.layer tt π.fix π.lb = splicedTimeDomainFix … ∩ splicedLBDomain π.lb` (the pinned domain
  with the lower bounds of ruling R187) on time vectors extending the free times by the pins (`hsliceD`; with
  `Dom = splicedTimeDomain` and `π.lb = none` it is B3s's `hslice`), the hinge expansions on `Dom` (`HHkPropD`);
* (ii) the conclusion D7's `RepresentsIntMKSel π sel n cP tt base roots s val` for a finset `sel` of atoms of
  `G_sb` that are not unit clocks (`hselclk`): the moments `∏_{v∈sel}(1+|ξ_v|)^{1/18}` of the kernel frequencies are
  paid by the slots adjacent to `v` (per-slot time weights `θs s ≥ 2c + Σ_i selE s i`, as U1's `ModesMomentSel`),
  at the extra per-slot constant `selF s ∈ {1, 3}` carried by the slot losses in `hs`, and the loss
  `L^{7(47d+2)·#sel}` of `RepresentsIntMKSel` is the room for the stronger slot weights (`hs`).
  (Pinning or filters of the atoms of `sel` are not needed by the engine.)

* `representsIntMK_of_vineModesFix'`: at `sel = ∅`, `Dom = splicedTimeDomain`, `θs ≡ θ`, `π.lb = none` the hypotheses
  are B3s's (pre-R187 form) and the conclusion is B3s's (`representsIntMKSel_empty`): the α engine is recovered;
* `repMK_of_rep`: from the same data, plain `π.RepresentsIntMK n (cP + 343) tt base roots (b ^ N) val` when
  `s ≤ b^N` and `L^{7(47d+2)·#sel} ≤ L^{343·d·nProt}` (`Stage1MKGate.ClassPieceOK.repMK`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.Induct WaveTurbulence.LGSpine WaveTurbulence.Represents
  WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton TTree
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.MkSlots
open scoped ENNReal

namespace WaveTurbulence.Flower.MkSlotsS

/-- The order/gain part of the `RepresentsIntMK` bound. -/
def repCoreMK (P : WTParams) {R : ℕ} (π : Stage1PieceMK P.d R) (n : ℕ) : ℝ :=
  (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
    P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ))

open scoped Classical in
/-- **The core of the selected engine**: a `RepIntCMKS` of mass `repCoreMK · L^{7(47d+2)·#sel} · s`. -/
theorem repIntCMKS_of_vineModesFixD {P : WTParams} {R : ℕ} (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L) (hη0 : 0 ≤ P.η)
    (π : Stage1PieceMK P.d R) (hS : π.Gsb.IsPlain) (tt : Fin (2 * R) → ℝ) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (selSk : GenDecoration π.Gsb P.d roots 0 → Prop)
    (hgsp : ∀ D' : SplicedKernelData π.Gsb P.d, D'.gapSpecification = π.gapSpecification →
      ∀ z : GenDecoration π.Gsb P.d roots 0,
        splicedGapIndicator π.Gsb D' P.L P.γ P.η base z.1 = if selSk z then 1 else 0)
    (Dom : Set (GBranch π.Gsb.tree → ℝ))
    (hsliceD : ∀ τ : {b : GBranch π.Gsb.tree // π.fix b = none} → ℝ,
      π.Gsb.extendFix π.fix τ ∈ Dom ↔ π.Gsb.extendFix π.fix τ ∈ fixLB π.Gsb π.layer tt π.fix π.lb)
    (hfilt : ∀ a q, π.filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) (hind : ∀ k, 0 ≤ π.ind k ∧ π.ind k ≤ 1)
    {J : Type} [Fintype J] [DecidableEq J]
    (route : ReplacementSlot π.Gsb → Fin 2 → ClkSrc π.Gsb ⊕ J)
    (hroute : ∀ s i, route s i = Sum.inl (argSrc hS s i) ∨ ∃ j, route s i = Sum.inr j)
    (hclk : J → Fin 3 → ClkSrc π.Gsb) (hmom : J → Fin 4 → GNode π.Gsb.tree)
    (src : J → Fin 4 → HingeDarts π.Gsb π.Cs.hinges ⊕ Fin (2 * R))
    (src_dart : ∀ j i x, src j i = Sum.inl x → ∀ z : GenDecoration π.Gsb P.d roots 0,
      bondIndex π.Gsb z.1 x.1 = z.1 (hmom j i))
    (src_root : ∀ j i r, src j i = Sum.inr r → ∀ z : GenDecoration π.Gsb P.d roots 0, z.1 (hmom j i) = roots r)
    (sel : Finset (GBranch π.Gsb.tree)) (hselclk : ∀ v ∈ sel, ∀ j i, hclk j i ≠ Sum.inr v)
    {I : Type} [Fintype I] (sgn : I → ℂ)
    (fam : I → SlotFam π.Gsb P.d) (μs : I → ReplacementSlot π.Gsb → ℝ≥0∞)
    (HkM : I → J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (θs : ReplacementSlot π.Gsb → ℝ) (hcθ : ∀ s, 2 * c + (selE route sel s 0 + selE route sel s 1) ≤ θs s)
    (hμ : ∀ i s, ∑' l, maxBracketPow (θs s) (half ((fam i).m s l)) * ENNReal.ofReal ((fam i).w s l) ≤ μs i s)
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
      HHkPropD π.toStage1PieceD tt base roots selSk Dom hclk hmom
        (fun j => HkM i j (modLam (fun s => (fam i).m s (ξ s)) route j)) H ∧
      ∏ j, Mh j ≤ (∏ j, (Ch * M0 i j)) *
        ∏ j, (1 + |((modLam (fun s => (fam i).m s (ξ s)) route j : ℤ) : ℝ)|) ^ c)
    (n : ℕ) (s : ℝ)
    (hs : ∑ i, ‖sgn i‖ * ((∏ t, selF route sel t * lf i t) * ∏ j, lfj i j) ≤
      P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) * s)
    (hexp : (∑ t, sz t) + ∑ j, cl2 j = n - π.Gsb.order)
    (hg : π.gsk ≤ (∑ t, g t) + ∑ j, gj j) (hb : π.bsk ≤ ∑ j, nj j) (hh : Fintype.card J ≤ π.Cs.hinges.card)
    (hJ : Fintype.card J ≤ π.Gsb.order) (val : ℂ)
    (hval : val = ∑ i, sgn i * ∑' ξ : ∀ t, (fam i).Λ t, (((∏ t, (fam i).w t (ξ t) : ℝ)) : ℂ) *
        outerValMμD π.Gsb P.L P.γ P.δ base roots tt Dom π.Cs.hinges
          (fun z => pieceAtomW π (cosetDecoration π.Gsb P.L base z.1) * (if selSk z then 1 else 0)) hS
          (fixMeasure π.fix)
          (fun t => (fam i).a t (ξ t)) (fun t => (fam i).m t (ξ t)) route hclk hmom (HkM i)) :
    RepIntCMKS π sel tt base roots val (repCoreMK P π n * (P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) * s)) := by
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
  set T : ℝ := repCoreMK P π n with hT
  have hT0 : 0 ≤ T := by
    have := Real.rpow_nonneg hL0.le (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) +
      P.η ^ 7 * (π.Cs.hinges.card : ℝ))
    simp only [hT, repCoreMK]
    positivity
  rw [hval]
  have hKh0 : ∀ i, 0 ≤ ∏ j, (Ch * M0 i j) := fun i =>
    Finset.prod_nonneg fun j _ => mul_nonneg (by linarith) (hM i j).1
  have hlf' : ∀ i t, 0 ≤ selF route sel t * lf i t := fun i t => mul_nonneg (selF_nonneg route sel t) (hlf i t)
  refine (repIntCMKS_vine_modes hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD hfilt hind route hroute hclk
    hmom src src_dart src_root sel hselclk sgn fam μs HkM hc hc1 θs hcθ hμ (fun i => ∏ j, (Ch * M0 i j)) hKh0
    hhinge (fun i => T * ((∏ t, selF route sel t * lf i t) * ∏ j, lfj i j))
    (fun i => mul_nonneg hT0 (mul_nonneg (Finset.prod_nonneg fun t _ => hlf' i t)
      (Finset.prod_nonneg fun j _ => hlfj i j))) ?_).mono ?_
  · intro i
    have hne : ∀ t, μs i t ≠ ⊤ := fun t => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hμb i t)
    have hμr : ∀ t, 0 ≤ selF route sel t * (μs i t).toReal ∧ selF route sel t * (μs i t).toReal ≤ K * x ^ (sz t) *
        P.L ^ (-(P.η ^ 8) * (g t : ℝ)) * (selF route sel t * lf i t) := fun t => by
      have h0 : (μs i t).toReal ≤ K * x ^ (sz t) * P.L ^ (-(P.η ^ 8) * (g t : ℝ)) * lf i t :=
        ENNReal.toReal_le_of_le_ofReal (by
          have := hlf i t
          have : 0 ≤ P.L ^ (-(P.η ^ 8) * (g t : ℝ)) := Real.rpow_nonneg hL0.le _
          have : 0 ≤ x ^ (sz t) := pow_nonneg hx0 _
          have : 0 ≤ K := by linarith
          positivity) (hμb i t)
      have hF := selF_nonneg route sel t
      refine ⟨mul_nonneg hF ENNReal.toReal_nonneg, ?_⟩
      calc selF route sel t * (μs i t).toReal
          ≤ selF route sel t * (K * x ^ (sz t) * P.L ^ (-(P.η ^ 8) * (g t : ℝ)) * lf i t) :=
            mul_le_mul_of_nonneg_left h0 hF
        _ = _ := by ring
    have hreal := vine_mass_le_repBound (nsb := π.Gsb.order) (R := R)
      (ιs := ReplacementSlot π.Gsb) (ιj := J) hslotsc hJ x P.L K (Cchi P.d) (nodeBallCard P.d : ℝ) Ch P.C₁
      (P.η ^ 8) (P.η ^ 2 / 2) (P.η ^ 7) hx0 hL1 hK hCge hb1 hCh hC (by positivity) (by positivity) (by positivity)
      (fun t => selF route sel t * (μs i t).toReal) sz g (fun t => selF route sel t * lf i t) (hlf' i) hμr
      (M0 i) cl2 gj nj (lfj i) (hlfj i) (hM i)
      n π.Gsb.order π.gsk π.bsk π.Cs.hinges.card hexp rfl hg hb hh
    have ht : ∀ t, ENNReal.ofReal (9 * selF route sel t) * μs i t =
        ENNReal.ofReal (9 * (selF route sel t * (μs i t).toReal)) := fun t => by
      have hF := selF_nonneg route sel t
      rw [← mul_assoc, ENNReal.ofReal_mul (p := 9 * selF route sel t) (q := (μs i t).toReal) (by positivity),
        ENNReal.ofReal_toReal (hne t)]
    have hmu : ∏ t, (ENNReal.ofReal (9 * selF route sel t) * μs i t) =
        ENNReal.ofReal (9 ^ (2 * π.Gsb.order + R) * ∏ t, (selF route sel t * (μs i t).toReal)) := by
      rw [Finset.prod_congr rfl fun t _ => ht t, ← ENNReal.ofReal_prod_of_nonneg
        (fun t _ => mul_nonneg (by norm_num) (mul_nonneg (selF_nonneg route sel t) ENNReal.toReal_nonneg)),
        Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hslotsc]
    rw [hmu, hbr, hord, ← ENNReal.ofReal_mul (by
      have := hKh0 i; have := Cchi_spec hd1; positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hCχ0 : 0 ≤ Cchi P.d := by linarith
    calc _ = Cchi P.d ^ π.Gsb.order * (9 ^ (2 * π.Gsb.order + R) *
            ∏ t, (selF route sel t * (μs i t).toReal)) *
          (nodeBallCard P.d : ℝ) ^ π.Gsb.order * ∏ j, (Ch * M0 i j) := by
          push_cast; ring
      _ ≤ _ := hreal
      _ = _ := by simp only [hT, repCoreMK, hx]
  · calc ∑ i, ‖sgn i‖ * (T * ((∏ t, selF route sel t * lf i t) * ∏ j, lfj i j))
        = T * ∑ i, ‖sgn i‖ * ((∏ t, selF route sel t * lf i t) * ∏ j, lfj i j) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ T * (P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) * s) := mul_le_mul_of_nonneg_left hs hT0

/-- The selected bound in the form of `RepresentsIntMKSel`. -/
theorem repCoreMK_le_repBoundSel (P : WTParams) {R : ℕ} (π : Stage1PieceMK P.d R) (a n : ℕ) (cP s : ℝ)
    (hL1 : 1 ≤ P.L) (hcP : 0 ≤ cP) (hT0 : 0 ≤ repCoreMK P π n)
    (hs0 : 0 ≤ P.L ^ (7 * (47 * P.d + 2) * (a : ℝ)) * s) :
    repCoreMK P π n * (P.L ^ (7 * (47 * P.d + 2) * (a : ℝ)) * s) ≤ repBoundSel P π a n cP s := by
  have hLc : 1 ≤ P.L ^ (cP * P.d * (π.nProt : ℝ)) := Real.one_le_rpow hL1 (by positivity)
  calc repCoreMK P π n * (P.L ^ (7 * (47 * P.d + 2) * (a : ℝ)) * s)
      ≤ repCoreMK P π n * P.L ^ (cP * P.d * (π.nProt : ℝ)) * (P.L ^ (7 * (47 * P.d + 2) * (a : ℝ)) * s) :=
        mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hT0 hLc) hs0
    _ = repBoundSel P π a n cP s := by simp only [repCoreMK, repBoundSel]; ring

theorem repCoreMK_nonneg {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R) (n : ℕ) (hL1 : 1 ≤ P.L)
    (hC1 : 0 ≤ P.C₁) : 0 ≤ repCoreMK P π n := by
  have := Real.rpow_nonneg (zero_le_one.trans hL1) (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) +
      P.η ^ 7 * (π.Cs.hinges.card : ℝ))
  unfold repCoreMK
  positivity

/-- The numeric hypothesis forces `C₁ ≥ 0`. -/
theorem C₁_nonneg_of_hC {P : WTParams} (hd1 : 1 ≤ P.d) {K Ch : ℝ} (hK : 1 ≤ K) (hCh : 1 ≤ Ch)
    (hC : Cchi P.d * (nodeBallCard P.d : ℝ) * (9 * K) ^ 2 * Ch ≤ P.C₁) : 0 ≤ P.C₁ := by
  obtain ⟨hCge, -⟩ := Cchi_spec hd1
  have hb1 : (1 : ℝ) ≤ nodeBallCard P.d := by exact_mod_cast nodeBallCard_pos P.d
  have : 1 ≤ Cchi P.d * (nodeBallCard P.d : ℝ) * (9 * K) ^ 2 * Ch := by
    have h1 := one_le_mul_of_one_le_of_one_le hCge hb1
    have h2 : 1 ≤ (9 * K) ^ 2 := by nlinarith
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 h2) hCh
  linarith

open scoped Classical in
/-- **S1: the selected engine** (`RepresentsIntMKSel` of a pinned vine piece on a time domain `Dom`, from the mode
form; see the module docstring). -/
theorem representsIntMKSel_of_vineModesFixD {P : WTParams} {R : ℕ} (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L)
    (hη0 : 0 ≤ P.η)
    (π : Stage1PieceMK P.d R) (hS : π.Gsb.IsPlain) (tt : Fin (2 * R) → ℝ) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (selSk : GenDecoration π.Gsb P.d roots 0 → Prop)
    (hgsp : ∀ D' : SplicedKernelData π.Gsb P.d, D'.gapSpecification = π.gapSpecification →
      ∀ z : GenDecoration π.Gsb P.d roots 0,
        splicedGapIndicator π.Gsb D' P.L P.γ P.η base z.1 = if selSk z then 1 else 0)
    (Dom : Set (GBranch π.Gsb.tree → ℝ))
    (hsliceD : ∀ τ : {b : GBranch π.Gsb.tree // π.fix b = none} → ℝ,
      π.Gsb.extendFix π.fix τ ∈ Dom ↔ π.Gsb.extendFix π.fix τ ∈ fixLB π.Gsb π.layer tt π.fix π.lb)
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
    (sel : Finset (GBranch π.Gsb.tree)) (hselclk : ∀ v ∈ sel, ∀ j i, hclk j i ≠ Sum.inr v)
    {I : Type} [Fintype I] (sgn : I → ℂ)
    (fam : I → SlotFam π.Gsb P.d) (μs : I → ReplacementSlot π.Gsb → ℝ≥0∞)
    (HkM : I → J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (θs : ReplacementSlot π.Gsb → ℝ) (hcθ : ∀ s, 2 * c + (selE route sel s 0 + selE route sel s 1) ≤ θs s)
    (hμ : ∀ i s, ∑' l, maxBracketPow (θs s) (half ((fam i).m s l)) * ENNReal.ofReal ((fam i).w s l) ≤ μs i s)
    (x K Ch : ℝ) (hx : x = P.C₁ * Real.sqrt P.δ) (hK : 1 ≤ K) (hCh : 1 ≤ Ch)
    (hC : Cchi P.d * (nodeBallCard P.d : ℝ) * (9 * K) ^ 2 * Ch ≤ P.C₁)
    (sz g : ReplacementSlot π.Gsb → ℕ) (lf : I → ReplacementSlot π.Gsb → ℝ) (hlf : ∀ i s, 0 ≤ lf i s)
    (hμb : ∀ i s, μs i s ≤ ENNReal.ofReal (K * x ^ (sz s) * P.L ^ (-(P.η ^ 8) * (g s : ℝ)) * lf i s))
    (M0 : I → J → ℝ) (cl2 gj nj : J → ℕ) (lfj : I → J → ℝ) (hlfj : ∀ i j, 0 ≤ lfj i j)
    (hM : ∀ i j, 0 ≤ M0 i j ∧ M0 i j ≤ x ^ (cl2 j) *
      P.L ^ (-(P.η ^ 8) * (gj j : ℝ) - P.η ^ 2 / 2 * (nj j : ℝ) + P.η ^ 7) * lfj i j)
    (hhinge : ∀ i (ξ : ∀ s, (fam i).Λ s), ∃ (H : HingeFam J P.d) (Mh : J → ℝ),
      (∀ j c', ∑' l, H.w j c' l ≤ Mh j) ∧
      HHkPropD π.toStage1PieceD tt base roots selSk Dom hclk hmom
        (fun j => HkM i j (modLam (fun s => (fam i).m s (ξ s)) route j)) H ∧
      ∏ j, Mh j ≤ (∏ j, (Ch * M0 i j)) *
        ∏ j, (1 + |((modLam (fun s => (fam i).m s (ξ s)) route j : ℤ) : ℝ)|) ^ c)
    (n : ℕ) (s : ℝ)
    (hs : ∑ i, ‖sgn i‖ * ((∏ t, selF route sel t * lf i t) * ∏ j, lfj i j) ≤
      P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) * s)
    (hexp : (∑ t, sz t) + ∑ j, cl2 j = n - π.Gsb.order)
    (hg : π.gsk ≤ (∑ t, g t) + ∑ j, gj j) (hb : π.bsk ≤ ∑ j, nj j) (hh : Fintype.card J ≤ π.Cs.hinges.card)
    (hJ : Fintype.card J ≤ π.Gsb.order) (val : ℂ)
    (hval : val = ∑ i, sgn i * ∑' ξ : ∀ t, (fam i).Λ t, (((∏ t, (fam i).w t (ξ t) : ℝ)) : ℂ) *
        outerValMμD π.Gsb P.L P.γ P.δ base roots tt Dom π.Cs.hinges
          (fun z => pieceAtomW π (cosetDecoration π.Gsb P.L base z.1) * (if selSk z then 1 else 0)) hS
          (fixMeasure π.fix)
          (fun t => (fam i).a t (ξ t)) (fun t => (fam i).m t (ξ t)) route hclk hmom (HkM i)) :
    RepresentsIntMKSel π sel n cP tt base roots s val := by
  have h := repIntCMKS_of_vineModesFixD hd1 hL1 hη0 π hS tt base roots selSk hgsp Dom hsliceD hfilt hind route
    hroute hclk hmom src src_dart src_root sel hselclk sgn fam μs HkM hc hc1 θs hcθ hμ x K Ch hx hK hCh hC sz g lf
    hlf hμb M0 cl2 gj nj lfj hlfj hM hhinge n s hs hexp hg hb hh hJ val hval
  refine h.toRepresentsIntMKSel n cP s (repCoreMK_le_repBoundSel P π sel.card n cP s hL1 hcP
    (repCoreMK_nonneg π n hL1 (C₁_nonneg_of_hC hd1 hK hCh hC)) ?_)
  exact le_trans (Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (mul_nonneg
    (Finset.prod_nonneg fun t _ => mul_nonneg (selF_nonneg route sel t) (hlf i t))
    (Finset.prod_nonneg fun j _ => hlfj i j))) hs

open scoped Classical in
/-- **`repMK`**: from the same data, plain `RepresentsIntMK` at `cP + 343` and mass `b^N`, when `s ≤ b^N` and
`L^{7(47d+2)·#sel} ≤ L^{343·d·nProt}` (Hyp.lean's `ClassPieceOK.repMK`: the representation is a count-measure
superposition, so the weight is summable). -/
theorem repMK_of_rep {P : WTParams} {R : ℕ} (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L)
    (hη0 : 0 ≤ P.η)
    (π : Stage1PieceMK P.d R) (hS : π.Gsb.IsPlain) (tt : Fin (2 * R) → ℝ) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (selSk : GenDecoration π.Gsb P.d roots 0 → Prop)
    (hgsp : ∀ D' : SplicedKernelData π.Gsb P.d, D'.gapSpecification = π.gapSpecification →
      ∀ z : GenDecoration π.Gsb P.d roots 0,
        splicedGapIndicator π.Gsb D' P.L P.γ P.η base z.1 = if selSk z then 1 else 0)
    (Dom : Set (GBranch π.Gsb.tree → ℝ))
    (hsliceD : ∀ τ : {b : GBranch π.Gsb.tree // π.fix b = none} → ℝ,
      π.Gsb.extendFix π.fix τ ∈ Dom ↔ π.Gsb.extendFix π.fix τ ∈ fixLB π.Gsb π.layer tt π.fix π.lb)
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
    (sel : Finset (GBranch π.Gsb.tree)) (hselclk : ∀ v ∈ sel, ∀ j i, hclk j i ≠ Sum.inr v)
    {I : Type} [Fintype I] (sgn : I → ℂ)
    (fam : I → SlotFam π.Gsb P.d) (μs : I → ReplacementSlot π.Gsb → ℝ≥0∞)
    (HkM : I → J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (θs : ReplacementSlot π.Gsb → ℝ) (hcθ : ∀ s, 2 * c + (selE route sel s 0 + selE route sel s 1) ≤ θs s)
    (hμ : ∀ i s, ∑' l, maxBracketPow (θs s) (half ((fam i).m s l)) * ENNReal.ofReal ((fam i).w s l) ≤ μs i s)
    (x K Ch : ℝ) (hx : x = P.C₁ * Real.sqrt P.δ) (hK : 1 ≤ K) (hCh : 1 ≤ Ch)
    (hC : Cchi P.d * (nodeBallCard P.d : ℝ) * (9 * K) ^ 2 * Ch ≤ P.C₁)
    (sz g : ReplacementSlot π.Gsb → ℕ) (lf : I → ReplacementSlot π.Gsb → ℝ) (hlf : ∀ i s, 0 ≤ lf i s)
    (hμb : ∀ i s, μs i s ≤ ENNReal.ofReal (K * x ^ (sz s) * P.L ^ (-(P.η ^ 8) * (g s : ℝ)) * lf i s))
    (M0 : I → J → ℝ) (cl2 gj nj : J → ℕ) (lfj : I → J → ℝ) (hlfj : ∀ i j, 0 ≤ lfj i j)
    (hM : ∀ i j, 0 ≤ M0 i j ∧ M0 i j ≤ x ^ (cl2 j) *
      P.L ^ (-(P.η ^ 8) * (gj j : ℝ) - P.η ^ 2 / 2 * (nj j : ℝ) + P.η ^ 7) * lfj i j)
    (hhinge : ∀ i (ξ : ∀ s, (fam i).Λ s), ∃ (H : HingeFam J P.d) (Mh : J → ℝ),
      (∀ j c', ∑' l, H.w j c' l ≤ Mh j) ∧
      HHkPropD π.toStage1PieceD tt base roots selSk Dom hclk hmom
        (fun j => HkM i j (modLam (fun s => (fam i).m s (ξ s)) route j)) H ∧
      ∏ j, Mh j ≤ (∏ j, (Ch * M0 i j)) *
        ∏ j, (1 + |((modLam (fun s => (fam i).m s (ξ s)) route j : ℤ) : ℝ)|) ^ c)
    (n : ℕ) (s : ℝ)
    (hs : ∑ i, ‖sgn i‖ * ((∏ t, selF route sel t * lf i t) * ∏ j, lfj i j) ≤
      P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) * s)
    (hexp : (∑ t, sz t) + ∑ j, cl2 j = n - π.Gsb.order)
    (hg : π.gsk ≤ (∑ t, g t) + ∑ j, gj j) (hb : π.bsk ≤ ∑ j, nj j) (hh : Fintype.card J ≤ π.Cs.hinges.card)
    (hJ : Fintype.card J ≤ π.Gsb.order) (val : ℂ)
    (hval : val = ∑ i, sgn i * ∑' ξ : ∀ t, (fam i).Λ t, (((∏ t, (fam i).w t (ξ t) : ℝ)) : ℂ) *
        outerValMμD π.Gsb P.L P.γ P.δ base roots tt Dom π.Cs.hinges
          (fun z => pieceAtomW π (cosetDecoration π.Gsb P.L base z.1) * (if selSk z then 1 else 0)) hS
          (fixMeasure π.fix)
          (fun t => (fam i).a t (ξ t)) (fun t => (fam i).m t (ξ t)) route hclk hmom (HkM i))
    (bN : ℝ) (hsb : s ≤ bN)
    (hLsel : P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) ≤ P.L ^ ((343 : ℝ) * P.d * (π.nProt : ℝ))) :
    π.RepresentsIntMK n (cP + 343) tt base roots bN val := by
  have h := repIntCMKS_of_vineModesFixD hd1 hL1 hη0 π hS tt base roots selSk hgsp Dom hsliceD hfilt hind route
    hroute hclk hmom src src_dart src_root sel hselclk sgn fam μs HkM hc hc1 θs hcθ hμ x K Ch hx hK hCh hC sz g lf
    hlf hμb M0 cl2 gj nj lfj hlfj hM hhinge n s hs hexp hg hb hh hJ val hval
  refine h.toRepIntCMK.toRepresentsIntMK n (cP + 343) bN ?_
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one hL1
  have hT0 := repCoreMK_nonneg π n hL1 (C₁_nonneg_of_hC hd1 hK hCh hC)
  have hLs : 0 < P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) := Real.rpow_pos_of_pos hL0 _
  have hs0 : 0 ≤ s := by
    have h0 : 0 ≤ P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) * s :=
      le_trans (Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (mul_nonneg
        (Finset.prod_nonneg fun t _ => mul_nonneg (selF_nonneg route sel t) (hlf i t))
        (Finset.prod_nonneg fun j _ => hlfj i j))) hs
    exact nonneg_of_mul_nonneg_right (by linarith) hLs
  have hLc : 1 ≤ P.L ^ (cP * P.d * (π.nProt : ℝ)) := Real.one_le_rpow hL1 (by positivity)
  have hsplit : P.L ^ ((cP + 343) * P.d * (π.nProt : ℝ)) =
      P.L ^ (cP * P.d * (π.nProt : ℝ)) * P.L ^ ((343 : ℝ) * P.d * (π.nProt : ℝ)) := by
    rw [← Real.rpow_add hL0]; ring_nf
  have h343 : 0 ≤ P.L ^ ((343 : ℝ) * P.d * (π.nProt : ℝ)) := Real.rpow_nonneg hL0.le _
  calc repCoreMK P π n * (P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) * s)
      ≤ repCoreMK P π n * (P.L ^ ((343 : ℝ) * P.d * (π.nProt : ℝ)) * bN) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hLsel hsb hs0 h343) hT0
    _ ≤ repCoreMK P π n * (P.L ^ (cP * P.d * (π.nProt : ℝ)) *
          (P.L ^ ((343 : ℝ) * P.d * (π.nProt : ℝ)) * bN)) := by
        refine mul_le_mul_of_nonneg_left ?_ hT0
        exact le_mul_of_one_le_left (mul_nonneg h343 (hs0.trans hsb)) hLc
    _ = repBoundMK P π n (cP + 343) bN := by
        simp only [repCoreMK, repBoundMK, hsplit]; ring

open scoped Classical in
/-- **At `sel = ∅` the selected engine is B3s's engine**: with `Dom = splicedTimeDomain`, `θs ≡ θ`, no lower bounds
(`π.lb = none`) and B3s's hypotheses verbatim, the conclusion is B3s's `RepresentsIntMK` (via
`representsIntMKSel_empty`). -/
theorem representsIntMK_of_vineModesFix' {P : WTParams} {R : ℕ} (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L) (hη0 : 0 ≤ P.η)
    (π : Stage1PieceMK P.d R) (hS : π.Gsb.IsPlain) (tt : Fin (2 * R) → ℝ) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (selSk : GenDecoration π.Gsb P.d roots 0 → Prop)
    (hgsp : ∀ D' : SplicedKernelData π.Gsb P.d, D'.gapSpecification = π.gapSpecification →
      ∀ z : GenDecoration π.Gsb P.d roots 0,
        splicedGapIndicator π.Gsb D' P.L P.γ P.η base z.1 = if selSk z then 1 else 0)
    (hslice : ∀ τ : {b : GBranch π.Gsb.tree // π.fix b = none} → ℝ,
      π.Gsb.extendFix π.fix τ ∈ splicedTimeDomain π.Gsb π.layer tt ↔
        π.Gsb.extendFix π.fix τ ∈ splicedTimeDomainFix π.Gsb π.layer tt π.fix)
    (hlb : π.lb = fun _ => none)
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
    {I : Type} [Fintype I] (sgn : I → ℂ)
    (fam : I → SlotFam π.Gsb P.d) (μs : I → ReplacementSlot π.Gsb → ℝ≥0∞)
    (HkM : I → J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ) {c θ : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hcθ : 2 * c ≤ θ)
    (hμ : ∀ i s, ∑' l, maxBracketPow θ (half ((fam i).m s l)) * ENNReal.ofReal ((fam i).w s l) ≤ μs i s)
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
      ∏ j, Mh j ≤ (∏ j, (Ch * M0 i j)) *
        ∏ j, (1 + |((modLam (fun s => (fam i).m s (ξ s)) route j : ℤ) : ℝ)|) ^ c)
    (n : ℕ) (s : ℝ) (hs : ∑ i, ‖sgn i‖ * ((∏ t, lf i t) * ∏ j, lfj i j) ≤ s)
    (hexp : (∑ t, sz t) + ∑ j, cl2 j = n - π.Gsb.order)
    (hg : π.gsk ≤ (∑ t, g t) + ∑ j, gj j) (hb : π.bsk ≤ ∑ j, nj j) (hh : Fintype.card J ≤ π.Cs.hinges.card)
    (hJ : Fintype.card J ≤ π.Gsb.order) (val : ℂ)
    (hval : val = ∑ i, sgn i * ∑' ξ : ∀ t, (fam i).Λ t, (((∏ t, (fam i).w t (ξ t) : ℝ)) : ℂ) *
        outerValMμ π.Gsb P.L P.γ P.δ base roots tt π.layer π.Cs.hinges
          (fun z => pieceAtomW π (cosetDecoration π.Gsb P.L base z.1) * (if selSk z then 1 else 0)) hS
          (fixMeasure π.fix)
          (fun t => (fam i).a t (ξ t)) (fun t => (fam i).m t (ξ t)) route hclk hmom (HkM i)) :
    π.RepresentsIntMK n cP tt base roots s val := by
  refine (representsIntMKSel_empty π n cP tt base roots s val).1 ?_
  refine representsIntMKSel_of_vineModesFixD hd1 hL1 hη0 π hS tt base roots selSk hgsp
    (splicedTimeDomain π.Gsb π.layer tt) (fun τ => by rw [hlb, fixLB_none]; exact hslice τ) hfilt hind cP hcP
    route hroute hclk hmom src src_dart src_root ∅
    (fun v hv => absurd hv (Finset.notMem_empty v)) sgn fam μs HkM hc hc1 (fun _ => θ) (fun s => by simpa using hcθ)
    hμ x K Ch hx hK hCh hC sz g lf hlf hμb M0 cl2 gj nj lfj hlfj hM hhinge n s ?_ hexp hg hb hh hJ val hval
  simpa using hs

end WaveTurbulence.Flower.MkSlotsS
