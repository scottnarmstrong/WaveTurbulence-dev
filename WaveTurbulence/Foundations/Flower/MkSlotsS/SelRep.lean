/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsS.EngBase
public import WaveTurbulence.Foundations.Flower.FinalMKDefs.PieceSel

/-! # B3s-HELPER4 (δ) S1 (1): count-measure representations with selection moments

`RepIntCMKS π sel tt base roots val B`: the count-measure form of D7's `RepresentsIntMKSel` (world
`FinalMKDefs/PieceSel.lean`), i.e. B3s's `MkSlots.RepIntCMK` whose mass is weighted by the selection moment
`momS sel (freq ξ) = ∏_{v ∈ sel} (1 + |freq ξ v|)^{1/18}` of the kernel frequencies.

* `momS`, `one_le_momS`, `momS_empty`;
* `RepIntCMKS.toRepresentsIntMKSel` (count measure), `RepIntCMKS.toRepIntCMK` (the moment is `≥ 1`);
* closure: `mono`, `zero`, `smul`, `add`, `finset_sum`, `tsum` (as B3s's `RepIntCMK` closure, EngDefs.lean);
* `RepIntCMKS.of_freq_le`: a `RepIntCMK`-type representation whose frequencies have moment `≤ M` is a `RepIntCMKS` of
  mass `B·M`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.Induct WaveTurbulence.LGSpine WaveTurbulence.Represents
  WaveTurbulence.RepAnalytic
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.MkSlots
open scoped ENNReal

namespace WaveTurbulence.Flower.MkSlotsS

/-! ## The selection moment -/

/-- The selection moment `∏_{v ∈ sel} (1 + |f v|)^{1/18}` of a frequency vector `f`. -/
def momS {ι : Type*} (sel : Finset ι) (f : ι → ℝ) : ℝ := ∏ v ∈ sel, (1 + |f v|) ^ (1 / 18 : ℝ)

theorem one_le_momS {ι : Type*} (sel : Finset ι) (f : ι → ℝ) : 1 ≤ momS sel f :=
  Finset.one_le_prod₀ fun v _ => Real.one_le_rpow (by linarith [abs_nonneg (f v)]) (by norm_num)

theorem momS_nonneg {ι : Type*} (sel : Finset ι) (f : ι → ℝ) : 0 ≤ momS sel f :=
  zero_le_one.trans (one_le_momS sel f)

@[simp] theorem momS_empty {ι : Type*} (f : ι → ℝ) : momS (∅ : Finset ι) f = 1 := by simp [momS]

/-! ## The count-measure form -/

/-- The count-measure form of `RepresentsIntMKSel` with explicit moment-weighted mass bound `B`. -/
def RepIntCMKS {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R) (sel : Finset (GBranch π.Gsb.tree))
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (val : ℂ) (B : ℝ) : Prop :=
  ∃ (Ξ : Type) (_ : Countable Ξ) (w : Ξ → ℂ) (ctr : Ξ → GardenDart π.Gsb → Mom P.d)
    (edge : Ξ → GardenDart π.Gsb → Mom P.d → ℂ)
    (hinge : Ξ → (HingeDarts π.Gsb π.Cs.hinges → Mom P.d) → ℂ) (freq : Ξ → GBranch π.Gsb.tree → ℝ),
    Summable (fun ξ => ‖w ξ * splicedKernelMK π.Gsb (π.dataMK tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))
      P.L P.γ P.η P.δ base roots‖) ∧
    val = ∑' ξ, w ξ * splicedKernelMK π.Gsb (π.dataMK tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))
      P.L P.γ P.η P.δ base roots ∧
    Summable (fun ξ => ‖w ξ‖ * momS sel (freq ξ)) ∧ ∑' ξ, ‖w ξ‖ * momS sel (freq ξ) ≤ B ∧
    ∀ ξ, SplicedAmplitudeBounds π.Gsb (Stage1Piece.data π.toStage1PieceD tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))

/-- The bound of `RepresentsIntMKSel`. -/
def repBoundSel (P : WTParams) {R : ℕ} (π : Stage1PieceMK P.d R) (a n : ℕ) (cP s : ℝ) : ℝ :=
  (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
    P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ)) *
      P.L ^ (cP * P.d * (π.nProt : ℝ)) * P.L ^ (7 * (47 * P.d + 2) * (a : ℝ)) * s

section Basic

variable {P : WTParams} {R : ℕ} {π : Stage1PieceMK P.d R} {sel : Finset (GBranch π.Gsb.tree)}
  {tt : Fin (2 * R) → ℝ} {base : Mom P.d} {roots : Fin (2 * R) → (Fin P.d → ℤ)}

theorem RepIntCMKS.toRepresentsIntMKSel {val : ℂ} {B : ℝ} (h : RepIntCMKS π sel tt base roots val B) (n : ℕ)
    (cP s : ℝ) (hB : B ≤ repBoundSel P π sel.card n cP s) :
    RepresentsIntMKSel π sel n cP tt base roots s val := by
  obtain ⟨Ξ, hc, w, ctr, edge, hinge, freq, h1, h2, h3, h4, h5⟩ := h
  let _ : MeasurableSpace Ξ := ⊤
  have : MeasurableSingletonClass Ξ := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  obtain ⟨hint, hint2⟩ := integral_count_eq_tsum _ h1
  have h3' : Summable fun ξ => ‖‖w ξ‖ * momS sel (freq ξ)‖ :=
    h3.congr fun ξ => (Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (momS_nonneg _ _))).symm
  obtain ⟨hint', hint2'⟩ := integral_count_real_eq_tsum _ h3'
  refine ⟨Ξ, inferInstance, Measure.count, w, ctr, edge, hinge, freq, hint, ?_, hint', ?_, h5⟩
  · rw [hint2]; exact h2
  · show ∫ ξ, ‖w ξ‖ * momS sel (freq ξ) ∂Measure.count ≤ _
    rw [hint2']; exact h4.trans hB

/-- Forgetting the moments (`momS ≥ 1`). -/
theorem RepIntCMKS.toRepIntCMK {val : ℂ} {B : ℝ} (h : RepIntCMKS π sel tt base roots val B) :
    RepIntCMK π tt base roots val B := by
  obtain ⟨Ξ, hc, w, ctr, edge, hinge, freq, h1, h2, h3, h4, h5⟩ := h
  have hle : ∀ ξ, ‖w ξ‖ ≤ ‖w ξ‖ * momS sel (freq ξ) := fun ξ =>
    le_mul_of_one_le_right (norm_nonneg _) (one_le_momS _ _)
  have hs : Summable fun ξ => ‖w ξ‖ := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle h3
  exact ⟨Ξ, hc, w, ctr, edge, hinge, freq, h1, h2, hs, (Summable.tsum_le_tsum hle hs h3).trans h4, h5⟩

/-- At `sel = ∅`, the two count-measure forms agree. -/
theorem repIntCMKS_empty_iff {val : ℂ} {B : ℝ} :
    RepIntCMKS π ∅ tt base roots val B ↔ RepIntCMK π tt base roots val B := by
  simp [RepIntCMKS, RepIntCMK]

theorem RepIntCMKS.mono {val : ℂ} {B B' : ℝ} (h : RepIntCMKS π sel tt base roots val B) (hB : B ≤ B') :
    RepIntCMKS π sel tt base roots val B' := by
  obtain ⟨Ξ, hc, w, ctr, edge, hinge, freq, h1, h2, h3, h4, h5⟩ := h
  exact ⟨Ξ, hc, w, ctr, edge, hinge, freq, h1, h2, h3, h4.trans hB, h5⟩

theorem RepIntCMKS.zero {B : ℝ} (hB : 0 ≤ B) : RepIntCMKS π sel tt base roots 0 B := by
  refine ⟨Empty, inferInstance, fun e => e.elim, fun e => e.elim, fun e => e.elim, fun e => e.elim,
    fun e => e.elim, ?_, ?_, ?_, ?_, fun e => e.elim⟩
  · exact (hasSum_fintype _).summable
  · simp
  · exact (hasSum_fintype _).summable
  · simpa using hB

theorem RepIntCMKS.smul {val : ℂ} {B : ℝ} (h : RepIntCMKS π sel tt base roots val B) (c : ℂ) :
    RepIntCMKS π sel tt base roots (c * val) (‖c‖ * B) := by
  obtain ⟨Ξ, hcnt, w, ctr, edge, hinge, freq, h1, h2, h3, h4, h5⟩ := h
  refine ⟨Ξ, hcnt, fun ξ => c * w ξ, ctr, edge, hinge, freq, ?_, ?_, ?_, ?_, h5⟩
  · simp_rw [mul_assoc]
    refine (h1.mul_left ‖c‖).congr fun ξ => ?_
    simp only [norm_mul]
  · rw [h2, ← tsum_mul_left]; exact tsum_congr fun ξ => by ring
  · simp_rw [norm_mul, mul_assoc]; exact h3.mul_left _
  · simp_rw [norm_mul, mul_assoc]
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left h4 (norm_nonneg _)

theorem RepIntCMKS.add {v₁ v₂ : ℂ} {B₁ B₂ : ℝ} (h₁ : RepIntCMKS π sel tt base roots v₁ B₁)
    (h₂ : RepIntCMKS π sel tt base roots v₂ B₂) : RepIntCMKS π sel tt base roots (v₁ + v₂) (B₁ + B₂) := by
  obtain ⟨Ξ, hc, w, ctr, edge, hinge, freq, a1, a2, a3, a4, a5⟩ := h₁
  obtain ⟨Ξ', hc', w', ctr', edge', hinge', freq', b1, b2, b3, b4, b5⟩ := h₂
  refine ⟨Ξ ⊕ Ξ', inferInstance, Sum.elim w w', Sum.elim ctr ctr', Sum.elim edge edge',
    Sum.elim hinge hinge', Sum.elim freq freq', ?_, ?_, ?_, ?_, ?_⟩
  · exact Summable.sum _ a1 b1
  · rw [Summable.tsum_sum (f := fun ξ => (Sum.elim w w' ξ) * splicedKernelMK π.Gsb
      (π.dataMK tt (Sum.elim ctr ctr' ξ) (Sum.elim edge edge' ξ) (Sum.elim hinge hinge' ξ)
        (Sum.elim freq freq' ξ)) P.L P.γ P.η P.δ base roots) a1.of_norm b1.of_norm]
    rw [a2, b2]; rfl
  · exact Summable.sum (f := fun ξ => ‖Sum.elim w w' ξ‖ * momS sel (Sum.elim freq freq' ξ)) a3 b3
  · rw [Summable.tsum_sum (f := fun ξ => ‖Sum.elim w w' ξ‖ * momS sel (Sum.elim freq freq' ξ)) a3 b3]
    exact add_le_add a4 b4
  · rintro (ξ | ξ)
    · exact a5 ξ
    · exact b5 ξ

theorem RepIntCMKS.finset_sum {ι : Type*} (s : Finset ι) (val : ι → ℂ) (B : ι → ℝ) (hB : ∀ i ∈ s, 0 ≤ B i)
    (h : ∀ i ∈ s, RepIntCMKS π sel tt base roots (val i) (B i)) :
    RepIntCMKS π sel tt base roots (∑ i ∈ s, val i) (∑ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using RepIntCMKS.zero (π := π) (sel := sel) (tt := tt) (base := base) (roots := roots) le_rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add
      (ih (fun i hi => hB i (Finset.mem_insert_of_mem hi)) (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- **Countable sums** (copy of B3s's `RepIntCMK.tsum`, moments carried along). -/
theorem RepIntCMKS.tsum (hS : π.Gsb.IsPlain) (hL : 0 < P.L)
    (hfilt : ∀ a q, π.filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) (hind : ∀ k, 0 ≤ π.ind k ∧ π.ind k ≤ 1)
    {ι : Type} [Countable ι] (val : ι → ℂ) (B : ι → ℝ)
    (hBs : Summable B) (h : ∀ i, RepIntCMKS π sel tt base roots (val i) (B i)) :
    Summable val ∧ RepIntCMKS π sel tt base roots (∑' i, val i) (∑' i, B i) := by
  choose Ξ hc w ctr edge hinge freq a1 a2 a3 a4 a5 using h
  have : ∀ i, Countable (Ξ i) := hc
  have hK0 : 0 ≤ ‖(coupling P.d P.L P.γ P.δ : ℂ)‖ ^ π.Gsb.order *
      (2 * P.L + 1) ^ (P.d * π.Gsb.molecule.bonds.card) := by positivity
  have hkb : ∀ p : Σ i, Ξ i, ‖splicedKernelMK π.Gsb (π.dataMK tt (ctr p.1 p.2) (edge p.1 p.2) (hinge p.1 p.2)
      (freq p.1 p.2)) P.L P.γ P.η P.δ base roots‖ ≤ ‖(coupling P.d P.L P.γ P.δ : ℂ)‖ ^ π.Gsb.order *
      (2 * P.L + 1) ^ (P.d * π.Gsb.molecule.bonds.card) := fun p =>
    WaveTurbulence.Flower.SelRes.norm_kernel_le_trivial hS _ (a5 p.1 p.2) hfilt hind hL _ _ _ _ _
  generalize ‖(coupling P.d P.L P.γ P.δ : ℂ)‖ ^ π.Gsb.order *
      (2 * P.L + 1) ^ (P.d * π.Gsb.molecule.bonds.card) = K at hK0 hkb
  have hWMs : Summable fun p : Σ i, Ξ i => ‖w p.1 p.2‖ * momS sel (freq p.1 p.2) := by
    refine (summable_sigma_of_nonneg (fun _ => mul_nonneg (norm_nonneg _) (momS_nonneg _ _))).mpr
      ⟨fun i => a3 i, ?_⟩
    exact Summable.of_nonneg_of_le (fun i => tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (momS_nonneg _ _))
      a4 hBs
  have hle : ∀ p : Σ i, Ξ i, ‖w p.1 p.2‖ ≤ ‖w p.1 p.2‖ * momS sel (freq p.1 p.2) := fun p =>
    le_mul_of_one_le_right (norm_nonneg _) (one_le_momS _ _)
  have hWs : Summable fun p : Σ i, Ξ i => ‖w p.1 p.2‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hWMs
  have hWKs : Summable fun p : Σ i, Ξ i => ‖w p.1 p.2 * splicedKernelMK π.Gsb (π.dataMK tt (ctr p.1 p.2)
      (edge p.1 p.2) (hinge p.1 p.2) (freq p.1 p.2)) P.L P.γ P.η P.δ base roots‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) (hWs.mul_right K)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hkb p) (norm_nonneg _)
  have hsumval : ∑' p : Σ i, Ξ i, w p.1 p.2 * splicedKernelMK π.Gsb (π.dataMK tt (ctr p.1 p.2) (edge p.1 p.2)
      (hinge p.1 p.2) (freq p.1 p.2)) P.L P.γ P.η P.δ base roots = ∑' i, val i := by
    rw [hWKs.of_norm.tsum_sigma' (fun i => hWKs.of_norm.sigma_factor i)]
    exact tsum_congr fun i => (a2 i).symm
  have hvs : Summable val := (hWKs.of_norm.sigma).congr fun i => (a2 i).symm
  refine ⟨hvs, Σ i, Ξ i, inferInstance, fun p => w p.1 p.2, fun p => ctr p.1 p.2, fun p => edge p.1 p.2,
    fun p => hinge p.1 p.2, fun p => freq p.1 p.2, hWKs, hsumval.symm, hWMs, ?_, fun p => a5 p.1 p.2⟩
  have hs2 : Summable fun i => ∑' ξ, ‖w i ξ‖ * momS sel (freq i ξ) := Summable.of_nonneg_of_le
    (fun i => tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (momS_nonneg _ _)) a4 hBs
  calc ∑' p : Σ i, Ξ i, ‖w p.1 p.2‖ * momS sel (freq p.1 p.2)
      = ∑' i, ∑' ξ, ‖w i ξ‖ * momS sel (freq i ξ) := hWMs.tsum_sigma' (fun i => a3 i)
    _ ≤ ∑' i, B i := Summable.tsum_le_tsum a4 hs2 hBs

end Basic

/-! ## From a frequency-controlled count-measure representation -/

/-- A count-measure representation (as `RepIntCMK`) whose kernel frequencies have selection moment at most `M`. -/
def RepIntCMKF {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R) (sel : Finset (GBranch π.Gsb.tree))
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (val : ℂ) (B M : ℝ) : Prop :=
  ∃ (Ξ : Type) (_ : Countable Ξ) (w : Ξ → ℂ) (ctr : Ξ → GardenDart π.Gsb → Mom P.d)
    (edge : Ξ → GardenDart π.Gsb → Mom P.d → ℂ)
    (hinge : Ξ → (HingeDarts π.Gsb π.Cs.hinges → Mom P.d) → ℂ) (freq : Ξ → GBranch π.Gsb.tree → ℝ),
    Summable (fun ξ => ‖w ξ * splicedKernelMK π.Gsb (π.dataMK tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))
      P.L P.γ P.η P.δ base roots‖) ∧
    val = ∑' ξ, w ξ * splicedKernelMK π.Gsb (π.dataMK tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))
      P.L P.γ P.η P.δ base roots ∧
    Summable (fun ξ => ‖w ξ‖) ∧ ∑' ξ, ‖w ξ‖ ≤ B ∧ (∀ ξ, momS sel (freq ξ) ≤ M) ∧
    ∀ ξ, SplicedAmplitudeBounds π.Gsb (Stage1Piece.data π.toStage1PieceD tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))

theorem RepIntCMKF.toRepIntCMKS {P : WTParams} {R : ℕ} {π : Stage1PieceMK P.d R}
    {sel : Finset (GBranch π.Gsb.tree)} {tt : Fin (2 * R) → ℝ} {base : Mom P.d}
    {roots : Fin (2 * R) → (Fin P.d → ℤ)} {val : ℂ} {B M : ℝ} (h : RepIntCMKF π sel tt base roots val B M)
    (hM0 : 0 ≤ M) : RepIntCMKS π sel tt base roots val (B * M) := by
  obtain ⟨Ξ, hc, w, ctr, edge, hinge, freq, h1, h2, h3, h4, hM, h5⟩ := h
  have hle : ∀ ξ, ‖w ξ‖ * momS sel (freq ξ) ≤ ‖w ξ‖ * M := fun ξ =>
    mul_le_mul_of_nonneg_left (hM ξ) (norm_nonneg _)
  have hs : Summable fun ξ => ‖w ξ‖ * momS sel (freq ξ) :=
    Summable.of_nonneg_of_le (fun ξ => mul_nonneg (norm_nonneg _) (momS_nonneg _ _)) hle (h3.mul_right M)
  refine ⟨Ξ, hc, w, ctr, edge, hinge, freq, h1, h2, hs, ?_, h5⟩
  calc ∑' ξ, ‖w ξ‖ * momS sel (freq ξ) ≤ ∑' ξ, ‖w ξ‖ * M := Summable.tsum_le_tsum hle hs (h3.mul_right M)
    _ = (∑' ξ, ‖w ξ‖) * M := tsum_mul_right
    _ ≤ B * M := mul_le_mul_of_nonneg_right h4 hM0

end WaveTurbulence.Flower.MkSlotsS
