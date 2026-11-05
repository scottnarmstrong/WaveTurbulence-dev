/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.CplDraft.InputMoments
public import WaveTurbulence.Foundations.XChain.TruncatedCumulantPartitionCarrier
public import WaveTurbulence.Foundations.XChain.TruncatedTreeExpansion
public import WaveTurbulence.Foundations.XChain.TreeRandomMoments
public import WaveTurbulence.Foundations.XChain.UnbalancedInputBlock
public import WaveTurbulence.Foundations.XChain.ForestGaugeCharge
public import WaveTurbulence.Foundations.XChain.TreeNormBounds

/-!
# CPL-1, step 2: the mode cutoff `c_K`

`truncArr K b` keeps the modes `|n_i| ≤ K` of an array `b` and sets the others to `0`.

**Statements.**
1. Deterministic.
   - `treeSummand (truncArr K b) κ` is `treeSummand b κ` when every leaf label of `κ` lies in the box, and
     `0` otherwise.
   - Hence `treeTerm (truncArr K b) → treeTerm b` and `a^tr(truncArr K b) → a^tr(b)` as `K → ∞`, for
     summable `b`.
2. Cumulants. A block cumulant of the cut data is the uncut one when the block's labels lie in the box, and
   `0` otherwise. Hence the same holds for INDUCT's partition integrand `topPartitionCumulantIntegrand`.
3. Random cut data `c_K = truncArr K (a(p))` on `F_p`. They satisfy INDUCT's all-order hypotheses
   (`hc`, `hcs`, `hM`): the sum is finite.
4. **Mean zero**: `𝔼_p a^tr(c_K)_n(t) = 0` (`integral_aTr_truncArr_eq_zero`). Expand it with INDUCT's
   `cumulant_aTr_eq_partition_carrier` (`w = 1`). Every leaf partition of a `+` tree has a block of
   nonzero charge (`exists_unbalanced_leaf_block`), and its input cumulant vanishes
   (`ansatz_unbalanced_topBlock_zero`).
-/

@[expose] public section

namespace WaveTurbulence.Cpl

open Finset MeasureTheory Set Filter Topology Induct
open scoped ENNReal

/-! ## 1. The cutoff -/

section Deterministic

variable {d : ℕ}

/-- The box `{|n_i| ≤ K}`. -/
def modeBox (d K : ℕ) : Finset (Fin d → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(K : ℤ)) K

/-- Keep the modes in `modeBox d K`. -/
def truncArr (K : ℕ) (b : (Fin d → ℤ) → ℂ) : (Fin d → ℤ) → ℂ :=
  fun n => if n ∈ modeBox d K then b n else 0

theorem eventually_mem_modeBox (n : Fin d → ℤ) : ∀ᶠ K in atTop, n ∈ modeBox d K := by
  refine eventually_atTop.2 ⟨univ.sup fun i => (n i).natAbs, fun K hK => ?_⟩
  simp only [modeBox, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have h1 : (n i).natAbs ≤ K := (le_sup (f := fun i => (n i).natAbs) (mem_univ i)).trans hK
  have h2 : ((n i).natAbs : ℤ) ≤ K := by exact_mod_cast h1
  rw [Int.natCast_natAbs] at h2
  exact abs_le.mp h2

theorem eventually_forall_mem_modeBox {ι : Type*} [Finite ι] (m : ι → (Fin d → ℤ)) :
    ∀ᶠ K in atTop, ∀ i, m i ∈ modeBox d K :=
  eventually_all.2 fun i => eventually_mem_modeBox (m i)

theorem truncArr_of_mem {K : ℕ} {b : (Fin d → ℤ) → ℂ} {n : Fin d → ℤ} (h : n ∈ modeBox d K) :
    truncArr K b n = b n := ite_eq_left h

theorem truncArr_of_notMem {K : ℕ} {b : (Fin d → ℤ) → ℂ} {n : Fin d → ℤ} (h : n ∉ modeBox d K) :
    truncArr K b n = 0 := ite_eq_right h

theorem norm_truncArr_le (K : ℕ) (b : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ) : ‖truncArr K b n‖ ≤ ‖b n‖ := by
  unfold truncArr
  split_ifs
  · exact le_rfl
  · simp

theorem summable_norm_truncArr (K : ℕ) (b : (Fin d → ℤ) → ℂ) : Summable fun n => ‖truncArr K b n‖ :=
  summable_of_ne_finset_zero (s := modeBox d K) fun n hn => by rw [truncArr_of_notMem hn, norm_zero]

theorem tsum_norm_truncArr (K : ℕ) (b : (Fin d → ℤ) → ℂ) :
    ∑' n, ‖truncArr K b n‖ = ∑ n ∈ modeBox d K, ‖b n‖ := by
  rw [tsum_eq_sum (s := modeBox d K) fun n hn => by rw [truncArr_of_notMem hn, norm_zero]]
  exact sum_congr rfl fun n hn => by rw [truncArr_of_mem hn]

theorem tsum_norm_truncArr_le (K : ℕ) {b : (Fin d → ℤ) → ℂ} (hb : Summable fun n => ‖b n‖) :
    ∑' n, ‖truncArr K b n‖ ≤ ∑' n, ‖b n‖ :=
  (summable_norm_truncArr K b).tsum_le_tsum (norm_truncArr_le K b) hb

theorem zpowSign_zero (ζ : ℤˣ) : zpowSign ζ 0 = 0 := by
  unfold zpowSign
  split_ifs <;> simp

variable (L γ δ : ℝ)

theorem treeSummand_truncArr (p : ℕ) (T : TTree) (K : ℕ) (b : (Fin d → ℤ) → ℂ) (t : ℝ)
    (n : Fin d → ℤ) (κ : TreeDecoration T d n) :
    SysAPI.treeSummand L γ δ p T (truncArr K b) t n κ =
      if ∀ ℓ : GLeaf (single T), κ.1 ℓ.toNode ∈ modeBox d K then SysAPI.treeSummand L γ δ p T b t n κ
      else 0 := by
  unfold SysAPI.treeSummand
  split_ifs with h
  · congr 1
    exact prod_congr rfl fun ℓ _ => by rw [truncArr_of_mem (h ℓ)]
  · push Not at h
    obtain ⟨ℓ, hℓ⟩ := h
    rw [prod_eq_zero (mem_univ ℓ) (by rw [truncArr_of_notMem hℓ, zpowSign_zero]), mul_zero]

theorem tendsto_treeTerm_truncArr (p : ℕ) (T : TTree) {b : (Fin d → ℤ) → ℂ}
    (hb : Summable fun m => ‖b m‖) (t : ℝ) (n : Fin d → ℤ) :
    Tendsto (fun K : ℕ => treeTerm L γ δ p T (truncArr K b) t n) atTop
      (𝓝 (treeTerm L γ δ p T b t n)) := by
  simp only [SysAPI.treeTerm_eq]
  apply Tendsto.const_mul
  apply tendsto_tsum_of_dominated_convergence (SysAPI.summable_treeSummand L γ δ p T hb t n)
  · intro κ
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_forall_mem_modeBox (fun ℓ : GLeaf (single T) => κ.1 ℓ.toNode)] with K hK
    rw [treeSummand_truncArr, ite_eq_left hK]
  · refine Eventually.of_forall fun K κ => ?_
    rw [treeSummand_truncArr]
    split_ifs
    · exact le_rfl
    · simp

theorem tendsto_aTr_truncArr (p Ntop : ℕ) {b : (Fin d → ℤ) → ℂ} (hb : Summable fun m => ‖b m‖)
    (t : ℝ) (n : Fin d → ℤ) :
    Tendsto (fun K : ℕ => aTr L γ δ p Ntop (truncArr K b) t n) atTop
      (𝓝 (aTr L γ δ p Ntop b t n)) := by
  simp only [aTr_eq_sum_TrTree]
  exact tendsto_finsetSum _ fun T _ => tendsto_treeTerm_truncArr L γ δ p T.1 hb t n

/-- `|a^tr(b)| ≤ ∑_T |pref_T| vol_T (∑|b|)^{#leaves}` (INDUCT `norm_treeTerm_le_l1`). -/
theorem norm_aTr_le_l1 (p Ntop : ℕ) {b : (Fin d → ℤ) → ℂ} (hb : Summable fun m => ‖b m‖) (t : ℝ)
    (n : Fin d → ℤ) :
    ‖aTr L γ δ p Ntop b t n‖ ≤ ∑ T : TrTree Ntop, (‖SysAPI.treePrefactor L γ δ d T.1‖ *
      SysAPI.boxVol T.1 p t) * (∑' m, ‖b m‖) ^ Fintype.card (GLeaf (single T.1)) := by
  rw [aTr_eq_sum_TrTree]
  exact (norm_sum_le _ _).trans (sum_le_sum fun T _ => norm_treeTerm_le_l1 L γ δ p T.1 hb t n)

end Deterministic

/-! ## 2. Cumulants of cut data -/

section Cumulants

variable {Ω : Type*} [MeasurableSpace Ω]

theorem cumulant_congr_on {ι : Type*} [DecidableEq ι] (μ : Measure Ω) {X Y : ι → Ω → ℂ}
    (s : Finset ι) (h : ∀ i ∈ s, X i = Y i) : cumulant μ X s = cumulant μ Y s := by
  unfold cumulant
  refine sum_congr rfl fun P _ => ?_
  congr 1
  refine prod_congr rfl fun A hA => ?_
  congr 1
  funext ω
  exact prod_congr rfl fun j hj => by rw [h j (P.le hA hj)]

theorem cumulant_eq_zero_of_mem_zero {ι : Type*} [DecidableEq ι] (μ : Measure Ω) (X : ι → Ω → ℂ)
    (s : Finset ι) {l : ι} (hl : l ∈ s) (hX : ∀ ω, X l ω = 0) : cumulant μ X s = 0 := by
  unfold cumulant
  refine sum_eq_zero fun P _ => ?_
  obtain ⟨A, hA, hlA⟩ := P.exists_mem hl
  have hz : (fun ω => ∏ j ∈ A, X j ω) = fun _ => 0 := funext fun ω => prod_eq_zero hlA (hX ω)
  rw [prod_eq_zero hA (by rw [hz, integral_zero]), mul_zero]

variable {w d : ℕ} (μ : Measure Ω) (sig : Fin w → ℤˣ) (top : Fin w → TTree)

theorem topBlockCumulant_truncArr (K : ℕ) (c : Ω → (Fin d → ℤ) → ℂ) {n : Fin w → (Fin d → ℤ)}
    (κ : ForestDecoration top d n) (B : Finset (GLeaf top)) :
    topBlockCumulant μ sig top (fun ω => truncArr K (c ω)) κ B =
      if ∀ l ∈ B, κ.1 l.toNode ∈ modeBox d K then topBlockCumulant μ sig top c κ B else 0 := by
  unfold topBlockCumulant
  split_ifs with h
  · exact cumulant_congr_on μ B fun l hl => funext fun ω => by simp only [truncArr_of_mem (h l hl)]
  · push Not at h
    obtain ⟨l, hl, hout⟩ := h
    exact cumulant_eq_zero_of_mem_zero μ _ B hl fun ω => by
      simp only [truncArr_of_notMem hout, zpowSign_zero]

variable (L γ δ : ℝ)

theorem topPartitionCumulantIntegrand_truncArr (P : Finpartition (univ : Finset (GLeaf top)))
    (K : ℕ) (c : Ω → (Fin d → ℤ) → ℂ) (p : ℕ) (t : ℝ) (n : Fin w → (Fin d → ℤ))
    (κ : ForestDecoration top d n) :
    topPartitionCumulantIntegrand μ L γ δ sig top P (fun ω => truncArr K (c ω)) p t n κ =
      if ∀ l : GLeaf top, κ.1 l.toNode ∈ modeBox d K then
        topPartitionCumulantIntegrand μ L γ δ sig top P c p t n κ else 0 := by
  unfold topPartitionCumulantIntegrand
  by_cases h : ∀ l : GLeaf top, κ.1 l.toNode ∈ modeBox d K
  · have hp : (∏ B : P.parts, topBlockCumulant μ sig top (fun ω => truncArr K (c ω)) κ B.1) =
        ∏ B : P.parts, topBlockCumulant μ sig top c κ B.1 :=
      prod_congr rfl fun B _ => by
        rw [topBlockCumulant_truncArr, ite_eq_left_iff.mpr fun h' => absurd (fun l _ => h l) h']
    rw [hp, ite_eq_left_iff.mpr fun h' => absurd h h']
  · have hp : (∏ B : P.parts, topBlockCumulant μ sig top (fun ω => truncArr K (c ω)) κ B.1) = 0 := by
      push Not at h
      obtain ⟨l, hout⟩ := h
      obtain ⟨B, hB, hlB⟩ := P.exists_mem (mem_univ l)
      refine prod_eq_zero (mem_univ (⟨B, hB⟩ : P.parts)) ?_
      rw [topBlockCumulant_truncArr]
      exact ite_eq_right_iff.mpr fun h' => absurd (h' l hlB) hout
    rw [hp, mul_zero, ite_eq_right_iff.mpr fun h' => absurd h' h]

end Cumulants

/-! ## 3. Random cut data on `F_p` -/

section Random

variable (P : WTParams) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : (Fin P.d → ℤ) → Ω → ℂ)
    (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω) (R : ℕ → Mom P.d → ℝ)
    (E : ℕ → (Fin P.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ) (p : ℕ)

theorem memLp_truncInput (ha : AnsatzAt P μ g a Fev R E Et p) (K : ℕ) (n : Fin P.d → ℤ) (q : ℕ)
    (hq : 1 ≤ q) : MemLp (fun ω => truncArr K (a ω p) n) (q : ℝ≥0∞) (μ.restrict (Fev p)) := by
  by_cases h : n ∈ modeBox P.d K
  · simp only [truncArr_of_mem h]
    exact memLp_input_mode P μ g a Fev R E Et p ha n q hq
  · simp only [truncArr_of_notMem h]
    exact MemLp.zero

theorem memLp_l1_truncInput (ha : AnsatzAt P μ g a Fev R E Et p) (K : ℕ) (q : ℕ) (hq : 1 ≤ q) :
    MemLp (fun ω => ∑' n, ‖truncArr K (a ω p) n‖) (q : ℝ≥0∞) (μ.restrict (Fev p)) := by
  simp only [tsum_norm_truncArr]
  exact memLp_finsetSum _ fun n _ => (memLp_input_mode P μ g a Fev R E Et p ha n q hq).norm

/-- **`𝔼_p a^tr(c_K)_n(t) = 0`.** -/
theorem integral_aTr_truncArr_eq_zero (hG : IsGaussianData μ g) (hL : 0 < P.L)
    (ha : AnsatzAt P μ g a Fev R E Et p)
    (hrapid : ∀ ω ∈ Fev p, IsRapidDecay (initialCoeff P.L P.φin g ω))
    (K Ntop : ℕ) (t : ℝ) (n : Fin P.d → ℤ) :
    ∫ ω in Fev p, aTr P.L P.γ P.δ p Ntop (truncArr K (a ω p)) t n ∂μ = 0 := by
  classical
  have hc := memLp_truncInput P μ g a Fev R E Et p ha K
  have hcs : ∀ᵐ ω ∂μ.restrict (Fev p), Summable fun n => ‖truncArr K (a ω p) n‖ :=
    Eventually.of_forall fun ω => summable_norm_truncArr K (a ω p)
  have hM := memLp_l1_truncInput P μ g a Fev R E Et p ha K
  have h := cumulant_aTr_eq_partition_carrier P.L P.γ P.δ p Ntop
    (fun ω => truncArr K (a ω p)) hc hcs hM t (fun _ : Fin 1 => n) (fun _ => 1)
  have hu : (univ : Finset (Fin 1)) = {0} := rfl
  rw [hu, cumulant_singleton] at h
  have hz1 (z : ℂ) : zpowSign 1 z = z := ite_eq_left rfl
  simp only [hz1] at h
  rw [h]
  refine sum_eq_zero fun top _ => ?_
  refine mul_eq_zero_of_right _ (sum_eq_zero fun Q _ => ?_)
  refine (tsum_congr fun κ => ?_).trans tsum_zero
  rw [topPartitionCumulantIntegrand_truncArr]
  split_ifs
  · have hs : ∑ j, ((fun _ : Fin 1 => (1 : ℤˣ)) j : ℤ) ≠ 0 := by simp
    obtain ⟨B, hB⟩ := exists_unbalanced_leaf_block (fun j => (top j).1) (fun _ : Fin 1 => (1 : ℤˣ))
      hs Q.1
    unfold topPartitionCumulantIntegrand
    rw [prod_eq_zero (mem_univ B) (ansatz_unbalanced_topBlock_zero P μ g hG hL a Fev R E Et p ha hrapid
      (fun _ : Fin 1 => (1 : ℤˣ)) (fun j => (top j).1) Q.1 κ B hB 0).1, mul_zero]
  · rfl

end Random

end WaveTurbulence.Cpl
