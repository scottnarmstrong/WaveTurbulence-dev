/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.RTChainObl

/-! # B3s-HELPER3 (B5(ii)): the root-trace COUPLE slot from `RootTraceGate`

RT (ii′) bounds the couple kernel per lattice ball `latticeBall L 0 (latPt d n)`, with the centre decay
`⟨latPt d n⟩^{-2d}`. A leaf-pair slot is consumed at every lattice momentum, with ball-localized amplitudes and one
summable mass: for each centre `n` the ball bound gives a superposition (`sup_of_xnorm_le`); multiplying its amplitudes
by main's partition piece `χ_n` (`RepAnalytic.chiC`, support in the unit ball at `latPt d n`, Leibniz
`snorm_chi_mul_le`) localizes them, and the union over `n` represents the kernel at every lattice momentum
(`hasSum_chiC_mul`) with mass `≲ Bd · Σ_n ⟨latPt d n⟩^{-2d}` (`summable_jbr_latPt_inv`, `2d > d`).

* `rtCchi`, `rtSd`, `rtKq`, `rtKcpl`: the constants;
* **`cenSup_of_balls`**: the per-ball to localized assembly;
* `genSlotKer_cpl`: on a root-trace couple slot the general slot kernel is RT (ii′)'s kernel;
* **`slotFam1_cpl`**: HELPER8's `MkSlotsO.SlotFam1` for a root-trace couple slot at `θ = η` (and `θ = 1/4` when one
  root is pinned). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open Set
open WaveTurbulence TTree WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  WaveTurbulence.LGSpine WaveTurbulence.Represents WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
  WaveTurbulence.VineAlign WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.ProtDefs
  WaveTurbulence.Flower.Stage1WNoVine WaveTurbulence.Flower.Stage1W WaveTurbulence.VineEstS3.FS
  WaveTurbulence.RepAnalytic

namespace WaveTurbulence.Flower.MkSlotsB

/-! ### The constants -/

/-- The Leibniz constant of the partition pieces at `SNorm (30 d) 0`, at least `1`. -/
def rtCchi (d : ℕ) : ℝ :=
  if h : 1 ≤ d then max 1 (Classical.choose (RepAnalytic.snorm_chi_mul_le h (30 * d) 0)) else 1

theorem one_le_rtCchi (d : ℕ) : 1 ≤ rtCchi d := by
  unfold rtCchi
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

theorem rtCchi_spec {d : ℕ} (hd : 1 ≤ d) (H : Mom d → ℂ) (hH : ContDiff ℝ (30 * d) H) (n : Fin d → ℤ) :
    SNorm (30 * d) 0 (fun k => chiC d n k * H k) ≤ ENNReal.ofReal (rtCchi d) * SNorm (30 * d) 0 H := by
  have hs := (Classical.choose_spec (RepAnalytic.snorm_chi_mul_le hd (30 * d) 0)).2 H hH n
  refine hs.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  unfold rtCchi
  split_ifs
  rw [pow_zero, inv_one, mul_one]
  exact le_max_right _ _

/-- The centre sum `Σ_n ⟨latPt d n⟩^{-2d}`. -/
def rtSd (d : ℕ) : ℝ := ∑' n : Fin d → ℤ, ((jbr (latPt d n)) ^ (2 * d))⁻¹

theorem rtSd_nonneg (d : ℕ) : 0 ≤ rtSd d :=
  tsum_nonneg fun _ => inv_nonneg.2 (pow_nonneg (Induct.jbr_pos _).le _)

/-- The couple constant at one weight. -/
def rtKq (d : ℕ) (θ : ℝ) : ℝ := 2 * (rtCchi d * (MkSlots.capCsup d θ).toReal * rtSd d)

theorem rtKq_nonneg (d : ℕ) (θ : ℝ) : 0 ≤ rtKq d θ := by
  unfold rtKq
  have := one_le_rtCchi d
  have := rtSd_nonneg d
  have : 0 ≤ (MkSlots.capCsup d θ).toReal := ENNReal.toReal_nonneg
  positivity

/-- **The root-trace couple slot constant.** -/
def rtKcpl (d : ℕ) (η : ℝ) : ℝ := 1 + rtKq d η + rtKq d (1 / 4)

theorem one_le_rtKcpl (d : ℕ) (η : ℝ) : 1 ≤ rtKcpl d η := by
  unfold rtKcpl
  have := rtKq_nonneg d η
  have := rtKq_nonneg d (1 / 4)
  linarith

/-! ### Per-ball superpositions to one localized superposition -/

/-- **The per-ball to localized assembly.** -/
theorem cenSup_of_balls {d : ℕ} (hd : 1 ≤ d) {θ : ℝ} (hθ : 0 ≤ θ) (L : ℝ) (q : Fin 2 → ℝ)
    (B : Set (Fin 2 → ℝ)) (hBc : B ⊆ cell q) (hBi : B ⊆ closure (interior B)) (f : (Fin 2 → ℝ) → Mom d → ℂ)
    (hfc : ∀ k, Continuous fun t => f t k) (Bd : ℝ≥0∞) (hBd : Bd ≠ ⊤)
    (hball : ∀ n : Fin d → ℤ, XNormRestr θ (30 * d) 0 B (latticeBall L 0 (latPt d n)) f ≤
      Bd * ENNReal.ofReal ((jbr (latPt d n) ^ (2 * d))⁻¹)) :
    ∃ (Λ : Type) (_ : Countable Λ) (wt : Λ → ℝ) (m : Λ → Fin 2 → ℤ) (c : Λ → Fin d → ℤ) (amp : Λ → Mom d → ℂ),
      (∀ l, 0 ≤ wt l) ∧ Summable wt ∧ (∀ l, SNorm (30 * d) 0 (amp l) ≤ 1) ∧
      (∀ l k, amp l k ≠ 0 → ‖k - latPt d (c l)‖ ≤ 1) ∧
      (∀ t ∈ B, ∀ n' : Fin d → ℤ,
        HasSum (fun l => (wt l : ℂ) * amp l (latticePoint L n') * fsPhase (m l) t) (f t (latticePoint L n'))) ∧
      ∑' l, maxBracketPow θ (half (m l)) * ENNReal.ofReal (wt l) ≤
        ENNReal.ofReal (rtCchi d * (MkSlots.capCsup d θ).toReal * rtSd d) * (2 * Bd) := by
  set u : (Fin d → ℤ) → ℝ := fun n => (jbr (latPt d n) ^ (2 * d))⁻¹ with hu
  have hu0 : ∀ n, 0 ≤ u n := fun n => inv_nonneg.2 (pow_nonneg (Induct.jbr_pos _).le _)
  have hus : Summable u := summable_jbr_latPt_inv hd (by omega)
  have hfam : ∀ n : Fin d → ℤ, ∃ (Λ : Type) (_ : Countable Λ) (wt : Λ → ℝ) (m : Λ → Fin 2 → ℤ)
      (amp : Λ → Mom d → ℂ), (∀ l, 0 ≤ wt l) ∧ Summable wt ∧ (∀ l, SNorm (30 * d) 0 (amp l) ≤ 1) ∧
      (∀ t ∈ B, ∀ k ∈ latticeBall L 0 (latPt d n), HasSum (fun l => (wt l : ℂ) * amp l k * fsPhase (m l) t)
        (f t k)) ∧
      ∑' l, maxBracketPow θ (half (m l)) * ENNReal.ofReal (wt l) ≤
        MkSlots.capCsup d θ * (2 * (Bd * ENNReal.ofReal (u n))) := fun n =>
    sup_of_xnorm_le hθ (MkSlots.capCsup_spec d hθ) q B _ f _ (ENNReal.mul_ne_top hBd ENNReal.ofReal_ne_top) hBc hBi
      (fun k _ => hfc k) (hball n)
  choose Λ hΛ w m a hw0 hws haS hsum hmass using hfam
  have hΛ' : ∀ n, Countable (Λ n) := hΛ
  set Cχ := rtCchi d with hCχ
  have hCχ1 : 1 ≤ Cχ := one_le_rtCchi d
  have hCχ0 : 0 < Cχ := lt_of_lt_of_le one_pos hCχ1
  have hCs := MkSlots.capCsup_ne_top d θ
  set Cs := (MkSlots.capCsup d θ).toReal with hCsdef
  have hCs0 : 0 ≤ Cs := ENNReal.toReal_nonneg
  -- the fibre sums
  have hfib : ∀ n, ∑' l, w n l ≤ Cs * (2 * (Bd.toReal * u n)) := by
    intro n
    have h1 : ENNReal.ofReal (∑' l, w n l) ≤ MkSlots.capCsup d θ * (2 * (Bd * ENNReal.ofReal (u n))) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (hw0 n) (hws n)]
      refine le_trans (ENNReal.tsum_le_tsum fun l => ?_) (hmass n)
      exact le_mul_of_one_le_left bot_le (RepAnalytic.one_le_maxBracketPow hθ _)
    have hfin : MkSlots.capCsup d θ * (2 * (Bd * ENNReal.ofReal (u n))) ≠ ⊤ :=
      ENNReal.mul_ne_top hCs (ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top hBd ENNReal.ofReal_ne_top))
    have h2 := (ENNReal.ofReal_le_iff_le_toReal hfin).1 h1
    refine h2.trans (le_of_eq ?_)
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hu0 n), ENNReal.toReal_ofNat]
    rfl
  have hws' : Summable fun p : (Σ n, Λ n) => Cχ * w p.1 p.2 := by
    refine (summable_sigma_of_nonneg fun p => mul_nonneg hCχ0.le (hw0 p.1 p.2)).2
      ⟨fun n => (hws n).mul_left Cχ, ?_⟩
    refine Summable.of_nonneg_of_le (fun n => tsum_nonneg fun l => mul_nonneg hCχ0.le (hw0 n l))
      (fun n => ?_) ((hus.mul_left (Cχ * (Cs * (2 * Bd.toReal)))))
    rw [tsum_mul_left]
    calc Cχ * ∑' l, w n l ≤ Cχ * (Cs * (2 * (Bd.toReal * u n))) := mul_le_mul_of_nonneg_left (hfib n) hCχ0.le
      _ = Cχ * (Cs * (2 * Bd.toReal)) * u n := by ring
  have hamp : ∀ (n : Fin d → ℤ) (l : Λ n),
      SNorm (30 * d) 0 (fun k => ((Cχ⁻¹ : ℝ) : ℂ) * (chiC d n k * a n l k)) ≤ 1 := by
    intro n l
    have hcd : ContDiff ℝ (30 * d) (a n l) :=
      contDiff_of_SNorm_ne_top (Nat.mul_ne_zero (by norm_num) (Nat.one_le_iff_ne_zero.mp hd))
        (ne_top_of_le_ne_top ENNReal.one_ne_top (haS n l))
    refine (VineEstS3.Eng.SNorm_smul_le (30 * d) 0 _ _).trans ?_
    calc ‖((Cχ⁻¹ : ℝ) : ℂ)‖ₑ * SNorm (30 * d) 0 (fun k => chiC d n k * a n l k)
        ≤ ‖((Cχ⁻¹ : ℝ) : ℂ)‖ₑ * (ENNReal.ofReal Cχ * 1) :=
          mul_le_mul' le_rfl ((rtCchi_spec hd (a n l) hcd n).trans (mul_le_mul' le_rfl (haS n l)))
      _ = 1 := by
          rw [mul_one, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hCχ0),
            ← ENNReal.ofReal_mul (inv_pos.2 hCχ0).le, inv_mul_cancel₀ hCχ0.ne', ENNReal.ofReal_one]
  refine ⟨Σ n, Λ n, inferInstance, fun p => Cχ * w p.1 p.2, fun p => m p.1 p.2, fun p => p.1,
    fun p k => ((Cχ⁻¹ : ℝ) : ℂ) * (chiC d p.1 k * a p.1 p.2 k), fun p => mul_nonneg hCχ0.le (hw0 p.1 p.2), hws',
    fun p => hamp p.1 p.2, fun p k hk => ?_, fun t ht n' => ?_, ?_⟩
  · exact norm_sub_latPt_le_one_of_chiC_mul_ne_zero (right_ne_zero_of_mul hk)
  · set k := latticePoint L n'
    have hfib' : ∀ n, HasSum (fun l : Λ n => ((Cχ * w n l : ℝ) : ℂ) *
        (((Cχ⁻¹ : ℝ) : ℂ) * (chiC d n k * a n l k)) * fsPhase (m n l) t) (chiC d n k * f t k) := by
      intro n
      have he : (fun l : Λ n => ((Cχ * w n l : ℝ) : ℂ) * (((Cχ⁻¹ : ℝ) : ℂ) * (chiC d n k * a n l k)) *
          fsPhase (m n l) t) = fun l => chiC d n k * ((w n l : ℂ) * a n l k * fsPhase (m n l) t) := by
        funext l
        have : (Cχ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hCχ0.ne'
        push_cast
        field_simp
      rw [he]
      by_cases h0 : chi d n k = 0
      · have hc : chiC d n k = 0 := by simp [chiC, h0]
        simp only [hc, zero_mul]
        exact hasSum_zero
      · have hk : k ∈ latticeBall L 0 (latPt d n) := ⟨norm_sub_le_one_of_chi_ne_zero h0, n', by rw [zero_add]⟩
        exact (hsum n t ht k hk).mul_left _
    refine HasSum.sigma_of_hasSum (hasSum_chiC_mul (f t) k) hfib' ?_
    refine Summable.of_norm_bounded hws' fun p => ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hCχ0.le (hw0 p.1 p.2))]
    have hph : ‖fsPhase (m p.1 p.2) t‖ = 1 := by unfold fsPhase; exact Circle.norm_coe _
    rw [hph, mul_one]
    exact mul_le_of_le_one_right (mul_nonneg hCχ0.le (hw0 p.1 p.2))
      (Represents.snorm_le_one_pointwise _ _ (hamp p.1 p.2) k)
  · -- the mass
    rw [ENNReal.tsum_sigma']
    have hstep : ∀ n, ∑' l, maxBracketPow θ (half (m n l)) * ENNReal.ofReal (Cχ * w n l) ≤
        ENNReal.ofReal Cχ * (MkSlots.capCsup d θ * (2 * (Bd * ENNReal.ofReal (u n)))) := by
      intro n
      calc ∑' l, maxBracketPow θ (half (m n l)) * ENNReal.ofReal (Cχ * w n l)
          = ENNReal.ofReal Cχ * ∑' l, maxBracketPow θ (half (m n l)) * ENNReal.ofReal (w n l) := by
            rw [← ENNReal.tsum_mul_left]
            refine tsum_congr fun l => ?_
            rw [ENNReal.ofReal_mul hCχ0.le]
            ring
        _ ≤ _ := mul_le_mul' le_rfl (hmass n)
    refine (ENNReal.tsum_le_tsum hstep).trans (le_of_eq ?_)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
      ← ENNReal.ofReal_tsum_of_nonneg hu0 hus, ← ENNReal.ofReal_toReal hCs,
      show (∑' n, u n) = rtSd d from rfl, ENNReal.ofReal_mul (mul_nonneg hCχ0.le hCs0),
      ENNReal.ofReal_mul hCχ0.le]
    ring

/-! ### The couple gate box -/

/-- A closed rectangle `[l₀, u₀] × [l₁, u₁]` (`l < u`) is in the closure of its interior. -/
theorem rect_subset_closure_interior (l0 u0 l1 u1 : ℝ) (h0 : l0 < u0) (h1 : l1 < u1) :
    {ts : Fin 2 → ℝ | ts 0 ∈ Icc l0 u0 ∧ ts 1 ∈ Icc l1 u1} ⊆
      closure (interior {ts : Fin 2 → ℝ | ts 0 ∈ Icc l0 u0 ∧ ts 1 ∈ Icc l1 u1}) := by
  set Rr := {ts : Fin 2 → ℝ | ts 0 ∈ Icc l0 u0 ∧ ts 1 ∈ Icc l1 u1}
  have hcv : Convex ℝ Rr := by
    intro x hx y hy a b ha hb hab
    obtain ⟨⟨hx1, hx2⟩, hx3, hx4⟩ := hx
    obtain ⟨⟨hy1, hy2⟩, hy3, hy4⟩ := hy
    have e : ∀ i, (a • x + b • y) i = a * x i + b * y i := fun i => by simp [smul_eq_mul]
    have hb' : b = 1 - a := by linarith
    subst hb'
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> rw [e] <;> nlinarith
  have hne : (interior Rr).Nonempty := by
    let U : Set (Fin 2 → ℝ) := {ts | l0 < ts 0 ∧ ts 0 < u0 ∧ l1 < ts 1 ∧ ts 1 < u1}
    have hUo : IsOpen U := by
      simp only [U, Set.ofPred_and]
      exact (isOpen_lt continuous_const (continuous_apply 0)).inter ((isOpen_lt (continuous_apply 0)
        continuous_const).inter ((isOpen_lt continuous_const (continuous_apply 1)).inter
          (isOpen_lt (continuous_apply 1) continuous_const)))
    have hUsub : U ⊆ Rr := fun ts h => ⟨⟨h.1.le, h.2.1.le⟩, ⟨h.2.2.1.le, h.2.2.2.le⟩⟩
    refine ⟨![(l0 + u0) / 2, (l1 + u1) / 2], interior_maximal hUsub hUo ?_⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith
  rw [hcv.closure_interior_eq_closure_of_nonempty_interior hne]
  exact subset_closure

/-- The couple gate box is a rectangle (the pinned coordinates cut at `s`, inside their windows). -/
theorem cplBox_eq_rect (q0 q1 s : ℝ) (Rt : Fin 2 → Prop) (h0 : Rt 0 → q0 ≤ s) (h1 : Rt 1 → q1 ≤ s) :
    timeBox q0 q1 ∩ {ts | ∀ j, Rt j → s ≤ ts j} =
      {ts : Fin 2 → ℝ | ts 0 ∈ Icc (if Rt 0 then s else q0) (q0 + 1) ∧
        ts 1 ∈ Icc (if Rt 1 then s else q1) (q1 + 1)} := by
  have c : ∀ (q x : ℝ) (R : Prop), (R → q ≤ s) →
      (((q ≤ x ∧ x ≤ q + 1) ∧ (R → s ≤ x)) ↔ ((if R then s else q) ≤ x ∧ x ≤ q + 1)) := by
    intro q x R hR
    by_cases hr : R
    · simp only [hr, ↓reduceIte, true_imp_iff]
      constructor
      · rintro ⟨⟨-, h2⟩, h3⟩
        exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨(hR hr).trans h1, h2⟩, h1⟩
    · simp only [hr, ↓reduceIte, false_imp_iff, and_true]
  ext ts
  have e0 := c q0 (ts 0) (Rt 0) h0
  have e1 := c q1 (ts 1) (Rt 1) h1
  simp only [timeBox, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Icc, Fin.forall_fin_two]
  rw [← e0, ← e1]
  tauto

/-! ### The couple slot -/

theorem clkLayer_le {w : ℕ} {S : Garden w} (p : ℕ) (layer0 : GBranch S.tree → ℕ) (hl : ∀ b, layer0 b ≤ p)
    (y : ClkSrc S) : clkLayer p layer0 y ≤ p := by
  cases y with
  | inl _ => exact le_rfl
  | inr b => exact hl b

section CplFam

variable {R p : ℕ} {a : PrescribedPrimeGarden (2 * R)} {J : Finset (Fin (2 * R))} {pat : Fin (2 * R) → FixPat}
  {t s : ℝ} {q' : SourcePair a.prime.skeleton} {Rt : Fin 2 → Prop}

/-- **The general slot kernel of a root-trace couple slot is RT (ii′)'s kernel.** -/
theorem genSlotKer_cpl (G : RTCouple a J pat t s p q' Rt) {d : ℕ} (L γ δ : ℝ) (σ kSel : Fin (2 * R) → Option ℕ)
    (Rs : Fin (2 * R) → ℝ) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom d → ℝ) (roots : Fin (2 * R) → (Fin d → ℤ))
    (Rf : Fin (2 * R) → Option ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom d)) (ts : Fin 2 → ℝ) (k : Mom d) :
    MkSlotsI.genSlotKer L γ δ p a J pat t s σ kSel Rs h roots Rf dag (.inl q') ts k =
      kernelProt L γ δ (nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) q')
        (MkSlots.capProfiles (nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a)
          (sourceLayer_isLayering a) q')
          (fun z => MkSlots.anchProfiles J (MkSlots.recLG a) h L roots
            ((nativeCoupleForest a.prime.data a.prime.prime.1 q').nodeEmbedding z).1))
        (fun κ => IncTop.starWeight (frontNat2 a (nativeCoupleForest a.prime.data a.prime.prime.1 q').nodeEmbedding p)
          (fun z y => frontierG (Rf ((nativeCoupleForest a.prime.data a.prime.prime.1 q').nodeEmbedding z).1.1)
            (y 0)) κ)
        (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 (MkSlotsO.rootPins Rt s) k (fun _ => 0) 0 := by
  unfold MkSlotsI.genSlotKer
  dsimp only [slotFnGWFRL]
  have hΘ : MkSlotsI.genΘs a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J L σ kSel Rs
      (.inl q') k = fun _ => 1 := funext fun κ => G.genΘs_one L σ kSel Rs k κ
  have hfix : MkSlots.fixNative a.prime.data a.prime.prime.1 (fixCap (MkSlots.recLG a) J pat t s) (.inl q') =
      MkSlotsO.rootPins Rt s := funext fun q => G.pins q
  have hm : (fun k' => ∏ z, MkSlots.chainW a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
      L γ δ p s J Rf dag ((nativeCoupleForest a.prime.data a.prime.prime.1 q').nodeEmbedding z) (k' z)) =
      fun κ => IncTop.starWeight (frontNat2 a (nativeCoupleForest a.prime.data a.prime.prime.1 q').nodeEmbedding p)
        (fun z y => frontierG (Rf ((nativeCoupleForest a.prime.data a.prime.prime.1 q').nodeEmbedding z).1.1)
          (y 0)) κ := by
    funext K'
    refine (Finset.prod_congr rfl fun z _ => ?_).trans (prod_fwNode_eq_starWeight (MkSlots.recLG a) p
      (fun j => frontierG (Rf j)) (nativeCoupleForest a.prime.data a.prime.prime.1 q').nodeEmbedding K')
    exact G.chainW_eq L γ δ s Rf dag z (K' z)
  rw [hΘ, hfix]
  refine (kernelNodeWR_kDomainR_eq_kernelProt L γ δ _ _ _ _ _ _ k _ _ _ (fun hf _ _ => hf.elim)).trans ?_
  exact congrArg (fun m' => kernelProt L γ δ _ _ m' (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0
    (MkSlotsO.rootPins Rt s) k (fun _ => 0) 0) hm

/-- **The root-trace couple slot family** at a weight `θ` allowed by RT (ii′), at every centre `x`. -/
theorem slotFam1_cpl {P : WTParams} (hRT : MkSlotsO.RootTraceBoundAt P) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L)
    (hηγ : P.η ^ 8 ≤ P.gamma1 - Real.sqrt P.η) (hC1 : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ)
    (C : ℝ) (hC : P.C₁ ≤ C) (hp : p < P.D) (hsz : a.prime.data.size ≤ P.N (p + 1) ^ 4) (hps : (p : ℝ) < s)
    (hsp : s < p + 1) (hlay : ∀ z, (MkSlots.recLG a).layer z ≤ p) (G : RTCouple a J pat t s p q' Rt)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ = P.η ∨ (θ = 1 / 4 ∧ ¬ (Rt 0 ∧ Rt 1)))
    (σ kSel : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (b : ℝ) (hb1 : 1 ≤ b)
    (hb : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b)
    (Rf : Fin (2 * R) → Option ℝ) (hRf1 : ∀ j r, Rf j = some r → 1 ≤ r)
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (x : Fin P.d → ℤ) (Kp : ℝ)
    (hKp : 2 * (rtCchi P.d * (MkSlots.capCsup P.d θ).toReal * rtSd P.d) ≤ Kp) (μ : ℝ≥0∞)
    (hμ : ENNReal.ofReal (Kp * MkSlotsI.genSlotMass P C b a J pat t s kSel Rs (.inl q')) ≤ μ) :
    MkSlotsO.SlotFam1 P (p := p) a J pat t s σ kSel Rs h roots Rf dag (.inl q') x θ μ := by
  set LGq := nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) q'
    with hLGq
  set Q := a.prime.data.couple q' with hQdef
  set e := (nativeCoupleForest a.prime.data a.prime.prime.1 q').nodeEmbedding with he
  set S := frontNat2 a e p with hS
  set ω : GNode LGq.garden.tree → IncTop.Star P.d → ℂ := fun z y => frontierG (Rf (e z).1.1) (y 0) with hω
  set H := MkSlots.capProfiles LGq (fun z => MkSlots.anchProfiles J (MkSlots.recLG a) h P.L roots (e z).1)
    with hH
  set B' := nativeCoupleB a.prime.data a.prime.prime.1 (fun _ => b.toNNReal) q' with hB'
  set layer0 : GBranch a.prime.skeleton.tree → ℕ :=
    fun β => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 β).toNode with hlayer0
  set q0 := clkLayer p layer0 (argSrc a.prime.prime.1 (.inl q') 0) with hq0def
  set q1 := clkLayer p layer0 (argSrc a.prime.prime.1 (.inl q') 1) with hq1def
  have hdec : Q.Decodes LGq.garden := by
    rw [hLGq, nativeCoupleLayered_garden]
    exact decodedCouple_decodes _
  set n := Q.size / 2 with hndef
  have hQs : Q.size = 2 * n := by
    obtain ⟨r, hr⟩ := code_size_even Q
    omega
  have hQD : Q.size ≤ a.prime.data.size := Represents.slotSize_le a.prime.data (.inl q')
  have hn : n ≤ P.N (p + 1) ^ 4 := by omega
  have hord : 1 ≤ Q.size := by
    rw [← decodedCouple_order Q, ← nativeCoupleLayered_garden a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) q']
    obtain ⟨j0, hj0⟩ := G.rt
    have hbr := (G.root_pinned j0 hj0).1
    have h1 : 1 ≤ (LGq.garden.tree j0).order := by
      cases hT : LGq.garden.tree j0 with
      | leaf => rw [hT] at hbr; simp [TTree.branching] at hbr
      | node l m r => simp [TTree.order]
    unfold Garden.order
    exact h1.trans (Finset.single_le_sum (f := fun j => (LGq.garden.tree j).order) (fun j _ => Nat.zero_le _)
      (Finset.mem_univ j0))
  have hn1 : 1 ≤ n := by omega
  have hl0 : ∀ β, layer0 β ≤ p := fun β => hlay _
  have hq0 : q0 ≤ p := clkLayer_le p layer0 hl0 _
  have hq1 : q1 ≤ p := clkLayer_le p layer0 hl0 _
  have hpin : ∀ j, Rt j → (clkLayer p layer0 (argSrc a.prime.prime.1 (.inl q') j) : ℝ) = p := by
    intro j hj
    have h1 := (G.root_pinned j hj).2
    have h2 := G.root_le j
    have h3 := clkLayer_le p layer0 hl0 (argSrc a.prime.prime.1 (.inl q') j)
    rw [h1] at h2
    exact_mod_cast le_antisymm h3 h2
  have hpres : ∀ z ∈ S, IncTop.StarPresented (30 * P.d) (ω z) (frontierConst P.d) :=
    fun z _ => starPresented_front Rf hRf1 (fun z => (e z).1.1) z
  have hLC : LeafwiseControlled LGq H B' := G.leafwise h P.L roots b (by linarith) hb
  set Bd : ℝ≥0∞ := (∏ z ∈ S, ENNReal.ofReal ((fun _ => frontierConst P.d) z)) *
    ENNReal.ofReal (P.L ^ (47 * (P.d : ℝ) + 5)) * regBound P n (LGq.incoherency Q.links) *
    ENNReal.ofReal (leafSizeProduct LGq B') with hBd
  have hBdt : Bd ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top) ?_)
      ENNReal.ofReal_ne_top
    · exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top
    · unfold regBound; exact ENNReal.ofReal_ne_top
  have hball := fun c₀ : Fin P.d → ℤ => (hRT p hp n hn s hps hsp).2 Rt θ G.rt hθ Q LGq G.wf hQs hdec G.layer_le
    G.root_pinned q0 q1 hq0 hq1 (G.root_le 0) (G.root_le 1) G.amb S ω (fun _ => frontierConst P.d) hpres H B'
    hLC 0 (latPt P.d c₀)
  have hplain : LGq.garden.IsPlain :=
    Comb.RootedSubforest.inducedGarden_plain (G := a.prime.data.garden a.prime.prime.1)
      (nativeCoupleForest a.prime.data a.prime.prime.1 q') (nativeCoupleForest_closed a.prime.data a.prime.prime.1 q')
  have hfc : ∀ k, Continuous fun ts : Fin 2 → ℝ =>
      kernelProt P.L P.γ P.δ LGq H (fun κ => IncTop.starWeight S ω κ) (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0
        (MkSlotsO.rootPins Rt s) k (fun _ => 0) 0 := fun k =>
    continuous_kernelProt_cpl P.L P.γ P.δ 0 LGq H _ 1
      (fun κ => norm_starWeight_front_le S Rf (fun z => (e z).1.1) κ) _ k
      (PL234.card_lone_le_of_plain hplain) (hLC.summable_coset hd hL k)
  have hrect := cplBox_eq_rect (q0 : ℝ) (q1 : ℝ) s Rt (fun h0 => by rw [hpin 0 h0]; exact hps.le)
    (fun h1 => by rw [hpin 1 h1]; exact hps.le)
  have hBc : timeBox (q0 : ℝ) (q1 : ℝ) ∩ {ts | ∀ j, Rt j → s ≤ ts j} ⊆ cell (cell2 q0 q1) := by
    intro ts hts
    rw [← timeBox_eq_cell]
    exact hts.1
  have hBi : timeBox (q0 : ℝ) (q1 : ℝ) ∩ {ts | ∀ j, Rt j → s ≤ ts j} ⊆
      closure (interior (timeBox (q0 : ℝ) (q1 : ℝ) ∩ {ts | ∀ j, Rt j → s ≤ ts j})) := by
    rw [hrect]
    refine rect_subset_closure_interior _ _ _ _ ?_ ?_
    · split_ifs with h0
      · have := hpin 0 h0; rw [show ((q0 : ℕ) : ℝ) = p from this]; exact hsp
      · linarith
    · split_ifs with h1
      · have := hpin 1 h1; rw [show ((q1 : ℕ) : ℝ) = p from this]; exact hsp
      · linarith
  obtain ⟨Λ, hΛ, wt, m, c, amp, hw0, hws, haS, hcen, hsum, hmass⟩ :=
    cenSup_of_balls hd hθ0 P.L (cell2 q0 q1) _ hBc hBi _ hfc Bd hBdt hball
  refine ⟨Λ, hΛ, wt, m, c, amp, hw0, hws, fun l k => Represents.snorm_le_one_pointwise _ (amp l) (haS l) k, haS,
    fun _ _ => hcen, fun ts hts n' _ _ _ => ?_, ?_⟩
  · rw [genSlotKer_cpl G]
    exact hsum ts (G.box hts) n'
  · have hcF0 : 0 ≤ frontierConst P.d := le_trans zero_le_one (one_le_frontierConst P.d)
    have hLSb : 0 ≤ slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
        (fun _ => b.toNNReal) (.inl q') := by
      unfold slotLeaf leafSizeProduct
      exact Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    have hsize : slotSize a.prime.data (.inl q') = 2 * n := hQs
    refine hmass.trans (le_trans ?_ hμ)
    unfold MkSlotsI.genSlotMass
    simp only [G.prot kSel, ↓reduceIte, G.selNative_empty kSel, Finset.prod_empty, mul_one, MkSlotsI.genLeaf,
      G.notCap, one_mul]
    rw [hsize]
    have hC0 : 0 ≤ rtCchi P.d * (MkSlots.capCsup P.d θ).toReal * rtSd P.d := by
      have := one_le_rtCchi P.d
      have := rtSd_nonneg P.d
      have : 0 ≤ (MkSlots.capCsup P.d θ).toReal := ENNReal.toReal_nonneg
      positivity
    refine le_of_eq_of_le ?_ (rtMass_le P C hC hC1 hδ hL hηγ _ Kp hC0 hKp S.card
      (slotNr a.prime.data a.prime.prime.1 (.inl q')) G.front_card n
      (slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) (.inl q')) hn1 _ hLSb)
    rw [hBd, Finset.prod_const, ENNReal.ofReal_pow hcF0]
    rfl

end CplFam

end WaveTurbulence.Flower.MkSlotsB
