/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FlowerDraft.Trees

/-!
# Flower-tree operators, part 1: definitions, analysis, linearity (packet X1)

* `fOp F b`: the flower-tree term `𝒥_F[b]` of an input `b` on `[p, p+1]`.
  - It is defined by root attachment: `𝒥_𝔣[b] = b` and
    `𝒥_{node i F T₁ T₂}[b](t) = ∫_p^t 𝒞₊(slot i ← 𝒥_F[b](s), 𝒥_{T₁}(s), 𝒥_{T₂}(s)) ds`, the middle slot
    conjugated. This is DH21 Prop 11.2: "attaching two sub-trees `𝒯_{1,2}` to a single node".
  - It is the operator with kernel `𝒥̃_F` (T (jtflower)); see `Flower-Kernel.lean`.
* `fOp_graft`: `𝒥_F[𝒥_H[b]] = 𝒥_{F.graft H}[b]`. This is pure definition-chasing.
* `Good`: continuous in time, with a summable majorant uniform in time. It contains `ZSpace` for `Λ > d`.
  `fOp F` preserves it (`good_fOp`) and is ℝ-linear on it (`fOp_add`, `fOp_neg`, `fOp_sum`).
-/

@[expose] public section

open MeasureTheory Finset Set

namespace WaveTurbulence.SysAPI

open FTree

/-- Arrays on `[p, p+1]`. -/
abbrev ArrI (p d : ℕ) : Type := Icc (p : ℝ) (p + 1) → (Fin d → ℤ) → ℂ

section Defs

variable (L γ δ : ℝ) {d : ℕ}

/-- `𝒞₊` with the stem input `u` in slot `i`, and `v, w` in the other two slots in order. The middle slot is
conjugated. -/
noncomputable def slotNonlin (i : Fin 3) (s : ℝ) (u v w : (Fin d → ℤ) → ℂ) : (Fin d → ℤ) → ℂ :=
  if i = 0 then aNonlin L γ δ 1 s u (fun m => (starRingEnd ℂ) (v m)) w
  else if i = 1 then aNonlin L γ δ 1 s v (fun m => (starRingEnd ℂ) (u m)) w
  else aNonlin L γ δ 1 s v (fun m => (starRingEnd ℂ) (w m)) u

/-- **The flower-tree term `𝒥_F[b]`** (DH21 Prop 11.2; T (jtflower) as an operator). -/
noncomputable def fOp (p : ℕ) (aP : (Fin d → ℤ) → ℂ) : FTree → ArrI p d → ArrI p d
  | .flower, b => b
  | .node i F T₁ T₂, b => fun t n => ∫ s in (p : ℝ)..t, slotNonlin L γ δ i s
      (Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) (fOp p aP F b) s)
      (treeTerm L γ δ p T₁ aP s) (treeTerm L γ δ p T₂ aP s) n

/-- **Grafting composes:** `𝒥_F[𝒥_H[b]] = 𝒥_{F.graft H}[b]`. -/
theorem fOp_graft (p : ℕ) (aP : (Fin d → ℤ) → ℂ) (F H : FTree) (b : ArrI p d) :
    fOp L γ δ p aP F (fOp L γ δ p aP H b) = fOp L γ δ p aP (F.graft H) b := by
  induction F with
  | flower => rfl
  | node i F T₁ T₂ ih =>
    funext t n
    simp only [fOp, graft]
    rw [ih]

theorem slotNonlin_zero (s : ℝ) (u v w : (Fin d → ℤ) → ℂ) :
    slotNonlin L γ δ 0 s u v w = aNonlin L γ δ 1 s u (fun m => (starRingEnd ℂ) (v m)) w := by
  simp [slotNonlin]

theorem slotNonlin_one (s : ℝ) (u v w : (Fin d → ℤ) → ℂ) :
    slotNonlin L γ δ 1 s u v w = aNonlin L γ δ 1 s v (fun m => (starRingEnd ℂ) (u m)) w := by
  simp [slotNonlin]

theorem slotNonlin_two (s : ℝ) (u v w : (Fin d → ℤ) → ℂ) :
    slotNonlin L γ δ 2 s u v w = aNonlin L γ δ 1 s v (fun m => (starRingEnd ℂ) (w m)) u := by
  simp [slotNonlin]

end Defs

/-! ## The convolution majorant -/

section Conv

variable {d : ℕ}

/-- `∑_q U(q₁) U(q₂) U(n − q₁ + q₂)`. -/
noncomputable def conv3 (U : (Fin d → ℤ) → ℝ) (n : Fin d → ℤ) : ℝ :=
  ∑' q : (Fin d → ℤ) × (Fin d → ℤ), U q.1 * U q.2 * U (n - q.1 + q.2)

variable {U : (Fin d → ℤ) → ℝ}

theorem summable_pair_mul (hU : Summable U) (hU0 : ∀ k, 0 ≤ U k) :
    Summable fun q : (Fin d → ℤ) × (Fin d → ℤ) => U q.1 * U q.2 :=
  summable_mul_of_summable_norm (f := U) (g := U)
    (by simpa [Real.norm_of_nonneg (hU0 _)] using hU) (by simpa [Real.norm_of_nonneg (hU0 _)] using hU)

theorem summable_conv3_family (hU : Summable U) (hU0 : ∀ k, 0 ≤ U k) (n : Fin d → ℤ) :
    Summable fun q : (Fin d → ℤ) × (Fin d → ℤ) => U q.1 * U q.2 * U (n - q.1 + q.2) :=
  Summable.of_nonneg_of_le (fun _ => mul_nonneg (mul_nonneg (hU0 _) (hU0 _)) (hU0 _))
    (fun _ => mul_le_mul_of_nonneg_left (hU.le_tsum _ fun _ _ => hU0 _)
      (mul_nonneg (hU0 _) (hU0 _))) ((summable_pair_mul hU hU0).mul_right _)

theorem conv3_nonneg (hU0 : ∀ k, 0 ≤ U k) (n : Fin d → ℤ) : 0 ≤ conv3 U n :=
  tsum_nonneg fun _ => mul_nonneg (mul_nonneg (hU0 _) (hU0 _)) (hU0 _)

theorem summable_conv3 (hU : Summable U) (hU0 : ∀ k, 0 ≤ U k) : Summable (conv3 U) := by
  let e : ((Fin d → ℤ) × (Fin d → ℤ)) × (Fin d → ℤ) ≃ (Fin d → ℤ) × ((Fin d → ℤ) × (Fin d → ℤ)) :=
    { toFun := fun x => (x.2 + x.1.1 - x.1.2, x.1)
      invFun := fun y => (y.2, y.1 - y.2.1 + y.2.2)
      left_inv := fun ⟨⟨a, b⟩, c⟩ => by simp only [Prod.mk.injEq, true_and]; abel
      right_inv := fun ⟨n, a, b⟩ => by simp only [Prod.mk.injEq, and_true]; abel }
  have hΨ : Summable fun x : ((Fin d → ℤ) × (Fin d → ℤ)) × (Fin d → ℤ) => U x.1.1 * U x.1.2 * U x.2 :=
    summable_mul_of_summable_norm (f := fun q : (Fin d → ℤ) × (Fin d → ℤ) => U q.1 * U q.2) (g := U)
      (by simpa [Real.norm_of_nonneg (mul_nonneg (hU0 _) (hU0 _))] using summable_pair_mul hU hU0)
      (by simpa [Real.norm_of_nonneg (hU0 _)] using hU)
  have hΦ : Summable fun y : (Fin d → ℤ) × ((Fin d → ℤ) × (Fin d → ℤ)) =>
      U y.2.1 * U y.2.2 * U (y.1 - y.2.1 + y.2.2) := by
    refine e.summable_iff.1 ?_
    convert hΨ using 1
    funext x
    show U x.1.1 * U x.1.2 * U (x.2 + x.1.1 - x.1.2 - x.1.1 + x.1.2) = U x.1.1 * U x.1.2 * U x.2
    congr 2
    abel
  exact hΦ.prod

variable (L γ δ : ℝ)

/-- `‖𝒞_ζ(f, g, h)_n‖ ≤ |c_ζ| · conv3 U n` for `f, g, h` dominated by a summable `U`. -/
theorem norm_aNonlin_le_conv3 (ζ : ℤ) (t : ℝ) {f g h : (Fin d → ℤ) → ℂ} (hU : Summable U)
    (hU0 : ∀ k, 0 ≤ U k) (hf : ∀ k, ‖f k‖ ≤ U k) (hg : ∀ k, ‖g k‖ ≤ U k) (hh : ∀ k, ‖h k‖ ≤ U k)
    (n : Fin d → ℤ) :
    ‖aNonlin L γ δ ζ t f g h n‖ ≤
      ‖((δ / (2 * L ^ ((d : ℝ) - γ)) : ℝ) : ℂ) * (Complex.I * ζ)‖ * conv3 U n := by
  rw [aNonlin_eq_tsum_aNonlinTerm, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hfs : Summable fun k => ‖f k‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hf hU
  have hgs : Summable fun k => ‖g k‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hg hU
  have hhb : ∀ k, ‖h k‖ ≤ ∑' k, U k := fun k => (hh k).trans (hU.le_tsum k fun _ _ => hU0 _)
  have hsum := summable_aNonlinTerm L γ δ ζ t hfs hgs hhb n
  refine (norm_tsum_le_tsum_norm hsum).trans
    (Summable.tsum_le_tsum (fun q => (norm_aNonlinTerm_le L γ δ ζ t f g h n q).trans ?_) hsum
      (summable_conv3_family hU hU0 n))
  exact mul_le_mul (mul_le_mul (hf _) (hg _) (norm_nonneg _) (hU0 _)) (hh _) (norm_nonneg _)
    (mul_nonneg (hU0 _) (hU0 _))

end Conv

/-! ## Majorants of the tree terms -/

section TreeMaj

variable (L γ δ : ℝ) {d : ℕ}

/-- A summable majorant of `s ↦ 𝒥_T(s)_k` on `s ≤ p + 1`. -/
noncomputable def treeMaj (p : ℕ) (T : TTree) (aP : (Fin d → ℤ) → ℂ) (k : Fin d → ℤ) : ℝ :=
  ‖treePrefactor L γ δ d T‖ * (boxVol T (p : ℝ) (p + 1) *
    ∑' κ : TreeDecoration T d k, ∏ ℓ : GLeaf (single T), ‖aP (κ.1 ℓ.toNode)‖)

theorem treeMaj_nonneg (p : ℕ) (T : TTree) (aP : (Fin d → ℤ) → ℂ) (k : Fin d → ℤ) :
    0 ≤ treeMaj L γ δ p T aP k :=
  mul_nonneg (norm_nonneg _) (mul_nonneg (boxVol_nonneg _ _ _)
    (tsum_nonneg fun _ => Finset.prod_nonneg fun _ _ => norm_nonneg _))

theorem norm_treeTerm_le_treeMaj (p : ℕ) (T : TTree) {aP : (Fin d → ℤ) → ℂ}
    (haP : Summable fun k => ‖aP k‖) {s : ℝ} (hs : s ≤ p + 1) (k : Fin d → ℤ) :
    ‖treeTerm L γ δ p T aP s k‖ ≤ treeMaj L γ δ p T aP k :=
  (norm_treeTerm_le L γ δ p T haP s k).trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (boxVol_mono T (p : ℝ) hs)
      (tsum_nonneg fun _ => Finset.prod_nonneg fun _ _ => norm_nonneg _)) (norm_nonneg _))

theorem summable_treeMaj (p : ℕ) (T : TTree) {aP : (Fin d → ℤ) → ℂ}
    (haP : Summable fun k => ‖aP k‖) : Summable (treeMaj L γ δ p T aP) := by
  have hg := summable_leafNorm_sigma T haP
  have hg0 : ∀ x : (Σ n : Fin d → ℤ, TreeDecoration T d n),
      0 ≤ ∏ ℓ : GLeaf (single T), ‖aP (x.2.1 ℓ.toNode)‖ :=
    fun x => Finset.prod_nonneg fun _ _ => norm_nonneg _
  obtain ⟨-, hgn⟩ := (summable_sigma_of_nonneg hg0).1 hg
  exact (hgn.mul_left _).mul_left _

end TreeMaj

/-! ## Good inputs -/

section Good

variable {d : ℕ}

/-- **Good inputs**: continuous in time for each mode, with a summable majorant uniform in time. -/
structure Good (p : ℕ) (b : ArrI p d) : Prop where
  cont : ∀ n, Continuous fun t => b t n
  maj : ∃ U : (Fin d → ℤ) → ℝ, Summable U ∧ (∀ k, 0 ≤ U k) ∧ ∀ t n, ‖b t n‖ ≤ U n

theorem Good.add {p : ℕ} {b c : ArrI p d} (hb : Good p b) (hc : Good p c) : Good p (b + c) := by
  obtain ⟨U, hU, hU0, hbU⟩ := hb.maj
  obtain ⟨V, hV, hV0, hcV⟩ := hc.maj
  exact ⟨fun n => (hb.cont n).add (hc.cont n), U + V, hU.add hV, fun k => add_nonneg (hU0 k) (hV0 k),
    fun t n => (norm_add_le _ _).trans (add_le_add (hbU t n) (hcV t n))⟩

theorem Good.neg {p : ℕ} {b : ArrI p d} (hb : Good p b) : Good p (-b) := by
  obtain ⟨U, hU, hU0, hbU⟩ := hb.maj
  exact ⟨fun n => (hb.cont n).neg, U, hU, hU0, fun t n => by simpa using hbU t n⟩

theorem Good.sub {p : ℕ} {b c : ArrI p d} (hb : Good p b) (hc : Good p c) : Good p (b - c) := by
  rw [sub_eq_add_neg]
  exact hb.add hc.neg

theorem Good.zero (p : ℕ) : Good p (0 : ArrI p d) :=
  ⟨fun _ => continuous_const, 0, summable_zero, fun _ => le_rfl, fun _ _ => by simp⟩

theorem Good.sum {p : ℕ} {ι : Type*} (S : Finset ι) {c : ι → ArrI p d} (hc : ∀ i ∈ S, Good p (c i)) :
    Good p (∑ i ∈ S, c i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using Good.zero p
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact (hc a (Finset.mem_insert_self a S)).add (ih fun i hi => hc i (Finset.mem_insert_of_mem hi))

theorem Good.iccExtend {p : ℕ} {b : ArrI p d} (hb : Good p b) (n : Fin d → ℤ) :
    Continuous fun s => Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s n := by
  have : (fun s => Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s n) =
      (fun t => b t n) ∘ Set.projIcc (p : ℝ) (p + 1) (by linarith) := rfl
  rw [this]
  exact (hb.cont n).comp continuous_projIcc

end Good

/-! ## Integrability, closure, linearity -/

section Analysis

variable (L γ δ : ℝ) {d : ℕ}

/-- The slot integrand is strongly measurable. -/
theorem stronglyMeasurable_slot (p : ℕ) {aP : (Fin d → ℤ) → ℂ} (haP : Summable fun k => ‖aP k‖)
    (i : Fin 3) (T₁ T₂ : TTree) {b : ArrI p d} (hb : Good p b) (n : Fin d → ℤ) :
    StronglyMeasurable fun s => slotNonlin L γ δ i s
      (Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s)
      (treeTerm L γ δ p T₁ aP s) (treeTerm L γ δ p T₂ aP s) n := by
  obtain ⟨U, hU, hU0, hbU⟩ := hb.maj
  have hB : ∀ k, StronglyMeasurable fun s => Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s k :=
    fun k => (hb.iccExtend k).stronglyMeasurable
  have hBs : ∀ s, Summable fun k => ‖Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s k‖ :=
    fun s => Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => hbU _ k) hU
  have h1 := fun k => stronglyMeasurable_treeTerm L γ δ p T₁ haP k
  have h2 := fun k => stronglyMeasurable_treeTerm L γ δ p T₂ haP k
  have h1s := fun s => summable_norm_treeTerm L γ δ p T₁ haP s
  have h2s := fun s => summable_norm_treeTerm L γ δ p T₂ haP s
  fin_cases i
  · simp only [Fin.zero_eta, slotNonlin_zero]
    exact stronglyMeasurable_aNonlin L γ δ hB h1 h2 hBs h1s h2s n
  · simp only [Fin.mk_one, slotNonlin_one]
    exact stronglyMeasurable_aNonlin L γ δ h1 hB h2 h1s hBs h2s n
  · simp only [Fin.reduceFinMk, slotNonlin_two]
    exact stronglyMeasurable_aNonlin L γ δ h1 h2 hB h1s h2s hBs n

/-- The slot integrand is bounded by `|c₊| · conv3 (U + 𝒥-majorants)`. -/
theorem norm_slot_le (p : ℕ) {aP : (Fin d → ℤ) → ℂ} (haP : Summable fun k => ‖aP k‖)
    (i : Fin 3) (T₁ T₂ : TTree) {U : (Fin d → ℤ) → ℝ} (hU : Summable U) (hU0 : ∀ k, 0 ≤ U k)
    {u : (Fin d → ℤ) → ℂ} (hu : ∀ k, ‖u k‖ ≤ U k) {s : ℝ} (hs : s ≤ p + 1) (n : Fin d → ℤ) :
    ‖slotNonlin L γ δ i s u (treeTerm L γ δ p T₁ aP s) (treeTerm L γ δ p T₂ aP s) n‖ ≤
      ‖((δ / (2 * L ^ ((d : ℝ) - γ)) : ℝ) : ℂ) * (Complex.I * ((1 : ℤ) : ℂ))‖ *
        conv3 (U + treeMaj L γ δ p T₁ aP + treeMaj L γ δ p T₂ aP) n := by
  set V := U + treeMaj L γ δ p T₁ aP + treeMaj L γ δ p T₂ aP
  have hV : Summable V := (hU.add (summable_treeMaj L γ δ p T₁ haP)).add (summable_treeMaj L γ δ p T₂ haP)
  have hV0 : ∀ k, 0 ≤ V k := fun k =>
    add_nonneg (add_nonneg (hU0 k) (treeMaj_nonneg L γ δ p T₁ aP k)) (treeMaj_nonneg L γ δ p T₂ aP k)
  have hu' : ∀ k, ‖u k‖ ≤ V k := fun k => (hu k).trans (by
    simp only [V, Pi.add_apply]
    linarith [treeMaj_nonneg L γ δ p T₁ aP k, treeMaj_nonneg L γ δ p T₂ aP k])
  have h1 : ∀ k, ‖treeTerm L γ δ p T₁ aP s k‖ ≤ V k := fun k =>
    (norm_treeTerm_le_treeMaj L γ δ p T₁ haP hs k).trans (by
      simp only [V, Pi.add_apply]
      linarith [hU0 k, treeMaj_nonneg L γ δ p T₂ aP k])
  have h2 : ∀ k, ‖treeTerm L γ δ p T₂ aP s k‖ ≤ V k := fun k =>
    (norm_treeTerm_le_treeMaj L γ δ p T₂ haP hs k).trans (by
      simp only [V, Pi.add_apply]
      linarith [hU0 k, treeMaj_nonneg L γ δ p T₁ aP k])
  have hc1 : ∀ k, ‖(starRingEnd ℂ) (treeTerm L γ δ p T₁ aP s k)‖ ≤ V k := fun k => by
    rw [Complex.norm_conj]; exact h1 k
  have hcu : ∀ k, ‖(starRingEnd ℂ) (u k)‖ ≤ V k := fun k => by rw [Complex.norm_conj]; exact hu' k
  have hc2 : ∀ k, ‖(starRingEnd ℂ) (treeTerm L γ δ p T₂ aP s k)‖ ≤ V k := fun k => by
    rw [Complex.norm_conj]; exact h2 k
  fin_cases i
  · simp only [Fin.zero_eta, slotNonlin_zero]
    exact norm_aNonlin_le_conv3 L γ δ 1 s hV hV0 hu' hc1 h2 n
  · simp only [Fin.mk_one, slotNonlin_one]
    exact norm_aNonlin_le_conv3 L γ δ 1 s hV hV0 h1 hcu h2 n
  · simp only [Fin.reduceFinMk, slotNonlin_two]
    exact norm_aNonlin_le_conv3 L γ δ 1 s hV hV0 h1 hc2 hu' n

/-- **Integrability** of the slot integrand on `[p, t]`, `t ∈ [p, p+1]`. -/
theorem intervalIntegrable_slot (p : ℕ) {aP : (Fin d → ℤ) → ℂ} (haP : Summable fun k => ‖aP k‖)
    (i : Fin 3) (T₁ T₂ : TTree) {b : ArrI p d} (hb : Good p b) {t : ℝ} (ht : t ∈ Icc (p : ℝ) (p + 1))
    (n : Fin d → ℤ) :
    IntervalIntegrable (fun s => slotNonlin L γ δ i s
      (Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s)
      (treeTerm L γ δ p T₁ aP s) (treeTerm L γ δ p T₂ aP s) n) volume p t := by
  obtain ⟨U, hU, hU0, hbU⟩ := hb.maj
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := ‖((δ / (2 * L ^ ((d : ℝ) - γ)) : ℝ) : ℂ) *
      (Complex.I * ((1 : ℤ) : ℂ))‖ * conv3 (U + treeMaj L γ δ p T₁ aP + treeMaj L γ δ p T₂ aP) n)
    (by rw [Set.uIoc]; exact measure_Ioc_lt_top.ne)
    (stronglyMeasurable_slot L γ δ p haP i T₁ T₂ hb n).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_uIoc fun s hs => ?_)
  have hs' : s ≤ p + 1 := by
    rw [Set.uIoc] at hs
    exact hs.2.trans (max_le (by linarith) ht.2)
  exact norm_slot_le L γ δ p haP i T₁ T₂ hU hU0 (fun k => hbU _ k) hs' n

/-- **Closure:** `𝒥_F[b]` is good for good `b`. -/
theorem good_fOp (p : ℕ) {aP : (Fin d → ℤ) → ℂ} (haP : Summable fun k => ‖aP k‖) {b : ArrI p d}
    (hb : Good p b) : ∀ F : FTree, Good p (fOp L γ δ p aP F b)
  | .flower => hb
  | .node i F T₁ T₂ => by
    have hF := good_fOp p haP hb F
    obtain ⟨U, hU, hU0, hbU⟩ := hF.maj
    refine ⟨fun n => ?_, fun n => ‖((δ / (2 * L ^ ((d : ℝ) - γ)) : ℝ) : ℂ) *
        (Complex.I * ((1 : ℤ) : ℂ))‖ * conv3 (U + treeMaj L γ δ p T₁ aP + treeMaj L γ δ p T₂ aP) n,
      ?_, ?_, ?_⟩
    · have hint := intervalIntegrable_slot L γ δ p haP i T₁ T₂ hF
        (t := p + 1) ⟨by linarith, le_rfl⟩ n
      have hco := intervalIntegral.continuousOn_primitive_interval' hint
        (a := (p : ℝ)) (by rw [Set.uIcc_of_le (by linarith)]; exact ⟨le_rfl, by linarith⟩)
      rw [Set.uIcc_of_le (by linarith)] at hco
      exact continuousOn_iff_continuous_domRestrict.1 hco
    · have hV : Summable (U + treeMaj L γ δ p T₁ aP + treeMaj L γ δ p T₂ aP) :=
        (hU.add (summable_treeMaj L γ δ p T₁ haP)).add (summable_treeMaj L γ δ p T₂ haP)
      have hV0 : ∀ k, 0 ≤ (U + treeMaj L γ δ p T₁ aP + treeMaj L γ δ p T₂ aP) k := fun k =>
        add_nonneg (add_nonneg (hU0 k) (treeMaj_nonneg L γ δ p T₁ aP k))
          (treeMaj_nonneg L γ δ p T₂ aP k)
      exact (summable_conv3 hV hV0).mul_left _
    · intro k
      have hV0 : ∀ k, 0 ≤ (U + treeMaj L γ δ p T₁ aP + treeMaj L γ δ p T₂ aP) k := fun k =>
        add_nonneg (add_nonneg (hU0 k) (treeMaj_nonneg L γ δ p T₁ aP k))
          (treeMaj_nonneg L γ δ p T₂ aP k)
      exact mul_nonneg (norm_nonneg _) (conv3_nonneg hV0 k)
    · intro t n
      have ht := t.2
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (p : ℝ)) (b := (t : ℝ))
        (C := ‖((δ / (2 * L ^ ((d : ℝ) - γ)) : ℝ) : ℂ) * (Complex.I * ((1 : ℤ) : ℂ))‖ *
          conv3 (U + treeMaj L γ δ p T₁ aP + treeMaj L γ δ p T₂ aP) n)
        (f := fun s => slotNonlin L γ δ i s (Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1)
          (fOp L γ δ p aP F b) s) (treeTerm L γ δ p T₁ aP s) (treeTerm L γ δ p T₂ aP s) n)
        fun s hs => by
          have hs' : s ≤ p + 1 := by
            rw [Set.uIoc] at hs
            exact hs.2.trans (max_le (by linarith) ht.2)
          exact norm_slot_le L γ δ p haP i T₁ T₂ hU hU0 (fun k => hbU _ k) hs' n
      have hC : 0 ≤ ‖((δ / (2 * L ^ ((d : ℝ) - γ)) : ℝ) : ℂ) * (Complex.I * ((1 : ℤ) : ℂ))‖ *
          conv3 (U + treeMaj L γ δ p T₁ aP + treeMaj L γ δ p T₂ aP) n :=
        mul_nonneg (norm_nonneg _) (conv3_nonneg (fun k => add_nonneg (add_nonneg (hU0 k)
          (treeMaj_nonneg L γ δ p T₁ aP k)) (treeMaj_nonneg L γ δ p T₂ aP k)) n)
      have h1 : |(t : ℝ) - p| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [ht.1, ht.2]
      exact h.trans (by nlinarith)

/-! ### Linearity of `𝒞₊` in one slot -/

theorem aNonlinTerm_add_left (ζ : ℤ) (t : ℝ) (f₁ f₂ g h : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ) (q) :
    aNonlinTerm L γ δ ζ t (f₁ + f₂) g h n q =
      aNonlinTerm L γ δ ζ t f₁ g h n q + aNonlinTerm L γ δ ζ t f₂ g h n q := by
  unfold aNonlinTerm; simp only [Pi.add_apply]; ring

theorem aNonlinTerm_add_mid (ζ : ℤ) (t : ℝ) (f g₁ g₂ h : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ) (q) :
    aNonlinTerm L γ δ ζ t f (g₁ + g₂) h n q =
      aNonlinTerm L γ δ ζ t f g₁ h n q + aNonlinTerm L γ δ ζ t f g₂ h n q := by
  unfold aNonlinTerm; simp only [Pi.add_apply]; ring

theorem aNonlinTerm_add_right (ζ : ℤ) (t : ℝ) (f g h₁ h₂ : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ) (q) :
    aNonlinTerm L γ δ ζ t f g (h₁ + h₂) n q =
      aNonlinTerm L γ δ ζ t f g h₁ n q + aNonlinTerm L γ δ ζ t f g h₂ n q := by
  unfold aNonlinTerm; simp only [Pi.add_apply]; ring

/-- `𝒞₊` is additive in the stem slot, for inputs dominated by a summable `U`. -/
theorem slotNonlin_add (i : Fin 3) (s : ℝ) {u₁ u₂ v w : (Fin d → ℤ) → ℂ} {U : (Fin d → ℤ) → ℝ}
    (hU : Summable U) (hU0 : ∀ k, 0 ≤ U k) (h₁ : ∀ k, ‖u₁ k‖ ≤ U k) (h₂ : ∀ k, ‖u₂ k‖ ≤ U k)
    (hv : ∀ k, ‖v k‖ ≤ U k) (hw : ∀ k, ‖w k‖ ≤ U k) (n : Fin d → ℤ) :
    slotNonlin L γ δ i s (u₁ + u₂) v w n =
      slotNonlin L γ δ i s u₁ v w n + slotNonlin L γ δ i s u₂ v w n := by
  have sm : ∀ {x : (Fin d → ℤ) → ℂ}, (∀ k, ‖x k‖ ≤ U k) → Summable fun k => ‖x k‖ :=
    fun hx => Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hx hU
  have smc : ∀ {x : (Fin d → ℤ) → ℂ}, (∀ k, ‖x k‖ ≤ U k) →
      Summable fun k => ‖(starRingEnd ℂ) (x k)‖ := fun hx => by simpa using sm hx
  have bd : ∀ {x : (Fin d → ℤ) → ℂ}, (∀ k, ‖x k‖ ≤ U k) → ∀ k, ‖x k‖ ≤ ∑' k, U k :=
    fun hx k => (hx k).trans (hU.le_tsum k fun _ _ => hU0 _)
  fin_cases i
  · simp only [Fin.zero_eta, slotNonlin_zero, aNonlin_eq_tsum_aNonlinTerm, aNonlinTerm_add_left]
    rw [Summable.tsum_add (summable_aNonlinTerm L γ δ 1 s (sm h₁) (smc hv) (bd hw) n).of_norm
      (summable_aNonlinTerm L γ δ 1 s (sm h₂) (smc hv) (bd hw) n).of_norm, mul_add]
  · have hconj : (fun m => (starRingEnd ℂ) ((u₁ + u₂) m)) =
        (fun m => (starRingEnd ℂ) (u₁ m)) + fun m => (starRingEnd ℂ) (u₂ m) := by
      funext m; simp
    simp only [Fin.mk_one, slotNonlin_one, aNonlin_eq_tsum_aNonlinTerm, hconj, aNonlinTerm_add_mid]
    rw [Summable.tsum_add (summable_aNonlinTerm L γ δ 1 s (sm hv) (smc h₁) (bd hw) n).of_norm
      (summable_aNonlinTerm L γ δ 1 s (sm hv) (smc h₂) (bd hw) n).of_norm, mul_add]
  · simp only [Fin.reduceFinMk, slotNonlin_two, aNonlin_eq_tsum_aNonlinTerm, aNonlinTerm_add_right]
    rw [Summable.tsum_add (summable_aNonlinTerm L γ δ 1 s (sm hv) (smc hw) (bd h₁) n).of_norm
      (summable_aNonlinTerm L γ δ 1 s (sm hv) (smc hw) (bd h₂) n).of_norm, mul_add]

/-- `𝒞₊` is odd in the stem slot. -/
theorem slotNonlin_neg (i : Fin 3) (s : ℝ) (u v w : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ) :
    slotNonlin L γ δ i s (-u) v w n = -slotNonlin L γ δ i s u v w n := by
  fin_cases i
  · simp only [Fin.zero_eta, slotNonlin_zero, aNonlin_eq_tsum_aNonlinTerm]
    rw [← mul_neg, ← tsum_neg]
    congr 2; funext q; unfold aNonlinTerm; simp only [Pi.neg_apply]; ring
  · simp only [Fin.mk_one, slotNonlin_one, aNonlin_eq_tsum_aNonlinTerm]
    rw [← mul_neg, ← tsum_neg]
    congr 2; funext q; unfold aNonlinTerm; simp only [Pi.neg_apply, map_neg]; ring
  · simp only [Fin.reduceFinMk, slotNonlin_two, aNonlin_eq_tsum_aNonlinTerm]
    rw [← mul_neg, ← tsum_neg]
    congr 2; funext q; unfold aNonlinTerm; simp only [Pi.neg_apply]; ring

/-! ### Linearity of `𝒥_F` -/

theorem iccExtend_add {p : ℕ} (b c : ArrI p d) (s : ℝ) :
    Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) (b + c) s =
      Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s +
        Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) c s := rfl

theorem iccExtend_neg {p : ℕ} (b : ArrI p d) (s : ℝ) :
    Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) (-b) s =
      -Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s := rfl

theorem fOp_add (p : ℕ) {aP : (Fin d → ℤ) → ℂ} (haP : Summable fun k => ‖aP k‖) {b c : ArrI p d}
    (hb : Good p b) (hc : Good p c) :
    ∀ F : FTree, fOp L γ δ p aP F (b + c) = fOp L γ δ p aP F b + fOp L γ δ p aP F c
  | .flower => rfl
  | .node i F T₁ T₂ => by
    have ih := fOp_add p haP hb hc F
    have hFb := good_fOp L γ δ p haP hb F
    have hFc := good_fOp L γ δ p haP hc F
    obtain ⟨U, hU, hU0, hbU⟩ := hFb.maj
    obtain ⟨V, hV, hV0, hcV⟩ := hFc.maj
    funext t n
    simp only [fOp, Pi.add_apply]
    rw [ih, ← intervalIntegral.integral_add (intervalIntegrable_slot L γ δ p haP i T₁ T₂ hFb t.2 n)
      (intervalIntegrable_slot L γ δ p haP i T₁ T₂ hFc t.2 n)]
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hs' : s ≤ p + 1 := by
      rw [Set.uIcc] at hs
      exact hs.2.trans (max_le (by linarith) t.2.2)
    set W := U + V + treeMaj L γ δ p T₁ aP + treeMaj L γ δ p T₂ aP
    have hW : Summable W := ((hU.add hV).add (summable_treeMaj L γ δ p T₁ haP)).add
      (summable_treeMaj L γ δ p T₂ haP)
    have hm1 := treeMaj_nonneg L γ δ p T₁ aP
    have hm2 := treeMaj_nonneg L γ δ p T₂ aP
    have hW0 : ∀ k, 0 ≤ W k := fun k => by
      simp only [W, Pi.add_apply]; linarith [hU0 k, hV0 k, hm1 k, hm2 k]
    refine (iccExtend_add _ _ s ▸ slotNonlin_add L γ δ i s hW hW0 (fun k => ?_) (fun k => ?_)
      (fun k => ?_) (fun k => ?_) n)
    · refine (hbU _ k).trans ?_
      simp only [W, Pi.add_apply]; linarith [hV0 k, hm1 k, hm2 k]
    · refine (hcV _ k).trans ?_
      simp only [W, Pi.add_apply]; linarith [hU0 k, hm1 k, hm2 k]
    · refine (norm_treeTerm_le_treeMaj L γ δ p T₁ haP hs' k).trans ?_
      simp only [W, Pi.add_apply]; linarith [hU0 k, hV0 k, hm2 k]
    · refine (norm_treeTerm_le_treeMaj L γ δ p T₂ haP hs' k).trans ?_
      simp only [W, Pi.add_apply]; linarith [hU0 k, hV0 k, hm1 k]

theorem fOp_neg (p : ℕ) (aP : (Fin d → ℤ) → ℂ) (b : ArrI p d) :
    ∀ F : FTree, fOp L γ δ p aP F (-b) = -fOp L γ δ p aP F b
  | .flower => rfl
  | .node i F T₁ T₂ => by
    have ih := fOp_neg p aP b F
    funext t n
    simp only [fOp, Pi.neg_apply]
    rw [ih, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [iccExtend_neg, slotNonlin_neg]

theorem fOp_sub (p : ℕ) {aP : (Fin d → ℤ) → ℂ} (haP : Summable fun k => ‖aP k‖) {b c : ArrI p d}
    (hb : Good p b) (hc : Good p c) (F : FTree) :
    fOp L γ δ p aP F (b - c) = fOp L γ δ p aP F b - fOp L γ δ p aP F c := by
  rw [sub_eq_add_neg, fOp_add L γ δ p haP hb hc.neg, fOp_neg, ← sub_eq_add_neg]

theorem fOp_zero (p : ℕ) (aP : (Fin d → ℤ) → ℂ) (F : FTree) :
    fOp L γ δ p aP F (0 : ArrI p d) = 0 := by
  have h := fOp_neg L γ δ p aP (0 : ArrI p d) F
  rw [neg_zero] at h
  have : (2 : ℂ) • fOp L γ δ p aP F (0 : ArrI p d) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    exact neg_add_cancel _
  simpa using this

theorem fOp_sum (p : ℕ) {aP : (Fin d → ℤ) → ℂ} (haP : Summable fun k => ‖aP k‖) {ι : Type*}
    (S : Finset ι) {c : ι → ArrI p d} (hc : ∀ i ∈ S, Good p (c i)) (F : FTree) :
    fOp L γ δ p aP F (∑ i ∈ S, c i) = ∑ i ∈ S, fOp L γ δ p aP F (c i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [fOp_zero]
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      fOp_add L γ δ p haP (hc a (Finset.mem_insert_self a S))
        (Good.sum S fun i hi => hc i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hc i (Finset.mem_insert_of_mem hi)]

end Analysis

end WaveTurbulence.SysAPI
