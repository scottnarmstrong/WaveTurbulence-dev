/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3Core
public import WaveTurbulence.Foundations.XChain.FlowerDraft.X2Couple

/-!
# X3: measurability of the couple quantities in (data, time)

All quantities are functions of a parameter `a ∈ α` (any measurable space) through data `B a` and
time `T a`. The two uses:
- `α = Ω × ℝ` with `B (ω, t) = a(ω, p)` and `T (ω, t) = t`: joint measurability for Tonelli (Part 1);
- `α = ((Fin d → ℤ) → ℂ)`: measurability in the data, for the excluded event.

The data are assumed summable at every parameter. `sumMod` replaces a non-summable datum by `0`,
which changes nothing on the event `Fev p`.

The proofs are DuhMeas's `stronglyMeasurable_tsum`, `stronglyMeasurable_treeTerm` and
`stronglyMeasurable_aNonlin` (`../duhamel/src/SysDraft/DuhMeas.lean`), with the time line `ℝ`
replaced by `α`.
-/

@[expose] public section

open WaveTurbulence.X2E
namespace WaveTurbulence.Fixedpt

open MeasureTheory Set SysAPI
open scoped ENNReal

variable (L γ δ : ℝ) {d : ℕ}

/-! ## Summable data -/

section Data

/-- The summable data form a measurable set. -/
theorem measurableSet_summable_norm :
    MeasurableSet {b : (Fin d → ℤ) → ℂ | Summable fun m => ‖b m‖} := by
  have h : {b : (Fin d → ℤ) → ℂ | Summable fun m => ‖b m‖} =
      {b | ∑' m, ((‖b m‖₊ : NNReal) : ℝ≥0∞) ≠ ⊤} := by
    ext b
    show (Summable fun m => ‖b m‖) ↔ ∑' m, ((‖b m‖₊ : NNReal) : ℝ≥0∞) ≠ ⊤
    rw [ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe]
    simp only [coe_nnnorm]
  rw [h]
  exact (Measurable.tsum fun m => (measurable_pi_apply m).nnnorm.coe_nnreal_ennreal)
    (measurableSet_singleton ⊤).compl

open Classical in
/-- A non-summable datum replaced by `0`. -/
noncomputable def sumMod (b : (Fin d → ℤ) → ℂ) : (Fin d → ℤ) → ℂ :=
  if Summable fun m => ‖b m‖ then b else 0

theorem sumMod_of_summable {b : (Fin d → ℤ) → ℂ} (hb : Summable fun m => ‖b m‖) : sumMod b = b := by
  simp [sumMod, hb]

theorem summable_sumMod (b : (Fin d → ℤ) → ℂ) : Summable fun m => ‖sumMod b m‖ := by
  unfold sumMod
  split_ifs with h
  · exact h
  · simp

variable {α : Type*} [MeasurableSpace α]

theorem stronglyMeasurable_sumMod {B : α → (Fin d → ℤ) → ℂ} (hB : ∀ k, StronglyMeasurable fun a => B a k)
    (k : Fin d → ℤ) : StronglyMeasurable fun a => sumMod (B a) k := by
  classical
  have hBm : Measurable B := measurable_pi_iff.mpr fun k => (hB k).measurable
  have hS : MeasurableSet {a | Summable fun m => ‖B a m‖} := hBm measurableSet_summable_norm
  have : (fun a => sumMod (B a) k) = fun a => if Summable (fun m => ‖B a m‖) then B a k else 0 := by
    funext a
    unfold sumMod
    split_ifs <;> rfl
  rw [this]
  exact StronglyMeasurable.ite hS (hB k) stronglyMeasurable_const

end Data

/-! ## Parametrized measurability -/

section Param

variable {α : Type*} [MeasurableSpace α]

/-- `stronglyMeasurable_tsum` of DuhMeas, over a general parameter space. -/
theorem stronglyMeasurable_tsum' {ι : Type*} [Countable ι] {f : ι → α → ℂ}
    (hf : ∀ i, StronglyMeasurable (f i)) (hs : ∀ a, Summable fun i => f i a) :
    StronglyMeasurable fun a => ∑' i, f i a :=
  stronglyMeasurable_of_tendsto (Filter.atTop : Filter (Finset ι))
    (fun F => Finset.stronglyMeasurable_fun_sum F fun i _ => hf i)
    (tendsto_pi_nhds.2 fun a => (hs a).hasSum)

theorem stronglyMeasurable_zpowSign (ζ : ℤˣ) {f : α → ℂ} (hf : StronglyMeasurable f) :
    StronglyMeasurable fun a => zpowSign ζ (f a) := by
  unfold zpowSign
  split_ifs
  · exact hf
  · exact Complex.continuous_conj.comp_stronglyMeasurable hf

theorem stronglyMeasurable_leafProd (S : TTree) {B : α → (Fin d → ℤ) → ℂ}
    (hB : ∀ k, StronglyMeasurable fun a => B a k) (κ : GNode (single S) → (Fin d → ℤ)) :
    StronglyMeasurable fun a => leafProd S (B a) κ := by
  unfold leafProd
  exact Finset.stronglyMeasurable_fun_prod _ fun ℓ _ => stronglyMeasurable_zpowSign _ (hB _)

variable {B : α → (Fin d → ℤ) → ℂ} {T : α → ℝ} (hB : ∀ k, StronglyMeasurable fun a => B a k)
  (hBs : ∀ a, Summable fun k => ‖B a k‖) (hT : Measurable T)

include hB hBs hT in
theorem stronglyMeasurable_treeTerm' (p : ℕ) (S : TTree) (n : Fin d → ℤ) :
    StronglyMeasurable fun a => treeTerm L γ δ p S (B a) (T a) n := by
  simp only [treeTerm_eq, treeSummand_eq]
  refine stronglyMeasurable_const.mul (stronglyMeasurable_tsum' (fun κ => ?_) fun a =>
    (summable_treeSummand L γ δ p S (hBs a) (T a) n).of_norm)
  exact (stronglyMeasurable_const.mul ((stronglyMeasurable_timeInt L γ δ S κ.1 p).comp_measurable hT)).mul
    (stronglyMeasurable_leafProd S hB κ.1)

include hB hBs hT in
theorem stronglyMeasurable_treeTermN' (p N : ℕ) (n : Fin d → ℤ) :
    StronglyMeasurable fun a => treeTermN L γ δ p N (B a) (T a) n := by
  simp only [treeTermN_eq_sum]
  exact Finset.stronglyMeasurable_fun_sum _ fun S _ => stronglyMeasurable_treeTerm' L γ δ hB hBs hT p S n

include hB hBs hT in
theorem stronglyMeasurable_aTr' (p Ntr : ℕ) (n : Fin d → ℤ) :
    StronglyMeasurable fun a => aTr L γ δ p Ntr (B a) (T a) n := by
  unfold aTr
  exact Finset.stronglyMeasurable_fun_sum _ fun N _ => stronglyMeasurable_treeTermN' L γ δ hB hBs hT p N n

omit hB hBs hT in
/-- `stronglyMeasurable_aNonlin` of DuhMeas, over a general parameter space. -/
theorem stronglyMeasurable_aNonlin' {F G H : α → (Fin d → ℤ) → ℂ}
    (hF : ∀ k, StronglyMeasurable fun a => F a k) (hG : ∀ k, StronglyMeasurable fun a => G a k)
    (hH : ∀ k, StronglyMeasurable fun a => H a k) (hFs : ∀ a, Summable fun k => ‖F a k‖)
    (hGs : ∀ a, Summable fun k => ‖G a k‖) (hHs : ∀ a, Summable fun k => ‖H a k‖) (hT : Measurable T)
    (n : Fin d → ℤ) :
    StronglyMeasurable fun a =>
      aNonlin L γ δ 1 (T a) (F a) (fun k => (starRingEnd ℂ) (G a k)) (H a) n := by
  simp only [aNonlin_eq_tsum_aNonlinTerm]
  refine stronglyMeasurable_const.mul (stronglyMeasurable_tsum' (fun q => ?_) fun a =>
    (summable_aNonlinTerm L γ δ 1 (T a) (hFs a) (by simpa using hGs a)
      (norm_le_tsum_norm (hHs a)) n).of_norm)
  unfold aNonlinTerm
  refine (((stronglyMeasurable_const.mul ?_).mul (hF q.1)).mul ?_).mul (hH _)
  · exact (by fun_prop : Continuous fun s : ℝ => Complex.exp (((((1 : ℤ) : ℝ) * Real.pi * δ *
      L ^ (2 * γ) * resFactor (latticePoint L q.1) (latticePoint L q.2)
        (latticePoint L (n - q.1 + q.2)) (latticePoint L n) * s : ℝ) : ℂ) * Complex.I)).stronglyMeasurable.comp_measurable
      hT
  · exact Complex.continuous_conj.comp_stronglyMeasurable (hG q.2)

include hB hBs hT in
theorem stronglyMeasurable_treeTermDt' (p : ℕ) (S : TTree) (n : Fin d → ℤ) :
    StronglyMeasurable fun a => treeTermDt L γ δ p S (B a) (T a) n := by
  cases S with
  | leaf => exact stronglyMeasurable_const
  | node l m r =>
    exact stronglyMeasurable_aNonlin' L γ δ (fun k => stronglyMeasurable_treeTerm' L γ δ hB hBs hT p l k)
      (fun k => stronglyMeasurable_treeTerm' L γ δ hB hBs hT p m k)
      (fun k => stronglyMeasurable_treeTerm' L γ δ hB hBs hT p r k)
      (fun a => summable_norm_treeTerm L γ δ p l (hBs a) (T a))
      (fun a => summable_norm_treeTerm L γ δ p m (hBs a) (T a))
      (fun a => summable_norm_treeTerm L γ δ p r (hBs a) (T a)) hT n

omit hB hBs hT in
theorem finsum_order_eq {M : Type*} [AddCommMonoid M] (N : ℕ) (f : TTree → M) :
    ∑ᶠ (S : TTree) (_ : S.order = N), f S = ∑ S ∈ treesOfOrder N, f S := by
  unfold treesOfOrder
  rw [← finsum_mem_eq_finite_toFinset_sum _ (finite_order_eq N)]
  rfl

include hB hBs hT in
theorem stronglyMeasurable_aTrDt' (p Ntr : ℕ) (n : Fin d → ℤ) :
    StronglyMeasurable fun a => aTrDt L γ δ p Ntr (B a) (T a) n := by
  unfold aTrDt
  simp only [finsum_order_eq]
  exact Finset.stronglyMeasurable_fun_sum _ fun N _ =>
    Finset.stronglyMeasurable_fun_sum _ fun S _ => stronglyMeasurable_treeTermDt' L γ δ hB hBs hT p S n

include hB hBs hT in
theorem stronglyMeasurable_slotValAt' (p Ntr : ℕ) (o : Slot Ntr) (k : Fin d → ℤ) :
    StronglyMeasurable fun a => slotValAt L γ δ p Ntr (B a) o (T a) k := by
  cases o with
  | none => exact stronglyMeasurable_const
  | some N => exact stronglyMeasurable_treeTermN' L γ δ hB hBs hT p N k

omit [MeasurableSpace α] hB hT in
include hBs in
theorem summable_slotValAt' (p Ntr : ℕ) (o : Slot Ntr) (a : α) (t : ℝ) :
    Summable fun k => ‖slotValAt L γ δ p Ntr (B a) o t k‖ := by
  cases o with
  | none => simp [slotValAt]
  | some N => exact summable_norm_treeTermN L γ δ p N (hBs a) t

include hB hBs hT in
theorem stronglyMeasurable_L0Dt' (p Ntr : ℕ) (n : Fin d → ℤ) :
    StronglyMeasurable fun a => L0Dt L γ δ p Ntr (B a) (T a) n := by
  unfold L0Dt
  exact Finset.stronglyMeasurable_fun_sum _ fun x _ =>
    stronglyMeasurable_aNonlin' L γ δ (fun k => stronglyMeasurable_slotValAt' L γ δ hB hBs hT p Ntr x.1 k)
      (fun k => stronglyMeasurable_slotValAt' L γ δ hB hBs hT p Ntr x.2.1 k)
      (fun k => stronglyMeasurable_slotValAt' L γ δ hB hBs hT p Ntr x.2.2 k)
      (fun a => summable_slotValAt' L γ δ hBs p Ntr x.1 a (T a))
      (fun a => summable_slotValAt' L γ δ hBs p Ntr x.2.1 a (T a))
      (fun a => summable_slotValAt' L γ δ hBs p Ntr x.2.2 a (T a)) hT n

end Param

end WaveTurbulence.Fixedpt
