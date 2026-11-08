/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKPin.Loc
public import WaveTurbulence.Foundations.Flower.FinalMKPin.Bridge
public import WaveTurbulence.Foundations.FlowerTop.Port.LadderSTBox
import Mathlib.Tactic

/-! # C4a PIN-FOURIER: the face box sum is bounded by the class integrals

With `E₀` the non-clock branches, the box sum of `LadderFourierAtMKFace` is at most
`#Sigs · 2^{4|Iv|} · (uniform class bound)` (`box_sum_boundI`). This is main's `box_sum_bound` with two changes:
- the clock frequency is shifted by the fixed real `cI β`, so a unit box around `σ + cI` is covered by the `2^{|Iv|}`
  integer boxes around `σ + ⌊cI⌋ + ε`, `ε ∈ {0,1}^{Iv}` (the floor trick);
- the boxes of distinct `σ` map injectively, so main's `sum_sup_le` (over all integer boxes) applies. -/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.Flower.FinalMKPin
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Ladder WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.FlowerP5
open MeasureTheory Set Finset
open scoped Classical ENNReal

variable {w d : ℕ} {G : Garden w}
variable {fix : GBranch G.tree → Option ℝ} {face : GBranch G.tree → Option (GBranch G.tree)}

/-- The non-clock branches. -/
noncomputable def E0 (fix : GBranch G.tree → Option ℝ) (face : GBranch G.tree → Option (GBranch G.tree)) :
    Finset (GBranch G.tree) :=
  univ.filter fun b => ¬ (fix b = none ∧ face b = none)

theorem notMem_E0 {b : GBranch G.tree} : b ∉ E0 fix face ↔ fix b = none ∧ face b = none := by
  simp [E0]

/-- The floor trick for one coordinate. -/
theorem floor_trick (x c : ℝ) (σ : ℤ) (h : |x - (σ + c)| ≤ 1) :
    |x - (((σ + ⌊c⌋ + (if (σ : ℝ) + ⌊c⌋ + 1 < x then 1 else 0) : ℤ) : ℝ))| ≤ 1 := by
  have h1 := Int.floor_le c
  have h2 := Int.lt_floor_add_one c
  rw [abs_le] at h ⊢
  split_ifs with hx
  · push_cast; constructor <;> linarith
  · push_cast; constructor <;> linarith [not_lt.mp hx]

theorem box_sum_boundI (hF : FaceOK fix face) (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ)
    (D : SplicedKernelData G d) (scales : Finset (GBranch G.tree) → ℝ) (L γ η δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (β : GBranch G.tree → ℝ) (Bcl : ℝ≥0∞)
    (hB : ∀ (π0 : PF G) (A : Finset (Iv fix face)),
      ∫⁻ α in Wnb (clsI D scales L γ η δ base roots π0 fix face β),
        ‖Phi (Om0 (chF fix face) (lsF layer fix face) (capF layer rootTime fix face)) (lsF layer fix face) A α‖ₑ ≤
        Bcl) :
    splicedFourierBoxSumMKFace G layer rootTime fix face (E0 fix face) β
        (splicedFrequencySpectrum G D scales L γ η δ base roots) ≤
      ((Sigs G).card : ℝ≥0∞) * (2 ^ Fintype.card (Iv fix face) * (2 ^ Fintype.card (Iv fix face) *
        (2 ^ Fintype.card (Iv fix face) * (2 ^ Fintype.card (Iv fix face) * Bcl)))) := by
  set 𝒜 := splicedFrequencySpectrum G D scales L γ η δ base roots with h𝒜
  set Ω := Om0 (chF fix face) (lsF layer fix face) (capF layer rootTime fix face) with hΩ
  set n := Fintype.card (Iv fix face)
  by_cases hne : 𝒜 = ∅
  · have : sourceFrequencyBoxesE G (E0 fix face) {α | α ∈ 𝒜 ∧ ∀ v ∈ E0 fix face, α v = β v} = ∅ := by
      ext σ; simp [sourceFrequencyBoxesE, hne]
    unfold splicedFourierBoxSumMKFace
    rw [this]
    simp
  obtain ⟨α0, hα0⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have : Nonempty (PF G) := by
    obtain ⟨π, _⟩ := Set.mem_iUnion.mp (spectrum_subset_iUnion G D scales L γ η δ base roots hα0)
    exact ⟨π⟩
  let repf : (∀ S : LQ G, GBranch G.tree × GBranch G.tree) → PF G :=
    fun c => Classical.epsilon (fun π : PF G => π.sig = c)
  have hrep : ∀ π : PF G, (repf π.sig).sig = π.sig := fun π => by
    show (Classical.epsilon (fun π' : PF G => π'.sig = π.sig)).sig = π.sig
    exact Classical.epsilon_spec (p := fun π' : PF G => π'.sig = π.sig) ⟨π, rfl⟩
  have hcover : ∀ α ∈ 𝒜, ∃ c ∈ Sigs G, α ∈ clsPF G D scales L γ η δ base roots (repf c) := by
    intro α hα
    obtain ⟨π, hπ⟩ := Set.mem_iUnion.mp (spectrum_subset_iUnion G D scales L γ η δ base roots hα)
    exact ⟨π.sig, π.sig_mem, clsPF_transport G D scales L γ η δ base roots π (repf π.sig) (hrep π).symm hπ⟩
  have hΩm := measurableSet_Om0_gen (chF fix face) (lsF layer fix face) (capF layer rootTime fix face)
  have hΩb := bdd_Om0_gen (chF fix face) (lsF layer fix face) (capF layer rootTime fix face)
  -- the summand of `sum_sup_le`
  set H : PF G → (Iv fix face → ℤ) → ℝ≥0∞ := fun π0 τ =>
    ⨆ (α : Iv fix face → ℝ) (_ : α ∈ clsI D scales L γ η δ base roots π0 fix face β)
      (_ : ∀ v, |α v - (τ v : ℝ)| ≤ 1), ‖Phi Ω (lsF layer fix face) ∅ α‖ₑ with hH
  set S := sourceFrequencyBoxesE G (E0 fix face) {α | α ∈ 𝒜 ∧ ∀ v ∈ E0 fix face, α v = β v}
  let σI : S → Iv fix face → ℤ := fun σ a => σ.1 ⟨a.1, notMem_E0.mpr a.2⟩
  let φ : (Iv fix face → Bool) → S → Iv fix face → ℤ := fun ε σ a =>
    σI σ a + ⌊cI fix face β a⌋ + (if ε a then 1 else 0)
  have hφinj : ∀ ε, Function.Injective (φ ε) := by
    intro ε σ σ' h
    apply Subtype.ext
    funext v
    have := congrFun h ⟨v.1, notMem_E0.mp v.2⟩
    simp only [φ, σI] at this
    have e : (⟨v.1, notMem_E0.mpr (notMem_E0.mp v.2)⟩ : {b // b ∉ E0 fix face}) = v := rfl
    rw [e] at this
    omega
  -- pointwise
  have hpt : ∀ σ : S, (⨆ (α : GBranch G.tree → ℝ) (_ : α ∈ 𝒜) (_ : ∀ v ∈ E0 fix face, α v = β v)
      (_ : ∀ v : {b : GBranch G.tree // b ∉ E0 fix face}, |α v.1 - σ.1 v| ≤ 1),
        ‖splicedFourierBMKFace G layer rootTime fix face α‖ₑ) ≤
      ∑ c ∈ Sigs G, ∑ ε : Iv fix face → Bool, H (repf c) (φ ε σ) := by
    intro σ
    refine iSup_le fun α => iSup_le fun hα => iSup_le fun hαE => iSup_le fun hσ => ?_
    obtain ⟨c, hc, hαc⟩ := hcover α hα
    have hag : AgreeE fix face β α := fun b hb => hαE b (by simp only [E0, Finset.mem_filter, Finset.mem_univ, true_and]; exact hb)
    rw [enorm_splicedFourierBMKFace_eq hF layer rootTime α]
    refine le_trans ?_ (Finset.single_le_sum (f := fun c => ∑ ε : Iv fix face → Bool, H (repf c) (φ ε σ))
      (fun _ _ => bot_le) hc)
    let ε : Iv fix face → Bool := fun a =>
      decide ((σI σ a : ℝ) + ⌊cI fix face β a⌋ + 1 < shiftF fix face α a)
    refine le_trans ?_ (Finset.single_le_sum (f := fun ε => H (repf c) (φ ε σ)) (fun _ _ => bot_le)
      (Finset.mem_univ ε))
    refine le_iSup_of_le (shiftF fix face α) (le_iSup_of_le ⟨α, hαc, hag, rfl⟩ (le_iSup_of_le (fun a => ?_) le_rfl))
    have h0 : |shiftF fix face α a - ((σI σ a : ℝ) + cI fix face β a)| ≤ 1 := by
      rw [shiftF_eq hag a]
      have := hσ ⟨a.1, notMem_E0.mpr a.2⟩
      have e : α a.1 + cI fix face β a - ((σI σ a : ℝ) + cI fix face β a) = α a.1 - (σI σ a : ℝ) := by ring
      rw [e]; exact this
    have := floor_trick (shiftF fix face α a) (cI fix face β a) (σI σ a) h0
    simp only [φ, ε, decide_eq_true_eq]
    convert this using 3
  -- assemble
  rw [boxSumMKFace_eq_gen]
  unfold boxSumGen
  calc ∑' σ : S, (⨆ (α : GBranch G.tree → ℝ) (_ : α ∈ 𝒜) (_ : ∀ v ∈ E0 fix face, α v = β v)
        (_ : ∀ v : {b : GBranch G.tree // b ∉ E0 fix face}, |α v.1 - σ.1 v| ≤ 1),
          ‖splicedFourierBMKFace G layer rootTime fix face α‖ₑ)
      ≤ ∑' σ : S, ∑ c ∈ Sigs G, ∑ ε : Iv fix face → Bool, H (repf c) (φ ε σ) := ENNReal.tsum_le_tsum hpt
    _ = ∑ c ∈ Sigs G, ∑ ε : Iv fix face → Bool, ∑' σ : S, H (repf c) (φ ε σ) := by
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ ≤ ∑ _c ∈ Sigs G, ∑ _ε : Iv fix face → Bool, (2 ^ n * (2 ^ n * (2 ^ n * Bcl))) := by
        refine Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun ε _ => ?_
        have hinj' : Function.Injective (fun σ : S => (⟨φ ε σ, Set.mem_univ _⟩ : (Set.univ : Set (Iv fix face → ℤ)))) :=
          fun σ σ' h => hφinj ε (congrArg Subtype.val h)
        refine le_trans (ENNReal.tsum_comp_le_tsum_of_injective hinj'
          (fun τ : (Set.univ : Set (Iv fix face → ℤ)) => H (repf c) τ.1)) ?_
        refine (sum_sup_le Ω hΩm _ hΩb (lsF layer fix face) (clsI D scales L γ η δ base roots (repf c) fix face β)
          Set.univ).trans ?_
        refine mul_le_mul' le_rfl (mul_le_mul' le_rfl ?_)
        calc ∑ A : Finset (Iv fix face), ∫⁻ α in Wnb (clsI D scales L γ η δ base roots (repf c) fix face β),
              ‖Phi Ω (lsF layer fix face) A α‖ₑ
            ≤ ∑ _A : Finset (Iv fix face), Bcl := Finset.sum_le_sum fun A _ => hB _ A
          _ = 2 ^ n * Bcl := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, nsmul_eq_mul]; push_cast; ring
    _ = _ := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          nsmul_eq_mul, nsmul_eq_mul]
        push_cast; ring

end WaveTurbulence.Flower.FinalMKPin
