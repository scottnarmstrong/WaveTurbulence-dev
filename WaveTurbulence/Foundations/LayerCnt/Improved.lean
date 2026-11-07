/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.Layervine

/-! # TARGET `layervine`, improved bound: reduction to the layer-range claim (L1522–L1532)

For a coherent vine whose atoms all lie in the layer range `[q', q]` (`q' = 𝔏_{v_2}`, `q = 𝔏_{v_1}`), the weighted
layering sum is at most `C_0^{m+(q−q')}`: clamp the layers to `[q', q]` and apply the core bound with `𝔇 = q − q'`.
The layer-range claim itself (source: monotone group chain `q' ≤ 𝔏_1 ≤ ⋯ ≤ 𝔏_r ≤ q`, and `𝔏 ∈ [q',q]` for the
remaining Vine-(V) atoms via canonequiv) is NOT proved here.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open Finset WaveTurbulence.Vine TTree
variable {w : ℕ}

/-- Clamp to `[q', q]` and shift by `q'`. -/
@[expose] def clampL (q q' t : ℕ) : ℕ := min (max t q') q - q'

theorem clampL_mono (q q' : ℕ) : Monotone (clampL q q') := by
  intro s t h; unfold clampL; omega

theorem clampL_le (q q' t : ℕ) : clampL q q' t ≤ q - q' := by unfold clampL; omega

theorem clampL_of_mem {q q' t : ℕ} (h1 : q' ≤ t) (h2 : t ≤ q) : clampL q q' t = t - q' := by
  unfold clampL; omega

/-- **Improved `layervine` bound, conditional on the layer range.** -/
theorem layervine_improved_of_range (B : ℝ) (hB : 1 ≤ B) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ {w : ℕ} (G : Garden w) (X : VineType) (S : Finset (GBranch G.tree)) (a b : GBranch G.tree)
      (R : VineRealization G.molecule X S a b) (m : ℕ),
      (X.IsBad = true → S.card = 2 * m + 2) → (X.IsBad = false → S.card = 2 * m + 5) →
      ∀ (q q' : ℕ), q' ≤ q → ∀ 𝓕 : Finset (GBranch G.tree → ℕ),
        (∀ f ∈ 𝓕, LFTwist.IsBranchPrelayering G f) →
        (∀ f ∈ 𝓕, realizedIncoherencyIndex R f = 0) →
        (∀ f ∈ 𝓕, ∀ x ∈ S, q' ≤ f x ∧ f x ≤ q) →
        (∀ f ∈ 𝓕, ∀ f' ∈ 𝓕, (∀ x ∈ S, f x = f' x) → f = f') →
        ∑ f ∈ 𝓕, ∏ x ∈ bondsIn G.molecule S,
            B ^ dst (f (G.molecule.atom x)) (f (G.molecule.atom (G.molecule.mate x))) ≤
          C₀ ^ (m + (q - q')) := by
  classical
  refine ⟨max 9 ((2 : ℝ) ^ 21 * 3 ^ 48 * B ^ 60), le_trans (by norm_num) (le_max_left _ _), ?_⟩
  intro w G X S a b R m hbad hnorm q q' hqq 𝓕 hpre hcoh hrange hinj
  set C₀ : ℝ := max 9 ((2 : ℝ) ^ 21 * 3 ^ 48 * B ^ 60) with hC₀
  have hC1 : 1 ≤ C₀ := le_trans (by norm_num) (le_max_left _ _)
  have hpr : ∀ f : GBranch G.tree → ℕ,
      ∏ x ∈ bondsIn G.molecule S,
        B ^ dst (f (G.molecule.atom x)) (f (G.molecule.atom (G.molecule.mate x))) =
      B ^ bondExp G.molecule S f := fun f => by
    unfold bondExp; rw [Finset.prod_pow_eq_pow_sum]
  simp only [hpr]
  set cl : (GBranch G.tree → ℕ) → (GBranch G.tree → ℕ) := fun f x => clampL q q' (f x) with hcl
  have hclinj : ∀ f ∈ 𝓕, ∀ f' ∈ 𝓕, (∀ x ∈ S, cl f x = cl f' x) → f = f' := by
    intro f hf f' hf' h
    apply hinj f hf f' hf'
    intro x hx
    have := h x hx
    simp only [hcl] at this
    rw [clampL_of_mem (hrange f hf x hx).1 (hrange f hf x hx).2,
      clampL_of_mem (hrange f' hf' x hx).1 (hrange f' hf' x hx).2] at this
    have := (hrange f hf x hx).1; have := (hrange f' hf' x hx).1
    omega
  have hbe : ∀ f ∈ 𝓕, bondExp G.molecule S (cl f) = bondExp G.molecule S f := by
    intro f hf
    unfold bondExp
    apply Finset.sum_congr rfl
    intro x hx
    simp only [bondsIn, mem_filter] at hx
    have h1 := hrange f hf _ hx.2.1
    have h2 := hrange f hf _ hx.2.2
    simp only [hcl]
    rw [clampL_of_mem h1.1 h1.2, clampL_of_mem h2.1 h2.2]
    unfold dst; omega
  have hsum : ∑ f ∈ 𝓕, B ^ bondExp G.molecule S f =
      ∑ h ∈ 𝓕.image cl, B ^ bondExp G.molecule S h := by
    rw [Finset.sum_image (fun f hf f' hf' h => hclinj f hf f' hf' (fun x _ => congrFun h x))]
    exact Finset.sum_congr rfl (fun f hf => (by rw [hbe f hf]))
  rw [hsum]
  have hflt : (𝓕.image cl).filter (fun h => realizedIncoherencyIndex R h = 0) = 𝓕.image cl := by
    apply Finset.filter_true_of_mem
    intro h hh
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hh
    have := (realizedIncoherencyIndex_eq_zero_iff R f).mp (hcoh f hf)
    refine (realizedIncoherencyIndex_eq_zero_iff R (cl f)).mpr ?_
    intro g hg x hx y hy
    exact congrArg (clampL q q') (this g hg x hx y hy)
  have hcore := vine_sum_le B hB G X S a b R m hbad hnorm (q - q') 0 (𝓕.image cl)
    (by
      intro h hh
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hh
      refine ⟨?_, fun x => clampL_le q q' _⟩
      intro b' c i hc
      exact clampL_mono q q' (hpre f hf b' c i hc))
    (by
      intro h hh h' hh' hagree
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hh
      obtain ⟨f', hf', rfl⟩ := Finset.mem_image.mp hh'
      have := hclinj f hf f' hf' hagree
      rw [this])
  rw [hflt] at hcore
  refine hcore.trans ?_
  have h9 : (9 : ℝ) ^ m ≤ C₀ ^ m := pow_le_pow_left₀ (by norm_num) (le_max_left _ _) m
  have hK : ((2 : ℝ) ^ 21 * 3 ^ 48 * B ^ 60) ^ (q - q') ≤ C₀ ^ (q - q') :=
    pow_le_pow_left₀ (by positivity) (le_max_right _ _) _
  calc (9 : ℝ) ^ m * (((2 : ℝ) ^ 21 * 3 ^ 48 * B ^ 60) ^ (q - q')) ^ (0 + 1)
      ≤ C₀ ^ m * C₀ ^ (q - q') := by
        rw [zero_add, pow_one]
        exact mul_le_mul h9 hK (by positivity) (by positivity)
    _ = C₀ ^ (m + (q - q')) := by rw [pow_add]

end WaveTurbulence.LayerCnt
