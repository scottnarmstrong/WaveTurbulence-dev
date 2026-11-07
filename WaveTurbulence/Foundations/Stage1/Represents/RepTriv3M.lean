/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepSupM
public import WaveTurbulence.Foundations.Stage1.Represents.RepTriv3
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-D (moments): trivial couple and trivial tree slots with the frequency moment

The time-independent slot kernels (RepTriv1/RepTriv3) are single-mode superpositions with frequency `0`, whose moment
weight is `⟨0⟩^θ = 1` (`maxBracketPow_half_zero`), so the moment-carrying forms hold with the same masses.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.LGSpine WaveTurbulence.VineEstS3.FS
open scoped ENNReal

variable {d r : ℕ}

theorem maxBracketPow_half_zero (θ : ℝ) : maxBracketPow θ (half (0 : Fin r → ℤ)) = 1 := by
  unfold maxBracketPow half
  have h : (⨆ i : Fin r, Real.sqrt (1 + (((0 : Fin r → ℤ) i : ℝ) / 2) ^ 2)) ⊔ 1 = 1 := by
    refine le_antisymm (sup_le (Real.iSup_le (fun i => by simp) zero_le_one) le_rfl) le_sup_right
  rw [h, Real.one_rpow, ENNReal.ofReal_one]

theorem SupM.congr {θ : ℝ} {A : ℕ} {B : Set (Fin r → ℝ)} {f g : (Fin r → ℝ) → Mom d → ℂ} {μ : ℝ≥0∞}
    (h : SupM θ A B f μ) (hfg : ∀ t ∈ B, ∀ k, f t k = g t k) : SupM θ A B g μ := by
  obtain ⟨Λ, hc, w, m, a, h1, h2, h3, h4, h5⟩ := h
  exact ⟨Λ, hc, w, m, a, h1, h2, h3, fun t ht k => by rw [← hfg t ht k]; exact h4 t ht k, h5⟩

theorem CenSupM.congr {θ : ℝ} {A : ℕ} {B : Set (Fin r → ℝ)} {f g : (Fin r → ℝ) → Mom d → ℂ} {μ : ℝ≥0∞}
    (h : CenSupM θ A B f μ) (hfg : ∀ t ∈ B, ∀ k, f t k = g t k) : CenSupM θ A B g μ := by
  obtain ⟨Λ, hc, w, m, n, a, h1, h2, h3, h3', h4, h5⟩ := h
  exact ⟨Λ, hc, w, m, n, a, h1, h2, h3, h3', fun t ht k => by rw [← hfg t ht k]; exact h4 t ht k, h5⟩

/-- A frequency-zero superposition carries its moment for free. -/
theorem CenSup.toCenSupM_of_zero {θ : ℝ} {A : ℕ} {B : Set (Fin r → ℝ)} {f : (Fin r → ℝ) → Mom d → ℂ}
    {μ : ℝ≥0∞} (h : ∃ (Λ : Type) (_ : Countable Λ) (w : Λ → ℝ) (n : Λ → Fin d → ℤ) (a : Λ → Mom d → ℂ),
      (∀ l, 0 ≤ w l) ∧ Summable w ∧ (∀ l, SNorm A 0 (a l) ≤ 1) ∧
      (∀ l k, a l k ≠ 0 → ‖k - latPt d (n l)‖ ≤ 1) ∧
      (∀ t ∈ B, ∀ k, HasSum (fun l => (w l : ℂ) * a l k * fsPhase (0 : Fin r → ℤ) t) (f t k)) ∧
      ∑' l, ENNReal.ofReal (w l) ≤ μ) : CenSupM θ A B f μ := by
  obtain ⟨Λ, hc, w, n, a, h1, h2, h3, h3', h4, h5⟩ := h
  refine ⟨Λ, hc, w, fun _ => 0, n, a, h1, h2, h3, h3', h4, ?_⟩
  simp only [maxBracketPow_half_zero, one_mul]
  exact h5

theorem cenSupM_profile {θ : ℝ} (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Bx : Set (Fin 2 → ℝ)) (H : Mom d → ℝ) (B : ℝ), 0 ≤ B →
      SNormR (40 * d) (40 * d) H ≤ ENNReal.ofReal B →
      CenSupM θ (30 * d) Bx (fun _ k => (H k : ℂ)) (ENNReal.ofReal (C * B)) := by
  obtain ⟨C0, hC0, hsum⟩ := tsum_snorm_chi_mul_le hd (30 * d) (Λ := 30 * d) (by omega)
  refine ⟨C0, hC0, fun Bx H B hB hH => ?_⟩
  set Hc : Mom d → ℂ := fun k => (H k : ℂ) with hHc
  have hH' : SNorm (40 * d) (40 * d) Hc ≤ ENNReal.ofReal B := hH
  have hcd : ContDiff ℝ (40 * d) Hc := WaveTurbulence.Induct.contDiff_of_SNorm_bound (A := 40 * d) (B := 40 * d) (by omega) _ _ hH'
  have h30 : SNorm (30 * d) (30 * d) Hc ≤ ENNReal.ofReal B :=
    SNorm_mono_bound (A := 40 * d) (B := 40 * d) (A' := 30 * d) (B' := 30 * d) (by omega) (by omega) Hc hcd B hB hH'
  have hcd30 : ContDiff ℝ (30 * d) Hc := hcd.of_le (by exact_mod_cast Nat.mul_le_mul_right d (by norm_num : 30 ≤ 40))
  have hs := hsum Hc hcd30
  have hfin : ∑' n : Fin d → ℤ, SNorm (30 * d) 0 (fun k => chiC d n k * Hc k) ≤ ENNReal.ofReal (C0 * B) := by
    refine hs.trans ?_
    rw [ENNReal.ofReal_mul hC0.le]
    exact mul_le_mul_right h30 _
  have hne : ∀ n, SNorm (30 * d) 0 (fun k => chiC d n k * Hc k) ≠ ⊤ := fun n =>
    ne_top_of_le_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfin)
      (ENNReal.le_tsum (f := fun n : Fin d → ℤ => SNorm (30 * d) 0 (fun k => chiC d n k * Hc k)) n)
  choose w a hw0 hwe ha hca hsupp using fun n : Fin d → ℤ =>
    exists_normalised (Λ₁ := 30 * d) (Λ₂ := 0) (fun k => chiC d n k * Hc k) (hne n)
  have hsumw : ∑' n, ENNReal.ofReal (w n) ≤ ENNReal.ofReal (C0 * B) := by
    refine le_trans (le_of_eq (tsum_congr fun n => hwe n)) hfin
  refine CenSup.toCenSupM_of_zero ⟨Fin d → ℤ, inferInstance, w, fun n => n, a, hw0, ?_, ha, ?_, ?_, hsumw⟩
  · exact summable_of_tsum_ofReal_ne_top hw0 (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsumw)
  · intro n k hk
    exact norm_sub_latPt_le_one_of_chiC_mul_ne_zero (hsupp n k hk)
  · intro t _ k
    have h1 := hasSum_chiC_mul Hc k
    have h2 : ∀ n : Fin d → ℤ, (w n : ℂ) * a n k * fsPhase (0 : Fin 2 → ℤ) t = chiC d n k * Hc k := by
      intro n
      rw [fsPhase_eq_prod_fin2]
      simp only [Pi.zero_apply, Int.cast_zero, mul_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero,
        Finset.prod_const_one, mul_one]
      exact (hca n k).symm
    simp_rw [h2]
    exact h1

theorem supM_one {θ : ℝ} (A : ℕ) (Bx : Set (Fin 2 → ℝ)) :
    SupM (d := d) θ A Bx (fun _ _ => (1 : ℂ)) (1 : ℝ≥0∞) := by
  refine ⟨Unit, inferInstance, fun _ => 1, fun _ => 0, fun _ _ => (1 : ℂ), fun _ => zero_le_one,
    (hasSum_fintype _).summable, fun _ => snorm_const_one_le A, ?_, ?_⟩
  · intro t _ k
    have : fsPhase (0 : Fin 2 → ℤ) t = 1 := by
      rw [fsPhase_eq_prod_fin2]; simp
    simp [this]
  · simp [maxBracketPow_half_zero]

open Classical in
/-- The explicit constant of the moment-carrying profile superposition (depends only on `d` and `θ`). -/
noncomputable def profCM (d : ℕ) (θ : ℝ) : ℝ := if h : 1 ≤ d then (cenSupM_profile (θ := θ) h).choose else 1

theorem profCM_spec {θ : ℝ} (hd : 1 ≤ d) : 0 < profCM d θ ∧ ∀ (Bx : Set (Fin 2 → ℝ)) (H : Mom d → ℝ) (B : ℝ),
      0 ≤ B → SNormR (40 * d) (40 * d) H ≤ ENNReal.ofReal B →
      CenSupM θ (30 * d) Bx (fun _ k => (H k : ℂ)) (ENNReal.ofReal (profCM d θ * B)) := by
  have e : profCM d θ = (cenSupM_profile (θ := θ) hd).choose := by unfold profCM; simp only [hd, ↓reduceDIte]
  rw [e]; exact (cenSupM_profile hd).choose_spec

theorem couple_slot_trivM {θ : ℝ} (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ C = profCM d θ ∧ ∀ (L γ δ : ℝ) (Bx : Set (Fin 2 → ℝ)) (LG : LayeredGarden 2),
      RegCpl.triv.Decodes LG.garden → ∀ (H : LeafProfiles 2 d) (B : (Fin 2 × TTree.Path) → NNReal),
      LeafwiseControlled LG H B →
      CenSupM θ (30 * d) Bx (fun ts k => coupleLeaves L γ δ LG H (ts 0) (ts 1) k)
        (ENNReal.ofReal (C * leafSizeProduct LG B)) := by
  obtain ⟨hC, h⟩ := profCM_spec (θ := θ) hd
  refine ⟨profCM d θ, hC, rfl, fun L γ δ Bx LG hQ H B hctrl => ?_⟩
  obtain ⟨ℓ0, -, hin, hk⟩ := coupleLeaves_triv L γ δ LG H hQ 0 0 (0 : Mom d)
  have hmem : ℓ0 ∈ inputLeaves LG.garden := by rw [hin]; exact Finset.mem_singleton_self _
  have hsz : leafSizeProduct LG B = (B ℓ0.1 : ℝ) := by
    unfold leafSizeProduct; rw [hin, Finset.prod_singleton]
  rw [hsz]
  refine (h Bx (H ℓ0.1) (B ℓ0.1 : ℝ) (NNReal.coe_nonneg _) (hctrl ℓ0 hmem)).congr ?_
  intro ts _ k
  obtain ⟨ℓ1, -, hin1, hk1⟩ := coupleLeaves_triv L γ δ LG H hQ (ts 0) (ts 1) k
  have : ℓ1 = ℓ0 := Finset.singleton_injective (hin1.symm.trans hin)
  subst this
  exact hk1.symm

theorem tree_slot_nilM {θ : ℝ} (Bx : Set (Fin 2 → ℝ)) (L γ δ : ℝ) (LG : LayeredGarden 1)
    (hX : RegChain.nil.DecodesTree LG.garden) (H : LeafProfiles 1 d) (B : (Fin 1 × TTree.Path) → NNReal) :
    SupM θ (30 * d) Bx (fun ts k => treeLeaves L γ δ LG H (ts 0) (ts 1) k)
      (ENNReal.ofReal (leafSizeProduct LG B)) := by
  have hsz : leafSizeProduct LG B = 1 := by
    unfold leafSizeProduct; rw [(treeLeaves_nil L γ δ LG H hX 0 0 (0 : Mom d)).1, Finset.prod_empty]
  rw [hsz, ENNReal.ofReal_one]
  refine (supM_one (d := d) (θ := θ) (30 * d) Bx).congr ?_
  intro ts _ k
  exact ((treeLeaves_nil L γ δ LG H hX (ts 0) (ts 1) k).2).symm

end WaveTurbulence.Represents
