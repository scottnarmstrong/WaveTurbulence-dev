/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepH1
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3Kernel
public import WaveTurbulence.Foundations.Stage1.Represents.RepH18
import Mathlib.Tactic

/-!
# S2 REPRESENTS, G1 (1): the weak output box

`outBoxW D = {t ∈ cube, max(t₁, t₂) ≤ t₀}` (the closure of `outBox D` when `qOut 1, qOut 2 ≤ qOut 0`).  A Fourier
superposition `Σ w a e^{πi m·t}` of an absolutely summable family that agrees with a function continuous on the cube on
`outBox` agrees with it on `outBoxW` (`hasSum_outBoxW`): both sides are continuous and `outBoxW` lies in the closure of `outBox`
inside the cube.  `exists_hingeFam_w` is `exists_hingeFam` with the identity delivered on `outBoxW`.  This is what lets a
dummy time `qOut i` stand for the clock of a leaf lower child (a strict inequality `td < t₀` could fail at `t₀ = qOut 0`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS3.Eng WaveTurbulence.RepAnalytic
open scoped ENNReal

/-- The weak output box: the cube with `max (t 1) (t 2) ≤ t 0`. -/
def outBoxW {d : ℕ} (D : SumintDatum d) : Set (Fin 3 → ℝ) :=
  {t | t ∈ cubeSet D.qOut ∧ max (t 1) (t 2) ≤ t 0}

theorem continuous_fsPhase' {r : ℕ} (m : Fin r → ℤ) : Continuous fun t : Fin r → ℝ => fsPhase m t := by
  have : (fun t : Fin r → ℝ => fsPhase m t) = fun t =>
      Complex.exp ((Real.pi * ∑ i, (m i : ℝ) * t i : ℝ) * Complex.I) := funext fun t => fsPhase_eq_exp m t
  rw [this]
  refine Complex.continuous_exp.comp (Continuous.mul (Complex.continuous_ofReal.comp ?_) continuous_const)
  exact continuous_const.mul (continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_apply i))

theorem norm_fsPhase' {r : ℕ} (m : Fin r → ℤ) (t : Fin r → ℝ) : ‖fsPhase m t‖ = 1 := by
  unfold fsPhase; exact Circle.norm_coe _

/-- **Extension of a Fourier superposition from `outBox` to `outBoxW`.** -/
theorem hasSum_outBoxW {d : ℕ} (D : SumintDatum d) (hq1 : D.qOut 1 ≤ D.qOut 0) (hq2 : D.qOut 2 ≤ D.qOut 0)
    (w : (Fin 3 → ℤ) → ℝ) (hw0 : ∀ m, 0 ≤ w m) (hws : Summable w) (a : (Fin 3 → ℤ) → ℂ) (ha : ∀ m, ‖a m‖ ≤ 1)
    (g : (Fin 3 → ℝ) → ℂ) (hg : ContinuousOn g (cubeSet D.qOut))
    (hser : ∀ t ∈ outBox D, HasSum (fun m => (w m : ℂ) * a m * fsPhase m t) (g t)) :
    ∀ t ∈ outBoxW D, HasSum (fun m => (w m : ℂ) * a m * fsPhase m t) (g t) := by
  intro t ht
  have hterm : ∀ m t', ‖(w m : ℂ) * a m * fsPhase m t'‖ ≤ w m := fun m t' => by
    rw [norm_mul, norm_mul, norm_fsPhase', mul_one, Complex.norm_real, Real.norm_of_nonneg (hw0 m)]
    exact mul_le_of_le_one_right (hw0 m) (ha m)
  have hcont : Continuous fun t' : Fin 3 → ℝ => ∑' m, (w m : ℂ) * a m * fsPhase m t' :=
    continuous_tsum (fun m => continuous_const.mul (continuous_fsPhase' m)) hws hterm
  have hsN : Summable fun m => (w m : ℂ) * a m * fsPhase m t :=
    Summable.of_norm_bounded hws (fun m => hterm m t)
  suffices hEq : g t = ∑' m, (w m : ℂ) * a m * fsPhase m t by
    rw [hEq]; exact hsN.hasSum
  -- approximate `t` from inside `outBox` along the segment to a strictly feasible point
  obtain ⟨htc, htl⟩ := ht
  set c : Fin 3 → ℝ := ![(D.qOut 0 : ℝ) + 1, (D.qOut 1 : ℝ), (D.qOut 2 : ℝ)] with hc
  set u : ℝ → Fin 3 → ℝ := fun s i => (1 - s) * t i + s * c i with hu
  have hucont : Continuous u := by
    refine continuous_pi fun i => ?_
    exact ((continuous_const.sub continuous_id).mul continuous_const).add (continuous_id.mul continuous_const)
  have hu0 : u 0 = t := by funext i; simp [hu]
  have hc0 : c 0 = (D.qOut 0 : ℝ) + 1 := by simp [hc]
  have hc1 : c 1 = (D.qOut 1 : ℝ) := by simp [hc]
  have hc2 : c 2 = (D.qOut 2 : ℝ) := by simp [hc]
  have hci : ∀ i, (D.qOut i : ℝ) ≤ c i ∧ c i ≤ D.qOut i + 1 := by
    intro i
    fin_cases i
    · simp only [Fin.zero_eta, hc0]; constructor <;> linarith
    · simp only [Fin.mk_one, hc1]; constructor <;> linarith
    · simp only [Fin.reduceFinMk, hc2]; constructor <;> linarith
  have hev : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), u s ∈ outBox D := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with s hs
    obtain ⟨hs0, hs1⟩ := hs
    refine ⟨fun i => ?_, ?_⟩
    · have hti := htc i
      have hci' := hci i
      simp only [hu]
      constructor <;> nlinarith [hti.1, hti.2, hci'.1, hci'.2]
    · have h1 : (D.qOut 1 : ℝ) ≤ D.qOut 0 := by exact_mod_cast hq1
      have h2 : (D.qOut 2 : ℝ) ≤ D.qOut 0 := by exact_mod_cast hq2
      have t1 := le_max_left (t 1) (t 2)
      have t2 := le_max_right (t 1) (t 2)
      simp only [hu, hc0, hc1, hc2]
      refine max_lt ?_ ?_ <;> nlinarith
  have hT : Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds t) := by
    rw [← hu0]; exact (hucont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hTc : Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin t (cubeSet D.qOut)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hT, ?_⟩
    filter_upwards [hev] with s hs using hs.1
  have hg1 : Filter.Tendsto (fun s => g (u s)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (g t)) :=
    (hg t htc).tendsto.comp hTc
  have hg2 : Filter.Tendsto (fun s => ∑' m, (w m : ℂ) * a m * fsPhase m (u s)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∑' m, (w m : ℂ) * a m * fsPhase m t)) := (hcont.tendsto t).comp hT
  have hgeq : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), g (u s) = ∑' m, (w m : ℂ) * a m * fsPhase m (u s) := by
    filter_upwards [hev] with s hs using (hser _ hs).tsum_eq.symm
  exact tendsto_nhds_unique_of_eventuallyEq hg1 hg2 hgeq

/-- **`exists_hingeFam` with the superposition identity on the weak box `outBoxW`.** -/
theorem exists_hingeFam_w {θ : ℝ} (hθ : 0 ≤ θ) (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (J : Type) (Dj : J → (Fin 4 → Fin d → ℤ) → SumintDatum d)
      (Kj : J → (Fin 4 → Fin d → ℤ) → Set (Fin 4 → Mom d)) (σ : J → ℤˣ)
      (f : J → (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ) (M : J → ℝ), (∀ j, 0 ≤ M j) →
      (∀ j c, (Dj j c).qOut 1 ≤ (Dj j c).qOut 0 ∧ (Dj j c).qOut 2 ≤ (Dj j c).qOut 0) →
      (∀ j c, ∀ E ∈ Kj j c, ContinuousOn (fun t => f j t (sumintBoundary (σ j) E)) (cubeSet (Dj j c).qOut)) →
      (∀ j c, XNorm00Restr θ (outBox (Dj j c)) (Kj j c) (fun t E => f j t (sumintBoundary (σ j) E)) ≤
        ENNReal.ofReal (M j)) →
      ∃ H : HingeFam J d, (∀ j c, ∑' l, H.w j c l ≤ C * M j) ∧
        ∀ j c, ∀ t ∈ outBoxW (Dj j c), ∀ k, sumintBoundary (σ j) k ∈ Kj j c →
          HasSum (fun l => (H.w j c l : ℂ) * H.a j c l k * fsPhase (H.m j c l) t) (f j t k) := by
  obtain ⟨C, hC, hsup⟩ := unit_superposition hθ d
  refine ⟨C, hC, fun J Dj Kj σ f M hM hq hcont hbd => ?_⟩
  have hex : ∀ j c, ∃ (w : (Fin 3 → ℤ) → ℝ) (a : (Fin 3 → ℤ) → (Fin 4 → Mom d) → ℂ),
      (∀ m, 0 ≤ w m) ∧ (∀ m E, ‖a m E‖ ≤ 1) ∧
      (∀ t ∈ outBox (Dj j c), ∀ E ∈ Kj j c, HasSum (fun m => (w m : ℂ) * a m E * fsPhase m t)
        (f j t (sumintBoundary (σ j) E))) ∧ Summable w ∧ ∑' m, w m ≤ C * M j := fun j c =>
    hsup (Dj j c) (Kj j c) (fun t E => f j t (sumintBoundary (σ j) E)) (M j) (hM j) (hcont j c) (hbd j c)
  choose w a hw0 ha hser hws hwb using hex
  refine ⟨{ Λ := fun _ _ => Fin 3 → ℤ
            cnt := fun _ _ => inferInstance
            w := w
            m := fun _ _ m => m
            a := fun j c m k => a j c m (sumintBoundary (σ j) k)
            w_nn := hw0
            w_sum := hws
            a_one := fun j c m k => ha j c m _ }, hwb, ?_⟩
  intro j c t ht k hk
  have hg : ContinuousOn (fun t => f j t k) (cubeSet (Dj j c).qOut) := by
    have := hcont j c _ hk
    simpa only [sumintBoundary_invol] using this
  have h1 : ∀ t' ∈ outBox (Dj j c), HasSum (fun m => (w j c m : ℂ) * a j c m (sumintBoundary (σ j) k) * fsPhase m t')
      (f j t' k) := by
    intro t' ht'
    have h := hser j c t' ht' (sumintBoundary (σ j) k) hk
    rwa [sumintBoundary_invol] at h
  exact hasSum_outBoxW (Dj j c) (hq j c).1 (hq j c).2 (w j c) (hw0 j c) (hws j c)
    (fun m => a j c m (sumintBoundary (σ j) k)) (fun m => ha j c m _) (fun t => f j t k) hg h1 t ht

end WaveTurbulence.Represents
