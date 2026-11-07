/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Fam.Graded1
/-! # FL-FAM: the graded bound for `(1 + |x|^2)^r · Phi`, by induction on the rounds
(graded variant of `Polar.round_bound`). -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Fam
open Finset LGSpine WaveTurbulence.Flower.Polar

variable {w d : ℕ}

variable (P : WTParams) (hL : 1 ≤ P.L) (p N : ℕ) (kind : FlowerKind) (pat : Fin w → FixPat)
  (dagger : Option (Fin w → Fin 3 → Mom P.d))
  (W : ∀ LG : LayeredGarden w, (GNode LG.garden.tree → Mom P.d) → ℝ) (hW : ∀ LG k, |W LG k| ≤ 1)
  (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ)

include hL hW in
theorem round_bound_graded (A B : ℕ) (hB : P.d + 1 ≤ B) (M : ℕ) (hM : 1 ≤ M) (hMw : 2 * N + w ≤ 2 * M)
    (lam : ℝ) (hlam : 0 < lam) (b X T1 : ℝ) (Good : TProf P.d w → Prop)
    (hGs : ∀ g, Good g → ∀ (j : Fin w) (i : Fin P.d) (μ : ℝ),
      Good (TProf.perturb g (polForm ((-1 : ℝ) ^ (j : ℕ)) j i g) μ))
    (hT1 : ∑ m ∈ range (2 * M + 1), |CentralDiff.cw M m / lam| ≤ T1)
    (hcore : ∀ g : TProf P.d w, Good g → Adm p A B [] (2 * b) g →
      ‖Phi P p N kind pat dagger W ζ t s n n' g‖ ≤ X) :
    ∀ (js : List (Fin w)) (g : TProf P.d w) (u lo : ℝ), Good g → 0 ≤ u → 0 ≤ lo → Adm p A B (apps js) u g →
      Lo p A B lo g →
      lo + u * ((1 + lam * M * ((2 : ℝ) ^ A * (P.d : ℝ) ^ A)) ^ (2 * js.length) - 1) ≤ 2 * b →
      ‖(((1 + ‖latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n'‖ ^ 2) ^ js.length : ℝ) : ℂ) *
          Phi P p N kind pat dagger W ζ t s n n' g‖ ≤ (1 + P.d * T1 ^ 2) ^ js.length * X := by
  intro js
  induction js with
  | nil =>
    intro g u lo hG hu hlo0 hA hl hle
    have hA' : Adm p A B [] (2 * b) g := by
      intro q hq j1 j2
      refine ⟨(hA q hq j1 j2).1, ?_⟩
      have h1 := hl q hq j1 j2
      have h2 : lo ≤ 2 * b := by simpa using hle
      simpa [wcnt_nil] using h1.trans (ENNReal.ofReal_le_ofReal h2)
    simpa using hcore g hG hA'
  | cons j js' ih =>
    intro g u lo hG hu hlo0 hA hl hle
    set ε : ℝ := lam * M * ((2 : ℝ) ^ A * (P.d : ℝ) ^ A) with hε
    have hε0 : 0 ≤ ε := by positivity
    have hA' : Adm p A B (j :: j :: apps js') u g := hA
    have hu1 : 0 ≤ (1 + ε) * u := by positivity
    have hu2 : 0 ≤ (1 + ε) * ((1 + ε) * u) := by positivity
    have hid := round_identity P hL p N kind pat dagger W hW ζ t s n n' A B hB M hM hMw lam hlam j
      (apps js') u hu g hA'
    set c : ℝ := 1 + ‖latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n'‖ ^ 2 with hc
    have hc0 : 0 ≤ c := by positivity
    set K : ℝ := 1 + P.d * T1 ^ 2 with hK
    have hpow : (1 + ε) ^ (2 * js'.length) ≤ (1 + ε) ^ (2 * (j :: js').length) :=
      pow_le_pow_right₀ (by linarith) (by simp)
    have hleg : lo + u * ((1 + ε) ^ (2 * js'.length) - 1) ≤ 2 * b := by
      have : u * ((1 + ε) ^ (2 * js'.length) - 1) ≤ u * ((1 + ε) ^ (2 * (j :: js').length) - 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hu
      linarith
    have hAg : Adm p A B (apps js') u g := (hA'.mono_cons hu).mono_cons hu
    have hg0 := ih g u lo hG hu hlo0 hAg hl hleg
    have hT10 : 0 ≤ T1 := (Finset.sum_nonneg fun m _ => abs_nonneg _).trans hT1
    have hK0 : 0 ≤ K := by positivity
    have hY : 0 ≤ K ^ js'.length * X := (norm_nonneg _).trans hg0
    have hmid : ∀ i : Fin P.d, ∀ m ∈ range (2 * M + 1), Adm p A B (j :: apps js') ((1 + ε) * u)
        (pert j i g lam M m) := fun i m hm => hA'.pert_step hu i lam hlam M m hm
    have hlmid : ∀ i : Fin P.d, ∀ m ∈ range (2 * M + 1), Lo p A B (lo + ε * u)
        (pert j i g lam M m) := by
      intro i m hm
      have := Lo.pert_step hA' hl hu hlo0 i lam hlam M m hm
      have e : lo + lam * M * ((2 : ℝ) ^ A * (P.d : ℝ) ^ A) * u = lo + ε * u := by rw [hε]
      rw [e] at this
      exact this
    have hfin : ∀ i : Fin P.d, ∀ m ∈ range (2 * M + 1), ∀ m' ∈ range (2 * M + 1),
        ‖((c ^ js'.length : ℝ) : ℂ) *
          Phi P p N kind pat dagger W ζ t s n n' (pert j i (pert j i g lam M m) lam M m')‖ ≤
        K ^ js'.length * X := by
      intro i m hm m' hm'
      have hl2 : Lo p A B (lo + ε * u + ε * ((1 + ε) * u)) (pert j i (pert j i g lam M m) lam M m') := by
        have := Lo.pert_step (hmid i m hm) (hlmid i m hm) hu1 (by positivity) i lam hlam M m' hm'
        have e : lo + ε * u + lam * M * ((2 : ℝ) ^ A * (P.d : ℝ) ^ A) * ((1 + ε) * u) =
            lo + ε * u + ε * ((1 + ε) * u) := by rw [hε]
        rw [e] at this
        exact this
      refine ih _ ((1 + ε) * ((1 + ε) * u)) (lo + ε * u + ε * ((1 + ε) * u))
        (hGs _ (hGs g hG j i _) j i _) hu2 (by positivity)
        ((hmid i m hm).pert_step hu1 i lam hlam M m' hm') hl2 ?_
      have e : lo + ε * u + ε * ((1 + ε) * u) + (1 + ε) * ((1 + ε) * u) * ((1 + ε) ^ (2 * js'.length) - 1)
          = lo + u * ((1 + ε) ^ (2 * (js'.length + 1)) - 1) := by ring
      rw [e]
      simpa using hle
    have hexp : (((c ^ (js'.length + 1) : ℝ)) : ℂ) *
        Phi P p N kind pat dagger W ζ t s n n' g =
        ((c ^ js'.length : ℝ) : ℂ) * Phi P p N kind pat dagger W ζ t s n n' g +
        ∑ i : Fin P.d, ∑ m ∈ range (2 * M + 1), ∑ m' ∈ range (2 * M + 1),
          ((CentralDiff.cw M m / lam : ℝ) : ℂ) * ((CentralDiff.cw M m' / lam : ℝ) : ℂ) *
            (((c ^ js'.length : ℝ) : ℂ) *
              Phi P p N kind pat dagger W ζ t s n n' (pert j i (pert j i g lam M m) lam M m')) := by
      have h1 : (((c ^ (js'.length + 1) : ℝ)) : ℂ) * Phi P p N kind pat dagger W ζ t s n n' g =
          ((c ^ js'.length : ℝ) : ℂ) * ((c : ℂ) * Phi P p N kind pat dagger W ζ t s n n' g) := by
        push_cast; ring
      rw [h1, hid, mul_add, Finset.mul_sum]
      congr 1
      refine sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine sum_congr rfl fun m _ => ?_
      rw [Finset.mul_sum]
      refine sum_congr rfl fun m' _ => ?_
      ring
    show ‖(((c ^ (js'.length + 1) : ℝ)) : ℂ) * _‖ ≤ K ^ (js'.length + 1) * X
    rw [hexp]
    have hsum := triple_sum_norm_le (d := P.d) (fun m => CentralDiff.cw M m / lam) (range (2 * M + 1))
      (fun i m m' => ((c ^ js'.length : ℝ) : ℂ) *
        Phi P p N kind pat dagger W ζ t s n n' (pert j i (pert j i g lam M m) lam M m'))
      (K ^ js'.length * X) T1 hY hT1 hfin
    calc _ ≤ ‖((c ^ js'.length : ℝ) : ℂ) * Phi P p N kind pat dagger W ζ t s n n' g‖ + _ := norm_add_le _ _
      _ ≤ K ^ js'.length * X + P.d * T1 ^ 2 * (K ^ js'.length * X) := add_le_add hg0 hsum
      _ = K ^ (js'.length + 1) * X := by rw [hK]; ring

end WaveTurbulence.Flower.Fam
