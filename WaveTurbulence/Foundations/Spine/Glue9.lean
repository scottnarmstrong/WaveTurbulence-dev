/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Glue8
public import WaveTurbulence.Foundations.Spine.GenSum
import Mathlib.Tactic
/-! The class bound for the literal time domain `splicedTimeDomain`. -/
@[expose] public section
open WaveTurbulence.Induct
open Finset MeasureTheory
open scoped ENNReal
namespace WaveTurbulence.Ladder
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDisjoint
open scoped Classical
variable {w d : ℕ} {G : Garden w}

theorem class_fourier (hp : G.IsPlain) {L : ℝ} (hL : 0 < L) (D : SplicedKernelData G d)
    (hamp : SplicedAmplitudeBounds G D) (scales : Finset (GBranch G.tree) → ℝ) (γ η δ : ℝ) (hδ : 0 ≤ δ)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (π0 : PF G)
    (cd : CD G D L γ δ base roots hp π0 (fun S => 8 * δ * L ^ (2 * γ) * scales S.1))
    (isSmall : LQ G → Prop) (hsm : ∀ S, isSmall S → scales S.1 < 1)
    (Dt : ℝ) (hDt0 : 0 ≤ Dt) (hDt : ∀ v, (D.layer v : ℝ) + 1 ≤ Dt) (A : Finset (GBranch G.tree)) :
    ∫⁻ α in Wnb (clsPF G D scales L γ η δ base roots π0),
        ‖Phi (splicedTimeDomain G D.layer D.rootTime) (fun v => (D.layer v : ℝ)) A α‖ₑ ≤
      2 ^ Fintype.card (Jr (cd.Kn isSmall)) *
        ((∏ s : Jr (cd.Kn isSmall), ENNReal.ofReal (2 * rhoS d L γ δ (scales s.1.1))) *
          ((∏ S : LQ G, ENNReal.ofReal (2 ^ (cd.Kn isSmall S) * Dt ^ (cd.Kn isSmall S) /
              (Nat.factorial (cd.Kn isSmall S) : ℝ))) *
            ENNReal.ofReal (Real.pi ^ Fintype.card (GBranch G.tree) *
              3 ^ (Fintype.card (GBranch G.tree) - Fintype.card (Jr (cd.Kn isSmall)))) *
            (2 * ENNReal.ofReal (2 * Real.arsinh (Mv d L) + 1)) ^
              (Fintype.card (GBranch G.tree) - Fintype.card (Jr (cd.Kn isSmall))))) := by
  obtain ⟨Sy, hSy, hKc, hSyW⟩ := exists_Sy hp hL D hamp scales γ η δ base roots
  have hinj := cd.elim_injective isSmall
  have hΩ : Om0 (fun a b : GBranch G.tree => a.IsChildOf b) (fun v => (D.layer v : ℝ)) (fun v => D.rootTime v.1.1) =
      splicedTimeDomain G D.layer D.rootTime := by
    ext t
    simp only [Om0, splicedTimeDomain, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3, h2⟩
    · rintro ⟨h1, h3, h2⟩; exact ⟨h1, h2, h3⟩
  have hcl := class_bound (fun a b : GBranch G.tree => a.IsChildOf b) (fun b => b.1.2.length)
    (fun a b h => isChildOf_length h) (fun a b b' h h' => isChildOf_unique h h')
    (cd.ua isSmall) (cd.va isSmall) hinj (fun v => (D.layer v : ℝ)) (fun v => D.rootTime v.1.1) Dt hDt0
    (fun v => ⟨Nat.cast_nonneg _, hDt v⟩)
    (fun t ht q => cd.hval isSmall t (fun b' b h => ht.2.2 b' b h) q)
    A Sy hSy (ENNReal.ofReal (2 * Real.arsinh (Mv d L) + 1)) hKc
    (fun s => rhoS d L γ δ (scales s.1.1)) (Wnb (clsPF G D scales L γ η δ base roots π0)) ?_
  · rw [hΩ] at hcl
    exact hcl
  · intro θ
    refine ⟨cd.hXf isSmall θ, cd.hXf_measurable isSmall θ,
      fun x β β' h => cd.hXf_dep isSmall hinj θ x β β' h, ?_⟩
    rintro α ⟨α', hα', hclose⟩
    refine ⟨fun b _ => hSyW α' (clsPF_subset_spectrum D scales L γ η δ base roots π0 hα') α hclose b,
      fun s => ?_⟩
    exact loc_atom hp hL D hamp scales γ η δ hδ base roots π0 cd isSmall hsm θ s α α' hα' hclose

end WaveTurbulence.Ladder
