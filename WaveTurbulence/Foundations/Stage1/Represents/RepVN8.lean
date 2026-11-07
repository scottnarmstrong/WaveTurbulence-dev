/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVN4
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-D: the hinge data of a mode from VINEEST(λ)

`exists_hinge_data_mod`: the modulated vine factors `HkM j λ` with per-centre bounds
`XNorm00Restr θ ≤ (1 + |λ|)^c M0_j` (VINEEST(λ), R58) give, for every modulation `lam : J → ℤ`, hinge families `H` and
masses `Mh_j = C (1 + |λ_j|)^c M0_j` with the hinge superposition property (G1, G2 as in `exists_hinge_data`) and
`Π_j Mh_j = C^{|J|} Π_j M0_j · Π_j (1 + |λ_j|)^c` (the shape of `hhinge` in `repIntC_vine_modes`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RepAnalytic
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS3.Eng
open scoped ENNReal

theorem exists_hinge_data_mod {θ : ℝ} (hθ : 0 ≤ θ) (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {w : ℕ} (S : Garden w) (J : Type) [Fintype J] (Dj : J → (Fin 4 → Fin d → ℤ) → SumintDatum d)
      (Kj : J → (Fin 4 → Fin d → ℤ) → Set (Fin 4 → Mom d)) (σ : J → ℤˣ)
      (HkM : J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ) (M0 : J → ℝ) (c : ℝ), (∀ j, 0 ≤ M0 j) →
      (∀ j c' lam, ∀ E ∈ Kj j c', ContinuousOn (fun t => HkM j lam t (sumintBoundary (σ j) E)) (cubeSet (Dj j c').qOut)) →
      (∀ j c' (lam : ℤ), XNorm00Restr θ (outBox (Dj j c')) (Kj j c')
        (fun t E => HkM j lam t (sumintBoundary (σ j) E)) ≤
        ENNReal.ofReal ((1 + |(lam : ℝ)|) ^ c * M0 j)) →
      ∀ (L : ℝ) (base : Mom d) (tt : Fin w → ℝ) (roots : Fin w → Fin d → ℤ)
        (selSk : GenDecoration S d roots 0 → Prop) (layer : GBranch S.tree → ℕ)
        (hmom : J → Fin 4 → GNode S.tree) (hclk : J → Fin 3 → ClkSrc S),
      (∀ κ : GenDecoration S d roots 0, selSk κ → ∀ τ ∈ splicedTimeDomain S layer tt, ∀ j c',
        (∀ i, ‖(base + latticePoint L (κ.1 (hmom j i))) - latPt d (c' i)‖ ≤ 1) →
          (fun i => clockOf S tt τ (hclk j i)) ∈ outBox (Dj j c')) →
      (∀ κ : GenDecoration S d roots 0, selSk κ → ∀ j c',
        (∀ i, ‖(base + latticePoint L (κ.1 (hmom j i))) - latPt d (c' i)‖ ≤ 1) →
          sumintBoundary (σ j) (fun i => base + latticePoint L (κ.1 (hmom j i))) ∈ Kj j c') →
      ∀ lam : J → ℤ, ∃ (H : HingeFam J d) (Mh : J → ℝ), (∀ j c', ∑' l, H.w j c' l ≤ Mh j) ∧
        (∀ κ : GenDecoration S d roots 0, selSk κ → ∀ τ ∈ splicedTimeDomain S layer tt, ∀ j c',
          (∀ i, ‖(base + latticePoint L (κ.1 (hmom j i))) - latPt d (c' i)‖ ≤ 1) →
          HasSum (fun l => (H.w j c' l : ℂ) * H.a j c' l (fun i => base + latticePoint L (κ.1 (hmom j i))) *
            fsPhase (H.m j c' l) (fun i => clockOf S tt τ (hclk j i)))
            (HkM j (lam j) (fun i => clockOf S tt τ (hclk j i))
              (fun i => base + latticePoint L (κ.1 (hmom j i))))) ∧
        ∏ j, Mh j = C ^ Fintype.card J * (∏ j, M0 j) * ∏ j, (1 + |((lam j : ℤ) : ℝ)|) ^ c := by
  obtain ⟨C, hC, hex⟩ := exists_hinge_data hθ d
  refine ⟨C, hC, fun {w} S J _ Dj Kj σ HkM M0 c hM0 hcont hbd L base tt roots selSk layer hmom hclk G1 G2 lam => ?_⟩
  obtain ⟨H, hH1, hH2⟩ := hex S J Dj Kj σ (fun j => HkM j (lam j))
    (fun j => (1 + |((lam j : ℤ) : ℝ)|) ^ c * M0 j)
    (fun j => mul_nonneg (by positivity) (hM0 j)) (fun j c' E hE => hcont j c' (lam j) E hE)
    (fun j c' => hbd j c' (lam j)) L base tt roots selSk layer hmom hclk G1 G2
  refine ⟨H, fun j => C * ((1 + |((lam j : ℤ) : ℝ)|) ^ c * M0 j), fun j c' => ?_, hH2, ?_⟩
  · exact hH1 j c'
  · rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    ring

end WaveTurbulence.Represents
