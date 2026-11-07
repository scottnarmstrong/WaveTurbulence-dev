/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepV1
public import WaveTurbulence.Foundations.Stage1.Represents.RepH6
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-D: the hinge side of a mode (`hHk`, `Mh`) from per-centre VINEEST bounds

`exists_hinge_data`: the hinge family `H` of `exists_hingeFam` for the vine factors `Hk j`, together with the field `hHk`
of `AsmCtxH` (valid in the unit balls around `c`), given the VINE-B♯ geometry:
(G1) the three unit clocks of a selected decoration at a time of the spliced domain lie in `outBox (Dj j c)`;
(G2) the hinge momenta, in the `sumint` order, lie in `Kj j c` (= `outSet`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RepAnalytic
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS3.Eng
open scoped ENNReal

theorem exists_hinge_data {θ : ℝ} (hθ : 0 ≤ θ) (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {w : ℕ} (S : Garden w) (J : Type) (Dj : J → (Fin 4 → Fin d → ℤ) → SumintDatum d)
      (Kj : J → (Fin 4 → Fin d → ℤ) → Set (Fin 4 → Mom d)) (σ : J → ℤˣ)
      (Hk : J → (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ) (M : J → ℝ), (∀ j, 0 ≤ M j) →
      (∀ j c, ∀ E ∈ Kj j c, ContinuousOn (fun t => Hk j t (sumintBoundary (σ j) E)) (cubeSet (Dj j c).qOut)) →
      (∀ j c, XNorm00Restr θ (outBox (Dj j c)) (Kj j c) (fun t E => Hk j t (sumintBoundary (σ j) E)) ≤
        ENNReal.ofReal (M j)) →
      ∀ (L : ℝ) (base : Mom d) (tt : Fin w → ℝ) (roots : Fin w → Fin d → ℤ)
        (selSk : GenDecoration S d roots 0 → Prop) (layer : GBranch S.tree → ℕ)
        (hmom : J → Fin 4 → GNode S.tree) (hclk : J → Fin 3 → ClkSrc S),
      (∀ κ : GenDecoration S d roots 0, selSk κ → ∀ τ ∈ splicedTimeDomain S layer tt, ∀ j c,
        (∀ i, ‖(base + latticePoint L (κ.1 (hmom j i))) - latPt d (c i)‖ ≤ 1) →
          (fun i => clockOf S tt τ (hclk j i)) ∈ outBox (Dj j c)) →
      (∀ κ : GenDecoration S d roots 0, selSk κ → ∀ j c,
        (∀ i, ‖(base + latticePoint L (κ.1 (hmom j i))) - latPt d (c i)‖ ≤ 1) →
          sumintBoundary (σ j) (fun i => base + latticePoint L (κ.1 (hmom j i))) ∈ Kj j c) →
      ∃ H : HingeFam J d, (∀ j c, ∑' l, H.w j c l ≤ C * M j) ∧
        ∀ κ : GenDecoration S d roots 0, selSk κ → ∀ τ ∈ splicedTimeDomain S layer tt, ∀ j c,
          (∀ i, ‖(base + latticePoint L (κ.1 (hmom j i))) - latPt d (c i)‖ ≤ 1) →
          HasSum (fun l => (H.w j c l : ℂ) * H.a j c l (fun i => base + latticePoint L (κ.1 (hmom j i))) *
            fsPhase (H.m j c l) (fun i => clockOf S tt τ (hclk j i)))
            (Hk j (fun i => clockOf S tt τ (hclk j i)) (fun i => base + latticePoint L (κ.1 (hmom j i)))) := by
  obtain ⟨C, hC, hex⟩ := exists_hingeFam hθ d
  refine ⟨C, hC, fun {w} S J Dj Kj σ Hk M hM hcont hbd L base tt roots selSk layer hmom hclk G1 G2 => ?_⟩
  obtain ⟨H, hH1, hH2⟩ := hex J Dj Kj σ Hk M hM hcont hbd
  exact ⟨H, hH1, fun κ hκ τ hτ j c hball =>
    hH2 j c _ (G1 κ hκ τ hτ j c hball) _ (G2 κ hκ j c hball)⟩

end WaveTurbulence.Represents
