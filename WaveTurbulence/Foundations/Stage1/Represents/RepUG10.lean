/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepLfClk1
public import WaveTurbulence.Foundations.Stage1.Represents.RepUG9
import Mathlib.Tactic

/-!
# S2 REPRESENTS, G1 (2): the leaf-clock hinge data with the weak output box

`exists_hinge_data_mod_ck_w` and `exists_hinge_data_units_leaf_w` are `exists_hinge_data_mod_ck` / `exists_hinge_data_units_leaf` with
G1 asked in the weak box `outBoxW` (the dummy time of a leaf lower child may then be `qOut i`) and the hypothesis
`qOut 1, qOut 2 ≤ qOut 0` (children's layers do not exceed the layer of the top joint).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RepAnalytic
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed
  WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C VineParamContract
open scoped ENNReal Classical

/-- `exists_hinge_data_mod_ck` with the weak box `outBoxW` in G1 (needs `qOut 1, qOut 2 ≤ qOut 0`). -/
theorem exists_hinge_data_mod_ck_w {θ : ℝ} (hθ : 0 ≤ θ) (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {w : ℕ} (S : Garden w) (J : Type) [Fintype J] (Dj : J → (Fin 4 → Fin d → ℤ) → SumintDatum d)
      (Kj : J → (Fin 4 → Fin d → ℤ) → Set (Fin 4 → Mom d)) (σ : J → ℤˣ)
      (HkM : J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ) (M0 : J → ℝ) (c : ℝ), (∀ j, 0 ≤ M0 j) →
      (∀ j c', (Dj j c').qOut 1 ≤ (Dj j c').qOut 0 ∧ (Dj j c').qOut 2 ≤ (Dj j c').qOut 0) →
      (∀ j c' lam, ∀ E ∈ Kj j c', ContinuousOn (fun t => HkM j lam t (sumintBoundary (σ j) E)) (cubeSet (Dj j c').qOut)) →
      (∀ j c' (lam : ℤ), XNorm00Restr θ (outBox (Dj j c')) (Kj j c')
        (fun t E => HkM j lam t (sumintBoundary (σ j) E)) ≤
        ENNReal.ofReal ((1 + |(lam : ℝ)|) ^ c * M0 j)) →
      ∀ (L : ℝ) (base : Mom d) (tt : Fin w → ℝ) (roots : Fin w → Fin d → ℤ)
        (selSk : GenDecoration S d roots 0 → Prop) (layer : GBranch S.tree → ℕ)
        (hmom : J → Fin 4 → GNode S.tree) (ck : J → (GBranch S.tree → ℝ) → Fin 3 → ℝ),
      (∀ κ : GenDecoration S d roots 0, selSk κ → ∀ τ ∈ splicedTimeDomain S layer tt, ∀ j c',
        (∀ i, ‖(base + latticePoint L (κ.1 (hmom j i))) - latPt d (c' i)‖ ≤ 1) →
          ck j τ ∈ outBoxW (Dj j c')) →
      (∀ κ : GenDecoration S d roots 0, selSk κ → ∀ j c',
        (∀ i, ‖(base + latticePoint L (κ.1 (hmom j i))) - latPt d (c' i)‖ ≤ 1) →
          sumintBoundary (σ j) (fun i => base + latticePoint L (κ.1 (hmom j i))) ∈ Kj j c') →
      ∀ lam : J → ℤ, ∃ (H : HingeFam J d) (Mh : J → ℝ), (∀ j c', ∑' l, H.w j c' l ≤ Mh j) ∧
        (∀ κ : GenDecoration S d roots 0, selSk κ → ∀ τ ∈ splicedTimeDomain S layer tt, ∀ j c',
          (∀ i, ‖(base + latticePoint L (κ.1 (hmom j i))) - latPt d (c' i)‖ ≤ 1) →
          HasSum (fun l => (H.w j c' l : ℂ) * H.a j c' l (fun i => base + latticePoint L (κ.1 (hmom j i))) *
            fsPhase (H.m j c' l) (ck j τ))
            (HkM j (lam j) (ck j τ) (fun i => base + latticePoint L (κ.1 (hmom j i))))) ∧
        ∏ j, Mh j = C ^ Fintype.card J * (∏ j, M0 j) * ∏ j, (1 + |((lam j : ℤ) : ℝ)|) ^ c := by
  obtain ⟨C, hC, hex⟩ := exists_hingeFam_w hθ d
  refine ⟨C, hC, fun {w} S J _ Dj Kj σ HkM M0 c hM0 hq hcont hbd L base tt roots selSk layer hmom ck G1 G2 lam => ?_⟩
  obtain ⟨H, hH1, hH2⟩ := hex J Dj Kj σ (fun j => HkM j (lam j))
    (fun j => (1 + |((lam j : ℤ) : ℝ)|) ^ c * M0 j)
    (fun j => mul_nonneg (by positivity) (hM0 j)) hq (fun j c' E hE => hcont j c' (lam j) E hE)
    (fun j c' => hbd j c' (lam j))
  refine ⟨H, fun j => C * ((1 + |((lam j : ℤ) : ℝ)|) ^ c * M0 j), fun j c' => hH1 j c', fun κ hκ τ hτ j c' hball =>
    hH2 j c' _ (G1 κ hκ τ hτ j c' hball) _ (G2 κ hκ j c' hball), ?_⟩
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  ring

end WaveTurbulence.Represents
