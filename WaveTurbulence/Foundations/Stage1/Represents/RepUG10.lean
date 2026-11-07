/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepLfClk2
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

theorem exists_hinge_data_units_leaf_w (P : WTParams) (hV : VineEstCanonLayerHalfMK P) (hη0 : 0 ≤ P.η)
    (hC₁ : 0 ≤ P.C₁) (hL0 : 0 < P.L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p : ℕ}, p < P.D → ∀ {w : ℕ} {S : Garden w} (hprime : IsPrimeGarden S) (hM9 : VINEPARAM)
      (RD : ReconstructionData S) (hG : S.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
      (hLayer : IsLayering (RD.garden hG) layer) (hcan : IsCanonGC (p + 1) (layeredReconstruction RD hG layer hLayer))
      (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4)
      {J : Type} [Fintype J] {U₀ : J → Finset (GBranch S.tree)} {a₀ b₀ : J → GBranch S.tree}
      {R₀ : ∀ j, CLRegionData S (U₀ j) (a₀ j) (b₀ j)} {n₀ : J → ℕ} (B₀ : ∀ j, CLChainAssembly S (R₀ j) (n₀ j))
      (hcl : ∀ j, clLocalOrder1 (R₀ j) ≤ P.N 1 ^ 4)
      (h : J → ℕ → Mom P.d → ℝ) (bb : J → ℝ) (hbb : ∀ j, 0 ≤ bb j)
      (hh : ∀ j, ∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (h j r) ≤ ENNReal.ofReal (bb j))
      (centre : J → (Fin 4 → Fin P.d → ℤ) → Fin 4 → Mom P.d) (base : Mom P.d)
      (hq : ∀ j, qOutOf RD hG layer (a₀ j) (b₀ j) (R₀ j) 1 ≤ qOutOf RD hG layer (a₀ j) (b₀ j) (R₀ j) 0 ∧
        qOutOf RD hG layer (a₀ j) (b₀ j) (R₀ j) 2 ≤ qOutOf RD hG layer (a₀ j) (b₀ j) (R₀ j) 0)
      (hcont : ∀ j c (lam : ℤ), ∀ E ∈ outSet (unitD hM9 (B₀ j) RD hG layer hLayer (centre j c) base) P.L P.γ P.η,
        ContinuousOn (fun t => unitHk P p (B₀ j) RD hG layer hLayer (h j) base lam t
          (sumintBoundary (S.sign (a₀ j).toNode) E))
          (cubeSet (unitD hM9 (B₀ j) RD hG layer hLayer (centre j c) base).qOut))
      (Gsb : Garden w) (tt : Fin w → ℝ) (roots : Fin w → Fin P.d → ℤ)
      (selSk : GenDecoration Gsb P.d roots 0 → Prop) (lay : GBranch Gsb.tree → ℕ)
      (hmom : J → Fin 4 → GNode Gsb.tree) (hclk : J → Fin 3 → ClkSrc Gsb)
      (leaf : J → Fin 3 → Prop) (td : J → Fin 3 → ℝ)
      (hind : ∀ j (lam : ℤ) (t t' : Fin 3 → ℝ) (k : Fin 4 → Mom P.d), (∀ i, ¬ leaf j i → t i = t' i) →
        unitHk P p (B₀ j) RD hG layer hLayer (h j) base lam t k =
          unitHk P p (B₀ j) RD hG layer hLayer (h j) base lam t' k),
      (∀ κ : GenDecoration Gsb P.d roots 0, selSk κ → ∀ τ ∈ splicedTimeDomain Gsb lay tt, ∀ j c,
        (∀ i, ‖(base + latticePoint P.L (κ.1 (hmom j i))) - latPt P.d (c i)‖ ≤ 1) →
          (fun i => if leaf j i then td j i else clockOf Gsb tt τ (hclk j i)) ∈
            outBoxW (unitD hM9 (B₀ j) RD hG layer hLayer (centre j c) base)) →
      (∀ κ : GenDecoration Gsb P.d roots 0, selSk κ → ∀ j c,
        (∀ i, ‖(base + latticePoint P.L (κ.1 (hmom j i))) - latPt P.d (c i)‖ ≤ 1) →
          sumintBoundary (S.sign (a₀ j).toNode) (fun i => base + latticePoint P.L (κ.1 (hmom j i))) ∈
            outSet (unitD hM9 (B₀ j) RD hG layer hLayer (centre j c) base) P.L P.γ P.η) →
      ∀ lam : J → ℤ, ∃ (H : HingeFam J P.d) (Mh : J → ℝ), (∀ j c', ∑' l, H.w j c' l ≤ Mh j) ∧
        (∀ κ : GenDecoration Gsb P.d roots 0, selSk κ → ∀ τ ∈ splicedTimeDomain Gsb lay tt, ∀ j c',
          (∀ i, ‖(base + latticePoint P.L (κ.1 (hmom j i))) - latPt P.d (c' i)‖ ≤ 1) →
          HasSum (fun l => (H.w j c' l : ℂ) * H.a j c' l (fun i => base + latticePoint P.L (κ.1 (hmom j i))) *
            fsPhase (H.m j c' l) (fun i => clockOf Gsb tt τ (hclk j i)))
            (unitHk P p (B₀ j) RD hG layer hLayer (h j) base (lam j) (fun i => clockOf Gsb tt τ (hclk j i))
              (fun i => base + latticePoint P.L (κ.1 (hmom j i))))) ∧
        ∏ j, Mh j = C ^ Fintype.card J *
          (∏ j, unitMass P hM9 (B₀ j) RD hG layer hLayer (bb j)) *
          ∏ j, (1 + |((lam j : ℤ) : ℝ)|) ^ (6 * P.η ^ 6) := by
  obtain ⟨C, hC, hex⟩ := exists_hinge_data_mod_ck_w (θ := 2 * P.η ^ 8) (by positivity) P.d
  refine ⟨C, hC, fun {p} hp {w} {S} hprime hM9 RD hG layer hLayer hcan hord {J} _ {U₀} {a₀} {b₀} {R₀} {n₀} B₀ hcl h bb hbb hh
    centre base hq hcont Gsb tt roots selSk lay hmom hclk leaf td hind G1 G2 lam => ?_⟩
  have hM0 : ∀ j, 0 ≤ unitMass P hM9 (B₀ j) RD hG layer hLayer (bb j) := fun j =>
    mul_nonneg (mul_nonneg (pow_nonneg (mul_nonneg hC₁ (Real.sqrt_nonneg _)) _) (Real.rpow_nonneg hL0.le _))
      (WaveTurbulence.VineEstS5C.regionLeafSize_const_nonneg RD hG (R₀ j) layer hLayer (hbb j))
  obtain ⟨H, Mh, hMh, hsum, hprod⟩ := hex Gsb J (fun j c => unitD hM9 (B₀ j) RD hG layer hLayer (centre j c) base)
    (fun j c => outSet (unitD hM9 (B₀ j) RD hG layer hLayer (centre j c) base) P.L P.γ P.η)
    (fun j => S.sign (a₀ j).toNode) (fun j lam t k => unitHk P p (B₀ j) RD hG layer hLayer (h j) base lam t k)
    (fun j => unitMass P hM9 (B₀ j) RD hG layer hLayer (bb j)) (6 * P.η ^ 6) hM0
    (fun j c' => hq j) hcont (fun j c lam => by
      have := unit_vineest_bound hV hp (h j) (bb j) (hbb j) (hh j) hprime hM9 (B₀ j) RD hG layer hLayer hcan hord
        (hcl j) (centre j c) base (lam : ℝ)
      have hM := step3D_M₁_const hM9 (B₀ j) RD hG layer hLayer (centre j c) (fun _ => (0 : Mom P.d)) base 0
      refine le_of_le_of_eq this ?_
      unfold unitMass
      rw [hM]) P.L base tt roots selSk lay hmom
    (fun j τ i => if leaf j i then td j i else clockOf Gsb tt τ (hclk j i)) G1 G2 lam
  refine ⟨H.leafWrap leaf td, Mh, hMh, fun κ hκ τ hτ j c' hball => ?_, hprod⟩
  have h1 := hsum κ hκ τ hτ j c' hball
  rw [hind j (lam j) _ (fun i => clockOf Gsb tt τ (hclk j i)) _ (fun i hi => by simp [hi])] at h1
  exact H.leafWrap_hasSum leaf td j c' _ (fun i => clockOf Gsb tt τ (hclk j i)) h1

end WaveTurbulence.Represents
