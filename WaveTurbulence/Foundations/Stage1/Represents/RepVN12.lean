/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVN8
public import WaveTurbulence.Foundations.Stage1.Represents.RepVN11
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-D/E: the hinge data of every unit from VINEEST(λ)

`unitMass`: the VINEEST mass `M0 j` of a unit, without the modulation loss (independent of the centre: `M₁` is read from
`rowCoupleG`/`rowTreeG`).  `exists_hinge_data_units`: for every modulation `lam : J → ℤ`, hinge families `H` and masses
`Mh` for the units `j : J` (VINE-A/C data `U₀ a₀ b₀ R₀ B₀` over the skeleton `S`) with the hinge superposition property
and `Π_j Mh_j ≤ C^{|J|} Π_j M0_j Π_j (1 + |λ_j|)^{6η⁶}`.  Named inputs: `hcont` (V5-CONT, kind-generic: V5-KIND),
`G1`, `G2` (VINE-B♯ geometry).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton
  WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C VineParamContract TTree WaveTurbulence.LGSpine
  WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3.FS
open scoped ENNReal

/-- The VINEEST mass of a unit (without the modulation loss). -/
noncomputable def unitMass (P : WTParams) {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {R : CLRegionData G U a b} {n : ℕ} (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (B₀ : ℝ) : ℝ :=
  (P.C₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R *
      P.L ^ (-(P.η ^ 8 * ((cohmolIndex B RD hG layer +
        (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R)
          (fun _ => (0 : Mom P.d)) (0 : Mom P.d)).M₁ : ℕ) : ℝ)) -
        P.η ^ 2 / 2 * ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) + P.η ^ 7) *
      regionLeafSize RD hG R layer hLayer (fun _ => B₀)

theorem step3D_M₁_const {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {R : CLRegionData G U a b} {n : ℕ} {d : ℕ} (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (RD : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer) (c c' : Fin 4 → Mom d) (wb wb' : Mom d) :
    (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) c wb).M₁ =
      (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) c' wb').M₁ :=
  rfl

/-- The `sumint` datum of the unit at the centre `centre` and offset `wBar`. -/
noncomputable abbrev unitD {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {R : CLRegionData G U a b} {n : ℕ} (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (RD : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer) (centre : Fin 4 → Mom d) (wBar : Mom d) : SumintDatum d :=
  step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar

/-- The modulated class kernel of the unit, curried as in `outerValM`. -/
noncomputable def unitHk (P : WTParams) (p : ℕ) {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} (B : CLChainAssembly G R n)
    (RD : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer) (h : ℕ → Mom P.d → ℝ) (wBar : Mom P.d) :
    ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ := fun lam t k =>
  WaveTurbulence.VineEstS5C.Cont.twistedRecenteredModC G a
    (canonFinsetK p (objKind w) (startState B RD hG layer hLayer) (chainStart B))
    P.L P.γ P.δ h wBar (lam : ℝ) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)

theorem exists_hinge_data_units (P : WTParams) (hV : VineEstCanonLayerHalfMK P) (hη0 : 0 ≤ P.η)
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
      (hcont : ∀ j c (lam : ℤ), ∀ E ∈ outSet (unitD hM9 (B₀ j) RD hG layer hLayer (centre j c) base) P.L P.γ P.η,
        ContinuousOn (fun t => unitHk P p (B₀ j) RD hG layer hLayer (h j) base lam t
          (sumintBoundary (S.sign (a₀ j).toNode) E))
          (cubeSet (unitD hM9 (B₀ j) RD hG layer hLayer (centre j c) base).qOut))
      (Gsb : Garden w) (tt : Fin w → ℝ) (roots : Fin w → Fin P.d → ℤ)
      (selSk : GenDecoration Gsb P.d roots 0 → Prop) (lay : GBranch Gsb.tree → ℕ)
      (hmom : J → Fin 4 → GNode Gsb.tree) (hclk : J → Fin 3 → ClkSrc Gsb),
      (∀ κ : GenDecoration Gsb P.d roots 0, selSk κ → ∀ τ ∈ splicedTimeDomain Gsb lay tt, ∀ j c,
        (∀ i, ‖(base + latticePoint P.L (κ.1 (hmom j i))) - latPt P.d (c i)‖ ≤ 1) →
          (fun i => clockOf Gsb tt τ (hclk j i)) ∈
            outBox (unitD hM9 (B₀ j) RD hG layer hLayer (centre j c) base)) →
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
  obtain ⟨C, hC, hex⟩ := exists_hinge_data_mod (θ := 2 * P.η ^ 8) (by positivity) P.d
  refine ⟨C, hC, fun {p} hp {w} {S} hprime hM9 RD hG layer hLayer hcan hord {J} _ {U₀} {a₀} {b₀} {R₀} {n₀} B₀ hcl h bb hbb hh
    centre base hcont Gsb tt roots selSk lay hmom hclk G1 G2 lam => ?_⟩
  have hM0 : ∀ j, 0 ≤ unitMass P hM9 (B₀ j) RD hG layer hLayer (bb j) := fun j =>
    mul_nonneg (mul_nonneg (pow_nonneg (mul_nonneg hC₁ (Real.sqrt_nonneg _)) _) (Real.rpow_nonneg hL0.le _))
      (WaveTurbulence.VineEstS5C.regionLeafSize_const_nonneg RD hG (R₀ j) layer hLayer (hbb j))
  exact hex Gsb J (fun j c => unitD hM9 (B₀ j) RD hG layer hLayer (centre j c) base)
    (fun j c => outSet (unitD hM9 (B₀ j) RD hG layer hLayer (centre j c) base) P.L P.γ P.η)
    (fun j => S.sign (a₀ j).toNode) (fun j lam t k => unitHk P p (B₀ j) RD hG layer hLayer (h j) base lam t k)
    (fun j => unitMass P hM9 (B₀ j) RD hG layer hLayer (bb j)) (6 * P.η ^ 6) hM0
    hcont (fun j c lam => by
      have := unit_vineest_bound hV hp (h j) (bb j) (hbb j) (hh j) hprime hM9 (B₀ j) RD hG layer hLayer hcan hord
        (hcl j) (centre j c) base (lam : ℝ)
      have hM := step3D_M₁_const hM9 (B₀ j) RD hG layer hLayer (centre j c) (fun _ => (0 : Mom P.d)) base 0
      refine le_of_le_of_eq this ?_
      unfold unitMass
      rw [hM]) P.L base tt roots selSk lay hmom hclk G1 G2 lam

end WaveTurbulence.Represents
