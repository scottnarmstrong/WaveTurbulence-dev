/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LayerStatement

/-! # The final vine estimate statements after finding F-COUNTGAIN (ruling R54)

TARGET Step 4 (L1919-L1922) bounds the number of choices of the exceptional pair `(Q, T)` of an operative vine by `C₂ C₀^{n(Q)+n(T)}`
(Prop `layerreg2`: the layerings cost `C₀^{|q-q'|}` with `|q - q'| ≤ 𝔇`) and says that `C₂` "can be covered by the `L^{-η²}` gain for this
bad vine".  The engine (`sumint`, (FourierboundI)) gives exactly `L^{-η²}` per bad vine, which (vineest2) also keeps, so the literal
`VineEstCanonLayer` is not reached by TARGET's route.  Ruling R54: prove the two versions below; `VineEstCanonLayer` is kept unchanged.

* `VineEstCanonLayerC2`: the right-hand side of `VineEstCanonLayer` times `C₂ ^ b` (`b` = number of bad vines of `U`).
* `VineEstCanonLayerHalf`: the bad-vine gain `L^{-(η²/2) b}` in place of `L^{-η² b}`, no extra factor (in prefix form `C₂ ^ b ≤ L^{(η²/2) b}`
  for `L ≥ C₂^{2/η²}`, since `C₂` is chosen after `δ, 𝔇` and `L` after `C₂`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton
  WaveTurbulence.VineEstS4 VineParamContract TTree
open scoped ENNReal

/-- **TARGET Proposition `vineest`, layer-uniform form, with the class-count factor `C₂ ^ b` (R54 (i)).**  Identical to
`VineEstCanonLayer` except for the factor `P.C₂ ^ b` on the right-hand side, `b` the number of bad vines of the chain. -/
def VineEstCanonLayerC2 (P : WTParams) : Prop :=
  ∀ {p : ℕ}, p < P.D → ∀ (h : ℕ → Mom P.d → ℝ) (B₀ : ℝ), 0 ≤ B₀ →
    (∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (h r) ≤ ENNReal.ofReal B₀) →
    ∀ {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
      {n : ℕ} (_hprime : IsPrimeGarden G) (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
      (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer), (∀ x, layer x ≤ p) →
    (RD.garden hG).order ≤ P.N (p + 1) ^ 4 → clLocalOrder1 R ≤ P.N 1 ^ 4 →
    ∀ (centre : Fin 4 → Mom P.d) (wBar : Mom P.d),
    RowCoherent hM9 B RD hG layer hLayer (step3W hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      P.L P.γ P.δ h p →
    XNorm00Restr (2 * P.η ^ 8) (outBox (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar))
      (outSet (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar) P.L P.γ P.η)
      (fun tt E => twistedRecentered (rowSel := VineEst.RowSel.plain) G a (canonFinset p (startState B RD hG layer hLayer) (chainStart B))
        P.L P.γ P.δ h wBar
        (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
        (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)) ≤
    ENNReal.ofReal ((P.C₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R *
      P.L ^ (-(P.η ^ 8 * ((cohmolIndex B RD hG layer +
        (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
        P.η ^ 2 * ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) + P.η ^ 7) *
      regionLeafSize RD hG R layer hLayer (fun _ => B₀) *
      P.C₂ ^ (Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card)

/-- **TARGET Proposition `vineest`, layer-uniform form, with the halved bad-vine gain `L^{-(η²/2) b}` (R54 (ii)).**  Identical to
`VineEstCanonLayer` except for the exponent `-(η²/2) b` in place of `-η² b`. -/
def VineEstCanonLayerHalf (P : WTParams) : Prop :=
  ∀ {p : ℕ}, p < P.D → ∀ (h : ℕ → Mom P.d → ℝ) (B₀ : ℝ), 0 ≤ B₀ →
    (∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (h r) ≤ ENNReal.ofReal B₀) →
    ∀ {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
      {n : ℕ} (_hprime : IsPrimeGarden G) (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
      (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer), (∀ x, layer x ≤ p) →
    (RD.garden hG).order ≤ P.N (p + 1) ^ 4 → clLocalOrder1 R ≤ P.N 1 ^ 4 →
    ∀ (centre : Fin 4 → Mom P.d) (wBar : Mom P.d),
    RowCoherent hM9 B RD hG layer hLayer (step3W hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      P.L P.γ P.δ h p →
    XNorm00Restr (2 * P.η ^ 8) (outBox (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar))
      (outSet (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar) P.L P.γ P.η)
      (fun tt E => twistedRecentered (rowSel := VineEst.RowSel.plain) G a (canonFinset p (startState B RD hG layer hLayer) (chainStart B))
        P.L P.γ P.δ h wBar
        (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
        (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)) ≤
    ENNReal.ofReal ((P.C₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R *
      P.L ^ (-(P.η ^ 8 * ((cohmolIndex B RD hG layer +
        (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
        P.η ^ 2 / 2 * ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) + P.η ^ 7) *
      regionLeafSize RD hG R layer hLayer (fun _ => B₀))

theorem regionLeafSize_const_nonneg {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (RD : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) {B₀ : ℝ} (hB₀ : 0 ≤ B₀) :
    0 ≤ regionLeafSize RD hG R layer hLayer (fun _ => B₀) := by
  unfold regionLeafSize
  exact mul_nonneg (Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => hB₀)
    (Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => hB₀)

/-- The arithmetic of R54 (ii): `C₂ ^ b ≤ L ^ ((η²/2) b)` turns the `C₂ ^ b` form into the halved-gain form. -/
theorem half_of_C2_real {A Rs C₂ L η x y : ℝ} {k : ℕ} (hA : 0 ≤ A) (hR : 0 ≤ Rs) (hL : 0 < L)
    (hC : C₂ ^ k ≤ L ^ (η ^ 2 / 2 * (k : ℝ))) :
    A * L ^ (x - η ^ 2 * (k : ℝ) + y) * Rs * C₂ ^ k ≤ A * L ^ (x - η ^ 2 / 2 * (k : ℝ) + y) * Rs := by
  have h1 : L ^ (x - η ^ 2 * (k : ℝ) + y) * C₂ ^ k ≤ L ^ (x - η ^ 2 / 2 * (k : ℝ) + y) := by
    have hsplit : L ^ (x - η ^ 2 / 2 * (k : ℝ) + y) = L ^ (x - η ^ 2 * (k : ℝ) + y) * L ^ (η ^ 2 / 2 * (k : ℝ)) := by
      rw [← Real.rpow_add hL]; ring_nf
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left hC (Real.rpow_nonneg hL.le _)
  calc A * L ^ (x - η ^ 2 * (k : ℝ) + y) * Rs * C₂ ^ k = A * (L ^ (x - η ^ 2 * (k : ℝ) + y) * C₂ ^ k) * Rs := by ring
    _ ≤ A * L ^ (x - η ^ 2 / 2 * (k : ℝ) + y) * Rs :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hA) hR

/-- `C₂ ≤ L ^ (η²/2)` once `L ≥ C₂ ^ (2/η²)`. -/
theorem C2_pow_le {C₂ L η : ℝ} (k : ℕ) (hη : 0 < η) (hC : 1 ≤ C₂) (hL : C₂ ^ (2 / η ^ 2) ≤ L) :
    C₂ ^ k ≤ L ^ (η ^ 2 / 2 * (k : ℝ)) := by
  have hC0 : 0 ≤ C₂ := by linarith
  have h1 : C₂ ≤ L ^ (η ^ 2 / 2) := by
    have hη2 : 0 < η ^ 2 / 2 := by positivity
    calc C₂ = (C₂ ^ (2 / η ^ 2)) ^ (η ^ 2 / 2) := by
            rw [← Real.rpow_mul hC0]; field_simp; simp
      _ ≤ L ^ (η ^ 2 / 2) := Real.rpow_le_rpow (Real.rpow_nonneg hC0 _) hL hη2.le
  have hL0 : 0 ≤ L := le_trans (Real.rpow_nonneg hC0 _) hL
  calc C₂ ^ k ≤ (L ^ (η ^ 2 / 2)) ^ k := pow_le_pow_left₀ hC0 h1 k
    _ = L ^ (η ^ 2 / 2 * (k : ℝ)) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0]

/-- **R54 (ii) from (i)**: the halved-gain statement follows from the `C₂ ^ b` statement in prefix form (enlarge `L₀` to `C₂^{2/η²}`). -/
theorem vineEstCanonLayerHalf_of_C2 (H : WTPrefix VineEstCanonLayerC2) : WTPrefix VineEstCanonLayerHalf := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H1⟩ := H d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin hφin τ hτ φ hsol => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H2⟩ := H1 η hη φin hφin τ hτ φ hsol
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, H3⟩ := H2 ν hν
  refine ⟨δ₀, hδ₀, fun δ hδ D hD htime => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H4⟩ := H3 δ hδ D hD htime
  refine ⟨C₂, hC₂, max L₀ (C₂ ^ (2 / η ^ 2)), le_max_of_le_left hL₀, fun L hL => ?_⟩
  have hLL₀ : L₀ ≤ L := (le_max_left _ _).trans hL
  have hLC : C₂ ^ (2 / η ^ 2) ≤ L := (le_max_right _ _).trans hL
  have hLpos : 0 < L := by linarith
  have key : VineEstCanonLayerC2 ⟨d, γ, η, φin, τ, φ, C₁, ν, δ, D, C₂, L⟩ := H4 L hLL₀
  intro p hp h B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer hlay hord hl1 centre wBar hcoh
  refine (key hp h B₀ hB₀ hh hprime hM9 B RD hG layer hLayer hlay hord hl1 centre wBar hcoh).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hδ0 : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg _
  exact half_of_C2_real (pow_nonneg (mul_nonneg (by linarith) hδ0) _)
    (regionLeafSize_const_nonneg RD hG R layer hLayer hB₀) hLpos (C2_pow_le _ hη.1 hC₂ hLC)

/-- **TARGET Proposition `vineest`, layer-uniform form, with the class-count factor `C₂ ^ b` (R54 (i)).**  Identical to
`VineEstCanonLayer` except for the factor `P.C₂ ^ b` on the right-hand side, `b` the number of bad vines of the chain. -/
def VineEstCanonLayerC2K (P : WTParams) : Prop :=
  ∀ {p : ℕ}, p < P.D → ∀ (h : ℕ → Mom P.d → ℝ) (B₀ : ℝ), 0 ≤ B₀ →
    (∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (h r) ≤ ENNReal.ofReal B₀) →
    ∀ {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
      {n : ℕ} (_hprime : IsPrimeGarden G) (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
      (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (kind : Bool), CanonicalObject p kind (layeredReconstruction RD hG layer hLayer) → (∀ x, layer x ≤ p) →
    (RD.garden hG).order ≤ P.N (p + 1) ^ 4 → clLocalOrder1 R ≤ P.N 1 ^ 4 →
    ∀ (centre : Fin 4 → Mom P.d) (wBar : Mom P.d),
    RowCoherent hM9 B RD hG layer hLayer (step3W hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      P.L P.γ P.δ h p →
    XNorm00Restr (2 * P.η ^ 8) (outBox (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar))
      (outSet (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar) P.L P.γ P.η)
      (fun tt E => twistedRecentered (rowSel := VineEst.RowSel.plain) G a (canonFinsetK p kind (startState B RD hG layer hLayer) (chainStart B))
        P.L P.γ P.δ h wBar
        (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
        (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)) ≤
    ENNReal.ofReal ((P.C₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R *
      P.L ^ (-(P.η ^ 8 * ((cohmolIndex B RD hG layer +
        (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
        P.η ^ 2 * ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) + P.η ^ 7) *
      regionLeafSize RD hG R layer hLayer (fun _ => B₀) *
      P.C₂ ^ (Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card)

/-- **TARGET Proposition `vineest`, layer-uniform form, with the halved bad-vine gain `L^{-(η²/2) b}` (R54 (ii)).**  Identical to
`VineEstCanonLayer` except for the exponent `-(η²/2) b` in place of `-η² b`. -/
def VineEstCanonLayerHalfK (P : WTParams) : Prop :=
  ∀ {p : ℕ}, p < P.D → ∀ (h : ℕ → Mom P.d → ℝ) (B₀ : ℝ), 0 ≤ B₀ →
    (∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (h r) ≤ ENNReal.ofReal B₀) →
    ∀ {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
      {n : ℕ} (_hprime : IsPrimeGarden G) (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
      (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (kind : Bool), CanonicalObject p kind (layeredReconstruction RD hG layer hLayer) → (∀ x, layer x ≤ p) →
    (RD.garden hG).order ≤ P.N (p + 1) ^ 4 → clLocalOrder1 R ≤ P.N 1 ^ 4 →
    ∀ (centre : Fin 4 → Mom P.d) (wBar : Mom P.d),
    RowCoherent hM9 B RD hG layer hLayer (step3W hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      P.L P.γ P.δ h p →
    XNorm00Restr (2 * P.η ^ 8) (outBox (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar))
      (outSet (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar) P.L P.γ P.η)
      (fun tt E => twistedRecentered (rowSel := VineEst.RowSel.plain) G a (canonFinsetK p kind (startState B RD hG layer hLayer) (chainStart B))
        P.L P.γ P.δ h wBar
        (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
        (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)) ≤
    ENNReal.ofReal ((P.C₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R *
      P.L ^ (-(P.η ^ 8 * ((cohmolIndex B RD hG layer +
        (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
        P.η ^ 2 / 2 * ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) + P.η ^ 7) *
      regionLeafSize RD hG R layer hLayer (fun _ => B₀))

/-- **R54 (ii) from (i)**: the halved-gain statement follows from the `C₂ ^ b` statement in prefix form (enlarge `L₀` to `C₂^{2/η²}`). -/
theorem vineEstCanonLayerHalfK_of_C2K (H : WTPrefix VineEstCanonLayerC2K) : WTPrefix VineEstCanonLayerHalfK := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H1⟩ := H d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin hφin τ hτ φ hsol => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H2⟩ := H1 η hη φin hφin τ hτ φ hsol
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, H3⟩ := H2 ν hν
  refine ⟨δ₀, hδ₀, fun δ hδ D hD htime => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H4⟩ := H3 δ hδ D hD htime
  refine ⟨C₂, hC₂, max L₀ (C₂ ^ (2 / η ^ 2)), le_max_of_le_left hL₀, fun L hL => ?_⟩
  have hLL₀ : L₀ ≤ L := (le_max_left _ _).trans hL
  have hLC : C₂ ^ (2 / η ^ 2) ≤ L := (le_max_right _ _).trans hL
  have hLpos : 0 < L := by linarith
  have key : VineEstCanonLayerC2K ⟨d, γ, η, φin, τ, φ, C₁, ν, δ, D, C₂, L⟩ := H4 L hLL₀
  intro p hp h B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre wBar hcoh
  refine (key hp h B₀ hB₀ hh hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre wBar hcoh).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hδ0 : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg _
  exact half_of_C2_real (pow_nonneg (mul_nonneg (by linarith) hδ0) _)
    (regionLeafSize_const_nonneg RD hG R layer hLayer hB₀) hLpos (C2_pow_le _ hη.1 hC₂ hLC)

end WaveTurbulence.VineEstS5C
