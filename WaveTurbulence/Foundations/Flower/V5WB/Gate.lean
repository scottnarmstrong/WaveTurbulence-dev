/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5WB.Final
public import WaveTurbulence.Foundations.Flower.Stage1WVine.WPrefix

/-! # V5W-B-WORLD: the weighted Stage-1 gate from the `S = none` half

STAGE1W-VINE's consumer `stage1ReductionGateFW_of_frontier (hV : V5FrontierClassBound)` reads the staged bound only at the
top filter `S = none` (`unit_vineest_boundW`: `hV … none (fun s hs => by cases hs)`).  The declarations threading `hV`
are copied by source from `Flower/Stage1WVine/{WHinge1, WHinge2, WAssembly, WPrefix}.lean` (see `COPIED-SHA256SUMS`;
`unit_vineest_boundW`, `hinge_units_constW`, `unit_hinge_dataW`, `vineCaseRepresentsFW_of_gate`,
`vineCaseRepresentsFW_of_frontier`, `stage1ReductionGateFW_of_frontier`, renamed with the suffix `N`) with the hypothesis
weakened to the `S = none` half `V5FrontierClassBoundOnAt (· = none)` (the one application gains the premise `rfl : none =
none`; the monotonicity is `v5FrontierClassBoundOnAt_mono`).  With `v5FrontierClassBoundNone` this makes the weighted
Stage-1 reduction gate unconditional: **`stage1ReductionGateFW : Stage1ReductionGateFW`**.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.V5WB
open WaveTurbulence.Flower.Stage1WVine

section
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RepAnalytic
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed WaveTurbulence.Represents
  WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C VineParamContract WaveTurbulence.Flower.Stage1W
  WaveTurbulence.Flower.V5W
open scoped ENNReal

/-- The X-norm bound of a weighted unit class kernel, from the `S = none` half of the bound. -/
theorem unit_vineest_boundWN {P : WTParams} (hV : V5FrontierClassBoundOnAt (· = none) P) {p : ℕ} (hp : p < P.D)
    (h : ℕ → Mom P.d → ℝ) (B₀ : ℝ) (hB₀ : 0 ≤ B₀)
    (hh : ∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (h r) ≤ ENNReal.ofReal B₀)
    {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
    {n : ℕ} (hprime : IsPrimeGarden G) (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
    (hcan : IsCanonGC (p + 1) (layeredReconstruction RD hG layer hLayer))
    (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4) (hcl : clLocalOrder1 R ≤ P.N 1 ^ 4)
    (g : Fin w → Mom P.d → ℂ) (cψ : ℝ) (hc : 1 ≤ cψ) (hgp : ∀ j, GPresented (32 * P.d) (g j) cψ)
    (hre : ∀ j x, (g j x).im = 0) (centre : Fin 4 → Mom P.d) (wBar : Mom P.d) (lam : ℤ) :
    XNorm00Restr (2 * P.η ^ 8) (outBox (unitD hM9 B RD hG layer hLayer centre wBar))
      (outSet (unitD hM9 B RD hG layer hLayer centre wBar) P.L P.γ P.η)
      (fun t E => unitHkFW P p B RD hG layer hLayer g h wBar lam t (sumintBoundary (G.sign a.toNode) E)) ≤
    ENNReal.ofReal ((1 + |(lam : ℝ)|) ^ (6 * P.η ^ 6) * unitMassFW P hM9 B RD hG layer hLayer cψ B₀) := by
  have hb := hV hp h B₀ hB₀ hh hprime hM9 B RD hG layer hLayer (objKind w) (canonicalObject_of_isCanonGC hcan)
    (fun x => WaveTurbulence.Canon.layer_le_of_isCanonGC hcan x) hord hcl centre wBar (lam : ℝ) g cψ hc hgp hre none rfl
    (fun s hs => by cases hs) (rowCoherent_of_canonical hM9 B RD hG layer hLayer p hcan centre wBar P.L P.γ P.δ h)
  refine le_of_le_of_eq hb ?_
  have hA : 0 ≤ cψ ^ (9 * U.card + 4 * clLocalOrder2 RD hG R) * topFilterMass :=
    mul_nonneg (pow_nonneg (by linarith) _) topFilterMass_nonneg
  rw [← ENNReal.ofReal_mul hA]
  congr 1
  unfold unitMassFW unitMass
  rw [step3D_M₁_const hM9 B RD hG layer hLayer centre (fun _ => (0 : Mom P.d)) wBar 0]
  ring


open scoped Classical in
/-- **The hinge data of the weighted units** (main's `hinge_units_const`; the constant depends only on `(d, η)`). -/
theorem hinge_units_constWN (d : ℕ) (η : ℝ) (hη : 0 ≤ η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : WTParams), P.d = d → P.η = η → V5FrontierClassBoundOnAt (· = none) P → 0 ≤ P.C₁ → 0 < P.L →
      ∀ {p : ℕ}, p < P.D → ∀ {w : ℕ} {S : Garden w} (hprime : IsPrimeGarden S) (hM9 : VINEPARAM)
      (RD : ReconstructionData S) (hG : S.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
      (hLayer : IsLayering (RD.garden hG) layer) (hcan : IsCanonGC (p + 1) (layeredReconstruction RD hG layer hLayer))
      (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4)
      {J : Type} [Fintype J] {U₀ : J → Finset (GBranch S.tree)} {a₀ b₀ : J → GBranch S.tree}
      {R₀ : ∀ j, CLRegionData S (U₀ j) (a₀ j) (b₀ j)} {n₀ : J → ℕ} (B₀ : ∀ j, CLChainAssembly S (R₀ j) (n₀ j))
      (hcl : ∀ j, clLocalOrder1 (R₀ j) ≤ P.N 1 ^ 4)
      (g : Fin w → Mom P.d → ℂ) (cψ : ℝ) (hc : 1 ≤ cψ) (hgp : ∀ j, GPresented (32 * P.d) (g j) cψ)
      (hre : ∀ j x, (g j x).im = 0)
      (h : J → ℕ → Mom P.d → ℝ) (bb : J → ℝ) (hbb : ∀ j, 0 ≤ bb j)
      (hh : ∀ j, ∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (h j r) ≤ ENNReal.ofReal (bb j))
      (centre : J → (Fin 4 → Fin P.d → ℤ) → Fin 4 → Mom P.d) (base : Mom P.d)
      (hq : ∀ j, qOutOf RD hG layer (a₀ j) (b₀ j) (R₀ j) 1 ≤ qOutOf RD hG layer (a₀ j) (b₀ j) (R₀ j) 0 ∧
        qOutOf RD hG layer (a₀ j) (b₀ j) (R₀ j) 2 ≤ qOutOf RD hG layer (a₀ j) (b₀ j) (R₀ j) 0)
      (hcont : ∀ j c (lam : ℤ), ∀ E ∈ outSet (unitD hM9 (B₀ j) RD hG layer hLayer (centre j c) base) P.L P.γ P.η,
        ContinuousOn (fun t => unitHkFW P p (B₀ j) RD hG layer hLayer g (h j) base lam t
          (sumintBoundary (S.sign (a₀ j).toNode) E))
          (cubeSet (unitD hM9 (B₀ j) RD hG layer hLayer (centre j c) base).qOut))
      (Gsb : Garden w) (tt : Fin w → ℝ) (roots : Fin w → Fin P.d → ℤ)
      (selSk : GenDecoration Gsb P.d roots 0 → Prop) (lay : GBranch Gsb.tree → ℕ)
      (hmom : J → Fin 4 → GNode Gsb.tree) (hclk : J → Fin 3 → ClkSrc Gsb)
      (leaf : J → Fin 3 → Prop) (td : J → Fin 3 → ℝ)
      (hind : ∀ j (lam : ℤ) (t t' : Fin 3 → ℝ) (k : Fin 4 → Mom P.d), (∀ i, ¬ leaf j i → t i = t' i) →
        unitHkFW P p (B₀ j) RD hG layer hLayer g (h j) base lam t k =
          unitHkFW P p (B₀ j) RD hG layer hLayer g (h j) base lam t' k),
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
            (unitHkFW P p (B₀ j) RD hG layer hLayer g (h j) base (lam j) (fun i => clockOf Gsb tt τ (hclk j i))
              (fun i => base + latticePoint P.L (κ.1 (hmom j i))))) ∧
        ∏ j, Mh j = C ^ Fintype.card J *
          (∏ j, unitMassFW P hM9 (B₀ j) RD hG layer hLayer cψ (bb j)) *
          ∏ j, (1 + |((lam j : ℤ) : ℝ)|) ^ (6 * P.η ^ 6) := by
  obtain ⟨C, hC, hex⟩ := exists_hinge_data_mod_ck_w (θ := 2 * η ^ 8) (by positivity) d
  refine ⟨C, hC, fun P hPd hPη hV hC₁ hL0 {p} hp {w} {S} hprime hM9 RD hG layer hLayer hcan hord {J} _ {U₀} {a₀} {b₀}
    {R₀} {n₀} B₀ hcl g cψ hc hgp hre h bb hbb hh centre base hq hcont Gsb tt roots selSk lay hmom hclk leaf td hind
    G1 G2 lam => ?_⟩
  subst hPd hPη
  have hM0 : ∀ j, 0 ≤ unitMassFW P hM9 (B₀ j) RD hG layer hLayer cψ (bb j) := fun j =>
    unitMassFW_nonneg P hM9 (B₀ j) RD hG layer hLayer cψ (bb j) (by linarith) hC₁ hL0 (hbb j)
  obtain ⟨H, Mh, hMh, hsum, hprod⟩ := hex Gsb J (fun j c => unitD hM9 (B₀ j) RD hG layer hLayer (centre j c) base)
    (fun j c => outSet (unitD hM9 (B₀ j) RD hG layer hLayer (centre j c) base) P.L P.γ P.η)
    (fun j => S.sign (a₀ j).toNode) (fun j lam t k => unitHkFW P p (B₀ j) RD hG layer hLayer g (h j) base lam t k)
    (fun j => unitMassFW P hM9 (B₀ j) RD hG layer hLayer cψ (bb j)) (6 * P.η ^ 6) hM0
    (fun j c' => hq j) hcont (fun j c lam => unit_vineest_boundWN hV hp (h j) (bb j) (hbb j) (hh j) hprime hM9 (B₀ j)
      RD hG layer hLayer hcan hord (hcl j) g cψ hc hgp hre (centre j c) base lam) P.L base tt roots selSk lay hmom
    (fun j τ i => if leaf j i then td j i else clockOf Gsb tt τ (hclk j i)) G1 G2 lam
  refine ⟨H.leafWrap leaf td, Mh, hMh, fun κ hκ τ hτ j c' hball => ?_, hprod⟩
  have h1 := hsum κ hκ τ hτ j c' hball
  rw [hind j (lam j) _ (fun i => clockOf Gsb tt τ (hclk j i)) _ (fun i hi => by simp [hi])] at h1
  exact H.leafWrap_hasSum leaf td j c' _ (fun i => clockOf Gsb tt τ (hclk j i)) h1


end

section
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA
  WaveTurbulence.VineEstS4 WaveTurbulence.VineC WaveTurbulence.LFTwist WaveTurbulence.VineAlign
  WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS5C
  VineParamContract WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.Represents
  WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W

/-- The hinge-data constant of `hinge_units_constWN`, as a function of `(d, η)`. -/
def ChinFWN (d : ℕ) (η : ℝ) : ℝ :=
  if h : 0 ≤ η then (hinge_units_constWN d η h).choose else 0

theorem ChinFWN_spec (d : ℕ) (η : ℝ) (h : 0 ≤ η) : 0 ≤ ChinFWN d η := by
  unfold ChinFWN
  rw [dif_pos h]
  exact (hinge_units_constWN d η h).choose_spec.1

open scoped Classical in
/-- **The hinge data of the weighted units of the representative** (main's `unit_hinge_data`). -/
theorem unit_hinge_dataWN (P : WTParams) (hV : V5FrontierClassBoundOnAt (· = none) P) (hM9 : VINEPARAM)
    (hgate : CoherentGateH P) (hinc : IncoherentGateH P) (htop : TopIncoherentDecayAtR P)
    (hd1 : 1 ≤ P.d) (hη0 : 0 < P.η) (hη6 : 6 * P.η ^ 6 ≤ P.η)
    (hη2 : P.η ≤ 1 / 2) (hC1 : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL1 : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    {p : ℕ} (hp : p < P.D) {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (hcan : IsCanonGC (p + 1) a.layered)
    (hord : (a.prime.data.garden a.prime.prime.1).order ≤ P.N (p + 1) ^ 4)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ) (hc : 1 ≤ cψ) (hgp : ∀ j, GPresented (32 * P.d) (g j) cψ)
    (hre : ∀ j x, (g j x).im = 0)
    (hp' : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (bb : ℝ) (hbb : 0 ≤ bb)
    (hB : ∀ q j j', q ≤ p → SNormR (40 * P.d) (40 * P.d) (hp' q j j') ≤ ENNReal.ofReal bb)
    (lam : Fin (unitBlocks a.prime.skeleton a.totalSigma).length → ℤ) :
    ∃ (H : HingeFam (Fin (unitBlocks a.prime.skeleton a.totalSigma).length) P.d)
      (Mh : Fin (unitBlocks a.prime.skeleton a.totalSigma).length → ℝ),
      (∀ j c', ∑' l, H.w j c' l ≤ Mh j) ∧
      HHkProp (a.normalizedPiece P.d) tt base roots
        (selSkC a P.L P.γ P.η (lt_of_lt_of_le zero_lt_one hL1).ne' base roots)
        ((profileShape a).hclk (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma))
        ((profileShape a).hmom (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma))
        (fun j => unitHkFW P p (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a)
          (sourceLayer_isLayering a) g
          (unitProfile (unitBlk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma) hp' j) base (lam j)) H ∧
      ∏ j, Mh j = ChinFWN P.d P.η ^ Fintype.card (Fin (unitBlocks a.prime.skeleton a.totalSigma).length) *
        (∏ j, unitMassFW P hM9 (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a)
          (sourceLayer_isLayering a) cψ bb) *
        ∏ j, (1 + |((lam j : ℤ) : ℝ)|) ^ (6 * P.η ^ 6) := by
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one hL1
  have hMa := Mole.garden_isMolecule a.prime.skeleton
  have hspec := (hinge_units_constWN P.d P.η hη0.le).choose_spec
  have hChin : ChinFWN P.d P.η = (hinge_units_constWN P.d P.η hη0.le).choose := by
    unfold ChinFWN; rw [dif_pos hη0.le]
  rw [hChin]
  have hcan' : IsCanonGC (p + 1) (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a)) := by rw [sourceLayer_reconstructs]; exact hcan
  have hordS : a.prime.skeleton.order ≤ P.N (p + 1) ^ 4 := by
    have := a.prime.data.decoded_order a.prime.prime.1 (a.prime.data.garden_decodes a.prime.prime.1)
    omega
  have hcl : ∀ j : Fin (unitBlocks a.prime.skeleton a.totalSigma).length,
      clLocalOrder1 (regionOf (unitBlk hMa a.totalSigma j)) ≤ P.N 1 ^ 4 := fun j =>
    clLocalOrder1_le_N1 P _ hordS
  have hh' : ∀ j : Fin (unitBlocks a.prime.skeleton a.totalSigma).length, ∀ r ≤ p,
      SNormR (40 * P.d) (40 * P.d) (unitProfile (unitBlk hMa a.totalSigma) hp' j r) ≤ ENNReal.ofReal bb :=
    fun j r hr => hB r _ _ hr
  have hLay : (a.normalizedPiece P.d).layer = (stSt a.prime.skeleton a.totalSigma).layer
      (RegRed.coreLayer (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a))
        a.prime.data a.prime.prime.1 (a.prime.data.garden_decodes a.prime.prime.1)) := by
    funext c
    show RegRed.coreLayer a.layered a.prime.data a.prime.prime.1 a.prime.decodes
      ((stSt a.prime.skeleton a.totalSigma).M.ob c) = _
    rw [coreLayer_of_spec a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) a.layered
      (sourceLayer_reconstructs a) a.prime.decodes]
    exact (coreLayer_of_spec a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) _ rfl _ _).symm
  have hG1 := g1_units P hMa a.totalSigma hM9 (B₀ := sourceAssembly a) a.prime.data a.prime.prime.1 (sourceLayer a)
    (sourceLayer_isLayering a) base tt roots (selSkC a P.L P.γ P.η hL0.ne' base roots)
    (fun j c => sumintBoundary (a.prime.skeleton.sign (unitBlk hMa a.totalSigma j).upper.toNode)
      (fun i => latPt P.d (c i)))
    (fun j c hc => qOut_one_eq_lay hMa a.totalSigma j a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) c hc)
    (fun j c hc => qOut_two_eq_lay hMa a.totalSigma j a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) c hc)
    (fun j => hqle_units hMa a.totalSigma j a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a))
  let D' : SplicedKernelData (stSt a.prime.skeleton a.totalSigma).G P.d :=
    ⟨fun _ => 0, ∅, fun _ => 0, fun _ _ => 0, fun _ => 0,
      NormalizedSplice.gapSpecification a.prime.skeleton a.totalSigma, fun _ => 0, fun _ => 0⟩
  have hG2 : ∀ κ : GenDecoration (stSt a.prime.skeleton a.totalSigma).G P.d roots 0,
      selSkC a P.L P.γ P.η hL0.ne' base roots κ → ∀ (j : Fin (unitBlocks a.prime.skeleton a.totalSigma).length)
        (c : Fin 4 → Fin P.d → ℤ),
      (∀ i, ‖(base + latticePoint P.L (κ.1 ((stShape hMa a.totalSigma).hmom (unitBlk_disj hMa a.totalSigma) j i))) -
        latPt P.d (c i)‖ ≤ 1) →
        sumintBoundary (a.prime.skeleton.sign (unitBlk hMa a.totalSigma j).upper.toNode)
            (fun i => base + latticePoint P.L (κ.1 ((stShape hMa a.totalSigma).hmom (unitBlk_disj hMa a.totalSigma) j i))) ∈
          outSet (unitD hM9 (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
            (sumintBoundary (a.prime.skeleton.sign (unitBlk hMa a.totalSigma j).upper.toNode)
              (fun i => latPt P.d (c i))) base) P.L P.γ P.η := by
    intro κ hκ j c hball
    refine g2_unitsN P hMa a.prime.prime.1 a.totalSigma hL0.ne' base roots D' rfl (B₀ := sourceAssembly a) hM9
      a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) κ ?_ j c hball
    have hD' : D'.gapSpecification = NormalizedSplice.gapSpecification a.prime.skeleton a.totalSigma := by
      simp only [D']
    have h1 := NormalizedSplice.gapValue_eq_indicator a.totalSigma D' hD' P.L P.γ P.η base κ.1
    have h2 : NormalizedSplice.gapValue a.prime.skeleton a.totalSigma P.L P.γ P.η base κ.1 = 1 :=
      (gap_value_eq_gapValue a P.L P.γ P.η hL0.ne' base roots κ).symm.trans hκ
    rw [← h1, h2]
    exact one_ne_zero
  have hcont : ∀ (j : Fin (unitBlocks a.prime.skeleton a.totalSigma).length) (c : Fin 4 → Fin P.d → ℤ) (lam : ℤ),
      ∀ E ∈ outSet (unitD hM9 (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a)
        (sourceLayer_isLayering a)
        (sumintBoundary (a.prime.skeleton.sign (unitBlk hMa a.totalSigma j).upper.toNode)
          (fun i => latPt P.d (c i))) base) P.L P.γ P.η,
        ContinuousOn (fun t => unitHkFW P p (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a)
          (sourceLayer_isLayering a) g (unitProfile (unitBlk hMa a.totalSigma) hp' j) base lam t
          (sumintBoundary (a.prime.skeleton.sign (unitBlk hMa a.totalSigma j).upper.toNode) E))
          (cubeSet (unitD hM9 (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a)
            (sourceLayer_isLayering a)
            (sumintBoundary (a.prime.skeleton.sign (unitBlk hMa a.totalSigma j).upper.toNode)
              (fun i => latPt P.d (c i))) base).qOut) :=
    fun j c lam => unit_hcontW hgate hinc htop hd1 hη0 hη6 hη2 hC1 hδ hL1 hw hp
      (unitProfile (unitBlk hMa a.totalSigma) hp' j) bb (hh' j) a.prime.prime hM9 (sourceAssembly a j) a.prime.data
      a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) hcan' hord g cψ hc hgp hre _ base lam
  have hind : ∀ (j : Fin (unitBlocks a.prime.skeleton a.totalSigma).length) (lam : ℤ) (t t' : Fin 3 → ℝ)
      (k : Fin 4 → Mom P.d), (∀ i, ¬ leafFlag hMa a.totalSigma j i → t i = t' i) →
      unitHkFW P p (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) g
        (unitProfile (unitBlk hMa a.totalSigma) hp' j) base lam t k =
      unitHkFW P p (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) g
        (unitProfile (unitBlk hMa a.totalSigma) hp' j) base lam t' k :=
    fun j lam t t' k ht => unitHkFW_hind P p (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) g _ base (leafFlag hMa a.totalSigma j) (leafFlag_zero hMa a.totalSigma j)
      (unit_hleaf1 hMa a.totalSigma a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
        a.prime.prime j)
      (unit_hleaf2 hMa a.totalSigma a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
        a.prime.prime j) lam t t' k ht
  obtain ⟨H, Mh, hsum, hHk, hprod⟩ := hspec.2 P rfl rfl hV (by linarith) hL0 hp a.prime.prime hM9 a.prime.data
    a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) hcan' hord (B₀ := sourceAssembly a) hcl g cψ hc hgp hre
    (fun j => unitProfile (unitBlk hMa a.totalSigma) hp' j) (fun _ => bb) (fun _ => hbb) hh'
    (fun j c => sumintBoundary (a.prime.skeleton.sign (unitBlk hMa a.totalSigma j).upper.toNode)
      (fun i => latPt P.d (c i))) base (fun j => hqle_units hMa a.totalSigma j a.prime.data a.prime.prime.1
        (sourceLayer a) (sourceLayer_isLayering a)) hcont (stSt a.prime.skeleton a.totalSigma).G tt roots
    (selSkC a P.L P.γ P.η hL0.ne' base roots)
    ((stSt a.prime.skeleton a.totalSigma).layer
      (RegRed.coreLayer (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a))
        a.prime.data a.prime.prime.1 (a.prime.data.garden_decodes a.prime.prime.1)))
    ((stShape hMa a.totalSigma).hmom (unitBlk_disj hMa a.totalSigma))
    ((stShape hMa a.totalSigma).hclk (unitBlk_disj hMa a.totalSigma))
    (leafFlag hMa a.totalSigma)
    (fun j i => ((qOutOf a.prime.data a.prime.prime.1 (sourceLayer a) (unitBlk hMa a.totalSigma j).upper
      (unitBlk hMa a.totalSigma j).lower (regionOf (unitBlk hMa a.totalSigma j)) i : ℕ) : ℝ)) hind hG1 hG2 lam
  refine ⟨H, Mh, hsum, ?_, hprod⟩
  intro κ hκ τ hτ j c hball
  rw [hLay] at hτ
  exact hHk κ hκ τ hτ j c hball


end

section
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA
  WaveTurbulence.VineEstS4 WaveTurbulence.VineC WaveTurbulence.LFTwist WaveTurbulence.VineAlign
  WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.PL2330
  WaveTurbulence.VineEstS5C VineParamContract WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Represents WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W
open scoped ENNReal Classical

/-- The hinge constant of the weighted units, with the top filter mass absorbed. -/
def ChFWN (d : ℕ) (η : ℝ) : ℝ := max 1 (ChinFWN d η * topFilterMass)

/-- The explicit minimal constant of the weighted vine case. -/
def CvineFWN (d : ℕ) (η c₁ : ℝ) : ℝ :=
  max (max 1 (2 * c₁ ^ 2 * (1 + cLeib d (30 * d))))
    (Cchi d * (nodeBallCard d : ℝ) * (9 * KslotMW d η) ^ 2 * ChFWN d η)

/-- The VINEEST mass of a unit with its weight power (without the top filter mass). -/
def unitMassCN (P : WTParams) {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {R : CLRegionData G U a b} {n : ℕ} (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (cψ B₀ : ℝ) : ℝ :=
  cψ ^ (9 * U.card + 4 * clLocalOrder2 RD hG R) * unitMass P hM9 B RD hG layer hLayer B₀

theorem prod_pow_mul_prodN {ι : Type*} [Fintype ι] (c : ℝ) (e : ι → ℕ) (f : ι → ℝ) :
    ∏ i, (c ^ e i * f i) = c ^ (∑ i, e i) * ∏ i, f i := by
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

section VineCase
variable (Pg : WTParams) (C : ℝ)

theorem vineCaseRepresentsFW_of_gateN (E : GateEnv Pg) (htop0 : TopIncoherentDecayAtR Pg) (hη : 0 < Pg.η)
    (hδ : 0 < Pg.δ) (hL2 : 2 ≤ Pg.L) (hC2 : 1 ≤ Pg.C₂) (hM9 : VINEPARAM) (hC : CvineFWN Pg.d Pg.η Pg.C₁ ≤ C)
    (hV : V5FrontierClassBoundOnAt (· = none) (PB Pg C)) (htop : TopIncoherentDecayAtR (PB Pg C)) :
    VineCaseRepresentsFW (PB Pg C) := by
  intro p hp R hR hRmax N hN1 hNmax A hA hcl tt htt base roots g cψ hcψ hgp hre U s hs0 hb hsize π hv
  obtain ⟨K, hK1, hKe, hslot⟩ := vine_slot_dataW Pg E htop0
  have hcLeib := cLeib_nonneg Pg.d (30 * Pg.d)
  have hC1' : 2 * Pg.C₁ ^ 2 * (1 + cLeib Pg.d (30 * Pg.d)) ≤ C :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hC
  have hCχ : Cchi Pg.d * (nodeBallCard Pg.d : ℝ) * (9 * K) ^ 2 * ChFWN Pg.d Pg.η ≤ C := by
    rw [hKe]; exact le_trans (le_max_right _ _) hC
  have hC1ge : 1 ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hC
  obtain ⟨hη6, hη1, hη12⟩ := eta_small_facts Pg.η hη E.hη
  have hCg : Pg.C₁ ≤ C := by nlinarith [E.hC1]
  have hgate : CoherentGateH (PB Pg C) :=
    coherentGateH_of (leafwiseCoherentApproximation30_largeConstantMonotone Pg C Pg.C₂ E.hC1 hC2 hδ hL2 hCg le_rfl
      E.hcoh)
  have hinc : IncoherentGateH (PB Pg C) :=
    incoherentGateH_of (leafwiseIncoherentDecay_largeConstantMonotone Pg C Pg.C₂ E.hC1 hC2 hδ hL2 hCg le_rfl E.hinc)
  have hd1 : 1 ≤ Pg.d := E.hd1
  have hL1 : 1 ≤ Pg.L := E.hL1
  have hL0 : 0 < Pg.L := lt_of_lt_of_le zero_lt_one hL1
  have hc0 : 0 ≤ cψ := by linarith
  obtain ⟨a, ha⟩ : ∃ a, repPt π = a := ⟨_, rfl⟩
  have haA : a.layered ∈ A := ha ▸ repPt_layered_mem π
  have hcA := hA a.layered haA
  have hcan : IsCanonGC (p + 1) a.layered := hcA.1
  have hdec := a.prime.data.decoded_order a.prime.prime.1 a.prime.decodes
  have hNmax' : N ≤ Pg.N (p + 1) ^ 4 := by rw [N_bumpC1] at hNmax; exact hNmax
  have hordN : a.layered.garden.order = N := hcA.2.2.1
  have hsz : a.prime.data.size ≤ Pg.N (p + 1) ^ 4 := by omega
  have hGplain : a.fullProfile.piece.gap.garden.IsPlain :=
    (stSt a.prime.skeleton a.totalSigma).plain a.prime.prime.1
  have hctrlA : ∀ LG ∈ A, U.toLF.Controlled LG := controlled_of_bounded hA U hb
  have hctrl_a : ∀ i, LeafwiseControlled a.layered (typeProfiles a.layered (U.h i)) (fun _ => U.b i) :=
    fun i => hctrlA _ haA i
  obtain ⟨fam, μ, hexpR, hμ, hμb⟩ := hslot C hC1' a hp hcan hsz tt htt U hctrl_a g cψ hcψ hgp hGplain
  obtain ⟨T, hT⟩ := exists_outputs_finset (p := p) a
  have hlay := fun y hy x => member_stateLayer_le hA hcl a haA y hy x
  have hcanM := fun y hy => member_isCanon hA hcl a haA y hy
  have hctrlM : ∀ y : UState (2 * R) (unitsSplit (sourceAssembly a)),
      y ∈ sourceClass a p (objKind (2 * R)) → U.toLF.Controlled y.1.layered :=
    fun y hy => hctrlA _ (outputs_mem_A hcl a haA hcan y hy)
  have hgn : ∀ j x, ‖g j x‖ ≤ cψ := fun j x => (hgp j).norm_le hc0 x
  have hsum := class_sum_modesW π a ha (PB Pg C) U hd1 hL1 tt htt base roots hlay hcanM hb hctrlM g cψ hcψ hgn
    hGplain fam hexpR T hT
  have hcanR : IsCanonGC (p + 1) (repPt π).layered := by rw [ha]; exact hcan
  have hTR : (T : Set (LayeredGarden (2 * R))) = (repPt π).outputs (p := p) (kind := objKind (2 * R)) := by
    rw [ha]; exact hT
  rw [sum_members_eqW hcl π hcanR _ U.toLF tt base roots (fwWeight p g base) T hTR, hsum]
  have hMa := Mole.garden_isMolecule a.prime.skeleton
  letI : Fintype U.ι := U.fin
  have hsgn : ∀ i : U.ι, ‖((U.sign i : ℝ) : ℂ)‖ ≤ 1 := fun i => by
    rw [Complex.norm_real]; exact U.sign_abs_le i
  have hn : N - a.prime.skeleton.order = a.prime.data.size := by omega
  have hnS : a.prime.skeleton.order ≤ N := by omega
  have hordD : (a.prime.data.garden a.prime.prime.1).order = N := by rw [a.prime.gardenEq, hordN]
  have hexpo := weight_exponent_le (profileShape a) (unitBlk_disj hMa a.totalSigma) a.prime.data a.prime.prime.1
    hGplain N hn hnS
  have hE : (∑ s', Stage1WNoVine.slotNr a.prime.data a.prime.prime.1 ((profileShape a).iota a.prime.prime.1 hGplain s')) +
      ∑ j, (9 * (unitBlk hMa a.totalSigma j).atoms.card +
        4 * clLocalOrder2 a.prime.data a.prime.prime.1 (regionOf (unitBlk hMa a.totalSigma j))) ≤ 16 * N := by
    rw [hordD] at hexpo; omega
  have hmc : ∀ (i : U.ι) j, unitMassCN (PB Pg C) hM9 (sourceAssembly a j) a.prime.data a.prime.prime.1
      (sourceLayer a) (sourceLayer_isLayering a) cψ (U.b i) =
      cψ ^ (9 * (unitBlk hMa a.totalSigma j).atoms.card +
        4 * clLocalOrder2 a.prime.data a.prime.prime.1 (regionOf (unitBlk hMa a.totalSigma j))) *
      unitMass (PB Pg C) hM9 (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a)
        (sourceLayer_isLayering a) (U.b i) := fun i j => rfl
  have hM0 : ∀ (i : U.ι) j, 0 ≤ unitMass (PB Pg C) hM9 (sourceAssembly a j) a.prime.data a.prime.prime.1
      (sourceLayer a) (sourceLayer_isLayering a) (U.b i) := fun i j => by
    unfold unitMass
    have hx0 : 0 ≤ (PB Pg C).C₁ * Real.sqrt (PB Pg C).δ :=
      mul_nonneg (by have : (1 : ℝ) ≤ C := hC1ge; show 0 ≤ C; linarith) (Real.sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg (pow_nonneg hx0 _) (Real.rpow_nonneg (by
      have : (1 : ℝ) ≤ Pg.L := hL1; show 0 ≤ Pg.L; linarith) _))
      (WaveTurbulence.VineEstS5C.regionLeafSize_const_nonneg _ _ _ _ _ (NNReal.coe_nonneg _))
  have hMC0 : ∀ (i : U.ι) j, 0 ≤ unitMassCN (PB Pg C) hM9 (sourceAssembly a j) a.prime.data a.prime.prime.1
      (sourceLayer a) (sourceLayer_isLayering a) cψ (U.b i) := fun i j => by
    rw [hmc]; exact mul_nonneg (pow_nonneg hc0 _) (hM0 i j)
  have key : Stage1Piece.RepresentsIntA (P := (PB Pg C)) (a.normalizedPiece (PB Pg C).d) N tt base roots
      (cψ ^ (16 * N) * s)
      (∑ i : U.ι, ((U.sign i : ℝ) : ℂ) * ∑' ξ : (∀ s, (fam i).Λ s), ((modeWt (fam i) ξ : ℝ) : ℂ) *
          outerValM a.fullProfile.piece.gap.garden (PB Pg C).L (PB Pg C).γ (PB Pg C).δ base roots tt
            a.fullProfile.piece.layer a.fullProfile.piece.hinges
            (fun z => if selSkC a (PB Pg C).L (PB Pg C).γ (PB Pg C).η (lt_of_lt_of_le zero_lt_one hL1).ne' base roots z
              then 1 else 0) hGplain
            (fun s' => (fam i).a s' (ξ s')) (fun s' => (fam i).m s' (ξ s'))
            ((profileShape a).route a.prime.prime.1 hGplain)
            ((profileShape a).hclk (unitBlk_disj hMa a.totalSigma))
            ((profileShape a).hmom (unitBlk_disj hMa a.totalSigma))
            (fun j lam t k => unitHkFW (PB Pg C) p (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a)
              (sourceLayer_isLayering a) g
              (unitProfile (unitBlk hMa a.totalSigma) (U.h i) j) base lam t k)) := by
    refine representsIntA_of_vineModes (P := (PB Pg C)) hd1 hL1 E.hη0 (a.normalizedPiece (PB Pg C).d) hGplain tt base
      roots (selSkC a (PB Pg C).L (PB Pg C).γ (PB Pg C).η (lt_of_lt_of_le zero_lt_one hL1).ne' base roots) ?_
      ((profileShape a).route a.prime.prime.1 hGplain)
      (fun s i => (profileShape a).route_natural a.prime.prime.1 hGplain s i)
      ((profileShape a).hclk (unitBlk_disj hMa a.totalSigma)) ((profileShape a).hmom (unitBlk_disj hMa a.totalSigma))
      (stSrc hMa a.totalSigma hGplain) (fun j i x hx z => stSrc_dart hMa a.totalSigma hGplain j i x hx roots z)
      (fun j i r hr z => stSrc_root hMa a.totalSigma hGplain j i r hr roots z)
      (fun i : U.ι => ((U.sign i : ℝ) : ℂ)) hsgn fam μ
      (fun i j lam t k => unitHkFW (PB Pg C) p (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a)
        (sourceLayer_isLayering a) g (unitProfile (unitBlk hMa a.totalSigma) (U.h i) j) base lam t k)
      (c := 6 * (PB Pg C).η ^ 6) (θ := (PB Pg C).η) (by positivity) hη1 hη12 hμ
      ((PB Pg C).C₁ * Real.sqrt (PB Pg C).δ) K (ChFWN Pg.d Pg.η) rfl hK1 (le_max_left _ _) hCχ
      (fun s' => slotSize a.prime.data ((profileShape a).iota a.prime.prime.1 hGplain s'))
      (fun s' => slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
        ((profileShape a).iota a.prime.prime.1 hGplain s'))
      (fun i s' => cψ ^ Stage1WNoVine.slotNr a.prime.data a.prime.prime.1
          ((profileShape a).iota a.prime.prime.1 hGplain s') *
        slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) (fun _ => U.b i)
          ((profileShape a).iota a.prime.prime.1 hGplain s'))
      ?_ hμb
      (fun i j => unitMassCN (PB Pg C) hM9 (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a)
        (sourceLayer_isLayering a) cψ (U.b i))
      (fun j => clLocalOrder2 a.prime.data a.prime.prime.1 (regionOf (unitBlk hMa a.totalSigma j)))
      (fun j => cohmolIndex (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a) +
        (step3D hM9 (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
          (canonBadKind hM9 (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a))
          (qOutOf a.prime.data a.prime.prime.1 (sourceLayer a) (unitBlk hMa a.totalSigma j).upper
            (unitBlk hMa a.totalSigma j).lower (regionOf (unitBlk hMa a.totalSigma j)))
          (fun _ => (0 : Mom (PB Pg C).d)) (0 : Mom (PB Pg C).d)).M₁)
      (fun j => (Finset.univ.filter fun i : Fin (unitN a.totalSigma j) =>
        (assemblyShape hM9 (sourceAssembly a j)).nor i = false).card)
      (fun i j => cψ ^ (9 * (unitBlk hMa a.totalSigma j).atoms.card +
          4 * clLocalOrder2 a.prime.data a.prime.prime.1 (regionOf (unitBlk hMa a.totalSigma j))) *
        regionLeafSize a.prime.data a.prime.prime.1 (regionOf (unitBlk hMa a.totalSigma j)) (sourceLayer a)
          (sourceLayer_isLayering a) (fun _ => ((U.b i : NNReal) : ℝ)))
      ?_ ?_ ?_ N (cψ ^ (16 * N) * s) ?_ ?_ ?_ ?_ ?_ ?_ _ ?_
    · intro D' hD z
      exact (PrescribedPrimeGarden.normalizedPiece_gapIndicator a D' hD (lt_of_lt_of_le zero_lt_one hL1).ne' _ _ base
        roots z).trans (selSkC_ite a _ _ _ (lt_of_lt_of_le zero_lt_one hL1).ne' base roots z)
    · intro i s'
      refine mul_nonneg (pow_nonneg hc0 _) ?_
      generalize (profileShape a).iota a.prime.prime.1 hGplain s' = s0
      unfold slotLeaf
      rcases s0 with p' | b
      · exact Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
      · exact Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    · intro i j
      exact mul_nonneg (pow_nonneg hc0 _)
        (WaveTurbulence.VineEstS5C.regionLeafSize_const_nonneg _ _ _ _ _ (NNReal.coe_nonneg _))
    · intro i j
      refine ⟨hMC0 i j, le_of_eq ?_⟩
      rw [hmc]
      unfold unitMass
      rw [nor_card_eq hM9 (sourceAssembly a j)]
      simp only [neg_mul]
      ring
    · intro i ξ
      have hw : 0 ≤ Pg.gamma1 - Real.sqrt Pg.η := le_trans (pow_nonneg E.hη0 8) E.hκ
      have hordg : (a.prime.data.garden a.prime.prime.1).order ≤ (PB Pg C).N (p + 1) ^ 4 := by
        rw [a.prime.gardenEq, hordN]; exact hNmax
      obtain ⟨H, Mh, hsum', hHk, hprod⟩ := unit_hinge_dataWN (PB Pg C) hV hM9 hgate hinc htop hd1 hη hη6 E.hη hC1ge
        hδ hL1 hw hp a hcan hordg tt base roots g cψ hcψ hgp hre (U.h i) (U.b i) (NNReal.coe_nonneg _)
        (fun q j j' hq => hb i q j j' hq)
        (modLam (fun s => (fam i).m s (ξ s)) ((profileShape a).route a.prime.prime.1 hGplain))
      refine ⟨H, Mh, hsum', hHk, ?_⟩
      have hpt : ∀ j, ChinFWN (PB Pg C).d (PB Pg C).η * unitMassFW (PB Pg C) hM9 (sourceAssembly a j) a.prime.data
          a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) cψ (U.b i) ≤
          ChFWN Pg.d Pg.η * unitMassCN (PB Pg C) hM9 (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a)
            (sourceLayer_isLayering a) cψ (U.b i) := fun j => by
        have e : ChinFWN (PB Pg C).d (PB Pg C).η * unitMassFW (PB Pg C) hM9 (sourceAssembly a j) a.prime.data
            a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) cψ (U.b i) =
            (ChinFWN Pg.d Pg.η * topFilterMass) * unitMassCN (PB Pg C) hM9 (sourceAssembly a j) a.prime.data
              a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) cψ (U.b i) := by
          unfold unitMassFW unitMassCN
          ring
        rw [e]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (hMC0 i j)
      have hlam : 0 ≤ ∏ j, (1 + |((modLam (fun s => (fam i).m s (ξ s))
          ((profileShape a).route a.prime.prime.1 hGplain) j : ℤ) : ℝ)|) ^ (6 * (PB Pg C).η ^ 6) :=
        Finset.prod_nonneg fun j _ => Real.rpow_nonneg (by positivity) _
      have hch := ChinFWN_spec Pg.d Pg.η E.hη0
      rw [hprod, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
      refine mul_le_mul_of_nonneg_right (Finset.prod_le_prod₀ (fun j _ => mul_nonneg hch
        (unitMassFW_nonneg (PB Pg C) hM9 (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a)
          (sourceLayer_isLayering a) cψ (U.b i) hc0 (by show (0 : ℝ) ≤ C; linarith) hL0 (NNReal.coe_nonneg _)))
        (fun j _ => hpt j)) hlam
    · have hprodeq : ∀ i : U.ι, (∏ t, slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
          (fun _ => U.b i) ((profileShape a).iota a.prime.prime.1 hGplain t)) *
          ∏ j, regionLeafSize a.prime.data a.prime.prime.1 (regionOf (unitBlk hMa a.totalSigma j)) (sourceLayer a)
            (sourceLayer_isLayering a) (fun _ => ((U.b i : NNReal) : ℝ)) =
          leafSizeProduct a.layered (fun _ => U.b i) := fun i => by
        rw [leaf_prod_split (profileShape a) (unitBlk_disj hMa a.totalSigma) a.prime.data a.prime.prime.1 hGplain
          (sourceLayer a) (sourceLayer_isLayering a) (U.b i), sourceLayer_reconstructs a]
      have hfac : ∀ i : U.ι, (∏ t, (cψ ^ Stage1WNoVine.slotNr a.prime.data a.prime.prime.1
            ((profileShape a).iota a.prime.prime.1 hGplain t) *
          slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) (fun _ => U.b i)
            ((profileShape a).iota a.prime.prime.1 hGplain t))) *
          ∏ j, (cψ ^ (9 * (unitBlk hMa a.totalSigma j).atoms.card +
            4 * clLocalOrder2 a.prime.data a.prime.prime.1 (regionOf (unitBlk hMa a.totalSigma j))) *
            regionLeafSize a.prime.data a.prime.prime.1 (regionOf (unitBlk hMa a.totalSigma j)) (sourceLayer a)
              (sourceLayer_isLayering a) (fun _ => ((U.b i : NNReal) : ℝ))) ≤
          cψ ^ (16 * N) * leafSizeProduct a.layered (fun _ => U.b i) := fun i => by
        rw [prod_pow_mul_prodN, prod_pow_mul_prodN, mul_mul_mul_comm, ← pow_add, hprodeq i]
        have hnn : 0 ≤ leafSizeProduct a.layered (fun _ => U.b i) :=
          Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hcψ hE) hnn
      calc _ ≤ ∑ i : U.ι, cψ ^ (16 * N) * leafSizeProduct a.layered (fun _ => U.b i) :=
            Finset.sum_le_sum fun i _ => by
              have hnn : 0 ≤ (∏ t, (cψ ^ Stage1WNoVine.slotNr a.prime.data a.prime.prime.1
                    ((profileShape a).iota a.prime.prime.1 hGplain t) *
                  slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) (fun _ => U.b i)
                    ((profileShape a).iota a.prime.prime.1 hGplain t))) *
                  ∏ j, (cψ ^ (9 * (unitBlk hMa a.totalSigma j).atoms.card +
                    4 * clLocalOrder2 a.prime.data a.prime.prime.1 (regionOf (unitBlk hMa a.totalSigma j))) *
                    regionLeafSize a.prime.data a.prime.prime.1 (regionOf (unitBlk hMa a.totalSigma j))
                      (sourceLayer a) (sourceLayer_isLayering a) (fun _ => ((U.b i : NNReal) : ℝ))) := by
                refine mul_nonneg (Finset.prod_nonneg fun t _ => mul_nonneg (pow_nonneg hc0 _) ?_)
                  (Finset.prod_nonneg fun j _ => mul_nonneg (pow_nonneg hc0 _)
                    (WaveTurbulence.VineEstS5C.regionLeafSize_const_nonneg _ _ _ _ _ (NNReal.coe_nonneg _)))
                generalize (profileShape a).iota a.prime.prime.1 hGplain t = s0
                unfold slotLeaf
                rcases s0 with p' | b
                · exact Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
                · exact Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
              exact (mul_le_of_le_one_left hnn (hsgn i)).trans (hfac i)
        _ = cψ ^ (16 * N) * U.toLF.size a.layered := by rw [← Finset.mul_sum]; rfl
        _ ≤ cψ ^ (16 * N) * s := mul_le_mul_of_nonneg_left (hsize a.layered haA) (pow_nonneg hc0 _)
    · exact exponent_order (profileShape a) (unitBlk_disj hMa a.totalSigma) a.prime.data a.prime.prime.1 hGplain N hn
        hnS
    · have h1 := gsk_bound (profileShape a) (unitBlk_disj hMa a.totalSigma) a.prime.data a.prime.prime.1 hGplain
        (sourceLayer a) (sourceLayer_isLayering a) a.totalSigma (B₀ := sourceAssembly a)
        (hcov_units hMa a.totalSigma)
        (fun v => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 v).toNode) (fun v => rfl)
      have h2 := gsk_of_spec a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) a.layered
        (sourceLayer_reconstructs a) a.prime.decodes a.totalSigma
      refine le_trans (le_of_eq h2) (le_trans h1 (le_of_eq ?_))
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [step3D_M1]
      rfl
    · refine le_trans (le_of_eq (normalizedPiece_bsk a _))
        (bsk_bound hM9 a.totalSigma (sourceAssembly a) (hcov_units hMa a.totalSigma))
    · exact le_of_eq ((card_hinges (profileShape a) (unitBlk_disj hMa a.totalSigma)).symm.trans
        (congrArg Finset.card (profileShape_hinges a)))
    · exact card_units_le_order (profileShape a) (unitBlk_disj hMa a.totalSigma)
    · rfl
  subst ha
  exact key

end VineCase


end

section
open WaveTurbulence WaveTurbulence.LGSpine Set VineParamContract WaveTurbulence.Represents
  WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3
  WaveTurbulence.VineEstS3.Eng WaveTurbulence.VineEstS4 WaveTurbulence.RegRed
open scoped ENNReal

/-- **The weighted vine case on the prefix**, from the staged `V5FrontierClassBound` (conditional helper). -/
theorem vineCaseRepresentsFW_of_frontierN (hV : WTPrefix (V5FrontierClassBoundOnAt (· = none))) : WTPrefix VineCaseRepresentsFW := by
  have hgates : WTPrefix (fun P => LeafwiseIncoherentDecayAt P ∧ LeafwiseCoherentApproximationAt P) :=
    prefix_and Spine.leafwise_incoherent_decay Spine.leafwise_coherent_approximation
      leafwiseIncoherentDecay_largeConstantMonotone leafwiseCoherentApproximation30_largeConstantMonotone
  have hm1 : LargeConstantMonotone (fun P => LeafwiseIncoherentDecayAt P ∧ LeafwiseCoherentApproximationAt P) :=
    leafwiseIncoherentDecay_largeConstantMonotone.and leafwiseCoherentApproximation30_largeConstantMonotone
  have hthree : WTPrefix (fun P => (LeafwiseIncoherentDecayAt P ∧ LeafwiseCoherentApproximationAt P) ∧
      TopIncoherentDecayAtR P) :=
    prefix_and hgates IncTop.topIncoherentDecayGateR hm1 Stage1WNoVine.topIncoherentDecayAtR_largeConstantMonotone
  have hall : WTPrefix (fun P => ((LeafwiseIncoherentDecayAt P ∧ LeafwiseCoherentApproximationAt P) ∧
      TopIncoherentDecayAtR P) ∧ V5FrontierClassBoundOnAt (· = none) P) :=
    prefix_and hthree hV (hm1.and Stage1WNoVine.topIncoherentDecayAtR_largeConstantMonotone)
      (v5FrontierClassBoundOnAt_mono _)
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, hη⟩ := hall d hd γ hγ
  set g1 : ℝ := min (2 * γ) (min 1 (2 * ((d : ℝ) - 1) * (1 - γ))) with hg1
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hg : 0 < g1 := by
    rw [hg1]
    refine lt_min (by linarith [hγ.1]) (lt_min one_pos ?_)
    have : 0 < 1 - γ := by linarith [hγ.2]
    nlinarith
  refine ⟨min η₀ (min (1 / 2) ((g1 / 2) ^ 2)), lt_min hη₀ (lt_min (by norm_num) (by positivity)), ?_⟩
  intro η hηm φin hφin τ hτ φ hsol
  have hη0 : η ≤ η₀ := hηm.2.trans (min_le_left _ _)
  have hη2 : η ≤ 1 / 2 := hηm.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hη3 : η ≤ (g1 / 2) ^ 2 := hηm.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨C₁g, hC₁g, ν₀, hν₀, hrest⟩ := hη η ⟨hηm.1, hη0⟩ φin hφin τ hτ φ hsol
  refine ⟨max C₁g (CvineFWN d η C₁g), hC₁g.trans (le_max_left _ _), ν₀, hν₀, ?_⟩
  intro ν hν
  obtain ⟨δ₀, hδ₀, hrest2⟩ := hrest ν hν
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ D hD htime
  obtain ⟨C₂, hC₂, L₀, hL₀, hrest3⟩ := hrest2 δ hδ D hD htime
  refine ⟨C₂, hC₂, L₀, hL₀, ?_⟩
  intro L hL
  obtain ⟨⟨⟨hincP, hcohP⟩, htopP⟩, hVP⟩ := hrest3 L hL
  let Pg : WTParams := ⟨d, γ, η, φin, τ, φ, C₁g, ν, δ, D, C₂, L⟩
  have hL2 : 2 ≤ L := hL₀.trans hL
  have E : GateEnv Pg :=
    { hd1 := by show 1 ≤ d; omega
      hL1 := by show 1 ≤ L; linarith
      hη0 := hηm.1.le
      hη := hη2
      hC1 := hC₁g
      hδ0 := hδ.1.le
      hκ := eta_pow_leN g1 η hg hηm.1 hη3 hη2
      hinc := hincP
      hcoh := hcohP }
  have hV' : V5FrontierClassBoundOnAt (· = none) (PB Pg (max C₁g (CvineFWN d η C₁g))) :=
    (v5FrontierClassBoundOnAt_mono _) Pg (max C₁g (CvineFWN d η C₁g)) C₂ hC₁g hC₂ hδ.1 hL2 (le_max_left _ _) le_rfl hVP
  have htop' : TopIncoherentDecayAtR (PB Pg (max C₁g (CvineFWN d η C₁g))) :=
    Stage1WNoVine.topIncoherentDecayAtR_largeConstantMonotone Pg (max C₁g (CvineFWN d η C₁g)) C₂ hC₁g hC₂ hδ.1 hL2
      (le_max_left _ _) le_rfl htopP
  exact vineCaseRepresentsFW_of_gateN Pg (max C₁g (CvineFWN d η C₁g)) E htopP hηm.1 hδ.1 hL2 hC₂
    WaveTurbulence.Vine.Param.vineparam (le_max_right _ _) hV' htop'

/-- The weighted Stage-1 reduction gate, from the staged `V5FrontierClassBound` (conditional helper). -/
theorem stage1ReductionGateFW_of_frontierN (hV : WTPrefix (V5FrontierClassBoundOnAt (· = none))) : Stage1ReductionGateFW :=
  stage1ReductionGateFW_of_pieces Stage1WNoVine.noVineRepresentsFW (vineCaseRepresentsFW_of_frontierN hV)


end

/-- **The weighted Stage-1 reduction gate, unconditional** (from the `S = none` half of the weighted vine bound). -/
theorem stage1ReductionGateFW : Stage1W.Stage1ReductionGateFW :=
  stage1ReductionGateFW_of_frontierN v5FrontierClassBoundNone

end WaveTurbulence.Flower.V5WB
