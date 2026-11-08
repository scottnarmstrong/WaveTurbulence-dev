/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WVine.WMember2
public import WaveTurbulence.Foundations.Flower.V5W.ContClass
public import WaveTurbulence.Foundations.Flower.V5W.Foreign
public import WaveTurbulence.Foundations.Stage1.Represents.RepVD15

/-! # STAGE1W-VINE (T6, part 1): the weighted unit class kernels and their hinge data

* `unitHkFW`: the weighted class kernel of a unit, `twistedRecenteredFW p (g j₁) none … (modW λ)` (S-V5W §1, `S = none`),
  the weighted analogue of main's `unitHk`.
* `unitHkFW_hind`: it does not depend on the clocks of lower children that are leaves in every member (main's
  `unitHk_hind`).
* `unit_vineest_boundW`: the staged **`V5FrontierClassBoundAt`** gives the X-norm bound of a unit with the weighted mass
  `unitMassFW = cψ^(9|U| + 4n₂) · topFilterMass · unitMass` (main's `unit_vineest_bound`).
* `unit_hcontW`: T5 `weightedClassContinuity` (with INC-TOP's `TopIncoherentDecayAtR`) gives `hcont` (main's
  `unit_hcont`).
* `hinge_units_constW`: main's `hinge_units_const` for the weighted kernels; the constant depends only on `(d, η)`.

Adapted from main's `Represents/{RepVN11, RepVN12, RepKC1, RepUG8, RepVC1}.lean` (see `COPIED-SHA256SUMS`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.Stage1WVine
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RepAnalytic
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed WaveTurbulence.Represents
  WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C VineParamContract WaveTurbulence.Flower.Stage1W
  WaveTurbulence.Flower.V5W
open scoped ENNReal

/-- **The weighted class kernel of a unit** (`S = none`, the unit's weight `g a.1.1`). -/
def unitHkFW (P : WTParams) (p : ℕ) {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} (B : CLChainAssembly G R n)
    (RD : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer) (g : Fin w → Mom P.d → ℂ) (h : ℕ → Mom P.d → ℝ) (wBar : Mom P.d) :
    ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ := fun lam t k =>
  twistedRecenteredFW p (g a.1.1) none G a
    (canonFinsetK p (objKind w) (startState B RD hG layer hLayer) (chainStart B))
    P.L P.γ P.δ h wBar (VineC.modW (lam : ℝ)) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)

/-- The weighted VINEEST mass of a unit: `cψ^(9|U| + 4 n₂) · topFilterMass` times main's `unitMass`. -/
def unitMassFW (P : WTParams) {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {R : CLRegionData G U a b} {n : ℕ} (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (cψ B₀ : ℝ) : ℝ :=
  cψ ^ (9 * U.card + 4 * clLocalOrder2 RD hG R) * topFilterMass * unitMass P hM9 B RD hG layer hLayer B₀

theorem topFilterMass_nonneg : 0 ≤ topFilterMass :=
  MeasureTheory.integral_nonneg fun _ => norm_nonneg _

theorem unitMassFW_nonneg (P : WTParams) {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {R : CLRegionData G U a b} {n : ℕ} (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (cψ B₀ : ℝ)
    (hc : 0 ≤ cψ) (hC₁ : 0 ≤ P.C₁) (hL0 : 0 < P.L) (hB₀ : 0 ≤ B₀) :
    0 ≤ unitMassFW P hM9 B RD hG layer hLayer cψ B₀ :=
  mul_nonneg (mul_nonneg (pow_nonneg hc _) topFilterMass_nonneg)
    (mul_nonneg (mul_nonneg (pow_nonneg (mul_nonneg hC₁ (Real.sqrt_nonneg _)) _) (Real.rpow_nonneg hL0.le _))
      (WaveTurbulence.VineEstS5C.regionLeafSize_const_nonneg RD hG R layer hLayer hB₀))

/-! ## Leaf independence -/

section Congr
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem clLocalKernelFW_congr_t (pw : ℕ) (g : Mom d → ℂ) (D : ReconstructionData G) (hG : G.IsPlain)
    (R : CLRegionData G U a b) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (m : (GNode G.tree → Fin d → ℤ) → ℂ) (W : ℝ → ℂ)
    (tU tP tN tP' tN' : ℝ) (e f g' h : Mom d)
    (hp : (b.child R.positive).1.2 ∉ (G.tree (b.child R.positive).1.1).branching ∨ tP = tP')
    (hn : (b.child R.negative).1.2 ∉ (G.tree (b.child R.negative).1.1).branching ∨ tN = tN') :
    clLocalKernelFW pw g D hG R L γ δ F layer hLayer base m W tU tP tN e f g' h =
      clLocalKernelFW pw g D hG R L γ δ F layer hLayer base m W tU tP' tN' e f g' h := by
  unfold clLocalKernelFW
  congr 1
  refine tsum_congr fun κ => MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  have h0 : ![tU, tP, tN] 0 = ![tU, tP', tN'] 0 := rfl
  have e1 := clLocalClock_congr R ![tU, tP, tN] ![tU, tP', tN'] h0 hp hn τ
  have e2 := clLocalSummandFW_congr pw g D hG R L γ δ F layer hLayer base ![e, f, g', h] ![tU, tP, tN]
    ![tU, tP', tN'] rfl hp hn κ τ
  simp only [e1, e2]

end Congr

section Hind
variable {w : ℕ} {ι : Type*} [Fintype ι]

/-- The weighted class kernel is independent of the clocks of lower children that are leaves in every member. -/
theorem twistedRecenteredFW_congr_leaf {d p : ℕ} {kind : Bool} {A : FamilyReconstruction w ι}
    {c : ChainAt A.skeleton A.family} (pw : ℕ) (g : Mom d → ℂ) (S : Option ℝ) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (base : Mom d) (W : ℝ → ℂ) (t0 t1 t2 t1' t2' : ℝ) (e f g' k : Mom d)
    (hp : ∀ x ∈ canonFinsetK p kind A c,
      (x.2.b.child (clRegionData x.1.skeleton x.2.block x.2.cl).positive).1.2 ∉
          (x.1.skeleton.tree (x.2.b.child (clRegionData x.1.skeleton x.2.block x.2.cl).positive).1.1).branching ∨ t1 = t1')
    (hn : ∀ x ∈ canonFinsetK p kind A c,
      (x.2.b.child (clRegionData x.1.skeleton x.2.block x.2.cl).negative).1.2 ∉
          (x.1.skeleton.tree (x.2.b.child (clRegionData x.1.skeleton x.2.block x.2.cl).negative).1.1).branching ∨ t2 = t2') :
    twistedRecenteredFW pw g S A.skeleton c.a (canonFinsetK p kind A c) L γ δ F base W t0 t1 t2 e f g' k =
      twistedRecenteredFW pw g S A.skeleton c.a (canonFinsetK p kind A c) L γ δ F base W t0 t1' t2' e f g' k := by
  unfold twistedRecenteredFW
  congr 1
  refine Finset.sum_congr rfl fun x hx => ?_
  unfold twistedLocalKernelFW
  exact clLocalKernelFW_congr_t pw g x.1.data x.1.plain (clRegionData x.1.skeleton x.2.block x.2.cl) L γ δ F
    (stateLayer x.1) (stateLayer_isLayering x.1) base _ W t0 t1 t2 t1' t2' e f g' k (hp x hx) (hn x hx)

/-- **`hind`** for the weighted unit kernel (main's `unitHk_hind`). -/
theorem unitHkFW_hind (P : WTParams) (p : ℕ) {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} (B : CLChainAssembly G R n)
    (RD : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer) (g : Fin w → Mom P.d → ℂ) (h : ℕ → Mom P.d → ℝ) (wBar : Mom P.d)
    (leaf : Fin 3 → Prop) (hl0 : ¬ leaf 0)
    (hleaf1 : leaf 1 → ∀ x ∈ canonFinsetK p (objKind w) (startState B RD hG layer hLayer) (chainStart B),
      (x.2.b.child (clRegionData x.1.skeleton x.2.block x.2.cl).positive).1.2 ∉
        (x.1.skeleton.tree (x.2.b.child (clRegionData x.1.skeleton x.2.block x.2.cl).positive).1.1).branching)
    (hleaf2 : leaf 2 → ∀ x ∈ canonFinsetK p (objKind w) (startState B RD hG layer hLayer) (chainStart B),
      (x.2.b.child (clRegionData x.1.skeleton x.2.block x.2.cl).negative).1.2 ∉
        (x.1.skeleton.tree (x.2.b.child (clRegionData x.1.skeleton x.2.block x.2.cl).negative).1.1).branching)
    (lam : ℤ) (t t' : Fin 3 → ℝ) (k : Fin 4 → Mom P.d) (ht : ∀ i, ¬ leaf i → t i = t' i) :
    unitHkFW P p B RD hG layer hLayer g h wBar lam t k = unitHkFW P p B RD hG layer hLayer g h wBar lam t' k := by
  have h0 : t 0 = t' 0 := ht 0 hl0
  unfold unitHkFW
  rw [h0]
  apply twistedRecenteredFW_congr_leaf (A := startState B RD hG layer hLayer) (c := chainStart B)
  · intro x hx
    by_cases h1 : leaf 1
    · exact Or.inl (hleaf1 h1 x hx)
    · exact Or.inr (ht 1 h1)
  · intro x hx
    by_cases h2 : leaf 2
    · exact Or.inl (hleaf2 h2 x hx)
    · exact Or.inr (ht 2 h2)

end Hind

/-! ## The unit bound from the staged `V5FrontierClassBoundAt`, and continuity from T5 -/

/-- The X-norm bound of a weighted unit class kernel, from the staged **`V5FrontierClassBoundAt`**. -/
theorem unit_vineest_boundW {P : WTParams} (hV : V5FrontierClassBoundAt P) {p : ℕ} (hp : p < P.D)
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
    (fun x => WaveTurbulence.Canon.layer_le_of_isCanonGC hcan x) hord hcl centre wBar (lam : ℝ) g cψ hc hgp hre none
    (fun s hs => by cases hs) (rowCoherent_of_canonical hM9 B RD hG layer hLayer p hcan centre wBar P.L P.γ P.δ h)
  refine le_of_le_of_eq hb ?_
  have hA : 0 ≤ cψ ^ (9 * U.card + 4 * clLocalOrder2 RD hG R) * topFilterMass :=
    mul_nonneg (pow_nonneg (by linarith) _) topFilterMass_nonneg
  rw [← ENNReal.ofReal_mul hA]
  congr 1
  unfold unitMassFW unitMass
  rw [step3D_M₁_const hM9 B RD hG layer hLayer centre (fun _ => (0 : Mom P.d)) wBar 0]
  ring

/-- **`hcont`** for the weighted unit kernels, from T5 `weightedClassContinuity` and INC-TOP. -/
theorem unit_hcontW {P : WTParams} (hgate : CoherentGateH P) (hinc : IncoherentGateH P)
    (htop : TopIncoherentDecayAtR P)
    (hd : 1 ≤ P.d) (hη0 : 0 < P.η) (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2)
    (hC : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    {p : ℕ} (hp : p < P.D) (h : ℕ → Mom P.d → ℝ) (bb : ℝ)
    (hh : ∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (h r) ≤ ENNReal.ofReal bb)
    {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
    {n : ℕ} (hprime : IsPrimeGarden G) (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
    (hcan : IsCanonGC (p + 1) (layeredReconstruction RD hG layer hLayer))
    (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4)
    (g : Fin w → Mom P.d → ℂ) (cψ : ℝ) (hc : 1 ≤ cψ) (hgp : ∀ j, GPresented (32 * P.d) (g j) cψ)
    (hre : ∀ j x, (g j x).im = 0) (centre : Fin 4 → Mom P.d) (wBar : Mom P.d) (lam : ℤ) :
    ∀ E ∈ outSet (unitD hM9 B RD hG layer hLayer centre wBar) P.L P.γ P.η,
      ContinuousOn (fun t => unitHkFW P p B RD hG layer hLayer g h wBar lam t (sumintBoundary (G.sign a.toNode) E))
        (cubeSet (unitD hM9 B RD hG layer hLayer centre wBar).qOut) := by
  have hB : ProfileBound P h (fun _ => max bb 1) p := fun r hr =>
    ⟨le_max_of_le_right zero_le_one,
      (hh r hr).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩
  exact weightedClassContinuity (kind := objKind w) (lam : ℝ) hgate hinc htop hd hη0 hη6 hη2 hC hδ hL hw hp hB
    (fun r _ => lt_of_lt_of_le zero_lt_one (le_max_right _ _)) hprime hM9 B RD hG layer hLayer
    (fun x => WaveTurbulence.Canon.layer_le_of_isCanonGC hcan x) hord centre wBar (g a.1.1) cψ hc (hgp _) (hre _)
    none (fun s hs => by cases hs)
    (rowCoherent_of_canonical hM9 B RD hG layer hLayer p hcan centre wBar P.L P.γ P.δ h)

open scoped Classical in
/-- **The hinge data of the weighted units** (main's `hinge_units_const`; the constant depends only on `(d, η)`). -/
theorem hinge_units_constW (d : ℕ) (η : ℝ) (hη : 0 ≤ η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : WTParams), P.d = d → P.η = η → V5FrontierClassBoundAt P → 0 ≤ P.C₁ → 0 < P.L →
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
    (fun j c' => hq j) hcont (fun j c lam => unit_vineest_boundW hV hp (h j) (bb j) (hbb j) (hh j) hprime hM9 (B₀ j)
      RD hG layer hLayer hcan hord (hcl j) g cψ hc hgp hre (centre j c) base lam) P.L base tt roots selSk lay hmom
    (fun j τ i => if leaf j i then td j i else clockOf Gsb tt τ (hclk j i)) G1 G2 lam
  refine ⟨H.leafWrap leaf td, Mh, hMh, fun κ hκ τ hτ j c' hball => ?_, hprod⟩
  have h1 := hsum κ hκ τ hτ j c' hball
  rw [hind j (lam j) _ (fun i => clockOf Gsb tt τ (hclk j i)) _ (fun i hi => by simp [hi])] at h1
  exact H.leafWrap_hasSum leaf td j c' _ (fun i => clockOf Gsb tt τ (hclk j i)) h1

end WaveTurbulence.Flower.Stage1WVine
