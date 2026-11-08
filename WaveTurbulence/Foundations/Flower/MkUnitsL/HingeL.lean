/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkUnitsL.ClassSumL
public import WaveTurbulence.Foundations.Flower.MkUnitsL.ContL
public import WaveTurbulence.Foundations.Flower.MkUnits.WHinge

/-! # MK-UNITS-L (B3-2): the hinge data of the weighted units with per-unit top filters

* `unitMassFWL`: the weighted VINEEST mass of a unit with the product filter `S`,
  `cψ^(9|U| + 4n₂) · topFilterMass^{|S|} · unitMass` (Stage1WVine's `unitMassFW` is the `|S| = 1` mass).
* `twistedRecenteredFWL_congr_leaf`, `unitHkFWL_hind`: leaf independence (Stage1WVine's).
* `unit_vineest_boundWL`: V5W-2L's **`V5FrontierClassBoundAtL`** (the isolated hypothesis) gives the X-norm bound of
  a unit with the mass `unitMassFWL`.
* `unit_hcontWL`: list-T5 (`ContL`) gives `hcont`.
* `hinge_units_constWL`, `ChinFWL`: main's `hinge_units_const` for the weighted kernels with per-unit filters
  `SU : J → List ℝ`; the constant depends only on `(d, η)`.
* `unit_hinge_dataWMkL`: B3's `unit_hinge_dataWMk` with `SU`.

Adapted from `Flower/Stage1WVine/WHinge1.lean`, `WHinge2.lean` and `Flower/MkUnits/WHinge.lean` (see
`COPIED-SHA256SUMS`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.MkUnitsL
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA
  WaveTurbulence.VineEstS4 WaveTurbulence.VineC WaveTurbulence.LFTwist WaveTurbulence.VineAlign
  WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS5C
  VineParamContract WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.Represents
  WaveTurbulence.Twist WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W WaveTurbulence.Flower.Stage1WVine
  WaveTurbulence.Flower.MkUnits
open WaveTurbulence.Flower.V5W2L (topFilterWeightL twistedLocalKernelFWL twistedRecenteredFWL)
open scoped ENNReal

/-- The weighted VINEEST mass of a unit with a product of top filters `S`:
`cψ^(9|U| + 4 n₂) · topFilterMass^{|S|}` times main's `unitMass`. -/
def unitMassFWL (P : WTParams) (S : List ℝ) {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (RD : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer) (cψ B₀ : ℝ) : ℝ :=
  cψ ^ (9 * U.card + 4 * clLocalOrder2 RD hG R) * topFilterMass ^ S.length * unitMass P hM9 B RD hG layer hLayer B₀

theorem unitMassFWL_nonneg (P : WTParams) (S : List ℝ) {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (RD : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer) (cψ B₀ : ℝ)
    (hc : 0 ≤ cψ) (hC₁ : 0 ≤ P.C₁) (hL0 : 0 < P.L) (hB₀ : 0 ≤ B₀) :
    0 ≤ unitMassFWL P S hM9 B RD hG layer hLayer cψ B₀ :=
  mul_nonneg (mul_nonneg (pow_nonneg hc _) (pow_nonneg topFilterMass_nonneg _))
    (mul_nonneg (mul_nonneg (pow_nonneg (mul_nonneg hC₁ (Real.sqrt_nonneg _)) _) (Real.rpow_nonneg hL0.le _))
      (WaveTurbulence.VineEstS5C.regionLeafSize_const_nonneg RD hG R layer hLayer hB₀))

section Hind
variable {w : ℕ} {ι : Type*} [Fintype ι]

/-- The weighted class kernel is independent of the clocks of lower children that are leaves in every member. -/
theorem twistedRecenteredFWL_congr_leaf {d p : ℕ} {kind : Bool} {A : FamilyReconstruction w ι}
    {c : ChainAt A.skeleton A.family} (pw : ℕ) (g : Mom d → ℂ) (S : List ℝ) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (base : Mom d) (W : ℝ → ℂ) (t0 t1 t2 t1' t2' : ℝ) (e f g' k : Mom d)
    (hp : ∀ x ∈ canonFinsetK p kind A c,
      (x.2.b.child (clRegionData x.1.skeleton x.2.block x.2.cl).positive).1.2 ∉
          (x.1.skeleton.tree (x.2.b.child (clRegionData x.1.skeleton x.2.block x.2.cl).positive).1.1).branching ∨ t1 = t1')
    (hn : ∀ x ∈ canonFinsetK p kind A c,
      (x.2.b.child (clRegionData x.1.skeleton x.2.block x.2.cl).negative).1.2 ∉
          (x.1.skeleton.tree (x.2.b.child (clRegionData x.1.skeleton x.2.block x.2.cl).negative).1.1).branching ∨ t2 = t2') :
    twistedRecenteredFWL pw g S A.skeleton c.a (canonFinsetK p kind A c) L γ δ F base W t0 t1 t2 e f g' k =
      twistedRecenteredFWL pw g S A.skeleton c.a (canonFinsetK p kind A c) L γ δ F base W t0 t1' t2' e f g' k := by
  unfold twistedRecenteredFWL
  congr 1
  refine Finset.sum_congr rfl fun x hx => ?_
  unfold twistedLocalKernelFWL
  exact clLocalKernelFW_congr_t pw g x.1.data x.1.plain (clRegionData x.1.skeleton x.2.block x.2.cl) L γ δ F
    (stateLayer x.1) (stateLayer_isLayering x.1) base _ W t0 t1 t2 t1' t2' e f g' k (hp x hx) (hn x hx)

/-- **`hind`** for the weighted unit kernel (main's `unitHk_hind`). -/
theorem unitHkFWL_hind (P : WTParams) (p : ℕ) (S : List ℝ) {G : Garden w} {U : Finset (GBranch G.tree)}
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
    unitHkFWL P p S B RD hG layer hLayer g h wBar lam t k = unitHkFWL P p S B RD hG layer hLayer g h wBar lam t' k := by
  have h0 : t 0 = t' 0 := ht 0 hl0
  unfold unitHkFWL
  rw [h0]
  apply twistedRecenteredFWL_congr_leaf (A := startState B RD hG layer hLayer) (c := chainStart B)
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
theorem unit_vineest_boundWL {P : WTParams} (hV : V5W2L.V5FrontierClassBoundAtL P) {p : ℕ} (hp : p < P.D)
    (h : ℕ → Mom P.d → ℝ) (B₀ : ℝ) (hB₀ : 0 ≤ B₀)
    (hh : ∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (h r) ≤ ENNReal.ofReal B₀)
    {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
    {n : ℕ} (hprime : IsPrimeGarden G) (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
    (hcan : IsCanonGC (p + 1) (layeredReconstruction RD hG layer hLayer))
    (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4) (hcl : clLocalOrder1 R ≤ P.N 1 ^ 4)
    (g : Fin w → Mom P.d → ℂ) (cψ : ℝ) (hc : 1 ≤ cψ) (hgp : ∀ j, GPresented (32 * P.d) (g j) cψ)
    (hre : ∀ j x, (g j x).im = 0) (S : List ℝ) (hS : ∀ s ∈ S, 0 < s) (centre : Fin 4 → Mom P.d) (wBar : Mom P.d)
    (lam : ℤ) :
    XNorm00Restr (2 * P.η ^ 8) (outBox (unitD hM9 B RD hG layer hLayer centre wBar))
      (outSet (unitD hM9 B RD hG layer hLayer centre wBar) P.L P.γ P.η)
      (fun t E => unitHkFWL P p S B RD hG layer hLayer g h wBar lam t (sumintBoundary (G.sign a.toNode) E)) ≤
    ENNReal.ofReal ((1 + |(lam : ℝ)|) ^ (6 * P.η ^ 6) * unitMassFWL P S hM9 B RD hG layer hLayer cψ B₀) := by
  have hb := hV hp h B₀ hB₀ hh hprime hM9 B RD hG layer hLayer (objKind w) (canonicalObject_of_isCanonGC hcan)
    (fun x => WaveTurbulence.Canon.layer_le_of_isCanonGC hcan x) hord hcl centre wBar (lam : ℝ) g cψ hc hgp hre S hS (rowCoherent_of_canonical hM9 B RD hG layer hLayer p hcan centre wBar P.L P.γ P.δ h)
  refine le_of_le_of_eq hb ?_
  have hA : 0 ≤ cψ ^ (9 * U.card + 4 * clLocalOrder2 RD hG R) * topFilterMass ^ S.length :=
    mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg topFilterMass_nonneg _)
  rw [← ENNReal.ofReal_mul hA]
  congr 1
  unfold unitMassFWL unitMass
  rw [step3D_M₁_const hM9 B RD hG layer hLayer centre (fun _ => (0 : Mom P.d)) wBar 0]
  ring

/-- **`hcont`** for the weighted unit kernels, from T5 `weightedClassContinuity` and INC-TOP. -/
theorem unit_hcontWL {P : WTParams} (hgate : CoherentGateH P) (hinc : IncoherentGateH P)
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
    (hre : ∀ j x, (g j x).im = 0) (S : List ℝ) (hS : ∀ s ∈ S, 0 < s) (centre : Fin 4 → Mom P.d) (wBar : Mom P.d)
    (lam : ℤ) :
    ∀ E ∈ outSet (unitD hM9 B RD hG layer hLayer centre wBar) P.L P.γ P.η,
      ContinuousOn (fun t => unitHkFWL P p S B RD hG layer hLayer g h wBar lam t (sumintBoundary (G.sign a.toNode) E))
        (cubeSet (unitD hM9 B RD hG layer hLayer centre wBar).qOut) := by
  have hB : ProfileBound P h (fun _ => max bb 1) p := fun r hr =>
    ⟨le_max_of_le_right zero_le_one,
      (hh r hr).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩
  exact weightedClassContinuityL (kind := objKind w) (lam : ℝ) hgate hinc htop hd hη0 hη6 hη2 hC hδ hL hw hp hB
    (fun r _ => lt_of_lt_of_le zero_lt_one (le_max_right _ _)) hprime hM9 B RD hG layer hLayer
    (fun x => WaveTurbulence.Canon.layer_le_of_isCanonGC hcan x) hord centre wBar (g a.1.1) cψ hc (hgp _) (hre _)
    S hS
    (rowCoherent_of_canonical hM9 B RD hG layer hLayer p hcan centre wBar P.L P.γ P.δ h)

open scoped Classical in
/-- **The hinge data of the weighted units** (main's `hinge_units_const`; the constant depends only on `(d, η)`). -/
theorem hinge_units_constWL (d : ℕ) (η : ℝ) (hη : 0 ≤ η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : WTParams), P.d = d → P.η = η → V5W2L.V5FrontierClassBoundAtL P → 0 ≤ P.C₁ → 0 < P.L →
      ∀ {p : ℕ}, p < P.D → ∀ {w : ℕ} {S : Garden w} (hprime : IsPrimeGarden S) (hM9 : VINEPARAM)
      (RD : ReconstructionData S) (hG : S.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
      (hLayer : IsLayering (RD.garden hG) layer) (hcan : IsCanonGC (p + 1) (layeredReconstruction RD hG layer hLayer))
      (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4)
      {J : Type} [Fintype J] {U₀ : J → Finset (GBranch S.tree)} {a₀ b₀ : J → GBranch S.tree}
      {R₀ : ∀ j, CLRegionData S (U₀ j) (a₀ j) (b₀ j)} {n₀ : J → ℕ} (B₀ : ∀ j, CLChainAssembly S (R₀ j) (n₀ j))
      (hcl : ∀ j, clLocalOrder1 (R₀ j) ≤ P.N 1 ^ 4)
      (g : Fin w → Mom P.d → ℂ) (cψ : ℝ) (hc : 1 ≤ cψ) (hgp : ∀ j, GPresented (32 * P.d) (g j) cψ)
      (hre : ∀ j x, (g j x).im = 0) (SU : J → List ℝ) (hSU : ∀ j, ∀ s ∈ SU j, 0 < s)
      (h : J → ℕ → Mom P.d → ℝ) (bb : J → ℝ) (hbb : ∀ j, 0 ≤ bb j)
      (hh : ∀ j, ∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (h j r) ≤ ENNReal.ofReal (bb j))
      (centre : J → (Fin 4 → Fin P.d → ℤ) → Fin 4 → Mom P.d) (base : Mom P.d)
      (hq : ∀ j, qOutOf RD hG layer (a₀ j) (b₀ j) (R₀ j) 1 ≤ qOutOf RD hG layer (a₀ j) (b₀ j) (R₀ j) 0 ∧
        qOutOf RD hG layer (a₀ j) (b₀ j) (R₀ j) 2 ≤ qOutOf RD hG layer (a₀ j) (b₀ j) (R₀ j) 0)
      (hcont : ∀ j c (lam : ℤ), ∀ E ∈ outSet (unitD hM9 (B₀ j) RD hG layer hLayer (centre j c) base) P.L P.γ P.η,
        ContinuousOn (fun t => unitHkFWL P p (SU j) (B₀ j) RD hG layer hLayer g (h j) base lam t
          (sumintBoundary (S.sign (a₀ j).toNode) E))
          (cubeSet (unitD hM9 (B₀ j) RD hG layer hLayer (centre j c) base).qOut))
      (Gsb : Garden w) (tt : Fin w → ℝ) (roots : Fin w → Fin P.d → ℤ)
      (selSk : GenDecoration Gsb P.d roots 0 → Prop) (lay : GBranch Gsb.tree → ℕ)
      (hmom : J → Fin 4 → GNode Gsb.tree) (hclk : J → Fin 3 → ClkSrc Gsb)
      (leaf : J → Fin 3 → Prop) (td : J → Fin 3 → ℝ)
      (hind : ∀ j (lam : ℤ) (t t' : Fin 3 → ℝ) (k : Fin 4 → Mom P.d), (∀ i, ¬ leaf j i → t i = t' i) →
        unitHkFWL P p (SU j) (B₀ j) RD hG layer hLayer g (h j) base lam t k =
          unitHkFWL P p (SU j) (B₀ j) RD hG layer hLayer g (h j) base lam t' k),
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
            (unitHkFWL P p (SU j) (B₀ j) RD hG layer hLayer g (h j) base (lam j) (fun i => clockOf Gsb tt τ (hclk j i))
              (fun i => base + latticePoint P.L (κ.1 (hmom j i))))) ∧
        ∏ j, Mh j = C ^ Fintype.card J *
          (∏ j, unitMassFWL P (SU j) hM9 (B₀ j) RD hG layer hLayer cψ (bb j)) *
          ∏ j, (1 + |((lam j : ℤ) : ℝ)|) ^ (6 * P.η ^ 6) := by
  obtain ⟨C, hC, hex⟩ := exists_hinge_data_mod_ck_w (θ := 2 * η ^ 8) (by positivity) d
  refine ⟨C, hC, fun P hPd hPη hV hC₁ hL0 {p} hp {w} {S} hprime hM9 RD hG layer hLayer hcan hord {J} _ {U₀} {a₀} {b₀}
    {R₀} {n₀} B₀ hcl g cψ hc hgp hre SU hSU h bb hbb hh centre base hq hcont Gsb tt roots selSk lay hmom hclk leaf td hind
    G1 G2 lam => ?_⟩
  subst hPd hPη
  have hM0 : ∀ j, 0 ≤ unitMassFWL P (SU j) hM9 (B₀ j) RD hG layer hLayer cψ (bb j) := fun j =>
    unitMassFWL_nonneg P (SU j) hM9 (B₀ j) RD hG layer hLayer cψ (bb j) (by linarith) hC₁ hL0 (hbb j)
  obtain ⟨H, Mh, hMh, hsum, hprod⟩ := hex Gsb J (fun j c => unitD hM9 (B₀ j) RD hG layer hLayer (centre j c) base)
    (fun j c => outSet (unitD hM9 (B₀ j) RD hG layer hLayer (centre j c) base) P.L P.γ P.η)
    (fun j => S.sign (a₀ j).toNode) (fun j lam t k => unitHkFWL P p (SU j) (B₀ j) RD hG layer hLayer g (h j) base lam t k)
    (fun j => unitMassFWL P (SU j) hM9 (B₀ j) RD hG layer hLayer cψ (bb j)) (6 * P.η ^ 6) hM0
    (fun j c' => hq j) hcont (fun j c lam => unit_vineest_boundWL hV hp (h j) (bb j) (hbb j) (hh j) hprime hM9 (B₀ j)
      RD hG layer hLayer hcan hord (hcl j) g cψ hc hgp hre (SU j) (hSU j) (centre j c) base lam) P.L base tt roots selSk lay hmom
    (fun j τ i => if leaf j i then td j i else clockOf Gsb tt τ (hclk j i)) G1 G2 lam
  refine ⟨H.leafWrap leaf td, Mh, hMh, fun κ hκ τ hτ j c' hball => ?_, hprod⟩
  have h1 := hsum κ hκ τ hτ j c' hball
  rw [hind j (lam j) _ (fun i => clockOf Gsb tt τ (hclk j i)) _ (fun i hi => by simp [hi])] at h1
  exact H.leafWrap_hasSum leaf td j c' _ (fun i => clockOf Gsb tt τ (hclk j i)) h1

/-- The hinge-data constant of `hinge_units_constWL`, as a function of `(d, η)`. -/
def ChinFWL (d : ℕ) (η : ℝ) : ℝ :=
  if h : 0 ≤ η then (hinge_units_constWL d η h).choose else 0

theorem ChinFWL_spec (d : ℕ) (η : ℝ) (h : 0 ≤ η) : 0 ≤ ChinFWL d η := by
  unfold ChinFWL
  rw [dif_pos h]
  exact (hinge_units_constWL d η h).choose_spec.1

open scoped Classical in
open scoped Classical in
/-- **The hinge data of the weighted units of the representative at a marking with per-unit top filters** (B3's
`unit_hinge_dataWMk` with `SU`, the unit bound V5W-2L's `V5FrontierClassBoundAtL`). -/
theorem unit_hinge_dataWMkL (P : WTParams) (hV : V5W2L.V5FrontierClassBoundAtL P) (hM9 : VINEPARAM)
    (hgate : CoherentGateH P) (hinc : IncoherentGateH P) (htop : TopIncoherentDecayAtR P)
    (hd1 : 1 ≤ P.d) (hη0 : 0 < P.η) (hη6 : 6 * P.η ^ 6 ≤ P.η)
    (hη2 : P.η ≤ 1 / 2) (hC1 : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL1 : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    {p : ℕ} (hp : p < P.D) {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
    (hcan : IsCanonGC (p + 1) a.layered)
    (hord : (a.prime.data.garden a.prime.prime.1).order ≤ P.N (p + 1) ^ 4)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ) (hc : 1 ≤ cψ) (hgp : ∀ j, GPresented (32 * P.d) (g j) cψ)
    (hre : ∀ j x, (g j x).im = 0)
    (SU : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length → List ℝ)
    (hSU : ∀ j, ∀ s ∈ SU j, 0 < s)
    (hp' : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (bb : ℝ) (hbb : 0 ≤ bb)
    (hB : ∀ q j j', q ≤ p → SNormR (40 * P.d) (40 * P.d) (hp' q j j') ≤ ENNReal.ofReal bb)
    (lam : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length → ℤ) :
    ∃ (H : HingeFam (Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) P.d)
      (Mh : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length → ℝ),
      (∀ j c', ∑' l, H.w j c' l ≤ Mh j) ∧
      HHkProp (a.normalizedPiece P.d (mk a.prime)) tt base roots
        (selSkCMk a mk P.L P.γ P.η (lt_of_lt_of_le zero_lt_one hL1).ne' base roots)
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hclk
          (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hmom
          (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
        (fun j => unitHkFWL P p (SU j) (sourceAssemblyMk a mk j) a.prime.data a.prime.prime.1 (sourceLayer a)
          (sourceLayer_isLayering a) g
          (unitProfile (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) hp' j) base
          (lam j)) H ∧
      ∏ j, Mh j = ChinFWL P.d P.η ^ Fintype.card (Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) *
        (∏ j, unitMassFWL P (SU j) hM9 (sourceAssemblyMk a mk j) a.prime.data a.prime.prime.1 (sourceLayer a)
          (sourceLayer_isLayering a) cψ bb) *
        ∏ j, (1 + |((lam j : ℤ) : ℝ)|) ^ (6 * P.η ^ 6) := by
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one hL1
  have hMa := Mole.garden_isMolecule a.prime.skeleton
  have hspec := (hinge_units_constWL P.d P.η hη0.le).choose_spec
  have hChin : ChinFWL P.d P.η = (hinge_units_constWL P.d P.η hη0.le).choose := by
    unfold ChinFWL; rw [dif_pos hη0.le]
  rw [hChin]
  have hcan' : IsCanonGC (p + 1) (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a)) := by rw [sourceLayer_reconstructs]; exact hcan
  have hordS : a.prime.skeleton.order ≤ P.N (p + 1) ^ 4 := by
    have := a.prime.data.decoded_order a.prime.prime.1 (a.prime.data.garden_decodes a.prime.prime.1)
    omega
  have hcl : ∀ j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length,
      clLocalOrder1 (regionOf (unitBlkMk hMa a.totalSigma (mk a.prime) j)) ≤ P.N 1 ^ 4 := fun j =>
    clLocalOrder1_le_N1 P _ hordS
  have hh' : ∀ j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length, ∀ r ≤ p,
      SNormR (40 * P.d) (40 * P.d) (unitProfile (unitBlkMk hMa a.totalSigma (mk a.prime)) hp' j r) ≤
        ENNReal.ofReal bb :=
    fun j r hr => hB r _ _ hr
  have hLay : (a.normalizedPiece P.d (mk a.prime)).layer = (stSt a.prime.skeleton a.totalSigma (mk a.prime)).layer
      (RegRed.coreLayer (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a))
        a.prime.data a.prime.prime.1 (a.prime.data.garden_decodes a.prime.prime.1)) := by
    funext c
    show RegRed.coreLayer a.layered a.prime.data a.prime.prime.1 a.prime.decodes
      ((stSt a.prime.skeleton a.totalSigma (mk a.prime)).M.ob c) = _
    rw [coreLayer_of_spec a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) a.layered
      (sourceLayer_reconstructs a) a.prime.decodes]
    exact (coreLayer_of_spec a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) _ rfl _ _).symm
  have hG1 := g1_unitsMk P hMa a.totalSigma hM9 (Mk := mk a.prime) (B₀ := sourceAssemblyMk a mk) a.prime.data
    a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) base tt roots
    (selSkCMk a mk P.L P.γ P.η hL0.ne' base roots)
    (fun j c => sumintBoundary (a.prime.skeleton.sign (unitBlkMk hMa a.totalSigma (mk a.prime) j).upper.toNode)
      (fun i => latPt P.d (c i)))
    (fun j c hc => qOut_one_eq_layMk hMa a.totalSigma j a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) c hc)
    (fun j c hc => qOut_two_eq_layMk hMa a.totalSigma j a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) c hc)
    (fun j => hqle_unitsMk hMa a.totalSigma j a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a))
  let D' : SplicedKernelData (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.d :=
    ⟨fun _ => 0, ∅, fun _ => 0, fun _ _ => 0, fun _ => 0,
      NormalizedSplice.gapSpecificationMk a.prime.skeleton a.totalSigma (mk a.prime), fun _ => 0, fun _ => 0⟩
  have hG2 : ∀ κ : GenDecoration (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.d roots 0,
      selSkCMk a mk P.L P.γ P.η hL0.ne' base roots κ →
      ∀ (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) (c : Fin 4 → Fin P.d → ℤ),
      (∀ i, ‖(base + latticePoint P.L (κ.1 ((stShape hMa a.totalSigma (mk a.prime)).hmom
          (unitBlkMk_disj hMa a.totalSigma (mk a.prime)) j i))) - latPt P.d (c i)‖ ≤ 1) →
        sumintBoundary (a.prime.skeleton.sign (unitBlkMk hMa a.totalSigma (mk a.prime) j).upper.toNode)
            (fun i => base + latticePoint P.L (κ.1 ((stShape hMa a.totalSigma (mk a.prime)).hmom
              (unitBlkMk_disj hMa a.totalSigma (mk a.prime)) j i))) ∈
          outSet (unitD hM9 (sourceAssemblyMk a mk j) a.prime.data a.prime.prime.1 (sourceLayer a)
            (sourceLayer_isLayering a)
            (sumintBoundary (a.prime.skeleton.sign (unitBlkMk hMa a.totalSigma (mk a.prime) j).upper.toNode)
              (fun i => latPt P.d (c i))) base) P.L P.γ P.η := by
    intro κ hκ j c hball
    refine mem_outSet_of_gsbNMk hMa a.prime.prime.1 a.totalSigma hL0.ne' P.γ P.η base roots κ D' rfl ?_ j c hball _
      rfl rfl
    have h1 := NormalizedSplice.gapValue_eq_indicatorMk a.totalSigma D' rfl P.L P.γ P.η base κ.1
    rw [← h1]
    rw [show NormalizedSplice.gapValueMk a.prime.skeleton a.totalSigma (mk a.prime) P.L P.γ P.η base κ.1 = 1 from hκ]
    exact one_ne_zero
  have hcont : ∀ (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length)
      (c : Fin 4 → Fin P.d → ℤ) (lam : ℤ),
      ∀ E ∈ outSet (unitD hM9 (sourceAssemblyMk a mk j) a.prime.data a.prime.prime.1 (sourceLayer a)
        (sourceLayer_isLayering a)
        (sumintBoundary (a.prime.skeleton.sign (unitBlkMk hMa a.totalSigma (mk a.prime) j).upper.toNode)
          (fun i => latPt P.d (c i))) base) P.L P.γ P.η,
        ContinuousOn (fun t => unitHkFWL P p (SU j) (sourceAssemblyMk a mk j) a.prime.data a.prime.prime.1 (sourceLayer a)
          (sourceLayer_isLayering a) g (unitProfile (unitBlkMk hMa a.totalSigma (mk a.prime)) hp' j) base lam t
          (sumintBoundary (a.prime.skeleton.sign (unitBlkMk hMa a.totalSigma (mk a.prime) j).upper.toNode) E))
          (cubeSet (unitD hM9 (sourceAssemblyMk a mk j) a.prime.data a.prime.prime.1 (sourceLayer a)
            (sourceLayer_isLayering a)
            (sumintBoundary (a.prime.skeleton.sign (unitBlkMk hMa a.totalSigma (mk a.prime) j).upper.toNode)
              (fun i => latPt P.d (c i))) base).qOut) :=
    fun j c lam => unit_hcontWL hgate hinc htop hd1 hη0 hη6 hη2 hC1 hδ hL1 hw hp
      (unitProfile (unitBlkMk hMa a.totalSigma (mk a.prime)) hp' j) bb (hh' j) a.prime.prime hM9
      (sourceAssemblyMk a mk j) a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) hcan' hord g cψ
      hc hgp hre (SU j) (hSU j) _ base lam
  have hind : ∀ (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) (lam : ℤ)
      (t t' : Fin 3 → ℝ) (k : Fin 4 → Mom P.d), (∀ i, ¬ leafFlag hMa a.totalSigma j i → t i = t' i) →
      unitHkFWL P p (SU j) (sourceAssemblyMk a mk j) a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) g
        (unitProfile (unitBlkMk hMa a.totalSigma (mk a.prime)) hp' j) base lam t k =
      unitHkFWL P p (SU j) (sourceAssemblyMk a mk j) a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) g
        (unitProfile (unitBlkMk hMa a.totalSigma (mk a.prime)) hp' j) base lam t' k :=
    fun j lam t t' k ht => unitHkFWL_hind P p (SU j) (sourceAssemblyMk a mk j) a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) g _ base (leafFlag hMa a.totalSigma j) (leafFlag_zeroMk hMa a.totalSigma j)
      (unit_hleaf1Mk hMa a.totalSigma (mk a.prime) a.prime.data a.prime.prime.1 (sourceLayer a)
        (sourceLayer_isLayering a) a.prime.prime j)
      (unit_hleaf2Mk hMa a.totalSigma (mk a.prime) a.prime.data a.prime.prime.1 (sourceLayer a)
        (sourceLayer_isLayering a) a.prime.prime j) lam t t' k ht
  obtain ⟨H, Mh, hsum, hHk, hprod⟩ := hspec.2 P rfl rfl hV (by linarith) hL0 hp a.prime.prime hM9 a.prime.data
    a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) hcan' hord (B₀ := sourceAssemblyMk a mk) hcl g cψ hc
    hgp hre SU hSU (fun j => unitProfile (unitBlkMk hMa a.totalSigma (mk a.prime)) hp' j) (fun _ => bb) (fun _ => hbb) hh'
    (fun j c => sumintBoundary (a.prime.skeleton.sign (unitBlkMk hMa a.totalSigma (mk a.prime) j).upper.toNode)
      (fun i => latPt P.d (c i))) base (fun j => hqle_unitsMk hMa a.totalSigma j a.prime.data a.prime.prime.1
        (sourceLayer a) (sourceLayer_isLayering a)) hcont (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G tt roots
    (selSkCMk a mk P.L P.γ P.η hL0.ne' base roots)
    ((stSt a.prime.skeleton a.totalSigma (mk a.prime)).layer
      (RegRed.coreLayer (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a))
        a.prime.data a.prime.prime.1 (a.prime.data.garden_decodes a.prime.prime.1)))
    ((stShape hMa a.totalSigma (mk a.prime)).hmom (unitBlkMk_disj hMa a.totalSigma (mk a.prime)))
    ((stShape hMa a.totalSigma (mk a.prime)).hclk (unitBlkMk_disj hMa a.totalSigma (mk a.prime)))
    (leafFlag hMa a.totalSigma)
    (fun j i => ((qOutOf a.prime.data a.prime.prime.1 (sourceLayer a) (unitBlkMk hMa a.totalSigma (mk a.prime) j).upper
      (unitBlkMk hMa a.totalSigma (mk a.prime) j).lower (regionOf (unitBlkMk hMa a.totalSigma (mk a.prime) j)) i : ℕ) :
        ℝ)) hind hG1 hG2 lam
  refine ⟨H, Mh, hsum, ?_, hprod⟩
  intro κ hκ τ hτ j c hball
  rw [hLay] at hτ
  exact hHk κ hκ τ hτ j c hball

end WaveTurbulence.Flower.MkUnitsL
