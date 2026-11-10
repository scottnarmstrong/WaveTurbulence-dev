/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WVine.GenVB1
public import WaveTurbulence.Foundations.VineEst.VineSpaceK.StatementDefs
public import WaveTurbulence.Foundations.Stage1.Represents.RepVB3

/-! # MK-UNITS-L (B3-2): VINE-B♯ with a slot family and per-unit top weights — definitions and the pointwise glue

Stage1WVine's generic VINE-B♯ (`Stage1WVine/GenVB1`) with the slot family `Fs` replaced by a `SlotFamW`: the slot
kernels `Fs.fs` together with a top weight `Fs.tw a` read at every region top `a` as `VineSpaceK.nodeWeight` (the
momenta at `a` and its three children, all in the region's local support).  The regional star product of a unit
carries its top weight (`starProdGW`); the skeleton value carries the product of the units' top weights at the
skeleton decoration (`topW`, `skelValW`).  For `Fs.tw = 1` everything is Stage1WVine's.  The per-unit top weight is
the product filter `topFilterWeightL (SU j)` of F-B3s-4 (ruling R179).

* `SlotFamW`, `topW`, `modeGW`, `skelTermW`, `skelValW`.
* `starProdGW`, `clLocalStarProductGW`, `clLocalSummandGW`, `gUnitGW`: Stage1WVine's with the top weight.
* `modalFnGW`: single modes at the outer slots, `Fs` at the regional slots (top weights unchanged).
* `regional_glueGW`, `integrand_glueGW`: the pointwise factorization of the glued integrand (the top weight of a unit
  is local: `clExtendIndices_restrict` at the top and its children, `cl_child_mem_support`).

Adapted from `Flower/Stage1WVine/GenVB1.lean` (see `COPIED-SHA256SUMS`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.MkUnitsL
open TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory
  WaveTurbulence.VineB
open WaveTurbulence.Flower.Stage1WVine (pairTimes chainTimes)
open WaveTurbulence.VineSpaceK (nodeWeight)

/-- **A slot family with top weights**: the slot kernels and, at every branch `a`, a weight of the four momenta
`![k_a, k_{a0}, k_{a1}, k_{a2}]` (read at a region top as `VineSpaceK.nodeWeight`). -/
structure SlotFamW {w : ℕ} (G : Garden w) (d : ℕ) where
  fs : ReplacementSlot G → (Fin 2 → ℝ) → Mom d → ℂ
  tw : GBranch G.tree → (Fin 4 → Mom d) → ℂ

section Skel
variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J]

/-- The product of the units' top weights at a skeleton decoration. -/
def topW (blk : J → CLBlock S) (Fs : SlotFamW S d) (L : ℝ) (base : Mom d) (x : GNode S.tree → (Fin d → ℤ)) : ℂ :=
  ∏ j, nodeWeight (Fs.tw (blk j).upper) L base (blk j).upper x

open scoped Classical in
/-- The summand of `skelValW` at a skeleton decoration (main's `skelTerm` with the units' top weights). -/
def skelTermW (blk : J → CLBlock S) (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (selSk : GenDecoration S d roots 0 → Prop) (Fs : SlotFamW S d) (κ : GenDecoration S d roots 0) : ℂ :=
  if selSk κ then (epsDec S κ.1 : ℂ) * ∫ τ : GBranch S.tree → ℝ,
      (coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt).indicator
        (fun τ => phaseProd L γ δ S (cosetDecoration S L base κ.1) τ *
          ((∏ s, Fs.fs s (slotTs hS tt τ s) (base + latticePoint L (κ.1 (slotNode hS s)))) *
            topW blk Fs L base κ.1)) τ else 0

/-- **The skeleton value with the units' top weights** (main's `skelVal`). -/
def skelValW (blk : J → CLBlock S) (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (selSk : GenDecoration S d roots 0 → Prop) (Fs : SlotFamW S d) : ℂ :=
  (coupling d L γ δ : ℂ) ^ S.order * S.zeta *
    ∑' κ : GenDecoration S d roots 0, skelTermW blk D hS L γ δ base roots tt layer selSk Fs κ

theorem skelValW_eq (blk : J → CLBlock S) (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (selSk : GenDecoration S d roots 0 → Prop) (Fs : SlotFamW S d) :
    skelValW blk D hS L γ δ base roots tt layer selSk Fs =
      (coupling d L γ δ : ℂ) ^ S.order * S.zeta *
        ∑' κ : GenDecoration S d roots 0, skelTermW blk D hS L γ δ base roots tt layer selSk Fs κ := rfl

end Skel

section Local
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- **The regional star product with an arbitrary slot family** (`VineEstS5C.starProd` with `Fs`). -/
def starProdGW (hG : G.IsPlain) (Fs : SlotFamW G d) (L : ℝ) (base : Mom d)
    (U : Finset (GBranch G.tree)) (a : GBranch G.tree) (top : ℝ) (x : GNode G.tree → (Fin d → ℤ))
    (u : GBranch G.tree → ℝ) : ℂ :=
  (∏ p ∈ clRegionalPairs hG U, Fs.fs (.inl p) (pairTimes hG top u p) (cosetDecoration G L base x (p.firstLeaf hG).toNode)) *
    (∏ v ∈ U.erase a, Fs.fs (.inr v) (chainTimes top u v) (cosetDecoration G L base x v.toNode)) *
    nodeWeight (Fs.tw a) L base a x

/-- `clLocalStarProduct` with an arbitrary slot family. -/
def clLocalStarProductGW (hG : G.IsPlain) (R : CLRegionData G U a b) (Fs : SlotFamW G d)
    (L : ℝ) (base : Mom d) (x : GNode G.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (τ : CLInternalTime R) : ℂ :=
  starProdGW hG Fs L base U a (t 0) x (clLocalClock R t τ)

/-- `clLocalSummand` with an arbitrary slot family. -/
def clLocalSummandGW (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (Fs : SlotFamW G d) (L γ δ : ℝ) (layer : GNode (D.forest hG) → ℕ)
    (base : Mom d) (boundary : Fin 4 → Mom d) (t : Fin 3 → ℝ) (κ : CLLocalDecoration R L base boundary)
    (τ : CLInternalTime R) : ℂ :=
  (clRegionalEpsilon G U (clExtendIndices R κ.1) : ℂ) *
    (clLocalTimeDomain R (fun v => layer (D.coreBranch hG v).toNode) t).indicator
      (fun τ => clRegionalPhase G U L γ δ (cosetDecoration G L base (clExtendIndices R κ.1)) (clLocalClock R t τ) *
        clLocalStarProductGW hG R Fs L base (clExtendIndices R κ.1) t τ) τ

open Classical in
/-- `psiNat` with an arbitrary slot family (a function of the decoration, the exterior clocks and the clock). -/
def psiNatGW (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (Fs : SlotFamW G d) (L γ δ : ℝ) (layer : GNode (D.forest hG) → ℕ)
    (base : Mom d) (x : GNode G.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (u : GBranch G.tree → ℝ) : ℂ :=
  (clRegionalEpsilon G U x : ℂ) *
    (if ClDom R (fun v => layer (D.coreBranch hG v).toNode) t u then
      clRegionalPhase G U L γ δ (cosetDecoration G L base x) u * starProdGW hG Fs L base U a (t 0) x u else 0)

open Classical in
theorem clLocalSummandG_eq_psiNatGW (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (Fs : SlotFamW G d) (L γ δ : ℝ) (layer : GNode (D.forest hG) → ℕ)
    (base : Mom d) (β : Fin 4 → Mom d) (t : Fin 3 → ℝ) (κ : CLLocalDecoration R L base β) (τ : CLInternalTime R) :
    clLocalSummandGW D hG R Fs L γ δ layer base β t κ τ =
      psiNatGW D hG R Fs L γ δ layer base (clExtendIndices R κ.1) t (clLocalClock R t τ) := by
  unfold clLocalSummandGW psiNatGW clLocalStarProductGW
  by_cases hτ : τ ∈ clLocalTimeDomain R (fun v => layer (D.coreBranch hG v).toNode) t
  · rw [Set.indicator_of_mem hτ, if_pos ((mem_clLocalTimeDomain_iff R _ t τ).mp hτ)]
  · rw [Set.indicator_of_notMem hτ, if_neg (fun h => hτ ((mem_clLocalTimeDomain_iff R _ t τ).mpr h))]

/-- Measurability of the slot family in its two clock arguments, at the regional slots of a block `(U, a)` and the
momenta of the base coset (all that the glue needs). -/
def RegMeasW (hG : G.IsPlain) (Fs : SlotFamW G d) (L : ℝ) (base : Mom d)
    (U : Finset (GBranch G.tree)) (a : GBranch G.tree) : Prop :=
  (∀ p ∈ clRegionalPairs hG U, ∀ n : Fin d → ℤ, Measurable fun ts : Fin 2 → ℝ => Fs.fs (.inl p) ts (base + latticePoint L n)) ∧
    ∀ v ∈ U.erase a, ∀ n : Fin d → ℤ, Measurable fun ts : Fin 2 → ℝ => Fs.fs (.inr v) ts (base + latticePoint L n)

theorem measurable_starProdGW (hG : G.IsPlain) (Fs : SlotFamW G d)
    (L : ℝ) (base : Mom d) (U : Finset (GBranch G.tree)) (a : GBranch G.tree) (hFs : RegMeasW hG Fs L base U a)
    (x : GNode G.tree → (Fin d → ℤ)) :
    Measurable fun z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) => starProdGW hG Fs L base U a (z.1 0) x z.2 := by
  classical
  have hu : ∀ v : GBranch G.tree, Measurable fun z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) => z.2 v :=
    fun v => (measurable_pi_apply v).comp measurable_snd
  have ht0 : Measurable fun z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) => z.1 0 :=
    (measurable_pi_apply 0).comp measurable_fst
  have hp : ∀ y : GNode G.tree, Measurable fun z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) => parentClock (z.1 0) z.2 y :=
    fun y => measurable_parentClock_top (α := (Fin 3 → ℝ) × (GBranch G.tree → ℝ)) (fun z => z.1 0) (fun z => z.2)
      ht0 hu y
  unfold starProdGW
  refine (Measurable.mul (Finset.measurable_prod _ fun p _ => ?_) (Finset.measurable_prod _ fun v _ => ?_)).mul
    measurable_const
  · have hv : Measurable fun z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) => pairTimes hG (z.1 0) z.2 p := by
      refine measurable_pi_iff.mpr fun i => ?_
      unfold pairTimes
      by_cases hi : i = 0
      · simp only [hi, if_true]; exact hp _
      · simp only [hi, if_false]; exact hp _
    exact (hFs.1 p ‹_› _).comp hv
  · have hv : Measurable fun z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) => chainTimes (z.1 0) z.2 v := by
      refine measurable_pi_iff.mpr fun i => ?_
      unfold chainTimes
      by_cases hi : i = 0
      · simp only [hi, if_true]; exact hp _
      · simp only [hi, if_false]; exact hu v
    exact (hFs.2 v ‹_› _).comp hv

theorem measurable_psiNatGW (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (Fs : SlotFamW G d) (L γ δ : ℝ) (base : Mom d)
    (hFs : RegMeasW hG Fs L base U a) (layer : GNode (D.forest hG) → ℕ) (x : GNode G.tree → (Fin d → ℤ)) :
    Measurable fun z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) => psiNatGW D hG R Fs L γ δ layer base x z.1 z.2 := by
  classical
  have hu : ∀ v : GBranch G.tree, Measurable fun z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) => z.2 v :=
    fun v => (measurable_pi_apply v).comp measurable_snd
  have hphase : Measurable fun z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) =>
      clRegionalPhase G U L γ δ (cosetDecoration G L base x) z.2 := by
    unfold clRegionalPhase
    exact Finset.measurable_prod _ fun v _ =>
      (continuous_phaseAtom L γ δ (G.sign v.toNode) _).measurable.comp (hu v)
  unfold psiNatGW
  exact measurable_const.mul (Measurable.ite (measurableSet_ClDom R _) (hphase.mul
    (measurable_starProdGW hG Fs L base U a hFs x)) measurable_const)

variable {α : Type*} [MeasurableSpace α]

theorem measurable_clLocalSummandG_jointW (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (Fs : SlotFamW G d) (L γ δ : ℝ) (base : Mom d) (hFs : RegMeasW hG Fs L base U a)
    (layer : GNode (D.forest hG) → ℕ) (β : Fin 4 → Mom d) (κ : CLLocalDecoration R L base β)
    (t : α → Fin 3 → ℝ) (τ : α → CLInternalTime R)
    (ht : ∀ i, Measurable fun x => t x i) (hτ : ∀ v, Measurable fun x => τ x v) :
    Measurable fun x => clLocalSummandGW D hG R Fs L γ δ layer base β (t x) κ (τ x) := by
  have h1 : Measurable fun x => ((t x, fun v => clLocalClock R (t x) (τ x) v) :
      (Fin 3 → ℝ) × (GBranch G.tree → ℝ)) :=
    Measurable.prodMk (measurable_pi_iff.mpr ht)
      (measurable_pi_iff.mpr fun v => measurable_clLocalClock_joint R t τ ht hτ v)
  have h2 := (measurable_psiNatGW D hG R Fs L γ δ base hFs layer (clExtendIndices R κ.1)).comp h1
  have heq : (fun x => clLocalSummandGW D hG R Fs L γ δ layer base β (t x) κ (τ x)) = fun x =>
      psiNatGW D hG R Fs L γ δ layer base (clExtendIndices R κ.1) (t x) (fun v => clLocalClock R (t x) (τ x) v) :=
    funext fun x => clLocalSummandG_eq_psiNatGW D hG R Fs L γ δ layer base β (t x) κ (τ x)
  rw [heq]
  exact h2

end Local

section Glued
variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}

/-- The modulated summand of unit `j` with the slot family `Fs` (`VineB.gUnit` with `Fs`). -/
def gUnitGW (blk : J → CLBlock S) (D : ReconstructionData S) (hS : S.IsPlain)
    (Fs : SlotFamW S d) (L γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ)
    (base : Mom d) (j : J) (lam : ℝ) (β : Fin 4 → Mom d) (t : Fin 3 → ℝ)
    (κ : CLLocalDecoration (regionOf (blk j)) L base β) (τ : CLInternalTime (regionOf (blk j))) : ℂ :=
  lowModC (regionOf (blk j)) lam t τ * clLocalSummandGW D hS (regionOf (blk j)) Fs L γ δ layer base β t κ τ

open scoped Classical in
/-- **The modal slot family** (outer single modes, the given family `Fs` at the regional slots). -/
def modalFnGW (Φ : SpliceShape blk Gsb) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (Fs : SlotFamW S d)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ) : SlotFamW S d :=
  ⟨fun s => if h : ∃ s', Φ.iota hS hSb s' = s then
      (fun ts k => amp (Classical.choose h) k * fsPhase (frq (Classical.choose h)) ts)
    else Fs.fs s, Fs.tw⟩

theorem modalFnGW_tw (Φ : SpliceShape blk Gsb) (hS : S.IsPlain) (hSb : Gsb.IsPlain) (Fs : SlotFamW S d)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ) :
    (modalFnGW Φ hS hSb Fs amp frq).tw = Fs.tw := by
  unfold modalFnGW
  rfl

theorem topW_modalFnGW (Φ : SpliceShape blk Gsb) (hS : S.IsPlain) (hSb : Gsb.IsPlain) (Fs : SlotFamW S d)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (L : ℝ) (base : Mom d)
    (x : GNode S.tree → (Fin d → ℤ)) :
    topW blk (modalFnGW Φ hS hSb Fs amp frq) L base x = topW blk Fs L base x := by
  unfold topW
  rw [modalFnGW_tw]

theorem modalFnG_iotaW (Φ : SpliceShape blk Gsb) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (Fs : SlotFamW S d)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (s' : ReplacementSlot Gsb) :
    (modalFnGW Φ hS hSb Fs amp frq).fs (Φ.iota hS hSb s') = fun ts k => amp s' k * fsPhase (frq s') ts := by
  classical
  unfold modalFnGW
  dsimp only
  have h : ∃ s'', Φ.iota hS hSb s'' = Φ.iota hS hSb s' := ⟨s', rfl⟩
  rw [dif_pos h]
  have := Φ.iota_inj hS hSb (Classical.choose_spec h)
  rw [this]

theorem modalFnG_regW (Φ : SpliceShape blk Gsb) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (Fs : SlotFamW S d)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (j : J)
    {s : ReplacementSlot S} (hs : s ∈ regSlots blk hS j) :
    (modalFnGW Φ hS hSb Fs amp frq).fs s = Fs.fs s := by
  classical
  unfold modalFnGW
  dsimp only
  rw [dif_neg]
  rintro ⟨s', hs'⟩
  have hmem := Φ.iota_mem_outer hS hSb s'
  rw [hs'] at hmem
  exact (Finset.mem_filter.mp hmem).2 j hs

theorem prod_modalFnGW (Φ : SpliceShape blk Gsb) (hd : Disj blk) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (Fs : SlotFamW S d) (amp : ReplacementSlot Gsb → Mom d → ℂ)
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (tt : Fin w → ℝ) (τ : GBranch S.tree → ℝ) (k : GNode S.tree → Mom d) :
    ∏ s, (modalFnGW Φ hS hSb Fs amp frq).fs s (slotTs hS tt τ s) (k (slotNode hS s)) =
      (∏ s', amp s' (k (slotNode hS (Φ.iota hS hSb s')))) *
        (∏ s', fsPhase (frq s') (slotTs hS tt τ (Φ.iota hS hSb s'))) *
        ∏ j, ∏ s ∈ regSlots blk hS j, Fs.fs s (slotTs hS tt τ s) (k (slotNode hS s)) := by
  have h1 := prod_slots (blk := blk) hS hd (fun s => (modalFnGW Φ hS hSb Fs amp frq).fs s (slotTs hS tt τ s)
    (k (slotNode hS s)))
  have h2 := Φ.prod_outer_iota hS hSb (fun s => (modalFnGW Φ hS hSb Fs amp frq).fs s (slotTs hS tt τ s)
    (k (slotNode hS s)))
  rw [h1, h2]
  refine congrArg₂ (· * ·) ?_ (Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun s hs => ?_)
  · rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s' _ => ?_
    rw [modalFnG_iotaW Φ hS hSb Fs amp frq s']
  · rw [modalFnG_regW Φ hS hSb Fs amp frq j hs]

/-- `prod_modalFnGW` with the units' top weights distributed over the units. -/
theorem prod_modalFnG_topW (Φ : SpliceShape blk Gsb) (hd : Disj blk) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (Fs : SlotFamW S d) (amp : ReplacementSlot Gsb → Mom d → ℂ)
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (tt : Fin w → ℝ) (τ : GBranch S.tree → ℝ) (k : GNode S.tree → Mom d)
    (L : ℝ) (base : Mom d) (x : GNode S.tree → (Fin d → ℤ)) :
    (∏ s, (modalFnGW Φ hS hSb Fs amp frq).fs s (slotTs hS tt τ s) (k (slotNode hS s))) *
        topW blk (modalFnGW Φ hS hSb Fs amp frq) L base x =
      (∏ s', amp s' (k (slotNode hS (Φ.iota hS hSb s')))) *
        (∏ s', fsPhase (frq s') (slotTs hS tt τ (Φ.iota hS hSb s'))) *
        ∏ j, ((∏ s ∈ regSlots blk hS j, Fs.fs s (slotTs hS tt τ s) (k (slotNode hS s))) *
          nodeWeight (Fs.tw (blk j).upper) L base (blk j).upper x) := by
  rw [prod_modalFnGW Φ hd hS hSb Fs amp frq tt τ k, Finset.prod_mul_distrib, mul_assoc]
  rfl

/-- **The top weight of a region is local**: at the extension of the restriction of a garden decoration it is the
top weight at the garden decoration (the top and its three children lie in the local support). -/
theorem nodeWeight_clExtendW {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) (W : (Fin 4 → Mom d) → ℂ) (L : ℝ) (base : Mom d)
    (κ : GNode G.tree → (Fin d → ℤ)) :
    nodeWeight W L base a (clExtendIndices R (fun x => κ x.1)) = nodeWeight W L base a κ := by
  have h : ∀ n, n ∈ clLocalSupport R →
      cosetDecoration G L base (clExtendIndices R (fun x => κ x.1)) n = cosetDecoration G L base κ n :=
    fun n hn => by unfold cosetDecoration; rw [clExtendIndices_restrict R κ n hn]
  unfold nodeWeight
  rw [h _ (cl_realization_mem_support R ((branch_mem_clRealizationNodes a).mpr hU.2.1)),
    h _ (cl_child_mem_support hU R hU.2.1 0), h _ (cl_child_mem_support hU R hU.2.1 1),
    h _ (cl_child_mem_support hU R hU.2.1 2)]

/-- The generic analogue of `clLocalStarProduct_restrict`: the regional product at the restriction of a garden
clock and a garden decoration. -/
theorem clLocalStarProductG_restrictW {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hU : G.molecule.IsBlock U a b) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (Fs : SlotFamW G d) (L top : ℝ) (base : Mom d)
    (κ : GNode G.tree → (Fin d → ℤ)) (τ : GBranch G.tree → ℝ) :
    clLocalStarProductGW hG R Fs L base (clExtendIndices R (fun x => κ x.1)) (clExternalTimes R τ) (clRestrictTime R τ) =
    (∏ p ∈ clRegionalPairs hG U, Fs.fs (.inl p) (pairTimes hG top τ p) (cosetDecoration G L base κ (p.firstLeaf hG).toNode)) *
      (∏ v ∈ clInteriorBranches R, Fs.fs (.inr v) (chainTimes top τ v) (cosetDecoration G L base κ v.toNode)) *
      nodeWeight (Fs.tw a) L base a κ := by
  classical
  unfold clLocalStarProductGW starProdGW
  refine congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ ?_) (nodeWeight_clExtendW hU R _ L base κ)
  · apply Finset.prod_congr rfl
    intro p hp
    obtain ⟨hx, hy⟩ := clRegionalPair_realization hG p hp
    have e : pairTimes hG (clExternalTimes R τ 0) (clLocalClock R (clExternalTimes R τ) (clRestrictTime R τ)) p =
        pairTimes hG top τ p := by
      funext i
      unfold pairTimes
      rw [clLocalParentClock_restrict hU R τ top _ hx (Mole.branch_toNode_ne_leaf a _).symm,
        clLocalParentClock_restrict hU R τ top _ hy (Mole.branch_toNode_ne_leaf a _).symm]
    rw [e]
    unfold cosetDecoration
    rw [clExtendIndices_restrict R κ _ (cl_realization_mem_support R hx)]
  · apply Finset.prod_congr rfl
    intro v hv
    have hv' := Finset.mem_erase.mp hv
    have hn : v.toNode ≠ a.toNode := fun he => hv'.1 (Subtype.ext (congrArg (fun x : GNode G.tree => x.1) he))
    have hx := (branch_mem_clRealizationNodes v).mpr hv'.2
    have e : chainTimes (clExternalTimes R τ 0) (clLocalClock R (clExternalTimes R τ) (clRestrictTime R τ)) v =
        chainTimes top τ v := by
      funext i
      unfold chainTimes
      rw [clLocalParentClock_restrict hU R τ top _ hx hn, clLocalClock_restrict_region R τ v hv'.2]
    rw [e]
    unfold cosetDecoration
    rw [clExtendIndices_restrict R κ _ (cl_realization_mem_support R hx)]

/-- **The regional slots of unit `j`** are the generic regional product (cf. `VineB.regional_glue`). -/
theorem regional_glueGW (Φ : SpliceShape blk Gsb) (hd : Disj blk) (hS : S.IsPlain) {L : ℝ} (hL : L ≠ 0)
    (base : Mom d) (Fs : SlotFamW S d) (tt : Fin w → ℝ)
    {roots : Fin w → (Fin d → ℤ)} (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j))
    (τ' : GBranch Gsb.tree → ℝ) (τs : ∀ j, CLInternalTime (regionOf (blk j))) (j : J) :
    (∏ s ∈ regSlots blk hS j, Fs.fs s (slotTs hS tt (Φ.glueTime hd τ' τs) s)
        (base + latticePoint L (Φ.glueFun z.1 (fun j => (κs j).1) (slotNode hS s)))) *
      nodeWeight (Fs.tw (blk j).upper) L base (blk j).upper (Φ.glueFun z.1 (fun j => (κs j).1)) =
      clLocalStarProductGW hS (regionOf (blk j)) Fs L base (clExtendIndices (regionOf (blk j)) (κs j).1)
        (Φ.clocks τ' j) (τs j) := by
  set τ := Φ.glueTime hd τ' τs
  set κ := Φ.glueFun z.1 (fun j => (κs j).1)
  rw [Φ.locDec_eq hd hL base z κs j, Φ.clocks_eq_external hd τ' τs j, ← Φ.restrict_glueTime hd τ' τs j,
    clLocalStarProductG_restrictW (blk j).isBlock hS (regionOf (blk j)) Fs L 0 base, prod_regSlots]
  refine congrArg₂ (· * ·) ?_ rfl
  congr 1
  · refine Finset.prod_congr rfl fun p hp => ?_
    have hf : Mole.IsInternalLeaf S (blk j).atoms (p.firstLeaf hS) := by
      classical
      exact (Finset.mem_filter.mp hp).2
    have hs := (second_internal_iff hS (blk j).atoms p).mpr hf
    obtain ⟨_, hn1, _, _⟩ := hf
    obtain ⟨_, hn2, _, _⟩ := hs
    have e : slotTs hS tt τ (.inl p) = pairTimes hS 0 τ p := by
      funext i
      unfold slotTs pairTimes
      by_cases hi : i = 0
      · simp only [hi, if_true, argSrc]
        rw [← parentClockWith_eq_clockOf, SpliceShape.parentClockWith_eq_parentClock tt 0 τ _ hn1]
      · simp only [hi, if_false, argSrc]
        rw [← parentClockWith_eq_clockOf, SpliceShape.parentClockWith_eq_parentClock tt 0 τ _ hn2]
    rw [e]
    rfl
  · refine Finset.prod_congr rfl fun v hv => ?_
    have hvm := VineB.mem_inter.mp hv
    obtain ⟨hn, -⟩ := real_parent (blk j) ((branch_real_iff _ _).mpr hvm.1)
      (fun he => hvm.2 (Subtype.ext (congrArg (fun x : GNode S.tree => x.1) he)))
    have e : slotTs hS tt τ (.inr v) = chainTimes 0 τ v := by
      funext i
      unfold slotTs chainTimes
      by_cases hi : i = 0
      · simp only [hi, if_true, argSrc]
        rw [← parentClockWith_eq_clockOf, SpliceShape.parentClockWith_eq_parentClock tt 0 τ _ hn]
      · simp only [hi, if_false, argSrc]
        rfl
    rw [e]
    rfl

/-- The unit factor of the factorized integrand (`VineB.SpliceShape.unitInt` with `Fs`). -/
def unitIntGW (Φ : SpliceShape blk Gsb) (D : ReconstructionData S) (hS : S.IsPlain)
    (Fs : SlotFamW S d) (L γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ)
    (base : Mom d) {roots : Fin w → (Fin d → ℤ)} (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (hSb : Gsb.IsPlain)
    (z : GenDecoration Gsb d roots 0) (τ' : GBranch Gsb.tree → ℝ) (j : J)
    (κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j))
    (τ : CLInternalTime (regionOf (blk j))) : ℂ :=
  recExp L γ δ (S.sign (blk j).upper.toNode) (Φ.clocks τ' j 0) (Φ.bdry L base z.1 j) *
    gUnitGW blk D hS Fs L γ δ layer base j (modLam frq (Φ.route hS hSb) j : ℝ) (Φ.bdry L base z.1 j)
      (Φ.clocks τ' j) κ τ

theorem measurable_unitIntGW (Φ : SpliceShape blk Gsb) (D : ReconstructionData S) (hS : S.IsPlain)
    (Fs : SlotFamW S d) (L γ δ : ℝ)
    (layer : GNode (D.forest hS) → ℕ) (base : Mom d) {roots : Fin w → (Fin d → ℤ)}
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (hSb : Gsb.IsPlain) (z : GenDecoration Gsb d roots 0) (j : J)
    (hFs : RegMeasW hS Fs L base (blk j).atoms (blk j).upper)
    (κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    Measurable fun p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))) =>
      unitIntGW Φ D hS Fs L γ δ layer base frq hSb z p.1 j κ (p.2 j) := by
  have hcl : ∀ i, Measurable fun p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))) =>
      Φ.clocks p.1 j i := fun i => (Φ.measurable_clocks j i).comp measurable_fst
  have hτ : ∀ v, Measurable fun p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))) =>
      p.2 j v := fun v => (measurable_pi_apply v).comp ((measurable_pi_apply j).comp measurable_snd)
  have h1 := measurable_clLocalSummandG_jointW D hS (regionOf (blk j)) Fs L γ δ base hFs layer
    (Φ.bdry L base z.1 j) κ (fun p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))) =>
      Φ.clocks p.1 j) (fun p => p.2 j) hcl hτ
  have h2 : Measurable fun p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))) =>
      lowModC (regionOf (blk j)) (modLam frq (Φ.route hS hSb) j : ℝ) (Φ.clocks p.1 j) (p.2 j) := by
    have hb := measurable_clLocalClock_joint (regionOf (blk j)) (fun p : (GBranch Gsb.tree → ℝ) ×
      (∀ j, CLInternalTime (regionOf (blk j))) => Φ.clocks p.1 j) (fun p => p.2 j) hcl hτ (blk j).lower
    unfold lowModC
    exact Measurable.cexp ((Complex.measurable_ofReal.comp (hb.const_mul (Real.pi *
      (modLam frq (Φ.route hS hSb) j : ℝ)))).mul_const Complex.I)
  have h3 : Measurable fun p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))) =>
      recExp L γ δ (S.sign (blk j).upper.toNode) (Φ.clocks p.1 j 0) (Φ.bdry L base z.1 j) := by
    unfold recExp
    exact Measurable.cexp ((Complex.measurable_ofReal.comp
      (((hcl 0).const_mul (-(Real.pi * δ * L ^ (2 * γ)))).mul_const
        (boundaryEnergyFromMomenta (S.sign (blk j).upper.toNode) (Φ.bdry L base z.1 j 0) (Φ.bdry L base z.1 j 1)
          (Φ.bdry L base z.1 j 2) (Φ.bdry L base z.1 j 3)))).mul_const Complex.I)
  exact h3.mul (h2.mul h1)

end Glued

end WaveTurbulence.Flower.MkUnitsL
