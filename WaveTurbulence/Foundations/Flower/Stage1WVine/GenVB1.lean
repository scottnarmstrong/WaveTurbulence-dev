/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Vine.B.Export
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.AbsBase2

/-! # STAGE1W-VINE (T3): VINE-B♯ with an arbitrary regional slot family — definitions and the pointwise glue

Main's VINE-B♯ (`Vine/B`) proves the per-mode identity `skelVal(modalFn) = outerValM(…, unitKernelM)` for the native
leafwise slot kernels `slotFn` at the regional slots of the units.  The frontier-weighted Stage-1 gate needs the same
identity with the *weighted* regional kernels.  This file copy-generalizes the kernel-specific part of `Vine/B`
(`PointB.regional_glue`, `Pointwise`, `Meas`) to an arbitrary slot family `Fs`; the structural part of `Vine/B`
(shapes, decoration and time glueing, routing, `modes_glue`, `eps_glue`, `phase_glue`, `dom_iff`) is reused by import.
The lower-joint clock routing (erratum E26 / R58: `route`, `modLam`, `lowModC` at the lower joint) is main's, unchanged.

* `starProdG`, `clLocalStarProductG`, `clLocalSummandG`, `gUnitG`: main's `starProd`, `clLocalStarProduct`,
  `clLocalSummand`, `gUnit` with `Fs` at the regional pairs and interior branches.
* `modalFnG`: single modes at the outer slots, `Fs` at the regional slots.
* `regional_glueG`, `integrand_glueG`: the pointwise factorization of the glued integrand.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.Stage1WVine
open TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory
  WaveTurbulence.VineB

section Local
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- The two clock arguments of a regional couple slot, read from a clock `u` (cf. `clLocalStarProduct`). -/
def pairTimes (hG : G.IsPlain) (top : ℝ) (u : GBranch G.tree → ℝ) (p : SourcePair G) : Fin 2 → ℝ :=
  fun i => if i = 0 then parentClock top u (p.firstLeaf hG).toNode else parentClock top u (p.secondLeaf hG).toNode

/-- The two clock arguments of a regional chain slot. -/
def chainTimes (top : ℝ) (u : GBranch G.tree → ℝ) (v : GBranch G.tree) : Fin 2 → ℝ :=
  fun i => if i = 0 then parentClock top u v.toNode else u v

/-- **The regional star product with an arbitrary slot family** (`VineEstS5C.starProd` with `Fs`). -/
def starProdG (hG : G.IsPlain) (Fs : ReplacementSlot G → (Fin 2 → ℝ) → Mom d → ℂ) (L : ℝ) (base : Mom d)
    (U : Finset (GBranch G.tree)) (a : GBranch G.tree) (top : ℝ) (x : GNode G.tree → (Fin d → ℤ))
    (u : GBranch G.tree → ℝ) : ℂ :=
  (∏ p ∈ clRegionalPairs hG U, Fs (.inl p) (pairTimes hG top u p) (cosetDecoration G L base x (p.firstLeaf hG).toNode)) *
    ∏ v ∈ U.erase a, Fs (.inr v) (chainTimes top u v) (cosetDecoration G L base x v.toNode)

/-- `clLocalStarProduct` with an arbitrary slot family. -/
def clLocalStarProductG (hG : G.IsPlain) (R : CLRegionData G U a b) (Fs : ReplacementSlot G → (Fin 2 → ℝ) → Mom d → ℂ)
    (L : ℝ) (base : Mom d) (x : GNode G.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (τ : CLInternalTime R) : ℂ :=
  starProdG hG Fs L base U a (t 0) x (clLocalClock R t τ)

/-- `clLocalSummand` with an arbitrary slot family. -/
def clLocalSummandG (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (Fs : ReplacementSlot G → (Fin 2 → ℝ) → Mom d → ℂ) (L γ δ : ℝ) (layer : GNode (D.forest hG) → ℕ)
    (base : Mom d) (boundary : Fin 4 → Mom d) (t : Fin 3 → ℝ) (κ : CLLocalDecoration R L base boundary)
    (τ : CLInternalTime R) : ℂ :=
  (clRegionalEpsilon G U (clExtendIndices R κ.1) : ℂ) *
    (clLocalTimeDomain R (fun v => layer (D.coreBranch hG v).toNode) t).indicator
      (fun τ => clRegionalPhase G U L γ δ (cosetDecoration G L base (clExtendIndices R κ.1)) (clLocalClock R t τ) *
        clLocalStarProductG hG R Fs L base (clExtendIndices R κ.1) t τ) τ

open Classical in
/-- `psiNat` with an arbitrary slot family (a function of the decoration, the exterior clocks and the clock). -/
def psiNatG (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (Fs : ReplacementSlot G → (Fin 2 → ℝ) → Mom d → ℂ) (L γ δ : ℝ) (layer : GNode (D.forest hG) → ℕ)
    (base : Mom d) (x : GNode G.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (u : GBranch G.tree → ℝ) : ℂ :=
  (clRegionalEpsilon G U x : ℂ) *
    (if ClDom R (fun v => layer (D.coreBranch hG v).toNode) t u then
      clRegionalPhase G U L γ δ (cosetDecoration G L base x) u * starProdG hG Fs L base U a (t 0) x u else 0)

open Classical in
theorem clLocalSummandG_eq_psiNatG (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (Fs : ReplacementSlot G → (Fin 2 → ℝ) → Mom d → ℂ) (L γ δ : ℝ) (layer : GNode (D.forest hG) → ℕ)
    (base : Mom d) (β : Fin 4 → Mom d) (t : Fin 3 → ℝ) (κ : CLLocalDecoration R L base β) (τ : CLInternalTime R) :
    clLocalSummandG D hG R Fs L γ δ layer base β t κ τ =
      psiNatG D hG R Fs L γ δ layer base (clExtendIndices R κ.1) t (clLocalClock R t τ) := by
  unfold clLocalSummandG psiNatG clLocalStarProductG
  by_cases hτ : τ ∈ clLocalTimeDomain R (fun v => layer (D.coreBranch hG v).toNode) t
  · rw [Set.indicator_of_mem hτ, if_pos ((mem_clLocalTimeDomain_iff R _ t τ).mp hτ)]
  · rw [Set.indicator_of_notMem hτ, if_neg (fun h => hτ ((mem_clLocalTimeDomain_iff R _ t τ).mpr h))]

/-- Measurability of the slot family in its two clock arguments, at the regional slots of a block `(U, a)` and the
momenta of the base coset (all that the glue needs). -/
def RegMeas (hG : G.IsPlain) (Fs : ReplacementSlot G → (Fin 2 → ℝ) → Mom d → ℂ) (L : ℝ) (base : Mom d)
    (U : Finset (GBranch G.tree)) (a : GBranch G.tree) : Prop :=
  (∀ p ∈ clRegionalPairs hG U, ∀ n : Fin d → ℤ, Measurable fun ts : Fin 2 → ℝ => Fs (.inl p) ts (base + latticePoint L n)) ∧
    ∀ v ∈ U.erase a, ∀ n : Fin d → ℤ, Measurable fun ts : Fin 2 → ℝ => Fs (.inr v) ts (base + latticePoint L n)

theorem measurable_starProdG (hG : G.IsPlain) (Fs : ReplacementSlot G → (Fin 2 → ℝ) → Mom d → ℂ)
    (L : ℝ) (base : Mom d) (U : Finset (GBranch G.tree)) (a : GBranch G.tree) (hFs : RegMeas hG Fs L base U a)
    (x : GNode G.tree → (Fin d → ℤ)) :
    Measurable fun z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) => starProdG hG Fs L base U a (z.1 0) x z.2 := by
  classical
  have hu : ∀ v : GBranch G.tree, Measurable fun z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) => z.2 v :=
    fun v => (measurable_pi_apply v).comp measurable_snd
  have ht0 : Measurable fun z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) => z.1 0 :=
    (measurable_pi_apply 0).comp measurable_fst
  have hp : ∀ y : GNode G.tree, Measurable fun z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) => parentClock (z.1 0) z.2 y :=
    fun y => measurable_parentClock_top (α := (Fin 3 → ℝ) × (GBranch G.tree → ℝ)) (fun z => z.1 0) (fun z => z.2)
      ht0 hu y
  unfold starProdG
  refine Measurable.mul (Finset.measurable_prod _ fun p _ => ?_) (Finset.measurable_prod _ fun v _ => ?_)
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

theorem measurable_psiNatG (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (Fs : ReplacementSlot G → (Fin 2 → ℝ) → Mom d → ℂ) (L γ δ : ℝ) (base : Mom d)
    (hFs : RegMeas hG Fs L base U a) (layer : GNode (D.forest hG) → ℕ) (x : GNode G.tree → (Fin d → ℤ)) :
    Measurable fun z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) => psiNatG D hG R Fs L γ δ layer base x z.1 z.2 := by
  classical
  have hu : ∀ v : GBranch G.tree, Measurable fun z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) => z.2 v :=
    fun v => (measurable_pi_apply v).comp measurable_snd
  have hphase : Measurable fun z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) =>
      clRegionalPhase G U L γ δ (cosetDecoration G L base x) z.2 := by
    unfold clRegionalPhase
    exact Finset.measurable_prod _ fun v _ =>
      (continuous_phaseAtom L γ δ (G.sign v.toNode) _).measurable.comp (hu v)
  unfold psiNatG
  exact measurable_const.mul (Measurable.ite (measurableSet_ClDom R _) (hphase.mul
    (measurable_starProdG hG Fs L base U a hFs x)) measurable_const)

variable {α : Type*} [MeasurableSpace α]

theorem measurable_clLocalSummandG_joint (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (Fs : ReplacementSlot G → (Fin 2 → ℝ) → Mom d → ℂ) (L γ δ : ℝ) (base : Mom d) (hFs : RegMeas hG Fs L base U a)
    (layer : GNode (D.forest hG) → ℕ) (β : Fin 4 → Mom d) (κ : CLLocalDecoration R L base β)
    (t : α → Fin 3 → ℝ) (τ : α → CLInternalTime R)
    (ht : ∀ i, Measurable fun x => t x i) (hτ : ∀ v, Measurable fun x => τ x v) :
    Measurable fun x => clLocalSummandG D hG R Fs L γ δ layer base β (t x) κ (τ x) := by
  have h1 : Measurable fun x => ((t x, fun v => clLocalClock R (t x) (τ x) v) :
      (Fin 3 → ℝ) × (GBranch G.tree → ℝ)) :=
    Measurable.prodMk (measurable_pi_iff.mpr ht)
      (measurable_pi_iff.mpr fun v => measurable_clLocalClock_joint R t τ ht hτ v)
  have h2 := (measurable_psiNatG D hG R Fs L γ δ base hFs layer (clExtendIndices R κ.1)).comp h1
  have heq : (fun x => clLocalSummandG D hG R Fs L γ δ layer base β (t x) κ (τ x)) = fun x =>
      psiNatG D hG R Fs L γ δ layer base (clExtendIndices R κ.1) (t x) (fun v => clLocalClock R (t x) (τ x) v) :=
    funext fun x => clLocalSummandG_eq_psiNatG D hG R Fs L γ δ layer base β (t x) κ (τ x)
  rw [heq]
  exact h2

end Local

section Glued
variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}

/-- The modulated summand of unit `j` with the slot family `Fs` (`VineB.gUnit` with `Fs`). -/
def gUnitG (blk : J → CLBlock S) (D : ReconstructionData S) (hS : S.IsPlain)
    (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) (L γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ)
    (base : Mom d) (j : J) (lam : ℝ) (β : Fin 4 → Mom d) (t : Fin 3 → ℝ)
    (κ : CLLocalDecoration (regionOf (blk j)) L base β) (τ : CLInternalTime (regionOf (blk j))) : ℂ :=
  lowModC (regionOf (blk j)) lam t τ * clLocalSummandG D hS (regionOf (blk j)) Fs L γ δ layer base β t κ τ

open scoped Classical in
/-- **The modal slot family** (outer single modes, the given family `Fs` at the regional slots). -/
def modalFnG (Φ : SpliceShape blk Gsb) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ) :
    ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ :=
  fun s => if h : ∃ s', Φ.iota hS hSb s' = s then
      (fun ts k => amp (Classical.choose h) k * fsPhase (frq (Classical.choose h)) ts)
    else Fs s

theorem modalFnG_iota (Φ : SpliceShape blk Gsb) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (s' : ReplacementSlot Gsb) :
    modalFnG Φ hS hSb Fs amp frq (Φ.iota hS hSb s') = fun ts k => amp s' k * fsPhase (frq s') ts := by
  classical
  unfold modalFnG
  have h : ∃ s'', Φ.iota hS hSb s'' = Φ.iota hS hSb s' := ⟨s', rfl⟩
  rw [dif_pos h]
  have := Φ.iota_inj hS hSb (Classical.choose_spec h)
  rw [this]

theorem modalFnG_reg (Φ : SpliceShape blk Gsb) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (j : J)
    {s : ReplacementSlot S} (hs : s ∈ regSlots blk hS j) :
    modalFnG Φ hS hSb Fs amp frq s = Fs s := by
  classical
  unfold modalFnG
  rw [dif_neg]
  rintro ⟨s', hs'⟩
  have hmem := Φ.iota_mem_outer hS hSb s'
  rw [hs'] at hmem
  exact (Finset.mem_filter.mp hmem).2 j hs

theorem prod_modalFnG (Φ : SpliceShape blk Gsb) (hd : Disj blk) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) (amp : ReplacementSlot Gsb → Mom d → ℂ)
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (tt : Fin w → ℝ) (τ : GBranch S.tree → ℝ) (k : GNode S.tree → Mom d) :
    ∏ s, modalFnG Φ hS hSb Fs amp frq s (slotTs hS tt τ s) (k (slotNode hS s)) =
      (∏ s', amp s' (k (slotNode hS (Φ.iota hS hSb s')))) *
        (∏ s', fsPhase (frq s') (slotTs hS tt τ (Φ.iota hS hSb s'))) *
        ∏ j, ∏ s ∈ regSlots blk hS j, Fs s (slotTs hS tt τ s) (k (slotNode hS s)) := by
  have h1 := prod_slots (blk := blk) hS hd (fun s => modalFnG Φ hS hSb Fs amp frq s (slotTs hS tt τ s)
    (k (slotNode hS s)))
  have h2 := Φ.prod_outer_iota hS hSb (fun s => modalFnG Φ hS hSb Fs amp frq s (slotTs hS tt τ s)
    (k (slotNode hS s)))
  rw [h1, h2]
  refine congrArg₂ (· * ·) ?_ (Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun s hs => ?_)
  · rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s' _ => ?_
    rw [modalFnG_iota Φ hS hSb Fs amp frq s']
  · rw [modalFnG_reg Φ hS hSb Fs amp frq j hs]

/-- The generic analogue of `clLocalStarProduct_restrict`: the regional product at the restriction of a garden
clock and a garden decoration. -/
theorem clLocalStarProductG_restrict {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hU : G.molecule.IsBlock U a b) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (Fs : ReplacementSlot G → (Fin 2 → ℝ) → Mom d → ℂ) (L top : ℝ) (base : Mom d)
    (κ : GNode G.tree → (Fin d → ℤ)) (τ : GBranch G.tree → ℝ) :
    clLocalStarProductG hG R Fs L base (clExtendIndices R (fun x => κ x.1)) (clExternalTimes R τ) (clRestrictTime R τ) =
    (∏ p ∈ clRegionalPairs hG U, Fs (.inl p) (pairTimes hG top τ p) (cosetDecoration G L base κ (p.firstLeaf hG).toNode)) *
      ∏ v ∈ clInteriorBranches R, Fs (.inr v) (chainTimes top τ v) (cosetDecoration G L base κ v.toNode) := by
  classical
  unfold clLocalStarProductG starProdG
  apply congrArg₂ (· * ·)
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
theorem regional_glueG (Φ : SpliceShape blk Gsb) (hd : Disj blk) (hS : S.IsPlain) {L : ℝ} (hL : L ≠ 0)
    (base : Mom d) (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) (tt : Fin w → ℝ)
    {roots : Fin w → (Fin d → ℤ)} (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j))
    (τ' : GBranch Gsb.tree → ℝ) (τs : ∀ j, CLInternalTime (regionOf (blk j))) (j : J) :
    ∏ s ∈ regSlots blk hS j, Fs s (slotTs hS tt (Φ.glueTime hd τ' τs) s)
        (base + latticePoint L (Φ.glueFun z.1 (fun j => (κs j).1) (slotNode hS s))) =
      clLocalStarProductG hS (regionOf (blk j)) Fs L base (clExtendIndices (regionOf (blk j)) (κs j).1)
        (Φ.clocks τ' j) (τs j) := by
  set τ := Φ.glueTime hd τ' τs
  set κ := Φ.glueFun z.1 (fun j => (κs j).1)
  rw [Φ.locDec_eq hd hL base z κs j, Φ.clocks_eq_external hd τ' τs j, ← Φ.restrict_glueTime hd τ' τs j,
    clLocalStarProductG_restrict (blk j).isBlock hS (regionOf (blk j)) Fs L 0 base, prod_regSlots]
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
def unitIntG (Φ : SpliceShape blk Gsb) (D : ReconstructionData S) (hS : S.IsPlain)
    (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) (L γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ)
    (base : Mom d) {roots : Fin w → (Fin d → ℤ)} (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (hSb : Gsb.IsPlain)
    (z : GenDecoration Gsb d roots 0) (τ' : GBranch Gsb.tree → ℝ) (j : J)
    (κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j))
    (τ : CLInternalTime (regionOf (blk j))) : ℂ :=
  recExp L γ δ (S.sign (blk j).upper.toNode) (Φ.clocks τ' j 0) (Φ.bdry L base z.1 j) *
    gUnitG blk D hS Fs L γ δ layer base j (modLam frq (Φ.route hS hSb) j : ℝ) (Φ.bdry L base z.1 j)
      (Φ.clocks τ' j) κ τ

/-- **The pointwise factorization** (cf. `VineB.SpliceShape.integrand_glue`). -/
theorem integrand_glueG (Φ : SpliceShape blk Gsb) (hd : Disj blk) (hS : S.IsPlain) (hSb : Gsb.IsPlain) {L : ℝ}
    (hL : L ≠ 0) (γ δ : ℝ) (base : Mom d) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j))
    (τ' : GBranch Gsb.tree → ℝ) (τs : ∀ j, CLInternalTime (regionOf (blk j))) :
    (epsDec S (Φ.glueDec hS hd hL base z κs).1 : ℂ) *
      (coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt).indicator
        (fun τ => phaseProd L γ δ S (cosetDecoration S L base (Φ.glueDec hS hd hL base z κs).1) τ *
          ∏ s, modalFnG Φ hS hSb Fs amp frq s (slotTs hS tt τ s)
            (base + latticePoint L ((Φ.glueDec hS hd hL base z κs).1 (slotNode hS s))))
        (Φ.glueTime hd τ' τs) =
    (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) *
      (openSb Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt).indicator
        (fun τ' => Φ.sbInt hS hSb L γ δ base tt amp frq z τ' *
          ∏ j, unitIntG Φ D hS Fs L γ δ layer base frq hSb z τ' j (κs j) (τs j)) τ' := by
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = Φ.glueDec hS hd hL base z κs := ⟨_, rfl⟩
  obtain ⟨τ, hτdef⟩ : ∃ τ, τ = Φ.glueTime hd τ' τs := ⟨_, rfl⟩
  rw [← hκ, ← hτdef]
  by_cases hτ : τ ∈ coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt
  · subst hτdef
    obtain ⟨hsb, hloc⟩ := (Φ.dom_iff hd _ tt τ' τs).mp hτ
    rw [Set.indicator_of_mem hτ, Set.indicator_of_mem hsb]
    have hκv : κ.1 = Φ.glueFun z.1 (fun j => (κs j).1) := by rw [hκ]; exact Φ.glueDec_val hS hd hL base z κs
    rw [hκv]
    rw [prod_modalFnG Φ hd hS hSb Fs amp frq tt (Φ.glueTime hd τ' τs)
      (fun x => base + latticePoint L (Φ.glueFun z.1 (fun j => (κs j).1) x))]
    rw [Φ.amp_glue hS hSb L base z.1 (fun j => (κs j).1) amp, Φ.modes_glue hd hS hSb tt frq τ' τs]
    have hreg := Finset.prod_congr (s₁ := (Finset.univ : Finset J)) rfl
      (fun j _ => regional_glueG Φ hd hS hL base Fs tt z κs τ' τs j)
    rw [hreg]
    rw [Φ.eps_glue hd hL base z κs, Φ.phase_glue hd hL γ δ base z κs τ' τs]
    unfold SpliceShape.sbInt unitIntG gUnitG clLocalSummandG
    simp only [Set.indicator_of_mem (hloc _), Finset.prod_mul_distrib, Complex.ofReal_mul, Complex.ofReal_prod]
    ring
  · rw [Set.indicator_of_notMem hτ, mul_zero]
    rw [hτdef, (Φ.dom_iff hd _ tt τ' τs).not] at hτ
    by_cases hsb : τ' ∈ openSb Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt
    · have : ∃ j, τs j ∉ clLocalTimeDomain (regionOf (blk j)) (fun b => layer (D.coreBranch hS b).toNode)
          (Φ.clocks τ' j) := by
        by_contra hc
        push Not at hc
        exact hτ ⟨hsb, hc⟩
      obtain ⟨j, hj⟩ := this
      rw [Set.indicator_of_mem hsb]
      have h0 : unitIntG Φ D hS Fs L γ δ layer base frq hSb z τ' j (κs j) (τs j) = 0 := by
        unfold unitIntG gUnitG clLocalSummandG
        rw [Set.indicator_of_notMem hj]
        simp
      rw [Finset.prod_eq_zero (Finset.mem_univ j) h0]
      simp
    · rw [Set.indicator_of_notMem hsb]
      simp

theorem measurable_unitIntG (Φ : SpliceShape blk Gsb) (D : ReconstructionData S) (hS : S.IsPlain)
    (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) (L γ δ : ℝ)
    (layer : GNode (D.forest hS) → ℕ) (base : Mom d) {roots : Fin w → (Fin d → ℤ)}
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (hSb : Gsb.IsPlain) (z : GenDecoration Gsb d roots 0) (j : J)
    (hFs : RegMeas hS Fs L base (blk j).atoms (blk j).upper)
    (κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    Measurable fun p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))) =>
      unitIntG Φ D hS Fs L γ δ layer base frq hSb z p.1 j κ (p.2 j) := by
  have hcl : ∀ i, Measurable fun p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))) =>
      Φ.clocks p.1 j i := fun i => (Φ.measurable_clocks j i).comp measurable_fst
  have hτ : ∀ v, Measurable fun p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))) =>
      p.2 j v := fun v => (measurable_pi_apply v).comp ((measurable_pi_apply j).comp measurable_snd)
  have h1 := measurable_clLocalSummandG_joint D hS (regionOf (blk j)) Fs L γ δ base hFs layer
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

end WaveTurbulence.Flower.Stage1WVine
