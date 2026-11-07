/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.C.VCExport

/-! # VINE-C with the canonical per-unit data (PLAN-VINE "Canonical per-unit data")

For the representative state (skeleton `S`, data `D`, layering) and units `j : J` with chain assemblies
`B j : CLChainAssembly S (R j) (n j)` on pairwise disjoint atom sets `U j`:

* `unitsFamily`: the core family of all units, indexed by `Σ j, (assemblySourceFamily (B j)).CoreIndex` (the union of the
  core families of the units' pieces); `unitsSplit` its splitting into the units; `unitsStart` the τ-class start state
  (the representative with this family); `unitsRegion j` the chain region of the unit `j` (V5's `chainStart (B j)`).
* `unitsSplit_st`, `unitsSplit_reg`: the restricted state and region of the unit `j` are LITERALLY V5's
  `startState (B j) D hS layer hLayer` and `chainStart (B j)` (`rfl`), so the unit factors of the class product are
  `canonFinsetK p kind (startState (B j) D hS layer hLayer) (chainStart (B j))`, the objects of VINEEST.
* `classProd_bijOn_units`, `sum_tauClass_vineB_units`: the class product and the vine-case class sum in these terms.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineC
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.Reg.Skeleton
  WaveTurbulence.Represents WaveTurbulence.RegRed WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 TTree MeasureTheory

variable {w : ℕ} {S : Garden w} {J : Type*} {U : J → Finset (GBranch S.tree)} {a b : J → GBranch S.tree}
  {R : ∀ j, CLRegionData S (U j) (a j) (b j)} {n : J → ℕ}

/-- The member index type of the units. -/
abbrev UnitsIndex (B : ∀ j, CLChainAssembly S (R j) (n j)) := Σ j, (assemblySourceFamily (B j)).CoreIndex

theorem unitsAtoms_sub (B : ∀ j, CLChainAssembly S (R j) (n j)) (j : J) (k : (assemblySourceFamily (B j)).CoreIndex) :
    (assemblySourceFamily (B j)).coreFamily.atoms k ⊆ U j :=
  (chainStart (B j)).atoms_sub k

/-- **The core family of all units.** -/
@[expose] noncomputable def unitsFamily (B : ∀ j, CLChainAssembly S (R j) (n j))
    (hdisj : ∀ j j', j ≠ j' → Disjoint (U j) (U j')) : CoreFamily S (UnitsIndex B) where
  kind x := (assemblySourceFamily (B x.1)).coreFamily.kind x.2
  atoms x := (assemblySourceFamily (B x.1)).coreFamily.atoms x.2
  upper x := (assemblySourceFamily (B x.1)).coreFamily.upper x.2
  placement x := (assemblySourceFamily (B x.1)).coreFamily.placement x.2
  core x := (assemblySourceFamily (B x.1)).coreFamily.core x.2
  designated x := (assemblySourceFamily (B x.1)).coreFamily.designated x.2
  separated x y hxy := by
    obtain ⟨j, k⟩ := x
    obtain ⟨j', k'⟩ := y
    by_cases hj : j = j'
    · subst hj
      exact (assemblySourceFamily (B j)).coreFamily.separated k k' (fun h => hxy (h ▸ rfl))
    · intro v hv hv' _ _ _
      exact absurd (Finset.disjoint_left.mp (hdisj j j' hj) (unitsAtoms_sub B j k hv) (unitsAtoms_sub B j' k' hv'))
        not_false

/-- The splitting of the members into the units. -/
@[expose] def unitsSplit (B : ∀ j, CLChainAssembly S (R j) (n j)) :
    UnitSplit (UnitsIndex B) J (fun j => (assemblySourceFamily (B j)).CoreIndex) where
  unitOf := Sigma.fst
  emb j k := ⟨j, k⟩
  inj _ := fun _ _ h => eq_of_heq (Sigma.mk.inj h).2
  unitOf_emb _ _ := rfl
  surj x := ⟨x.2, rfl⟩

/-- **The τ-class start state**: the representative `(S, D, layer)` with the family of all units. -/
@[expose] noncomputable def unitsStart (B : ∀ j, CLChainAssembly S (R j) (n j))
    (hdisj : ∀ j j', j ≠ j' → Disjoint (U j) (U j')) (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) : FamilyReconstruction w (UnitsIndex B) where
  skeleton := S
  family := unitsFamily B hdisj
  plain := hS
  data := D
  layered := layeredReconstruction D hS layer hLayer
  decodes := D.garden_decodes hS

/-- **The chain region of the unit `j`** in the τ-class start state (V5's `chainStart (B j)`, disjoint from the other
units). -/
@[expose] noncomputable def unitsRegion (B : ∀ j, CLChainAssembly S (R j) (n j))
    (hdisj : ∀ j j', j ≠ j' → Disjoint (U j) (U j')) (j : J) :
    UnitAt S (unitsFamily B hdisj) ((unitsSplit B).Q j) where
  blk := ⟨U j, a j, b j, (B j).isBlock⟩
  cl := (R j).parentPattern
  atoms_sub x hx := by
    obtain ⟨j', k⟩ := x
    replace hx : j' = j := hx
    subst hx
    exact unitsAtoms_sub B j' k
  lower_ne x hx := by
    obtain ⟨j', k⟩ := x
    replace hx : j' = j := hx
    subst hx
    exact (chainStart (B j')).lower_ne k
  disj x hx := by
    obtain ⟨j', k⟩ := x
    replace hx : ¬ j' = j := hx
    exact Finset.disjoint_of_subset_left (unitsAtoms_sub B j' k) (hdisj j' j hx)

variable (B : ∀ j, CLChainAssembly S (R j) (n j)) (hdisj : ∀ j j', j ≠ j' → Disjoint (U j) (U j'))
  (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)

/-- The restricted state of the unit `j` is V5's start state of its chain assembly. -/
theorem unitsSplit_st (j : J) :
    (unitsSplit B).st (unitsStart B hdisj D hS layer hLayer) j = startState (B j) D hS layer hLayer := rfl

/-- The chain region of the unit `j` is V5's start region of its chain assembly. -/
theorem unitsSplit_reg (j : J) :
    HEq ((unitsSplit B).reg (A := unitsStart B hdisj D hS layer hLayer) (unitsRegion B hdisj) j) (chainStart (B j)) :=
  HEq.rfl

/-- V5's class of the unit `j` in the product is literally `canonFinsetK p kind (startState …) (chainStart …)`. -/
theorem canonFinsetK_units (p : ℕ) (kind : Bool) (j : J) :
    canonFinsetK p kind ((unitsSplit B).st (unitsStart B hdisj D hS layer hLayer) j)
        ((unitsSplit B).reg (A := unitsStart B hdisj D hS layer hLayer) (unitsRegion B hdisj) j) =
      canonFinsetK p kind (startState (B j) D hS layer hLayer) (chainStart (B j)) := rfl

/-- The upper joint of the unit region is the upper joint `a j` of the chain assembly. -/
theorem unitsRegion_upper (j : J) : (unitsRegion B hdisj j).blk.a = a j := rfl

variable [Fintype J] [DecidableEq J]

/-- **The class-product bijection with the canonical per-unit data**:
`τ ≅ Π_j canonFinsetK p kind (startState (B j) D hS layer hLayer) (chainStart (B j))`. -/
theorem classProd_bijOn_units (hprime : IsPrimeGarden S) (p : ℕ) (kind : Bool) :
    Set.BijOn (classProd (unitsSplit B) p kind (unitsStart B hdisj D hS layer hLayer) (unitsRegion B hdisj))
      (classU (unitsSplit B) p kind (unitsStart B hdisj D hS layer hLayer) (unitsRegion B hdisj))
      (Fintype.piFinset fun j => canonFinsetK p kind (startState (B j) D hS layer hLayer) (chainStart (B j))) :=
  classProd_bijOn (Us := unitsSplit B) (p := p) (kind := kind) (A := unitsStart B hdisj D hS layer hLayer) hprime
    (unitsRegion B hdisj)

/-- **The vine-case τ-class sum with the canonical per-unit data** (VINE-C over VINE-B♯, INTERFACE v2): the unit
factors are the recentered modulated class kernels over `canonFinsetK p kind (startState (B j) …) (chainStart (B j))`,
recentered at the upper joint `a j`, with the modulation `λ_j = modLam (frq i) (route i) j`. -/
theorem sum_tauClass_vineB_units {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {U₀ : J₀ → Finset (GBranch S.tree)}
    {a₀ b₀ : J₀ → GBranch S.tree} {R₀ : ∀ j, CLRegionData S (U₀ j) (a₀ j) (b₀ j)} {n₀ : J₀ → ℕ}
    (B₀ : ∀ j, CLChainAssembly S (R₀ j) (n₀ j)) (hdisj₀ : ∀ j j', j ≠ j' → Disjoint (U₀ j) (U₀ j'))
    (hprime : IsPrimeGarden S) {p : ℕ} {kind : Bool} (T : Finset (LayeredGarden w))
    (hT : (T : Set (LayeredGarden w)) = (unitsStart B₀ hdisj₀ D hS layer hLayer).allCoreOutputs (p := p) (kind := kind))
    (V : LayeredGarden w → ℂ) {I : Type*} [Fintype I] (sgn : I → ℂ) {d : ℕ} (G : Garden w) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (lay : GBranch G.tree → ℕ) (hinges : Finset (GBranch G.tree))
    (Zw : GenDecoration G d roots 0 → ℝ) (hG : G.IsPlain) (amp : I → ReplacementSlot G → Mom d → ℂ)
    (frq : I → ReplacementSlot G → Fin 2 → ℤ) (route : I → ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J₀)
    (hclk : J₀ → Fin 3 → ClkSrc G) (hmom : J₀ → Fin 4 → GNode G.tree) (F : I → J₀ → ℕ → Mom d → ℝ)
    (hV : ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      V y.1.layered = ∑ i, sgn i *
        outerValM G L γ δ base roots tt lay hinges Zw hG (amp i) (frq i) (route i) hclk hmom
          (fun j lam t k => unitRecenteredW y.1 (y.2 j) L γ δ (F i j) base (modW lam) (t 0) (t 1) (t 2)
            (k 0) (k 1) (k 2) (k 3)))
    (hint : ∀ i, ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      ∀ z, Integrable (outerIntegrandM G L γ δ base roots tt lay hG (amp i) (frq i) (route i) hclk hmom
        (fun j lam t k => unitRecenteredW y.1 (y.2 j) L γ δ (F i j) base (modW lam) (t 0) (t 1) (t 2)
          (k 0) (k 1) (k 2) (k 3)) z))
    (hsm : ∀ i, ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      Summable (fun z : GenDecoration G d roots 0 =>
        (splicedEpsilon G hinges z.1 : ℂ) * (Zw z : ℂ) *
          ∫ τ, outerIntegrandM G L γ δ base roots tt lay hG (amp i) (frq i) (route i) hclk hmom
            (fun j lam t k => unitRecenteredW y.1 (y.2 j) L γ δ (F i j) base (modW lam) (t 0) (t 1) (t 2)
              (k 0) (k 1) (k 2) (k 3)) z τ)) :
    ∑ LG ∈ T, V LG = ∑ i, sgn i *
      outerValM G L γ δ base roots tt lay hinges Zw hG (amp i) (frq i) (route i) hclk hmom
        (fun j lam t k => twistedRecenteredW S (a₀ j)
          (canonFinsetK p kind (startState (B₀ j) D hS layer hLayer) (chainStart (B₀ j)))
          L γ δ (F i j) base (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)) :=
  sum_tauClass_vineB (Us₀ := unitsSplit B₀) (A := unitsStart B₀ hdisj₀ D hS layer hLayer) hprime
    (unitsRegion B₀ hdisj₀) T hT V sgn G L γ δ base roots tt lay hinges Zw hG amp frq route hclk hmom F hV hint hsm

end WaveTurbulence.VineC
