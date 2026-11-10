/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5WT.Engine
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceK.NormalizedAffine
public import WaveTurbulence.Foundations.Flower.FlAffine.Affine
public import WaveTurbulence.Foundations.Flower.V5W.Defs
public import WaveTurbulence.Foundations.Flower.V5WB.Final

/-! # V5W-T T4′: the region-top stem filter in V5's normalized chain coordinates (supplement Lemma 9.3)

`topFilterPullbackStatement : TopFilterPullbackStatement`: for every CL region `R` with top branch `a`, the top filter
`nodeWeight (topFilterWeight S) L base a` (i.e. `χ₀(|Ω_a|/S)`, `S = none`: no filter) has an output-dependent engine
pullback of mass `topFilterMass = ∫ ‖𝓕 χ₀‖`.

Mathematics.  On every chart point the decoration conserves momentum at `a` (`a ∈ U`) and has the boundary momenta
`k_a = e`, `k_{a, excluded} = f` (`clBoundaryNodes R 0, 1`), where `excluded ≠ 1` (`CLSpliceSlots.excluded_ne_middle`).
FL-AFFINE's `topFilter_omegaNode` (stem child `i`, same-sign child `o = excluded`, mid child `1`) gives
`χ₀(|Ω_a|/s) = χ₀Measure.value(⟪(2/s)·r, k_{a,1}⟫ - (2/s)⟪r, f⟫)`, `r = e - f`, and `k_{a,1}` is affine in the
normalized lattice (`VineSpaceK.normalized_node_affine`).  So the filter is the value of the one-dimensional measure
`χ₀Measure` at an affine function of the lattice whose LINEAR part `⟪(2/s) r(E), A v ·⟫` depends on the output `E`
through `r` — an `OutCharMix` (`affineOutCharMix`), not a `CharMix` (S-V5W §3.4).

`toOutCharMix`, `spatialOutCharMix`, `affineOutCharMix` are V5W-A's `toCharMix`, `spatialCharMix`, `affineCharMix`
with the frequency map depending on the output; their values at an output are the plain constructions at that output
(definitional), so no proof is copied.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.Flower.V5WT
open WaveTurbulence MeasureTheory Cut2A DegenVine
open scoped FourierTransform

/-! ## Output-dependent spatial and affine mixtures -/

section Mixtures
variable {V α : Type} [MeasurableSpace α] {d : ℕ}

/-- `VineSpaceK.toCharMix` with an output-dependent frequency map. -/
def toOutCharMix [MeasurableSpace V] (S : SumintShape) (F : SpatialMeasure V α) (hamp : Measurable F.amplitude)
    (ν : V → (Fin 4 → Mom d) → S.VIdx → Mom d) (hν : ∀ E, Measurable fun ξ => ν ξ E)
    (phase : α → (Fin 4 → Mom d) → ℂ) (hphase : ∀ z, Measurable (fun a => phase a z))
    (hphaseNorm : ∀ a z, ‖phase a z‖ ≤ 1) : OutCharMix S d where
  α := α
  μ := (VineSpaceK.toCharMix S F hamp (fun ξ => ν ξ 0) (hν 0) phase hphase hphaseNorm).μ
  hμ := (VineSpaceK.toCharMix S F hamp (fun ξ => ν ξ 0) (hν 0) phase hphase hphaseNorm).hμ
  ζ := fun a E => ν (F.frequency a) E
  hζ := fun E => (hν E).comp F.frequency_measurable
  u := (VineSpaceK.toCharMix S F hamp (fun ξ => ν ξ 0) (hν 0) phase hphase hphaseNorm).u
  hu := (VineSpaceK.toCharMix S F hamp (fun ξ => ν ξ 0) (hν 0) phase hphase hphaseNorm).hu
  hu1 := (VineSpaceK.toCharMix S F hamp (fun ξ => ν ξ 0) (hν 0) phase hphase hphaseNorm).hu1

theorem toOutCharMix_mass [MeasurableSpace V] (S : SumintShape) (F : SpatialMeasure V α)
    (hamp : Measurable F.amplitude)
    (ν : V → (Fin 4 → Mom d) → S.VIdx → Mom d) (hν : ∀ E, Measurable fun ξ => ν ξ E)
    (phase : α → (Fin 4 → Mom d) → ℂ) (hphase : ∀ z, Measurable (fun a => phase a z))
    (hphaseNorm : ∀ a z, ‖phase a z‖ ≤ 1) :
    (toOutCharMix S F hamp ν hν phase hphase hphaseNorm).mass = F.mass :=
  VineSpaceK.toCharMix_mass S F hamp (fun ξ => ν ξ 0) (hν 0) phase hphase hphaseNorm

/-- `VineSpaceK.spatialCharMix` with an output-dependent frequency map. -/
def spatialOutCharMix [MeasurableSpace V] (S : SumintShape) (F : SpatialMeasure V α)
    (ν : V → (Fin 4 → Mom d) → S.VIdx → Mom d) (hν : ∀ E, Measurable fun ξ => ν ξ E)
    (phase : α → (Fin 4 → Mom d) → ℂ) (hphase : ∀ E, Measurable fun a => phase a E)
    (hphaseNorm : ∀ a E, ‖phase a E‖ ≤ 1) : OutCharMix S d :=
  toOutCharMix S (VineSpaceK.measurableDensity F) (VineSpaceK.measurable_measurableDensity F)
    ν hν phase hphase hphaseNorm

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [CompleteSpace V]

/-- `VineSpaceK.affineCharMix` with an output-dependent linear part `A E`. -/
def affineOutCharMix (S : SumintShape) (F : SpatialMeasure V α)
    (A : (Fin 4 → Mom d) → S.VIdx → Mom d →L[ℝ] V) (c : (Fin 4 → Mom d) → V) : OutCharMix S d :=
  spatialOutCharMix S F (fun ξ E v => (A E v).adjoint ξ)
    (fun E => (continuous_pi fun v => (A E v).adjoint.continuous).measurable)
    (fun a E => (Real.fourierChar (inner ℝ (F.frequency a) (c E)) : ℂ))
    (fun E => (continuous_subtype_val.comp Real.continuous_fourierChar).measurable.comp
      (F.frequency_measurable.inner measurable_const))
    (fun _ _ => by simp only [Circle.norm_coe, le_refl])

theorem affineOutCharMix_mass (S : SumintShape) (F : SpatialMeasure V α)
    (A : (Fin 4 → Mom d) → S.VIdx → Mom d →L[ℝ] V) (c : (Fin 4 → Mom d) → V) :
    (affineOutCharMix S F A c).mass = F.mass := by
  unfold affineOutCharMix spatialOutCharMix
  rw [toOutCharMix_mass, VineSpaceK.mass_measurableDensity]

theorem affineOutCharMix_val (S : SumintShape) (F : SpatialMeasure V α)
    (A : (Fin 4 → Mom d) → S.VIdx → Mom d →L[ℝ] V) (c : (Fin 4 → Mom d) → V)
    (L : ℝ) (E : Fin 4 → Mom d) (x : S.VIdx → Fin d → ℤ) :
    (affineOutCharMix S F A c).val L E x = F.value (c E + ∑ v, A E v (latticePoint L (x v))) := by
  have h : (affineOutCharMix S F A c).val L E x = (VineSpaceK.affineCharMix S F (A E) c).val L E x := rfl
  rw [h, VineSpaceK.affineCharMix_val]

end Mixtures

/-! ## The top filter at a conserving node -/

section Node
variable {w d : ℕ} {G : Garden w}

theorem latticePoint_cons (L : ℝ) (u v x : Fin d → ℤ) :
    latticePoint L (u - v + x) = latticePoint L u - latticePoint L v + latticePoint L x := by
  ext j
  change (((u j - v j + x j : ℤ) : ℝ) / L) = (u j : ℝ) / L - (v j : ℝ) / L + (x j : ℝ) / L
  push_cast
  ring

/-- **The top filter at a node with lattice conservation** is `χ₀Measure` at
`⟪(2/s)(k_b - k_o), k_{b,1}⟫ - (2/s)⟪k_b - k_o, k_o⟫` (FL-AFFINE, Lemma 9.3), `o ∈ {0, 2}`. -/
theorem nodeWeight_topFilter_eq (L : ℝ) (base : Mom d) (s : ℝ) (b : GBranch G.tree) (z : GNode G.tree → Fin d → ℤ)
    (hcons : z b.toNode = z (b.child 0) - z (b.child 1) + z (b.child 2)) (o : Fin 3) (ho : o ≠ 1) :
    VineSpaceK.nodeWeight (V5W.topFilterWeight (some s)) L base b z =
      FlAffine.chi0Measure.value
        (innerSL ℝ ((2 / s) • (cosetDecoration G L base z b.toNode - cosetDecoration G L base z (b.child o)))
          (cosetDecoration G L base z (b.child 1)) +
        -((2 / s) * inner ℝ (cosetDecoration G L base z b.toNode - cosetDecoration G L base z (b.child o))
          (cosetDecoration G L base z (b.child o)))) := by
  set k := cosetDecoration G L base z with hk
  have hk' : k b.toNode = k (b.child 0) - k (b.child 1) + k (b.child 2) := by
    simp only [hk, cosetDecoration, hcons, latticePoint_cons]
    abel
  have hio : ∃ i : Fin 3, (i = 0 ∧ o = 2) ∨ (i = 2 ∧ o = 0) := by
    fin_cases o
    · exact ⟨2, Or.inr ⟨rfl, rfl⟩⟩
    · exact absurd rfl ho
    · exact ⟨0, Or.inl ⟨rfl, rfl⟩⟩
  obtain ⟨i, hi⟩ := hio
  have h := FlAffine.topFilter_omegaNode G k b hk' i o hi s
  unfold FlAffine.topFilterMeasure at h
  rw [Cut2A.SpatialMeasure.affine_value] at h
  rw [← h]
  simp [VineSpaceK.nodeWeight, V5W.topFilterWeight, omegaNode, hk]

end Node

/-! ## The pullback (Lemma 9.3 in chain coordinates) -/

section Pull
open RegRed Reg.Skeleton VineParamContract VineEstS2 VineEstS3 VineEstS4 VineEstS5C VineEstS5C.P3
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem topFilterMass_eq : V5W.topFilterMass = FlAffine.chi0Measure.mass := rfl

/-- The `S = some s` case. -/
theorem enginePullbackOut_topFilter_some (R : CLRegionData G U a b) (L : ℝ) (base : Mom d) (s : ℝ) :
    EnginePullbackOut R L base (VineSpaceK.nodeWeight (V5W.topFilterWeight (some s)) L base a)
      V5W.topFilterMass := by
  classical
  intro n hM9 B hL
  obtain ⟨A₁, c₁, hc₁⟩ := VineSpaceK.normalized_node_affine hM9 B (a.child 1) L base
  set σ : ℤˣ := G.sign a.toNode with hσ
  let r : (Fin 4 → Mom d) → Mom d := fun E => sumintBoundary σ E 0 - sumintBoundary σ E 1
  let f : (Fin 4 → Mom d) → Mom d := fun E => sumintBoundary σ E 1
  let A : (Fin 4 → Mom d) → (assemblyShape hM9 B).VIdx → Mom d →L[ℝ] ℝ :=
    fun E v => (innerSL ℝ ((2 / s) • r E)).comp (A₁ v)
  let c : (Fin 4 → Mom d) → ℝ := fun E =>
    innerSL ℝ ((2 / s) • r E) (base + c₁ E) + -((2 / s) * inner ℝ (r E) (f E))
  refine ⟨affineOutCharMix (assemblyShape hM9 B) FlAffine.chi0Measure A c, ?_, ?_⟩
  · rw [affineOutCharMix_mass]
    exact le_of_eq topFilterMass_eq.symm
  · intro β hβ x
    rw [affineOutCharMix_val]
    set κ := (clNormalizedChainEquiv hL B base β hβ hM9).symm x with hκ
    set z := clExtendIndices R κ.1 with hz
    have haU : a ∈ U := B.isBlock.2.1
    have hcons := κ.2.1 a haU
    have hb0 := κ.2.2.2 0
    have hb1 := κ.2.2.2 1
    simp only [clBoundaryNodes, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hb0 hb1
    rw [nodeWeight_topFilter_eq L base s a z hcons R.excluded R.excluded_ne_middle]
    have hE : (fun j => base + latticePoint L (β j)) =
        sumintBoundary σ (sumintBoundary σ (fun j => base + latticePoint L (β j))) :=
      (sumintBoundary_invol σ _).symm
    have he : cosetDecoration G L base z a.toNode =
        sumintBoundary σ (sumintBoundary σ (fun j => base + latticePoint L (β j))) 0 := by
      rw [← hE]; exact hb0
    have hf : cosetDecoration G L base z (a.child R.excluded) =
        sumintBoundary σ (sumintBoundary σ (fun j => base + latticePoint L (β j))) 1 := by
      rw [← hE]; exact hb1
    have ha1 : cosetDecoration G L base z (a.child 1) =
        base + (c₁ (sumintBoundary σ (fun j => base + latticePoint L (β j))) +
          ∑ v, A₁ v (latticePoint L (x v))) := by
      change base + latticePoint L (z (a.child 1)) = _
      rw [hz, hκ, hc₁ hL β hβ x]
    rw [he, hf, ha1]
    congr 1
    simp only [A, c, r, f, map_add, map_sum, ContinuousLinearMap.comp_apply]
    ring

end Pull

end WaveTurbulence.Flower.V5WT
