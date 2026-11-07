/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceDarts
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceTimeIntegral
/-! All actual bond-amplitude, hinge-amplitude and local-gap factors of
the normalized spliced kernel commute with the selected-splice maps. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.LGSpine
variable {w d : ℕ} {G H : Garden w}

/-- The outgoing-dart representatives of actual bonds are preserved by a molecular isomorphism. -/
theorem molIso_mem_bonds_iff (F : MolIso G.molecule H.molecule) (x : GardenDart G) :
    F.d x ∈ H.molecule.bonds ↔ x ∈ G.molecule.bonds := by
  change F.d x ∈ Finset.univ.filter (fun y => H.molecule.out y = true) ↔
    x ∈ Finset.univ.filter (fun y => G.molecule.out y = true)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, F.out_comm]

/-- Every transported actual edge amplitude has exactly its original momentum argument. -/
theorem unitSplice_edgeAmplitude (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (D : SplicedKernelData (stSt G σ).G d)
    (L : ℝ) (base : Mom d) (z : GNode (stSt Z.target (transportPrescription Z.iso σ)).G.tree → (Fin d → ℤ))
    (x : GardenDart (stSt G σ).G) :
    (mapSplicedKernelData (unitSpliceMolIso Z σ hsel) D).edgeAmplitude ((unitSpliceMolIso Z σ hsel).d x)
      (base + latticePoint L (bondIndex (stSt Z.target (transportPrescription Z.iso σ)).G z ((unitSpliceMolIso Z σ hsel).d x))) =
    D.edgeAmplitude x (base + latticePoint L (bondIndex (stSt G σ).G (z ∘ unitSpliceNodeEquiv Z σ hsel) x)) := by
  change D.edgeAmplitude ((unitSpliceMolIso Z σ hsel).d.symm ((unitSpliceMolIso Z σ hsel).d x)) _ = _
  rw [Equiv.symm_apply_apply]
  exact congrArg (fun r => D.edgeAmplitude x (base + latticePoint L r)) (unitSplice_bondIndex Z σ hsel z x).symm

/-- The entire product over actual outgoing bond representatives is invariant. -/
theorem unitSplice_edgeAmplitude_product (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (D : SplicedKernelData (stSt G σ).G d)
    (L : ℝ) (base : Mom d) (z : GNode (stSt Z.target (transportPrescription Z.iso σ)).G.tree → (Fin d → ℤ)) :
    (∏ x ∈ (stSt G σ).G.molecule.bonds,
      D.edgeAmplitude x (base + latticePoint L (bondIndex (stSt G σ).G (z ∘ unitSpliceNodeEquiv Z σ hsel) x))) =
    ∏ x ∈ (stSt Z.target (transportPrescription Z.iso σ)).G.molecule.bonds,
      (mapSplicedKernelData (unitSpliceMolIso Z σ hsel) D).edgeAmplitude x
        (base + latticePoint L (bondIndex (stSt Z.target (transportPrescription Z.iso σ)).G z x)) := by
  let F := unitSpliceMolIso Z σ hsel
  refine Finset.prod_bij (fun x _ => F.d x) (fun x hx => (molIso_mem_bonds_iff F x).mpr hx)
    (fun x _ y _ h => F.d.injective h) ?_ (fun x _ => (unitSplice_edgeAmplitude Z σ hsel D L base z x).symm)
  intro y hy
  refine ⟨F.d.symm y, (molIso_mem_bonds_iff F _).mp ?_, F.d.apply_symm_apply y⟩
  simpa only [Equiv.apply_symm_apply] using hy

/-- The exact full hinge-amplitude argument is transported, without any regularity premise. -/
theorem unitSplice_hingeAmplitude (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (D : SplicedKernelData (stSt G σ).G d)
    (L : ℝ) (base : Mom d) (z : GNode (stSt Z.target (transportPrescription Z.iso σ)).G.tree → (Fin d → ℤ)) :
    (mapSplicedKernelData (unitSpliceMolIso Z σ hsel) D).hingeAmplitude
      (fun x => base + latticePoint L (bondIndex (stSt Z.target (transportPrescription Z.iso σ)).G z x.1)) =
    D.hingeAmplitude (fun x => base + latticePoint L (bondIndex (stSt G σ).G (z ∘ unitSpliceNodeEquiv Z σ hsel) x.1)) := by
  apply congrArg D.hingeAmplitude
  funext x
  exact congrArg (fun r => base + latticePoint L r) (unitSplice_bondIndex Z σ hsel z x.1).symm

/-- The complete literal local-gap indicator is invariant under actual data and coordinate transport. -/
theorem unitSplice_splicedGapIndicator (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (D : SplicedKernelData (stSt G σ).G d)
    (L γ η : ℝ) (base : Mom d) (z : GNode (stSt Z.target (transportPrescription Z.iso σ)).G.tree → (Fin d → ℤ)) :
    splicedGapIndicator (stSt G σ).G D L γ η base (z ∘ unitSpliceNodeEquiv Z σ hsel) =
      splicedGapIndicator (stSt Z.target (transportPrescription Z.iso σ)).G
        (mapSplicedKernelData (unitSpliceMolIso Z σ hsel) D) L γ η base z := by
  classical
  let F := unitSpliceMolIso Z σ hsel
  unfold splicedGapIndicator
  conv_lhs => rw [← F.e.symm.prod_comp]
  apply Finset.prod_congr rfl
  intro v _
  cases hq : D.gapSpecification (F.e.symm v) with
  | none =>
    simp only [F] at hq
    simp only [mapSplicedKernelData, hq, Option.map_none]
  | some q =>
    simp only [F] at hq
    simp only [F, mapSplicedKernelData, hq, Option.map_some, mapLocalGapSpecification]
    rw [unitSplice_bondIndex, unitSplice_bondIndex]

end WaveTurbulence.VineA
