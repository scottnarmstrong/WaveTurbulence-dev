/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceLocalLadder
public import WaveTurbulence.Foundations.Spine.SplicedAmplitudeSupport
/-! Exact local/outside factorization of the source spliced momentum amplitude. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset
open scoped Classical

noncomputable def splicedVertexGapFactor {w d : ℕ} (G : Garden w) (D : SplicedKernelData G d)
    (L γ η : ℝ) (base : Mom d) (z : GNode G.tree → (Fin d → ℤ)) (v : GBranch G.tree) : ℝ :=
  match D.gapSpecification v with
  | none => 1
  | some q => if Molecule.gapKind L γ η
      (base + latticePoint L (bondIndex G z q.first) -
        (base + latticePoint L (bondIndex G z q.second))) = q.kind then 1 else 0

noncomputable def localLadderMomentumAmplitude {w d : ℕ} (G : Garden w) (D : SplicedKernelData G d)
    (S : Finset (GBranch G.tree)) (L γ η : ℝ) (base : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) : ℂ :=
  ((∏ v ∈ S, epsCoef (z (v.child 0)) (z (v.child 1)) (z (v.child 2))) : ℂ) *
    (localLadderGapIndicator G D S L γ η base z : ℂ) *
    ∏ x ∈ G.molecule.bonds.filter (G.molecule.InGroup S),
      D.edgeAmplitude x (base + latticePoint L (bondIndex G z x))

noncomputable def outerLadderMomentumAmplitude {w d : ℕ} (G : Garden w) (D : SplicedKernelData G d)
    (S : Finset (GBranch G.tree)) (L γ η : ℝ) (base : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) : ℂ :=
  ((∏ v ∈ (univ.filter fun v => v ∉ D.hinges) \ S,
      epsCoef (z (v.child 0)) (z (v.child 1)) (z (v.child 2))) : ℂ) *
    ((∏ v ∈ univ \ S, splicedVertexGapFactor G D L γ η base z v) : ℂ) *
    (∏ x ∈ G.molecule.bonds \ (G.molecule.bonds.filter (G.molecule.InGroup S)),
      D.edgeAmplitude x (base + latticePoint L (bondIndex G z x))) *
    D.hingeAmplitude (fun x => base + latticePoint L (bondIndex G z x.1))

 theorem splicedMomentumAmplitude_split {w d : ℕ} (G : Garden w) (D : SplicedKernelData G d)
    (S : Finset (GBranch G.tree)) (hS : Disjoint S D.hinges)
    (L γ η : ℝ) (base : Mom d) (z : GNode G.tree → (Fin d → ℤ)) :
    splicedMomentumAmplitude G D L γ η base z =
      localLadderMomentumAmplitude G D S L γ η base z *
        outerLadderMomentumAmplitude G D S L γ η base z := by
  classical
  have hsub : S ⊆ univ.filter (fun v => v ∉ D.hinges) := by
    intro v hv
    exact mem_filter.mpr ⟨mem_univ _, fun hh => Finset.disjoint_left.mp hS hv hh⟩
  have hε := Finset.prod_sdiff hsub (f := fun v : GBranch G.tree =>
    epsCoef (z (v.child 0)) (z (v.child 1)) (z (v.child 2)))
  have hgap := Finset.prod_sdiff (Finset.subset_univ S)
    (f := splicedVertexGapFactor G D L γ η base z)
  have hedge := Finset.prod_sdiff (Finset.filter_subset (G.molecule.InGroup S) G.molecule.bonds)
    (f := fun x => D.edgeAmplitude x (base + latticePoint L (bondIndex G z x)))
  unfold splicedMomentumAmplitude localLadderMomentumAmplitude outerLadderMomentumAmplitude
  have hg : splicedGapIndicator G D L γ η base z =
      (∏ v ∈ univ \ S, splicedVertexGapFactor G D L γ η base z v) * localLadderGapIndicator G D S L γ η base z := by
    exact hgap.symm
  rw [hg, ← hedge]
  have he : splicedEpsilon G D.hinges z =
      (∏ v ∈ (univ.filter fun v => v ∉ D.hinges) \ S,
        epsCoef (z (v.child 0)) (z (v.child 1)) (z (v.child 2))) *
      ∏ v ∈ S, epsCoef (z (v.child 0)) (z (v.child 1)) (z (v.child 2)) := hε.symm
  rw [he]
  push_cast
  ring

end WaveTurbulence.LGSpine
