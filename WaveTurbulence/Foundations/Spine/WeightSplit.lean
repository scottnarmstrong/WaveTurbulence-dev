/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.RungGarden
public import WaveTurbulence.Foundations.Spine.BondProd
public import WaveTurbulence.Foundations.Spine.LadderFactor
/-! # Splitting the ladder weight (S3b LADDER-DECAY)

`ladderWeight = (end atoms) * (interior rungs in chart coordinates) * (chain bond amplitudes) *
(outer bond amplitudes)`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open WaveTurbulence WaveTurbulence.LGSpine Finset

variable {w d : ℕ} {G : Garden w}

/-- The epsilon and gap factor of one atom. -/
noncomputable def atomFac (D : SplicedKernelData G d) (L γ η : ℝ) (base : Mom d)
    (zz : GNode G.tree → (Fin d → ℤ)) (a : GBranch G.tree) : ℝ :=
  epsCoef (zz (a.child 0)) (zz (a.child 1)) (zz (a.child 2)) *
    gapAtomSpec (D.gapSpecification a) L γ η base zz

lemma localLadderGapIndicator_eq (D : SplicedKernelData G d) (S : Finset (GBranch G.tree))
    (L γ η : ℝ) (base : Mom d) (zz : GNode G.tree → (Fin d → ℤ)) :
    localLadderGapIndicator G D S L γ η base zz = ∏ a ∈ S, gapAtomSpec (D.gapSpecification a) L γ η base zz := by
  unfold localLadderGapIndicator
  refine Finset.prod_congr rfl (fun a _ => ?_)
  rcases D.gapSpecification a with _ | q <;> rfl

open scoped Classical in
lemma ladderWeight_eq_prod (D : SplicedKernelData G d) (S : Finset (GBranch G.tree)) (L γ η : ℝ)
    (base : Mom d) (zz : GNode G.tree → (Fin d → ℤ)) :
    ladderWeight D S L γ η base zz = ((∏ a ∈ S, atomFac D L γ η base zz a : ℝ) : ℂ) *
      ∏ x ∈ G.molecule.bonds.filter (G.molecule.InGroup S),
        D.edgeAmplitude x (base + latticePoint L (bondIndex G zz x)) := by
  unfold ladderWeight atomFac
  rw [Finset.prod_mul_distrib, ← localLadderGapIndicator_eq]
  push_cast
  ring

namespace LadderDarts.Ctx
variable {n : ℕ} {u v : Fin (n + 1 + 1) → GBranch G.tree} (C : LadderDarts.Ctx G.molecule u v)

include C in
/-- **Interior/end split of the atom factors.** -/
theorem prod_atomFac (D : SplicedKernelData G d) (L γ η : ℝ) (base : Mom d)
    (zz : GNode G.tree → (Fin d → ℤ))
    (hκ : ∀ x, bondIndex G zz (G.molecule.mate x) = bondIndex G zz x)
    (hsol : C.signs.IsSol (C.chainOf (bondIndex G zz))) :
    ∏ a ∈ Molecule.ladderAtoms u v, atomFac D L γ η base zz a =
      (∏ a ∈ Molecule.ladderAtoms u v \ intAtoms u v, atomFac D L γ η base zz a) *
        ∏ i : Fin n, C.rungW D L γ η i ((C.chainOf (bondIndex G zz)).a 0 - (C.chainOf (bondIndex G zz)).b 0)
          (C.signs.pairs (C.chainOf (bondIndex G zz)) i) := by
  have hsub : intAtoms u v ⊆ Molecule.ladderAtoms u v := interiorAtoms_subset
  rw [← Finset.prod_sdiff hsub]
  congr 1
  apply Complex.ofReal_injective
  have h1 := C.prod_interior (fun a => ((atomFac D L γ η base zz a : ℝ) : ℂ))
  have h2 : (∏ a ∈ intAtoms u v, ((atomFac D L γ η base zz a : ℝ) : ℂ)) =
      ∏ i : Fin n, (((atomFac D L γ η base zz (u (LadderDarts.ir i)) : ℝ) : ℂ) *
        ((atomFac D L γ η base zz (v (LadderDarts.ir i)) : ℝ) : ℂ)) := h1
  push_cast
  rw [h2]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have := C.rungW_eq D L γ η base zz hκ hsol i
  rw [← this]
  unfold atomFac
  push_cast
  ring

end LadderDarts.Ctx

end WaveTurbulence.LadderDecay
