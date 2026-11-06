/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.EndConst
public import WaveTurbulence.Foundations.Spine.RungPhase
public import WaveTurbulence.Foundations.Spine.FibreGarden
public import WaveTurbulence.Foundations.Spine.LadderFactor
public import WaveTurbulence.Foundations.Spine.ChainBound
public import WaveTurbulence.Foundations.Spine.BondProd
/-! # The factorization identity of the local ladder summand (S3b LADDER-DECAY) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.WeylSums Finset

variable {w d : ℕ} {G : Garden w}

lemma qrel_eq {n : ℕ} (S : ChainSigns n) (L : ChainLab n (Fin d → ℤ)) (h : S.IsSol L) (i : Fin n) :
    S.qrel L i = S.sg i 3 • (S.epsF i.succ • (L.a 0 - L.b 0)) := by
  unfold ChainSigns.qrel
  rw [S.b_eq L h i.succ]

namespace LadderDarts.Ctx
variable {n : ℕ} {u v : Fin (n + 1 + 1) → GBranch G.tree} (C : LadderDarts.Ctx G.molecule u v)

open scoped Classical in
/-- The class-dependent unimodular and bounded constant. -/
noncomputable def classTheta (D : SplicedKernelData G d) (L γ η δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (zs : GenDecoration G d roots 0) (t : (Molecule.ladderAtoms u v) → ℝ) : ℂ :=
  ((∏ a ∈ Molecule.ladderAtoms u v \ intAtoms u v, atomFac D L γ η base zs.1 a : ℝ) : ℂ) *
    (∏ a ∈ Molecule.ladderAtoms u v \ intAtoms u v, phaseAt D L γ δ base zs.1 a (tExt _ t a)) *
    (∏ x ∈ G.molecule.bonds.filter (fun x => G.molecule.InGroup (Molecule.ladderAtoms u v) x ∧ ¬ C.IsT x),
      D.edgeAmplitude x (base + latticePoint L (bondIndex G zs.1 x))) *
    ∏ i : Fin n, Complex.exp (((Real.pi * ((δ * L ^ (2 * γ) *
        ((C.signs.sg i 2 : ℝ) + (C.signs.sg i 3 : ℝ)) *
        ‖latticePoint L (C.signs.qrel (C.chainOf (bondIndex G zs.1)) i)‖ ^ 2 +
        D.frequency (v (LadderDarts.ir i))) * tExt _ t (v (LadderDarts.ir i)) +
        D.frequency (u (LadderDarts.ir i)) * tExt _ t (u (LadderDarts.ir i))) : ℝ) : ℂ) * Complex.I)


/-- Symmetry of the bond labels of a decoration. -/
lemma bondIndex_sym {roots : Fin w → (Fin d → ℤ)} (z : GenDecoration G d roots 0) (x : GardenDart G) :
    bondIndex G z.1 (G.molecule.mate x) = bondIndex G z.1 x := by
  rw [bondIndex_eq_restrict]
  exact Mole.restrictLabels_mate G z.1 (fun l => z.2.1.2 l) x

include C in
lemma isSol_dec (hP : G.IsPlain) {L : ℝ} (hL : L ≠ 0) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (hn : Mole.RootPairCompatible G (rootVec L base roots))
    (z : GenDecoration G d roots 0) : C.signs.IsSol (C.chainOf (bondIndex G z.1)) := by
  have h := C.interior_cons hP hL base roots (decEquiv L base roots hP hL hn z)
  exact C.isSol_chainOf (bondIndex G z.1) (bondIndex_sym z) h.1 h.2

end LadderDarts.Ctx
end WaveTurbulence.LadderDecay
