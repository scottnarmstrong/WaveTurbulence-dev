/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineHyperAdjointVC
public import WaveTurbulence.Foundations.Molecule.VineLatticeGaps
import Mathlib.Tactic

/-! # Hyper-vine-like gaps retain their designated adjoint bond

Owner reading 2026-11-04: a hyper-block object retains its actual designated
joint bond. Different valid deletions on one atom group are different objects.
The gap uses this same designation throughout, as TARGET defdiff requires.
No pinned definition is altered; the existential shape predicates remain useful.
-/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Actual source data for a hyper-vine-like object, retaining the bond
which defines its adjoint VC and therefore its decorated gap. -/
structure HyperLikeRealization (M : Molecule V D) (S : Finset V) (a b : V) where
  added : D
  ends_eq : M.ends added=s(a,b)
  adjoint : IsVC (Mole.eraseBond M added) S a b

/-- Erasing the designated data recovers exactly the existential HV/HVC shape. -/
theorem hyperLike_iff_realization {M : Molecule V D} {S : Finset V} {a b : V} :
    (IsHV M S a b ∨ IsHVC M S a b) ↔ Nonempty (HyperLikeRealization M S a b) := by
  rw [hyperLike_iff_adjoint_VC]
  constructor
  · rintro ⟨e,he,hVC⟩
    exact ⟨⟨e,he,hVC⟩⟩
  · rintro ⟨R⟩
    exact ⟨R.added,R.ends_eq,R.adjoint⟩

namespace HyperLikeRealization
variable {M : Molecule V D} {S : Finset V} {a b : V} (R : HyperLikeRealization M S a b)

/-- TARGET defdiff: the hyper-object gap is the actual gap of this
specified adjoint, with lattice labels restricted to its surviving darts. -/
@[expose] def IsGap {d : ℕ} (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (r : Mom d) : Prop :=
  (Mole.eraseBond M R.added).IsBlockGap L w (fun x => κ x.1) S a r

/-- Owner reading 2026-11-04, flagged for source audit: hyper-object
containment uses atom-set inclusion, and equal atom groups require the same
designated deleted bond up to mates. Different designations of one group
are distinct non-nested objects (see the triple-bond audit example). -/
@[expose] def IsContained {A : Finset V} {x y : V} (P : HyperLikeRealization M A x y)
    (R : HyperLikeRealization M S a b) : Prop :=
  A ⊆ S ∧ (A=S → P.added=R.added ∨ P.added=M.mate R.added)

/-- For a fixed designated hyper-object and ordered joint, the gap is unique. -/
theorem gap_unique {d : ℕ} (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) {r r' : Mom d}
    (hr : R.IsGap L w κ r) (hr' : R.IsGap L w κ r') : r=r' :=
  blockGap_unique (Mole.eraseBond M R.added) R.adjoint.1 hr hr'

/-- In particular a fixed object cannot have two different gap kinds. -/
theorem gapKind_unique {d : ℕ} (L γ η : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) {r r' : Mom d}
    (hr : R.IsGap L w κ r) (hr' : R.IsGap L w κ r') :
    Molecule.gapKind L γ η r=Molecule.gapKind L γ η r' :=
  congrArg (Molecule.gapKind L γ η) (R.gap_unique L w κ hr hr')

end HyperLikeRealization
end WaveTurbulence.Vine
