/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Rg5SSum

/-! # VINE-C: a whole CL region moved rigidly by a unit twist elsewhere (geometry and decorations)

TARGET observation 1 at L1948 (used in (redvine), L1953–L1956): the expression `K^{U_j}_{(G)}` is not affected by LF twists at vines of another unit.
For a unit twist `(G, P)` and a CL region `U` (joints `a`, `b`), `FullRigid P U` says that the lower joint `P.lower` is not
in `U` and that no child of ANY atom of `U` is `P.lower` or the partner of the retained leaf (V5's `RigidAt P U b` only
constrains the atoms of `U.erase b`; here the lower joint `b` is included, since `b` belongs to the interior of the
unit kernel).  Then the naive node bijection maps the whole local support of `U` onto that of the transported region,
with the same slot labels (`region_eq_rigid`, `bd_naive_rigid`, `support_iff_rigid`), and the local decorations with the
SAME four boundary momenta correspond (`decEquivR`), without any exchange of labels.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineC
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton
  WaveTurbulence.VineEstS4 TTree

variable {w : ℕ} {G : Garden w} (P : CorePlacement G)

/-- The region `U` is moved rigidly (including the children of its lower joint) by the unit twist `P`. -/
structure FullRigid (U : Finset (GBranch G.tree)) : Prop where
  lower_notMem : P.lower ∉ U
  child_lower : ∀ v ∈ U, ∀ i : Fin 3, v.child i ≠ P.lower.toNode
  child_partner : ∀ v ∈ U, ∀ i : Fin 3, v.child i ≠ (G.pair P.retained).toNode

namespace FullRigid
variable {P} {U : Finset (GBranch G.tree)} (hF : FullRigid P U)
include hF

theorem rigidAt (b : GBranch G.tree) : RigidAt P U b :=
  ⟨hF.lower_notMem, fun v hv => hF.child_lower v (Finset.mem_of_mem_erase hv),
    fun v hv => hF.child_partner v (Finset.mem_of_mem_erase hv)⟩

theorem ne_lower {v : GBranch G.tree} (hv : v ∈ U) : v ≠ P.lower := fun h => hF.lower_notMem (h ▸ hv)

theorem mem_erase_lower {v : GBranch G.tree} (hv : v ∈ U) : v ∈ U.erase P.lower :=
  Finset.mem_erase.mpr ⟨hF.ne_lower hv, hv⟩

theorem erase_lower : U.erase P.lower = U := Finset.erase_eq_of_notMem hF.lower_notMem

theorem erase_lower' : (twistedAtoms G P U).erase (eB P P.lower) = twistedAtoms G P U :=
  Finset.erase_eq_of_notMem (fun h => hF.lower_notMem ((mem_twistedAtoms G P U P.lower).mp h))

/-- Every child of every atom of `U` is moved like a child. -/
theorem child_naive {v : GBranch G.tree} (hv : v ∈ U) (i : Fin 3) :
    naiveNodeEquiv G P (v.child i) = (eB P v).child i :=
  (hF.rigidAt P.lower).child_naive (hF.mem_erase_lower hv) i

theorem child_retained {v : GBranch G.tree} (hv : v ∈ U) (i : Fin 3) : v.child i ≠ P.retained.toNode := by
  intro he
  exact hF.ne_lower hv ((Twist.parent_eq_of_child (n := P.retained.toNode) (retained_nonroot G P)
    (p := v) (i := i) he.symm).symm.trans (retained_parent G P))

end FullRigid

section Region
variable {P} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (hB : G.molecule.IsBlock U a b) (hF : FullRigid P U)
  (R : CLRegionData G U a b) (R' : CLRegionData (unitTwistGarden G P) (twistedAtoms G P U) (eB P a) (eB P b))

include hB hF in
/-- The slots of the transported region are those of the original. -/
theorem region_eq_rigid :
    R'.excluded = R.excluded ∧ R'.kept = R.kept ∧ R'.positive = R.positive ∧ R'.negative = R.negative := by
  have hR := hF.rigidAt b
  have hex := excluded_eq_rigid P hB hR R R'
  have hkp := kept_eq_rigid P hB hR R R'
  have hbU : b ∈ U := hB.2.2.1
  have hsgn : ∀ i : Fin 3, (unitTwistGarden G P).sign ((eB P b).child i) = G.sign (b.child i) := by
    intro i
    rw [← hF.child_naive hbU i]
    exact sign_naive_ordinary P _ (hF.child_lower b hbU i) (hF.child_retained hbU i) (hF.child_partner b hbU i)
  have hpos : R'.positive = R.positive := by
    have hp' : R'.positive ≠ R.kept := hkp ▸ (fun h => (R'.lower_excluded R'.positive |>.mpr (Or.inl rfl)) h)
    rcases (R.lower_excluded R'.positive).mp hp' with h | h
    · exact h
    · exfalso
      have h4 : G.sign (b.child R'.positive) = 1 := (hsgn _).symm.trans R'.positive_sign
      rw [h] at h4
      have := R.negative_sign
      rw [h4] at this
      exact absurd this (by decide)
  have hneg : R'.negative = R.negative := by
    have hp' : R'.negative ≠ R.kept := hkp ▸ (fun h => (R'.lower_excluded R'.negative |>.mpr (Or.inr rfl)) h)
    rcases (R.lower_excluded R'.negative).mp hp' with h | h
    · exfalso
      exact R'.distinct (hpos.trans h.symm)
    · exact h
  exact ⟨hex, hkp, hpos, hneg⟩

include hB hF in
/-- The four boundary nodes correspond under the naive node bijection (no exchange). -/
theorem bd_naive_rigid (j : Fin 4) : naiveNodeEquiv G P (clBoundaryNodes R j) = clBoundaryNodes R' j := by
  obtain ⟨he, _, hp, hn⟩ := region_eq_rigid hB hF R R'
  fin_cases j
  · exact naiveNodeEquiv_branch G P a
  · change naiveNodeEquiv G P (a.child R.excluded) = (eB P a).child R'.excluded
    rw [he]
    exact hF.child_naive hB.2.1 _
  · change naiveNodeEquiv G P (b.child R.positive) = (eB P b).child R'.positive
    rw [hp]
    exact hF.child_naive hB.2.2.1 _
  · change naiveNodeEquiv G P (b.child R.negative) = (eB P b).child R'.negative
    rw [hn]
    exact hF.child_naive hB.2.2.1 _

include hB hF in
/-- The local supports correspond under the naive node bijection. -/
theorem support_iff_rigid (x : GNode G.tree) :
    x ∈ clLocalSupport R ↔ naiveNodeEquiv G P x ∈ clLocalSupport R' := by
  refine (mem_clLocalSupport R x).trans (Iff.trans ?_ (mem_clLocalSupport R' (naiveNodeEquiv G P x)).symm)
  refine or_congr (RigidAt.real_iff P (hF.rigidAt b) x) ?_
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨j, (bd_naive_rigid hB hF R R' j).symm⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, (naiveNodeEquiv G P).injective ((bd_naive_rigid hB hF R R' j).trans hj)⟩

/-- The restriction of the naive node bijection to the supports. -/
@[expose] noncomputable def suppEquivR : ↥(clLocalSupport R) ≃ ↥(clLocalSupport R') :=
  Equiv.subtypeEquiv (naiveNodeEquiv G P) (support_iff_rigid hB hF R R')

theorem ext_compR {d : ℕ} (zz : ↥(clLocalSupport R') → (Fin d → ℤ)) (x : GNode G.tree) :
    clExtendIndices R (fun y => zz (suppEquivR hB hF R R' y)) x = clExtendIndices R' zz (naiveNodeEquiv G P x) := by
  classical
  by_cases hx : x ∈ clLocalSupport R
  · rw [clExtendIndices_apply R _ x hx,
      clExtendIndices_apply R' zz _ ((support_iff_rigid hB hF R R' x).mp hx)]
    rfl
  · have hx' : naiveNodeEquiv G P x ∉ clLocalSupport R' := fun h => hx ((support_iff_rigid hB hF R R' x).mpr h)
    unfold clExtendIndices
    rw [dite_eq_right hx, dite_eq_right hx']

section Dec
variable {d : ℕ} (L : ℝ) (base : Mom d) (β : Fin 4 → Mom d)

theorem dec_iffR (zz : ↥(clLocalSupport R') → (Fin d → ℤ)) :
    ((∀ v ∈ twistedAtoms G P U, clExtendIndices R' zz v.toNode = clExtendIndices R' zz (v.child 0) -
        clExtendIndices R' zz (v.child 1) + clExtendIndices R' zz (v.child 2)) ∧
      (∀ l, Mole.IsInternalLeaf (unitTwistGarden G P) (twistedAtoms G P U) l →
        clExtendIndices R' zz l.toNode = clExtendIndices R' zz ((unitTwistGarden G P).pair l).toNode) ∧
      ∀ j, base + latticePoint L (clExtendIndices R' zz (clBoundaryNodes R' j)) = β j) ↔
    ((∀ v ∈ U, clExtendIndices R (fun y => zz (suppEquivR hB hF R R' y)) v.toNode =
        clExtendIndices R (fun y => zz (suppEquivR hB hF R R' y)) (v.child 0) -
        clExtendIndices R (fun y => zz (suppEquivR hB hF R R' y)) (v.child 1) +
        clExtendIndices R (fun y => zz (suppEquivR hB hF R R' y)) (v.child 2)) ∧
      (∀ l, Mole.IsInternalLeaf G U l →
        clExtendIndices R (fun y => zz (suppEquivR hB hF R R' y)) l.toNode =
          clExtendIndices R (fun y => zz (suppEquivR hB hF R R' y)) (G.pair l).toNode) ∧
      ∀ j, base + latticePoint L (clExtendIndices R (fun y => zz (suppEquivR hB hF R R' y))
        (clBoundaryNodes R j)) = β j) := by
  set ext := clExtendIndices R (fun y => zz (suppEquivR hB hF R R' y)) with hext_def
  set ext' := clExtendIndices R' zz with hext'_def
  have hext : ∀ x, ext x = ext' (naiveNodeEquiv G P x) := fun x => ext_compR hB hF R R' zz x
  have hR := hF.rigidAt b
  have cons_at : ∀ v ∈ U, (ext v.toNode = ext (v.child 0) - ext (v.child 1) + ext (v.child 2)) ↔
      (ext' (eB P v).toNode = ext' ((eB P v).child 0) - ext' ((eB P v).child 1) + ext' ((eB P v).child 2)) := by
    intro v hv
    have a0 : ext v.toNode = ext' (eB P v).toNode := (hext _).trans (congrArg ext' (naiveNodeEquiv_branch G P v))
    have a1 : ∀ i : Fin 3, ext (v.child i) = ext' ((eB P v).child i) := fun i =>
      (hext _).trans (congrArg ext' (hF.child_naive hv i))
    rw [a0, a1 0, a1 1, a1 2]
  have leaf_at : ∀ l : GLeaf G.tree, Mole.IsInternalLeaf G U l → ((ext l.toNode = ext (G.pair l).toNode) ↔
      (ext' (eL P l).toNode = ext' ((unitTwistGarden G P).pair (eL P l)).toNode)) := by
    intro l _
    have a0 : ext l.toNode = ext' (eL P l).toNode := (hext _).trans (congrArg ext' (naiveNodeEquiv_leaf G P l))
    have a1 : ext (G.pair l).toNode = ext' (eL P (G.pair l)).toNode :=
      (hext _).trans (congrArg ext' (naiveNodeEquiv_leaf G P _))
    have a2 : eL P (G.pair l) = (unitTwistGarden G P).pair (eL P l) := (unitTwistGarden_pair G P l).symm
    rw [a0, a1, a2]
  refine and_congr ?_ (and_congr ?_ ?_)
  · constructor
    · intro H v hv
      exact (cons_at v hv).mpr (H _ ((mem_twistedAtoms G P U v).mpr hv))
    · intro H v' hv'
      obtain ⟨v, rfl⟩ := (eB P).surjective v'
      exact (cons_at v ((mem_twistedAtoms G P U v).mp hv')).mp (H v ((mem_twistedAtoms G P U v).mp hv'))
  · constructor
    · intro H l hl
      have hl' := (internal_iff_rigid P hR l).mpr hl
      exact (leaf_at l hl).mpr (H _ hl')
    · intro H l' hl'
      obtain ⟨l, rfl⟩ := (eL P).surjective l'
      have hl := (internal_iff_rigid P hR l).mp hl'
      exact (leaf_at l hl).mp (H l hl)
  · have hb : ∀ j, ext (clBoundaryNodes R j) = ext' (clBoundaryNodes R' j) :=
      fun j => (hext _).trans (congrArg ext' (bd_naive_rigid hB hF R R' j))
    simp only [hb]

/-- **The local decorations of the region and of its rigid image correspond (same boundary momenta).** -/
@[expose] noncomputable def decEquivR : CLLocalDecoration R' L base β ≃ CLLocalDecoration R L base β :=
  Equiv.subtypeEquiv (Equiv.arrowCongr (suppEquivR hB hF R R').symm (Equiv.refl _))
    (fun zz => dec_iffR hB hF R R' L base β zz)

theorem decEquivR_ext (κ : CLLocalDecoration R' L base β) (x : GNode G.tree) :
    clExtendIndices R (decEquivR hB hF R R' L base β κ).1 x = clExtendIndices R' κ.1 (naiveNodeEquiv G P x) :=
  ext_compR hB hF R R' κ.1 x

end Dec

end Region

end WaveTurbulence.VineC
