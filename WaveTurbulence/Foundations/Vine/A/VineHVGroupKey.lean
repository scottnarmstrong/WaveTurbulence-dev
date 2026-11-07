/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineGroupPickCarrier
public import WaveTurbulence.Foundations.Vine.A.VineNormalizationNames
/-! R83 single-HV keys: normalized bond first, then ordered joint and dart names. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Mole WaveTurbulence.Stage1
variable {w : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)}

/-- Both joints of a valid HV candidate belong to its support. -/
theorem HVCandidate.joints {t : GBranch G.tree × GBranch G.tree × GardenDart G}
    (h : HVCandidate G S t) : t.1 ∈ S ∧ t.2.1 ∈ S :=
  ⟨h.2.choose_spec.1.2.1, h.2.choose_spec.1.2.2.1⟩

/-- A candidate's deleted bond is internal to its support. -/
theorem HVCandidate.internal {t : GBranch G.tree × GBranch G.tree × GardenDart G}
    (h : HVCandidate G S t) : G.molecule.InGroup S t.2.2 := by
  have he := h.1
  unfold Molecule.ends at he
  rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1.symm ▸ h.joints.1, h2.symm ▸ h.joints.2⟩
  · exact ⟨h1.symm ▸ h.joints.2, h2.symm ▸ h.joints.1⟩

/-- A valid single-HV candidate's deleted bond survives the all-SG splice. -/
def hvCandidateDart (hS : SingleHVGroup G S) (t : {t // HVCandidate G S t}) : CoarseDart G :=
  ⟨t.1.2.2, ((coarseSplice G).M.od_range _).mpr (by
    rintro ⟨a, ha, _⟩
    rw [hS.cls_none t.2.internal.1] at ha
    cases ha)⟩

/-- The bond is compared first in a fixed lexicographic address order; joint
and directed-dart names break ties. There is no prescription argument. -/
noncomputable def hvGroupKey (hS : SingleHVGroup G S) (t : {t // HVCandidate G S t}) : List (List ℕ) :=
  let d := coarseDartWord G (hvCandidateDart hS t)
  let m := coarseDartWord G (coarseDartMate G (hvCandidateDart hS t))
  [min d m, max d m, coarseAtomWord G t.1.1, coarseAtomWord G t.1.2.1, d]

/-- The complete normalized key distinguishes every valid single-HV triple. -/
theorem hvGroupKey_injective (hS : SingleHVGroup G S) : Function.Injective (hvGroupKey hS) := by
  intro x y he
  have htail := (List.cons.inj (List.cons.inj he).2).2
  have ha := (List.cons.inj htail).1
  have hb := (List.cons.inj (List.cons.inj htail).2).1
  have hd := (List.cons.inj (List.cons.inj (List.cons.inj htail).2).2).1
  have hea : x.1.1 = y.1.1 := coarseAtomWord_inj_of_none
    (hS.cls_none x.2.joints.1) (hS.cls_none y.2.joints.1) ha
  have heb : x.1.2.1 = y.1.2.1 := coarseAtomWord_inj_of_none
    (hS.cls_none x.2.joints.2) (hS.cls_none y.2.joints.2) hb
  have hed : x.1.2.2 = y.1.2.2 := congrArg Subtype.val (coarseDartWord_injective G hd)
  exact Subtype.ext (Prod.ext hea (Prod.ext heb hed))

/-- The single-HV normalized candidate set has exactly one least triple. -/
theorem hvGroupKey_existsUnique (hS : SingleHVGroup G S) :
    ∃! t : {t // HVCandidate G S t}, ∀ u, hvGroupKey hS t ≤ hvGroupKey hS u := by
  let : Nonempty {t // HVCandidate G S t} := hS.candidate
  exact existsUnique_least_key (hvGroupKey hS) (hvGroupKey_injective hS)

/-- R83's single-HV choice, made once in the sigma-independent normalization. -/
noncomputable def hvGroupPick (G : Garden w) (S : Finset (GBranch G.tree)) :
    Option (GBranch G.tree × GBranch G.tree × GardenDart G) := by
  classical
  exact if hS : SingleHVGroup G S then some (hvGroupKey_existsUnique hS).choose.1 else none

/-- Success is exactly the approved single-HV maximal-group case. -/
theorem hvGroupPick_isSome : (hvGroupPick G S).isSome ↔ SingleHVGroup G S := by
  classical
  unfold hvGroupPick
  split_ifs with hS <;> simp only [Option.isSome_some, Option.isSome_none, Bool.false_eq_true, hS]

/-- The chosen triple is valid and is the unique least normalized candidate. -/
theorem hvGroupPick_spec {t : GBranch G.tree × GBranch G.tree × GardenDart G}
    (h : hvGroupPick G S = some t) : ∃ hS : SingleHVGroup G S, ∃ ht : HVCandidate G S t,
      ∀ u, hvGroupKey hS ⟨t, ht⟩ ≤ hvGroupKey hS u := by
  classical
  unfold hvGroupPick at h
  split_ifs at h with hS
  · have he := Option.some.inj h
    subst t
    exact ⟨hS, _, (hvGroupKey_existsUnique hS).choose_spec.1⟩

end WaveTurbulence.VineA
