/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitClasses
public import WaveTurbulence.Foundations.Vine.A.VineQuotientClasses
public import WaveTurbulence.Foundations.Molecule.TwistExcludedSubtree
/-! The exceptional PC/LP exchange occurs entirely among deleted darts.
Consequently the ordinary leaf-and-branch map preserves deletion as well. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Twist
variable {w : ℕ} {G : Garden w}

/-- Swapping two points of a predicate preserves that predicate everywhere. -/
theorem swap_predicate_iff {A : Type*} [DecidableEq A] (R : A → Prop)
    {a b : A} (ha : R a) (hb : R b) (x : A) : R (Equiv.swap a b x) ↔ R x := by
  by_cases hx : x = a
  · subst x
    rw [Equiv.swap_apply_left]
    exact iff_of_true hb ha
  · by_cases hy : x = b
    · subst x
      rw [Equiv.swap_apply_right]
      exact iff_of_true ha hb
    · rw [Equiv.swap_apply_of_ne_of_ne hx hy]

/-- Deletion of a dart means that both its atoms have the same nonempty merge class. -/
def DeletedDart (cls : GBranch G.tree → Option (GBranch G.tree)) (d : GardenDart G) : Prop :=
  ∃ a, cls (G.molecule.atom d) = some a ∧ cls (G.molecule.atom (G.molecule.mate d)) = some a

/-- Reversing an actual dart preserves deletion. -/
theorem deletedDart_mate_iff (cls : GBranch G.tree → Option (GBranch G.tree)) (d : GardenDart G) :
    DeletedDart cls (G.molecule.mate d) ↔ DeletedDart cls d := by
  unfold DeletedDart
  rw [G.molecule.mate_mate]
  exact ⟨fun ⟨a, h1, h2⟩ => ⟨a, h2, h1⟩, fun ⟨a, h1, h2⟩ => ⟨a, h2, h1⟩⟩

/-- Both ends of the retained LP bond belong to the actual active vine. -/
theorem retainedLP_inGroup (Z : TwistGroupSite G) : G.molecule.InGroup Z.S0 (retainedLP G Z.P) := by
  have ha : G.molecule.atom (retainedLP G Z.P) = Z.P.lower := retained_parent G Z.P
  exact ⟨ha.symm ▸ Z.hB.2.2.1, placement_paired_parent_mem G Z.P Z.hP⟩

/-- B1b-2 (Mk-general form of `exceptionalDartSwap_deleted`). -/
theorem exceptionalDartSwap_deletedMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)}
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (d : GardenDart G) :
    DeletedDart (spliceFold G (unitBlocks G σ Mk)).cls (exceptionalDartSwap G Z.P d) ↔
      DeletedDart (spliceFold G (unitBlocks G σ Mk)).cls d := by
  classical
  let R := DeletedDart (spliceFold G (unitBlocks G σ Mk)).cls
  have hp : R (lowerPC G Z.P false) := active_internal_dart_mergedMk Z σ hsel
    ⟨Z.hB.2.2.1, Z.hCL.2.choose_spec⟩
  have hl : R (retainedLP G Z.P) := active_internal_dart_mergedMk Z σ hsel (retainedLP_inGroup Z)
  have hp' : R (lowerPC G Z.P true) := (deletedDart_mate_iff _ _).mpr hp
  have hl' : R (G.molecule.mate (retainedLP G Z.P)) := (deletedDart_mate_iff _ _).mpr hl
  change R (Equiv.swap _ _ (Equiv.swap _ _ d)) ↔ R d
  exact (swap_predicate_iff R hp' hl' _).trans (swap_predicate_iff R hp hl d)

/-- B1b-2 (Mk-general form of `naiveDart_deleted_iff`). -/
theorem naiveDart_deleted_iffMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (d : GardenDart G) :
    DeletedDart (spliceFold Z.target (unitBlocks Z.target (transportPrescription Z.iso σ) Mk')).cls
      (naiveDartEquiv G Z.P d) ↔ DeletedDart (spliceFold G (unitBlocks G σ Mk)).cls d := by
  let x := (exceptionalDartSwap G Z.P).symm d
  have h := merged_dart_intertwines Z.iso (unitBlocks_cls_twistMk Z σ hT hsel) x
  change DeletedDart _ (twistDartEquiv G Z.P x) ↔ DeletedDart _ x at h
  have he : twistDartEquiv G Z.P x = naiveDartEquiv G Z.P d := by
    change naiveDartEquiv G Z.P (exceptionalDartSwap G Z.P ((exceptionalDartSwap G Z.P).symm d)) = _
    rw [Equiv.apply_symm_apply]
  rw [he] at h
  have hx := exceptionalDartSwap_deletedMk Z σ hsel x
  rw [show exceptionalDartSwap G Z.P x = d from Equiv.apply_symm_apply _ _] at hx
  exact h.trans hx.symm

end WaveTurbulence.VineA
