/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitClasses
/-! Compatible actual atom maps preserve quotient crowns and the retained
branch and dart carriers of splice maps. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Stage1
variable {w : ℕ} {G H K J : Garden w}
variable {cls : GBranch G.tree → Option (GBranch G.tree)}
variable {clh : GBranch H.tree → Option (GBranch H.tree)}

/-- An injective relabeling preserves the existence of a common option value. -/
theorem option_map_common_iff {A B : Type*} (e : A ≃ B) (s t : Option A) :
    (∃ b, s.map e = some b ∧ t.map e = some b) ↔ ∃ a, s = some a ∧ t = some a := by
  cases s <;> cases t <;> simp [e.injective.eq_iff]

/-- Quotient retractions commute with every compatible actual atom map. -/
theorem repC_intertwines (F : MolIso G.molecule H.molecule)
    (hc : ∀ v, clh (F.e v) = (cls v).map F.e) (v : GBranch G.tree) :
    repC clh (F.e v) = F.e (repC cls v) := by
  unfold repC
  rw [hc]
  cases cls v <;> rfl

/-- Compatible merge classes preserve exactly the retained old branching names. -/
theorem kept_branch_intertwines (F : MolIso G.molecule H.molecule)
    (hc : ∀ v, clh (F.e v) = (cls v).map F.e) (v : GBranch G.tree) :
    (clh (F.e v) = none ∨ clh (F.e v) = some (F.e v)) ↔ (cls v = none ∨ cls v = some v) := by
  rw [hc]
  cases cls v <;> simp [F.e.injective.eq_iff]

/-- Compatible merge classes preserve exactly the deleted old darts. -/
theorem merged_dart_intertwines (F : MolIso G.molecule H.molecule)
    (hc : ∀ v, clh (F.e v) = (cls v).map F.e) (x : GardenDart G) :
    (∃ a, clh (H.molecule.atom (F.d x)) = some a ∧
      clh (H.molecule.atom (H.molecule.mate (F.d x))) = some a) ↔
    ∃ a, cls (G.molecule.atom x) = some a ∧ cls (G.molecule.atom (G.molecule.mate x)) = some a := by
  rw [F.atom_comm, F.mate_comm, F.atom_comm, hc, hc]
  exact option_map_common_iff F.e _ _

/-- Actual retained branch ranges agree under a compatible old atom map. -/
theorem splice_branch_ranges (F : MolIso G.molecule H.molecule)
    (hc : ∀ v, clh (F.e v) = (cls v).map F.e)
    (M : SpMap G K cls) (N : SpMap H J clh) (v : GBranch H.tree) :
    (∃ c, F.e (M.ob c) = v) ↔ ∃ c, N.ob c = v := by
  obtain ⟨u, rfl⟩ := F.e.surjective v
  constructor
  · rintro ⟨c, he⟩
    apply (N.ob_range _).mpr
    exact (kept_branch_intertwines F hc u).mpr ((M.ob_range _).mp ⟨c, F.e.injective he⟩)
  · intro h
    have hu := (kept_branch_intertwines F hc u).mp ((N.ob_range _).mp h)
    obtain ⟨c, he⟩ := (M.ob_range _).mpr hu
    exact ⟨c, congrArg F.e he⟩

/-- Actual retained dart ranges agree under a compatible old dart map. -/
theorem splice_dart_ranges (F : MolIso G.molecule H.molecule)
    (hc : ∀ v, clh (F.e v) = (cls v).map F.e)
    (M : SpMap G K cls) (N : SpMap H J clh) (x : GardenDart H) :
    (∃ y, F.d (M.od y) = x) ↔ ∃ y, N.od y = x := by
  obtain ⟨z, rfl⟩ := F.d.surjective x
  constructor
  · rintro ⟨y, he⟩
    apply (N.od_range _).mpr
    exact fun h => ((M.od_range _).mp ⟨y, F.d.injective he⟩) ((merged_dart_intertwines F hc z).mp h)
  · intro h
    have hz : ¬ ∃ a, cls (G.molecule.atom z) = some a ∧ cls (G.molecule.atom (G.molecule.mate z)) = some a :=
      fun hz => ((N.od_range _).mp h) ((merged_dart_intertwines F hc z).mpr hz)
    obtain ⟨y, he⟩ := (M.od_range _).mpr hz
    exact ⟨y, congrArg F.d he⟩

end WaveTurbulence.VineA
