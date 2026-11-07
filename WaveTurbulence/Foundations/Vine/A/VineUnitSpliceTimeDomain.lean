/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceLeafParents
public import WaveTurbulence.Foundations.Spine.SourceSplicedKernel
/-! Actual selected simultaneous splice maps preserve branching incidence
and the full truncated time domain under coordinate transport. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.LGSpine
variable {w : ℕ} {G : Garden w}

/-- Branching child incidence is equivalent to a nonroot parent equation. -/
theorem branch_isChildOf_iff_parent {F : Fin w → TTree} (b a : GBranch F) :
    b.IsChildOf a ↔ ∃ hn : b.1.2 ≠ [], GNode.parent b.toNode hn = a := by
  constructor
  · rintro ⟨hi, i, he⟩
    have hn : b.1.2 ≠ [] := he ▸ List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil i [])
    refine ⟨hn, ?_⟩
    apply Subtype.ext
    change (b.1.1, b.1.2.dropLast) = a.1
    rw [hi, he, List.dropLast_append_cons, List.dropLast_singleton, List.append_nil]
  · rintro ⟨hn, he⟩
    have hi := congrArg (fun c : GBranch F => c.1.1) he
    have hp := congrArg (fun c : GBranch F => c.1.2) he
    exact ⟨hi, b.1.2.getLast hn, by rw [← hp]; exact (List.dropLast_append_getLast hn).symm⟩

/-- The actual post-splice atom map preserves the branching child relation in both directions. -/
theorem unitSpliceMolIso_child_iff (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (b a : GBranch (stSt G σ).G.tree) :
    ((unitSpliceMolIso Z σ hsel).e b).IsChildOf ((unitSpliceMolIso Z σ hsel).e a) ↔ b.IsChildOf a := by
  let F := unitSpliceMolIso Z σ hsel
  rw [branch_isChildOf_iff_parent, branch_isChildOf_iff_parent]
  constructor
  · rintro ⟨hn, he⟩
    have ho : b.1.2 ≠ [] := fun h => hn ((unitSpliceMolIso_branch_root Z σ hsel b).mpr h)
    refine ⟨ho, F.e.injective ?_⟩
    exact (unitSpliceMolIso_parent Z σ hsel b ho).trans he
  · rintro ⟨ho, he⟩
    have hn : (F.e b).1.2 ≠ [] := fun h => ho ((unitSpliceMolIso_branch_root Z σ hsel b).mp h)
    exact ⟨hn, (unitSpliceMolIso_parent Z σ hsel b ho).symm.trans (congrArg F.e he)⟩

/-- All time-domain conditions, including external root truncation, transport through the actual map. -/
theorem unitSplice_timeDomain_iff (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0)
    (layer : GBranch (stSt G σ).G.tree → ℕ) (tt : Fin w → ℝ)
    (t : GBranch (stSt G σ).G.tree → ℝ) :
    let F := unitSpliceMolIso Z σ hsel
    (fun v => t (F.e.symm v)) ∈ splicedTimeDomain
      (stSt Z.target (transportPrescription Z.iso σ)).G (fun v => layer (F.e.symm v)) tt ↔
      t ∈ splicedTimeDomain (stSt G σ).G layer tt := by
  dsimp only
  let F := unitSpliceMolIso Z σ hsel
  constructor
  · rintro ⟨hI, hpc, hrt⟩
    refine ⟨?_, ?_, ?_⟩
    · intro v
      simpa only [F, Equiv.symm_apply_apply] using hI (F.e v)
    · intro v u hch
      simpa only [F, Equiv.symm_apply_apply] using
        hpc (F.e v) (F.e u) ((unitSpliceMolIso_child_iff Z σ hsel v u).mpr hch)
    · intro v
      have h := hrt (F.e v)
      simpa only [F, Equiv.symm_apply_apply, unitSpliceMolIso_branch_index] using h
  · rintro ⟨hI, hpc, hrt⟩
    refine ⟨?_, ?_, ?_⟩
    · intro v
      exact hI (F.e.symm v)
    · intro v u hch
      obtain ⟨v, rfl⟩ := F.e.surjective v
      obtain ⟨u, rfl⟩ := F.e.surjective u
      simpa only [F, Equiv.symm_apply_apply] using hpc v u ((unitSpliceMolIso_child_iff Z σ hsel v u).mp hch)
    · intro v
      obtain ⟨v, rfl⟩ := F.e.surjective v
      simpa only [F, Equiv.symm_apply_apply, unitSpliceMolIso_branch_index] using hrt v

end WaveTurbulence.VineA
