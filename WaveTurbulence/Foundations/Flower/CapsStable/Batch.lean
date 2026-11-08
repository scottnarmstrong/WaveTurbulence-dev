/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.CapsStable.Step

/-! # CAPS-STABLE: `CapsTwistStable`

**`capsTwistStable : CapsComp.CapsTwistStable`** (o75 Lemma 2 (a), (b), (c), (e) for the capped labels of
supplement Lemma 2.1(4), at the concrete marking rule `protSkOf`). By induction on main's `FamilyBatch`, carrying
* `CompLabels` of the current garden (`op_labels`), and
* `FamUnm`: every family member is Π₀-unmarked at its non-upper atoms (`op_famUnm`).

The brief's hypothesis (no protected vertex of `Π`, selections included, in the near region of any non-upper atom)
gives `FamUnm` at the start, since `Π₀ ⊆ Π` (`famUnm_of_unprot`). No `𝒱`-membership of the members is used
(R166/F-MK-1 check: the members' own unmarkedness is what each step needs, and it is carried branch by branch). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkMark WaveTurbulence.LFTwist
  WaveTurbulence.Flower.CapsComp

namespace WaveTurbulence.Flower.CapsStable

variable {w : ℕ}

/-- `Π₀` is contained in `Π`. -/
theorem protI0_subset (LG : LayeredGarden w) (J : Finset (Fin w)) (pat : Fin w → FixPat) (tt ss : ℝ)
    (sel : Finset (GBranch LG.garden.tree)) :
    protI0 LG J pat tt ss ⊆ protectedSet LG J (fixCap LG J pat tt ss) sel := by
  intro a ha
  unfold protI0 protectedSet at ha
  unfold protectedSet
  rw [Finset.mem_filter] at ha ⊢
  obtain ⟨hu, σ, hn, hσ⟩ := ha
  refine ⟨hu, σ, hn, ?_⟩
  rcases hσ with h | ⟨b, hb, h⟩
  · exact Or.inl h
  · refine Or.inr ⟨b, hb, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · exact absurd h (Finset.notMem_empty _)

/-- The brief's unprotectedness gives Π₀-unmarkedness of every member. -/
theorem famUnm_of_unprot {R : ℕ} (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat)
    (kSel : Fin (2 * R) → Option ℕ) (tt ss : ℝ) {ι : Type} (B : FamilyReconstruction (2 * R) ι)
    (hun : ∀ i, ∀ b ∈ B.family.atoms i, b ≠ B.family.upper i →
      ¬ protSkOf R J (fun LG => fixCap LG J pat tt ss) (fun LG => selSetCap LG J kSel) B b) :
    FamUnm J pat tt ss B := by
  intro j b hb hbu ⟨a, ha, hna⟩
  exact hun j b hb hbu ⟨a, protI0_subset _ _ _ _ _ _ ha, hna⟩

/-- **The batch induction.** -/
theorem batch_labels {p : ℕ} {kind : Bool} {ι : Type*} {L : List ι} {A B : FamilyReconstruction w ι}
    (h : FamilyBatch p kind L A B) {J : Finset (Fin w)} {pat : Fin w → FixPat} (tt ss : ℝ)
    {Ntr : ℕ} {kd : FlowerKind} {matchOK : Fin w → Fin w → Prop} :
    FamUnm J pat tt ss A → CompLabels p Ntr kd J matchOK pat A.layered →
      CompLabels p Ntr kd J matchOK pat B.layered := by
  induction h with
  | nil A => exact fun _ hL => hL
  | skip i h ih => exact ih
  | apply op h ih => exact fun hF hL => ih (op_famUnm op tt ss hF) (op_labels op tt ss hF hL)

/-- **`CapsTwistStable`** (the named input of A3b CAPS-COMP, exact statement). -/
theorem capsTwistStable : CapsTwistStable := by
  intro P p n R Ntr kd J matchOK pat kSel tt ss sg kind ι B Lst _hprime _hcan hpre hun LH hLH
  obtain ⟨M, B', -, hbatch, rfl⟩ := hLH
  exact batch_labels hbatch tt ss (famUnm_of_unprot J pat kSel tt ss B hun) hpre.2

end WaveTurbulence.Flower.CapsStable
