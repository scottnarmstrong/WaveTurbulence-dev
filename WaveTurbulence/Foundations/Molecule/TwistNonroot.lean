/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.CoreBranchAddresses

/-! # Nonroot incidences survive the unit twist

TARGET twistexplain (a): the actual PC and LP dart carriers have the same
boundary exclusions after the exchange, since both insertion slots are nonroot.
-/

public section
namespace WaveTurbulence.Twist
open TTree

/-- Moving between two nonroot slots preserves the root/nonroot distinction. -/
theorem exchangeAddress_nonroot_iff {w : ℕ} (h₀ h₁ a : Fin w × Path) (keep : Fin 3)
    (h₀n : h₀.2 ≠ []) (h₁n : h₁.2 ≠ []) :
    (exchangeAddress h₀ h₁ keep a).2 ≠ [] ↔ a.2 ≠ [] := by
  unfold exchangeAddress
  split
  · rename_i hi
    have ha : a.2 ≠ [] := fun he => h₀n (List.eq_nil_of_prefix_nil (he ▸ hi.2))
    have hb : h₁.2 ++ switchPath keep (a.2.drop h₀.2.length) ≠ [] :=
      List.append_ne_nil_of_left_ne_nil h₁n _
    exact iff_of_true hb ha
  · split
    · rename_i he
      subst a
      exact iff_of_true h₀n h₁n
    · rfl

variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- The actual branch bijection preserves nonroot status. -/
theorem coreBranchEquiv_nonroot (b : GBranch G.tree) :
    (coreBranchEquiv G P b).1.2 ≠ [] ↔ b.1.2 ≠ [] := by
  rw [coreBranchEquiv_address]
  exact exchangeAddress_nonroot_iff _ _ _ _ P.nonroot P.paired_nonroot

/-- The actual leaf bijection preserves nonroot status. -/
theorem coreLeafEquiv_nonroot (l : GLeaf G.tree) :
    (coreLeafEquiv G P l).1.2 ≠ [] ↔ l.1.2 ≠ [] := by
  rw [coreLeafEquiv_address]
  exact exchangeAddress_nonroot_iff _ _ _ _ P.nonroot P.paired_nonroot

/-- The concrete bijection on nonroot branching nodes. -/
@[expose] noncomputable def nonrootBranchEquiv :
    {b : GBranch G.tree // b.1.2 ≠ []} ≃ {b : GBranch (unitTwistGarden G P).tree // b.1.2 ≠ []} :=
  (coreBranchEquiv G P).subtypeEquiv fun b => (coreBranchEquiv_nonroot G P b).symm

/-- The concrete bijection on unmarked LP leaves whose partners are nonroot. -/
@[expose] noncomputable def lpLeafEquiv :
    {l : GLeaf G.tree // G.mark l = none ∧ l.1.2 ≠ [] ∧ (G.pair l).1.2 ≠ []} ≃
    {l : GLeaf (unitTwistGarden G P).tree // (unitTwistGarden G P).mark l = none ∧
      l.1.2 ≠ [] ∧ ((unitTwistGarden G P).pair l).1.2 ≠ []} :=
  (coreLeafEquiv G P).subtypeEquiv fun l => by
    rw [unitTwistGarden_mark,unitTwistGarden_pair,
      coreLeafEquiv_nonroot,coreLeafEquiv_nonroot]

/-- The ordinary branch/leaf transport on actual dart carriers, before the PC/LP exchange. -/
@[expose] noncomputable def naiveDartEquiv : GardenDart G ≃ GardenDart (unitTwistGarden G P) :=
  Equiv.sumCongr (Equiv.prodCongr (nonrootBranchEquiv G P) (Equiv.refl Bool)) (lpLeafEquiv G P)

/-- The ordinary dart transport respects the actual pairing of half-edges. -/
theorem naiveDartEquiv_mate (x : GardenDart G) :
    (unitTwistGarden G P).molecule.mate (naiveDartEquiv G P x) = naiveDartEquiv G P (G.molecule.mate x) := by
  cases x with
  | inl c => rfl
  | inr l =>
    apply congrArg Sum.inr
    apply Subtype.ext
    exact unitTwistGarden_pair G P l.1

end WaveTurbulence.Twist
