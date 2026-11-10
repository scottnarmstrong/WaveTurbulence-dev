/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceMaximalObjects
public import WaveTurbulence.Foundations.Spine.SourceChainSwap
/-! The union object of two ordinary chain objects meeting at one joint, its small gap, and the
maximality consequence: a selected object cannot be strictly below an eligible non-omitted object.
The eligibility (container) of the union is NOT proved here; see WORKLOG. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine.SourceVine
open Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

/-- The ordinary union object of two chains `a - c` and `c - b` meeting exactly at `c`, when the
union is a block. -/
noncomputable def oneJointUnionObject {S T : Finset V} {a b c : V} {n m : ℕ}
    (hS : Chain M S a c n) (hT : Chain M T c b m) (hST : S ∩ T = {c})
    (hB : M.IsBlock (S ∪ T) a b) : Object M :=
  ⟨S ∪ T, a, b, .vc ⟨hB, n + m, chain_union_of_one_joint hS hT hST⟩⟩

/-- Block gaps of an ordinary object persist to any larger ordinary object with the same
first joint: the joint dart pair is unchanged. -/
theorem blockGap_mono {S U : Finset V} {a : V} {d : ℕ} {L : ℝ} {w : Mom d}
    {κ : D → (Fin d → ℤ)} {r : Mom d} (hSU : S ⊆ U) (hr : M.IsBlockGap L w κ S a r) :
    M.IsBlockGap L w κ U a r := by
  obtain ⟨x, y, hx, hy, hgx, hgy, hox, hoy, he⟩ := hr
  exact ⟨x, y, hx, hy, ⟨hSU hgx.1, hSU hgx.2⟩, ⟨hSU hgy.1, hSU hgy.2⟩, hox, hoy, he⟩

theorem oneJointUnionObject_hasGapKind {S T : Finset V} {a b c : V} {n m : ℕ}
    (hS : Chain M S a c n) (hT : Chain M T c b m) (hST : S ∩ T = {c})
    (hB : M.IsBlock (S ∪ T) a b) {d : ℕ} {L γ η : ℝ} {w : Mom d} {κ : D → (Fin d → ℤ)}
    {kind : Molecule.GapKind}
    (hP : ∃ r, M.IsBlockGap L w κ S a r ∧ Molecule.gapKind L γ η r = kind) :
    (oneJointUnionObject hS hT hST hB).HasGapKind L γ η w κ kind := by
  obtain ⟨r, hr, hk⟩ := hP
  exact ⟨r, blockGap_mono subset_union_left hr, hk⟩

end WaveTurbulence.LGSpine.SourceVine

namespace WaveTurbulence.LGSpine
open SourceVine Finset

/-- A selected object is not strictly below an eligible non-omitted ordinary object. -/
theorem selected_not_strictly_below_vc {w d : ℕ} {G : Garden w} {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} {F : Set (GBranch G.tree)} {omitted : Set (Finset (GBranch G.tree))}
    {collection : Set (Object G.molecule)}
    (hc : IsSourceSecondCollection G L γ η base κ F omitted collection)
    {P U : Object G.molecule} (hP : P ∈ collection)
    (hU : eligibleSecondObject G L γ η base κ F U) (hUo : U.atoms ∉ omitted)
    (hUvc : ∃ h, U.shape = .vc h) (hsub : P.atoms ⊆ U.atoms) : U.atoms ⊆ P.atoms := by
  obtain ⟨_, _, hmax⟩ := (hc.2.2 P).mp hP
  have hPU : P.IsContained U := by
    have hsub' := hsub
    rcases hUvc with ⟨h, hh⟩
    rcases P with ⟨A, x, y, Psh⟩
    rcases U with ⟨S, a, b, Ush⟩
    cases Psh <;> cases Ush
    · exact hsub'
    · cases hh
    · exact hsub'
    · cases hh
  exact Object.contained_atoms_subset _ _ (hmax U hU hUo hPU)

end WaveTurbulence.LGSpine
