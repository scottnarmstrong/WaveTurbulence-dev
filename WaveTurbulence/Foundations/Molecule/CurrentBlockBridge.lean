/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeDegreeCompat
public import WaveTurbulence.Foundations.Molecule.JointChildSlots
public import WaveTurbulence.Foundations.Molecule.VineTypeIIncidences

/-!
# Connected B2 blocks and the accepted degree-only auxiliary proofs

The source-facing IsBlock and IsVine predicates have the exact current
B2 bodies. Earlier CLCN and VINES proofs are copied under distinct
IsBlockDeg and IsVineDeg compatibility names. These lemmas discharge that
weaker degree premise from the current connected source predicates.
-/

public section
namespace WaveTurbulence.Molecpl
variable {V D : Type*} [DecidableEq V] [Fintype D] (M : Molecule V D)

/-- Current B2 blocks imply the degree data used by the accepted CLCN proofs. -/
theorem isBlock_degree {S : Finset V} {a b : V} (h : M.IsBlock S a b) : M.IsBlockDeg S a b := by
  rcases h with ⟨hS,ha,hb,hn,hoa,hia,hob,hib,hf,_hc⟩
  exact ⟨hS,ha,hb,hn,hoa,hia,hob,hib,hf⟩

/-- The degree and connectedness decomposition is exact, with no change of source semantics. -/
theorem isBlock_iff_degree_connected {S : Finset V} {a b : V} :
    M.IsBlock S a b ↔ M.IsBlockDeg S a b ∧ M.GroupConnected S := by
  constructor
  · intro h
    exact ⟨isBlock_degree M h,h.2.2.2.2.2.2.2.2.2⟩
  · rintro ⟨⟨hS,ha,hb,hn,hoa,hia,hob,hib,hf⟩,hc⟩
    exact ⟨hS,ha,hb,hn,hoa,hia,hob,hib,hf,hc⟩

/-- Current B2 vine realizations imply the degree-only compatibility realizations. -/
theorem isVine_degree [DecidableEq D] {X : VineType} {S : Finset V} {a b : V} (h : M.IsVine X S a b) :
    M.IsVineDeg X S a b := ⟨isBlock_degree M h.1,h.2⟩

/-- The accepted type-I incidence extraction applies to the actual current B2 predicate. -/
theorem typeI_twoIncidences [DecidableEq D] {S : Finset V} {a b : V} (h : M.IsVine .I S a b) :
    Nonempty (Vine.TwoIncidences M a b) := Vine.typeI_twoIncidences h

end WaveTurbulence.Molecpl
