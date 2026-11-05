/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TypeIScenarios
public import WaveTurbulence.Foundations.Molecule.ScenarioCode
public import WaveTurbulence.Foundations.Molecule.ConnectedGeometryBridge

/-! # Vines inside actual gardens

TARGET Proposition molecpl, L1397--L1422. The main type-II result retains
the exact bond multiplicities and proves existence of exactly one printed
scenario for the chosen labels, up to the symmetry allowed by the source.
The all-type CL geometry supplies the common structural analogue for
normal vines. The theorem includes the m=1 type-II vine (F72).
-/

public section
namespace WaveTurbulence.Molecpl
open TTree
variable {w : ℕ} (G : Garden w)

/-- TARGET molecpl (2): exact adjacent bond counts and exactly one of (II-a)--(II-e). -/
theorem molecpl_typeII {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hV : G.molecule.IsVine .II S a b) (hCL : Mole.CLParentPattern G S a b) :
    ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ p ≠ a ∧ p ≠ b ∧ q ≠ a ∧ q ≠ b ∧
      G.molecule.bondsBetween b p = 1 ∧ G.molecule.bondsBetween b q = 1 ∧
      G.molecule.bondsBetween p q = 2 ∧ ∃! i : Fin 5, TypeIIScenario G a b p q i := by
  obtain ⟨p,hp,q,hq,hne,hpa,hpb,hqa,hqb,hbp,hbq,hpq,hs⟩ := typeII_scenarios G hV hCL
  have hex : ∃ i : Fin 5, TypeIIScenario G a b p q i := by
    rcases hs with h | h | h | h | h
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩
    · exact ⟨3,h⟩
    · exact ⟨4,h⟩
  obtain ⟨i,hi⟩ := hex
  exact ⟨p,hp,q,hq,hne,hpa,hpb,hqa,hqb,hbp,hbq,hpq,i,hi,
    fun j hj => typeII_scenarios_exclusive G hne hpb hj hi⟩

/-- The complete actual CL subtree geometry is common to all eight vine types. -/
theorem molecpl_CL {X : VineType} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hV : G.molecule.IsVine X S a b) (hCL : Mole.CLParentPattern G S a b) :
    Nonempty (Mole.CLGeometricData G S a b) := vine_CL_geometry G hV hCL

end WaveTurbulence.Molecpl
