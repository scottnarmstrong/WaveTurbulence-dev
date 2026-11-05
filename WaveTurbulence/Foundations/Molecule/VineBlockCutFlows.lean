/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineInducedFlows
public import WaveTurbulence.Foundations.Molecule.VineGapConservation
import Mathlib.Tactic

/-! # A cut separating the block joints carries exactly the block gap -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D E : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    [AddCommGroup E] [Module ℝ E]

/-- TARGET subsetvc, cut-flow identity: inside a block, every atomic cut
containing its first joint and excluding its second carries the first gap.
Only conservation at full-degree atoms is assumed. -/
theorem block_separating_cutFlow (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} (hB : M.IsBlock S a b)
    (k : D → E) (hk : ∀ x,k (M.mate x)=k x)
    (hc : ∀ v ∈ M.atoms,M.deg v=4 → ∑ x ∈ M.dartsAt v,M.dartSign x • k x=0)
    {r : E} (hr : IsGroupGap M S k a r)
    (T : Finset V) (hTS : T ⊆ S) (ha : a ∈ T) (hb : b ∉ T) :
    (∑ x ∈ boundary (Mole.induced M S) T,
      (Mole.induced M S).dartSign x • k x.1)=r := by
  have hzero : ∀ v ∈ T,v ≠ a → groupFlow M S k v=0 := by
    intro v hv hne
    have hvb : v ≠ b := fun he => hb (he ▸ hv)
    have hd := hB.2.2.2.2.2.2.2.2.1 v (hTS hv) hne hvb
    rw [groupFlow_eq_full M hM (hTS hv) hB.1 hd]
    apply hc v (hB.1 (hTS hv))
    have hle := Mole.degIn_le_deg M S v
    have hfour := Mole.deg_le_four M hM (hB.1 (hTS hv))
    omega
  calc
    _ = ∑ v ∈ T,groupFlow M S k v :=
      (sum_conservation_boundary (Mole.induced M S) T (fun x => k x.1)
        (groupFlow M S k) (fun x => hk x.1)
        (fun v _hv => induced_localFlow M S k v)).symm
    _ = groupFlow M S k a := sum_eq_single a (fun v hv hne => hzero v hv hne)
      (fun h => False.elim (h ha))
    _ = r := (groupGap_eq_flow M (Mole.block_joint_degrees M hB).1 hr).symm

end WaveTurbulence.Vine
