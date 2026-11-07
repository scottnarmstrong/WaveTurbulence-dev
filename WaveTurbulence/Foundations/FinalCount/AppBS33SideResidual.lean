/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBClosedSideOperations
public import WaveTurbulence.Foundations.FinalCount.AppBOutgoingEndpoint
import Mathlib.Tactic

/-! # Exact residual divergence on the 35 side of split 3S3 -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_s33_removed_sum_at_side {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) (ht : AppbS33SplitTopology M r)
    {v : V} (hv : v ∈ appbS33Side r)
    {E : Type*} [AddCommGroup E] (g : D → E) (hg : ∀ x,g (M.mate x) = -g x) :
    (∑ x ∈ Degen.removedDartsAt M r.removedAtoms v,g x) =
      (if r.vertex 3 = v then (appbIncidenceSign M (r.vertex 3) (r.edge ⟨1,by decide⟩).val : ℤ) •
        g (r.edge ⟨1,by decide⟩).val else 0)+
      (if r.vertex 5 = v then (appbIncidenceSign M (r.vertex 5) (r.edge ⟨3,by decide⟩).val : ℤ) •
        g (r.edge ⟨3,by decide⟩).val else 0) := by
  obtain ⟨hn1,hn2,hm3,hn4,hm5,hn6⟩ := appb_s33_side_labels_topology M r ht
  have h1 : r.vertex 1 ≠ v := fun he => hn1 (he.symm ▸ hv)
  have h2 : r.vertex 2 ≠ v := fun he => hn2 (he.symm ▸ hv)
  have h4 : r.vertex 4 ≠ v := fun he => hn4 (he.symm ▸ hv)
  have h6 : r.vertex 6 ≠ v := fun he => hn6 (he.symm ▸ hv)
  have hkeep := ((Degen.mem_residualComponent M r.removedAtoms (r.vertex 3) v).mp hv).2.1
  rw [r.sum_removedDartsAt_local_edges hkeep g hg]
  change (∑ i : Fin 5,((if M.atom (r.edge i).val = v then g (r.edge i).val else 0)-
    (if M.atom (M.mate (r.edge i).val) = v then g (r.edge i).val else 0))) = _
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  change ((if M.atom (r.edge ⟨0,by decide⟩).val = v then g (r.edge ⟨0,by decide⟩).val else 0)-(if M.atom (M.mate (r.edge ⟨0,by decide⟩).val) = v then g (r.edge ⟨0,by decide⟩).val else 0))+(((if M.atom (r.edge ⟨1,by decide⟩).val = v then g (r.edge ⟨1,by decide⟩).val else 0)-(if M.atom (M.mate (r.edge ⟨1,by decide⟩).val) = v then g (r.edge ⟨1,by decide⟩).val else 0))+(((if M.atom (r.edge ⟨2,by decide⟩).val = v then g (r.edge ⟨2,by decide⟩).val else 0)-(if M.atom (M.mate (r.edge ⟨2,by decide⟩).val) = v then g (r.edge ⟨2,by decide⟩).val else 0))+(((if M.atom (r.edge ⟨3,by decide⟩).val = v then g (r.edge ⟨3,by decide⟩).val else 0)-(if M.atom (M.mate (r.edge ⟨3,by decide⟩).val) = v then g (r.edge ⟨3,by decide⟩).val else 0))+(((if M.atom (r.edge ⟨4,by decide⟩).val = v then g (r.edge ⟨4,by decide⟩).val else 0)-(if M.atom (M.mate (r.edge ⟨4,by decide⟩).val) = v then g (r.edge ⟨4,by decide⟩).val else 0))+(0))))) = _
  rw [appb_outgoing_contribution_at_external M _ _ _ v (r.endpoints ⟨0,by decide⟩) h1,
    appb_outgoing_contribution_at_external M _ _ _ v (r.endpoints ⟨1,by decide⟩) h1,
    appb_outgoing_contribution_at_external M _ _ _ v (r.endpoints ⟨2,by decide⟩) h1,
    appb_outgoing_contribution_at_external M _ _ _ v (r.endpoints ⟨3,by decide⟩) h2,
    appb_outgoing_contribution_at_external M _ _ _ v (r.endpoints ⟨4,by decide⟩) h2]
  change (if r.vertex 2 = v then _ else (0 : E))+((if r.vertex 3 = v then _ else 0)+((if r.vertex 4 = v then _ else 0)+((if r.vertex 5 = v then _ else 0)+((if r.vertex 6 = v then _ else 0)+0)))) = _
  simp only [h2,h4,h6,ite_false,zero_add,add_zero]
  rfl

end WaveTurbulence.Mole
