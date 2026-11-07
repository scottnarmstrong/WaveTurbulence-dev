/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBRemovedOutgoingSums
public import WaveTurbulence.Foundations.FinalCount.AppBIncidenceSigns
public import WaveTurbulence.Foundations.FinalCount.AppBD33CutData
import Mathlib.Tactic

/-! # Removed local divergence expressed at the surviving boundary endpoints -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_outgoing_contribution_at_external (M : Molecule V D) (x : D) (a b v : V)
    (he : M.ends x = s(a,b)) (ha : a ≠ v) {E : Type*} [AddCommGroup E] (A : E) :
    ((if M.atom x = v then A else 0)-(if M.atom (M.mate x) = v then A else 0)) =
      if b = v then (appbIncidenceSign M b x : ℤ) • A else 0 := by
  rcases Sym2.eq_iff.mp he with h | h
  all_goals by_cases hb : b = v
  all_goals simp [h.1,h.2,ha,hb,appbIncidenceSign]

theorem appb_d33_removed_sum_at_survivor {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33.pattern) {v : V} (hv : v ∉ r.removedAtoms)
    {E : Type*} [AddCommGroup E] (g : D → E) (hg : ∀ x,g (M.mate x) = -g x) :
    (∑ x ∈ Degen.removedDartsAt M r.removedAtoms v,g x) =
      (if r.vertex 3 = v then (appbIncidenceSign M (r.vertex 3) (r.edge ⟨2,by decide⟩).val : ℤ) •
        g (r.edge ⟨2,by decide⟩).val else 0)+
      (if r.vertex 4 = v then (appbIncidenceSign M (r.vertex 4) (r.edge ⟨3,by decide⟩).val : ℤ) •
        g (r.edge ⟨3,by decide⟩).val else 0) := by
  have h1 : r.vertex 1 ≠ v := fun he => hv (he ▸ mem_image_of_mem _ (show 1 ∈ AppbPatternKind.d33.pattern.removed by decide))
  have h2 : r.vertex 2 ≠ v := fun he => hv (he ▸ mem_image_of_mem _ (show 2 ∈ AppbPatternKind.d33.pattern.removed by decide))
  rw [r.sum_removedDartsAt_local_edges hv g hg]
  change (∑ i : Fin 4,((if M.atom (r.edge i).val = v then g (r.edge i).val else 0)-
    (if M.atom (M.mate (r.edge i).val) = v then g (r.edge i).val else 0))) = _
  rw [Fin.sum_univ_four]
  change (((if M.atom (r.edge ⟨0,by decide⟩).val = v then g (r.edge ⟨0,by decide⟩).val else 0)-
      (if M.atom (M.mate (r.edge ⟨0,by decide⟩).val) = v then g (r.edge ⟨0,by decide⟩).val else 0))+
    ((if M.atom (r.edge ⟨1,by decide⟩).val = v then g (r.edge ⟨1,by decide⟩).val else 0)-
      (if M.atom (M.mate (r.edge ⟨1,by decide⟩).val) = v then g (r.edge ⟨1,by decide⟩).val else 0)))+
    ((if M.atom (r.edge ⟨2,by decide⟩).val = v then g (r.edge ⟨2,by decide⟩).val else 0)-
      (if M.atom (M.mate (r.edge ⟨2,by decide⟩).val) = v then g (r.edge ⟨2,by decide⟩).val else 0))+
    ((if M.atom (r.edge ⟨3,by decide⟩).val = v then g (r.edge ⟨3,by decide⟩).val else 0)-
      (if M.atom (M.mate (r.edge ⟨3,by decide⟩).val) = v then g (r.edge ⟨3,by decide⟩).val else 0)) = _
  rw [appb_outgoing_contribution_at_external M _ _ _ v (r.endpoints ⟨0,by decide⟩) h1,
    appb_outgoing_contribution_at_external M _ _ _ v (r.endpoints ⟨1,by decide⟩) h1,
    appb_outgoing_contribution_at_external M _ _ _ v (r.endpoints ⟨2,by decide⟩) h1,
    appb_outgoing_contribution_at_external M _ _ _ v (r.endpoints ⟨3,by decide⟩) h2]
  change (if r.vertex 2 = v then _ else (0 : E))+
    (if r.vertex 2 = v then _ else 0)+
    (if r.vertex 3 = v then (appbIncidenceSign M (r.vertex 3) (r.edge ⟨2,by decide⟩).val : ℤ) •
      g (r.edge ⟨2,by decide⟩).val else 0)+
    (if r.vertex 4 = v then (appbIncidenceSign M (r.vertex 4) (r.edge ⟨3,by decide⟩).val : ℤ) •
      g (r.edge ⟨3,by decide⟩).val else 0) = _
  simp only [h2,ite_false,zero_add]

end WaveTurbulence.Mole
