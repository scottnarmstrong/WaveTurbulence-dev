/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBOutgoingEndpoint
public import WaveTurbulence.Foundations.FinalCount.AppBLocalCompletion
import Mathlib.Tactic

/-! # Explicit two-boundary residual parameters for double-pair reinsertion -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_d33_residual_momentum {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33.pattern) {d : ℕ} (L : ℝ) (w : Mom d)
    (c : V → Mom d) (κ : D → (Fin d → ℤ)) (hκ : ∀ x,κ (M.mate x) = κ x)
    {v : V} (hv : v ∉ r.removedAtoms) :
    Degen.residualMomentum M r.removedAtoms L w c κ v = c v-
      (if r.vertex 3 = v then (appbIncidenceSign M (r.vertex 3) (r.edge ⟨2,by decide⟩).val : ℤ) •
        Molecule.kvec L w κ (r.edge ⟨2,by decide⟩).val else 0)-
      (if r.vertex 4 = v then (appbIncidenceSign M (r.vertex 4) (r.edge ⟨3,by decide⟩).val : ℤ) •
        Molecule.kvec L w κ (r.edge ⟨3,by decide⟩).val else 0) := by
  have hs := appb_d33_removed_sum_at_survivor r hv (fun x => M.dartSign x • Molecule.kvec L w κ x)
    (fun x => by rw [Degen.dartSign_mate,Molecule.kvec,hκ x,neg_smul]; rfl)
  have ho (i : Fin AppbPatternKind.d33.pattern.edges.length) : M.out (r.edge i).val = true :=
    (mem_filter.mp (mem_filter.mp (r.edge i).property).1).2
  simp only [Molecule.dartSign,ho,ite_true,one_smul] at hs
  unfold Degen.residualMomentum Molecule.dartSign
  rw [hs]
  abel

theorem appb_d33_residual_energy {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33.pattern) {d : ℕ} (L : ℝ) (w : Mom d)
    (β : V → ℝ) (κ : D → (Fin d → ℤ)) (hκ : ∀ x,κ (M.mate x) = κ x)
    {v : V} (hv : v ∉ r.removedAtoms) :
    Degen.residualEnergy M r.removedAtoms L w β κ v = β v-
      (if r.vertex 3 = v then (appbIncidenceSign M (r.vertex 3) (r.edge ⟨2,by decide⟩).val : ℤ)*
        ‖Molecule.kvec L w κ (r.edge ⟨2,by decide⟩).val‖^2 else 0)-
      (if r.vertex 4 = v then (appbIncidenceSign M (r.vertex 4) (r.edge ⟨3,by decide⟩).val : ℤ)*
        ‖Molecule.kvec L w κ (r.edge ⟨3,by decide⟩).val‖^2 else 0) := by
  have hs := appb_d33_removed_sum_at_survivor r hv (fun x => M.dartSign x * ‖Molecule.kvec L w κ x‖^2)
    (fun x => by rw [Degen.dartSign_mate,Molecule.kvec,hκ x,neg_mul]; rfl)
  have ho (i : Fin AppbPatternKind.d33.pattern.edges.length) : M.out (r.edge i).val = true :=
    (mem_filter.mp (mem_filter.mp (r.edge i).property).1).2
  simp only [Molecule.dartSign,ho,ite_true,one_mul,zsmul_eq_mul] at hs
  unfold Degen.residualEnergy Molecule.dartSign
  rw [hs]
  ring

end WaveTurbulence.Mole
