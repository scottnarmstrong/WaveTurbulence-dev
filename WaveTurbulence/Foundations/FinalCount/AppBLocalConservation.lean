/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBOutgoingSums
import Mathlib.Tactic

/-! # Local momentum and energy constraints in the actual figure labels -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

/-- The local tuple inherits the source's exact momentum equation. -/
theorem local_momentum {d : ℕ} (L : ℝ) (w : Mom d) (c : V → Mom d)
    (κ : D → (Fin d → ℤ)) (hκ : M.IsDecoration L w c κ)
    {v : V} (hv : v ∈ r.removedAtoms) :
    (∑ i : Fin P.edges.length,
      ((if M.atom (r.edge i).val = v then Molecule.kvec L w (r.localLabels κ) i else 0) -
        (if M.atom (M.mate (r.edge i).val) = v then Molecule.kvec L w (r.localLabels κ) i else 0))) = c v := by
  have hs := r.sum_dartsAt_local_edges hv
    (fun x => M.dartSign x • Molecule.kvec L w κ x) (fun x => by
      rw [Degen.dartSign_mate,Molecule.kvec,hκ.1 x,neg_smul]
      rfl)
  rw [hκ.2 v (r.removedAtoms_subset hv)] at hs
  rw [hs]
  apply sum_congr rfl
  intro i hi
  have ho : M.out (r.edge i).val = true := (mem_filter.mp (mem_filter.mp (r.edge i).property).1).2
  simp only [Molecule.dartSign,ho,ite_true,one_smul,Molecule.kvec,localLabels]

/-- The local tuple inherits the actual restricted energy window with
unchanged tolerance. -/
theorem local_energy {d : ℕ} (L γ δ : ℝ) (w : Mom d) (c : V → Mom d)
    (β : V → ℝ) (k0 : D → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hres : M.IsRestricted L γ δ w β k0 κ)
    {v : V} (hv : v ∈ r.removedAtoms) :
    |(∑ i : Fin P.edges.length,
      ((if M.atom (r.edge i).val = v then ‖Molecule.kvec L w (r.localLabels κ) i‖^2 else 0) -
        (if M.atom (M.mate (r.edge i).val) = v then ‖Molecule.kvec L w (r.localLabels κ) i‖^2 else 0))) - β v| ≤
      δ⁻¹*L^(-2*γ) := by
  have hs := r.sum_dartsAt_local_edges hv
    (fun x => M.dartSign x * ‖Molecule.kvec L w κ x‖^2) (fun x => by
      rw [Degen.dartSign_mate,Molecule.kvec,hκ.1 x,neg_mul]
      rfl)
  have he : M.Gamma L w κ v = ∑ i : Fin P.edges.length,
      ((if M.atom (r.edge i).val = v then ‖Molecule.kvec L w (r.localLabels κ) i‖^2 else 0) -
        (if M.atom (M.mate (r.edge i).val) = v then ‖Molecule.kvec L w (r.localLabels κ) i‖^2 else 0)) := by
    refine hs.trans ?_
    apply sum_congr rfl
    intro i hi
    have ho : M.out (r.edge i).val = true := (mem_filter.mp (mem_filter.mp (r.edge i).property).1).2
    simp only [Molecule.dartSign,ho,ite_true,one_mul,Molecule.kvec,localLabels]
  rw [← he]
  exact hres.1 v (r.removedAtoms_subset hv)

/-- Localizing balls are inherited coordinate by coordinate, with no
radius enlargement in the actual outgoing tuple. -/
theorem local_spatial {d : ℕ} (L γ δ : ℝ) (w : Mom d) (β : V → ℝ)
    (k0 : D → Mom d) (κ : D → (Fin d → ℤ))
    (hres : M.IsRestricted L γ δ w β k0 κ) (i : Fin P.edges.length) :
    ‖Molecule.kvec L w (r.localLabels κ) i-k0 (r.edge i).val‖ ≤ 1 :=
  hres.2 (r.edge i).val

end AppbRealization
end WaveTurbulence.Mole
