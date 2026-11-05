/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSlotPorts
public import WaveTurbulence.Foundations.Molecule.VineAllocatedReduction
public import WaveTurbulence.Foundations.Molecule.VineHyperEmptySequence
import Mathlib.Tactic

/-! # Both absent old endpoint pairs exclude an entire source slot from a hyper-block -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A source slot has no selected fresh atoms when both old endpoint pairs
are absent. All incidence and allocation data are obtained from the actual
outer vine realization, including the zero-extra-rung case. -/
theorem hyperBlock_empty_slot_from_ports (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    {A : Finset V} {x y : V} (hH : Mole.IsHyperBlock M A x y)
    (pre post : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ)
    (hloc : X.template.slots.zip R.k=pre++(s,k)::post)
    (hports : ∀ v ∈ S,R.f v=s.1.1 ∨ R.f v=s.2.1 ∨ R.f v=s.1.2 ∨ R.f v=s.2.2 → v ∉ A) :
    let N := (pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n
    ∀ v ∈ S,N ≤ R.f v → R.f v<N+2*k → v ∉ A := by
  obtain ⟨Q,hmem,hp,hlabels⟩ := R.has_rungSequence_ports pre post s k hloc
  dsimp only at hlabels ⊢
  have hu0 := hports (Q.u 0) (hmem 0).1 (Or.inl hp.1)
  have hv0 := hports (Q.v 0) (hmem 0).2 (Or.inr (Or.inl hp.2.1))
  have huN := hports (Q.u (k+1)) (hmem (k+1)).1 (Or.inr (Or.inr (Or.inl hp.2.2.1)))
  have hvN := hports (Q.v (k+1)) (hmem (k+1)).2 (Or.inr (Or.inr (Or.inr hp.2.2.2)))
  have hempty := hyperBlock_empty_ended_sequence M hM hH Q hu0 hv0 huN hvN
  intro v hv hlo hhi
  obtain ⟨i,hi,hin,he⟩ := allocatedSequence_covers M S R.f R.injOn Q
    (fun i hi hin => ⟨(hmem i).1,(hmem i).2,hlabels i hi hin⟩) hv hlo hhi
  rcases he with rfl | rfl
  · exact (hempty i hi hin).1
  · exact (hempty i hi hin).2

end WaveTurbulence.Vine
