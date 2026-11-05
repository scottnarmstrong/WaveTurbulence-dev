/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineEraseBondDegrees
public import WaveTurbulence.Foundations.Molecule.VineEraseBondMolecule
public import WaveTurbulence.Foundations.Molecule.VineLatticeGaps
import Mathlib.Tactic

/-! # Source decorations restricted to a designated adjoint -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Atoms incident to a deleted nonloop bond have degree at most three
after deletion. Thus no new full atom is a deleted endpoint. -/
theorem eraseBond_endpoint_degree_le_three (M : Molecule V D) (hM : M.IsMolecule) (e : D)
    (hne : M.atom e ≠ M.atom (M.mate e)) :
    (Mole.eraseBond M e).deg (M.atom e) ≤ 3 ∧
      (Mole.eraseBond M e).deg (M.atom (M.mate e)) ≤ 3 := by
  have h1 := eraseBond_degree_endpoint M e hne
  have h2 := eraseBond_degree_endpoint M (M.mate e) (by rw [M.mate_mate]; exact hne.symm)
  rw [eraseBond_mate_degree] at h2
  have hb1 := Mole.deg_le_four M hM (M.atom_mem e)
  have hb2 := Mole.deg_le_four M hM (M.atom_mem (M.mate e))
  constructor <;> omega

/-- Every nonendpoint retains its exact signed local momentum sum. -/
theorem eraseBond_local_sum {W : Type*} [AddCommGroup W] [Module ℝ W]
    (M : Molecule V D) (e : D) (v : V) (h1 : M.atom e ≠ v) (h2 : M.atom (M.mate e) ≠ v)
    (k : D → W) :
    (∑ d ∈ (Mole.eraseBond M e).dartsAt v,(Mole.eraseBond M e).dartSign d • k d.1)=
      ∑ d ∈ M.dartsAt v,M.dartSign d • k d := by
  apply sum_bij (fun d _hd => d.1)
  · intro d hd
    exact (Mole.mem_dartsAt M v d.1).mpr ((Mole.mem_dartsAt (Mole.eraseBond M e) v d).mp hd)
  · intro d _hd f _hf he
    exact Subtype.ext he
  · intro d hd
    have hdv := (Mole.mem_dartsAt M v d).mp hd
    have hde : d ≠ e := by intro he; subst d; exact h1 hdv
    have hdm : d ≠ M.mate e := by intro he; subst d; exact h2 hdv
    exact ⟨⟨d,hde,hdm⟩,(Mole.mem_dartsAt (Mole.eraseBond M e) v _).mpr hdv,rfl⟩
  · intro d _hd
    rfl

/-- Restricting source labels to an adjoint produces an actual decoration
with adjusted endpoint defects. All degree-four defects remain zero; the
new defect function is the actual signed local sum, not an assumed balance. -/
theorem eraseBond_decoration_exists {d : ℕ} (M : Molecule V D) (hM : M.IsMolecule)
    (e : D) (hne : M.atom e ≠ M.atom (M.mate e))
    (L : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hc : ∀ v ∈ M.atoms,M.deg v=4 → c v=0) :
    ∃ c', (Mole.eraseBond M e).IsDecoration L w c' (fun z => κ z.1) ∧
      ∀ v ∈ (Mole.eraseBond M e).atoms,(Mole.eraseBond M e).deg v=4 → c' v=0 := by
  let N := Mole.eraseBond M e
  let c' : V → Mom d := fun v => ∑ z ∈ N.dartsAt v,N.dartSign z • Molecule.kvec L w (fun z => κ z.1) z
  refine ⟨c',⟨?_,fun _v _hv => rfl⟩,?_⟩
  · intro z
    exact hκ.1 z.1
  · intro v hv hd
    change N.deg v=4 at hd
    have hend := eraseBond_endpoint_degree_le_three M hM e hne
    have hv1 : M.atom e ≠ v := by intro he; have hh := he ▸ hend.1; change N.deg v ≤ 3 at hh; omega
    have hv2 : M.atom (M.mate e) ≠ v := by intro he; have hh := he ▸ hend.2; change N.deg v ≤ 3 at hh; omega
    have hdeg : M.deg v=4 := by
      have hl := (eraseBond_degree_le M e v).2.2
      have hu := Mole.deg_le_four M hM hv
      change N.deg v ≤ M.deg v at hl
      omega
    change (∑ z ∈ N.dartsAt v,N.dartSign z • Molecule.kvec L w κ z.1)=0
    rw [eraseBond_local_sum M e v hv1 hv2]
    exact (hκ.2 v hv).trans (hc v hv hdeg)

end WaveTurbulence.Vine
