/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.GluePhase

/-!
# The full chart of a cell decomposition (M4 Theorem C)

`Decomp.toFullChart`: every cell decomposition of a block of a molecule gives a normal de-indexed full chart, whose
paired slots and core triple are exactly the atom sets of its pair cells and of its core cell
(`Decomp.chartGroups_toFullChart`).
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Chart

open Finset VineParamContract

namespace Decomp

variable {V D : Type*} [DecidableEq V] [Fintype D] {M : Molecule V D} {S : Finset V} {a b : V}
variable (Dc : Decomp M S a b)

theorem nodeRes_slot (hB : M.IsBlock S a b) {d : ℕ} (g r : Mom d) (x : Fin (nshape Dc.m).n → Mom d)
    (i : Fin (nshape Dc.m).n) (hi : i ≠ (nshape Dc.m).x0) :
    nodeResonance (Dc.indexing hB) (decodeWith Dc.F Dc.C g r x) g r i =
      energy M S (decodeWith Dc.F Dc.C g r x) ((Dc.indexing hB).atom i).1 := by
  unfold nodeResonance
  change _ + (if i = (nshape Dc.m).x0 then ‖g‖ ^ 2 - ‖g - r‖ ^ 2 else 0) = _
  simp [hi]

/-- The atom sets of the pair cells and of the core cell. -/
noncomputable def cellGroups : Finset (Finset V) :=
  (univ.image fun j : Fin Dc.m =>
      ({(Dc.emb (.inl j)).atom (a1 (k := Dc.k) j), (Dc.emb (.inl j)).atom (a0 (k := Dc.k) j)} : Finset V)) ∪
    {{(Dc.emb Cell.core).atom (cA (m := Dc.m) (k := Dc.k) 0), (Dc.emb Cell.core).atom (cA (m := Dc.m) (k := Dc.k) 1), (Dc.emb Cell.core).atom (cA (m := Dc.m) (k := Dc.k) 2)}}

section Phases

variable (hB : M.IsBlock S a b) {d : ℕ} (g r : Mom d) (x : Fin (nshape Dc.m).n → Mom d)
include hB

theorem rung_t (j : Fin Dc.m) :
    nodeResonance (Dc.indexing hB) (decodeWith Dc.F Dc.C g r x) g r ((nshape Dc.m).xSlot j) =
      2 * inner ℝ (x ((nshape Dc.m).xSlot j)) (x ((nshape Dc.m).ySlot j)) +
        2 * inner ℝ r (((Dc.cfg (.inl j)).ζ 0 : ℝ) • x ((nshape Dc.m).xSlot j) +
          ((Dc.cfg (.inl j)).ζ 1 : ℝ) • x ((nshape Dc.m).ySlot j) + ((Dc.cfg (.inl j)).ζ 2 : ℝ) • r) := by
  rw [Dc.nodeRes_slot hB g r x _ (Dc.xSlot_ne j), Dc.atom_xSlot hB, Dc.energy_cell, Dc.zvec_pair]
  have hg : (Dc.cfg (.inl j)).gram (a1 (k := Dc.k) j) = tTarget (Dc.cfg (.inl j)).ζ := (Dc.pairOK j).2.1
  rw [hg]
  exact quad_tTarget _ _ _ _

theorem rung_s (j : Fin Dc.m) :
    nodeResonance (Dc.indexing hB) (decodeWith Dc.F Dc.C g r x) g r ((nshape Dc.m).ySlot j) =
      -2 * inner ℝ (x ((nshape Dc.m).xSlot j)) (x ((nshape Dc.m).ySlot j)) := by
  rw [Dc.nodeRes_slot hB g r x _ (Dc.ySlot_ne j), Dc.atom_ySlot hB, Dc.energy_cell, Dc.zvec_pair]
  have hg : (Dc.cfg (.inl j)).gram (a0 (k := Dc.k) j) = sTarget := (Dc.pairOK j).1
  rw [hg]
  exact quad_sTarget _ _ _

theorem core_energy (c : Fin 3) :
    nodeResonance (Dc.indexing hB) (decodeWith Dc.F Dc.C g r x) g r ((nshape Dc.m).uSlot rfl c) =
      LocalChart.quad ((Dc.cfg Cell.core).gram (cA (m := Dc.m) (k := Dc.k) c)) ![x ((nshape Dc.m).uSlot rfl 0),
        x ((nshape Dc.m).uSlot rfl 1), x ((nshape Dc.m).uSlot rfl 2), r] := by
  rw [Dc.nodeRes_slot hB g r x _ (Dc.uSlot_ne c), Dc.atom_uSlot hB, Dc.energy_cell, Dc.zvec_core]
  rfl

theorem core_first :
    nodeResonance (Dc.indexing hB) (decodeWith Dc.F Dc.C g r x) g r ((nshape Dc.m).uSlot rfl 0) =
      2 * (((toUnit (Dc.cfg Cell.core).σ₁ : ℤˣ) : ℤ) : ℝ) *
        inner ℝ (x ((nshape Dc.m).uSlot rfl 0)) (x ((nshape Dc.m).uSlot rfl 1)) := by
  rw [Dc.core_energy hB g r x 0]
  have hg : (Dc.cfg Cell.core).gram (cA (m := Dc.m) (k := Dc.k) 0) = aTarget (Dc.cfg Cell.core).σ₁ := Dc.coreOK.1
  rw [hg, toUnit_val Dc.coreOK.2.2.2.1]
  exact quad_aTarget _ _ _ _ _

theorem core_second :
    nodeResonance (Dc.indexing hB) (decodeWith Dc.F Dc.C g r x) g r ((nshape Dc.m).uSlot rfl 1) =
      2 * (((toUnit (Dc.cfg Cell.core).σ₁ : ℤˣ) : ℤ) : ℝ) * (if (Dc.cfg Cell.core).lin then
          inner ℝ (x ((nshape Dc.m).uSlot rfl 0)) (x ((nshape Dc.m).uSlot rfl 2))
        else (((toUnit (Dc.cfg Cell.core).σ₂ : ℤˣ) : ℤ) : ℝ) * inner ℝ (x ((nshape Dc.m).uSlot rfl 2))
          (x ((nshape Dc.m).uSlot rfl 0) + x ((nshape Dc.m).uSlot rfl 1) - x ((nshape Dc.m).uSlot rfl 2))) := by
  rw [Dc.core_energy hB g r x 1]
  have hg : (Dc.cfg Cell.core).gram (cA (m := Dc.m) (k := Dc.k) 1) = bTarget (Dc.cfg Cell.core).lin (Dc.cfg Cell.core).σ₁
      (Dc.cfg Cell.core).σ₂ := Dc.coreOK.2.1
  rw [hg, toUnit_val Dc.coreOK.2.2.2.1, toUnit_val Dc.coreOK.2.2.2.2.1]
  exact quad_bTarget _ _ _ _ _ _ _

theorem core_sum :
    (∑ c : Fin 3, nodeResonance (Dc.indexing hB) (decodeWith Dc.F Dc.C g r x) g r ((nshape Dc.m).uSlot rfl c)) =
      2 * inner ℝ r (((Dc.cfg Cell.core).ξ 0 : ℝ) • x ((nshape Dc.m).uSlot rfl 0) +
        ((Dc.cfg Cell.core).ξ 1 : ℝ) • x ((nshape Dc.m).uSlot rfl 1) +
        ((Dc.cfg Cell.core).ξ 2 : ℝ) • x ((nshape Dc.m).uSlot rfl 2) + ((Dc.cfg Cell.core).ξ 3 : ℝ) • r) := by
  simp only [Dc.core_energy hB g r x]
  rw [Fin.sum_univ_three, ← quad_add, ← quad_add]
  have := LocalChart.quad_eq_of_symm (m := 4)
    (G := fun i j : Fin 4 => (Dc.cfg Cell.core).gram (cA (m := Dc.m) (k := Dc.k) 0) i j +
      (Dc.cfg Cell.core).gram (cA (m := Dc.m) (k := Dc.k) 1) i j +
      (Dc.cfg Cell.core).gram (cA (m := Dc.m) (k := Dc.k) 2) i j)
    (H := sumTarget (Dc.cfg Cell.core).ξ) (fun i j => Dc.coreOK.2.2.1 i j)
    ![x ((nshape Dc.m).uSlot rfl 0), x ((nshape Dc.m).uSlot rfl 1), x ((nshape Dc.m).uSlot rfl 2), r]
  rw [quad_sumTarget] at this
  exact this

end Phases

/-- **M4 Theorem C, from a cell decomposition**: the full chart. -/
noncomputable def toFullChart (hM : M.IsMolecule) (hB : M.IsBlock S a b) : FullChart M false S a b :=
  (Dc.toChartData hM hB).toFullChart hM hB Dc.junction (fun h => absurd h Bool.false_ne_true)
    (Dc.rung_bonds hB) (fun j => (Dc.cfg (.inl j)).ζ) (fun j c => (Dc.pairOK j).2.2.1 c)
    (fun h => absurd h Bool.false_ne_true)
    (Dc.cfg Cell.core).lin (toUnit (Dc.cfg Cell.core).σ₁) (toUnit (Dc.cfg Cell.core).σ₂) (Dc.cfg Cell.core).ξ
    (fun c => Dc.coreOK.2.2.2.2.2.1 c)
    (fun d g r x => Dc.joint_phase hB d g r x)
    (fun _ g r x j => Dc.rung_t hB g r x j)
    (fun _ g r x j => Dc.rung_s hB g r x j)
    (fun _ _ g r x => Dc.core_first hB g r x)
    (fun _ _ g r x => Dc.core_second hB g r x)
    (fun _ _ g r x => Dc.core_sum hB g r x)

theorem toFullChart_atom (hM : M.IsMolecule) (hB : M.IsBlock S a b) (i : Fin (nshape Dc.m).n) :
    ((Dc.toFullChart hM hB).indexing.atom i).1 = ((Dc.indexing hB).atom i).1 := rfl

theorem chartGroups_toFullChart (hM : M.IsMolecule) (hB : M.IsBlock S a b) :
    chartGroups (Dc.toFullChart hM hB) = Dc.cellGroups := by
  unfold chartGroups cellGroups
  simp only [dite_true]
  congr 1
  · apply Finset.image_congr
    intro j _
    have e1 := Dc.atom_xSlot hB j
    have e2 := Dc.atom_ySlot hB j
    exact congrArg₂ (fun u v => ({u, v} : Finset V)) e1 e2
  · have e0 := Dc.atom_uSlot hB 0
    have e1 := Dc.atom_uSlot hB 1
    have e2 := Dc.atom_uSlot hB 2
    show ({{((Dc.indexing hB).atom ((nshape Dc.m).uSlot rfl 0)).1, ((Dc.indexing hB).atom
      ((nshape Dc.m).uSlot rfl 1)).1, ((Dc.indexing hB).atom ((nshape Dc.m).uSlot rfl 2)).1}} :
        Finset (Finset V)) = _
    rw [e0, e1, e2]

end Decomp

end WaveTurbulence.TVine.Chart
