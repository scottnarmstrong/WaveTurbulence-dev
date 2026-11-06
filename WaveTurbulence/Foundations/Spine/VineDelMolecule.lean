/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.VineDelTheorem
public import WaveTurbulence.Foundations.Molecule.VineInteriorConnected
public import WaveTurbulence.Foundations.Molecule.MoleculeConnectedBlocks
import Mathlib.Tactic
/-! # Deleting a nonjoint atom of an actual vine leaves a connected group -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Vine Finset

/-- TARGET defvine, DH23 Lemma 4.11 hypothesis: an interior atom of an actual vine does not
disconnect it. This is checked on every expanded template (`expand_connDel`). -/
theorem isVine_erase_connected {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (hV : M.IsVine X S a b) {v : V} (hvS : v ∈ S) (hva : v ≠ a) (hvb : v ≠ b) :
    Mole.GroupConnected M (S.erase v) := by
  classical
  obtain ⟨hB, ⟨R⟩⟩ := isVine_iff_realization.mp hV
  let n := (X.expand R.k).n
  let g : ℕ → V := fun i => if hi : i < n then (R.atomAt ⟨i, hi⟩).1 else a
  have hgm (i : ℕ) : g i ∈ S := by
    dsimp only [g]
    split_ifs with hi
    · exact (R.atomAt ⟨i, hi⟩).2
    · exact hB.2.1
  have hgl (i : ℕ) (hi : i < n) : R.f (g i) = i := by
    dsimp only [g]
    rw [dite_eq_left hi]
    exact R.label_atomAt ⟨i, hi⟩
  have hgf (u : V) (hu : u ∈ S) : g (R.f u) = u := by
    apply R.injOn (hgm _) hu
    exact hgl _ (mem_range.mp (R.image_eq ▸ mem_image_of_mem R.f hu))
  have hvl := mem_range.mp (R.image_eq ▸ mem_image_of_mem R.f hvS)
  have hv2 : 2 ≤ R.f v := by
    have hn : ¬ R.f v < 2 := by
      intro he
      have := (realization_index_lt_two_iff R hB hvS).mp he
      rcases this with h | h
      · exact hva h
      · exact hvb h
    omega
  have hconn := expand_connDel X R.k R.length_eq (R.f v) hv2 hvl
  have hedge (p q : ℕ) (hpq : FAdj (· ≠ R.f v) (fun _ => true) (X.expand R.k).bonds p q) :
      (Mole.induced M (S.erase v)).Adj (g p) (g q) := by
    have hadj : EdgeAdj (X.expand R.k).bonds p q := by
      rcases hpq.2.2 with ⟨h, _⟩ | ⟨h, _⟩
      · exact Or.inl h
      · exact Or.inr h
    have hb := (show EdgeBounded n (X.expand R.k).bonds from expand_endpoints X R.k).adj hadj
    have hgp : g p ∈ S.erase v := by
      refine mem_erase.mpr ⟨fun h => hpq.1 ?_, hgm p⟩
      rw [← hgl p hb.1, h]
    have hgq : g q ∈ S.erase v := by
      refine mem_erase.mpr ⟨fun h => hpq.2.1 ?_, hgm q⟩
      rw [← hgl q hb.2, h]
    apply R.subgroup_adj_of_edge (erase_subset v S) hgp hgq
    rw [hgl p hb.1, hgl q hb.2]
    exact hadj
  have lift {p q : ℕ} (hp : Relation.EqvGen (FAdj (· ≠ R.f v) (fun _ => true)
      (X.expand R.k).bonds) p q) :
      (Mole.induced M (S.erase v)).SameComponent (g p) (g q) := by
    induction hp with
    | rel u w huw => exact Relation.EqvGen.rel _ _ (hedge u w huw)
    | refl u => exact Relation.EqvGen.refl _
    | symm u w _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans u w z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  refine ⟨⟨a, mem_erase.mpr ⟨hva.symm, hB.2.1⟩⟩, ?_⟩
  intro u hu w hw
  obtain ⟨huv, huS⟩ := mem_erase.mp hu
  obtain ⟨hwv, hwS⟩ := mem_erase.mp hw
  have hul := mem_range.mp (R.image_eq ▸ mem_image_of_mem R.f huS)
  have hwl := mem_range.mp (R.image_eq ▸ mem_image_of_mem R.f hwS)
  have hne : ∀ z, z ∈ S → z ≠ v → R.f z ≠ R.f v := fun z hz hzv h => hzv (R.injOn hz hvS h)
  have hh := lift (hconn (R.f u) (R.f w) hul hwl (hne u huS huv) (hne w hwS hwv))
  simpa only [hgf u huS, hgf w hwS] using hh

end WaveTurbulence.LGSpine
