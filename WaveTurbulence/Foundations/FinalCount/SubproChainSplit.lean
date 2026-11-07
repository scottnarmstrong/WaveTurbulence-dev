/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.VineChainBlock
public import WaveTurbulence.Foundations.Molecule.VineTwoJointSeparator
public import WaveTurbulence.Foundations.Molecule.VineVertexConnected
public import WaveTurbulence.Foundations.Molecule.MoleculeComponentPartitions
import Mathlib.Tactic

/-!
# S4-DISJ: splitting a vine chain at a cut atom

If a block `U` that is an actual vine chain from `a` to `b` is the union of two blocks `C` (joints `a`, `c`) and `C'` (joints `c`, `b`)
meeting only in `c`, then `C` and `C'` are themselves chains (`c` is a junction of the chain). Proof: induction on the chain; a vine has no
cut atom (`isVine_erase_connected`), and no path can cross the edge cut `C \ {c} | C' \ {c}`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Subpro
open WaveTurbulence Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Two blocks `C` (joints `a`, `c`) and `C'` (joints `c`, `b`) with union a block (joints `a`, `b`) and meeting in `c` are not
joined by a bond away from `c`. -/
theorem no_cross_of_blocks (M : Molecule V D) (hM : M.IsMolecule) {C C' U : Finset V} {a b c : V}
    (hC : M.IsBlock C a c) (hU : M.IsBlock U a b) (hUe : U = C ∪ C') (hi : C ∩ C' = {c}) :
    ∀ x ∈ C, x ≠ c → ∀ y ∈ C', y ≠ c → ¬ M.Adj x y := by
  intro x hx hxc y hy hyc ⟨z, hzx, hzy⟩
  have hCU : C ⊆ U := hUe ▸ subset_union_left
  have hC'U : C' ⊆ U := hUe ▸ subset_union_right
  have hzU : M.InGroup U z := ⟨hzx ▸ hCU hx, hzy ▸ hC'U hy⟩
  have hzC : M.InGroup C z := by
    by_cases hxa : x = a
    · subst hxa
      have hd1 := (Mole.block_joint_degrees M hC).1
      have hd2 := (Mole.block_joint_degrees M hU).1
      have hsub : (M.dartsAt x).filter (M.InGroup C) ⊆ (M.dartsAt x).filter (M.InGroup U) := by
        intro w hw
        have hw' := Finset.mem_filter.mp hw
        exact Finset.mem_filter.mpr ⟨hw'.1, hCU hw'.2.1, hCU hw'.2.2⟩
      have heq := Finset.eq_of_subset_of_card_le hsub (by
        change M.degIn U x ≤ M.degIn C x
        omega)
      have hzm : z ∈ (M.dartsAt x).filter (M.InGroup U) :=
        Finset.mem_filter.mpr ⟨(Mole.mem_dartsAt M x z).mpr hzx, hzU⟩
      rw [← heq] at hzm
      exact (Finset.mem_filter.mp hzm).2
    · have hint : M.degIn C x = 4 := hC.2.2.2.2.2.2.2.2.1 x hx hxa hxc
      have hdeg : M.deg x ≤ 4 := Mole.deg_le_four M hM (hC.1 hx)
      have hle : (M.dartsAt x).filter (M.InGroup C) ⊆ M.dartsAt x := Finset.filter_subset _ _
      have heq := Finset.eq_of_subset_of_card_le hle (by
        change M.deg x ≤ M.degIn C x
        omega)
      have hzm : z ∈ M.dartsAt x := (Mole.mem_dartsAt M x z).mpr hzx
      rw [← heq] at hzm
      exact (Finset.mem_filter.mp hzm).2
  have hyC : y ∈ C := hzy ▸ hzC.2
  have : y ∈ C ∩ C' := mem_inter.mpr ⟨hyC, hy⟩
  rw [hi] at this
  exact hyc (mem_singleton.mp this)


/-- A connected set avoiding `c` lies on one side of the cut `C \ {c} | C' \ {c}`. -/
theorem side_of_connected (M : Molecule V D) {C C' : Finset V} {c : V}
    (hno : ∀ x ∈ C, x ≠ c → ∀ y ∈ C', y ≠ c → ¬ M.Adj x y) {W : Finset V}
    (hW : W ⊆ (C ∪ C').erase c) (hconn : ∀ u ∈ W, ∀ v ∈ W, (Mole.induced M W).SameComponent u v)
    {u v : V} (hu : u ∈ W) (hv : v ∈ W) : u ∈ C.erase c ↔ v ∈ C.erase c := by
  have hW' : W ⊆ C.erase c ∪ C'.erase c := by
    intro x hx
    have hx' := hW hx
    rw [Finset.erase_union_distrib] at hx'
    exact hx'
  have hno' : ∀ p ∈ C.erase c, ∀ q ∈ C'.erase c, ¬ M.Adj p q := fun p hp q hq =>
    hno p (Finset.mem_of_mem_erase hp) (Finset.ne_of_mem_erase hp) q (Finset.mem_of_mem_erase hq)
      (Finset.ne_of_mem_erase hq)
  exact Mole.partition_path_side M (P := C.erase c) (Q := C'.erase c) (S := C.erase c ∪ C'.erase c) rfl hno'
    (Vine.induced_path_mono M hW' (hconn u hu v hv))

/-- **Chain splitting.** -/
theorem chain_split (M : Molecule V D) (hM : M.IsMolecule) {U : Finset V} {a b : V} {n : ℕ}
    (h : Vine.Chain M U a b n) :
    ∀ {C C' : Finset V} {c : V}, M.IsBlock U a b → C ∪ C' = U → C ∩ C' = {c} → a ∈ C → b ∈ C' →
      c ≠ a → c ≠ b → (∀ x ∈ C, x ≠ c → ∀ y ∈ C', y ≠ c → ¬ M.Adj x y) →
      (∃ i, Vine.Chain M C a c i) ∧ ∃ j, Vine.Chain M C' c b j := by
  induction h with
  | single hS =>
    rename_i U a b
    intro C C' c hU hcov hi ha hb hca hcb hno
    exfalso
    obtain ⟨X, hX⟩ := hS
    have hbC : b ∉ C := fun hbC => hcb (mem_singleton.mp (hi ▸ mem_inter.mpr ⟨hbC, hb⟩)).symm
    have hcC : c ∈ C := (mem_inter.mp (hi ▸ mem_singleton_self c)).1
    have hW : U.erase c ⊆ (C ∪ C').erase c := by rw [hcov]
    have hcon := Vine.isVine_erase_connected hX c
    have haU : a ∈ U.erase c := mem_erase.mpr ⟨hca.symm, hcov ▸ mem_union_left _ ha⟩
    have hbU : b ∈ U.erase c := mem_erase.mpr ⟨hcb.symm, hcov ▸ mem_union_right _ hb⟩
    have := (side_of_connected M hno hW hcon haU hbU).mp (mem_erase.mpr ⟨hca.symm, ha⟩)
    exact hbC (Finset.mem_of_mem_erase this)
  | @append S T a b' b n hS hT hi hne ih =>
    intro C C' c hU hcov hi' ha hb hca hcb hno
    obtain ⟨X, hX⟩ := hT
    have hSB : M.IsBlock S a b' := Vine.chain_prefix_isBlock M hM hS hX hi hU
    have hb'S : b' ∈ S := (Vine.chain_joints_mem hS).2
    have haS : a ∈ S := (Vine.chain_joints_mem hS).1
    have hb'T : b' ∈ T := hX.1.2.1
    have hbT : b ∈ T := hX.1.2.2.1
    have hb'b : b' ≠ b := hX.1.2.2.2.1
    have hab' : a ≠ b' := Vine.chain_joints_ne hS
    have hcC : c ∈ C := (mem_inter.mp (hi' ▸ mem_singleton_self c)).1
    have hcC' : c ∈ C' := (mem_inter.mp (hi' ▸ mem_singleton_self c)).2
    have hcU : c ∈ S ∪ T := hcov ▸ mem_union_left _ hcC
    have hW : (S ∪ T).erase c ⊆ (C ∪ C').erase c := by rw [hcov]
    have hbC : b ∉ C := fun hbC => hcb (mem_singleton.mp (hi' ▸ mem_inter.mpr ⟨hbC, hb⟩)).symm
    have haC' : a ∉ C' := fun haC' => hca (mem_singleton.mp (hi' ▸ mem_inter.mpr ⟨ha, haC'⟩)).symm
    have hTconn := Vine.isVine_connected hX
    have hSconn := Vine.chain_connected hS
    -- the side of an atom of `U \ {c}`
    have hside : ∀ {W : Finset V} {u v : V}, W ⊆ (S ∪ T).erase c →
        (∀ u ∈ W, ∀ v ∈ W, (Mole.induced M W).SameComponent u v) → u ∈ W → v ∈ W →
        (u ∈ C.erase c ↔ v ∈ C.erase c) := fun hW' hc hu hv =>
      side_of_connected M hno (hW'.trans hW) hc hu hv
    by_cases hcT : c ∈ T
    · by_cases hcb' : c = b'
      · -- c is the last junction: C = S, C' = T
        subst hcb'
        have hSe := Vine.chain_erase_last_connected hS
        have hTe := Vine.isVine_erase_connected hX c
        have hSsub : S.erase c ⊆ (S ∪ T).erase c := erase_subset_erase _ subset_union_left
        have hTsub : T.erase c ⊆ (S ∪ T).erase c := erase_subset_erase _ subset_union_right
        have haP : a ∈ C.erase c := mem_erase.mpr ⟨hca.symm, ha⟩
        have hbQ : b ∈ T.erase c := mem_erase.mpr ⟨hcb.symm, hbT⟩
        have hSP : ∀ u ∈ S.erase c, u ∈ C.erase c := fun u hu =>
          (hside hSsub hSe (mem_erase.mpr ⟨hca.symm, haS⟩) hu).mp haP
        have hTP : ∀ u ∈ T.erase c, u ∈ C'.erase c := by
          intro u hu
          have hbn : b ∉ C.erase c := fun h => hbC (mem_of_mem_erase h)
          have h1 : u ∉ C.erase c := fun h => hbn ((hside hTsub hTe hu hbQ).mp h)
          have hu' : u ∈ (C ∪ C').erase c := hW (hTsub hu)
          rw [Finset.erase_union_distrib, mem_union] at hu'
          exact hu'.resolve_left h1
        have hCS : C = S := by
          apply Finset.Subset.antisymm
          · intro x hx
            have hxU : x ∈ S ∪ T := hcov ▸ mem_union_left _ hx
            rcases mem_union.mp hxU with hxS | hxT
            · exact hxS
            · by_cases hxc : x = c
              · exact hxc ▸ hb'S
              · have := mem_of_mem_erase (hTP x (mem_erase.mpr ⟨hxc, hxT⟩))
                exact absurd (mem_singleton.mp (hi' ▸ mem_inter.mpr ⟨hx, this⟩)) hxc
          · intro x hx
            by_cases hxc : x = c
            · exact hxc ▸ hcC
            · exact mem_of_mem_erase (hSP x (mem_erase.mpr ⟨hxc, hx⟩))
        have hCT : C' = T := by
          apply Finset.Subset.antisymm
          · intro x hx
            have hxU : x ∈ S ∪ T := hcov ▸ mem_union_right _ hx
            rcases mem_union.mp hxU with hxS | hxT
            · by_cases hxc : x = c
              · exact hxc ▸ hb'T
              · have := mem_of_mem_erase (hSP x (mem_erase.mpr ⟨hxc, hxS⟩))
                exact absurd (mem_singleton.mp (hi' ▸ mem_inter.mpr ⟨this, hx⟩)) hxc
            · exact hxT
          · intro x hx
            by_cases hxc : x = c
            · exact hxc ▸ hcC'
            · exact mem_of_mem_erase (hTP x (mem_erase.mpr ⟨hxc, hx⟩))
        refine ⟨⟨n, hCS ▸ hS⟩, ⟨1, ?_⟩⟩
        rw [hCT]
        exact Vine.Chain.single ⟨X, hX⟩
      · -- c interior to the last vine: impossible
        exfalso
        have hcS : c ∉ S := fun hcS => hcb' (mem_singleton.mp (hi ▸ mem_inter.mpr ⟨hcS, hcT⟩))
        have hTe := Vine.isVine_erase_connected hX c
        have hSsub : S ⊆ (S ∪ T).erase c := fun x hx =>
          mem_erase.mpr ⟨fun h => hcS (h ▸ hx), mem_union_left _ hx⟩
        have hTsub : T.erase c ⊆ (S ∪ T).erase c := erase_subset_erase _ subset_union_right
        have haP : a ∈ C.erase c := mem_erase.mpr ⟨hca.symm, ha⟩
        have hb'e : b' ∈ T.erase c := mem_erase.mpr ⟨fun h => hcb' h.symm, hb'T⟩
        have hbe : b ∈ T.erase c := mem_erase.mpr ⟨hcb.symm, hbT⟩
        have h1 := (hside hSsub hSconn haS hb'S).mp haP
        have h2 := (hside hTsub hTe hb'e hbe).mp h1
        exact hbC (mem_of_mem_erase h2)
    · -- c lies in S, c ≠ b'
      have hcS : c ∈ S := (mem_union.mp hcU).resolve_right hcT
      have hcb'' : c ≠ b' := fun h => hcT (h ▸ hb'T)
      have hTsub : T ⊆ (S ∪ T).erase c := fun x hx =>
        mem_erase.mpr ⟨fun h => hcT (h ▸ hx), mem_union_right _ hx⟩
      have hbn : b ∉ C.erase c := fun h => hbC (mem_of_mem_erase h)
      have hTC' : ∀ u ∈ T, u ∈ C' ∧ u ≠ c := by
        intro u hu
        have h1 : u ∉ C.erase c := fun h => hbn ((hside hTsub hTconn hu hbT).mp h)
        have hu' : u ∈ (C ∪ C').erase c := hW (hTsub hu)
        rw [Finset.erase_union_distrib, mem_union] at hu'
        have := hu'.resolve_left h1
        exact ⟨mem_of_mem_erase this, ne_of_mem_erase this⟩
      have hCS : C ⊆ S := by
        intro x hx
        have hxU : x ∈ S ∪ T := hcov ▸ mem_union_left _ hx
        rcases mem_union.mp hxU with hxS | hxT
        · exact hxS
        · obtain ⟨h1, h2⟩ := hTC' x hxT
          exact absurd (mem_singleton.mp (hi' ▸ mem_inter.mpr ⟨hx, h1⟩)) h2
      obtain ⟨⟨i, hi1⟩, ⟨j, hj1⟩⟩ := ih (C := C) (C' := C' ∩ S) (c := c) hSB
        (by
          apply Finset.Subset.antisymm
          · intro x hx
            rcases mem_union.mp hx with hx | hx
            · exact hCS hx
            · exact (mem_inter.mp hx).2
          · intro x hx
            have hxU : x ∈ C ∪ C' := hcov ▸ mem_union_left _ hx
            rcases mem_union.mp hxU with hx' | hx'
            · exact mem_union_left _ hx'
            · exact mem_union_right _ (mem_inter.mpr ⟨hx', hx⟩))
        (by
          apply Finset.Subset.antisymm
          · intro x hx
            obtain ⟨h1, h2⟩ := mem_inter.mp hx
            have h3 : x ∈ C ∩ C' := mem_inter.mpr ⟨h1, (mem_inter.mp h2).1⟩
            rw [hi'] at h3
            exact h3
          · intro x hx
            have hxc : x = c := mem_singleton.mp hx
            subst hxc
            exact mem_inter.mpr ⟨hcC, mem_inter.mpr ⟨hcC', hcS⟩⟩)
        ha (mem_inter.mpr ⟨(hTC' b' hb'T).1, hb'S⟩) hca hcb''
        (fun x hx hxc y hy hyc => hno x hx hxc y (mem_inter.mp hy).1 hyc)
      refine ⟨⟨i, hi1⟩, ⟨j + 1, ?_⟩⟩
      have hC'eq : C' = (C' ∩ S) ∪ T := by
        apply Finset.Subset.antisymm
        · intro x hx
          have hxU : x ∈ S ∪ T := hcov ▸ mem_union_right _ hx
          rcases mem_union.mp hxU with hxS | hxT
          · exact mem_union_left _ (mem_inter.mpr ⟨hx, hxS⟩)
          · exact mem_union_right _ hxT
        · intro x hx
          rcases mem_union.mp hx with hx | hx
          · exact (mem_inter.mp hx).1
          · exact (hTC' x hx).1
      have hint : (C' ∩ S) ∩ T = {b'} := by
        apply Finset.Subset.antisymm
        · intro x hx
          obtain ⟨h12, h3⟩ := mem_inter.mp hx
          have h4 : x ∈ S ∩ T := mem_inter.mpr ⟨(mem_inter.mp h12).2, h3⟩
          rw [hi] at h4
          exact h4
        · intro x hx
          have hxb : x = b' := mem_singleton.mp hx
          subst hxb
          exact mem_inter.mpr ⟨mem_inter.mpr ⟨(hTC' x hb'T).1, hb'S⟩, hb'T⟩
      rw [hC'eq]
      exact Vine.Chain.append hj1 ⟨X, hX⟩ hint hcb

end WaveTurbulence.Subpro
