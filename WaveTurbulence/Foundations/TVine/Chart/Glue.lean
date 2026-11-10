/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.Decomp

/-!
# Gluing: the chart data of a cell decomposition (M4 Theorem C, (C0)–(C3))

From a cell decomposition:
* **(C0) indexing**: slot `x₀ ↦ b`, `xSlot j ↦` the `t`-atom (local atom `1`) of pair cell `j`, `ySlot j ↦` its
  `s`-atom (local atom `0`), `uSlot c ↦` the core atom `c` (`Decomp.indexing`);
* **(C2) unit decoding** (`Decomp.form_unit`): every coefficient of a glued form is a coefficient of one local
  chart, since coordinates of distinct cells are disjoint and `κ_c` only involves ancestors (smaller rank);
* conservation of the glued forms at every atom (local conservation, transferred by the local embeddings);
* **(C3) coordinates**: each coordinate is the local opposite difference of its cell's chart;
* **(C1) uniqueness** over every abelian group: by induction along the gluing tree, using each local chart's
  uniqueness certificate and N1 Lemma D for the extra (2-cut) equations.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Chart

open Finset VineParamContract

namespace Decomp

variable {V D : Type*} [DecidableEq V] [Fintype D] {M : Molecule V D} {S : Finset V} {a b : V}
variable (Dc : Decomp M S a b)

/-! ## Slots and atoms -/

/-- The atom of a cell carrying a local coordinate's slot: `x ↦ t` (atom `1`), `y ↦ s` (atom `0`) for pairs; the
identity for the core. -/
def slotAtomIdx {m k : ℕ} : (c : Cell m k) → Fin (nCof c) → Fin (nAof c)
  | .inl _, i => ⟨1 - i.val, by show 1 - i.val < 2; omega⟩
  | .inr (.inl _), i => ⟨i.val, i.2⟩
  | .inr (.inr _), i => i.elim0

open Classical in
/-- The local coordinate of a slot (`none` for `x₀`). -/
noncomputable def slotInv (i : Fin (nshape Dc.m).n) : Option (Σ c : Cell Dc.m Dc.k, Fin (nCof c)) :=
  if h : ∃ σ : Σ c : Cell Dc.m Dc.k, Fin (nCof c), slotS σ = i then some h.choose else none

theorem slotInv_slotS (σ : Σ c : Cell Dc.m Dc.k, Fin (nCof c)) : Dc.slotInv (slotS σ) = some σ := by
  have h : ∃ τ : Σ c : Cell Dc.m Dc.k, Fin (nCof c), slotS τ = slotS σ := ⟨σ, rfl⟩
  unfold slotInv
  rw [dite_cond_eq_true (eq_true h)]
  exact congrArg some (slotS_injective h.choose_spec)

theorem slotInv_x0 : Dc.slotInv (nshape Dc.m).x0 = none := by
  unfold slotInv
  have h : ¬ ∃ σ : Σ c : Cell Dc.m Dc.k, Fin (nCof c), slotS σ = (nshape Dc.m).x0 := by
    rintro ⟨σ, hσ⟩
    exact slotS_ne_x0 σ hσ
  rw [dite_cond_eq_false (eq_false h)]

theorem slotInv_eq_none {i : Fin (nshape Dc.m).n} (h : Dc.slotInv i = none) : i = (nshape Dc.m).x0 := by
  by_contra hne
  obtain ⟨σ, rfl⟩ := slotS_surj (k := Dc.k) i hne
  rw [Dc.slotInv_slotS] at h
  simp at h

theorem slotInv_eq_some {i : Fin (nshape Dc.m).n} {σ : Σ c : Cell Dc.m Dc.k, Fin (nCof c)}
    (h : Dc.slotInv i = some σ) : slotS σ = i := by
  by_cases hi : i = (nshape Dc.m).x0
  · subst hi; rw [Dc.slotInv_x0] at h; simp at h
  obtain ⟨τ, rfl⟩ := slotS_surj (k := Dc.k) i hi
  rw [Dc.slotInv_slotS] at h
  rw [Option.some_inj.mp h]

/-- The atom of a slot. -/
noncomputable def atomOf (i : Fin (nshape Dc.m).n) : V :=
  match Dc.slotInv i with
  | none => b
  | some σ => (Dc.emb σ.1).atom (slotAtomIdx σ.1 σ.2)

theorem atomOf_x0 : Dc.atomOf (nshape Dc.m).x0 = b := by
  unfold atomOf; rw [Dc.slotInv_x0]

theorem atomOf_slotS (σ : Σ c : Cell Dc.m Dc.k, Fin (nCof c)) :
    Dc.atomOf (slotS σ) = (Dc.emb σ.1).atom (slotAtomIdx σ.1 σ.2) := by
  unfold atomOf; rw [Dc.slotInv_slotS]

theorem slotAtomIdx_inj {m k : ℕ} {c : Cell m k} {i i' : Fin (nCof c)}
    (h : slotAtomIdx c i = slotAtomIdx c i') : i = i' := by
  rcases c with (j | _ | j)
  · have hi : (i : ℕ) < 2 := i.2; have hi' : (i' : ℕ) < 2 := i'.2
    have := congrArg Fin.val h
    simp only [slotAtomIdx] at this
    exact Fin.ext (by omega)
  · exact Fin.ext (congrArg Fin.val h)
  · exact i.elim0

theorem slotAtomIdx_surj {m k : ℕ} (c : Cell m k) (u : Fin (nAof c)) :
    ∃ i : Fin (nCof c), slotAtomIdx c i = u := by
  rcases c with (j | _ | j)
  · have hu : (u : ℕ) < 2 := u.2
    exact ⟨⟨1 - u.val, by show 1 - u.val < 2; omega⟩, Fin.ext (by simp only [slotAtomIdx]; omega)⟩
  · exact ⟨⟨u.val, u.2⟩, rfl⟩
  · exact u.elim0

theorem atomOf_mem (hB : M.IsBlock S a b) (i : Fin (nshape Dc.m).n) : Dc.atomOf i ∈ S.erase a := by
  unfold atomOf
  split
  · exact mem_erase.mpr ⟨hB.2.2.2.1.symm, hB.2.2.1⟩
  · exact mem_erase.mpr ⟨Dc.atom_ne_a _ _, Dc.atom_mem _ _⟩

theorem atomOf_injective : Function.Injective Dc.atomOf := by
  intro i j h
  rcases hi : Dc.slotInv i with _ | σ <;> rcases hj : Dc.slotInv j with _ | τ
  · rw [Dc.slotInv_eq_none hi, Dc.slotInv_eq_none hj]
  · unfold atomOf at h; rw [hi, hj] at h; exact absurd h.symm (Dc.atom_ne_b _ _)
  · unfold atomOf at h; rw [hi, hj] at h; exact absurd h (Dc.atom_ne_b _ _)
  · unfold atomOf at h; rw [hi, hj] at h
    have he := Dc.atom_inj _ _ _ _ h
    rw [← Dc.slotInv_eq_some hi, ← Dc.slotInv_eq_some hj]
    rcases σ with ⟨c, i'⟩; rcases τ with ⟨c', j'⟩
    simp only [Sigma.mk.inj_iff] at he
    obtain ⟨rfl, he⟩ := he
    have := slotAtomIdx_inj (eq_of_heq he)
    rw [this]

/-- **(C0) The indexing** of the chart. -/
noncomputable def indexing (hB : M.IsBlock S a b) : Indexing M false S a b where
  shape := nshape Dc.m
  atom := Equiv.ofBijective (fun i => ⟨Dc.atomOf i, Dc.atomOf_mem hB i⟩) ⟨fun i j h =>
      Dc.atomOf_injective (congrArg Subtype.val h), by
    rintro ⟨v, hv⟩
    rcases Dc.cover v (mem_erase.mp hv).2 with rfl | rfl | ⟨c, u, rfl⟩
    · exact absurd rfl (mem_erase.mp hv).1
    · exact ⟨(nshape Dc.m).x0, Subtype.ext Dc.atomOf_x0⟩
    · obtain ⟨i, hi⟩ := slotAtomIdx_surj c u
      refine ⟨slotS ⟨c, i⟩, Subtype.ext ?_⟩
      show Dc.atomOf (slotS ⟨c, i⟩) = (Dc.emb c).atom u
      rw [Dc.atomOf_slotS, hi]⟩
  lower := Dc.atomOf_x0

/-! ## Unit decoding -/

theorem kap_support : ∀ (c : Cell Dc.m Dc.k) (i : Fin (nshape Dc.m).n), (Dc.kap c).1 i ≠ 0 →
    i = (nshape Dc.m).x0 ∨ ∃ σ : Σ c : Cell Dc.m Dc.k, Fin (nCof c), slotS σ = i ∧ Dc.rank σ.1 < Dc.rank c := by
  intro c
  induction hr : Dc.rank c using Nat.strong_induction_on generalizing c with
  | _ N ih =>
  intro i hi
  cases hp : Dc.parent c with
  | none =>
    rw [Dc.kap_none hp] at hi
    left; by_contra h; simp [baseKap, h] at hi
  | some sw =>
    obtain ⟨s, w⟩ := sw
    have hrk := Dc.parent_rank c s w hp
    rw [Dc.kap_some hp] at hi
    simp only [Prod.fst_add, Pi.add_apply] at hi
    by_cases h1 : (Dc.kap s).1 i = 0
    · rw [h1, zero_add] at hi
      right
      unfold transfer at hi
      split at hi
      · simp only at hi
        by_contra hno
        apply hi
        apply lift_of_not_mem
        intro i' he
        exact hno ⟨⟨s, i'⟩, he, hr ▸ hrk⟩
      · simp at hi
    · rcases ih (Dc.rank s) (hr ▸ hrk) s rfl i h1 with h | ⟨σ, h2, h3⟩
      · exact Or.inl h
      · exact Or.inr ⟨σ, h2, by omega⟩

theorem kap_slot_zero (c : Cell Dc.m Dc.k) (i' : Fin (nCof c)) : (Dc.kap c).1 (slotOf c i') = 0 := by
  by_contra h
  rcases Dc.kap_support c _ h with h1 | ⟨σ, h2, h3⟩
  · exact slotS_ne_x0 ⟨c, i'⟩ h1
  · have := slotS_injective (m := Dc.m) (k := Dc.k) (h2.trans rfl : slotS σ = slotS ⟨c, i'⟩)
    subst this; exact lt_irrefl _ h3

theorem kap_unit : ∀ (c : Cell Dc.m Dc.k) (i : Fin (nshape Dc.m).n), IsUnitZ ((Dc.kap c).1 i) := by
  intro c
  induction hr : Dc.rank c using Nat.strong_induction_on generalizing c with
  | _ N ih =>
  intro i
  cases hp : Dc.parent c with
  | none =>
    rw [Dc.kap_none hp]; simp only [baseKap, IsUnitZ]; split_ifs <;> simp
  | some sw =>
    obtain ⟨s, w⟩ := sw
    have hrk := Dc.parent_rank c s w hp
    rw [Dc.kap_some hp]
    simp only [Prod.fst_add, Pi.add_apply]
    unfold transfer
    split
    · rename_i p hp1
      by_cases hs : ∃ i', slotOf s i' = i
      · obtain ⟨i', rfl⟩ := hs
        rw [Dc.kap_slot_zero, zero_add]
        simp only [lift_slot]
        exact LocalChart.loc_unit (Dc.valid s) _ _
      · push Not at hs
        simp only [lift_of_not_mem s _ i hs, add_zero]
        exact ih (Dc.rank s) (hr ▸ hrk) s rfl i
    · simp only [Prod.fst_zero, Pi.zero_apply, add_zero]
      exact ih (Dc.rank s) (hr ▸ hrk) s rfl i

theorem form_unit (e : Bond M S) (i : Fin (nshape Dc.m).n) : IsUnitZ ((Dc.form e).1 i) := by
  unfold form
  split
  · split_ifs <;> simp [baseKap] <;> split_ifs <;> simp [IsUnitZ]
  · rename_i c l _
    unfold locForm
    simp only [Prod.fst_add, Pi.add_apply]
    by_cases hs : ∃ i', slotOf c i' = i
    · obtain ⟨i', rfl⟩ := hs
      rw [Dc.kap_slot_zero, zero_add, lift_slot]
      exact LocalChart.loc_unit (Dc.valid c) _ _
    · push Not at hs
      rw [lift_of_not_mem c _ i hs, add_zero]
      exact Dc.kap_unit c i

end Decomp

end WaveTurbulence.TVine.Chart
