/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.GlueCons

/-!
# Gluing: exact phases and the full chart (M4 Theorem C, (C4))

At an atom of a cell every glued label is `κ_c + W_l` with `W_l` the local label (`form_emb`). By conservation at
the atom the energy is free of `κ_c` (N1 Lemma D, κ-freeness), so it is the local quadratic form of the cell's
chart, which is the required phase form by the decided Gram identities (`PairOK`, `CoreOK`). At the lower joint
`nodeResonance = 2⟨r, x₀⟩` directly. This gives `Decomp.toFullChart`.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Chart

open Finset VineParamContract

/-- κ-freeness: with `Σ s_l = 0` and `Σ s_l W_l = 0`, a common shift does not change `Σ −s_l |K + W_l|²`. -/
theorem kfree {d : ℕ} {ι : Type*} [Fintype ι] (s : ι → ℤ) (K : Mom d) (W : ι → Mom d) (h1 : (∑ l, s l) = 0)
    (h2 : (∑ l, (s l : ℝ) • W l) = 0) :
    (∑ l, -(s l : ℝ) * ‖K + W l‖ ^ 2) = ∑ l, -(s l : ℝ) * ‖W l‖ ^ 2 := by
  have e : ∀ l, -(s l : ℝ) * ‖K + W l‖ ^ 2 =
      -(s l : ℝ) * ‖K‖ ^ 2 - 2 * inner ℝ K ((s l : ℝ) • W l) + -(s l : ℝ) * ‖W l‖ ^ 2 := by
    intro l; rw [norm_add_sq_real, real_inner_smul_right]; ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    ← inner_sum, h2, inner_zero_right, mul_zero, sub_zero]
  have : (∑ l, -(s l : ℝ)) = 0 := by
    rw [Finset.sum_neg_distrib, neg_eq_zero]; exact_mod_cast h1
  rw [this, zero_mul, zero_add]

/-- A unit of `ℤ` from `±1`. -/
def toUnit (z : ℤ) : ℤˣ := if z = 1 then 1 else -1

theorem toUnit_val {z : ℤ} (h : z = 1 ∨ z = -1) : ((toUnit z : ℤˣ) : ℤ) = z := by
  unfold toUnit; rcases h with rfl | rfl <;> simp

theorem isUnitZ_unitCoeff {z : ℤ} (h : IsUnitZ z) : UnitCoeff z := h

namespace Decomp

variable {V D : Type*} [DecidableEq V] [Fintype D] {M : Molecule V D} {S : Finset V} {a b : V}
variable (Dc : Decomp M S a b)

theorem sum_lift {E : Type*} [AddCommGroup E] (c : Cell Dc.m Dc.k) (v : Fin (nCof c) → ℤ)
    (x : Fin (nshape Dc.m).n → E) : (∑ i, lift c v i • x i) = ∑ i', v i' • x (slotOf c i') := by
  unfold lift
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i' _ => ?_)
  simp only [ite_smul, zero_smul, Finset.sum_ite_eq, mem_univ, ite_true]

/-- The local variable vector of a cell: its coordinates, then `r`. -/
def zvec {d : ℕ} (c : Cell Dc.m Dc.k) (x : Fin (nshape Dc.m).n → Mom d) (r : Mom d) :
    Fin (nCof c + 1) → Mom d :=
  fun i => if h : i.val < nCof c then x (slotOf c ⟨i, h⟩) else r

theorem decode_emb {d : ℕ} (g r : Mom d) (x : Fin (nshape Dc.m).n → Mom d) (c : Cell Dc.m Dc.k)
    (l : Fin (Dc.nB c)) :
    decodeWith Dc.F Dc.C g r x ((Dc.emb c).bond l) =
      (g + (∑ i, (Dc.kap c).1 i • x i) + (Dc.kap c).2 • r) +
        ∑ i, ((Dc.cfg c).vec l i : ℝ) • Dc.zvec c x r i := by
  unfold decodeWith
  have hF : ∀ i, Dc.F ((Dc.emb c).bond l) i = (Dc.kap c).1 i + lift c ((Dc.cfg c).loc l) i := by
    intro i; simp [F, Dc.form_emb, locForm]
  have hC : Dc.C ((Dc.emb c).bond l) = (Dc.kap c).2 + (Dc.cfg c).locR l := by
    simp [C, Dc.form_emb, locForm]
  simp only [hF, hC, add_smul, Finset.sum_add_distrib, Dc.sum_lift]
  rw [Fin.sum_univ_castSucc]
  have h1 : ∀ i' : Fin (nCof c), ((Dc.cfg c).vec l (Fin.castSucc i') : ℝ) • Dc.zvec c x r (Fin.castSucc i') =
      (Dc.cfg c).loc l i' • x (slotOf c i') := by
    intro i'
    simp only [LocalChart.vec, zvec, Fin.val_castSucc, i'.2, dite_true, Fin.eta]
    rw [Int.cast_smul_eq_zsmul]
  have h2 : ((Dc.cfg c).vec l (Fin.last _) : ℝ) • Dc.zvec c x r (Fin.last _) = (Dc.cfg c).locR l • r := by
    simp only [LocalChart.vec, zvec, Fin.val_last, lt_irrefl, dite_false]
    rw [Int.cast_smul_eq_zsmul]
  simp only [h1, h2]
  abel

/-- **The energy at a cell atom** is the cell's local quadratic form. -/
theorem energy_cell {d : ℕ} (g r : Mom d) (x : Fin (nshape Dc.m).n → Mom d) (c : Cell Dc.m Dc.k)
    (u : Fin (nAof c)) :
    energy M S (decodeWith Dc.F Dc.C g r x) ((Dc.emb c).atom u) = LocalChart.quad ((Dc.cfg c).gram u) (Dc.zvec c x r) := by
  rw [(Dc.emb c).energy_transfer]
  change (∑ l, -((Dc.cfg c).inc u l : ℝ) * ‖decodeWith Dc.F Dc.C g r x ((Dc.emb c).bond l)‖ ^ 2) = _
  simp only [Dc.decode_emb]
  rw [kfree]
  · exact LocalChart.energy_local (Dc.valid c) u (Dc.zvec c x r)
  · exact LocalChart.sum_inc (Dc.valid c) u
  · simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [← Finset.sum_smul]
    have : (∑ l, ((Dc.cfg c).inc u l : ℝ) * ((Dc.cfg c).vec l i : ℝ)) = 0 := by
      have hz : (∑ l, (Dc.cfg c).inc u l * (Dc.cfg c).vec l i) = 0 := by
        unfold LocalChart.vec
        by_cases h : i.val < nCof c
        · simp only [h, dite_true]; exact LocalChart.sum_inc_loc (Dc.valid c) u _
        · simp only [h, dite_false]; exact LocalChart.sum_inc_locR (Dc.valid c) u
      exact_mod_cast hz
    rw [this, zero_smul]

/-! ## Slots of pairs and of the core -/

/-- Local coordinate/atom indices of a pair cell. -/
abbrev p0 {m k : ℕ} (j : Fin m) : Fin (nCof (Sum.inl j : Cell m k)) := ⟨0, by show 0 < 2; omega⟩
abbrev p1 {m k : ℕ} (j : Fin m) : Fin (nCof (Sum.inl j : Cell m k)) := ⟨1, by show 1 < 2; omega⟩
abbrev a0 {m k : ℕ} (j : Fin m) : Fin (nAof (Sum.inl j : Cell m k)) := ⟨0, by show 0 < 2; omega⟩
abbrev a1 {m k : ℕ} (j : Fin m) : Fin (nAof (Sum.inl j : Cell m k)) := ⟨1, by show 1 < 2; omega⟩
/-- Core atom indices. -/
abbrev cA {m k : ℕ} (c : Fin 3) : Fin (nAof (Cell.core : Cell m k)) := ⟨c.val, c.2⟩

theorem atom_xSlot (hB : M.IsBlock S a b) (j : Fin Dc.m) :
    ((Dc.indexing hB).atom ((nshape Dc.m).xSlot j)).1 = (Dc.emb (.inl j)).atom (a1 (k := Dc.k) j) := by
  show Dc.atomOf (slotS ⟨.inl j, p0 (k := Dc.k) j⟩) = _
  rw [Dc.atomOf_slotS]; rfl

theorem atom_ySlot (hB : M.IsBlock S a b) (j : Fin Dc.m) :
    ((Dc.indexing hB).atom ((nshape Dc.m).ySlot j)).1 = (Dc.emb (.inl j)).atom (a0 (k := Dc.k) j) := by
  show Dc.atomOf (slotS ⟨.inl j, p1 (k := Dc.k) j⟩) = _
  rw [Dc.atomOf_slotS]; rfl

theorem atom_uSlot (hB : M.IsBlock S a b) (c : Fin 3) :
    ((Dc.indexing hB).atom ((nshape Dc.m).uSlot rfl c)).1 = (Dc.emb Cell.core).atom (cA (m := Dc.m) (k := Dc.k) c) := by
  show Dc.atomOf (slotS (k := Dc.k) ⟨Cell.core, c⟩) = _
  rw [Dc.atomOf_slotS]; rfl

theorem zvec_pair {d : ℕ} (j : Fin Dc.m) (x : Fin (nshape Dc.m).n → Mom d) (r : Mom d) :
    Dc.zvec (.inl j) x r = ![x ((nshape Dc.m).xSlot j), x ((nshape Dc.m).ySlot j), r] := by
  funext i
  have hi : (i : ℕ) < 3 := i.2
  rcases i with ⟨_ | _ | _ | _, h⟩
  · rfl
  · rfl
  · simp [zvec, nCof]
  · exfalso; have : _ + 1 + 1 + 1 < 3 := h; omega

theorem zvec_core {d : ℕ} (x : Fin (nshape Dc.m).n → Mom d) (r : Mom d) :
    Dc.zvec Cell.core x r = ![x ((nshape Dc.m).uSlot rfl 0), x ((nshape Dc.m).uSlot rfl 1),
      x ((nshape Dc.m).uSlot rfl 2), r] := by
  funext i
  have hi : (i : ℕ) < 4 := i.2
  rcases i with ⟨_ | _ | _ | _ | _, h⟩
  · rfl
  · rfl
  · rfl
  · simp [zvec, nCof]
  · exfalso; have : _ + 1 + 1 + 1 + 1 < 4 := h; omega

theorem ySlot_ne (j : Fin Dc.m) : (nshape Dc.m).ySlot j ≠ (nshape Dc.m).x0 := slotS_ne_x0 ⟨.inl j, p1 (k := Dc.k) j⟩
theorem xSlot_ne (j : Fin Dc.m) : (nshape Dc.m).xSlot j ≠ (nshape Dc.m).x0 := slotS_ne_x0 ⟨.inl j, p0 (k := Dc.k) j⟩
theorem uSlot_ne (c : Fin 3) : (nshape Dc.m).uSlot rfl c ≠ (nshape Dc.m).x0 :=
  slotS_ne_x0 (k := Dc.k) ⟨Cell.core, c⟩

/-! ## The number of bonds between two atoms of a cell -/

theorem bondsBetween_emb (c : Cell Dc.m Dc.k) (u w : Fin (nAof c)) (huw : u ≠ w) :
    M.bondsBetween ((Dc.emb c).atom u) ((Dc.emb c).atom w) =
      (univ.filter fun l : Fin (Dc.nB c) => ((Dc.cfg c).src l = some u ∧ (Dc.cfg c).dst l = some w) ∨
        ((Dc.cfg c).src l = some w ∧ (Dc.cfg c).dst l = some u)).card := by
  classical
  symm
  unfold Molecule.bondsBetween
  apply Finset.card_bij (fun l _ => ((Dc.emb c).bond l).1)
  · intro l hl
    simp only [mem_filter, mem_univ, true_and] at hl
    simp only [Molecule.bonds, mem_filter, mem_univ, true_and]
    refine ⟨(bond_spec _).1, ?_⟩
    unfold Molecule.ends
    rcases hl with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 := (Dc.emb c).tl_eq l u h1; have e2 := (Dc.emb c).hd_eq l w h2
      unfold tl at e1; unfold hd at e2; rw [e1, e2]
    · have e1 := (Dc.emb c).tl_eq l w h1; have e2 := (Dc.emb c).hd_eq l u h2
      unfold tl at e1; unfold hd at e2; rw [e1, e2, Sym2.eq_swap]
  · intro l _ l' _ h
    exact (Dc.emb c).bond_inj (Subtype.ext h)
  · intro x hx
    simp only [Molecule.bonds, mem_filter, mem_univ, true_and] at hx
    have hends := hx.2
    unfold Molecule.ends at hends
    have hmem : M.atom x ∈ S ∧ M.atom (M.mate x) ∈ S := by
      rcases Sym2.eq_iff.mp hends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
        exact ⟨Dc.atom_mem _ _, Dc.atom_mem _ _⟩
    let e : Bond M S := ⟨x, mem_internalBondSet hx.1 hmem⟩
    have hat : tl e = (Dc.emb c).atom u ∨ hd e = (Dc.emb c).atom u := by
      rcases Sym2.eq_iff.mp hends with ⟨h1, -⟩ | ⟨-, h2⟩
      · left; exact h1
      · right; exact h2
    obtain ⟨l, hl⟩ := (Dc.emb c).complete u e hat
    refine ⟨l, ?_, by rw [hl]⟩
    simp only [mem_filter, mem_univ, true_and]
    rcases Sym2.eq_iff.mp hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      refine ⟨((Dc.emb c).tl_iff l u).mp ?_, ((Dc.emb c).hd_iff l w).mp ?_⟩
      · rw [hl]; exact h1
      · rw [hl]; exact h2
    · right
      refine ⟨((Dc.emb c).tl_iff l w).mp ?_, ((Dc.emb c).hd_iff l u).mp ?_⟩
      · rw [hl]; exact h1
      · rw [hl]; exact h2

theorem rung_bonds (hB : M.IsBlock S a b) (j : Fin Dc.m) :
    M.bondsBetween ((Dc.indexing hB).atom ((nshape Dc.m).xSlot j)).1
      ((Dc.indexing hB).atom ((nshape Dc.m).ySlot j)).1 = if Dc.junction = some j then 1 else 2 := by
  rw [Dc.atom_xSlot hB, Dc.atom_ySlot hB, Dc.bondsBetween_emb _ _ _ (fun h => absurd (congrArg Fin.val h) (by show (1 : ℕ) ≠ 0; omega)), ← Dc.junction_mu j,
    ← (Dc.pairOK j).2.2.2.1]
  unfold pairBonds
  congr 1
  apply Finset.filter_congr
  intro l _
  exact Or.comm

/-! ## The joint phase -/

theorem joint_energy {d : ℕ} (g r : Mom d) (x : Fin (nshape Dc.m).n → Mom d) :
    energy M S (decodeWith Dc.F Dc.C g r x) (Dc.jb.atom 0) =
      ‖g - x (nshape Dc.m).x0 - r‖ ^ 2 - ‖g - x (nshape Dc.m).x0‖ ^ 2 := by
  rw [Dc.jb.energy_transfer, Fin.sum_univ_two, jinc0, jinc1]
  have hs : ∀ y : (Fin (nshape Dc.m).n → ℤ) × ℤ, y = Dc.baseKap + (0, 1) ∨ y = Dc.baseKap →
      (∑ i, y.1 i • x i) = -x (nshape Dc.m).x0 := by
    rintro y (rfl | rfl) <;>
    · simp only [baseKap, Prod.fst_add, add_zero, ite_smul, neg_smul, one_smul, zero_smul,
        Finset.sum_ite_eq', mem_univ, ite_true]
  have h0 : decodeWith Dc.F Dc.C g r x (Dc.jb.bond 0) = g - x (nshape Dc.m).x0 := by
    unfold decodeWith
    have e1 : (∑ i, Dc.F (Dc.jb.bond 0) i • x i) = -x (nshape Dc.m).x0 := by
      rw [← hs (Dc.baseKap + (0, 1)) (Or.inl rfl)]; simp [F, Dc.form_jb0]
    have e2 : Dc.C (Dc.jb.bond 0) = 0 := by simp [C, Dc.form_jb0, baseKap]
    rw [e1, e2, zero_smul, add_zero, sub_eq_add_neg]
  have h1 : decodeWith Dc.F Dc.C g r x (Dc.jb.bond 1) = g - x (nshape Dc.m).x0 - r := by
    unfold decodeWith
    have e1 : (∑ i, Dc.F (Dc.jb.bond 1) i • x i) = -x (nshape Dc.m).x0 := by
      rw [← hs Dc.baseKap (Or.inr rfl)]; simp [F, Dc.form_jb1]
    have e2 : Dc.C (Dc.jb.bond 1) = -1 := by simp [C, Dc.form_jb1, baseKap]
    rw [e1, e2, neg_smul, one_smul]; abel
  rw [h0, h1]
  push_cast
  ring

theorem joint_phase (hB : M.IsBlock S a b) (d : ℕ) (g r : Mom d) (x : Fin (nshape Dc.m).n → Mom d) :
    nodeResonance (Dc.indexing hB) (decodeWith Dc.F Dc.C g r x) g r (nshape Dc.m).x0 =
      2 * inner ℝ r (x (nshape Dc.m).x0) := by
  unfold nodeResonance
  change energy M S (decodeWith Dc.F Dc.C g r x) (Dc.atomOf (nshape Dc.m).x0) +
    (if (nshape Dc.m).x0 = (nshape Dc.m).x0 then ‖g‖ ^ 2 - ‖g - r‖ ^ 2 else 0) = _
  rw [Dc.atomOf_x0.trans Dc.jb_atom.symm, Dc.joint_energy]
  simp only [ite_true]
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, real_inner_comm g r,
    real_inner_comm (x (nshape Dc.m).x0) r, real_inner_comm g (x (nshape Dc.m).x0)]
  ring

end Decomp

end WaveTurbulence.TVine.Chart
