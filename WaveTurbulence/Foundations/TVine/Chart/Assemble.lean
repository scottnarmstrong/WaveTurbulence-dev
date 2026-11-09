/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.LemmaD

/-!
# Assembling a full chart from verified integer forms

A chart is determined by integer data: the decoding forms `k_e = g + Σ_i F e i • x_i + c e • r` of the bonds and the
two origins `p i, q i` of each coordinate (`x_i = origin(p i) − origin(q i)`). This file turns such data into a
`FullChart`, given
* conservation of the forms at every atom (`Σ_e inc(v,e) F e i = 0`, `Σ_e inc(v,e) c e = [v = b] − [v = a]`);
* the coordinate identities `form(p i) − form(q i) = δ_i` (`encode ∘ decode = id`);
* **uniqueness**: a homogeneous labelling (zero flow everywhere) with all coordinates zero vanishes
  (`decode ∘ encode = id` on the fiber over every abelian group; this is the referee's repair R1: the square system
  is unimodular);
* the phase identities, stated on the decoded labels.

`Chart.bond_count_block` is the bond count `2(|S| − 1)` of a block.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Chart

open Finset VineParamContract

variable {V D : Type*} [DecidableEq V] [Fintype D] {M : Molecule V D} {S : Finset V}

/-! ## Bond count of a block -/

/-- A block with `|S|` atoms has `2|S| − 2` internal bonds (joints have degree 2, other atoms degree 4). -/
theorem bond_count_block {a b : V} (hB : M.IsBlock S a b) :
    (internalBondSet M S).card + 2 = 2 * S.card := by
  classical
  have htl : (∑ v ∈ S, ((univ : Finset (Bond M S)).filter fun e => tl e = v).card) =
      Fintype.card (Bond M S) := by
    rw [← Finset.card_eq_sum_card_fiberwise (fun e _ => tl_mem e)]; rfl
  have hhd : (∑ v ∈ S, ((univ : Finset (Bond M S)).filter fun e => hd e = v).card) =
      Fintype.card (Bond M S) := by
    rw [← Finset.card_eq_sum_card_fiberwise (fun e _ => hd_mem e)]; rfl
  simp only [card_tl, card_hd] at htl hhd
  have hdeg : (∑ v ∈ S, M.degIn S v) = 2 * Fintype.card (Bond M S) := by
    simp only [degIn_eq, Finset.sum_add_distrib, htl, hhd]; ring
  have hsum : (∑ v ∈ S, M.degIn S v) + 4 = 4 * S.card := by
    have ha := hB.2.1; have hb := hB.2.2.1; have hab := hB.2.2.2.1
    have hda : M.degIn S a = 2 := by rw [degIn_eq, hB.2.2.2.2.1, hB.2.2.2.2.2.1]
    have hdb : M.degIn S b = 2 := by rw [degIn_eq, hB.2.2.2.2.2.2.1, hB.2.2.2.2.2.2.2.1]
    rw [← Finset.add_sum_erase S _ ha, ← Finset.add_sum_erase (S.erase a) _ (mem_erase.mpr ⟨hab.symm, hb⟩)]
    rw [Finset.sum_congr rfl (g := fun _ => 4) (fun v hv => by
      simp only [mem_erase] at hv
      exact hB.2.2.2.2.2.2.2.2.1 v hv.2.2 hv.2.1 hv.1)]
    rw [Finset.sum_const, smul_eq_mul, hda, hdb, card_erase_of_mem (mem_erase.mpr ⟨hab.symm, hb⟩),
      card_erase_of_mem ha]
    have : 2 ≤ S.card := by
      have : ({a, b} : Finset V) ⊆ S := by
        intro x hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption
      have := Finset.card_le_card this
      rw [Finset.card_pair hab] at this; exact this
    omega
  have hc : (internalBondSet M S).card = Fintype.card (Bond M S) := (Fintype.card_coe _).symm
  omega

/-! ## Forms of origins -/

/-- The anchor-free form `(x-coefficients, r-coefficient)` of an origin: a bond's decoding form, `g` itself, or
`h = g − r`. -/
def originForm {n : ℕ} (F : Matrix (Bond M S) (Fin n) ℤ) (c : Bond M S → ℤ) : Bond M S ⊕ Fin 2 → (Fin n → ℤ) × ℤ
  | .inl e => (F e, c e)
  | .inr j => (0, if j = 0 then 0 else -1)

/-- The decoded labels. -/
def decodeWith {n : ℕ} (F : Matrix (Bond M S) (Fin n) ℤ) (c : Bond M S → ℤ) {E : Type*} [AddCommGroup E]
    (g r : E) (x : Fin n → E) (e : Bond M S) : E :=
  g + (∑ i, F e i • x i) + c e • r

theorem origin_decodeWith {n : ℕ} (F : Matrix (Bond M S) (Fin n) ℤ) (c : Bond M S → ℤ) {E : Type*}
    [AddCommGroup E] (g r : E) (x : Fin n → E) (o : Bond M S ⊕ Fin 2) :
    origin M S (decodeWith F c g r x) g r o = g + (∑ i, (originForm F c o).1 i • x i) + (originForm F c o).2 • r := by
  rcases o with e | j
  · rfl
  · simp only [origin, originForm]
    split_ifs <;> simp [sub_eq_add_neg]

/-- The homogeneous origin values of a labelling (anchor and `h` set to zero). -/
def origin0 {E : Type*} [AddCommGroup E] (k : Bond M S → E) : Bond M S ⊕ Fin 2 → E
  | .inl e => k e
  | .inr _ => 0

/-- **The data of a chart**, with its verification. -/
structure ChartData (M : Molecule V D) (bad : Bool) (S : Finset V) (a b : V) where
  indexing : Indexing M bad S a b
  F : Matrix (Bond M S) (Fin indexing.shape.n) ℤ
  c : Bond M S → ℤ
  p : Fin indexing.shape.n → Bond M S ⊕ Fin 2
  q : Fin indexing.shape.n → Bond M S ⊕ Fin 2
  unit : ∀ e i, UnitCoeff (F e i)
  consF : ∀ v ∈ S, ∀ i, (∑ e : Bond M S, incidence M v e.1 * F e i) = 0
  consC : ∀ v ∈ S, (∑ e : Bond M S, incidence M v e.1 * c e) = (if v = b then 1 else 0) - (if v = a then 1 else 0)
  coord : ∀ i, (originForm F c (p i)).1 - (originForm F c (q i)).1 = Pi.single i 1 ∧
    (originForm F c (p i)).2 = (originForm F c (q i)).2
  unique : ∀ (E : Type) [AddCommGroup E] (d : Bond M S → E), (∀ v ∈ S, flow M S d v = 0) →
    (∀ i, origin0 d (p i) - origin0 d (q i) = 0) → d = 0

namespace ChartData

variable {bad : Bool} {a b : V} (C : ChartData M bad S a b)

theorem decode_mem (hM : M.IsMolecule) (hB : M.IsBlock S a b) {E : Type} [AddCommGroup E] (g r : E)
    (x : Fin C.indexing.shape.n → E) {v : V} (hv : v ∈ S) :
    flow M S (decodeWith C.F C.c g r x) v = (if v = b then r else 0) - (if v = a then r else 0) := by
  unfold flow decodeWith
  simp only [smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
  rw [← Finset.sum_smul, sum_incidence_block hM hB hv, zero_smul, zero_add, Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun i _ => by rw [← Finset.sum_smul, C.consF v hv i, zero_smul]),
    Finset.sum_const_zero, zero_add, ← Finset.sum_smul, C.consC v hv]
  split_ifs <;> simp

/-- The decoded fiber element. -/
def decodeFiber (hM : M.IsMolecule) (hB : M.IsBlock S a b) {E : Type} [AddCommGroup E] (g r : E)
    (x : Fin C.indexing.shape.n → E) : FlowFiber M S a b E r :=
  ⟨decodeWith C.F C.c g r x, by
    have hab := hB.2.2.2.1
    refine ⟨?_, ?_, ?_⟩
    · rw [C.decode_mem hM hB g r x hB.2.1]; simp [hab]
    · rw [C.decode_mem hM hB g r x hB.2.2.1]; simp [Ne.symm hab]
    · intro v hv ha hb'
      rw [C.decode_mem hM hB g r x hv]; simp [ha, hb']⟩

theorem encode_decode {E : Type} [AddCommGroup E] (g r : E) (x : Fin C.indexing.shape.n → E)
    (i : Fin C.indexing.shape.n) :
    origin M S (decodeWith C.F C.c g r x) g r (C.p i) - origin M S (decodeWith C.F C.c g r x) g r (C.q i) = x i := by
  rw [origin_decodeWith, origin_decodeWith, (C.coord i).2]
  have h1 := (C.coord i).1
  have : (∑ j, (originForm C.F C.c (C.p i)).1 j • x j) - (∑ j, (originForm C.F C.c (C.q i)).1 j • x j) = x i := by
    rw [← Finset.sum_sub_distrib]
    simp only [← sub_smul]
    have h2 : ∀ j, (originForm C.F C.c (C.p i)).1 j - (originForm C.F C.c (C.q i)).1 j =
        (Pi.single i (1 : ℤ) : Fin C.indexing.shape.n → ℤ) j :=
      fun j => by rw [← Pi.sub_apply, h1]
    simp only [h2]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [Pi.single_apply, hj]
    · simp
  rw [← this]; abel

theorem origin_sub {E : Type} [AddCommGroup E] (k k' : Bond M S → E) (g r : E) (o : Bond M S ⊕ Fin 2) :
    origin M S k g r o - origin M S k' g r o = origin0 (k - k') o := by
  rcases o with e | j
  · rfl
  · simp [origin, origin0]

/-- **The chart equivalence.** -/
def chartEquiv (hM : M.IsMolecule) (hB : M.IsBlock S a b) {E : Type} [AddCommGroup E] (g r : E) :
    FlowFiber M S a b E r ≃ (Fin C.indexing.shape.n → E) where
  toFun k i := origin M S k.1 g r (C.p i) - origin M S k.1 g r (C.q i)
  invFun x := C.decodeFiber hM hB g r x
  left_inv k := by
    apply Subtype.ext
    have hab := hB.2.2.2.1
    let k' := (C.decodeFiber hM hB g r (fun i => origin M S k.1 g r (C.p i) - origin M S k.1 g r (C.q i))).1
    have hd := C.unique E (k.1 - k') (by
      intro v hv
      have e1 : flow M S (k.1 - k') v = flow M S k.1 v - flow M S k' v := by
        unfold flow; simp only [Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]
      rw [e1, flow_fiber hab k hv,
        flow_fiber hab (C.decodeFiber hM hB g r (fun i => origin M S k.1 g r (C.p i) -
          origin M S k.1 g r (C.q i))) hv, sub_self]) (by
      intro i
      have e2 := C.encode_decode g r (fun i => origin M S k.1 g r (C.p i) - origin M S k.1 g r (C.q i)) i
      rw [← origin_sub, ← origin_sub]
      change _ - origin M S (decodeWith C.F C.c g r _) g r (C.p i) -
        (_ - origin M S (decodeWith C.F C.c g r _) g r (C.q i)) = 0
      rw [sub_sub_sub_comm, e2, sub_self])
    exact (sub_eq_zero.mp hd).symm
  right_inv x := by
    funext i
    exact C.encode_decode g r x i

end ChartData

/-- **A full chart from verified data**: the decoding is `C`'s, and the remaining fields are supplied on the decoded
labels. -/
def ChartData.toFullChart {bad : Bool} {a b : V} (C : ChartData M bad S a b) (hM : M.IsMolecule)
    (hB : M.IsBlock S a b)
    (junction : Option (Fin C.indexing.shape.m)) (junction_bad : bad = true → junction = none)
    (rung_bonds : ∀ j : Fin C.indexing.shape.m,
      M.bondsBetween (C.indexing.atom (C.indexing.shape.xSlot j)).1
        (C.indexing.atom (C.indexing.shape.ySlot j)).1 = if junction = some j then 1 else 2)
    (ζc : Fin C.indexing.shape.m → Fin 3 → ℤ) (ζ_unit : ∀ j c, UnitCoeff (ζc j c))
    (ζ_bad_nonzero : bad = true → ∀ j, ζc j 0 ≠ 0 ∨ ζc j 1 ≠ 0)
    (coreLinear : Bool) (coreFirstSign coreSign : ℤˣ) (ξc : Fin 4 → ℤ) (ξ_unit : ∀ c, UnitCoeff (ξc c))
    (joint_phase : ∀ (d : ℕ) (g r : Mom d) (x : Fin C.indexing.shape.n → Mom d),
      nodeResonance C.indexing (decodeWith C.F C.c g r x) g r C.indexing.shape.x0 =
        2 * inner ℝ r (x C.indexing.shape.x0))
    (rung_t_phase : ∀ (d : ℕ) (g r : Mom d) (x : Fin C.indexing.shape.n → Mom d) (j : Fin C.indexing.shape.m),
      nodeResonance C.indexing (decodeWith C.F C.c g r x) g r (C.indexing.shape.xSlot j) =
        2 * inner ℝ (x (C.indexing.shape.xSlot j)) (x (C.indexing.shape.ySlot j)) +
          2 * inner ℝ r ((ζc j 0 : ℝ) • x (C.indexing.shape.xSlot j) +
            (ζc j 1 : ℝ) • x (C.indexing.shape.ySlot j) + (ζc j 2 : ℝ) • r))
    (rung_s_phase : ∀ (d : ℕ) (g r : Mom d) (x : Fin C.indexing.shape.n → Mom d) (j : Fin C.indexing.shape.m),
      nodeResonance C.indexing (decodeWith C.F C.c g r x) g r (C.indexing.shape.ySlot j) =
        -2 * inner ℝ (x (C.indexing.shape.xSlot j)) (x (C.indexing.shape.ySlot j)))
    (core_first_phase : ∀ (hn : bad = false) (d : ℕ) (g r : Mom d) (x : Fin C.indexing.shape.n → Mom d),
      nodeResonance C.indexing (decodeWith C.F C.c g r x) g r (C.indexing.shape.uSlot hn 0) =
        2 * ((coreFirstSign : ℤ) : ℝ) * inner ℝ (x (C.indexing.shape.uSlot hn 0)) (x (C.indexing.shape.uSlot hn 1)))
    (core_second_phase : ∀ (hn : bad = false) (d : ℕ) (g r : Mom d) (x : Fin C.indexing.shape.n → Mom d),
      nodeResonance C.indexing (decodeWith C.F C.c g r x) g r (C.indexing.shape.uSlot hn 1) =
        2 * ((coreFirstSign : ℤ) : ℝ) * (if coreLinear then
            inner ℝ (x (C.indexing.shape.uSlot hn 0)) (x (C.indexing.shape.uSlot hn 2))
          else ((coreSign : ℤ) : ℝ) * inner ℝ (x (C.indexing.shape.uSlot hn 2))
            (x (C.indexing.shape.uSlot hn 0) + x (C.indexing.shape.uSlot hn 1) - x (C.indexing.shape.uSlot hn 2))))
    (core_sum_phase : ∀ (hn : bad = false) (d : ℕ) (g r : Mom d) (x : Fin C.indexing.shape.n → Mom d),
      (∑ c : Fin 3, nodeResonance C.indexing (decodeWith C.F C.c g r x) g r (C.indexing.shape.uSlot hn c)) =
        2 * inner ℝ r ((ξc 0 : ℝ) • x (C.indexing.shape.uSlot hn 0) +
          (ξc 1 : ℝ) • x (C.indexing.shape.uSlot hn 1) +
          (ξc 2 : ℝ) • x (C.indexing.shape.uSlot hn 2) + (ξc 3 : ℝ) • r)) :
    FullChart M bad S a b where
  indexing := C.indexing
  bond_count := by
    have h := bond_count_block hB
    have hn : C.indexing.shape.n + 1 = S.card := by
      have := Fintype.card_congr C.indexing.atom
      simp only [Fintype.card_fin, Fintype.card_coe] at this
      rw [this, card_erase_of_mem hB.2.1]
      have : 0 < S.card := Finset.card_pos.mpr ⟨a, hB.2.1⟩
      omega
    omega
  junction := junction
  junction_bad := junction_bad
  rung_bonds := rung_bonds
  decodeFree := C.F
  decodeGap := C.c
  free_unit := C.unit
  chart g r := C.chartEquiv hM hB g r
  decode_eq _ _ _ _ := rfl
  difference i := ⟨C.p i, C.q i, fun _ _ _ => rfl⟩
  ζc := ζc
  ζ_unit := ζ_unit
  ζ_bad_nonzero := ζ_bad_nonzero
  coreLinear := coreLinear
  coreFirstSign := coreFirstSign
  coreSign := coreSign
  ξc := ξc
  ξ_unit := ξ_unit
  joint_phase := joint_phase
  rung_t_phase := rung_t_phase
  rung_s_phase := rung_s_phase
  core_first_phase := core_first_phase
  core_second_phase := core_second_phase
  core_sum_phase := core_sum_phase

end WaveTurbulence.TVine.Chart
