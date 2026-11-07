/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.ChainLadder
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.YLem2Y1
import Mathlib.Tactic

/-! # `ylem2`, second statement: `ℓ` an exit, a copy of the triple bond, or a rail

`𝕄 ∖ {ℓ}` for `ℓ` removed by a (Y) sequence ending in (Y2) (DH23 L1950, proof L1956):
* `ℓ` an exit: the chain is attached by the other exit only ((Y1) case 2 bound, no loss);
* `ℓ` a copy of the triple bond: the whole chain is a `Ladder3` (operation (b) peel, no loss);
* `ℓ` a rail between pairs `k`, `k + 1`: the pairs up to `k` are attached by the other rail only ((Y1) case 2), and
  the pairs from `k + 1` on are a `Ladder3`.
In each case `𝔄(𝕄 ∖ {ℓ}) ≤ 𝔄(𝕄 ∖ chain)` at the same LG parameter. Each case takes the general bound it uses as a
hypothesis at fixed `L`; `YLem2Second` supplies them.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Summing the bond count correction of `𝕄 ∖ {ℓ}` over a set. -/
theorem sum_eraseBond_of_ends (M : Molecule V D) (e : D) {p q : V} (he : M.ends e = s(p, q)) (v : V)
    (S : Finset V) :
    ∑ w ∈ S, (MoleProp.eraseBond M e).bondsBetween v w + ∑ w ∈ S, (if s(p, q) = s(v, w) then 1 else 0) =
      ∑ w ∈ S, M.bondsBetween v w := by
  rw [← sum_add_distrib]
  exact sum_congr rfl fun w _ => bondsBetween_eraseBond_of_ends M e he v w

namespace Y2End
variable {M : Molecule V D} {C : YChain M} (E : Y2End C)

omit [DecidableEq D] in
theorem ends_x : M.ends E.x = s(C.a C.n, M.atom (M.mate E.x)) := by unfold Molecule.ends; rw [E.hx]

omit [DecidableEq D] in
theorem ends_y : M.ends E.y = s(C.b C.n, M.atom (M.mate E.y)) := by unfold Molecule.ends; rw [E.hy]

/-! ### `ℓ` an exit -/

section Exit
variable (e : D) (he : M.ends e = M.ends E.x)
include he

omit [DecidableEq D] in
theorem exit_ends : M.atom e ∈ ({C.a C.n, M.atom (M.mate E.x)} : Finset V) ∧
    M.atom (M.mate e) ∈ ({C.a C.n, M.atom (M.mate E.x)} : Finset V) := by
  have h := he
  rw [E.ends_x] at h
  change s(M.atom e, M.atom (M.mate e)) = _ at h
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

/-- The chain on `𝕄 ∖ {ℓ}`. -/
def exitChain : YChain (MoleProp.eraseBond M e) :=
  C.onErase e (fun p hp q hq => by
      rw [he, E.ends_x]
      exact sym2_ne_of_right (fun h => E.hxo (h ▸ hp)) (fun h => E.hxo (h ▸ hq)))
    (fun i hi => by
      have hne : ∀ v ∈ ({C.a C.n, M.atom (M.mate E.x)} : Finset V), v ≠ C.a i ∧ v ≠ C.b i := by
        intro v hv
        simp only [mem_insert, mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact ⟨fun h => by have := C.inj_a _ le_rfl i hi.le h; omega, C.ne_ab _ le_rfl i hi.le⟩
        · exact ⟨fun h => E.hxo (h ▸ C.a_mem hi.le), fun h => E.hxo (h ▸ C.b_mem hi.le)⟩
      obtain ⟨h1, h2⟩ := E.exit_ends e he
      exact ⟨(hne _ h1).1, (hne _ h1).2, (hne _ h2).1, (hne _ h2).2⟩)

/-- The other exit is the only attachment: a (Y1), case 2 ending on `𝕄 ∖ {ℓ}`. -/
def exitEnd : Y1End2 (E.exitChain e he) where
  x := ⟨E.y, ne_of_ends_ne M e (by
    rw [he, E.ends_x, E.ends_y]
    exact sym2_ne_of_left (fun h => C.ne_ab _ le_rfl _ le_rfl h.symm) (fun h => E.hxo (h ▸ C.b_mem le_rfl)))⟩
  hx := Or.inr E.hy
  hxo := E.hyo
  hdeg := by
    have h := he
    rw [E.ends_x] at h
    have ha := deg_eraseBond_of_ends M e h (C.a C.n)
    have hb := deg_eraseBond_of_ends M e h (C.b C.n)
    have hc : M.atom (M.mate E.x) ≠ C.a C.n := fun h' => E.hxo (h' ▸ C.a_mem le_rfl)
    have hc' : M.atom (M.mate E.x) ≠ C.b C.n := fun h' => E.hxo (h' ▸ C.b_mem le_rfl)
    have hab : C.a C.n ≠ C.b C.n := C.ne_ab _ le_rfl _ le_rfl
    simp only [hc, hc', hab, ite_true, ite_false, add_zero] at ha hb
    rw [E.deg_four _ (C.a_mem le_rfl)] at ha
    rw [E.deg_four _ (C.b_mem le_rfl)] at hb
    change (MoleProp.eraseBond M e).deg (C.a C.n) + (MoleProp.eraseBond M e).deg (C.b C.n) = 7
    omega

/-- **`ℓ` an exit.** -/
theorem exit_case {d : ℕ} {L γ δ η C1 : ℝ} (P : Finset V → ℝ)
    (hY1 : ∀ (C' : YChain (MoleProp.eraseBond M e)), Y1End2 C' →
      AFree (MoleProp.eraseBond M e) d L γ δ η C1 P ≤
        AFree (Degen.eraseAtoms (MoleProp.eraseBond M e) C'.set) d L γ δ η C1 P) :
    AFree (MoleProp.eraseBond M e) d L γ δ η C1 P ≤ AFree (Degen.eraseAtoms M C.set) d L γ δ η C1 P := by
  refine (hY1 _ (E.exitEnd e he)).trans ?_
  have hY : M.atom e ∈ C.set ∨ M.atom (M.mate e) ∈ C.set := by
    have h := he
    rw [E.ends_x] at h
    change s(M.atom e, M.atom (M.mate e)) = _ at h
    rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact Or.inl (h1 ▸ C.a_mem le_rfl)
    · exact Or.inr (h2 ▸ C.a_mem le_rfl)
  exact afree_eraseBond_erase_le M e C.set hY L γ δ η C1 P

end Exit

/-! ### `ℓ` a copy of the triple bond -/

include E in
/-- **`ℓ` a copy of the triple bond.** -/
theorem triple_case (e : D) (he : M.ends e = s(C.a 0, C.b 0)) {d : ℕ} {L γ δ η C1 : ℝ} (P : Finset V → ℝ)
    (hpeel : ∀ Lad : Ladder3 (MoleProp.eraseBond M e), AFree (MoleProp.eraseBond M e) d L γ δ η C1 P ≤
      AFree (Degen.eraseAtoms (MoleProp.eraseBond M e) Lad.set) d L γ δ η C1 P) :
    AFree (MoleProp.eraseBond M e) d L γ δ η C1 P ≤ AFree (Degen.eraseAtoms M C.set) d L γ δ η C1 P := by
  have h0 : (0 : ℕ) ≤ C.n := Nat.zero_le _
  have hab : C.a 0 ≠ C.b 0 := C.ne_ab 0 h0 0 h0
  let Lad := E.ladderFrom (MoleProp.eraseBond M e) 0 h0 (fun i _ hi => C.mem i hi)
    (by have := bondsBetween_eraseBond_of_ends M e he (C.a 0) (C.b 0); rw [C.triple] at this; simpa using this)
    (fun p q _ _ hne => by
      have := bondsBetween_eraseBond_of_ends M e he p q
      rw [ite_of_not (Ne.symm hne), add_zero] at this; exact this)
    (by
      have ha := deg_eraseBond_of_ends M e he (C.a 0)
      have hb := deg_eraseBond_of_ends M e he (C.b 0)
      rw [ite_of_pos rfl, ite_of_not hab.symm] at ha
      rw [ite_of_not hab, ite_of_pos rfl] at hb
      rw [E.deg_four _ (C.a_mem h0)] at ha
      rw [E.deg_four _ (C.b_mem h0)] at hb
      omega)
    (fun i hi hin => by
      have ha := deg_eraseBond_of_ends M e he (C.a i)
      have hb := deg_eraseBond_of_ends M e he (C.b i)
      have h1 : C.a 0 ≠ C.a i := fun h => by have := C.inj_a 0 h0 i hin h; omega
      have h2 : C.b 0 ≠ C.a i := fun h => C.ne_ab i hin 0 h0 h.symm
      have h3 : C.a 0 ≠ C.b i := C.ne_ab 0 h0 i hin
      have h4 : C.b 0 ≠ C.b i := fun h => by have := C.inj_b 0 h0 i hin h; omega
      simp only [h1, h2, h3, h4, ite_false, add_zero] at ha hb
      exact ⟨ha, hb⟩)
  have hset : Lad.set = C.set := (E.ladderFrom_set _ _ _ _ _ _ _ _).trans C.upper_zero
  refine (hpeel Lad).trans ?_
  rw [hset]
  have hY : M.atom e ∈ C.set ∨ M.atom (M.mate e) ∈ C.set := by
    change s(M.atom e, M.atom (M.mate e)) = _ at he
    rcases Sym2.eq_iff.mp he with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Or.inl (h1 ▸ C.a_mem h0)
    · exact Or.inl (h1 ▸ C.b_mem h0)
  exact afree_eraseBond_erase_le M e C.set hY L γ δ η C1 P

/-! ### `ℓ` a rail -/

include E in
/-- **`ℓ` the rail `a k – a (k + 1)`.** -/
theorem rail_a_case {k : ℕ} (hk : k < C.n) (e : D) (he : M.ends e = s(C.a k, C.a (k + 1))) {d : ℕ}
    {L γ δ η C1 : ℝ} (P : Finset V → ℝ)
    (hY1 : ∀ (C' : YChain (MoleProp.eraseBond M e)), Y1End2 C' →
      AFree (MoleProp.eraseBond M e) d L γ δ η C1 P ≤
        AFree (Degen.eraseAtoms (MoleProp.eraseBond M e) C'.set) d L γ δ η C1 P)
    (hpeel : ∀ (Y : Finset V) (Lad : Ladder3 (Degen.eraseAtoms (MoleProp.eraseBond M e) Y)),
      AFree (Degen.eraseAtoms (MoleProp.eraseBond M e) Y) d L γ δ η C1 P ≤
        AFree (Degen.eraseAtoms (Degen.eraseAtoms (MoleProp.eraseBond M e) Y) Lad.set) d L γ δ η C1 P) :
    AFree (MoleProp.eraseBond M e) d L γ δ η C1 P ≤ AFree (Degen.eraseAtoms M C.set) d L γ δ η C1 P := by
  classical
  have hkn : k ≤ C.n := hk.le
  have hak : C.a k ≠ C.a (k + 1) := fun h => by have := C.inj_a k hkn (k + 1) hk h; omega
  have hends : ∀ v, M.atom e = v ∨ M.atom (M.mate e) = v → v = C.a k ∨ v = C.a (k + 1) := by
    intro v hv
    change s(M.atom e, M.atom (M.mate e)) = _ at he
    rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hv with rfl | rfl <;> tauto
  -- the lower chain on `𝕄 ∖ {ℓ}`
  have hout : ∀ p ∈ (C.low k hkn).set, ∀ q ∈ (C.low k hkn).set, M.ends e ≠ s(p, q) := fun p hp q hq => by
    rw [he]
    exact sym2_ne_of_right (fun h => C.a_notMem_low hkn (by omega) hk (by rw [h]; exact hp))
      (fun h => C.a_notMem_low hkn (by omega) hk (by rw [h]; exact hq))
  have hlow : ∀ i < (C.low k hkn).n, M.atom e ≠ (C.low k hkn).a i ∧ M.atom e ≠ (C.low k hkn).b i ∧
      M.atom (M.mate e) ≠ (C.low k hkn).a i ∧ M.atom (M.mate e) ≠ (C.low k hkn).b i := by
    intro i hi
    change i < k at hi
    have hne : ∀ v, v = C.a k ∨ v = C.a (k + 1) → v ≠ C.a i ∧ v ≠ C.b i := by
      rintro v (rfl | rfl)
      · exact ⟨fun h => by have := C.inj_a k hkn i (by omega) h; omega, C.ne_ab k hkn i (by omega)⟩
      · exact ⟨fun h => by have := C.inj_a (k + 1) hk i (by omega) h; omega, C.ne_ab (k + 1) hk i (by omega)⟩
    exact ⟨(hne _ (hends _ (Or.inl rfl))).1, (hne _ (hends _ (Or.inl rfl))).2,
      (hne _ (hends _ (Or.inr rfl))).1, (hne _ (hends _ (Or.inr rfl))).2⟩
  -- its (Y1), case 2 ending: the rail `b k – b (k + 1)`
  have hbr : (MoleProp.eraseBond M e).bondsBetween (C.b k) (C.b (k + 1)) = 1 := by
    have := bondsBetween_eraseBond_of_ends M e he (C.b k) (C.b (k + 1))
    rw [ite_of_not (sym2_ne_of_left (C.ne_ab k hkn k hkn) (C.ne_ab k hkn (k + 1) hk)), add_zero,
      (C.rail k hk).2] at this
    exact this
  have hbne : C.b k ≠ C.b (k + 1) := fun h => by have := C.inj_b k hkn (k + 1) hk h; omega
  rw [← Degen.card_neighborDarts _ hbne] at hbr
  obtain ⟨z, hz⟩ := card_pos.mp (by omega :
    0 < (Degen.neighborDarts (MoleProp.eraseBond M e) (C.b k) (C.b (k + 1))).card)
  obtain ⟨hz1, hz2⟩ := (Degen.mem_neighborDarts _ _ _ z).mp hz
  have da := deg_eraseBond_of_ends M e he (C.a k)
  rw [ite_of_pos rfl, ite_of_not hak.symm, add_zero, E.deg_four _ (C.a_mem hkn)] at da
  have db := deg_eraseBond_of_ends M e he (C.b k)
  rw [ite_of_not (C.ne_ab k hkn k hkn), ite_of_not (C.ne_ab (k + 1) hk k hkn), add_zero, add_zero,
    E.deg_four _ (C.b_mem hkn)] at db
  let El : Y1End2 ((C.low k hkn).onErase e hout hlow) :=
    ⟨z, Or.inr hz1, by rw [hz2]; exact C.b_notMem_low hkn (by omega) hk, by
      change (MoleProp.eraseBond M e).deg (C.a k) + (MoleProp.eraseBond M e).deg (C.b k) = 7; omega⟩
  have step1 := hY1 _ El
  -- the upper ladder on `(𝕄 ∖ {ℓ}) ∖ lower`
  have hupl : ∀ v ∈ C.upper (k + 1), v ∉ (C.low k hkn).set := by
    intro v hv
    obtain ⟨i, h1, h2, rfl | rfl⟩ := C.mem_upper.mp hv
    · exact C.a_notMem_low hkn (by omega) h2
    · exact C.b_notMem_low hkn (by omega) h2
  have hakU : C.a k ∉ C.upper (k + 1) := by
    intro h
    obtain ⟨i, h1, h2, h | h⟩ := C.mem_upper.mp h
    · have := C.inj_a k hkn i h2 h; omega
    · exact C.ne_ab k hkn i h2 h
  have hbbN : ∀ p q : V, p ∈ C.upper (k + 1) → q ∈ C.upper (k + 1) →
      (MoleProp.eraseBond M e).bondsBetween p q = M.bondsBetween p q := by
    intro p q hp hq
    have := bondsBetween_eraseBond_of_ends M e he p q
    rw [ite_of_not (sym2_ne_of_left (fun h => hakU (by rw [h]; exact hp)) (fun h => hakU (by rw [h]; exact hq))),
      add_zero] at this
    exact this
  have hU : ∀ i, k + 1 ≤ i → i ≤ C.n → C.a i ∈ C.upper (k + 1) ∧ C.b i ∈ C.upper (k + 1) := fun i h1 h2 =>
    ⟨C.mem_upper.mpr ⟨i, h1, h2, Or.inl rfl⟩, C.mem_upper.mpr ⟨i, h1, h2, Or.inr rfl⟩⟩
  have hmem' : ∀ i, k + 1 ≤ i → i ≤ C.n →
      C.a i ∈ (Degen.eraseAtoms (MoleProp.eraseBond M e) (C.low k hkn).set).atoms ∧
        C.b i ∈ (Degen.eraseAtoms (MoleProp.eraseBond M e) (C.low k hkn).set).atoms := fun i h1 h2 =>
    ⟨mem_sdiff.mpr ⟨(C.mem i h2).1, C.a_notMem_low hkn (by omega) h2⟩,
      mem_sdiff.mpr ⟨(C.mem i h2).2, C.b_notMem_low hkn (by omega) h2⟩⟩
  have hbb' : ∀ p q : V, p ∈ C.upper (k + 1) → q ∈ C.upper (k + 1) →
      (Degen.eraseAtoms (MoleProp.eraseBond M e) (C.low k hkn).set).bondsBetween p q = M.bondsBetween p q :=
    fun p q hp hq => by
      rw [Degen.bondsBetween_erase_eq _ _ (hupl p hp) (hupl q hq)]; exact hbbN p q hp hq
  have hrung' : (Degen.eraseAtoms (MoleProp.eraseBond M e) (C.low k hkn).set).bondsBetween
      (C.a (k + 1)) (C.b (k + 1)) = 2 := by
    rw [hbb' _ _ (hU _ le_rfl hk).1 (hU _ le_rfl hk).2]; exact C.rung (k + 1) (by omega) hk
  -- degrees after erasing the lower chain
  have hsplit : ∀ v, v ∉ (C.low k hkn).set →
      (Degen.eraseAtoms (MoleProp.eraseBond M e) (C.low k hkn).set).deg v +
        ∑ w ∈ (C.low k hkn).set, (MoleProp.eraseBond M e).bondsBetween v w = (MoleProp.eraseBond M e).deg v :=
    fun v hv => by
      have h1 := deg_eraseAtoms_add (N := MoleProp.eraseBond M e) (C.low k hkn).set hv
      unfold Degen.removedDartsAt at h1
      rw [YChain.card_darts_toward (M := MoleProp.eraseBond M e) v (C.low k hkn).set hv] at h1
      exact h1
  have hSa : ∑ w ∈ (C.low k hkn).set, (MoleProp.eraseBond M e).bondsBetween (C.a (k + 1)) w = 0 := by
    have h1 := sum_eraseBond_of_ends M e he (C.a (k + 1)) (C.low k hkn).set
    rw [E.sum_low_a hk (by omega) hk, ite_of_pos rfl] at h1
    have h2 := single_le_sum (f := fun w => if s(C.a k, C.a (k + 1)) = s(C.a (k + 1), w) then 1 else 0)
      (fun _ _ => Nat.zero_le _) ((C.low k hkn).a_mem le_rfl)
    change (if s(C.a k, C.a (k + 1)) = s(C.a (k + 1), C.a k) then 1 else 0) ≤ _ at h2
    rw [ite_of_pos Sym2.eq_swap] at h2
    omega
  have hSb : ∑ w ∈ (C.low k hkn).set, (MoleProp.eraseBond M e).bondsBetween (C.b (k + 1)) w = 1 := by
    have h1 := sum_eraseBond_of_ends M e he (C.b (k + 1)) (C.low k hkn).set
    rw [E.sum_low_b hk (by omega) hk, ite_of_pos rfl] at h1
    have h2 : ∑ w ∈ (C.low k hkn).set, (if s(C.a k, C.a (k + 1)) = s(C.b (k + 1), w) then 1 else 0) = 0 :=
      sum_eq_zero fun w _ => ite_of_not (Ne.symm (sym2_ne_of_left (C.ne_ab k hkn (k + 1) hk).symm
        (C.ne_ab (k + 1) hk (k + 1) hk).symm))
    rw [h2, add_zero] at h1
    exact h1
  have hdeg0' : (Degen.eraseAtoms (MoleProp.eraseBond M e) (C.low k hkn).set).deg (C.a (k + 1)) = 3 ∧
      (Degen.eraseAtoms (MoleProp.eraseBond M e) (C.low k hkn).set).deg (C.b (k + 1)) = 3 := by
    have ha := hsplit _ (C.a_notMem_low hkn (j := k + 1) (by omega) hk)
    have hb := hsplit _ (C.b_notMem_low hkn (j := k + 1) (by omega) hk)
    rw [hSa, add_zero] at ha
    rw [hSb] at hb
    have da' := deg_eraseBond_of_ends M e he (C.a (k + 1))
    rw [ite_of_not hak, ite_of_pos rfl, E.deg_four _ (C.a_mem (i := k + 1) hk)] at da'
    have db' := deg_eraseBond_of_ends M e he (C.b (k + 1))
    rw [ite_of_not (C.ne_ab k hkn (k + 1) hk), ite_of_not (C.ne_ab (k + 1) hk (k + 1) hk), add_zero, add_zero,
      E.deg_four _ (C.b_mem (i := k + 1) hk)] at db'
    omega
  have hdeg' : ∀ i, k + 1 < i → i ≤ C.n →
      (Degen.eraseAtoms (MoleProp.eraseBond M e) (C.low k hkn).set).deg (C.a i) = M.deg (C.a i) ∧
        (Degen.eraseAtoms (MoleProp.eraseBond M e) (C.low k hkn).set).deg (C.b i) = M.deg (C.b i) := by
    intro i h1 h2
    have ha := hsplit _ (C.a_notMem_low hkn (by omega) h2)
    have hb := hsplit _ (C.b_notMem_low hkn (by omega) h2)
    have za : ∑ w ∈ (C.low k hkn).set, (MoleProp.eraseBond M e).bondsBetween (C.a i) w = 0 := by
      have := E.sum_low_a hk (by omega) h2
      rw [ite_of_not (by omega)] at this
      exact Nat.eq_zero_of_le_zero (this ▸ sum_le_sum fun w _ => bondsBetween_eraseBond_le' M e _ w)
    have zb : ∑ w ∈ (C.low k hkn).set, (MoleProp.eraseBond M e).bondsBetween (C.b i) w = 0 := by
      have := E.sum_low_b hk (by omega) h2
      rw [ite_of_not (by omega)] at this
      exact Nat.eq_zero_of_le_zero (this ▸ sum_le_sum fun w _ => bondsBetween_eraseBond_le' M e _ w)
    rw [za, add_zero] at ha
    rw [zb, add_zero] at hb
    have n1 : C.a k ≠ C.a i := fun h => by have := C.inj_a k hkn i h2 h; omega
    have n2 : C.a (k + 1) ≠ C.a i := fun h => by have := C.inj_a (k + 1) hk i h2 h; omega
    have ga := deg_eraseBond_of_ends M e he (C.a i)
    rw [ite_of_not n1, ite_of_not n2, add_zero, add_zero] at ga
    have gb := deg_eraseBond_of_ends M e he (C.b i)
    rw [ite_of_not (C.ne_ab k hkn i h2), ite_of_not (C.ne_ab (k + 1) hk i h2), add_zero, add_zero] at gb
    rw [ha, hb]
    exact ⟨ga, gb⟩
  have step2 := hpeel (C.low k hkn).set
    (E.ladderFrom _ (k + 1) hk hmem' hrung' (fun p q hp hq _ => hbb' p q hp hq) hdeg0' hdeg')
  rw [E.ladderFrom_set] at step2
  have step3 := afree_erase_erase_le (MoleProp.eraseBond M e) (C.low k hkn).set (C.upper (k + 1)) (d := d) L γ δ η C1 P
  rw [C.low_union_upper hk] at step3
  have hY : M.atom e ∈ C.set ∨ M.atom (M.mate e) ∈ C.set := by
    rcases hends _ (Or.inl rfl) with h | h
    · exact Or.inl (h ▸ C.a_mem hkn)
    · exact Or.inl (h ▸ C.a_mem hk)
  exact step1.trans (step2.trans (step3.trans (afree_eraseBond_erase_le M e C.set hY L γ δ η C1 P)))

include E in
/-- **`ℓ` the rail `b k – b (k + 1)`** (mirror of `rail_a_case`). -/
theorem rail_b_case {k : ℕ} (hk : k < C.n) (e : D) (he : M.ends e = s(C.b k, C.b (k + 1))) {d : ℕ}
    {L γ δ η C1 : ℝ} (P : Finset V → ℝ)
    (hY1 : ∀ (C' : YChain (MoleProp.eraseBond M e)), Y1End2 C' →
      AFree (MoleProp.eraseBond M e) d L γ δ η C1 P ≤
        AFree (Degen.eraseAtoms (MoleProp.eraseBond M e) C'.set) d L γ δ η C1 P)
    (hpeel : ∀ (Y : Finset V) (Lad : Ladder3 (Degen.eraseAtoms (MoleProp.eraseBond M e) Y)),
      AFree (Degen.eraseAtoms (MoleProp.eraseBond M e) Y) d L γ δ η C1 P ≤
        AFree (Degen.eraseAtoms (Degen.eraseAtoms (MoleProp.eraseBond M e) Y) Lad.set) d L γ δ η C1 P) :
    AFree (MoleProp.eraseBond M e) d L γ δ η C1 P ≤ AFree (Degen.eraseAtoms M C.set) d L γ δ η C1 P := by
  have h := E.swap.rail_a_case (C := C.swap) hk e he P hY1 hpeel
  rwa [C.swap_set] at h

end Y2End
end WaveTurbulence.MoleProp4
