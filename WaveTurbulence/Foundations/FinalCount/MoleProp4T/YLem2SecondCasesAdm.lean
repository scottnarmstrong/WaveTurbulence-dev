/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.YLem2SecondCases
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.AdmBounds
import Mathlib.Tactic

/-! # `ylem2`, second statement, cases exit / triple copy / rail, for any admissibility

As `YLem2SecondCases`, with the decorations of `𝕄 ∖ {ℓ}` restricted by any `Adm ⊆ lgAdm`. The decorations of
`𝕄 ∖ chain` obtained are restrictions of `Adm`-decorations, so any condition `Φ` that holds for the restriction of
every `Adm`-decoration (`resY`) persists.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The restriction of a decoration of `𝕄 ∖ {ℓ}` to the darts away from `Y` (`ℓ` has an end in `Y`). -/
def resY (M : Molecule V D) (e : D) (Y : Finset V) (he : M.atom e ∈ Y ∨ M.atom (M.mate e) ∈ Y) {d : ℕ}
    (κ : MoleProp.WithoutBondDart M e → (Fin d → ℤ)) : Degen.RetainedDart M Y → (Fin d → ℤ) :=
  fun y => κ ((eraseBondEraseEquiv M e Y he).symm y).val

/-- Transporting restricted decorations from `(𝕄 ∖ {ℓ}) ∖ Y` to `𝕄 ∖ Y`, keeping any condition on restrictions. -/
theorem countAFree_eraseBond_erase_adm (M : Molecule V D) (e : D) (Y : Finset V)
    (he : M.atom e ∈ Y ∨ M.atom (M.mate e) ∈ Y) {d : ℕ} {L γ δ η C1 : ℝ} {P : Finset V → ℝ}
    {Adm : (MoleProp.WithoutBondDart M e → (Fin d → ℤ)) → Prop}
    (hAdm : ∀ κ, Adm κ → lgAdm (MoleProp.eraseBond M e) L γ η P κ)
    {Φ : (Degen.RetainedDart M Y → (Fin d → ℤ)) → Prop} (hΦ : ∀ κ, Adm κ → Φ (resY M e Y he κ)) :
    MoleProp.countAFree (Degen.eraseAtoms (MoleProp.eraseBond M e) Y) L γ δ C1 (0 : Mom d)
        (MoleProp.erasedFreeAdmissibility (MoleProp.eraseBond M e) Y Adm) P ≤
      MoleProp.countAFree (Degen.eraseAtoms M Y) L γ δ C1 (0 : Mom d)
        (fun τ => lgAdm (Degen.eraseAtoms M Y) L γ η P τ ∧ Φ τ) P := by
  refine MoleProp.countAFree_le_of_dart_equiv _ _ (eraseBondEraseEquiv M e Y he) rfl (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) L γ δ C1 0 _ _ (fun κ' h => ⟨?_, ?_⟩) P
  · exact lgAdm_relabel _ _ (eraseBondEraseEquiv M e Y he) rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (erasedFree_sub_lgAdm _ _ hAdm κ' h)
  · obtain ⟨κ, hκ, _, rfl⟩ := h
    exact hΦ κ hκ

namespace Y2End
variable {M : Molecule V D} {C : YChain M} (E : Y2End C)

/-- **`ℓ` an exit, any admissibility.** -/
theorem exit_case_adm (e : D) (he : M.ends e = M.ends E.x) {d : ℕ} {L γ δ η C1 : ℝ} (P : Finset V → ℝ) (S : Finset V) (hS : C.set = S)
    (hYe : M.atom e ∈ S ∨ M.atom (M.mate e) ∈ S)
    (Adm : (MoleProp.WithoutBondDart M e → (Fin d → ℤ)) → Prop)
    (hAdm : ∀ κ, Adm κ → lgAdm (MoleProp.eraseBond M e) L γ η P κ)
    (Φ : (Degen.RetainedDart M S → (Fin d → ℤ)) → Prop) (hΦ : ∀ κ, Adm κ → Φ (resY M e S hYe κ))
    (hY1 : ∀ (C' : YChain (MoleProp.eraseBond M e)), Y1End2 C' →
      ∀ Adm' : (MoleProp.WithoutBondDart M e → (Fin d → ℤ)) → Prop,
      (∀ κ, Adm' κ → lgAdm (MoleProp.eraseBond M e) L γ η P κ) →
      MoleProp.countAFree (MoleProp.eraseBond M e) L γ δ C1 (0 : Mom d) Adm' P ≤
        MoleProp.countAFree (Degen.eraseAtoms (MoleProp.eraseBond M e) C'.set) L γ δ C1 (0 : Mom d)
          (MoleProp.erasedFreeAdmissibility (MoleProp.eraseBond M e) C'.set Adm') P):
    MoleProp.countAFree (MoleProp.eraseBond M e) L γ δ C1 (0 : Mom d) Adm P ≤
      MoleProp.countAFree (Degen.eraseAtoms M S) L γ δ C1 (0 : Mom d)
        (fun τ => lgAdm (Degen.eraseAtoms M S) L γ η P τ ∧ Φ τ) P := by
  subst hS
  exact (hY1 _ (E.exitEnd e he) Adm hAdm).trans (countAFree_eraseBond_erase_adm M e C.set hYe hAdm hΦ)

include E in
/-- **`ℓ` a copy of the triple bond, any admissibility.** -/
theorem triple_case_adm (e : D) (he : M.ends e = s(C.a 0, C.b 0)) {d : ℕ} {L γ δ η C1 : ℝ} (P : Finset V → ℝ) (S : Finset V) (hS : C.set = S)
    (hYe : M.atom e ∈ S ∨ M.atom (M.mate e) ∈ S)
    (Adm : (MoleProp.WithoutBondDart M e → (Fin d → ℤ)) → Prop)
    (hAdm : ∀ κ, Adm κ → lgAdm (MoleProp.eraseBond M e) L γ η P κ)
    (Φ : (Degen.RetainedDart M S → (Fin d → ℤ)) → Prop) (hΦ : ∀ κ, Adm κ → Φ (resY M e S hYe κ))
    (hpeel : ∀ (Lad : Ladder3 (MoleProp.eraseBond M e)) (Adm' : (MoleProp.WithoutBondDart M e → (Fin d → ℤ)) → Prop),
      (∀ κ, Adm' κ → lgAdm (MoleProp.eraseBond M e) L γ η P κ) →
      MoleProp.countAFree (MoleProp.eraseBond M e) L γ δ C1 (0 : Mom d) Adm' P ≤
        MoleProp.countAFree (Degen.eraseAtoms (MoleProp.eraseBond M e) Lad.set) L γ δ C1 (0 : Mom d)
          (MoleProp.erasedFreeAdmissibility (MoleProp.eraseBond M e) Lad.set Adm') P):
    MoleProp.countAFree (MoleProp.eraseBond M e) L γ δ C1 (0 : Mom d) Adm P ≤
      MoleProp.countAFree (Degen.eraseAtoms M S) L γ δ C1 (0 : Mom d)
        (fun τ => lgAdm (Degen.eraseAtoms M S) L γ η P τ ∧ Φ τ) P := by
  subst hS
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
  have h := hpeel Lad Adm hAdm
  rw [hset] at h
  exact h.trans (countAFree_eraseBond_erase_adm M e C.set hYe hAdm hΦ)

include E in
/-- **`ℓ` the rail `a k – a (k + 1)`, any admissibility.** -/
theorem rail_a_case_adm {k : ℕ} (hk : k < C.n) (e : D) (he : M.ends e = s(C.a k, C.a (k + 1))) {d : ℕ} {L γ δ η C1 : ℝ} (P : Finset V → ℝ) (S : Finset V) (hS : C.set = S)
    (hYe : M.atom e ∈ S ∨ M.atom (M.mate e) ∈ S)
    (Adm : (MoleProp.WithoutBondDart M e → (Fin d → ℤ)) → Prop)
    (hAdm : ∀ κ, Adm κ → lgAdm (MoleProp.eraseBond M e) L γ η P κ)
    (Φ : (Degen.RetainedDart M S → (Fin d → ℤ)) → Prop) (hΦ : ∀ κ, Adm κ → Φ (resY M e S hYe κ))
    (hY1 : ∀ (C' : YChain (MoleProp.eraseBond M e)), Y1End2 C' →
      ∀ Adm' : (MoleProp.WithoutBondDart M e → (Fin d → ℤ)) → Prop,
      (∀ κ, Adm' κ → lgAdm (MoleProp.eraseBond M e) L γ η P κ) →
      MoleProp.countAFree (MoleProp.eraseBond M e) L γ δ C1 (0 : Mom d) Adm' P ≤
        MoleProp.countAFree (Degen.eraseAtoms (MoleProp.eraseBond M e) C'.set) L γ δ C1 (0 : Mom d)
          (MoleProp.erasedFreeAdmissibility (MoleProp.eraseBond M e) C'.set Adm') P)
    (hpeel : ∀ (Y : Finset V) (Lad : Ladder3 (Degen.eraseAtoms (MoleProp.eraseBond M e) Y))
      (Adm' : (Degen.RetainedDart (MoleProp.eraseBond M e) Y → (Fin d → ℤ)) → Prop),
      (∀ κ, Adm' κ → lgAdm (Degen.eraseAtoms (MoleProp.eraseBond M e) Y) L γ η P κ) →
      MoleProp.countAFree (Degen.eraseAtoms (MoleProp.eraseBond M e) Y) L γ δ C1 (0 : Mom d) Adm' P ≤
        MoleProp.countAFree (Degen.eraseAtoms (Degen.eraseAtoms (MoleProp.eraseBond M e) Y) Lad.set) L γ δ C1
          (0 : Mom d) (MoleProp.erasedFreeAdmissibility (Degen.eraseAtoms (MoleProp.eraseBond M e) Y) Lad.set Adm') P):
    MoleProp.countAFree (MoleProp.eraseBond M e) L γ δ C1 (0 : Mom d) Adm P ≤
      MoleProp.countAFree (Degen.eraseAtoms M S) L γ δ C1 (0 : Mom d)
        (fun τ => lgAdm (Degen.eraseAtoms M S) L γ η P τ ∧ Φ τ) P := by
  subst hS
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
  have step1 := hY1 _ El Adm hAdm
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
    (MoleProp.erasedFreeAdmissibility (MoleProp.eraseBond M e) (C.low k hkn).set Adm)
    (erasedFree_sub_lgAdm _ _ hAdm)
  rw [E.ladderFrom_set] at step2
  have step3 := MoleProp.countAFree_erase_twice_le_union (MoleProp.eraseBond M e) (C.low k hkn).set
    (C.upper (k + 1)) L γ δ C1 (0 : Mom d) Adm P
  rw [C.low_union_upper hk] at step3
  exact step1.trans (step2.trans (step3.trans (countAFree_eraseBond_erase_adm M e C.set hYe hAdm hΦ)))

include E in
/-- **`ℓ` the rail `b k – b (k + 1)`, any admissibility** (mirror). -/
theorem rail_b_case_adm {k : ℕ} (hk : k < C.n) (e : D) (he : M.ends e = s(C.b k, C.b (k + 1))) {d : ℕ} {L γ δ η C1 : ℝ} (P : Finset V → ℝ) (S : Finset V) (hS : C.set = S)
    (hYe : M.atom e ∈ S ∨ M.atom (M.mate e) ∈ S)
    (Adm : (MoleProp.WithoutBondDart M e → (Fin d → ℤ)) → Prop)
    (hAdm : ∀ κ, Adm κ → lgAdm (MoleProp.eraseBond M e) L γ η P κ)
    (Φ : (Degen.RetainedDart M S → (Fin d → ℤ)) → Prop) (hΦ : ∀ κ, Adm κ → Φ (resY M e S hYe κ))
    (hY1 : ∀ (C' : YChain (MoleProp.eraseBond M e)), Y1End2 C' →
      ∀ Adm' : (MoleProp.WithoutBondDart M e → (Fin d → ℤ)) → Prop,
      (∀ κ, Adm' κ → lgAdm (MoleProp.eraseBond M e) L γ η P κ) →
      MoleProp.countAFree (MoleProp.eraseBond M e) L γ δ C1 (0 : Mom d) Adm' P ≤
        MoleProp.countAFree (Degen.eraseAtoms (MoleProp.eraseBond M e) C'.set) L γ δ C1 (0 : Mom d)
          (MoleProp.erasedFreeAdmissibility (MoleProp.eraseBond M e) C'.set Adm') P)
    (hpeel : ∀ (Y : Finset V) (Lad : Ladder3 (Degen.eraseAtoms (MoleProp.eraseBond M e) Y))
      (Adm' : (Degen.RetainedDart (MoleProp.eraseBond M e) Y → (Fin d → ℤ)) → Prop),
      (∀ κ, Adm' κ → lgAdm (Degen.eraseAtoms (MoleProp.eraseBond M e) Y) L γ η P κ) →
      MoleProp.countAFree (Degen.eraseAtoms (MoleProp.eraseBond M e) Y) L γ δ C1 (0 : Mom d) Adm' P ≤
        MoleProp.countAFree (Degen.eraseAtoms (Degen.eraseAtoms (MoleProp.eraseBond M e) Y) Lad.set) L γ δ C1
          (0 : Mom d) (MoleProp.erasedFreeAdmissibility (Degen.eraseAtoms (MoleProp.eraseBond M e) Y) Lad.set Adm') P) :
    MoleProp.countAFree (MoleProp.eraseBond M e) L γ δ C1 (0 : Mom d) Adm P ≤
      MoleProp.countAFree (Degen.eraseAtoms M S) L γ δ C1 (0 : Mom d)
        (fun τ => lgAdm (Degen.eraseAtoms M S) L γ η P τ ∧ Φ τ) P :=
  E.swap.rail_a_case_adm (C := C.swap) hk e he P S (C.swap_set.trans hS) hYe Adm hAdm Φ hΦ hY1 hpeel

end Y2End
end WaveTurbulence.MoleProp4
