/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.PostFacts
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.ChainLadder
import Mathlib.Tactic

/-! # `ylem2`, second statement: `ℓ` a copy of a rung

`ℓ` a copy of the double bond `a i = b i`, `i ≥ 1`. In `𝕄 ∖ {ℓ}`, the pairs below `i` form a chain with a (Y2) ending
(exits: the rails into `a i`, `b i`), so the first statement replaces them by one new bond `b i → a i` (or reverse).
In the result, pair `i` is again a double bond, now of two degree-three atoms, and the pairs from `i` on are peeled by
operation (b). Loss: the (Y2) constant, and the LG parameter `η → η/2`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4
universe u v
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace Y2End
variable {M : Molecule V D} {C : YChain M} (E : Y2End C)

include E in
/-- **`ℓ` a copy of the rung `a i = b i`, `i ≥ 1`.** -/
theorem rung_case {i : ℕ} (hi0 : 0 < i) (hi : i ≤ C.n) (e : D) (he : M.ends e = s(C.a i, C.b i))
    (hcapN : ∀ v ∈ (MoleProp.eraseBond M e).atoms, (MoleProp.eraseBond M e).outdeg v ≤ 2 ∧
      (MoleProp.eraseBond M e).indeg v ≤ 2)
    (hconnN : ∀ u ∈ (MoleProp.eraseBond M e).atoms, ∀ w ∈ (MoleProp.eraseBond M e).atoms,
      (MoleProp.eraseBond M e).SameComponent u w)
    {d : ℕ} {L γ δ η C1 K : ℝ} (P : Finset V → ℝ)
    (hY2 : ∀ (C' : YChain (MoleProp.eraseBond M e)) (E' : Y2End C'),
      (∀ S ∈ MoleProp.ladderCells (E'.toTwoExit hcapN).post, (E'.toTwoExit hcapN).c ∈ S →
        GoodCell (E'.toTwoExit hcapN).post S) →
      AFree (MoleProp.eraseBond M e) d L γ δ η C1 P ≤
        ENNReal.ofReal K * AFreeSup (E'.toTwoExit hcapN).post d L γ δ (η / 2) C1)
    (hpeel : ∀ {W : Type v} [Fintype W] [DecidableEq W] (N2 : Molecule V W), N2.IsMolecule → ∀ Lad : Ladder3 N2,
      ∀ P' : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells N2, 0 ≤ P' S) →
        AFree N2 d L γ δ (η / 2) C1 P' ≤ AFree (Degen.eraseAtoms N2 Lad.set) d L γ δ (η / 2) C1 P') :
    AFree (MoleProp.eraseBond M e) d L γ δ η C1 P ≤
      ENNReal.ofReal K * AFreeSup (Degen.eraseAtoms M C.set) d L γ δ (η / 2) C1 := by
  classical
  have hk : i - 1 ≤ C.n := by omega
  have hi1 : i - 1 + 1 = i := Nat.sub_add_cancel hi0
  have hab : C.a i ≠ C.b i := C.ne_ab i hi i hi
  have hends : ∀ w, M.atom e = w ∨ M.atom (M.mate e) = w → w = C.a i ∨ w = C.b i := by
    intro w hw
    change s(M.atom e, M.atom (M.mate e)) = _ at he
    rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hw with rfl | rfl <;> tauto
  have hailo : C.a i ∉ (C.low (i - 1) hk).set := C.a_notMem_low hk (by omega) hi
  have hbilo : C.b i ∉ (C.low (i - 1) hk).set := C.b_notMem_low hk (by omega) hi
  -- the lower chain on `𝕄 ∖ {ℓ}`
  have hout : ∀ p ∈ (C.low (i - 1) hk).set, ∀ q ∈ (C.low (i - 1) hk).set, M.ends e ≠ s(p, q) :=
    fun p hp q hq => by
      rw [he]
      exact sym2_ne_of_left (fun h => hailo (by rw [h]; exact hp)) (fun h => hailo (by rw [h]; exact hq))
  have hlow : ∀ j < (C.low (i - 1) hk).n, M.atom e ≠ (C.low (i - 1) hk).a j ∧ M.atom e ≠ (C.low (i - 1) hk).b j ∧
      M.atom (M.mate e) ≠ (C.low (i - 1) hk).a j ∧ M.atom (M.mate e) ≠ (C.low (i - 1) hk).b j := by
    intro j hj
    change j < i - 1 at hj
    have hne : ∀ w, w = C.a i ∨ w = C.b i → w ≠ C.a j ∧ w ≠ C.b j := by
      rintro w (rfl | rfl)
      · exact ⟨fun h => by have := C.inj_a i hi j (by omega) h; omega, C.ne_ab i hi j (by omega)⟩
      · exact ⟨fun h => C.ne_ab j (by omega) i hi h.symm, fun h => by have := C.inj_b i hi j (by omega) h; omega⟩
    exact ⟨(hne _ (hends _ (Or.inl rfl))).1, (hne _ (hends _ (Or.inl rfl))).2,
      (hne _ (hends _ (Or.inr rfl))).1, (hne _ (hends _ (Or.inr rfl))).2⟩
  -- its exits: the rails into pair `i`
  have hra : (MoleProp.eraseBond M e).bondsBetween (C.a (i - 1)) (C.a i) = 1 := by
    have := bondsBetween_eraseBond_of_ends M e he (C.a (i - 1)) (C.a i)
    rw [ite_of_not (sym2_ne_of_right (fun h => C.ne_ab _ hk i hi h.symm) hab.symm), add_zero] at this
    rw [this]
    have := (C.rail (i - 1) (by omega)).1
    rwa [hi1] at this
  have hrb : (MoleProp.eraseBond M e).bondsBetween (C.b (i - 1)) (C.b i) = 1 := by
    have := bondsBetween_eraseBond_of_ends M e he (C.b (i - 1)) (C.b i)
    rw [ite_of_not (sym2_ne_of_left (C.ne_ab i hi _ hk) hab), add_zero] at this
    rw [this]
    have := (C.rail (i - 1) (by omega)).2
    rwa [hi1] at this
  have hane : C.a (i - 1) ≠ C.a i := fun h => by have := C.inj_a _ hk i hi h; omega
  have hbne : C.b (i - 1) ≠ C.b i := fun h => by have := C.inj_b _ hk i hi h; omega
  rw [← Degen.card_neighborDarts _ hane] at hra
  rw [← Degen.card_neighborDarts _ hbne] at hrb
  obtain ⟨x, hxm⟩ := card_pos.mp (by omega :
    0 < (Degen.neighborDarts (MoleProp.eraseBond M e) (C.a (i - 1)) (C.a i)).card)
  obtain ⟨y, hym⟩ := card_pos.mp (by omega :
    0 < (Degen.neighborDarts (MoleProp.eraseBond M e) (C.b (i - 1)) (C.b i)).card)
  obtain ⟨hx1, hx2⟩ := (Degen.mem_neighborDarts _ _ _ x).mp hxm
  obtain ⟨hy1, hy2⟩ := (Degen.mem_neighborDarts _ _ _ y).mp hym
  have hdegN : ∀ j ≤ C.n, j ≠ i → (MoleProp.eraseBond M e).deg (C.a j) = M.deg (C.a j) ∧
      (MoleProp.eraseBond M e).deg (C.b j) = M.deg (C.b j) := by
    intro j hj hji
    have ga := deg_eraseBond_of_ends M e he (C.a j)
    have gb := deg_eraseBond_of_ends M e he (C.b j)
    rw [ite_of_not (fun h => hji (C.inj_a i hi j hj h).symm), ite_of_not (fun h => C.ne_ab j hj i hi h.symm),
      add_zero, add_zero] at ga
    rw [ite_of_not (C.ne_ab i hi j hj), ite_of_not (fun h => hji (C.inj_b i hi j hj h).symm),
      add_zero, add_zero] at gb
    exact ⟨ga, gb⟩
  have hdeg3 : (MoleProp.eraseBond M e).deg (C.a i) = 3 ∧ (MoleProp.eraseBond M e).deg (C.b i) = 3 := by
    have ga := deg_eraseBond_of_ends M e he (C.a i)
    have gb := deg_eraseBond_of_ends M e he (C.b i)
    rw [ite_of_pos rfl, ite_of_not hab.symm, add_zero, E.deg_four _ (C.a_mem hi)] at ga
    rw [ite_of_not hab, ite_of_pos rfl, add_zero, E.deg_four _ (C.b_mem hi)] at gb
    omega
  let El : Y2End ((C.low (i - 1) hk).onErase e hout hlow) :=
    { x := x, y := y, hx := hx1, hy := hy1
      hxo := by rw [hx2]; exact hailo
      hyo := by rw [hy2]; exact hbilo
      far := by rw [hx2, hy2]; exact hab
      deg_a := by
        change (MoleProp.eraseBond M e).deg (C.a (i - 1)) = 4
        rw [(hdegN (i - 1) hk (by omega)).1]; exact E.deg_four _ (C.a_mem hk)
      deg_b := by
        change (MoleProp.eraseBond M e).deg (C.b (i - 1)) = 4
        rw [(hdegN (i - 1) hk (by omega)).2]; exact E.deg_four _ (C.b_mem hk) }
  set T := El.toTwoExit hcapN with hT
  have hTY : T.Y = (C.low (i - 1) hk).set := El.toTwoExit_Y hcapN
  have hcd : (T.c = C.a i ∧ T.d = C.b i) ∨ (T.c = C.b i ∧ T.d = C.a i) := by
    have := El.toTwoExit_cd hcapN
    change (T.c = (MoleProp.eraseBond M e).atom ((MoleProp.eraseBond M e).mate x) ∧
      T.d = (MoleProp.eraseBond M e).atom ((MoleProp.eraseBond M e).mate y)) ∨
      (T.c = (MoleProp.eraseBond M e).atom ((MoleProp.eraseBond M e).mate y) ∧
      T.d = (MoleProp.eraseBond M e).atom ((MoleProp.eraseBond M e).mate x)) at this
    rw [hx2, hy2] at this
    exact this
  have hdc : s(T.d, T.c) = s(C.a i, C.b i) := by
    rcases hcd with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact Sym2.eq_swap
    · rw [h1, h2]
  have hpostdeg : ∀ w, w ∉ (C.low (i - 1) hk).set → T.post.deg w = (MoleProp.eraseBond M e).deg w := fun w hw =>
    T.post_deg (by rw [hTY]; exact hw)
  -- the first statement on the lower chain
  have hgood : ∀ S ∈ MoleProp.ladderCells T.post, T.c ∈ S → GoodCell T.post S := by
    intro S _ hc
    refine Or.inr ⟨T.c, hc, ?_⟩
    rcases hcd with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1, hpostdeg _ hailo, hdeg3.1]
    · rw [h1, hpostdeg _ hbilo, hdeg3.2]
  have step1 := hY2 _ El hgood
  refine step1.trans (mul_le_mul' le_rfl (iSup₂_le fun P' hP' => ?_))
  -- the upper ladder on the post molecule
  have hU : ∀ j, i ≤ j → j ≤ C.n → C.a j ∉ (C.low (i - 1) hk).set ∧ C.b j ∉ (C.low (i - 1) hk).set :=
    fun j h1 h2 => ⟨C.a_notMem_low hk (by omega) h2, C.b_notMem_low hk (by omega) h2⟩
  have hupl : ∀ w ∈ C.upper i, w ∉ (C.low (i - 1) hk).set := by
    intro w hw
    obtain ⟨j, h1, h2, rfl | rfl⟩ := C.mem_upper.mp hw
    exacts [(hU j h1 h2).1, (hU j h1 h2).2]
  have hpostatoms : T.post.atoms = (MoleProp.eraseBond M e).atoms \ (C.low (i - 1) hk).set := by
    rw [T.post_atoms, hTY]
  have hmolPost : T.post.IsMolecule :=
    isMolecule_of_connected _ (T.post_caps hcapN) (T.post_connected hconnN)
      (by rw [hpostatoms]; exact mem_sdiff.mpr ⟨(C.mem i hi).1, hailo⟩)
      (by rw [hpostdeg _ hailo, hdeg3.1]; norm_num)
  have hbbpost : ∀ p q : V, p ∉ (C.low (i - 1) hk).set → q ∉ (C.low (i - 1) hk).set →
      T.post.bondsBetween p q =
        (MoleProp.eraseBond M e).bondsBetween p q + (if s(C.a i, C.b i) = s(p, q) then 1 else 0) := by
    intro p q hp hq
    unfold TwoExit.post
    rw [addBond_bondsBetween, hdc, Degen.bondsBetween_erase_eq _ _ (by rw [hTY]; exact hp) (by rw [hTY]; exact hq)]
  have hrung : T.post.bondsBetween (C.a i) (C.b i) = 2 := by
    have h1 := hbbpost _ _ hailo hbilo
    have h2 := bondsBetween_eraseBond_of_ends M e he (C.a i) (C.b i)
    rw [ite_of_pos rfl] at h1 h2
    rw [C.rung i hi0 hi] at h2
    omega
  have hbb : ∀ p q : V, p ∈ C.upper i → q ∈ C.upper i → s(p, q) ≠ s(C.a i, C.b i) →
      T.post.bondsBetween p q = M.bondsBetween p q := by
    intro p q hp hq hne
    have h1 := hbbpost _ _ (hupl p hp) (hupl q hq)
    have h2 := bondsBetween_eraseBond_of_ends M e he p q
    rw [ite_of_not (Ne.symm hne), add_zero] at h1 h2
    rw [h1, h2]
  have hdeg0 : T.post.deg (C.a i) = 3 ∧ T.post.deg (C.b i) = 3 := by
    rw [hpostdeg _ hailo, hpostdeg _ hbilo]; exact hdeg3
  have hdeg : ∀ j, i < j → j ≤ C.n → T.post.deg (C.a j) = M.deg (C.a j) ∧ T.post.deg (C.b j) = M.deg (C.b j) := by
    intro j h1 h2
    rw [hpostdeg _ (hU j h1.le h2).1, hpostdeg _ (hU j h1.le h2).2]
    exact hdegN j h2 (by omega)
  have hmem : ∀ j, i ≤ j → j ≤ C.n → C.a j ∈ T.post.atoms ∧ C.b j ∈ T.post.atoms := fun j h1 h2 => by
    rw [hpostatoms]
    exact ⟨mem_sdiff.mpr ⟨(C.mem j h2).1, (hU j h1 h2).1⟩, mem_sdiff.mpr ⟨(C.mem j h2).2, (hU j h1 h2).2⟩⟩
  have step2 := hpeel T.post hmolPost (E.ladderFrom T.post i hi hmem hrung hbb hdeg0 hdeg) P' hP'
  rw [E.ladderFrom_set] at step2
  have hcU : T.c ∈ C.upper i := by
    rcases hcd with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;>
      [exact C.mem_upper.mpr ⟨i, le_rfl, hi, Or.inl rfl⟩; exact C.mem_upper.mpr ⟨i, le_rfl, hi, Or.inr rfl⟩]
  have hdU : T.d ∈ C.upper i := by
    rcases hcd with ⟨_, h2⟩ | ⟨_, h2⟩ <;> rw [h2] <;>
      [exact C.mem_upper.mpr ⟨i, le_rfl, hi, Or.inr rfl⟩; exact C.mem_upper.mpr ⟨i, le_rfl, hi, Or.inl rfl⟩]
  have hunion : T.Y ∪ C.upper i = C.set := by
    rw [hTY]
    have := C.low_union_upper (k := i - 1) (by omega)
    rwa [hi1] at this
  have step3 := T.afree_post_erase_le (C.upper i) hcU hdU (d := d) L γ δ (η / 2) C1 P'
  rw [hunion] at step3
  have hYe : M.atom e ∈ C.set ∨ M.atom (M.mate e) ∈ C.set := by
    rcases hends _ (Or.inl rfl) with h | h
    · exact Or.inl (h ▸ C.a_mem hi)
    · exact Or.inl (h ▸ C.b_mem hi)
  have step4 := afree_eraseBond_erase_le M e C.set hYe (d := d) L γ δ (η / 2) C1 P'
  have hcells : ∀ S ∈ MoleProp.ladderCells (Degen.eraseAtoms M C.set), 0 ≤ P' S := by
    intro S hS
    rw [← ladderCells_eraseBond_erase M e C.set hYe, ← hunion, ← T.ladderCells_post_erase (C.upper i) hcU hdU]
      at hS
    exact nonneg_erase hP' _ S hS
  exact step2.trans (step3.trans (step4.trans (afree_le_afreeSup _ P' hcells)))

end Y2End
end WaveTurbulence.MoleProp4
