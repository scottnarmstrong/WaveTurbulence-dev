/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.C4Main
public import WaveTurbulence.Foundations.TVine.Defs
import Mathlib.Tactic

/-! # Bridge, part 1: a complete (Y2) sequence is a path of D11 `Y2Step`s (packet L6, `C4TBridge`)

`molGraph N`: the bond multigraph of a molecule (vertices the atoms, `mult s(p,q)` = the number of bonds between `p`
and `q`, i.e. `bondsBetween p q`). For a (Y) chain `C` of `N` with a (Y2) ending `E` (main's `YChain`, `Y2End`, DH23
L1929), the complete (Y2) sequence removes the `n + 1` pairs `(a i, b i)` and adds one bond between the far ends
(`TwoExit.post`). In D11's terms this is `n + 1` single (Y2) moves (`TVine.Y2Step`): after removing `(a i, b i)` the
added bond `a (i+1) – b (i+1)` makes the next rung a triple pair. `y2seq_reflTransGen` proves
`ReflTransGen Y2Step (molGraph N) (molGraph post)` from main's bond tables of a chain (`bb_ab`, `bb_aa`, `bb_bb`,
`bb_a_out`, `bb_b_out`, `TwoExit.post_bondsBetween`). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
namespace WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.FinalCountG8 WaveTurbulence.MoleProp4 WaveTurbulence.TVine

section graph
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The bond multigraph of a molecule. -/
def molGraph (N : Molecule V D) : UMultigraph V where
  verts := N.atoms
  mult e := (N.bonds.filter fun x => N.ends x = e).card
  supp e he x hx := by
    obtain ⟨y, hy⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero he)
    have hye := (mem_filter.mp hy).2
    rw [← hye] at hx
    rcases Sym2.mem_iff.mp hx with rfl | rfl <;> exact N.atom_mem _

theorem molGraph_mult (N : Molecule V D) (p q : V) : (molGraph N).mult s(p, q) = N.bondsBetween p q := rfl

theorem UMultigraph.ext' {G G' : UMultigraph V} (hv : G.verts = G'.verts) (hm : ∀ e, G.mult e = G'.mult e) :
    G = G' := by
  cases G; cases G'
  simp only at hv
  subst hv
  congr
  funext e
  exact hm e

end graph

section chain
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
variable {N : Molecule V D} (C : YChain N) (E : Y2End C)

/-- The atoms removed by the first `i` pairs of the chain. -/
def remY (i : ℕ) : Finset V := (range i).image C.a ∪ (range i).image C.b

theorem remY_zero : remY C 0 = ∅ := by simp [remY]

theorem remY_succ (i : ℕ) : remY C (i + 1) = insert (C.a i) (insert (C.b i) (remY C i)) := by
  ext x
  simp only [remY, range_add_one, image_insert, mem_union, mem_insert]
  tauto

theorem remY_set : remY C (C.n + 1) = C.set := rfl

theorem mem_remY {i : ℕ} {x : V} : x ∈ remY C i ↔ ∃ k < i, x = C.a k ∨ x = C.b k := by
  simp only [remY, mem_union, mem_image, mem_range]
  constructor
  · rintro (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
    · exact ⟨k, hk, Or.inl rfl⟩
    · exact ⟨k, hk, Or.inr rfl⟩
  · rintro ⟨k, hk, rfl | rfl⟩
    · exact Or.inl ⟨k, hk, rfl⟩
    · exact Or.inr ⟨k, hk, rfl⟩

theorem a_notMem_remY {i j : ℕ} (hij : i ≤ j) (hj : j ≤ C.n) : C.a j ∉ remY C i := by
  intro h
  obtain ⟨k, hk, h | h⟩ := (mem_remY C).mp h
  · have := C.inj_a j hj k (by omega) h; omega
  · exact C.ne_ab j hj k (by omega) h

theorem b_notMem_remY {i j : ℕ} (hij : i ≤ j) (hj : j ≤ C.n) : C.b j ∉ remY C i := by
  intro h
  obtain ⟨k, hk, h | h⟩ := (mem_remY C).mp h
  · exact C.ne_ab k (by omega) j hj h.symm
  · have := C.inj_b j hj k (by omega) h; omega

theorem remY_sub {i : ℕ} (hi : i ≤ C.n + 1) : remY C i ⊆ C.set := by
  intro x hx
  obtain ⟨k, hk, h | h⟩ := (mem_remY C).mp hx
  · exact h ▸ C.a_mem (by omega)
  · exact h ▸ C.b_mem (by omega)

/-- A chain atom outside `remY i` is `a j` or `b j` with `i ≤ j`. -/
theorem mem_set_of_notMem_remY {i : ℕ} {x : V} (hx : x ∈ C.set) (hxi : x ∉ remY C i) :
    ∃ j, i ≤ j ∧ j ≤ C.n ∧ (x = C.a j ∨ x = C.b j) := by
  obtain ⟨j, hj, h⟩ := C.mem_set.mp hx
  refine ⟨j, ?_, hj, h⟩
  by_contra hlt
  exact hxi ((mem_remY C).mpr ⟨j, by omega, h⟩)

/-- The far end of the outgoing chain exit at `a n` and of the exit at `b n`. -/
abbrev cx : V := N.atom (N.mate E.x)
abbrev cy : V := N.atom (N.mate E.y)

/-- The bond added at stage `i`: the next rung (`1 ≤ i ≤ n`) or the closing bond (`i = n + 1`). -/
def extraY (i : ℕ) (e : Sym2 V) : ℕ :=
  (if 1 ≤ i ∧ i ≤ C.n ∧ e = s(C.a i, C.b i) then 1 else 0) + (if i = C.n + 1 ∧ e = s(cx C E, cy C E) then 1 else 0)

open Classical in
/-- The multigraph after removing the first `i` pairs of the chain (D11 moves). -/
noncomputable def stageY (i : ℕ) : UMultigraph V where
  verts := N.atoms \ remY C i
  mult e := if ∃ v ∈ e, v ∈ remY C i then 0 else (molGraph N).mult e + extraY C E i e
  supp e he x hx := by
    split_ifs at he with h
    · exact absurd rfl he
    push Not at h
    refine mem_sdiff.mpr ⟨?_, h x hx⟩
    by_cases h0 : (molGraph N).mult e = 0
    · rw [h0, zero_add] at he
      unfold extraY at he
      split_ifs at he with h1 h2 h2
      · rw [h1.2.2] at hx
        rcases Sym2.mem_iff.mp hx with rfl | rfl
        exacts [(C.mem i h1.2.1).1, (C.mem i h1.2.1).2]
      · rw [h1.2.2] at hx
        rcases Sym2.mem_iff.mp hx with rfl | rfl
        exacts [(C.mem i h1.2.1).1, (C.mem i h1.2.1).2]
      · rw [h2.2] at hx
        rcases Sym2.mem_iff.mp hx with rfl | rfl <;> exact N.atom_mem _
      · exact absurd rfl he
    · exact (molGraph N).supp e h0 x hx

theorem stageY_zero : stageY C E 0 = molGraph N := by
  refine UMultigraph.ext' (by simp [stageY, remY_zero, molGraph]) fun e => ?_
  simp only [stageY, remY_zero, Finset.notMem_empty, and_false, exists_false, if_false, extraY]
  simp

theorem stageY_mult (i : ℕ) (p q : V) : (stageY C E i).mult s(p, q) =
    if p ∈ remY C i ∨ q ∈ remY C i then 0 else N.bondsBetween p q + extraY C E i s(p, q) := by
  classical
  simp only [stageY, Sym2.mem_iff, exists_eq_or_imp, exists_eq_left]
  rfl

/-- The next triple pair's partners: `(a (i+1), b (i+1))`, or the far ends `(cx, cy)` at the last pair. -/
def ccY (i : ℕ) : V := if i < C.n then C.a (i + 1) else cx C E
def ddY (i : ℕ) : V := if i < C.n then C.b (i + 1) else cy C E

theorem cx_notMem : cx C E ∉ C.set := E.hxo
theorem cy_notMem : cy C E ∉ C.set := E.hyo

theorem ccY_notMem {i : ℕ} (hi : i ≤ C.n) : ccY C E i ∉ remY C i := by
  unfold ccY; split_ifs with h
  · exact a_notMem_remY C (by omega) (by omega)
  · exact fun h' => cx_notMem C E (remY_sub C (by omega) h')

theorem ddY_notMem {i : ℕ} (hi : i ≤ C.n) : ddY C E i ∉ remY C i := by
  unfold ddY; split_ifs with h
  · exact b_notMem_remY C (by omega) (by omega)
  · exact fun h' => cy_notMem C E (remY_sub C (by omega) h')

theorem extraY_eq_zero {i : ℕ} (hi : i ≤ C.n) {e : Sym2 V} (he : C.a i ∉ e) : extraY C E i e = 0 := by
  unfold extraY
  rw [if_neg (by rintro ⟨-, -, rfl⟩; exact he (Sym2.mem_mk_left _ _)), if_neg (by omega)]

theorem extraY_succ {i : ℕ} (hi : i ≤ C.n) (e : Sym2 V) :
    extraY C E (i + 1) e = if e = s(ccY C E i, ddY C E i) then 1 else 0 := by
  unfold extraY ccY ddY
  by_cases h : i < C.n
  · simp only [if_pos h, show i + 1 ≠ C.n + 1 by omega, false_and, if_false, add_zero]
    by_cases he : e = s(C.a (i + 1), C.b (i + 1))
    · rw [if_pos ⟨by omega, by omega, he⟩, if_pos he]
    · rw [if_neg (fun h' => he h'.2.2), if_neg he]
  · obtain rfl : i = C.n := by omega
    rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _),
      if_neg (show ¬ (1 ≤ C.n + 1 ∧ C.n + 1 ≤ C.n ∧ e = s(C.a (C.n + 1), C.b (C.n + 1))) by omega), zero_add]
    simp only [true_and]

section hloop
variable (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z))
include hloop

theorem stageY_mult_ab {i : ℕ} (hi : i ≤ C.n) : (stageY C E i).mult s(C.a i, C.b i) = 3 := by
  rw [stageY_mult, if_neg (by
    rintro (h | h)
    exacts [a_notMem_remY C le_rfl hi h, b_notMem_remY C le_rfl hi h]), bb_ab E hi hi, if_pos rfl]
  unfold extraY
  rw [if_neg (show ¬ (i = C.n + 1 ∧ _) by omega)]
  by_cases h0 : i = 0
  · subst h0; simp
  · rw [if_neg h0, if_pos ⟨by omega, hi, rfl⟩]

theorem stageY_mult_ac {i : ℕ} (hi : i ≤ C.n) : (stageY C E i).mult s(C.a i, ccY C E i) = 1 := by
  rw [stageY_mult, if_neg (by
    rintro (h | h)
    exacts [a_notMem_remY C le_rfl hi h, ccY_notMem C E hi h])]
  have hab : C.a i ≠ C.b i := C.ne_ab i hi i hi
  have hx : extraY C E i s(C.a i, ccY C E i) = 0 := by
    unfold extraY
    rw [if_neg (show ¬ (i = C.n + 1 ∧ _) by omega), add_zero]
    refine if_neg ?_
    rintro ⟨-, -, h⟩
    rcases Sym2.eq_iff.mp h with ⟨-, h⟩ | ⟨h, -⟩
    · unfold ccY at h; split_ifs at h with hlt
      · exact C.ne_ab (i + 1) (by omega) i hi h
      · exact cx_notMem C E (h ▸ C.b_mem hi)
    · exact hab h
  rw [hx, add_zero]
  unfold ccY; split_ifs with hlt
  · rw [bb_aa E hloop hi (by omega), if_pos (Or.inl rfl)]
  · rw [bb_a_out E hloop hi (cx_notMem C E), if_pos ⟨by omega, rfl⟩]

theorem stageY_mult_bd {i : ℕ} (hi : i ≤ C.n) : (stageY C E i).mult s(C.b i, ddY C E i) = 1 := by
  rw [stageY_mult, if_neg (by
    rintro (h | h)
    exacts [b_notMem_remY C le_rfl hi h, ddY_notMem C E hi h])]
  have hab : C.a i ≠ C.b i := C.ne_ab i hi i hi
  have hx : extraY C E i s(C.b i, ddY C E i) = 0 := by
    unfold extraY
    rw [if_neg (show ¬ (i = C.n + 1 ∧ _) by omega), add_zero]
    refine if_neg ?_
    rintro ⟨-, -, h⟩
    rcases Sym2.eq_iff.mp h with ⟨h, -⟩ | ⟨-, h⟩
    · exact hab h.symm
    · unfold ddY at h; split_ifs at h with hlt
      · exact C.ne_ab i hi (i + 1) (by omega) h.symm
      · exact cy_notMem C E (h ▸ C.a_mem hi)
  rw [hx, add_zero]
  unfold ddY; split_ifs with hlt
  · rw [bb_bb E hloop hi (by omega), if_pos (Or.inl rfl)]
  · rw [bb_b_out E hloop hi (cy_notMem C E), if_pos ⟨by omega, rfl⟩]

theorem stageY_mult_a_other {i : ℕ} (hi : i ≤ C.n) (x : V) (hxb : x ≠ C.b i) (hxc : x ≠ ccY C E i) :
    (stageY C E i).mult s(C.a i, x) = 0 := by
  rw [stageY_mult]
  split_ifs with hR
  · rfl
  push Not at hR
  have hab : C.a i ≠ C.b i := C.ne_ab i hi i hi
  have hx : extraY C E i s(C.a i, x) = 0 := by
    unfold extraY
    rw [if_neg (show ¬ (i = C.n + 1 ∧ _) by omega), add_zero]
    refine if_neg ?_
    rintro ⟨-, -, h⟩
    rcases Sym2.eq_iff.mp h with ⟨-, h⟩ | ⟨h, -⟩
    · exact hxb h
    · exact hab h
  rw [hx, add_zero]
  by_cases hxS : x ∈ C.set
  · obtain ⟨j, hij, hj, rfl | rfl⟩ := mem_set_of_notMem_remY C hxS hR.2
    · rw [bb_aa E hloop hi hj, if_neg]
      rintro (h | h)
      · apply hxc; unfold ccY; rw [if_pos (by omega)]; rw [← h]
      · omega
    · rw [bb_ab E hi hj, if_neg]
      rintro rfl; exact hxb rfl
  · rw [bb_a_out E hloop hi hxS, if_neg]
    rintro ⟨rfl, rfl⟩
    apply hxc; unfold ccY; rw [if_neg (by omega)]

theorem stageY_mult_b_other {i : ℕ} (hi : i ≤ C.n) (x : V) (hxa : x ≠ C.a i) (hxd : x ≠ ddY C E i) :
    (stageY C E i).mult s(C.b i, x) = 0 := by
  rw [stageY_mult]
  split_ifs with hR
  · rfl
  push Not at hR
  have hab : C.a i ≠ C.b i := C.ne_ab i hi i hi
  have hx : extraY C E i s(C.b i, x) = 0 := by
    unfold extraY
    rw [if_neg (show ¬ (i = C.n + 1 ∧ _) by omega), add_zero]
    refine if_neg ?_
    rintro ⟨-, -, h⟩
    rcases Sym2.eq_iff.mp h with ⟨h, -⟩ | ⟨-, h⟩
    · exact hab h.symm
    · exact hxa h
  rw [hx, add_zero]
  by_cases hxS : x ∈ C.set
  · obtain ⟨j, hij, hj, rfl | rfl⟩ := mem_set_of_notMem_remY C hxS hR.2
    · rw [Degen.bondsBetween_comm, bb_ab E hj hi, if_neg]
      rintro rfl; exact hxa rfl
    · rw [bb_bb E hloop hi hj, if_neg]
      rintro (h | h)
      · apply hxd; unfold ddY; rw [if_pos (by omega)]; rw [← h]
      · omega
  · rw [bb_b_out E hloop hi hxS, if_neg]
    rintro ⟨rfl, rfl⟩
    apply hxd; unfold ddY; rw [if_neg (by omega)]

end hloop

theorem stageY_verts_succ (i : ℕ) :
    (stageY C E (i + 1)).verts = (((stageY C E i).verts.erase (C.a i)).erase (C.b i)) := by
  ext x
  simp only [stageY, remY_succ, mem_sdiff, mem_insert, mem_erase]
  tauto

theorem stageY_mult_succ {i : ℕ} (hi : i ≤ C.n) (e : Sym2 V) :
    (stageY C E (i + 1)).mult e = if C.a i ∈ e ∨ C.b i ∈ e then 0 else
      (stageY C E i).mult e + (if e = s(ccY C E i, ddY C E i) then 1 else 0) := by
  induction e using Sym2.ind with
  | _ p q =>
  rw [stageY_mult, stageY_mult, extraY_succ C E hi]
  simp only [remY_succ, mem_insert, Sym2.mem_iff]
  by_cases hA : (C.a i = p ∨ C.a i = q) ∨ (C.b i = p ∨ C.b i = q)
  · rw [if_pos hA, if_pos (by rcases hA with (h | h) | (h | h) <;> simp [h])]
  rw [if_neg hA]
  push Not at hA
  obtain ⟨⟨hap, haq⟩, hbp, hbq⟩ := hA
  have hp : (p = C.a i ∨ p = C.b i ∨ p ∈ remY C i) ↔ p ∈ remY C i := by
    constructor
    · rintro (h | h | h)
      exacts [absurd h.symm hap, absurd h.symm hbp, h]
    · exact fun h => Or.inr (Or.inr h)
  have hq : (q = C.a i ∨ q = C.b i ∨ q ∈ remY C i) ↔ q ∈ remY C i := by
    constructor
    · rintro (h | h | h)
      exacts [absurd h.symm haq, absurd h.symm hbq, h]
    · exact fun h => Or.inr (Or.inr h)
  simp only [hp, hq]
  split_ifs with hR hcd hcd
  · exfalso
    rcases Sym2.eq_iff.mp hcd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hR with h | h
      exacts [ccY_notMem C E hi h, ddY_notMem C E hi h]
    · rcases hR with h | h
      exacts [ddY_notMem C E hi h, ccY_notMem C E hi h]
  · rfl
  · rw [extraY_eq_zero C E hi (by simp only [Sym2.mem_iff]; push Not; exact ⟨hap, haq⟩)]
  · rw [extraY_eq_zero C E hi (by simp only [Sym2.mem_iff]; push Not; exact ⟨hap, haq⟩)]

/-- **One D11 (Y2) move per pair of the chain.** -/
theorem stageY_step (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z)) {i : ℕ} (hi : i ≤ C.n) :
    Y2Step (stageY C E i) (stageY C E (i + 1)) := by
  have hab : C.a i ≠ C.b i := C.ne_ab i hi i hi
  have hcd : ccY C E i ≠ ddY C E i := by
    unfold ccY ddY; split_ifs with h
    · exact C.ne_ab (i + 1) (by omega) (i + 1) (by omega)
    · exact E.far
  have hca : ccY C E i ≠ C.a i := by
    unfold ccY; split_ifs with h
    · intro h'; have := C.inj_a (i + 1) (by omega) i hi h'; omega
    · exact fun h' => cx_notMem C E (h' ▸ C.a_mem hi)
  have hcb : ccY C E i ≠ C.b i := by
    unfold ccY; split_ifs with h
    · exact C.ne_ab (i + 1) (by omega) i hi
    · exact fun h' => cx_notMem C E (h' ▸ C.b_mem hi)
  have hda : ddY C E i ≠ C.a i := by
    unfold ddY; split_ifs with h
    · exact fun h' => C.ne_ab i hi (i + 1) (by omega) h'.symm
    · exact fun h' => cy_notMem C E (h' ▸ C.a_mem hi)
  have hdb : ddY C E i ≠ C.b i := by
    unfold ddY; split_ifs with h
    · intro h'; have := C.inj_b (i + 1) (by omega) i hi h'; omega
    · exact fun h' => cy_notMem C E (h' ▸ C.b_mem hi)
  exact ⟨C.a i, C.b i, ccY C E i, ddY C E i, hab, hcd, hca, hcb, hda, hdb,
    stageY_mult_ab C E hloop hi, stageY_mult_ac C E hloop hi, stageY_mult_bd C E hloop hi,
    stageY_mult_a_other C E hloop hi, stageY_mult_b_other C E hloop hi, stageY_verts_succ C E i,
    stageY_mult_succ C E hi⟩

theorem stageY_path (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z)) :
    ∀ i ≤ C.n + 1, Relation.ReflTransGen Y2Step (stageY C E 0) (stageY C E i) := by
  intro i
  induction i with
  | zero => exact fun _ => Relation.ReflTransGen.refl
  | succ k ih =>
    intro hk
    exact (ih (by omega)).tail (stageY_step C E hloop (by omega))

/-- The last stage is the bond multigraph of main's post molecule. -/
theorem stageY_last (hcap : ∀ v ∈ N.atoms, N.outdeg v ≤ 2 ∧ N.indeg v ≤ 2) :
    stageY C E (C.n + 1) = molGraph (E.toTwoExit hcap).post := by
  set T := E.toTwoExit hcap with hT
  have hY : T.Y = C.set := E.toTwoExit_Y hcap
  have hcd : s(T.d, T.c) = s(cx C E, cy C E) := by
    rw [hT]; unfold Y2End.toTwoExit TwoExit.c TwoExit.d
    split_ifs with h
    · exact Sym2.eq_swap
    · rfl
  refine UMultigraph.ext' ?_ fun e => ?_
  · show N.atoms \ remY C (C.n + 1) = T.post.atoms
    rw [TwoExit.post_atoms, hY, remY_set]
  · induction e using Sym2.ind with
    | _ p q =>
    rw [stageY_mult, molGraph_mult, TwoExit.post_bondsBetween, hY, remY_set, hcd]
    unfold extraY
    rw [if_neg (show ¬ (1 ≤ C.n + 1 ∧ C.n + 1 ≤ C.n ∧ _) by omega), zero_add]
    by_cases h1 : p ∈ C.set ∨ q ∈ C.set
    · rw [if_pos h1, if_pos h1, zero_add, if_neg]
      intro h
      rcases Sym2.eq_iff.mp h with ⟨h, h'⟩ | ⟨h, h'⟩ <;> rcases h1 with h1 | h1
      · exact cx_notMem C E (h ▸ h1)
      · exact cy_notMem C E (h' ▸ h1)
      · exact cy_notMem C E (h' ▸ h1)
      · exact cx_notMem C E (h ▸ h1)
    · rw [if_neg h1, if_neg h1]
      by_cases h : s(p, q) = s(cx C E, cy C E)
      · rw [if_pos ⟨rfl, h⟩, if_pos h.symm]
      · rw [if_neg (fun h' => h h'.2), if_neg (fun h' => h h'.symm)]

/-- **A complete (Y2) sequence is a path of D11 (Y2) moves** between the bond multigraphs. -/
theorem y2seq_reflTransGen (hcap : ∀ v ∈ N.atoms, N.outdeg v ≤ 2 ∧ N.indeg v ≤ 2)
    (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z)) :
    Relation.ReflTransGen Y2Step (molGraph N) (molGraph (E.toTwoExit hcap).post) := by
  rw [← stageY_zero C E, ← stageY_last C E hcap]
  exact stageY_path C E hloop _ le_rfl

end chain

end WaveTurbulence.GammaLow.FinalCount
