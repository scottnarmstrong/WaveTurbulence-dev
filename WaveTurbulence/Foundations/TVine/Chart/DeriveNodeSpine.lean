/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.DeriveBudget
public import WaveTurbulence.Foundations.TVine.Chart.DeriveJunction
public import WaveTurbulence.Foundations.TVine.Chart.DeriveCores

/-!
# Derivation of the cell decomposition, XVII: the spine cells

The spine piece `Z (i+1)` (`i < r`) is placed with input region `reg i (he i)` and exit region `reg (i+1) (hx (i+1))`:
* a rung (`bondsBetween = 2`) by `rungTable` (`pc_spineRung`);
* the junction of a (P-a) attachment by `junctionTable`, with its pendant region `S ∖ H 0` (`pc_spineJunction`);
* the (B)/(C) core when there is no pendant (`pc_spineCore`); its orientation (which atoms carry the port bonds) is
  forced by the budget at each atom.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Chart

open Finset VineParamContract Struct

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {S : Finset V} {a b : V}

theorem deg4 (hB : M.IsBlock S a b) {v : V} (hv : v ∈ S) (hva : v ≠ a) (hvb : v ≠ b) : M.degIn S v = 4 :=
  hB.2.2.2.2.2.2.2.2.1 v hv hva hvb

theorem deg_a (hB : M.IsBlock S a b) : M.degIn S a = 2 := by
  rw [degIn_eq, hB.2.2.2.2.1, hB.2.2.2.2.2.1]

theorem deg_b (hB : M.IsBlock S a b) : M.degIn S b = 2 := by
  rw [degIn_eq, hB.2.2.2.2.2.2.1, hB.2.2.2.2.2.2.2.1]

theorem Att.flag_eq {att : Att} {i : ℕ} (h : att ≠ .pb i) : att.hx i = att.he i := by
  cases att with
  | none => rfl
  | pa j => rfl
  | pb j =>
    have : j ≠ i := fun h' => h (h' ▸ rfl)
    simp only [Att.hx, Att.he, decide_eq_decide]
    omega

theorem Att.flag_mono {att : Att} {i : ℕ} (h : att.he i = true) : att.hx (i + 1) = true := by
  cases att with
  | none => exact h
  | pa j => simp only [Att.he, Att.hx, decide_eq_true_eq] at h ⊢; omega
  | pb j => simp only [Att.he, Att.hx, decide_eq_true_eq] at h ⊢; omega

theorem Att.flag_back {att : Att} {i : ℕ} (hpa : att ≠ .pa (i + 1)) (h : att.hx (i + 1) = true) :
    att.he i = true := by
  cases att with
  | none => exact h
  | pa j =>
    have : j ≠ i + 1 := fun h' => hpa (h' ▸ rfl)
    simp only [Att.he, Att.hx, decide_eq_true_eq] at h ⊢; omega
  | pb j => simp only [Att.he, Att.hx, decide_eq_true_eq] at h ⊢; omega

theorem atoms_two {u w : V} {f : Fin 2 → V} (hf : f = ![u, w]) :
    ∀ v, v ∈ ({u, w} : Finset V) ↔ ∃ i, f i = v := by
  subst hf; intro v; simp only [mem_insert, mem_singleton]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · rintro ⟨i, rfl⟩; fin_cases i <;> simp

theorem atoms_three {x y z : V} {f : Fin 3 → V} (hf : f = ![x, y, z]) :
    ∀ v, v ∈ ({x, y, z} : Finset V) ↔ ∃ i, f i = v := by
  subst hf; intro v; simp only [mem_insert, mem_singleton]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · rintro ⟨i, rfl⟩; fin_cases i <;> simp

/-! ## Orientation logic -/

theorem logic_B {x y z P1 P2 Q1 Q2 : V} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hP1 : P1 = x ∨ P1 = y ∨ P1 = z) (hP2 : P2 = x ∨ P2 = y ∨ P2 = z)
    (hQ1 : Q1 = x ∨ Q1 = y ∨ Q1 = z) (hQ2 : Q2 = x ∨ Q2 = y ∨ Q2 = z)
    (hP : P1 ≠ P2) (hQ : Q1 ≠ Q2) (hIz : P1 = z ∨ P2 = z) (hOz : Q1 = z ∨ Q2 = z)
    (hx : ¬ ((P1 = x ∨ P2 = x) ∧ (Q1 = x ∨ Q2 = x))) (hy : ¬ ((P1 = y ∨ P2 = y) ∧ (Q1 = y ∨ Q2 = y))) :
    ((P1 = z ∨ P1 = x) ∧ (P2 = z ∨ P2 = x) ∧ (Q1 = z ∨ Q1 = y) ∧ (Q2 = z ∨ Q2 = y)) ∨
    ((P1 = z ∨ P1 = y) ∧ (P2 = z ∨ P2 = y) ∧ (Q1 = z ∨ Q1 = x) ∧ (Q2 = z ∨ Q2 = x)) := by
  have hyx := hxy.symm; have hzy := hyz.symm; have hzx := hxz.symm
  rcases hP1 with h1 | h1 | h1 <;> rcases hP2 with h2 | h2 | h2 <;>
    rcases hQ1 with h3 | h3 | h3 <;> rcases hQ2 with h4 | h4 | h4 <;> subst P1 P2 Q1 Q2 <;> simp_all

theorem logic_two {x y z P1 P2 : V} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hP1 : P1 = x ∨ P1 = y ∨ P1 = z) (hP2 : P2 = x ∨ P2 = y ∨ P2 = z) (hP : P1 ≠ P2)
    (hy : ¬ (P1 = y ∨ P2 = y)) : (P1 = x ∨ P1 = z) ∧ (P2 = x ∨ P2 = z) := by
  have hyx := hxy.symm; have hzy := hyz.symm; have hzx := hxz.symm
  rcases hP1 with h1 | h1 | h1 <;> rcases hP2 with h2 | h2 | h2 <;> subst P1 P2 <;> simp_all

theorem logic_C {x y z P1 P2 : V} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hP1 : P1 = x ∨ P1 = y ∨ P1 = z) (hP2 : P2 = x ∨ P2 = y ∨ P2 = z) (hP : P1 ≠ P2)
    (hIx : P1 = x ∨ P2 = x) (hIz : P1 = z ∨ P2 = z) : (P1 = x ∨ P1 = z) ∧ (P2 = x ∨ P2 = z) := by
  have hyx := hxy.symm; have hzy := hyz.symm; have hzx := hxz.symm
  rcases hP1 with h1 | h1 | h1 <;> rcases hP2 with h2 | h2 | h2 <;> subst P1 P2 <;> simp_all

/-! ## The budget at the atoms of a sandwiched piece -/

theorem both_of_budget {C Xi Xo : Finset V} (pti : Port2 M S Xi a b) (pto : Port2 M S Xo a b) {v : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hvXi : v ∉ Xi) (hvXo : v ∈ Xo)
    (hsum : (innerAt (M := M) (S := S) C v).card + (portAt (M := M) (S := S) Xi v).card +
      (portAt (M := M) (S := S) Xo v).card = 4) (hin : (innerAt (M := M) (S := S) C v).card ≤ 2) :
    (hd pti.out = v ∨ tl pti.inn = v) ∧ (tl pto.out = v ∨ hd pto.inn = v) := by
  have h1 := portAt_le_one pti hva hvb
  have h2 := portAt_le_one pto hva hvb
  exact ⟨inEnd_of_pos pti hvXi (by omega), outEnd_of_pos pto hvXo (by omega)⟩

theorem not_both_of_budget {C Xi Xo : Finset V} (pti : Port2 M S Xi a b) (pto : Port2 M S Xo a b) {v : V}
    (hsum : (innerAt (M := M) (S := S) C v).card + (portAt (M := M) (S := S) Xi v).card +
      (portAt (M := M) (S := S) Xo v).card = 4) (hin : 3 ≤ (innerAt (M := M) (S := S) C v).card) :
    ¬ ((hd pti.out = v ∨ tl pti.inn = v) ∧ (tl pto.out = v ∨ hd pto.inn = v)) := by
  rintro ⟨h1, h2⟩
  have p1 : 0 < (portAt (M := M) (S := S) Xi v).card := by
    rcases h1 with h | h
    · exact portAt_pos_out pti (Or.inr h)
    · exact portAt_pos_inn pti (Or.inl h)
  have p2 : 0 < (portAt (M := M) (S := S) Xo v).card := by
    rcases h2 with h | h
    · exact portAt_pos_out pto (Or.inl h)
    · exact portAt_pos_inn pto (Or.inr h)
  omega

theorem not_in_of_budget {C Xi Xo : Finset V} (pti : Port2 M S Xi a b) {v : V}
    (hsum : (innerAt (M := M) (S := S) C v).card + (portAt (M := M) (S := S) Xi v).card +
      (portAt (M := M) (S := S) Xo v).card = 4) (hin : 4 ≤ (innerAt (M := M) (S := S) C v).card) :
    ¬ (hd pti.out = v ∨ tl pti.inn = v) := by
  intro h1
  have p1 : 0 < (portAt (M := M) (S := S) Xi v).card := by
    rcases h1 with h | h
    · exact portAt_pos_out pti (Or.inr h)
    · exact portAt_pos_inn pti (Or.inl h)
  omega

theorem perm_xyz (x y z : V) : ({x, y, z} : Finset V) = {y, x, z} := by
  ext v; simp only [mem_insert, mem_singleton]; tauto

theorem perm_zxy (x y z : V) : ({x, y, z} : Finset V) = {z, x, y} := by
  ext v; simp only [mem_insert, mem_singleton]; tauto

theorem perm_yxz' (x y z : V) : ({x, y, z} : Finset V) = {y, z, x} := by
  ext v; simp only [mem_insert, mem_singleton]; tauto

namespace Lay

variable (L : Lay M S a b)

theorem reg_mono {i i' : ℕ} (hii : i ≤ i') {h h' : Bool} (hh : h = true → h' = true) :
    L.reg i h ⊆ L.reg i' h' := by
  intro v hv
  rcases L.mem_reg.mp hv with ⟨j, hj, hvj⟩ | ⟨h1, h2⟩
  · exact L.mem_reg.mpr (Or.inl ⟨j, by omega, hvj⟩)
  · exact L.mem_reg.mpr (Or.inr ⟨hh h1, h2⟩)

variable (hB : M.IsBlock S a b)
include hB

theorem Z_not_reg {i : ℕ} (hi : i < L.r + 1) {v : V} (hv : v ∈ L.Z (i + 1)) (h : Bool) : v ∉ L.reg i h := by
  intro h'; have := (L.mem_reg_Z hB (by omega) (by omega) hv).mp h'; omega

theorem Z_in_reg {i : ℕ} (hi : i < L.r + 1) {v : V} (hv : v ∈ L.Z (i + 1)) (h : Bool) : v ∈ L.reg (i + 1) h :=
  (L.mem_reg_Z hB (by omega) (by omega) hv).mpr le_rfl

theorem reg_sub_compl {i : ℕ} (hi : i ≤ L.r + 1) : L.reg i false ⊆ S \ L.H 0 := by
  intro v hv
  rcases L.mem_reg.mp hv with ⟨j, hj, hvj⟩ | ⟨h, -⟩
  · exact mem_sdiff.mpr ⟨L.Z_sub hB (by omega) hvj, L.not_mem_H_of_Z hB (by omega) hvj⟩
  · exact absurd h (by simp)

theorem pend_in_ends {k : ℕ} (hk : k < L.s) (π : Port2 M S (S \ L.H k) a b) :
    hd π.out ∈ L.Y k ∧ tl π.inn ∈ L.Y k := by
  have hnot : ∀ v, v ∈ S \ L.H k → v ∉ L.Y k := fun v hv h => (mem_sdiff.mp hv).2 (L.Y_sub_H hk h)
  constructor
  · rcases L.pend_inner hB hk π.out (out_mem π) with ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h (hnot _ π.out_tl)
    · exact h
  · rcases L.pend_inner hB hk π.inn (inn_mem π) with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h (hnot _ π.inn_hd)

theorem pend_out_ends {k : ℕ} (hk : k + 1 < L.s) (π : Port2 M S (S \ L.H (k + 1)) a b) :
    tl π.out ∈ L.Y k ∧ hd π.inn ∈ L.Y k := by
  constructor
  · rcases L.pend_outer hB hk π.out (out_mem π) with ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · exact absurd h (mem_sdiff.mp π.out_tl).2
  · rcases L.pend_outer hB hk π.inn (inn_mem π) with ⟨-, h⟩ | ⟨h, -⟩
    · exact absurd h (mem_sdiff.mp π.inn_hd).2
    · exact h

variable {att : Att} (A : L.AttData att)
include A

theorem entry_ends {i : ℕ} (hi : i ≤ L.r) (π : Port2 M S (L.reg i (att.he i)) a b) :
    hd π.out ∈ L.Z (i + 1) ∧ tl π.inn ∈ L.Z (i + 1) := by
  constructor
  · rcases L.entry_outer hB A hi π.out (out_mem π) with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h π.out_hd
  · rcases L.entry_outer hB A hi π.inn (inn_mem π) with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h π.inn_tl
    · exact h

theorem exit_ends {i : ℕ} (hi : i ≤ L.r) (π : Port2 M S (L.reg i (att.hx i)) a b) :
    tl π.out ∈ L.Z i ∧ hd π.inn ∈ L.Z i := by
  constructor
  · rcases L.exit_inner hB A hi π.out (out_mem π) with ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · exact absurd π.out_tl h
  · rcases L.exit_inner hB A hi π.inn (inn_mem π) with ⟨-, h⟩ | ⟨h, -⟩
    · exact absurd π.inn_hd h
    · exact h

theorem pend_spine_ends (hs : 1 ≤ L.s) (π : Port2 M S (S \ L.H 0) a b) :
    (tl π.out = A.x ∨ tl π.out = A.x') ∧ (hd π.inn = A.x ∨ hd π.inn = A.x') := by
  obtain ⟨-, hset, -, -, hy, hy', hα, hα'⟩ := A.pend hs
  have hmem : ∀ e, e ∈ portSet (M := M) (S := S) (S \ L.H 0) → e = A.α ∨ e = A.α' := by
    intro e he
    rw [portSet_compl, portSet_eq_cross, hset, mem_insert, mem_singleton] at he
    exact he
  have hyH : A.y ∈ L.H 0 := L.Y_sub_H (by omega) hy
  have hy'H : A.y' ∈ L.H 0 := L.Y_sub_H (by omega) hy'
  have hnotH : ∀ v, v ∈ S \ L.H 0 → v ∉ L.H 0 := fun v hv => (mem_sdiff.mp hv).2
  constructor
  · have hout := π.out_tl
    rcases hmem π.out (out_mem π) with h | h <;> rw [h] at hout ⊢
    · rcases hα with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inl h1
      · exact absurd (show tl A.α ∈ L.H 0 by rw [h1]; exact hyH) (hnotH _ hout)
    · rcases hα' with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inr h1
      · exact absurd (show tl A.α' ∈ L.H 0 by rw [h1]; exact hy'H) (hnotH _ hout)
  · have hinn := π.inn_hd
    rcases hmem π.inn (inn_mem π) with h | h <;> rw [h] at hinn ⊢
    · rcases hα with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact absurd (show hd A.α ∈ L.H 0 by rw [h2]; exact hyH) (hnotH _ hinn)
      · exact Or.inl h2
    · rcases hα' with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact absurd (show hd A.α' ∈ L.H 0 by rw [h2]; exact hy'H) (hnotH _ hinn)
      · exact Or.inr h2

theorem spine_sandwich {i : ℕ} (hi : i < L.r) (hpa : att ≠ .pa (i + 1)) :
    L.reg i (att.he i) ⊆ L.reg (i + 1) (att.hx (i + 1)) ∧
    (∀ v ∈ L.Z (i + 1), v ∉ L.reg i (att.he i)) ∧ L.Z (i + 1) ⊆ L.reg (i + 1) (att.hx (i + 1)) ∧
    (∀ v ∈ S, v ∈ L.reg (i + 1) (att.hx (i + 1)) → v ∉ L.reg i (att.he i) → v ∈ L.Z (i + 1)) := by
  refine ⟨L.reg_mono (by omega) Att.flag_mono, fun v hv => L.Z_not_reg hB (by omega) hv _,
    fun v hv => L.Z_in_reg hB (by omega) hv _, ?_⟩
  intro v _ h1 h2
  rcases L.mem_reg.mp h1 with ⟨j, hj, hvj⟩ | ⟨hh, hH⟩
  · rcases Nat.lt_or_ge j (i + 1) with hlt | hge
    · exact absurd (L.mem_reg.mpr (Or.inl ⟨j, by omega, hvj⟩)) h2
    · have : j = i + 1 := by omega
      rw [← this]; exact hvj
  · exact absurd (L.mem_reg.mpr (Or.inr ⟨Att.flag_back hpa hh, hH⟩)) h2

variable (hM : M.IsMolecule) (hT : M.IsTVine S a b) (hA : AttachInput)
include hM hT hA

theorem port_reg {i : ℕ} (hi : i ≤ L.r) (hh : Bool) (hflag : hh = att.hx i ∨ hh = att.he i) :
    Nonempty (Port2 M S (L.reg i hh) a b) :=
  port2_of hM hT hA (L.reg_sub hB i (by omega) hh) (L.card_flag hB A hM hi hh hflag)

omit A in
theorem port_pend {k : ℕ} (hk : k < L.s) : Nonempty (Port2 M S (S \ L.H k) a b) :=
  port2_of hM hT hA sdiff_subset (L.card_pend hB hk)

/-! ## Spine rungs -/

theorem pc_spineRung {i : ℕ} (hi : i < L.r) {u w : V} (huw : u ≠ w) (hZ : L.Z (i + 1) = {u, w})
    (h2 : M.bondsBetween u w = 2) :
    Nonempty (PCell M S a b 2 2 (fun _ c => PairOK c ∧ c.mu = 2) (L.Z (i + 1)) (L.reg i (att.he i))
      (some (L.reg (i + 1) (att.hx (i + 1)))) none 1 1 6) := by
  have hu : u ∈ L.Z (i + 1) := by rw [hZ]; simp
  have hw : w ∈ L.Z (i + 1) := by rw [hZ]; simp
  obtain ⟨hua, hub⟩ := L.Z_interior (by omega) (by omega) hu
  obtain ⟨hwa, hwb⟩ := L.Z_interior (by omega) (by omega) hw
  have huS := L.Z_sub hB (by omega) hu
  have hwS := L.Z_sub hB (by omega) hw
  obtain ⟨pti⟩ := L.port_reg hB A hM hT hA (i := i) (by omega) (att.he i) (Or.inr rfl)
  obtain ⟨pto⟩ := L.port_reg hB A hM hT hA (i := i + 1) (by omega) (att.hx (i + 1)) (Or.inl rfl)
  have hEi : InEnds pti u w := by
    obtain ⟨h1, h2⟩ := L.entry_ends hB A (by omega) pti
    rw [hZ, mem_insert, mem_singleton] at h1 h2
    exact inEnds_of pti hua hub hwa hwb h1 h2
  have hEo : OutEnds pto u w := by
    obtain ⟨h1, h2⟩ := L.exit_ends hB A (by omega) pto
    rw [hZ, mem_insert, mem_singleton] at h1 h2
    exact outEnds_of pto hua hub hwa hwb h1 h2
  obtain ⟨d₀, d₁, hdd, hd₀, hd₁⟩ := two_bonds huS hwS h2
  obtain ⟨c, hc, φ, hφA, -, heO, heI, p, hp, hp1, hp2⟩ := place_rung rungTable rungTable_ok rungTable_cover hM
    huw (hB.1 huS) (hB.1 hwS) (deg4 hB huS hua hub) (deg4 hB hwS hwa hwb) d₀ d₁ hdd hd₀ hd₁ pti pto
    (L.reg_mono (by omega) Att.flag_mono) (L.Z_not_reg hB (by omega) hu _) (L.Z_not_reg hB (by omega) hw _)
    (L.Z_in_reg hB (by omega) hu _) (L.Z_in_reg hB (by omega) hw _) hEi hEo
  obtain ⟨hv, hok, hrc, hrel, hex, hmu⟩ := rungTable_ok c hc
  have hoB : c.outB = none := outB_none_of rungShape hrc (by decide)
  exact ⟨{
    cfg := c
    emb := φ
    valid := hv
    ok := ⟨hok, hmu⟩
    rel := hrel
    extra := fun x => (extra_none hex hoB x).elim
    atoms := by rw [hZ]; exact atoms_two hφA
    pin := pti
    bO := heO
    bI := heI
    oM := by
      intro X hX pt
      obtain rfl := Option.some.inj hX
      exact ⟨p, hp, hp1.trans (port2_out_eq pto pt), hp2.trans (port2_inn_eq pto pt)⟩
    oB := by intro X hX; cases hX }⟩

/-! ## The junction -/

theorem pc_spineJunction {i : ℕ} (hi : i < L.r) (hpa : att = .pa (i + 1)) :
    Nonempty (PCell M S a b 2 2 (fun _ c => PairOK c ∧ c.mu = 1) (L.Z (i + 1)) (L.reg i (att.he i))
      (some (L.reg (i + 1) (att.hx (i + 1)))) (some (S \ L.H 0)) 1 1 7) := by
  subst hpa
  have hcase : 1 ≤ L.s ∧ 1 ≤ i + 1 ∧ i + 1 ≤ L.r ∧ A.x ∈ L.Z (i + 1) ∧ A.x' ∈ L.Z (i + 1) ∧
      IsJunctionPiece M (L.Z (i + 1)) := A.case
  obtain ⟨hs, -, -, hx, hx', hJ⟩ := hcase
  obtain ⟨u, w, huw, hZ, h1⟩ := hJ
  have hu : u ∈ L.Z (i + 1) := by rw [hZ]; simp
  have hw : w ∈ L.Z (i + 1) := by rw [hZ]; simp
  obtain ⟨hua, hub⟩ := L.Z_interior (by omega) (by omega) hu
  obtain ⟨hwa, hwb⟩ := L.Z_interior (by omega) (by omega) hw
  have huS := L.Z_sub hB (by omega) hu
  have hwS := L.Z_sub hB (by omega) hw
  obtain ⟨pti⟩ := L.port_reg hB A hM hT hA (i := i) (by omega) _ (Or.inr rfl)
  obtain ⟨pto⟩ := L.port_reg hB A hM hT hA (i := i + 1) (by omega) _ (Or.inl rfl)
  obtain ⟨ptb⟩ := L.port_pend hB hM hT hA (k := 0) (by omega)
  have hEi : InEnds pti u w := by
    obtain ⟨h1, h2⟩ := L.entry_ends hB A (by omega) pti
    rw [hZ, mem_insert, mem_singleton] at h1 h2
    exact inEnds_of pti hua hub hwa hwb h1 h2
  have hEo : OutEnds pto u w := by
    obtain ⟨h1, h2⟩ := L.exit_ends hB A (by omega) pto
    rw [hZ, mem_insert, mem_singleton] at h1 h2
    exact outEnds_of pto hua hub hwa hwb h1 h2
  have hEb : OutEnds ptb u w := by
    obtain ⟨h1, h2⟩ := L.pend_spine_ends hB A hs ptb
    rw [hZ, mem_insert, mem_singleton] at hx hx'
    apply outEnds_of ptb hua hub hwa hwb
    · rcases h1 with h | h <;> rw [h] <;> assumption
    · rcases h2 with h | h <;> rw [h] <;> assumption
  obtain ⟨d₀, hd₀⟩ := one_bond huS hwS h1
  have hhe : (Att.pa (i + 1)).he i = false := by simp [Att.he]
  have hhx : (Att.pa (i + 1)).hx (i + 1) = true := by simp [Att.hx]
  have hH0 : ∀ v, v ∈ L.H 0 → v ∈ L.reg (i + 1) ((Att.pa (i + 1)).hx (i + 1)) := fun v hv =>
    L.mem_reg.mpr (Or.inr ⟨hhx, hv⟩)
  have hXib : L.reg i ((Att.pa (i + 1)).he i) ⊆ S \ L.H 0 := by
    rw [hhe]; exact L.reg_sub_compl hB (by omega)
  have hob : ∀ v ∈ S, v ∉ L.reg (i + 1) ((Att.pa (i + 1)).hx (i + 1)) → v ∈ S \ L.H 0 := fun v hv h =>
    mem_sdiff.mpr ⟨hv, fun h' => h (hH0 v h')⟩
  have hbo : ∀ v ∈ S, v ∉ S \ L.H 0 → v ∈ L.reg (i + 1) ((Att.pa (i + 1)).hx (i + 1)) := fun v hv h =>
    hH0 v (by by_contra h'; exact h (mem_sdiff.mpr ⟨hv, h'⟩))
  have hub' : u ∈ S \ L.H 0 := mem_sdiff.mpr ⟨huS, L.not_mem_H_of_Z hB (by omega) hu⟩
  have hwb' : w ∈ S \ L.H 0 := mem_sdiff.mpr ⟨hwS, L.not_mem_H_of_Z hB (by omega) hw⟩
  obtain ⟨c, hc, φ, hφA, -, heO, heI, ⟨p, hp, hp1, hp2⟩, q, hq, hq1, hq2⟩ := place_junction junctionTable
    junctionTable_ok junctionTable_cover hM huw (hB.1 huS) (hB.1 hwS) (deg4 hB huS hua hub)
    (deg4 hB hwS hwa hwb) d₀ hd₀ pti pto ptb (L.reg_mono (by omega) Att.flag_mono) hXib hob hbo
    (L.Z_not_reg hB (by omega) hu _) (L.Z_not_reg hB (by omega) hw _) (L.Z_in_reg hB (by omega) hu _)
    (L.Z_in_reg hB (by omega) hw _) hub' hwb' hEi hEo hEb
  obtain ⟨hv, hok, -, hrel, hex, hmu⟩ := junctionTable_ok c hc
  exact ⟨{
    cfg := c
    emb := φ
    valid := hv
    ok := ⟨hok, hmu⟩
    rel := hrel
    extra := extra_some φ sdiff_subset ptb hex hq hq1 hq2
    atoms := by rw [hZ]; exact atoms_two hφA
    pin := pti
    bO := heO
    bI := heI
    oM := by
      intro X hX pt
      obtain rfl := Option.some.inj hX
      exact ⟨p, hp, hp1.trans (port2_out_eq pto pt), hp2.trans (port2_inn_eq pto pt)⟩
    oB := by
      intro X hX pt
      obtain rfl := Option.some.inj hX
      exact ⟨q, hq, hq1.trans (port2_out_eq ptb pt), hq2.trans (port2_inn_eq ptb pt)⟩ }⟩

/-! ## The spine core -/

theorem pc_spineCore {i : ℕ} (hi : i < L.r) (hnone : att = .none) (hC : IsCoreBC M (L.Z (i + 1))) :
    Nonempty (PCell M S a b 3 3 (fun _ c => CoreOK c) (L.Z (i + 1)) (L.reg i (att.he i))
      (some (L.reg (i + 1) (att.hx (i + 1)))) none 1 1 8) := by
  obtain ⟨x, y, z, hxy, hyz, hxz, hZ, hbxy, hBC⟩ := hC
  have hx : x ∈ L.Z (i + 1) := by rw [hZ]; simp
  have hy : y ∈ L.Z (i + 1) := by rw [hZ]; simp
  have hz : z ∈ L.Z (i + 1) := by rw [hZ]; simp
  obtain ⟨hxa, hxb⟩ := L.Z_interior (by omega) (by omega) hx
  obtain ⟨hya, hyb⟩ := L.Z_interior (by omega) (by omega) hy
  obtain ⟨hza, hzb⟩ := L.Z_interior (by omega) (by omega) hz
  have hxS := L.Z_sub hB (by omega) hx
  have hyS := L.Z_sub hB (by omega) hy
  have hzS := L.Z_sub hB (by omega) hz
  obtain ⟨pti⟩ := L.port_reg hB A hM hT hA (i := i) (by omega) (att.he i) (Or.inr rfl)
  obtain ⟨pto⟩ := L.port_reg hB A hM hT hA (i := i + 1) (by omega) (att.hx (i + 1)) (Or.inl rfl)
  have hpa : att ≠ .pa (i + 1) := by rw [hnone]; exact fun h => by cases h
  obtain ⟨hio, hCi, hCo, hdiff⟩ := L.spine_sandwich hB A hi hpa
  have hbud : ∀ v, v ∈ L.Z (i + 1) → v ≠ a → v ≠ b →
      (innerAt (M := M) (S := S) (L.Z (i + 1)) v).card + (portAt (M := M) (S := S) (L.reg i (att.he i)) v).card +
        (portAt (M := M) (S := S) (L.reg (i + 1) (att.hx (i + 1))) v).card = 4 := by
    intro v hv hva hvb
    rw [budget hio hCi hCo hdiff hv (noLoopAt hT hva hvb)]
    exact deg4 hB (L.Z_sub hB (by omega) hv) hva hvb
  have hix : (innerAt (M := M) (S := S) (L.Z (i + 1)) x).card = M.bondsBetween x y + M.bondsBetween x z := by
    rw [hZ]; exact card_innerAt_three hxy hyz hxz hxS hyS hzS (noLoopAt hT hxa hxb)
  have hiy : (innerAt (M := M) (S := S) (L.Z (i + 1)) y).card = M.bondsBetween y x + M.bondsBetween y z := by
    rw [hZ, perm_xyz]; exact card_innerAt_three hxy.symm hxz hyz hyS hxS hzS (noLoopAt hT hya hyb)
  have hiz : (innerAt (M := M) (S := S) (L.Z (i + 1)) z).card = M.bondsBetween z x + M.bondsBetween z y := by
    rw [hZ, perm_zxy]; exact card_innerAt_three hxz.symm hxy hyz.symm hzS hxS hyS (noLoopAt hT hza hzb)
  rw [bondsBetween_comm y x] at hiy
  rw [bondsBetween_comm z x, bondsBetween_comm z y] at hiz
  have hmem3 : ∀ v, v ∈ L.Z (i + 1) → v = x ∨ v = y ∨ v = z := by
    intro v hv; rw [hZ] at hv; simpa only [mem_insert, mem_singleton] using hv
  obtain ⟨hP1, hP2⟩ := L.entry_ends hB A (by omega) pti
  obtain ⟨hQ1, hQ2⟩ := L.exit_ends hB A (by omega) pto
  have hPne : hd pti.out ≠ tl pti.inn := fun h =>
    pti.distinct _ (L.Z_interior (by omega) (by omega) hP1).1 (L.Z_interior (by omega) (by omega) hP1).2
      ⟨Or.inr rfl, Or.inl h.symm⟩
  have hQne : tl pto.out ≠ hd pto.inn := fun h =>
    pto.distinct _ (L.Z_interior (by omega) (by omega) hQ1).1 (L.Z_interior (by omega) (by omega) hQ1).2
      ⟨Or.inl rfl, Or.inr h.symm⟩
  have hnXi : ∀ v, v ∈ L.Z (i + 1) → v ∉ L.reg i (att.he i) := hCi
  have hXo : ∀ v, v ∈ L.Z (i + 1) → v ∈ L.reg (i + 1) (att.hx (i + 1)) := fun v hv => hCo hv
  obtain ⟨dxy₀, dxy₁, hdxy, hxy₀, hxy₁⟩ := two_bonds hxS hyS hbxy
  rcases hBC with ⟨hbyz, hbxz⟩ | ⟨hbyz, hbxz⟩
  · -- (B): `z` carries one bond of each port, `x` and `y` one port bond each
    obtain ⟨dyz, hyz₀⟩ := one_bond hyS hzS hbyz
    obtain ⟨dxz, hxz₀⟩ := one_bond hxS hzS hbxz
    have hz2 := both_of_budget pti pto hza hzb (hnXi z hz) (hXo z hz) (hbud z hz hza hzb) (by omega)
    have hx3 := not_both_of_budget pti pto (hbud x hx hxa hxb) (by omega)
    have hy3 := not_both_of_budget pti pto (hbud y hy hya hyb) (by omega)
    rcases logic_B hxy hyz hxz (hmem3 _ hP1) (hmem3 _ hP2) (hmem3 _ hQ1) (hmem3 _ hQ2) hPne hQne
      (by rcases hz2.1 with h | h <;> [left; right] <;> exact h) (by rcases hz2.2 with h | h <;> [left; right] <;> exact h)
      (by rintro ⟨h1, h2⟩; exact hx3 ⟨by rcases h1 with h | h <;> [left; right] <;> exact h,
        by rcases h2 with h | h <;> [left; right] <;> exact h⟩)
      (by rintro ⟨h1, h2⟩; exact hy3 ⟨by rcases h1 with h | h <;> [left; right] <;> exact h,
        by rcases h2 with h | h <;> [left; right] <;> exact h⟩) with ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩
    · have hEi : InEnds pti z x := inEnds_of pti hza hzb hxa hxb e1 e2
      have hEo : OutEnds pto z y := outEnds_of pto hza hzb hya hyb e3 e4
      obtain ⟨c, hc, φ, hφA, -, heO, heI, p, hp, hp1, hp2⟩ := place_coreB coreBTable coreBTable_ok
        coreBTable_cover hM hxy hxz hyz (hB.1 hxS) (hB.1 hyS) (hB.1 hzS) (deg4 hB hxS hxa hxb)
        (deg4 hB hyS hya hyb) (deg4 hB hzS hza hzb) dxy₀ hxy₀ dxy₁ hxy₁ dyz hyz₀ dxz hxz₀ hdxy pti pto hio
        (hnXi x hx) (hnXi y hy) (hnXi z hz) (hXo x hx) (hXo y hy) (hXo z hz) hEi hEo
      obtain ⟨hv, hok, hrc, hrel, hex⟩ := coreBTable_ok c hc
      have hB' := outB_none_of coreBShape hrc (by decide)
      exact ⟨{
        cfg := c, emb := φ, valid := hv, ok := hok, rel := hrel
        extra := fun x => (extra_none hex hB' x).elim
        atoms := by rw [hZ]; exact atoms_three hφA
        pin := pti, bO := heO, bI := heI
        oM := by
          intro X hX pt
          obtain rfl := Option.some.inj hX
          exact ⟨p, hp, hp1.trans (port2_out_eq pto pt), hp2.trans (port2_inn_eq pto pt)⟩
        oB := by intro X hX; cases hX }⟩
    · have hEi : InEnds pti z y := inEnds_of pti hza hzb hya hyb e1 e2
      have hEo : OutEnds pto z x := outEnds_of pto hza hzb hxa hxb e3 e4
      obtain ⟨c, hc, φ, hφA, -, heO, heI, p, hp, hp1, hp2⟩ := place_coreB coreBTable coreBTable_ok
        coreBTable_cover hM hxy.symm hyz hxz (hB.1 hyS) (hB.1 hxS) (hB.1 hzS) (deg4 hB hyS hya hyb)
        (deg4 hB hxS hxa hxb) (deg4 hB hzS hza hzb) dxy₀ hxy₀.symm dxy₁ hxy₁.symm dxz hxz₀ dyz hyz₀ hdxy pti pto
        hio (hnXi y hy) (hnXi x hx) (hnXi z hz) (hXo y hy) (hXo x hx) (hXo z hz) hEi hEo
      obtain ⟨hv, hok, hrc, hrel, hex⟩ := coreBTable_ok c hc
      have hB' := outB_none_of coreBShape hrc (by decide)
      exact ⟨{
        cfg := c, emb := φ, valid := hv, ok := hok, rel := hrel
        extra := fun x => (extra_none hex hB' x).elim
        atoms := by rw [hZ, perm_xyz]; exact atoms_three hφA
        pin := pti, bO := heO, bI := heI
        oM := by
          intro X hX pt
          obtain rfl := Option.some.inj hX
          exact ⟨p, hp, hp1.trans (port2_out_eq pto pt), hp2.trans (port2_inn_eq pto pt)⟩
        oB := by intro X hX; cases hX }⟩
  · -- (C): the ends `x`, `z` carry one bond of each port
    obtain ⟨dyz₀, dyz₁, hdyz, hyz₀, hyz₁⟩ := two_bonds hyS hzS hbyz
    have hx2 := both_of_budget pti pto hxa hxb (hnXi x hx) (hXo x hx) (hbud x hx hxa hxb) (by omega)
    have hz2 := both_of_budget pti pto hza hzb (hnXi z hz) (hXo z hz) (hbud z hz hza hzb) (by omega)
    obtain ⟨e1, e2⟩ := logic_C hxy hyz hxz (hmem3 _ hP1) (hmem3 _ hP2) hPne hx2.1 hz2.1
    obtain ⟨e3, e4⟩ := logic_C hxy hyz hxz (hmem3 _ hQ1) (hmem3 _ hQ2) hQne hx2.2 hz2.2
    have hEi : InEnds pti x z := inEnds_of pti hxa hxb hza hzb e1 e2
    have hEo : OutEnds pto x z := outEnds_of pto hxa hxb hza hzb e3 e4
    obtain ⟨c, hc, φ, hφA, -, heO, heI, p, hp, hp1, hp2⟩ := place_coreC coreCTable coreCTable_ok
      coreCTable_cover hM hxy hxz hyz (hB.1 hxS) (hB.1 hyS) (hB.1 hzS) (deg4 hB hxS hxa hxb)
      (deg4 hB hyS hya hyb) (deg4 hB hzS hza hzb) dxy₀ hxy₀ dxy₁ hxy₁ dyz₀ hyz₀ dyz₁ hyz₁ hdxy hdyz pti pto hio
      (hnXi x hx) (hnXi y hy) (hnXi z hz) (hXo x hx) (hXo y hy) (hXo z hz) hEi hEo
    obtain ⟨hv, hok, hrc, hrel, hex⟩ := coreCTable_ok c hc
    have hB' := outB_none_of coreCShape hrc (by decide)
    exact ⟨{
      cfg := c, emb := φ, valid := hv, ok := hok, rel := hrel
      extra := fun x => (extra_none hex hB' x).elim
      atoms := by rw [hZ]; exact atoms_three hφA
      pin := pti, bO := heO, bI := heI
      oM := by
        intro X hX pt
        obtain rfl := Option.some.inj hX
        exact ⟨p, hp, hp1.trans (port2_out_eq pto pt), hp2.trans (port2_inn_eq pto pt)⟩
      oB := by intro X hX; cases hX }⟩

end Lay

end WaveTurbulence.TVine.Chart
