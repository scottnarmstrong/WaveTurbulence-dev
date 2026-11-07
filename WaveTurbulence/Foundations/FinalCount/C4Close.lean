/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.C4Route
public import WaveTurbulence.Foundations.FinalCount.C4Cut
public import WaveTurbulence.Foundations.FinalCount.C5VineD
public import WaveTurbulence.Foundations.FinalCount.G8R.ThmA
import Mathlib.Tactic

/-! # Prop 9.6, case (4): the closures `𝕄₁` are regular molecules without cut vertex

* one chain `u → b → b′ → v`: `closureOne` is the post molecule of the literal two-exit set `{b, b′}`;
* two chains: `closureTwo`; the in/out degrees of its atoms are those of `𝕄₀`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp4

section
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **`closureOne` is regular, connected, without cut vertex.** -/
theorem regcore_closureOne {M : Molecule V D} (hcap : ∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2)
    (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z)) (hconn : ∀ a ∈ M.atoms, ∀ c ∈ M.atoms, M.SameComponent a c)
    (hnocut : ∀ w ∈ M.atoms, ∀ a ∈ M.atoms, ∀ c ∈ M.atoms, a ≠ w → c ≠ w →
      (Degen.eraseAtoms M {w}).SameComponent a c)
    {b b' : V} (hb : b ∈ M.atoms) (hb' : b' ∈ M.atoms) (hdeg4 : ∀ v ∈ M.atoms, v ≠ b → v ≠ b' → M.deg v = 4)
    {x₁ x₂ : D} (hcross : crossDarts M {b, b'} = {x₁, x₂}) (hne : x₁ ≠ x₂) (ho1 : M.out x₁ = false)
    (ho2 : M.out x₂ = true) (hfar : M.atom (M.mate x₁) ≠ M.atom (M.mate x₂)) :
    RegCore (closureOne M b b' x₁ x₂) := by
  have hsub : ({b, b'} : Finset V) ⊆ M.atoms := by
    intro v hv; rcases mem_insert.mp hv with rfl | h
    · exact hb
    · rw [mem_singleton.mp h]; exact hb'
  let T : TwoExit M := ⟨{b, b'}, hsub, x₂, x₁, by rw [hcross]; exact pair_comm _ _, hne.symm, hfar.symm, ho2, ho1⟩
  have hT : closureOne M b b' x₁ x₂ = T.post := rfl
  rw [hT]
  refine ⟨T.post_caps hcap, T.post_loop hloop, fun a ha => ?_, T.post_connected hconn, T.post_noCut hnocut⟩
  rw [T.post_atoms] at ha
  obtain ⟨haM, haY⟩ := mem_sdiff.mp ha
  rw [T.post_deg haY]
  exact hdeg4 a haM (fun h => haY (by simp [T, h])) (fun h => haY (by simp [T, h]))

theorem outdeg_split (M : Molecule V D) (Y : Finset V) {z : V} (hz : z ∉ Y) :
    M.outdeg z = (Degen.eraseAtoms M Y).outdeg z +
      ((Degen.removedDartsAt M Y z).filter (fun x => M.out x = true)).card := by
  classical
  have h := Degen.sum_dartsAt_split M Y hz (fun x => if M.out x = true then (1 : ℕ) else 0)
  have e1 : ∑ x ∈ M.dartsAt z, (if M.out x = true then (1 : ℕ) else 0) = M.outdeg z := by
    rw [sum_boole]; rfl
  have e2 : ∑ x ∈ (Degen.eraseAtoms M Y).dartsAt z, (if M.out x.val = true then (1 : ℕ) else 0) =
      (Degen.eraseAtoms M Y).outdeg z := by
    rw [sum_boole]; rfl
  have e3 : ∑ x ∈ Degen.removedDartsAt M Y z, (if M.out x = true then (1 : ℕ) else 0) =
      ((Degen.removedDartsAt M Y z).filter (fun x => M.out x = true)).card := by
    rw [sum_boole]; simp
  rw [e1, e2, e3] at h
  exact h

theorem indeg_split (M : Molecule V D) (Y : Finset V) {z : V} (hz : z ∉ Y) :
    M.indeg z = (Degen.eraseAtoms M Y).indeg z +
      ((Degen.removedDartsAt M Y z).filter (fun x => M.out x = false)).card := by
  classical
  have h := Degen.sum_dartsAt_split M Y hz (fun x => if M.out x = false then (1 : ℕ) else 0)
  have e1 : ∑ x ∈ M.dartsAt z, (if M.out x = false then (1 : ℕ) else 0) = M.indeg z := by
    rw [sum_boole]; rfl
  have e2 : ∑ x ∈ (Degen.eraseAtoms M Y).dartsAt z, (if M.out x.val = false then (1 : ℕ) else 0) =
      (Degen.eraseAtoms M Y).indeg z := by
    rw [sum_boole]; rfl
  have e3 : ∑ x ∈ Degen.removedDartsAt M Y z, (if M.out x = false then (1 : ℕ) else 0) =
      ((Degen.removedDartsAt M Y z).filter (fun x => M.out x = false)).card := by
    rw [sum_boole]; simp
  rw [e1, e2, e3] at h
  exact h

/-- The removed darts at `z` for a degree-two atom `b` with darts `p` (in) and `q` (out). -/
theorem removed_card (K : Molecule V D) {b : V} {p q : D} (hp : K.atom p = b) (hq : K.atom q = b)
    (hall : ∀ x, K.atom x = b → x = p ∨ x = q) (hop : K.out p = false) (hoq : K.out q = true) (z : V) :
    ((Degen.removedDartsAt K {b} z).filter (fun x => K.out x = true)).card = (if K.atom (K.mate p) = z then 1 else 0) ∧
    ((Degen.removedDartsAt K {b} z).filter (fun x => K.out x = false)).card = (if K.atom (K.mate q) = z then 1 else 0) := by
  classical
  have hmo : ∀ y, K.out (K.mate y) = !K.out y := fun y => by
    have := K.out_mate y; cases h : K.out y <;> simp_all
  have hset : ∀ (e : D) (bo : Bool), K.atom e = b → K.out e = !bo →
      (∀ x, K.atom x = b → K.out x = !bo → x = e) →
      ((Degen.removedDartsAt K {b} z).filter (fun x => K.out x = bo)).card =
        (if K.atom (K.mate e) = z then 1 else 0) := by
    intro e bo he hoe huniq
    have hcard : (Degen.removedDartsAt K {b} z).filter (fun x => K.out x = bo) =
        if K.atom (K.mate e) = z then {K.mate e} else ∅ := by
      ext x
      simp only [Degen.removedDartsAt, Molecule.dartsAt, mem_filter, mem_univ, true_and, mem_singleton]
      split_ifs with hc
      · simp only [mem_singleton]
        constructor
        · rintro ⟨⟨_, hx2⟩, hxo⟩
          have hmx : K.atom (K.mate x) = b := by simpa using hx2
          have : K.mate x = e := huniq _ hmx (by rw [hmo, hxo])
          rw [← this, K.mate_mate]
        · rintro rfl
          refine ⟨⟨hc, by simp [K.mate_mate, he]⟩, ?_⟩
          have := hmo e; rw [hoe] at this
          cases bo <;> simpa using this
      · simp only [Finset.notMem_empty, iff_false]
        rintro ⟨⟨hx1, hx2⟩, hxo⟩
        have hmx : K.atom (K.mate x) = b := by simpa using hx2
        have : K.mate x = e := huniq _ hmx (by rw [hmo, hxo])
        apply hc; rw [← this, K.mate_mate]; exact hx1
    rw [hcard]; split_ifs <;> simp
  refine ⟨hset p true hp (by rw [hop]; rfl) ?_, hset q false hq (by rw [hoq]; rfl) ?_⟩
  · intro x hx hxo
    rcases hall x hx with rfl | rfl
    · rfl
    · simp [hoq] at hxo
  · intro x hx hxo
    rcases hall x hx with rfl | rfl
    · simp [hop] at hxo
    · rfl

/-- **The in/out degrees of `closureTwo` are those of `𝕄₀`** (the new bonds restore the removed darts). -/
theorem closureTwo_dir (M : Molecule V D) {b b' : V} {y₁ y₂ y₃ y₄ : D} (hbb' : b ≠ b')
    (hat1 : M.atom y₁ = b) (hat2 : M.atom y₂ = b) (hat3 : M.atom y₃ = b') (hat4 : M.atom y₄ = b')
    (hall1 : ∀ x, M.atom x = b → x = y₁ ∨ x = y₂) (hall2 : ∀ x, M.atom x = b' → x = y₃ ∨ x = y₄)
    (ho1 : M.out y₁ = false) (ho2 : M.out y₂ = true) (ho3 : M.out y₃ = false) (ho4 : M.out y₄ = true)
    (p₃ : M.atom y₃ ∉ ({b} : Finset V) ∧ M.atom (M.mate y₃) ∉ ({b} : Finset V))
    (p₄ : M.atom y₄ ∉ ({b} : Finset V) ∧ M.atom (M.mate y₄) ∉ ({b} : Finset V))
    {z : V} (hzb : z ≠ b) (hzb' : z ≠ b') :
    (closureTwo M b b' y₁ y₂ y₃ y₄).outdeg z = M.outdeg z ∧ (closureTwo M b b' y₁ y₂ y₃ y₄).indeg z = M.indeg z := by
  classical
  unfold closureTwo
  have hz1 : z ∉ ({b} : Finset V) := by simpa using hzb
  have hz2 : z ∉ ({b'} : Finset V) := by simpa using hzb'
  have hall2' : ∀ x : Degen.RetainedDart M {b}, (Degen.eraseAtoms M {b}).atom x = b' →
      x = ⟨y₃, p₃⟩ ∨ x = ⟨y₄, p₄⟩ := by
    intro x hx
    rcases hall2 x.val hx with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have r1 := removed_card M hat1 hat2 hall1 ho1 ho2 z
  have r2 := removed_card (Degen.eraseAtoms M {b}) (b := b') (p := ⟨y₃, p₃⟩) (q := ⟨y₄, p₄⟩) hat3 hat4 hall2' ho3 ho4 z
  have o1 := outdeg_split M {b} hz1
  have i1 := indeg_split M {b} hz1
  have o2 := outdeg_split (Degen.eraseAtoms M {b}) {b'} hz2
  have i2 := indeg_split (Degen.eraseAtoms M {b}) {b'} hz2
  rw [show (Degen.eraseAtoms M {b}).atom ((Degen.eraseAtoms M {b}).mate ⟨y₃, p₃⟩) = M.atom (M.mate y₃) from rfl,
    show (Degen.eraseAtoms M {b}).atom ((Degen.eraseAtoms M {b}).mate ⟨y₄, p₄⟩) = M.atom (M.mate y₄) from rfl] at r2
  rw [addBond_outdeg, addBond_outdeg, addBond_indeg', addBond_indeg']
  refine ⟨?_, ?_⟩
  · rw [r1.1] at o1
    rw [r2.1] at o2
    split_ifs at o1 o2 ⊢ <;> omega
  · rw [r1.2] at i1
    rw [r2.2] at i2
    split_ifs at i1 i2 ⊢ <;> omega

/-- Adjacency of distinct atoms is a positive bond count. -/
theorem adj_iff_bb {N : Molecule V D} (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z)) (p q : V) :
    (∃ z, N.atom z = p ∧ N.atom (N.mate z) = q) ↔ 1 ≤ N.bondsBetween p q := by
  classical
  constructor
  · rintro ⟨z, rfl, rfl⟩
    rw [← Degen.card_neighborDarts N (hloop z)]
    exact card_pos.mpr ⟨z, (Degen.mem_neighborDarts N _ _ z).mpr ⟨rfl, rfl⟩⟩
  · intro h
    have hpq : p ≠ q := by
      rintro rfl
      rw [bondsBetween_self_eq_zero hloop] at h; omega
    rw [← Degen.card_neighborDarts N hpq] at h
    obtain ⟨z, hz⟩ := card_pos.mp h
    exact ⟨z, (Degen.mem_neighborDarts N _ _ z).mp hz⟩

/-- Connectivity in terms of the bond counts. -/
theorem sc_iff_bb {N : Molecule V D} (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z)) (a c : V) :
    N.SameComponent a c ↔ Relation.EqvGen (fun p q => 1 ≤ N.bondsBetween p q) a c := by
  unfold Molecule.SameComponent
  constructor
  · intro h
    exact Relation.EqvGen.mono (fun p q hpq => (adj_iff_bb hloop p q).mp hpq) a c h
  · intro h
    exact Relation.EqvGen.mono (fun p q hpq => (adj_iff_bb hloop p q).mpr hpq) a c h

/-- Connectivity after erasing `W`, in terms of the bond counts. -/
theorem sc_erase_iff {N : Molecule V D} (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z)) (W : Finset V) (a c : V) :
    (Degen.eraseAtoms N W).SameComponent a c ↔
      Relation.EqvGen (fun p q => p ∉ W ∧ q ∉ W ∧ 1 ≤ N.bondsBetween p q) a c := by
  unfold Molecule.SameComponent
  constructor
  · intro h
    refine Relation.EqvGen.mono (fun p q hpq => ?_) a c h
    obtain ⟨z, rfl, rfl⟩ := hpq
    exact ⟨z.property.1, z.property.2, (adj_iff_bb hloop _ _).mp ⟨z.val, rfl, rfl⟩⟩
  · intro h
    refine Relation.EqvGen.mono (fun p q hpq => ?_) a c h
    obtain ⟨hp, hq, h1⟩ := hpq
    obtain ⟨z, rfl, rfl⟩ := (adj_iff_bb hloop p q).mpr h1
    exact ⟨⟨z, hp, hq⟩, rfl, rfl⟩

end

/-- **Graph transfer through two replaced chains** (bond-count level): paths of `𝕄₀ ∖ W` between atoms outside the chains
give paths of `𝕄₁ ∖ W`, where each chain atom `b` (neighbours `c, d`) is replaced by a bond `c — d`. -/
theorem graph_transfer {V : Type*} [DecidableEq V] (bb₀ bb₁ : V → V → ℕ) (b b' c d c' d' : V) (W : Finset V)
    (hbb : b ≠ b') (hsym : ∀ p q, bb₀ p q = bb₀ q p)
    (hA : ∀ p q, p ≠ b → p ≠ b' → q ≠ b → q ≠ b' → bb₀ p q ≤ bb₁ p q)
    (hB : 1 ≤ bb₁ c d) (hB' : 1 ≤ bb₁ c' d')
    (hC : ∀ x, 1 ≤ bb₀ b x → x = c ∨ x = d) (hD : ∀ x, 1 ≤ bb₀ b' x → x = c' ∨ x = d')
    (hE : c ≠ b ∧ c ≠ b' ∧ d ≠ b ∧ d ≠ b' ∧ c' ≠ b ∧ c' ≠ b' ∧ d' ≠ b ∧ d' ≠ b')
    (hW : ¬ (c ∈ W ∧ d ∈ W)) (hW' : ¬ (c' ∈ W ∧ d' ∈ W)) (x y : V)
    (hxy : Relation.EqvGen (fun p q => p ∉ W ∧ q ∉ W ∧ 1 ≤ bb₀ p q) x y)
    (hx : x ≠ b ∧ x ≠ b') (hy : y ≠ b ∧ y ≠ b') :
    Relation.EqvGen (fun p q => p ∉ W ∧ q ∉ W ∧ 1 ≤ bb₁ p q) x y := by
  classical
  obtain ⟨hcb, hcb', hdb, hdb', hc'b, hc'b', hd'b, hd'b'⟩ := hE
  let r : V → V := fun v => if v = b then (if c ∈ W then d else c) else if v = b' then (if c' ∈ W then d' else c') else v
  have hr0 : ∀ v, v ≠ b → v ≠ b' → r v = v := fun v h1 h2 => by simp [r, h1, h2]
  have hrb : r b = if c ∈ W then d else c := by simp [r]
  have hrb' : r b' = if c' ∈ W then d' else c' := by simp [r, hbb.symm]
  have step_other : ∀ p q, p ≠ b → p ≠ b' → q ≠ b → q ≠ b' → p ∉ W → q ∉ W → 1 ≤ bb₀ p q →
      Relation.EqvGen (fun p q => p ∉ W ∧ q ∉ W ∧ 1 ≤ bb₁ p q) p q := fun p q h1 h2 h3 h4 hpW hqW h =>
    Relation.EqvGen.rel _ _ ⟨hpW, hqW, le_trans h (hA p q h1 h2 h3 h4)⟩
  have step_b : ∀ q, q ≠ b → q ≠ b' → q ∉ W → 1 ≤ bb₀ b q →
      Relation.EqvGen (fun p q => p ∉ W ∧ q ∉ W ∧ 1 ≤ bb₁ p q) (r b) q := by
    intro q hqb hqb' hqW h
    rcases hC q h with rfl | rfl
    · rw [hrb, if_neg hqW]; exact Relation.EqvGen.refl _
    · by_cases hcW : c ∈ W
      · rw [hrb, if_pos hcW]; exact Relation.EqvGen.refl _
      · rw [hrb, if_neg hcW]; exact Relation.EqvGen.rel _ _ ⟨hcW, hqW, hB⟩
  have step_b' : ∀ q, q ≠ b → q ≠ b' → q ∉ W → 1 ≤ bb₀ b' q →
      Relation.EqvGen (fun p q => p ∉ W ∧ q ∉ W ∧ 1 ≤ bb₁ p q) (r b') q := by
    intro q hqb hqb' hqW h
    rcases hD q h with rfl | rfl
    · rw [hrb', if_neg hqW]; exact Relation.EqvGen.refl _
    · by_cases hcW : c' ∈ W
      · rw [hrb', if_pos hcW]; exact Relation.EqvGen.refl _
      · rw [hrb', if_neg hcW]; exact Relation.EqvGen.rel _ _ ⟨hcW, hqW, hB'⟩
  have key : ∀ p q, Relation.EqvGen (fun p q => p ∉ W ∧ q ∉ W ∧ 1 ≤ bb₀ p q) p q →
      Relation.EqvGen (fun p q => p ∉ W ∧ q ∉ W ∧ 1 ≤ bb₁ p q) (r p) (r q) := by
    intro p q h
    induction h with
    | rel p q hpq =>
      obtain ⟨hpW, hqW, h1⟩ := hpq
      by_cases hpb : p = b
      · rw [hpb] at h1
        by_cases hqb : q = b
        · rw [hqb] at h1; rcases hC b h1 with h | h
          · exact absurd h.symm hcb
          · exact absurd h.symm hdb
        by_cases hqb' : q = b'
        · rw [hqb'] at h1; rcases hC b' h1 with h | h
          · exact absurd h.symm hcb'
          · exact absurd h.symm hdb'
        rw [hpb, hr0 q hqb hqb']
        exact step_b q hqb hqb' hqW h1
      by_cases hpb' : p = b'
      · rw [hpb'] at h1
        by_cases hqb : q = b
        · rw [hqb] at h1; rcases hD b h1 with h | h
          · exact absurd h.symm hc'b
          · exact absurd h.symm hd'b
        by_cases hqb' : q = b'
        · rw [hqb'] at h1; rcases hD b' h1 with h | h
          · exact absurd h.symm hc'b'
          · exact absurd h.symm hd'b'
        rw [hpb', hr0 q hqb hqb']
        exact step_b' q hqb hqb' hqW h1
      rw [hr0 p hpb hpb']
      by_cases hqb : q = b
      · rw [hqb] at h1 ⊢
        rw [hsym] at h1
        exact Relation.EqvGen.symm _ _ (step_b p hpb hpb' hpW h1)
      by_cases hqb' : q = b'
      · rw [hqb'] at h1 ⊢
        rw [hsym] at h1
        exact Relation.EqvGen.symm _ _ (step_b' p hpb hpb' hpW h1)
      rw [hr0 q hqb hqb']
      exact step_other p q hpb hpb' hqb hqb' hpW hqW h1
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  have := key x y hxy
  rwa [hr0 x hx.1 hx.2, hr0 y hy.1 hy.2] at this

section
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem atoms_closureTwo (M : Molecule V D) (b b' : V) (y₁ y₂ y₃ y₄ : D)
    (h1 : M.atom (M.mate y₁) ∈ (M.atoms \ {b}) \ {b'}) (h2 : M.atom (M.mate y₂) ∈ (M.atoms \ {b}) \ {b'})
    (h3 : M.atom (M.mate y₃) ∈ (M.atoms \ {b}) \ {b'}) (h4 : M.atom (M.mate y₄) ∈ (M.atoms \ {b}) \ {b'}) :
    (closureTwo M b b' y₁ y₂ y₃ y₄).atoms = (M.atoms \ {b}) \ {b'} := by
  change insert (M.atom (M.mate y₁)) (insert (M.atom (M.mate y₂))
    (insert (M.atom (M.mate y₃)) (insert (M.atom (M.mate y₄)) ((M.atoms \ {b}) \ {b'})))) = _
  rw [insert_eq_of_mem h4, insert_eq_of_mem h3, insert_eq_of_mem h2, insert_eq_of_mem h1]

theorem loop_closureTwo (M : Molecule V D) (b b' : V) (y₁ y₂ y₃ y₄ : D) (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z))
    (huv : M.atom (M.mate y₁) ≠ M.atom (M.mate y₂)) (huv' : M.atom (M.mate y₃) ≠ M.atom (M.mate y₄)) :
    ∀ z, (closureTwo M b b' y₁ y₂ y₃ y₄).atom z ≠ (closureTwo M b b' y₁ y₂ y₃ y₄).atom
      ((closureTwo M b b' y₁ y₂ y₃ y₄).mate z) := by
  rintro ((z | bo) | bo')
  · exact hloop z.val.val
  · cases bo
    · exact huv'.symm
    · exact huv'
  · cases bo'
    · exact huv.symm
    · exact huv

theorem bb_closureTwo (M : Molecule V D) (b b' : V) (y₁ y₂ y₃ y₄ : D) {p q : V} (hp : p ≠ b) (hp' : p ≠ b')
    (hq : q ≠ b) (hq' : q ≠ b') :
    (closureTwo M b b' y₁ y₂ y₃ y₄).bondsBetween p q = M.bondsBetween p q +
      (if s(M.atom (M.mate y₃), M.atom (M.mate y₄)) = s(p, q) then 1 else 0) +
      (if s(M.atom (M.mate y₁), M.atom (M.mate y₂)) = s(p, q) then 1 else 0) := by
  unfold closureTwo
  rw [addBond_bondsBetween, addBond_bondsBetween,
    Degen.bondsBetween_erase_eq _ {b'} (by simpa using hp') (by simpa using hq'),
    Degen.bondsBetween_erase_eq M {b} (by simpa using hp) (by simpa using hq)]

/-- **`closureTwo` is regular, connected, without cut vertex.** -/
theorem regcore_closureTwo (M : Molecule V D) {b b' : V} {y₁ y₂ y₃ y₄ : D}
    (hcap : ∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z))
    (hconn : ∀ a ∈ M.atoms, ∀ c ∈ M.atoms, M.SameComponent a c)
    (hnocut : ∀ w ∈ M.atoms, ∀ a ∈ M.atoms, ∀ c ∈ M.atoms, a ≠ w → c ≠ w →
      (Degen.eraseAtoms M {w}).SameComponent a c)
    (hdeg4 : ∀ v ∈ M.atoms, v ≠ b → v ≠ b' → M.deg v = 4) (hbb' : b ≠ b')
    (hat1 : M.atom y₁ = b) (hat2 : M.atom y₂ = b) (hat3 : M.atom y₃ = b') (hat4 : M.atom y₄ = b')
    (hne12 : y₁ ≠ y₂) (hne34 : y₃ ≠ y₄)
    (hall1 : ∀ x, M.atom x = b → x = y₁ ∨ x = y₂) (hall2 : ∀ x, M.atom x = b' → x = y₃ ∨ x = y₄)
    (ho1 : M.out y₁ = false) (ho2 : M.out y₂ = true) (ho3 : M.out y₃ = false) (ho4 : M.out y₄ = true)
    (hends : ∀ y ∈ ({y₁, y₂, y₃, y₄} : Finset D), M.atom (M.mate y) ∈ M.atoms ∧ M.atom (M.mate y) ≠ b ∧
      M.atom (M.mate y) ≠ b')
    (huv : M.atom (M.mate y₁) ≠ M.atom (M.mate y₂)) (huv' : M.atom (M.mate y₃) ≠ M.atom (M.mate y₄)) :
    RegCore (closureTwo M b b' y₁ y₂ y₃ y₄) := by
  classical
  have e1 := hends y₁ (by simp); have e2 := hends y₂ (by simp)
  have e3 := hends y₃ (by simp); have e4 := hends y₄ (by simp)
  have hmem : ∀ y, M.atom (M.mate y) ∈ M.atoms → M.atom (M.mate y) ≠ b → M.atom (M.mate y) ≠ b' →
      M.atom (M.mate y) ∈ (M.atoms \ {b}) \ {b'} := fun y h1 h2 h3 =>
    mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨h1, by simpa using h2⟩, by simpa using h3⟩
  have hAt := atoms_closureTwo M b b' y₁ y₂ y₃ y₄ (hmem _ e1.1 e1.2.1 e1.2.2) (hmem _ e2.1 e2.2.1 e2.2.2)
    (hmem _ e3.1 e3.2.1 e3.2.2) (hmem _ e4.1 e4.2.1 e4.2.2)
  have hatM : ∀ z, z ∈ (closureTwo M b b' y₁ y₂ y₃ y₄).atoms → z ∈ M.atoms ∧ z ≠ b ∧ z ≠ b' := by
    intro z hz
    rw [hAt] at hz
    obtain ⟨h1, h2⟩ := mem_sdiff.mp hz
    obtain ⟨h3, h4⟩ := mem_sdiff.mp h1
    exact ⟨h3, by simpa using h4, by simpa using h2⟩
  have p₃ : M.atom y₃ ∉ ({b} : Finset V) ∧ M.atom (M.mate y₃) ∉ ({b} : Finset V) :=
    ⟨by rw [hat3]; simpa using hbb'.symm, by simpa using e3.2.1⟩
  have p₄ : M.atom y₄ ∉ ({b} : Finset V) ∧ M.atom (M.mate y₄) ∉ ({b} : Finset V) :=
    ⟨by rw [hat4]; simpa using hbb'.symm, by simpa using e4.2.1⟩
  have hdirs := fun z (hz : z ∈ (closureTwo M b b' y₁ y₂ y₃ y₄).atoms) =>
    closureTwo_dir M hbb' hat1 hat2 hat3 hat4 hall1 hall2 ho1 ho2 ho3 ho4 p₃ p₄ (hatM z hz).2.1 (hatM z hz).2.2
  have hbb_b := bb_two_darts M hloop hat1 hat2 hne12 hall1
  have hbb_b' := bb_two_darts M hloop hat3 hat4 hne34 hall2
  have hbsym := Degen.bondsBetween_comm M
  have hC : ∀ x, 1 ≤ M.bondsBetween b x → x = M.atom (M.mate y₁) ∨ x = M.atom (M.mate y₂) := by
    intro x h
    rw [hbb_b x] at h
    by_cases h1 : M.atom (M.mate y₁) = x
    · exact Or.inl h1.symm
    · by_cases h2 : M.atom (M.mate y₂) = x
      · exact Or.inr h2.symm
      · rw [if_neg h1, if_neg h2] at h; omega
  have hD : ∀ x, 1 ≤ M.bondsBetween b' x → x = M.atom (M.mate y₃) ∨ x = M.atom (M.mate y₄) := by
    intro x h
    rw [hbb_b' x] at h
    by_cases h1 : M.atom (M.mate y₃) = x
    · exact Or.inl h1.symm
    · by_cases h2 : M.atom (M.mate y₄) = x
      · exact Or.inr h2.symm
      · rw [if_neg h1, if_neg h2] at h; omega
  have hloop1 := loop_closureTwo M b b' y₁ y₂ y₃ y₄ hloop huv huv'
  have hbb1 : ∀ {p q : V}, p ≠ b → p ≠ b' → q ≠ b → q ≠ b' →
      (closureTwo M b b' y₁ y₂ y₃ y₄).bondsBetween p q = M.bondsBetween p q +
        (if s(M.atom (M.mate y₃), M.atom (M.mate y₄)) = s(p, q) then 1 else 0) +
        (if s(M.atom (M.mate y₁), M.atom (M.mate y₂)) = s(p, q) then 1 else 0) :=
    fun h1 h2 h3 h4 => bb_closureTwo M b b' y₁ y₂ y₃ y₄ h1 h2 h3 h4
  have hA : ∀ p q, p ≠ b → p ≠ b' → q ≠ b → q ≠ b' → M.bondsBetween p q ≤
      (closureTwo M b b' y₁ y₂ y₃ y₄).bondsBetween p q := by
    intro p q h1 h2 h3 h4
    rw [hbb1 h1 h2 h3 h4]; omega
  have hB : 1 ≤ (closureTwo M b b' y₁ y₂ y₃ y₄).bondsBetween (M.atom (M.mate y₁)) (M.atom (M.mate y₂)) := by
    rw [hbb1 e1.2.1 e1.2.2 e2.2.1 e2.2.2, if_pos rfl]; omega
  have hB' : 1 ≤ (closureTwo M b b' y₁ y₂ y₃ y₄).bondsBetween (M.atom (M.mate y₃)) (M.atom (M.mate y₄)) := by
    rw [hbb1 e3.2.1 e3.2.2 e4.2.1 e4.2.2, if_pos rfl]; omega
  have hE : M.atom (M.mate y₁) ≠ b ∧ M.atom (M.mate y₁) ≠ b' ∧ M.atom (M.mate y₂) ≠ b ∧ M.atom (M.mate y₂) ≠ b' ∧
      M.atom (M.mate y₃) ≠ b ∧ M.atom (M.mate y₃) ≠ b' ∧ M.atom (M.mate y₄) ≠ b ∧ M.atom (M.mate y₄) ≠ b' :=
    ⟨e1.2.1, e1.2.2, e2.2.1, e2.2.2, e3.2.1, e3.2.2, e4.2.1, e4.2.2⟩
  refine ⟨fun z hz => ?_, hloop1, fun z hz => ?_, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hdirs z hz
    rw [h1, h2]; exact hcap z (hatM z hz).1
  · obtain ⟨h1, h2⟩ := hdirs z hz
    have := Mole.outdeg_add_indeg (closureTwo M b b' y₁ y₂ y₃ y₄) z
    have h4 := Mole.outdeg_add_indeg M z
    have := hdeg4 z (hatM z hz).1 (hatM z hz).2.1 (hatM z hz).2.2
    omega
  · -- connectivity
    intro a ha c hc
    have h0 := (sc_iff_bb hloop a c).mp (hconn a (hatM a ha).1 c (hatM c hc).1)
    rw [sc_iff_bb hloop1]
    have h0' : Relation.EqvGen (fun p q => p ∉ (∅ : Finset V) ∧ q ∉ (∅ : Finset V) ∧ 1 ≤ M.bondsBetween p q) a c :=
      Relation.EqvGen.mono (fun p q h => ⟨by simp, by simp, h⟩) a c h0
    have := graph_transfer M.bondsBetween (closureTwo M b b' y₁ y₂ y₃ y₄).bondsBetween b b' _ _ _ _ ∅ hbb' hbsym hA hB hB'
      hC hD hE (by simp) (by simp) a c h0' ⟨(hatM a ha).2.1, (hatM a ha).2.2⟩ ⟨(hatM c hc).2.1, (hatM c hc).2.2⟩
    exact Relation.EqvGen.mono (fun p q h => h.2.2) a c this
  · -- no cut vertex
    intro w hw a ha c hc haw hcw
    have h0 := (sc_erase_iff hloop {w} a c).mp (hnocut w (hatM w hw).1 a (hatM a ha).1 c (hatM c hc).1 haw hcw)
    rw [sc_erase_iff hloop1]
    have hW1 : ¬ (M.atom (M.mate y₁) ∈ ({w} : Finset V) ∧ M.atom (M.mate y₂) ∈ ({w} : Finset V)) := by
      rintro ⟨h1, h2⟩; exact huv ((mem_singleton.mp h1).trans (mem_singleton.mp h2).symm)
    have hW2 : ¬ (M.atom (M.mate y₃) ∈ ({w} : Finset V) ∧ M.atom (M.mate y₄) ∈ ({w} : Finset V)) := by
      rintro ⟨h1, h2⟩; exact huv' ((mem_singleton.mp h1).trans (mem_singleton.mp h2).symm)
    exact graph_transfer M.bondsBetween (closureTwo M b b' y₁ y₂ y₃ y₄).bondsBetween b b' _ _ _ _ {w} hbb' hbsym hA hB hB'
      hC hD hE hW1 hW2 a c h0 ⟨(hatM a ha).2.1, (hatM a ha).2.2⟩ ⟨(hatM c hc).2.1, (hatM c hc).2.2⟩

theorem trip_closureTwo (M : Molecule V D) (b b' : V) (y₁ y₂ y₃ y₄ : D) (hle2 : ∀ p q, M.bondsBetween p q ≤ 2)
    (hAt : (closureTwo M b b' y₁ y₂ y₃ y₄).atoms = (M.atoms \ {b}) \ {b'}) :
    (tripSet (closureTwo M b b' y₁ y₂ y₃ y₄)).card ≤ 2 := by
  classical
  have hsub : tripSet (closureTwo M b b' y₁ y₂ y₃ y₄) ⊆
      {s(M.atom (M.mate y₃), M.atom (M.mate y₄)), s(M.atom (M.mate y₁), M.atom (M.mate y₂))} := by
    intro e he
    obtain ⟨p, q, rfl, h3⟩ := tripSet_iff.mp he
    have hpq := bb_pos_mem (N := closureTwo M b b' y₁ y₂ y₃ y₄) (p := p) (q := q) (by omega)
    rw [hAt] at hpq
    obtain ⟨hp, hq⟩ := hpq
    have hp1 := mem_sdiff.mp hp; have hp2 := mem_sdiff.mp hp1.1
    have hq1 := mem_sdiff.mp hq; have hq2 := mem_sdiff.mp hq1.1
    rw [bb_closureTwo M b b' y₁ y₂ y₃ y₄ (by simpa using hp2.2) (by simpa using hp1.2) (by simpa using hq2.2)
      (by simpa using hq1.2)] at h3
    have := hle2 p q
    simp only [mem_insert, mem_singleton]
    by_cases h1 : s(M.atom (M.mate y₃), M.atom (M.mate y₄)) = s(p, q)
    · exact Or.inl h1.symm
    · by_cases h2 : s(M.atom (M.mate y₁), M.atom (M.mate y₂)) = s(p, q)
      · exact Or.inr h2.symm
      · rw [if_neg h1, if_neg h2] at h3; omega
  exact (card_le_card hsub).trans card_le_two

end
end WaveTurbulence.FinalCountG8
