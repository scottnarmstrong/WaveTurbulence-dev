/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.DeriveSandwich
public import WaveTurbulence.Foundations.TVine.Chart.DerivePend
public import WaveTurbulence.Foundations.TVine.Chart.DecompOwn

/-!
# Derivation of the cell decomposition, XVI: the bond budget at an atom, joints, placed cells

* **The budget** (M4 Lemma A + degree 4): at an atom `v` of a piece `C` sandwiched between an input region `Xi` and
  an output region `Xo`, the bonds at `v` are its inner bonds, at most one input bond and at most one output bond.
* The joint embeddings `jointEmb` (the joints have one outgoing and one incoming bond).
* `PCell`: a placed cell (a chart of a table with a local embedding, its input port, and its output ports).
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Chart

open Finset VineParamContract

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {S : Finset V} {a b : V}

theorem bondsBetween_comm (x y : V) : M.bondsBetween x y = M.bondsBetween y x := by
  unfold Molecule.bondsBetween; rw [Sym2.eq_swap]

/-- The bonds at `v` with both ends in `C`. -/
noncomputable def innerAt (C : Finset V) (v : V) : Finset (Bond M S) :=
  (bondsAt v).filter fun e => tl e ∈ C ∧ hd e ∈ C

/-- The bonds of the port of `X` at `v`. -/
noncomputable def portAt (X : Finset V) (v : V) : Finset (Bond M S) :=
  (portSet X).filter fun e => tl e = v ∨ hd e = v

/-- No loop at an interior atom. -/
theorem noLoopAt (hT : M.IsTVine S a b) {v : V} (hva : v ≠ a) (hvb : v ≠ b) :
    ∀ e : Bond M S, tl e = v → hd e ≠ v := by
  intro e h h'
  exact no_loop hT e (h ▸ hva) (h ▸ hvb) (h.trans h'.symm)

/-- **The budget.** -/
theorem budget {C Xi Xo : Finset V} (hio : Xi ⊆ Xo) (hCi : ∀ v ∈ C, v ∉ Xi) (hCo : C ⊆ Xo)
    (hdiff : ∀ v ∈ S, v ∈ Xo → v ∉ Xi → v ∈ C) {v : V} (hv : v ∈ C)
    (hloop : ∀ e : Bond M S, tl e = v → hd e ≠ v) :
    (innerAt (M := M) (S := S) C v).card + (portAt (M := M) (S := S) Xi v).card +
      (portAt (M := M) (S := S) Xo v).card = M.degIn S v := by
  classical
  rw [← card_bondsAt_eq hloop]
  have hvi := hCi v hv
  have hvo := hCo hv
  have hnot : ∀ e : Bond M S, tl e ∈ C → hd e ∈ C → ¬ Crosses Xi e ∧ ¬ Crosses Xo e := by
    intro e h1 h2
    unfold Crosses
    refine ⟨?_, ?_⟩
    · rintro (⟨h, -⟩ | ⟨h, -⟩)
      · exact hCi _ h1 h
      · exact hCi _ h2 h
    · rintro (⟨-, h⟩ | ⟨-, h⟩)
      · exact h (hCo h2)
      · exact h (hCo h1)
  have hIO : ∀ e : Bond M S, (tl e = v ∨ hd e = v) → Crosses Xi e → ¬ Crosses Xo e := by
    intro e he h1 h2
    unfold Crosses at h1 h2
    rcases he with he | he
    · rw [he] at h1 h2
      rcases h1 with ⟨h, -⟩ | ⟨h, -⟩
      · exact hvi h
      · rcases h2 with ⟨-, h'⟩ | ⟨-, h'⟩
        · exact h' (hio h)
        · exact h' hvo
    · rw [he] at h1 h2
      rcases h1 with ⟨h, -⟩ | ⟨h, -⟩
      · rcases h2 with ⟨-, h'⟩ | ⟨-, h'⟩
        · exact h' hvo
        · exact h' (hio h)
      · exact hvi h
  have hd1 : Disjoint (innerAt (M := M) (S := S) C v) (portAt (M := M) (S := S) Xi v) := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    simp only [innerAt, portAt, mem_filter, mem_portSet] at h1 h2
    exact (hnot e h1.2.1 h1.2.2).1 h2.1
  have hd2 : Disjoint (innerAt (M := M) (S := S) C v ∪ portAt (M := M) (S := S) Xi v)
      (portAt (M := M) (S := S) Xo v) := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    simp only [innerAt, portAt, mem_union, mem_filter, mem_portSet] at h1 h2
    rcases h1 with h1 | h1
    · exact (hnot e h1.2.1 h1.2.2).2 h2.1
    · exact hIO e h1.2 h1.1 h2.1
  rw [← card_union_of_disjoint hd1, ← card_union_of_disjoint hd2]
  congr 1
  ext e
  simp only [innerAt, portAt, mem_union, mem_filter, mem_portSet, mem_bondsAt]
  constructor
  · rintro ((⟨h, -⟩ | ⟨-, h⟩) | ⟨-, h⟩) <;> exact h
  · intro he
    rcases sandwich hCi hCo hdiff hv e he with h | h | h
    · exact Or.inl (Or.inl ⟨he, h⟩)
    · exact Or.inl (Or.inr ⟨h, he⟩)
    · exact Or.inr ⟨h, he⟩

/-- A port has at most one bond at an interior atom. -/
theorem portAt_le_one {X : Finset V} (π : Port2 M S X a b) {v : V} (hva : v ≠ a) (hvb : v ≠ b) :
    (portAt (M := M) (S := S) X v).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro e he f hf
  simp only [portAt, mem_filter] at he hf
  exact port_at_most_one π hva hvb he.1 hf.1 he.2 hf.2

/-- An input-side atom with a port bond is an inner end of the port. -/
theorem inEnd_of_pos {X : Finset V} (π : Port2 M S X a b) {v : V} (hvX : v ∉ X)
    (h : 0 < (portAt (M := M) (S := S) X v).card) : hd π.out = v ∨ tl π.inn = v := by
  obtain ⟨e, he⟩ := Finset.card_pos.mp h
  simp only [portAt, mem_filter] at he
  obtain ⟨he, hv⟩ := he
  rw [π.set_eq, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl
  · rcases hv with hv | hv
    · exact absurd (hv ▸ π.out_tl) hvX
    · exact Or.inl hv
  · rcases hv with hv | hv
    · exact Or.inr hv
    · exact absurd (hv ▸ π.inn_hd) hvX

/-- An output-side atom with a port bond is an inner end of the port. -/
theorem outEnd_of_pos {X : Finset V} (π : Port2 M S X a b) {v : V} (hvX : v ∈ X)
    (h : 0 < (portAt (M := M) (S := S) X v).card) : tl π.out = v ∨ hd π.inn = v := by
  obtain ⟨e, he⟩ := Finset.card_pos.mp h
  simp only [portAt, mem_filter] at he
  obtain ⟨he, hv⟩ := he
  rw [π.set_eq, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl
  · rcases hv with hv | hv
    · exact Or.inl hv
    · exact absurd (hv ▸ hvX) π.out_hd
  · rcases hv with hv | hv
    · exact absurd (hv ▸ hvX) π.inn_tl
    · exact Or.inr hv

theorem portAt_pos_out {X : Finset V} (π : Port2 M S X a b) {v : V} (h : tl π.out = v ∨ hd π.out = v) :
    0 < (portAt (M := M) (S := S) X v).card :=
  Finset.card_pos.mpr ⟨π.out, by simp only [portAt, mem_filter]; exact ⟨out_mem π, h⟩⟩

theorem portAt_pos_inn {X : Finset V} (π : Port2 M S X a b) {v : V} (h : tl π.inn = v ∨ hd π.inn = v) :
    0 < (portAt (M := M) (S := S) X v).card :=
  Finset.card_pos.mpr ⟨π.inn, by simp only [portAt, mem_filter]; exact ⟨inn_mem π, h⟩⟩

/-- The inner bonds of an atom of a 2-atom piece. -/
theorem card_innerAt_pair {u w : V} (huw : u ≠ w) (hu : u ∈ S) (hw : w ∈ S)
    (hloop : ∀ e : Bond M S, tl e = u → hd e ≠ u) :
    (innerAt (M := M) (S := S) {u, w} u).card = M.bondsBetween u w := by
  rw [← card_cross_single hu hw]
  congr 1
  ext e
  simp only [innerAt, mem_filter, mem_bondsAt, mem_cross, mem_insert, mem_singleton]
  constructor
  · rintro ⟨h0, h1 | h1, h2 | h2⟩
    · exact absurd h2 (hloop e h1)
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · rcases h0 with h0 | h0
      · exact absurd (h0.symm.trans h1) huw
      · exact absurd (h0.symm.trans h2) huw
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨Or.inl h1, Or.inl h1, Or.inr h2⟩
    · exact ⟨Or.inr h2, Or.inr h1, Or.inl h2⟩

/-- The inner bonds of an atom of a 3-atom piece. -/
theorem card_innerAt_three {x y z : V} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) (hx : x ∈ S) (hy : y ∈ S)
    (hz : z ∈ S) (hloop : ∀ e : Bond M S, tl e = x → hd e ≠ x) :
    (innerAt (M := M) (S := S) {x, y, z} x).card = M.bondsBetween x y + M.bondsBetween x z := by
  rw [← card_cross_single hx hy, ← card_cross_single hx hz, ← card_union_of_disjoint]
  · congr 1
    ext e
    simp only [innerAt, mem_filter, mem_bondsAt, mem_cross, mem_union, mem_insert, mem_singleton]
    constructor
    · rintro ⟨h0, h1 | h1 | h1, h2 | h2 | h2⟩
      · exact absurd h2 (hloop e h1)
      · exact Or.inl (Or.inl ⟨h1, h2⟩)
      · exact Or.inr (Or.inl ⟨h1, h2⟩)
      · exact Or.inl (Or.inr ⟨h1, h2⟩)
      · rcases h0 with h0 | h0
        · exact absurd (h0.symm.trans h1) hxy
        · exact absurd (h0.symm.trans h2) hxy
      · rcases h0 with h0 | h0
        · exact absurd (h0.symm.trans h1) hxy
        · exact absurd (h0.symm.trans h2) hxz
      · exact Or.inr (Or.inr ⟨h1, h2⟩)
      · rcases h0 with h0 | h0
        · exact absurd (h0.symm.trans h1) hxz
        · exact absurd (h0.symm.trans h2) hxy
      · rcases h0 with h0 | h0
        · exact absurd (h0.symm.trans h1) hxz
        · exact absurd (h0.symm.trans h2) hxz
    · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩))
      · exact ⟨Or.inl h1, Or.inl h1, Or.inr (Or.inl h2)⟩
      · exact ⟨Or.inr h2, Or.inr (Or.inl h1), Or.inl h2⟩
      · exact ⟨Or.inl h1, Or.inl h1, Or.inr (Or.inr h2)⟩
      · exact ⟨Or.inr h2, Or.inr (Or.inr h1), Or.inl h2⟩
  · rw [Finset.disjoint_left]
    intro e h1 h2
    simp only [mem_cross, mem_singleton] at h1 h2
    rcases h1 with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;> rcases h2 with ⟨h2, h2'⟩ | ⟨h2, h2'⟩
    · exact hyz (h1'.symm.trans h2')
    · exact hxz (h1.symm.trans h2)
    · exact hxy (h2.symm.trans h1)
    · exact hyz (h1.symm.trans h2)

/-! ## Internal bonds -/

theorem ends_of_cross_single {x y : V} {e : Bond M S} (he : e ∈ cross (M := M) (S := S) {x} {y}) :
    (tl e = x ∧ hd e = y) ∨ (tl e = y ∧ hd e = x) := by
  simpa only [mem_cross, mem_singleton] using he

theorem one_bond {x y : V} (hx : x ∈ S) (hy : y ∈ S) (h : M.bondsBetween x y = 1) :
    ∃ d : Bond M S, (tl d = x ∧ hd d = y) ∨ (tl d = y ∧ hd d = x) := by
  rw [← card_cross_single hx hy] at h
  obtain ⟨d, hd⟩ := Finset.card_eq_one.mp h
  exact ⟨d, ends_of_cross_single (by rw [hd]; exact mem_singleton_self d)⟩

theorem two_bonds {x y : V} (hx : x ∈ S) (hy : y ∈ S) (h : M.bondsBetween x y = 2) :
    ∃ d₀ d₁ : Bond M S, d₀ ≠ d₁ ∧ ((tl d₀ = x ∧ hd d₀ = y) ∨ (tl d₀ = y ∧ hd d₀ = x)) ∧
      ((tl d₁ = x ∧ hd d₁ = y) ∨ (tl d₁ = y ∧ hd d₁ = x)) := by
  rw [← card_cross_single hx hy] at h
  obtain ⟨d₀, d₁, hne, hd⟩ := Finset.card_eq_two.mp h
  exact ⟨d₀, d₁, hne, ends_of_cross_single (by rw [hd]; simp), ends_of_cross_single (by rw [hd]; simp)⟩

/-! ## Port ends -/

theorem inEnds_of {X : Finset V} (π : Port2 M S X a b) {u w : V} (hua : u ≠ a) (hub : u ≠ b) (hwa : w ≠ a)
    (hwb : w ≠ b) (h1 : hd π.out = u ∨ hd π.out = w) (h2 : tl π.inn = u ∨ tl π.inn = w) : InEnds π u w := by
  unfold InEnds
  have hd : ∀ v, v ≠ a → v ≠ b → hd π.out = v → tl π.inn = v → False :=
    fun v hva hvb e1 e2 => π.distinct v hva hvb ⟨Or.inr e1, Or.inl e2⟩
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd h2 (fun h => hd u hua hub h1 h)
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd h2 (fun h => hd w hwa hwb h1 h)

theorem outEnds_of {X : Finset V} (π : Port2 M S X a b) {u w : V} (hua : u ≠ a) (hub : u ≠ b) (hwa : w ≠ a)
    (hwb : w ≠ b) (h1 : tl π.out = u ∨ tl π.out = w) (h2 : hd π.inn = u ∨ hd π.inn = w) : OutEnds π u w := by
  unfold OutEnds
  have hd : ∀ v, v ≠ a → v ≠ b → tl π.out = v → hd π.inn = v → False :=
    fun v hva hvb e1 e2 => π.distinct v hva hvb ⟨Or.inl e1, Or.inr e2⟩
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd h2 (fun h => hd u hua hub h1 h)
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd h2 (fun h => hd w hwa hwb h1 h)

theorem port2_out_eq' {X Y : Finset V} (h : X = Y) (π : Port2 M S X a b) (π' : Port2 M S Y a b) :
    π.out = π'.out := by subst h; exact port2_out_eq π π'

theorem port2_inn_eq' {X Y : Finset V} (h : X = Y) (π : Port2 M S X a b) (π' : Port2 M S Y a b) :
    π.inn = π'.inn := by subst h; exact port2_inn_eq π π'

/-! ## Joints -/

/-- **The embedding of a joint**: its outgoing bond `e₀` and its incoming bond `e₁`. -/
noncomputable def jointEmb (v : V) (e₀ e₁ : Bond M S) (h0t : tl e₀ = v) (h0h : hd e₀ ≠ v) (h1h : hd e₁ = v)
    (h1t : tl e₁ ≠ v) (hdeg : M.degIn S v ≤ 2) : LocEmb jointGraph M S where
  atom := ![v]
  bond := ![e₀, e₁]
  atom_inj := fun i j _ => Subsingleton.elim i j
  bond_inj := by
    have hne : e₀ ≠ e₁ := fun h => h1t (h ▸ h0t)
    intro i j h
    fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> first | exact hne h | exact hne h.symm
  tl_eq := by
    intro l u h
    fin_cases l <;> fin_cases u <;> simp at h ⊢
    exact h0t
  tl_out := by
    intro l h u
    fin_cases l <;> fin_cases u <;> simp at h ⊢
    exact h1t
  hd_eq := by
    intro l u h
    fin_cases l <;> fin_cases u <;> simp at h ⊢
    exact h1h
  hd_out := by
    intro l h u
    fin_cases l <;> fin_cases u <;> simp at h ⊢
    exact h0h
  complete := by
    intro u e he
    have hne : e₀ ≠ e₁ := fun h => h1t (h ▸ h0t)
    have hsub : ({e₀, e₁} : Finset (Bond M S)) ⊆ bondsAt v := by
      intro f hf
      rw [mem_insert, mem_singleton] at hf
      rcases hf with rfl | rfl
      · exact mem_bondsAt.mpr (Or.inl h0t)
      · exact mem_bondsAt.mpr (Or.inr h1h)
    have heq := bondsAt_eq_of_card _ hsub (by rw [card_pair hne]; exact hdeg)
    have hmem : e ∈ bondsAt (M := M) (S := S) v := by
      fin_cases u; exact mem_bondsAt.mpr he
    rw [← heq, mem_insert, mem_singleton] at hmem
    rcases hmem with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

theorem jointEmb_atom (v : V) (e₀ e₁ : Bond M S) (h0t h0h h1h h1t hdeg) :
    (jointEmb v e₀ e₁ h0t h0h h1h h1t hdeg).atom 0 = v := rfl

theorem jointEmb_bond0 (v : V) (e₀ e₁ : Bond M S) (h0t h0h h1h h1t hdeg) :
    (jointEmb v e₀ e₁ h0t h0h h1h h1t hdeg).bond 0 = e₀ := rfl

theorem jointEmb_bond1 (v : V) (e₀ e₁ : Bond M S) (h0t h0h h1h h1t hdeg) :
    (jointEmb v e₀ e₁ h0t h0h h1h h1t hdeg).bond 1 = e₁ := rfl

/-! ## Placed cells -/

/-- **A placed cell**: a chart with a local embedding whose atoms are `P`, whose input pair is the port of `Xin`, whose
exit (resp. pendant) pair is the port of `XoM` (resp. `XoB`), with label offsets `rin`, `rM`. -/
structure PCell (M : Molecule V D) (S : Finset V) (a b : V) (nA nC : ℕ) (Q : (nB : ℕ) → LocalChart nA nC nB → Prop)
    (P Xin : Finset V) (XoM XoB : Option (Finset V)) (rin rM : ℤ) (nB : ℕ) where
  cfg : LocalChart nA nC nB
  emb : LocEmb cfg.graph M S
  valid : cfg.Valid
  ok : Q nB cfg
  rel : cfg.Rel rin rM 0
  extra : ∀ x, emb.bond (cfg.X₁ x) ≠ emb.bond (cfg.X₂ x) ∧
    ∃ Y ⊆ S, ∀ e, Crosses Y e ↔ e = emb.bond (cfg.X₁ x) ∨ e = emb.bond (cfg.X₂ x)
  atoms : ∀ v, v ∈ P ↔ ∃ u, emb.atom u = v
  pin : Port2 M S Xin a b
  bO : emb.bond cfg.eO = pin.out
  bI : emb.bond cfg.eI = pin.inn
  oM : ∀ X, XoM = some X → ∀ pt : Port2 M S X a b,
    ∃ p, cfg.outM = some p ∧ emb.bond p.1 = pt.out ∧ emb.bond p.2 = pt.inn
  oB : ∀ X, XoB = some X → ∀ pt : Port2 M S X a b,
    ∃ p, cfg.outB = some p ∧ emb.bond p.1 = pt.out ∧ emb.bond p.2 = pt.inn

theorem outB_none_of {nA nC nB : ℕ} (P : PShape nA nB) {c : LocalChart nA nC nB} (h : P.RoleCompat c)
    (hP : ∀ l, P.role l ≠ .exB) : c.outB = none := by
  obtain ⟨-, -, -, -, -, h⟩ := h
  revert h
  cases c.outB with
  | none => intro _; rfl
  | some p => obtain ⟨o, i⟩ := p; intro h; exact absurd h.1 (hP o)

theorem extra_none {nA nC nB : ℕ} {c : LocalChart nA nC nB} (hE : c.ExtrasOK) (hB : c.outB = none)
    (x : Fin c.nX) : False := by
  rcases hE x with h | h <;> rw [hB] at h <;> simp at h

theorem extra_some {nA nC nB : ℕ} {c : LocalChart nA nC nB} (φ : LocEmb c.graph M S) {X : Finset V} (hX : X ⊆ S)
    (pt : Port2 M S X a b) (hE : c.ExtrasOK) {p : Fin nB × Fin nB} (hB : c.outB = some p)
    (h1 : φ.bond p.1 = pt.out) (h2 : φ.bond p.2 = pt.inn) (x : Fin c.nX) :
    φ.bond (c.X₁ x) ≠ φ.bond (c.X₂ x) ∧
      ∃ Y ⊆ S, ∀ e, Crosses Y e ↔ e = φ.bond (c.X₁ x) ∨ e = φ.bond (c.X₂ x) := by
  have hc : ∀ e, Crosses X e ↔ e = pt.out ∨ e = pt.inn := fun e => by
    rw [← mem_portSet, pt.set_eq]; simp
  rcases hE x with h | h <;> rw [hB, Option.some_inj] at h <;> rw [← h] at h1 h2 <;> dsimp only at h1 h2
  · refine ⟨by rw [h1, h2]; exact pt.ne, X, hX, fun e => by rw [hc, h1, h2]⟩
  · refine ⟨by rw [h1, h2]; exact pt.ne.symm, X, hX, fun e => by rw [hc, h1, h2, or_comm]⟩

/-- **Wiring two placed cells**: the input of `C` is the `w`-output of `C'`. -/
theorem PCell.wire {nA nC nA' nC' nB nB' : ℕ} {Q : (nB : ℕ) → LocalChart nA nC nB → Prop}
    {Q' : (nB : ℕ) → LocalChart nA' nC' nB → Prop} {P P' X X' : Finset V} {XoM XoB XoM' XoB' : Option (Finset V)}
    {rin rM rin' rM' : ℤ} (C : PCell M S a b nA nC Q P X XoM XoB rin rM nB)
    (C' : PCell M S a b nA' nC' Q' P' X' XoM' XoB' rin' rM' nB') (w : Bool)
    (h : (if w then XoB' else XoM') = some X) (hr : rin = if w then 0 else rM') :
    ∃ p, outPair C'.cfg w = some p ∧ C.emb.bond C.cfg.eO = C'.emb.bond p.1 ∧
      C.emb.bond C.cfg.eI = C'.emb.bond p.2 ∧ C.cfg.locR C.cfg.eO = C'.cfg.locR p.1 - C'.cfg.locR p.2 := by
  cases w with
  | false =>
    obtain ⟨p, hp, h1, h2⟩ := C'.oM X h C.pin
    refine ⟨p, hp, by rw [C.bO, h1], by rw [C.bI, h2], ?_⟩
    rw [C.rel.1, C'.rel.2.1 p (by rw [hp]; rfl)]
    exact hr
  | true =>
    obtain ⟨p, hp, h1, h2⟩ := C'.oB X h C.pin
    refine ⟨p, hp, by rw [C.bO, h1], by rw [C.bI, h2], ?_⟩
    rw [C.rel.1, C'.rel.2.2 p (by rw [hp]; rfl)]
    exact hr

end WaveTurbulence.TVine.Chart
