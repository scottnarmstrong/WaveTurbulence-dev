/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.FinalCount.Count.C6Shape
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Count.C6Struct
public import WaveTurbulence.Foundations.FinalCount.G8R.MergeGraph
public import WaveTurbulence.Foundations.FinalCount.G8R.ThmA
import Mathlib.Tactic

/-! # Case (6d): the theta chains of `𝕄₀` and the charges (packet L6-COUNT, Case6TopLow; M2 §4.10)

* `thetaGenData_double`: a chain `C` (two exits ending at `p ≠ q`) with `p = q` a double bond gives the theta chain
  `S = {p, q} ∪ C` (`C' = ∅`; M2 Lemma 4.3 after operation (d) on `C`).
* `thetaGenData_single`: two singleton chains `{r}`, `{r'}` between `p` and `q` with one bond `p – q` give the
  generalized theta chain `S = {p, q, r, r'}` (`C = {r}`, `C' = {r'}`).
* `ThetaGenData.erase`: the data pass to the molecule after operation (c) (`eraseAtoms 𝕄₀ K₁`, `S ∩ K₁ = ∅`).
* `charge_sum_zero`, `charge_deg2`, `chain_charge`: for a decoration, `∑_v c_v = 0`; a degree-two atom with darts
  `out`, `in` has `c = k_out − k_in`; a chain with exits `y₁, y₂` has `k_{mate y₁} − k_{mate y₂} = ± ∑_C c`. -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.GammaLow.FinalCount.Count
open WaveTurbulence.MoleProp4 WaveTurbulence.FinalCountG8

section
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The two darts of a double bond `p = q` at `p`. -/
theorem darts_double {M : Molecule V D} {p q : V} (hpq : p ≠ q) (hbb : M.bondsBetween p q = 2) :
    ∃ a b, a ≠ b ∧ M.atom a = p ∧ M.atom (M.mate a) = q ∧ M.atom b = p ∧ M.atom (M.mate b) = q ∧
      ∀ z, M.atom z = p → M.atom (M.mate z) = q → z = a ∨ z = b := by
  classical
  obtain ⟨a, b, hab, he⟩ := card_eq_two.mp ((card_darts_between M hpq).trans hbb)
  have ha : a ∈ univ.filter fun x => M.atom x = p ∧ M.atom (M.mate x) = q := by rw [he]; simp
  have hb : b ∈ univ.filter fun x => M.atom x = p ∧ M.atom (M.mate x) = q := by rw [he]; simp
  obtain ⟨_, ha1, ha2⟩ := mem_filter.mp ha
  obtain ⟨_, hb1, hb2⟩ := mem_filter.mp hb
  refine ⟨a, b, hab, ha1, ha2, hb1, hb2, fun z hz1 hz2 => ?_⟩
  have : z ∈ univ.filter fun x => M.atom x = p ∧ M.atom (M.mate x) = q := mem_filter.mpr ⟨mem_univ _, hz1, hz2⟩
  rw [he] at this; simpa using this

/-- The dart of a single bond `p – q` at `p`. -/
theorem dart_single {M : Molecule V D} {p q : V} (hpq : p ≠ q) (hbb : M.bondsBetween p q = 1) :
    ∃ a, M.atom a = p ∧ M.atom (M.mate a) = q ∧ ∀ z, M.atom z = p → M.atom (M.mate z) = q → z = a := by
  classical
  obtain ⟨a, he⟩ := card_eq_one.mp ((card_darts_between M hpq).trans hbb)
  have ha : a ∈ univ.filter fun x => M.atom x = p ∧ M.atom (M.mate x) = q := by rw [he]; simp
  obtain ⟨_, ha1, ha2⟩ := mem_filter.mp ha
  refine ⟨a, ha1, ha2, fun z hz1 hz2 => ?_⟩
  have : z ∈ univ.filter fun x => M.atom x = p ∧ M.atom (M.mate x) = q := mem_filter.mpr ⟨mem_univ _, hz1, hz2⟩
  rw [he] at this; simpa using this

/-- A dart entering a chain `C` from outside is the mate of one of its two exits. -/
theorem enter_chain {M : Molecule V D} {C : Finset V} {y₁ y₂ : D} (hcross : crossDarts M C = {y₁, y₂})
    {z : D} (hz : M.atom z ∉ C) (hmz : M.atom (M.mate z) ∈ C) : z = M.mate y₁ ∨ z = M.mate y₂ := by
  have : M.mate z ∈ crossDarts M C := mem_crossDarts.mpr ⟨hmz, by rw [M.mate_mate]; exact hz⟩
  rw [hcross] at this
  rcases mem_insert.mp this with e | e
  · left; rw [← e, M.mate_mate]
  · right; rw [← mem_singleton.mp e, M.mate_mate]

/-- No three equal directions among three distinct darts at an atom with in/out caps two. -/
theorem not_three_equal {M : Molecule V D} {p : V} (hcap : M.outdeg p ≤ 2 ∧ M.indeg p ≤ 2) {x y z : D}
    (hx : M.atom x = p) (hy : M.atom y = p) (hz : M.atom z = p) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ¬ (M.out x = M.out y ∧ M.out y = M.out z) := by
  classical
  rintro ⟨h1, h2⟩
  have hsub : ({x, y, z} : Finset D) ⊆ (M.dartsAt p).filter fun w => M.out w = M.out x := by
    intro w hw
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact mem_filter.mpr ⟨(Mole.mem_dartsAt M p _).mpr hx, rfl⟩
    · exact mem_filter.mpr ⟨(Mole.mem_dartsAt M p _).mpr hy, h1.symm⟩
    · exact mem_filter.mpr ⟨(Mole.mem_dartsAt M p _).mpr hz, (h1.trans h2).symm⟩
  have h3 : ({x, y, z} : Finset D).card = 3 := by
    rw [card_insert_of_notMem (by simp [hxy, hxz]), card_pair hyz]
  have hle := card_le_card hsub
  cases ho : M.out x
  · have : ((M.dartsAt p).filter fun w => M.out w = M.out x).card = M.indeg p := by
      rw [ho]; rfl
    omega
  · have : ((M.dartsAt p).filter fun w => M.out w = M.out x).card = M.outdeg p := by
      rw [ho]; rfl
    omega

/-- **The theta chain of a doubly bonded chain** (M2 Lemma 4.3, `C' = ∅`). -/
theorem thetaGenData_double {M : Molecule V D} (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z))
    (hcap : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2) {C : Finset V} {p q : V} {y₁ y₂ : D}
    (hCA : C ⊆ M.atoms) (hp : p ∈ M.atoms) (hq : q ∈ M.atoms) (hpC : p ∉ C) (hqC : q ∉ C) (hpq : p ≠ q)
    (hcross : crossDarts M C = {y₁, y₂}) (hp1 : M.atom (M.mate y₁) = p) (hq2 : M.atom (M.mate y₂) = q)
    (hch : ∀ v ∈ C, M.outdeg v = 1 ∧ M.indeg v = 1) (hdir : M.out y₁ ≠ M.out y₂)
    (hconn : ∀ u ∈ C, ∀ v ∈ C, (piece M C).SameComponent u v) (hbb : M.bondsBetween p q = 2) :
    ∃ a b, ThetaGenData M (insert p (insert q C)) p q a b (M.mate y₁) (M.mate y₂) C ∅ := by
  classical
  obtain ⟨a, b, hab, ha, hma, hb, hmb, hpq2⟩ := darts_double hpq hbb
  have hy1C : M.atom y₁ ∈ C := (mem_crossDarts.mp (by rw [hcross]; simp : y₁ ∈ crossDarts M C)).1
  have hy2C : M.atom y₂ ∈ C := (mem_crossDarts.mp (by rw [hcross]; simp : y₂ ∈ crossDarts M C)).1
  have hz₁ : M.atom (M.mate (M.mate y₁)) ∈ C := by rw [M.mate_mate]; exact hy1C
  have hz₂ : M.atom (M.mate (M.mate y₂)) ∈ C := by rw [M.mate_mate]; exact hy2C
  have haz : a ≠ M.mate y₁ := fun e => hqC (by rw [← hma, e]; exact hz₁)
  have hbz : b ≠ M.mate y₁ := fun e => hqC (by rw [← hmb, e]; exact hz₁)
  set S := insert p (insert q C) with hSdef
  have hmemS : ∀ v, v ∈ S ↔ v = p ∨ v = q ∨ v ∈ C := by intro v; simp [hSdef]
  refine ⟨a, b, ?_⟩
  refine
    { sub := fun v hv => by
        rcases (hmemS v).mp hv with rfl | rfl | hv
        · exact hp
        · exact hq
        · exact hCA hv
      hS := by rw [union_empty]
      hpq := hpq
      hpC := by simpa using hpC
      hqC := by simpa using hqC
      disj := disjoint_empty_right _
      ha := ha
      hb := hb
      hz₁ := hp1
      hz₂ := hq2
      hma := hma
      hmb := Or.inl ⟨rfl, hmb⟩
      hab := hab
      hmz₁ := hz₁
      hmz₂ := hz₂
      pin := ?_
      qdeg := ?_
      signs := not_three_equal (hcap p hp) ha hb hp1 hab haz hbz
      dir := by rw [M.out_mate, M.out_mate]; intro e; exact hdir (by simpa using e)
      closed := ?_
      chain := fun v hv => hch v (by simpa using hv)
      crossC := ?_
      connC := hconn
      connC' := fun u hu => by simp at hu
      noLoop := hloop }
  · intro z hz hmS
    rcases (hmemS _).mp hmS with e | e | e
    · exact absurd (hz.trans e.symm) (hloop z)
    · rcases hpq2 z hz e with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · rcases enter_chain hcross (by rw [hz]; exact hpC) e with e2 | e2
      · exact Or.inr (Or.inr e2)
      · exfalso; apply hpq; rw [← hz, e2, hq2]
  · have hfilt : (univ.filter fun z => M.atom z = q ∧ M.atom (M.mate z) ∈ S) = {M.mate a, M.mate b, M.mate y₂} := by
      ext z
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hz, hmS⟩
        rcases (hmemS _).mp hmS with e | e | e
        · rcases hpq2 (M.mate z) e (by rw [M.mate_mate]; exact hz) with e2 | e2
          · left; rw [← e2, M.mate_mate]
          · right; left; rw [← e2, M.mate_mate]
        · exact absurd (hz.trans e.symm) (hloop z)
        · rcases enter_chain hcross (by rw [hz]; exact hqC) e with e2 | e2
          · exfalso; apply hpq; rw [← hp1, ← e2, hz]
          · right; right; exact e2
      · rintro (rfl | rfl | rfl)
        · exact ⟨hma, by rw [M.mate_mate, ha]; exact (hmemS p).mpr (Or.inl rfl)⟩
        · exact ⟨hmb, by rw [M.mate_mate, hb]; exact (hmemS p).mpr (Or.inl rfl)⟩
        · exact ⟨hq2, (hmemS _).mpr (Or.inr (Or.inr hz₂))⟩
    rw [hfilt]
    have h1 : M.mate a ≠ M.mate b := fun e => hab (by
      have := congrArg M.mate e; rwa [M.mate_mate, M.mate_mate] at this)
    have h2 : M.mate a ≠ M.mate y₂ := fun e => hpC (by
      have := congrArg (fun x => M.atom (M.mate x)) e
      simp only [M.mate_mate] at this; rw [← ha, this]; exact hy2C)
    have h3 : M.mate b ≠ M.mate y₂ := fun e => hpC (by
      have := congrArg (fun x => M.atom (M.mate x)) e
      simp only [M.mate_mate] at this; rw [← hb, this]; exact hy2C)
    rw [card_insert_of_notMem (by simp [h1, h2]), card_pair h3]
  · intro z hz
    have hz' : M.atom z ∈ C := by simpa using hz
    by_cases hmC : M.atom (M.mate z) ∈ C
    · exact (hmemS _).mpr (Or.inr (Or.inr hmC))
    · have : z ∈ crossDarts M C := mem_crossDarts.mpr ⟨hz', hmC⟩
      rw [hcross] at this
      rcases mem_insert.mp this with rfl | e
      · rw [hp1]; exact (hmemS p).mpr (Or.inl rfl)
      · rw [mem_singleton.mp e, hq2]; exact (hmemS q).mpr (Or.inr (Or.inl rfl))
  · intro z hz hmz
    have : z ∈ crossDarts M C := mem_crossDarts.mpr ⟨hz, hmz⟩
    rw [hcross] at this
    rcases mem_insert.mp this with rfl | e
    · left; rw [M.mate_mate]
    · right; rw [mem_singleton.mp e, M.mate_mate]

/-- **The generalized theta chain of two singleton chains between `p` and `q` with one bond `p – q`.** -/
theorem thetaGenData_single {M : Molecule V D} (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z))
    (hcap : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2) {r r' p q : V} {y₁ y₂ y₃ y₄ : D}
    (hr : r ∈ M.atoms) (hr' : r' ∈ M.atoms) (hp : p ∈ M.atoms) (hq : q ∈ M.atoms) (hrr : r ≠ r')
    (hpr : p ≠ r) (hpr' : p ≠ r') (hqr : q ≠ r) (hqr' : q ≠ r') (hpq : p ≠ q)
    (hc1 : crossDarts M {r} = {y₁, y₂}) (hp1 : M.atom (M.mate y₁) = p) (hq2 : M.atom (M.mate y₂) = q)
    (hc2 : crossDarts M {r'} = {y₃, y₄}) (hp3 : M.atom (M.mate y₃) = p) (hq4 : M.atom (M.mate y₄) = q)
    (hdr : M.outdeg r = 1 ∧ M.indeg r = 1) (hdr' : M.outdeg r' = 1 ∧ M.indeg r' = 1)
    (hdir : M.out y₁ ≠ M.out y₂) (hbb : M.bondsBetween p q = 1) :
    ∃ a, ThetaGenData M (insert p (insert q ({r} ∪ {r'}))) p q a (M.mate y₃) (M.mate y₁) (M.mate y₂) {r} {r'} := by
  classical
  obtain ⟨a, ha, hma, hpq1⟩ := dart_single hpq hbb
  have hy1 : M.atom y₁ = r := mem_singleton.mp (mem_crossDarts.mp (by rw [hc1]; simp : y₁ ∈ crossDarts M {r})).1
  have hy2 : M.atom y₂ = r := mem_singleton.mp (mem_crossDarts.mp (by rw [hc1]; simp : y₂ ∈ crossDarts M {r})).1
  have hy3 : M.atom y₃ = r' := mem_singleton.mp (mem_crossDarts.mp (by rw [hc2]; simp : y₃ ∈ crossDarts M {r'})).1
  have hy4 : M.atom y₄ = r' := mem_singleton.mp (mem_crossDarts.mp (by rw [hc2]; simp : y₄ ∈ crossDarts M {r'})).1
  set S : Finset V := insert p (insert q ({r} ∪ {r'})) with hSdef
  have hmemS : ∀ v, v ∈ S ↔ v = p ∨ v = q ∨ v = r ∨ v = r' := by intro v; simp [hSdef]
  have hab : a ≠ M.mate y₃ := fun e => hqr' (by rw [← hma, e, M.mate_mate, hy3])
  have haz : a ≠ M.mate y₁ := fun e => hqr (by rw [← hma, e, M.mate_mate, hy1])
  have hbz : M.mate y₃ ≠ M.mate y₁ := fun e => hrr (by
    have := congrArg (fun x => M.atom (M.mate x)) e; simp only [M.mate_mate] at this; rw [← hy1, ← hy3, this])
  refine ⟨a, ?_⟩
  refine
    { sub := fun v hv => by
        rcases (hmemS v).mp hv with rfl | rfl | rfl | rfl
        · exact hp
        · exact hq
        · exact hr
        · exact hr'
      hS := rfl
      hpq := hpq
      hpC := by simp [hpr, hpr']
      hqC := by simp [hqr, hqr']
      disj := by simpa using hrr
      ha := ha
      hb := hp3
      hz₁ := hp1
      hz₂ := hq2
      hma := hma
      hmb := Or.inr (by rw [M.mate_mate, hy3]; exact mem_singleton_self _)
      hab := hab
      hmz₁ := by rw [M.mate_mate, hy1]; exact mem_singleton_self _
      hmz₂ := by rw [M.mate_mate, hy2]; exact mem_singleton_self _
      pin := ?_
      qdeg := ?_
      signs := not_three_equal (hcap p hp) ha hp3 hp1 hab haz hbz
      dir := by rw [M.out_mate, M.out_mate]; intro e; exact hdir (by simpa using e)
      closed := ?_
      chain := ?_
      crossC := ?_
      connC := fun u hu v hv => by rw [mem_singleton.mp hu, mem_singleton.mp hv]; exact Relation.EqvGen.refl _
      connC' := fun u hu v hv => by rw [mem_singleton.mp hu, mem_singleton.mp hv]; exact Relation.EqvGen.refl _
      noLoop := hloop }
  · intro z hz hmS
    rcases (hmemS _).mp hmS with e | e | e | e
    · exact absurd (hz.trans e.symm) (hloop z)
    · exact Or.inl (hpq1 z hz e)
    · rcases enter_chain hc1 (by rw [hz]; simpa using hpr) (by rw [e]; exact mem_singleton_self _) with e2 | e2
      · exact Or.inr (Or.inr e2)
      · exfalso; apply hpq; rw [← hz, e2, hq2]
    · rcases enter_chain hc2 (by rw [hz]; simpa using hpr') (by rw [e]; exact mem_singleton_self _) with e2 | e2
      · exact Or.inr (Or.inl e2)
      · exfalso; apply hpq; rw [← hz, e2, hq4]
  · have hfilt : (univ.filter fun z => M.atom z = q ∧ M.atom (M.mate z) ∈ S) =
        {M.mate a, M.mate y₄, M.mate y₂} := by
      ext z
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hz, hmS⟩
        rcases (hmemS _).mp hmS with e | e | e | e
        · have := hpq1 (M.mate z) e (by rw [M.mate_mate]; exact hz)
          left; rw [← this, M.mate_mate]
        · exact absurd (hz.trans e.symm) (hloop z)
        · rcases enter_chain hc1 (by rw [hz]; simpa using hqr) (by rw [e]; exact mem_singleton_self _) with e2 | e2
          · exfalso; apply hpq; rw [← hp1, ← e2, hz]
          · right; right; exact e2
        · rcases enter_chain hc2 (by rw [hz]; simpa using hqr') (by rw [e]; exact mem_singleton_self _) with e2 | e2
          · exfalso; apply hpq; rw [← hp3, ← e2, hz]
          · right; left; exact e2
      · rintro (rfl | rfl | rfl)
        · exact ⟨hma, by rw [M.mate_mate, ha]; exact (hmemS p).mpr (Or.inl rfl)⟩
        · exact ⟨hq4, by rw [M.mate_mate, hy4]; exact (hmemS r').mpr (Or.inr (Or.inr (Or.inr rfl)))⟩
        · exact ⟨hq2, by rw [M.mate_mate, hy2]; exact (hmemS r).mpr (Or.inr (Or.inr (Or.inl rfl)))⟩
    rw [hfilt]
    have hpa : M.atom (M.mate (M.mate a)) = p := by rw [M.mate_mate]; exact ha
    have hp4 : M.atom (M.mate (M.mate y₄)) = r' := by rw [M.mate_mate]; exact hy4
    have hp2 : M.atom (M.mate (M.mate y₂)) = r := by rw [M.mate_mate]; exact hy2
    have h1 : M.mate a ≠ M.mate y₄ := fun e => hpr' (by rw [← hpa, e, hp4])
    have h2 : M.mate a ≠ M.mate y₂ := fun e => hpr (by rw [← hpa, e, hp2])
    have h3 : M.mate y₄ ≠ M.mate y₂ := fun e => hrr (by rw [← hp2, ← e, hp4])
    rw [card_insert_of_notMem (by simp [h1, h2]), card_pair h3]
  · intro z hz
    have hz' : M.atom z = r ∨ M.atom z = r' := by simpa using hz
    rcases hz' with hz' | hz'
    · by_cases hm : M.atom (M.mate z) = r
      · exact absurd (hz'.trans hm.symm) (hloop z)
      · have : z ∈ crossDarts M {r} := mem_crossDarts.mpr ⟨by rw [hz']; exact mem_singleton_self _, by simpa using hm⟩
        rw [hc1] at this
        rcases mem_insert.mp this with rfl | e
        · rw [hp1]; exact (hmemS p).mpr (Or.inl rfl)
        · rw [mem_singleton.mp e, hq2]; exact (hmemS q).mpr (Or.inr (Or.inl rfl))
    · by_cases hm : M.atom (M.mate z) = r'
      · exact absurd (hz'.trans hm.symm) (hloop z)
      · have : z ∈ crossDarts M {r'} := mem_crossDarts.mpr ⟨by rw [hz']; exact mem_singleton_self _, by simpa using hm⟩
        rw [hc2] at this
        rcases mem_insert.mp this with rfl | e
        · rw [hp3]; exact (hmemS p).mpr (Or.inl rfl)
        · rw [mem_singleton.mp e, hq4]; exact (hmemS q).mpr (Or.inr (Or.inl rfl))
  · intro v hv
    have hv' : v = r ∨ v = r' := by simpa using hv
    rcases hv' with rfl | rfl
    · exact hdr
    · exact hdr'
  · intro z hz hmz
    have : z ∈ crossDarts M {r} := mem_crossDarts.mpr ⟨hz, hmz⟩
    rw [hc1] at this
    rcases mem_insert.mp this with rfl | e
    · left; rw [M.mate_mate]
    · right; rw [mem_singleton.mp e, M.mate_mate]

/-- Connectivity of `𝕄[C]` passes to `(𝕄 ∖ K)[C]` when `C ∩ K = ∅`. -/
theorem sameComponent_piece_erase {M : Molecule V D} {K C : Finset V} (hCK : Disjoint C K) {u v : V}
    (h : (piece M C).SameComponent u v) : (piece (Degen.eraseAtoms M K) C).SameComponent u v := by
  induction h with
  | rel x y hxy =>
    obtain ⟨z, rfl, rfl⟩ := hxy
    have hm := piece_dart_mem z
    let z₁ : Degen.RetainedDart M K := ⟨z.val, disjoint_left.mp hCK hm.1, disjoint_left.mp hCK hm.2⟩
    have h2 : (Degen.eraseAtoms M K).atom z₁ ∈ C ∧
        (Degen.eraseAtoms M K).atom ((Degen.eraseAtoms M K).mate z₁) ∈ C := hm
    exact Relation.EqvGen.rel _ _ ⟨pieceDart (Degen.eraseAtoms M K) C z₁ h2, rfl, rfl⟩
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

namespace ThetaGenData
variable {M : Molecule V D} {S : Finset V} {p q : V} {a b z₁ z₂ : D} {C C' : Finset V}
  (h : ThetaGenData M S p q a b z₁ z₂ C C')
include h

theorem retained (K : Finset V) (hSK : Disjoint S K) {z : D} (hz : M.atom z ∈ S) (hmz : M.atom (M.mate z) ∈ S) :
    M.atom z ∉ K ∧ M.atom (M.mate z) ∉ K := ⟨disjoint_left.mp hSK hz, disjoint_left.mp hSK hmz⟩

/-- **The theta data pass to `𝕄 ∖ K` when `S ∩ K = ∅`.** -/
theorem erase (K : Finset V) (hSK : Disjoint S K) :
    ThetaGenData (Degen.eraseAtoms M K) S p q ⟨a, h.retained K hSK h.haS.1 h.haS.2⟩
      ⟨b, h.retained K hSK h.hbS.1 h.hbS.2⟩ ⟨z₁, h.retained K hSK h.hz₁S.1 h.hz₁S.2⟩
      ⟨z₂, h.retained K hSK h.hz₂S.1 h.hz₂S.2⟩ C C' := by
  classical
  have hCS : ∀ v ∈ C ∪ C', v ∈ S := fun v hv => h.C_mem hv
  refine
    { sub := fun v hv => mem_sdiff.mpr ⟨h.sub hv, disjoint_left.mp hSK hv⟩
      hS := h.hS
      hpq := h.hpq
      hpC := h.hpC
      hqC := h.hqC
      disj := h.disj
      ha := h.ha
      hb := h.hb
      hz₁ := h.hz₁
      hz₂ := h.hz₂
      hma := h.hma
      hmb := h.hmb
      hab := fun e => h.hab (congrArg Subtype.val e)
      hmz₁ := h.hmz₁
      hmz₂ := h.hmz₂
      pin := fun z hz hm => by
        rcases h.pin z.val hz hm with e | e | e
        · exact Or.inl (Subtype.ext e)
        · exact Or.inr (Or.inl (Subtype.ext e))
        · exact Or.inr (Or.inr (Subtype.ext e))
      qdeg := ?_
      signs := h.signs
      dir := h.dir
      closed := fun z hz => h.closed z.val hz
      chain := ?_
      crossC := fun z hz hmz => by
        rcases h.crossC z.val hz hmz with e | e
        · exact Or.inl (Subtype.ext e)
        · exact Or.inr (Subtype.ext e)
      connC := fun u hu v hv => sameComponent_piece_erase
        (disjoint_left.mpr fun x hx hxK => disjoint_left.mp hSK (hCS x (mem_union_left _ hx)) hxK) (h.connC u hu v hv)
      connC' := fun u hu v hv => sameComponent_piece_erase
        (disjoint_left.mpr fun x hx hxK => disjoint_left.mp hSK (hCS x (mem_union_right _ hx)) hxK) (h.connC' u hu v hv)
      noLoop := fun x => h.noLoop x.val }
  · rw [← h.qdeg]
    refine card_bij (fun x _ => x.val) ?_ (fun x _ y _ e => Subtype.ext e) ?_
    · intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx ⊢
      exact hx
    · intro z hz
      simp only [mem_filter, mem_univ, true_and] at hz
      refine ⟨⟨z, h.retained K hSK (hz.1 ▸ h.q_mem) hz.2⟩, ?_, rfl⟩
      simp only [mem_filter, mem_univ, true_and]
      exact hz
  · intro v hv
    have hno : ∀ x, M.atom x = v → M.atom x ∉ K ∧ M.atom (M.mate x) ∉ K := fun x hx =>
      h.retained K hSK (hx ▸ hCS v hv) (h.closed x (hx ▸ hv))
    have e1 := eraseAtoms_dir_card M K hno true
    have e2 := eraseAtoms_dir_card M K hno false
    unfold Molecule.outdeg Molecule.indeg
    rw [e1, e2]
    exact h.chain v hv

end ThetaGenData

/-! ### Charges of decorations -/

/-- **The total charge vanishes.** -/
theorem charge_sum_zero {M : Molecule V D} {d : ℕ} {L : ℝ} {c : V → Mom d} {κ : D → (Fin d → ℤ)}
    (hκ : M.IsDecoration L 0 c κ) : ∑ v ∈ M.atoms, c v = 0 := by
  classical
  rw [sum_charges_eq_cross hκ (subset_refl _)]
  have : crossDarts M M.atoms = ∅ := by
    ext x; simp only [mem_crossDarts, notMem_empty, iff_false, not_and, not_not]
    intro _; exact M.atom_mem _
  rw [this, sum_empty]

/-- The two darts of an atom with in = out = 1. -/
theorem deg2_darts {M : Molecule V D} {v : V} (h : M.outdeg v = 1 ∧ M.indeg v = 1) :
    ∃ xo xi, M.atom xo = v ∧ M.atom xi = v ∧ M.out xo = true ∧ M.out xi = false ∧ M.dartsAt v = {xo, xi} := by
  classical
  obtain ⟨xo, ho⟩ := card_eq_one.mp h.1
  obtain ⟨xi, hi⟩ := card_eq_one.mp h.2
  have hxo : xo ∈ (M.dartsAt v).filter fun x => M.out x = true := by rw [ho]; exact mem_singleton_self _
  have hxi : xi ∈ (M.dartsAt v).filter fun x => M.out x = false := by rw [hi]; exact mem_singleton_self _
  obtain ⟨hxoA, hxoO⟩ := mem_filter.mp hxo
  obtain ⟨hxiA, hxiO⟩ := mem_filter.mp hxi
  refine ⟨xo, xi, (Mole.mem_dartsAt M v xo).mp hxoA, (Mole.mem_dartsAt M v xi).mp hxiA, hxoO, hxiO, ?_⟩
  ext z
  simp only [mem_insert, mem_singleton]
  constructor
  · intro hz
    cases hzo : M.out z
    · right
      have : z ∈ (M.dartsAt v).filter fun x => M.out x = false := mem_filter.mpr ⟨hz, hzo⟩
      rw [hi] at this; exact mem_singleton.mp this
    · left
      have : z ∈ (M.dartsAt v).filter fun x => M.out x = true := mem_filter.mpr ⟨hz, hzo⟩
      rw [ho] at this; exact mem_singleton.mp this
  · rintro (rfl | rfl)
    · exact hxoA
    · exact hxiA

/-- **The charge of a degree-two atom is its gap** `k_out − k_in`. -/
theorem charge_deg2 {M : Molecule V D} {d : ℕ} {L : ℝ} {c : V → Mom d} {κ : D → (Fin d → ℤ)}
    (hκ : M.IsDecoration L 0 c κ) {v : V} (hv : v ∈ M.atoms) {xo xi : D} (hxo : M.out xo = true)
    (hxi : M.out xi = false) (hne : xo ≠ xi) (hstar : M.dartsAt v = {xo, xi}) :
    c v = Molecule.gapAt L 0 κ xo xi := by
  have h := hκ.2 v hv
  rw [hstar, sum_pair hne] at h
  unfold Molecule.dartSign at h
  rw [hxo, hxi] at h
  simp only [ite_true, Bool.false_eq_true, ite_false, one_smul, neg_one_smul] at h
  rw [← h]
  unfold Molecule.gapAt
  abel

/-- **The charge of a chain**: `s (k_{mate y₁} − k_{mate y₂}) = ∑_C c` for exits `y₁, y₂` of opposite directions,
`s` the sign of `y₁`. -/
theorem chain_charge {M : Molecule V D} {d : ℕ} {L : ℝ} {c : V → Mom d} {κ : D → (Fin d → ℤ)}
    (hκ : M.IsDecoration L 0 c κ) {C : Finset V} (hC : C ⊆ M.atoms) {y₁ y₂ : D} (hne : y₁ ≠ y₂)
    (hcross : crossDarts M C = {y₁, y₂}) (hdir : M.out y₁ ≠ M.out y₂) :
    M.dartSign y₁ • (Molecule.kvec L 0 κ (M.mate y₁) - Molecule.kvec L 0 κ (M.mate y₂)) = ∑ v ∈ C, c v := by
  rw [sum_charges_eq_cross hκ hC, hcross, sum_pair hne]
  have hs : M.dartSign y₂ = - M.dartSign y₁ := by
    unfold Molecule.dartSign; cases h1 : M.out y₁ <;> cases h2 : M.out y₂ <;> simp_all
  simp only [Molecule.kvec, hκ.1]
  rw [hs, smul_sub, neg_smul]
  abel

end

end WaveTurbulence.GammaLow.FinalCount.Count
