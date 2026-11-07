/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.ChainStruct
public import WaveTurbulence.Foundations.FinalCount.ChainOrient
public import WaveTurbulence.Foundations.FinalCount.C5Cut
public import WaveTurbulence.Foundations.FinalCount.C5Bad
import Mathlib.Tactic

/-! # Prop 9.6, case (4): a cut vertex of degree `4` gives a `β`-cut

In a connected molecule with all atoms balanced (`outdeg = indeg`) and all degrees even, if a degree-`4` atom `w` is a cut
vertex (two atoms `a, b ≠ w` are disconnected in `M ∖ w`), then the component of `a` in `M ∖ w` receives exactly two bonds
of `w`, of opposite directions, and so does the rest. The cut at `w` along the two darts of the rest separates `w` from the
new atom.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4

section
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem cutvertex_cut (M : Molecule V D) (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z))
    (hconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) (hbal : ∀ a ∈ M.atoms, M.outdeg a = M.indeg a)
    (heven : ∀ a ∈ M.atoms, M.deg a % 2 = 0) {w : V} (hw : w ∈ M.atoms) (hdw : M.deg w = 4) {a b : V}
    (ha : a ∈ M.atoms) (haw : a ≠ w) (hb : b ∈ M.atoms) (hbw : b ≠ w)
    (hab : ¬ (Degen.eraseAtoms M {w}).SameComponent a b) {v₂ : V} (hv₂ : v₂ ∉ M.atoms) :
    ∃ x₁ x₂, M.IsCutData w v₂ x₁ x₂ ∧ ¬ (M.cut w v₂ x₁ x₂).SameComponent w v₂ := by
  classical
  set N := Degen.eraseAtoms M {w} with hN
  have hT : N.atoms = M.atoms \ {w} := rfl
  set C : Finset V := N.atoms.filter (fun c => N.SameComponent a c) with hC
  set R : Finset V := N.atoms.filter (fun c => ¬ N.SameComponent a c) with hR
  have haN : a ∈ N.atoms := by rw [hT]; exact mem_sdiff.mpr ⟨ha, by simpa using haw⟩
  have hbN : b ∈ N.atoms := by rw [hT]; exact mem_sdiff.mpr ⟨hb, by simpa using hbw⟩
  have hCT : C ⊆ M.atoms \ {w} := fun c hc => hT ▸ (mem_filter.mp hc).1
  have hRT : R ⊆ M.atoms \ {w} := fun c hc => hT ▸ (mem_filter.mp hc).1
  have hAdjN : ∀ x : D, M.atom x ∈ M.atoms \ {w} → M.atom (M.mate x) ∈ M.atoms \ {w} →
      N.SameComponent (M.atom x) (M.atom (M.mate x)) := by
    intro x h1 h2
    exact Relation.EqvGen.rel _ _ ⟨⟨x, (mem_sdiff.mp h1).2, (mem_sdiff.mp h2).2⟩, rfl, rfl⟩
  have hCcl : ∀ x : D, M.atom x ∈ C → M.atom (M.mate x) ∈ M.atoms \ {w} → M.atom (M.mate x) ∈ C := by
    intro x hx hy
    obtain ⟨hx1, hx2⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨hT ▸ hy, Relation.EqvGen.trans _ _ _ hx2 (hAdjN x (hCT hx) hy)⟩
  have hRcl : ∀ x : D, M.atom x ∈ R → M.atom (M.mate x) ∈ M.atoms \ {w} → M.atom (M.mate x) ∈ R := by
    intro x hx hy
    obtain ⟨hx1, hx2⟩ := mem_filter.mp hx
    refine mem_filter.mpr ⟨hT ▸ hy, fun h => hx2 ?_⟩
    have h' : N.SameComponent (M.atom (M.mate x)) (M.atom x) := by
      have := hAdjN (M.mate x) hy (by rw [M.mate_mate]; exact hT ▸ hx1)
      simpa [M.mate_mate] using this
    exact Relation.EqvGen.trans _ _ _ h h'
  have haC : a ∈ C := mem_filter.mpr ⟨haN, Relation.EqvGen.refl _⟩
  have hbR : b ∈ R := mem_filter.mpr ⟨hbN, hab⟩
  have hbnC : b ∉ C := fun h => hab (mem_filter.mp h).2
  have hCne : (Degen.boundaryDarts M C).Nonempty :=
    exists_boundary_of_connected M hconn C (fun c hc => (mem_sdiff.mp (hCT hc)).1) ⟨a, haC⟩
      ⟨b, hb, hbnC⟩
  have hRne : (Degen.boundaryDarts M R).Nonempty :=
    exists_boundary_of_connected M hconn R (fun c hc => (mem_sdiff.mp (hRT hc)).1) ⟨b, hbR⟩
      ⟨a, ha, fun h => (mem_filter.mp h).2 (Relation.EqvGen.refl _)⟩
  have hdisj : Disjoint (Degen.boundaryDarts M C) (Degen.boundaryDarts M R) := by
    rw [Finset.disjoint_left]
    intro x hxC hxR
    simp only [Degen.boundaryDarts, mem_filter, mem_univ, true_and] at hxC hxR
    exact (mem_filter.mp hxR.1).2 (mem_filter.mp hxC.1).2
  have hmC : ∀ x ∈ Degen.boundaryDarts M C, M.mate x ∈ crossDarts M {w} := bd_mate_cross M {w} C hCT hCcl
  have hmR : ∀ x ∈ Degen.boundaryDarts M R, M.mate x ∈ crossDarts M {w} := bd_mate_cross M {w} R hRT hRcl
  have hsub : ((Degen.boundaryDarts M C ∪ Degen.boundaryDarts M R).image M.mate) ⊆ crossDarts M {w} := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    rcases mem_union.mp hx with h | h
    · exact hmC x h
    · exact hmR x h
  have hinj : Function.Injective M.mate := fun x y h => by
    have := congrArg M.mate h; simpa [M.mate_mate] using this
  have hcrossw : (crossDarts M {w}).card = 4 := by
    have : crossDarts M {w} = M.dartsAt w := by
      ext x
      simp only [mem_crossDarts, mem_singleton, Molecule.dartsAt, mem_filter, mem_univ, true_and]
      constructor
      · exact fun h => h.1
      · intro h; exact ⟨h, fun h' => hloop x (h.trans h'.symm)⟩
    rw [this]; exact hdw
  have hcard := card_le_card hsub
  rw [card_image_of_injective _ hinj, card_union_of_disjoint hdisj, hcrossw] at hcard
  -- parity of the boundary of `C` and `R`
  have hpar : ∀ S : Finset V, S ⊆ M.atoms \ {w} → (Degen.boundaryDarts M S).card % 2 = 0 := by
    intro S hS
    have hsum := Degen.sum_degrees_cut M S
    have hev : (∑ z ∈ S, M.deg z) % 2 = 0 := by
      rw [Finset.sum_nat_mod]
      have : ∀ z ∈ S, M.deg z % 2 = 0 := fun z hz => heven z (mem_sdiff.mp (hS hz)).1
      rw [Finset.sum_congr rfl this]; simp
    omega
  have hpC := hpar C hCT
  have hpR := hpar R hRT
  have hC2 : (Degen.boundaryDarts M C).card = 2 := by
    have := card_pos.mpr hCne; have := card_pos.mpr hRne; omega
  have hR2 : (Degen.boundaryDarts M R).card = 2 := by
    have := card_pos.mpr hCne; have := card_pos.mpr hRne; omega
  -- the two boundary darts of `R` are opposite
  obtain ⟨p, q, hpq, hRbd⟩ := card_eq_two.mp hR2
  have hbalR : ∀ v ∈ R, M.outdeg v = M.indeg v := fun v hv => hbal v (mem_sdiff.mp (hRT hv)).1
  have hopp : M.out p ≠ M.out q :=
    chain_cross_opposite M R hbalR hpq (by simpa [Degen.boundaryDarts, crossDarts] using hRbd)
  -- all four darts at `w`
  have hcls : ∀ z, M.atom z = w → (M.atom (M.mate z) ∈ C ∨ M.atom (M.mate z) ∈ R) := by
    intro z hz
    have hne : M.atom (M.mate z) ≠ w := fun h => hloop z (hz.trans h.symm)
    have hmem : M.atom (M.mate z) ∈ N.atoms := by rw [hT]; exact mem_sdiff.mpr ⟨M.atom_mem _, by simpa using hne⟩
    by_cases h : N.SameComponent a (M.atom (M.mate z))
    · exact Or.inl (mem_filter.mpr ⟨hmem, h⟩)
    · exact Or.inr (mem_filter.mpr ⟨hmem, h⟩)
  have hRsub : ∀ z, M.atom z = w → M.atom (M.mate z) ∈ R → M.mate z ∈ Degen.boundaryDarts M R := by
    intro z hz hzR
    simp only [Degen.boundaryDarts, mem_filter, mem_univ, true_and, M.mate_mate]
    exact ⟨hzR, by rw [hz]; intro h; exact (mem_sdiff.mp (hRT h)).2 (mem_singleton_self w)⟩
  have hbdp : p ∈ Degen.boundaryDarts M R := by rw [hRbd]; simp
  have hbdq : q ∈ Degen.boundaryDarts M R := by rw [hRbd]; simp
  have hwp : M.atom (M.mate p) = w := by
    have := mem_singleton.mp (mem_crossDarts.mp (hmR p hbdp)).1; exact this
  have hwq : M.atom (M.mate q) = w := by
    have := mem_singleton.mp (mem_crossDarts.mp (hmR q hbdq)).1; exact this
  -- choose `x₁` incoming, `x₂` outgoing
  obtain ⟨x₁, x₂, hx₁o, hx₂o, hx₁w, hx₂w, hx₁R, hx₂R, hx₁₂⟩ :
      ∃ x₁ x₂ : D, M.out x₁ = false ∧ M.out x₂ = true ∧ M.atom x₁ = w ∧ M.atom x₂ = w ∧
        M.atom (M.mate x₁) ∈ R ∧ M.atom (M.mate x₂) ∈ R ∧ ∀ z, M.atom z = w → M.atom (M.mate z) ∈ R → z = x₁ ∨ z = x₂ := by
    have hmo : ∀ y, M.out (M.mate y) = !M.out y := fun y => by
      have := M.out_mate y; cases h : M.out y <;> simp_all
    have hpR : M.atom p ∈ R := by
      simp only [Degen.boundaryDarts, mem_filter, mem_univ, true_and] at hbdp; exact hbdp.1
    have hqR : M.atom q ∈ R := by
      simp only [Degen.boundaryDarts, mem_filter, mem_univ, true_and] at hbdq; exact hbdq.1
    have hcover : ∀ z, M.atom z = w → M.atom (M.mate z) ∈ R → z = M.mate p ∨ z = M.mate q := by
      intro z hz hzR
      have hzb := hRsub z hz hzR
      rw [hRbd] at hzb
      rcases mem_insert.mp hzb with h | h
      · left; rw [← M.mate_mate z, h]
      · right; rw [← M.mate_mate z, mem_singleton.mp h]
    by_cases hpo : M.out p = true
    · have hqo : M.out q = false := by
        cases h : M.out q
        · rfl
        · exact absurd (hpo.trans h.symm) hopp
      refine ⟨M.mate p, M.mate q, by rw [hmo, hpo]; rfl, by rw [hmo, hqo]; rfl, hwp, hwq, by rw [M.mate_mate]; exact hpR,
        by rw [M.mate_mate]; exact hqR, hcover⟩
    · have hpo' : M.out p = false := by simpa using hpo
      have hqo : M.out q = true := by
        cases h : M.out q
        · exact absurd (hpo'.trans h.symm) hopp
        · rfl
      refine ⟨M.mate q, M.mate p, by rw [hmo, hqo]; rfl, by rw [hmo, hpo']; rfl, hwq, hwp, by rw [M.mate_mate]; exact hqR,
        by rw [M.mate_mate]; exact hpR, fun z hz hzR => (hcover z hz hzR).symm⟩
  have hCmem : ∀ c ∈ C, c ∈ M.atoms ∧ c ≠ w := fun c hc => by
    have := mem_sdiff.mp (hCT hc); exact ⟨this.1, by simpa using this.2⟩
  refine ⟨x₁, x₂, ⟨hw, hv₂, hx₁w, hx₂w, ?_, hx₁o, hx₂o⟩, ?_⟩
  · intro h
    have : M.atom (M.mate (M.mate x₁)) = M.atom (M.mate x₂) := by rw [h]
    rw [M.mate_mate] at this
    have h2 : M.atom x₁ ∈ R := by rw [this]; exact hx₂R
    rw [hx₁w] at h2
    exact (mem_sdiff.mp (hRT h2)).2 (mem_singleton_self w)
  · -- the separating set
    intro hsame
    set K := M.cut w v₂ x₁ x₂ with hK
    have hKatom : ∀ z, K.atom z = if M.atom z = w ∧ z ≠ x₁ ∧ z ≠ x₂ then v₂ else M.atom z := fun z => rfl
    have hKmate : K.mate = M.mate := rfl
    let S : Finset V := insert v₂ C
    have hwS : w ∉ S := by
      simp only [S, mem_insert, not_or]
      exact ⟨fun h => hv₂ (h ▸ hw), fun h => (hCmem w h).2 rfl⟩
    have hv₂S : v₂ ∈ S := mem_insert_self _ _
    have hSC : ∀ c, c ∈ S ↔ c = v₂ ∨ c ∈ C := fun c => mem_insert
    have key : ∀ z, (K.atom z ∈ S ↔ K.atom (K.mate z) ∈ S) := by
      have side : ∀ z, M.atom z = w → (K.atom z ∈ S ↔ K.atom (M.mate z) ∈ S) := by
        intro z hz
        have hz' : M.atom (M.mate z) ≠ w := fun h => hloop z (hz.trans h.symm)
        have hK2 : K.atom (M.mate z) = M.atom (M.mate z) := by
          rw [hKatom]; exact if_neg (fun h => hz' h.1)
        rw [hK2]
        have hCR : ∀ c, c ∈ C → c ∉ R := fun c hc hR' => (mem_filter.mp hR').2 (mem_filter.mp hc).2
        rcases hcls z hz with hzC | hzR
        · have hnz1 : z ≠ x₁ := fun h => hCR _ hzC (h ▸ hx₁R)
          have hnz2 : z ≠ x₂ := fun h => hCR _ hzC (h ▸ hx₂R)
          rw [hKatom, if_pos ⟨hz, hnz1, hnz2⟩]
          exact ⟨fun _ => (hSC _).mpr (Or.inr hzC), fun _ => (hSC _).mpr (Or.inl rfl)⟩
        · have hnotS : M.atom (M.mate z) ∉ S := by
            intro h
            rcases (hSC _).mp h with h | h
            · exact hv₂ (h ▸ M.atom_mem _)
            · exact hCR _ h hzR
          rcases hx₁₂ z hz hzR with h | h
          · rw [hKatom, if_neg (fun hh => hh.2.1 h), hz]
            exact ⟨fun h => absurd h hwS, fun h => absurd h hnotS⟩
          · rw [hKatom, if_neg (fun hh => hh.2.2 h), hz]
            exact ⟨fun h => absurd h hwS, fun h => absurd h hnotS⟩
      intro z
      rw [hKmate]
      by_cases h1 : M.atom z = w
      · exact side z h1
      · by_cases h2 : M.atom (M.mate z) = w
        · have := side (M.mate z) h2
          rw [M.mate_mate] at this
          exact this.symm
        · have e1 : K.atom z = M.atom z := by rw [hKatom]; exact if_neg (fun h => h1 h.1)
          have e2 : K.atom (M.mate z) = M.atom (M.mate z) := by rw [hKatom]; exact if_neg (fun h => h2 h.1)
          rw [e1, e2]
          have m1 : M.atom z ∈ M.atoms \ {w} := mem_sdiff.mpr ⟨M.atom_mem _, by simpa using h1⟩
          have m2 : M.atom (M.mate z) ∈ M.atoms \ {w} := mem_sdiff.mpr ⟨M.atom_mem _, by simpa using h2⟩
          have hadj := hAdjN z m1 m2
          constructor
          · intro h
            rcases (hSC _).mp h with h | h
            · exact absurd (h ▸ M.atom_mem z) hv₂
            · exact (hSC _).mpr (Or.inr (mem_filter.mpr ⟨hT ▸ m2, Relation.EqvGen.trans _ _ _ (mem_filter.mp h).2 hadj⟩))
          · intro h
            rcases (hSC _).mp h with h | h
            · exact absurd (h ▸ M.atom_mem _) hv₂
            · refine (hSC _).mpr (Or.inr (mem_filter.mpr ⟨hT ▸ m1, ?_⟩))
              exact Relation.EqvGen.trans _ _ _ (mem_filter.mp h).2 (Relation.EqvGen.symm _ _ hadj)
    have hclosed : ∀ u t, K.SameComponent u t → (u ∈ S ↔ t ∈ S) := by
      intro u t h
      induction h with
      | rel u t hut =>
        obtain ⟨z, rfl, rfl⟩ := hut
        exact key z
      | refl u => exact Iff.rfl
      | symm u t _ ih => exact ih.symm
      | trans u t s _ _ ih1 ih2 => exact ih1.trans ih2
    exact hwS ((hclosed _ _ hsame).mpr hv₂S)

/-- In an even component every atom is balanced (`outdeg = indeg`) and has even degree. -/
theorem shape_balanced {M : Molecule V D} {cls : V → Cls} {odd : Prop} (hS : FinalShape M cls odd) (hnodd : ¬ odd) :
    ∀ a ∈ M.atoms, M.outdeg a = M.indeg a := by
  intro a ha
  have h4 := Mole.outdeg_add_indeg M a
  have hc := hS.caps a ha
  rcases hS.evenDeg hnodd a ha with h | h
  · have := hS.dir2 a ha h; omega
  · omega

theorem shape_even {M : Molecule V D} {cls : V → Cls} {odd : Prop} (hS : FinalShape M cls odd) (hnodd : ¬ odd) :
    ∀ a ∈ M.atoms, M.deg a % 2 = 0 := by
  intro a ha
  rcases hS.evenDeg hnodd a ha with h | h <;> omega

/-- **`M₀` has no cut vertex** (even component): `ε`-atoms by `noBetaCut` and `epsLG` (a cut vertex of degree `4` gives a
`β`-cut), `β`-atoms by parity. -/
theorem nocut_M0 {d : ℕ} {M : Molecule V D} {cls : V → Cls} {odd : Prop} {L γ η : ℝ}
    {Adm : (D → (Fin d → ℤ)) → Prop} (hS : FinalShape M cls odd) (hF : FinalDec M cls L γ η Adm) (hLp : 0 < L)
    (hnodd : ¬ odd) {κ : D → (Fin d → ℤ)} (hκ : Adm κ) (hfr : ∃ v₂ : V, v₂ ∉ M.atoms) :
    ∀ w ∈ M.atoms, ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, a ≠ w → b ≠ w →
      (Degen.eraseAtoms M {w}).SameComponent a b := by
  classical
  intro w hw a ha b hb haw hbw
  by_cases hε : (cls w).IsEps
  · by_contra hab
    obtain ⟨v₂, hv₂⟩ := hfr
    have hdw : M.deg w = 4 := by
      have := (hS.classes w hw).not.mpr (fun h => h hε)
      rcases hS.evenDeg hnodd w hw with h | h <;> omega
    obtain ⟨x₁, x₂, hc, hsep⟩ := cutvertex_cut M hS.noLoop hS.conn (shape_balanced hS hnodd) (shape_even hS hnodd) hw hdw
      ha haw hb hbw hab hv₂
    exact not_alpha_of_not_sameComponent M hS.conn hc hsep (noBeta_eps hS hF hLp hκ hw hε hc)
  · have hd2 : M.deg w = 2 := by
      have := (hS.classes w hw).mpr hε
      rcases hS.evenDeg hnodd w hw with h | h <;> omega
    have hcard : (crossDarts M {w}).card = 2 := by
      have : crossDarts M {w} = M.dartsAt w := by
        ext x
        simp only [mem_crossDarts, mem_singleton, Molecule.dartsAt, mem_filter, mem_univ, true_and]
        constructor
        · exact fun h => h.1
        · intro h; exact ⟨h, fun h' => hS.noLoop x (h.trans h'.symm)⟩
      rw [this]; exact hd2
    exact connected_erase_of_two_cross M hS.conn (shape_even hS hnodd) {w} hcard a
      (mem_sdiff.mpr ⟨ha, by simpa using haw⟩) b (mem_sdiff.mpr ⟨hb, by simpa using hbw⟩)

end
end WaveTurbulence.FinalCountG8
