/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairStars
public import WaveTurbulence.Foundations.FinalCount.MoleProp.LowDegreeBoundaryPatterns
import Mathlib.Tactic

/-! # The old single-crossing cut fixing the extra degree-four label -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

private theorem adj_erase_of_not_mem (M : Molecule V D) (Y : Finset V) {a b : V}
    (ha : a ∉ Y) (hb : b ∉ Y) (hab : M.Adj a b) : (eraseAtoms M Y).Adj a b := by
  obtain ⟨x,hx,hxm⟩ := hab
  exact ⟨⟨x,hx.symm ▸ ha,hxm.symm ▸ hb⟩,hx,hxm⟩

/-- In the degree-three/four, two-circuit-loss branch, the old graph has
an actual singleton crossing cut at the structural extra dart. Its other
endpoint lies outside the affected cell. No post-deletion charge is used. -/
theorem exists_extra_old_single_boundary (M : Molecule V D) (hM : M.IsMolecule)
    (hloop : ∀ x, M.atom x ≠ M.atom (M.mate x))
    {a b : V} (hab : a ≠ b) (ha3 : M.deg a = 3) (hb4 : M.deg b = 4)
    (hdouble : M.bondsBetween a b = 2) {S : Finset V}
    (hS : IsLadderCell M S) (hmeet : ¬ Disjoint S {a,b})
    (hloss : (eraseAtoms M {a,b}).circuitRank = M.circuitRank - 2) :
    ∃ (t : D) (U : Finset V), M.atom t = b ∧ M.atom (M.mate t) ∉ S ∧
      U ⊆ M.atoms ∧ Disjoint U S ∧ boundaryDarts M U = {M.mate t} := by
  classical
  obtain ⟨u,v,x,y,r,s,hL,hUS,hu0,hv0,hxy,hx,hy,hr,hs,_hout,_hxr,_hyr,
      _hmxy,_hmxs,_hmys,hA,_hB3,hB4⟩ := exists_double_pair_stars M hM hab ha3 hdouble hS hmeet
  obtain ⟨t,ht,hbt,hB⟩ := hB4 hb4
  obtain ⟨hu,hv,huv⟩ := Sum.elim_injective.mp hL.2.1
  let c := u 1
  let d := v 1
  let N := eraseAtoms M {a}
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hac : a ≠ c := by rw [← hu0]; exact hu.ne h01
  have had : a ≠ d := by rw [← hu0]; exact huv 0 1
  have hbc : b ≠ c := by rw [← hv0]; exact (huv 1 0).symm
  have hbd : b ≠ d := by rw [← hv0]; exact hv.ne h01
  have hcd : c ≠ d := huv 1 1
  have ham : a ∈ M.atoms := hx.1 ▸ M.atom_mem x
  have hbm : b ∈ M.atoms := hx.2 ▸ M.atom_mem (M.mate x)
  have hcm : c ∈ M.atoms := (hL.2.2.1 1).1
  have hdm : d ∈ M.atoms := (hL.2.2.1 1).2
  have hbN : b ∈ N.atoms := mem_sdiff.mpr ⟨hbm,by simpa only [mem_singleton] using hab.symm⟩
  have hcN : c ∈ N.atoms := mem_sdiff.mpr ⟨hcm,by simpa only [mem_singleton] using hac.symm⟩
  have hdN : d ∈ N.atoms := mem_sdiff.mpr ⟨hdm,by simpa only [mem_singleton] using had.symm⟩
  have hloopN : ∀ q : RetainedDart M {a}, N.atom q ≠ N.atom (N.mate q) := fun q => hloop q.val
  have hdegN : N.deg b = 2 := by
    have hh := degree_erase_double_endpoint M hab hdouble
    change N.deg b + 2 = M.deg b at hh
    omega
  have hfirst := circuitRank_erase_first_double_cell_eq M hM hloop hab ha3 hdouble hS hmeet
  have hsecond : (eraseAtoms N {b}).circuitRank = N.circuitRank := by
    change (eraseAtoms (eraseAtoms M {a}) {b}).circuitRank = (eraseAtoms M {a}).circuitRank
    rw [circuitRank_erase_erase_singleton_eq]
    omega
  have hnew : (newComponents N {b}).card = 2 := by
    have hh := circuitRank_erase_singleton_sub_general N hbN
    have hi := incident_card_eq_deg_of_loopless N hloopN b
    omega
  have hbdN : N.Adj b d := adj_erase_of_not_mem M {a}
    (by simpa only [mem_singleton] using hab.symm)
    (by simpa only [mem_singleton] using had.symm) ⟨s,hs.1,hs.2⟩
  have hdcM : M.Adj d c := Mole.adj_symmetric M
    (adj_of_bondsBetween_pos M hcd (by have hh := hL.2.2.2.1 1; change M.bondsBetween c d = 2 at hh; omega))
  have hdcN : N.Adj d c := adj_erase_of_not_mem M {a}
    (by simpa only [mem_singleton] using had.symm)
    (by simpa only [mem_singleton] using hac.symm) hdcM
  let T := residualComponent N {b} d
  have hdT : d ∈ T := (mem_residualComponent N {b} d d).mpr
    ⟨hdN,by simpa only [mem_singleton] using hbd.symm,Relation.EqvGen.refl d⟩
  have hcT : c ∈ T := (mem_residualComponent N {b} d c).mpr
    ⟨hcN,by simpa only [mem_singleton] using hbc.symm,
      Relation.EqvGen.rel _ _ ⟨by simpa only [mem_singleton] using hbd.symm,
        by simpa only [mem_singleton] using hbc.symm,hdcN⟩⟩
  have hTK : T ∈ newComponents N {b} := residualComponent_mem_newComponents_of_sameComponent N
    hbN hdN hbd.symm (Relation.EqvGen.rel _ _ (Mole.adj_symmetric N hbdN))
  have hcardErase : ((newComponents N {b}).erase T).card = 1 := by
    have hh := card_erase_add_one hTK
    omega
  obtain ⟨U,hUe⟩ := card_pos.mp (by omega : 0 < ((newComponents N {b}).erase T).card)
  obtain ⟨hUT,hUK⟩ := mem_erase.mp hUe
  have hUi := (mem_filter.mp hUK).1
  obtain ⟨w,_hw,hrep⟩ := mem_image.mp hUi
  have hdU : d ∉ U := by
    intro hdu
    have he := residualComponent_eq_of_mem N {b} (hrep.symm ▸ hdu) hdT
    exact hUT (hrep.symm.trans he)
  have hcU : c ∉ U := by
    intro hcu
    have he := residualComponent_eq_of_mem N {b} (hrep.symm ▸ hcu) hcT
    exact hUT (hrep.symm.trans he)
  have hsubN : U ⊆ N.atoms := by
    intro z hz
    rw [← hrep] at hz
    exact ((mem_residualComponent N {b} w z).mp hz).1
  have hbU : b ∉ U := by
    intro hbu
    rw [← hrep] at hbu
    exact ((mem_residualComponent N {b} w b).mp hbu).2.1 (mem_singleton_self b)
  have haU : a ∉ U := fun hau => (mem_sdiff.mp (hsubN hau)).2 (mem_singleton_self a)
  have hsubM : U ⊆ M.atoms := fun z hz => (mem_sdiff.mp (hsubN hz)).1
  have hdis : Disjoint U S := by
    apply disjoint_left.mpr
    intro z hzU hzS
    rw [← hUS] at hzS
    rcases mem_union.mp hzS with hz | hz
    · obtain ⟨i,_,rfl⟩ := mem_image.mp hz
      fin_cases i
      · exact haU (hu0 ▸ hzU)
      · exact hcU hzU
    · obtain ⟨i,_,rfl⟩ := mem_image.mp hz
      fin_cases i
      · exact hbU (hv0 ▸ hzU)
      · exact hdU hzU
  have hboundN : (boundaryDarts N U).card = 1 :=
    boundary_card_eq_one_of_card_newComponents_eq_degree N (by omega) hUK
  have haneighbors (q : D) (hq : M.atom q = a) : M.atom (M.mate q) = b ∨ M.atom (M.mate q) = c := by
    have hqmem := (Mole.mem_dartsAt M a q).mpr hq
    rw [hA] at hqmem
    rcases mem_insert.mp hqmem with rfl | hqmem
    · exact Or.inl hx.2
    rcases mem_insert.mp hqmem with rfl | hqmem
    · exact Or.inl hy.2
    have hqr : q = r := mem_singleton.mp hqmem
    subst q
    exact Or.inr hr.2
  have hBimage : boundaryDarts M U = (boundaryDarts N U).image (fun q => q.val) := by
    ext q
    constructor
    · intro hq
      have hqU := (mem_filter.mp hq).2.1
      have hqmU := (mem_filter.mp hq).2.2
      have hqa : M.atom q ∉ ({a} : Finset V) := by
        intro hh
        exact haU ((mem_singleton.mp hh) ▸ hqU)
      have hqma : M.atom (M.mate q) ∉ ({a} : Finset V) := by
        intro hh
        have hcases := haneighbors (M.mate q) (mem_singleton.mp hh)
        rw [M.mate_mate] at hcases
        rcases hcases with h | h
        · exact hbU (h ▸ hqU)
        · exact hcU (h ▸ hqU)
      exact mem_image.mpr ⟨⟨q,hqa,hqma⟩,mem_filter.mpr ⟨mem_univ _,hqU,hqmU⟩,rfl⟩
    · intro hq
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hq
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hz).2.1,(mem_filter.mp hz).2.2⟩
  have hboundM : (boundaryDarts M U).card = 1 := by
    rw [hBimage,card_image_of_injective _ Subtype.val_injective]
    exact hboundN
  obtain ⟨q,hq⟩ := card_eq_one.mp hboundM
  have hqmem : q ∈ boundaryDarts M U := by rw [hq]; exact mem_singleton_self _
  have hqU := (mem_filter.mp hqmem).2.1
  have hqim : q ∈ (boundaryDarts N U).image (fun z => z.val) := hBimage ▸ hqmem
  obtain ⟨qN,hqN,hqval⟩ := mem_image.mp hqim
  have hqN' : qN ∈ boundaryDarts N (residualComponent N {b} w) := hrep.symm ▸ hqN
  have hqb := mem_singleton.mp (residual_boundary_ends_in_removed N {b} w hqN')
  change M.atom (M.mate qN.val) = b at hqb
  have hqmb : M.atom (M.mate q) = b := by rw [← hqval]; exact hqb
  have hqstar := (Mole.mem_dartsAt M b (M.mate q)).mpr hqmb
  rw [hB] at hqstar
  simp only [mem_insert,mem_singleton] at hqstar
  have hqt : M.mate q = t := by
    rcases hqstar with h | h | h | h
    · have hqx : q = x := Mole.mate_injective M h
      exact False.elim (haU (by rw [hqx,hx.1] at hqU; exact hqU))
    · have hqy : q = y := Mole.mate_injective M h
      exact False.elim (haU (by rw [hqy,hy.1] at hqU; exact hqU))
    · have hqs : q = M.mate s := by rw [← h,M.mate_mate]
      exact False.elim (hdU (by rw [hqs,hs.2] at hqU; exact hqU))
    · exact h
  have hqt' : q = M.mate t := by rw [← hqt,M.mate_mate]
  have hcut : boundaryDarts M U = {M.mate t} := by rw [hq,hqt']
  have htU : M.atom (M.mate t) ∈ U := by rwa [hqt'] at hqU
  have htS : M.atom (M.mate t) ∉ S := fun hmem => disjoint_left.mp hdis htU hmem
  exact ⟨t,U,hbt,htS,hsubM,hdis,hcut⟩

/-- The old singleton cut belongs to the extra dart of any already chosen
actual paired star, not merely to a fresh existentially selected dart. -/
theorem exists_extra_old_single_boundary_of_selected_star (M : Molecule V D) (hM : M.IsMolecule)
    (hloop : ∀ q, M.atom q ≠ M.atom (M.mate q))
    {a b : V} (hab : a ≠ b) (ha3 : M.deg a = 3) (hb4 : M.deg b = 4)
    (hdouble : M.bondsBetween a b = 2) {S : Finset V}
    (hS : IsLadderCell M S) (hmeet : ¬ Disjoint S {a,b})
    (hloss : (eraseAtoms M {a,b}).circuitRank = M.circuitRank - 2)
    {x y s t : D} (hB : M.dartsAt b = {M.mate x,M.mate y,s,t})
    (hxa : M.atom x = a) (hya : M.atom y = a) (hsS : M.atom (M.mate s) ∈ S) :
    ∃ U : Finset V, U ⊆ M.atoms ∧ Disjoint U S ∧ boundaryDarts M U = {M.mate t} := by
  obtain ⟨q,U,hqb,hqS,hsub,hdis,hcut⟩ :=
    exists_extra_old_single_boundary M hM hloop hab ha3 hb4 hdouble hS hmeet hloss
  have haS : a ∈ S := by
    by_contra ha
    exact hmeet ((cell_disjoint_double_pair_iff M hM hab hdouble hS).mpr ha)
  have hqstar := (Mole.mem_dartsAt M b q).mpr hqb
  rw [hB] at hqstar
  simp only [mem_insert,mem_singleton] at hqstar
  have hqt : q = t := by
    rcases hqstar with h | h | h | h
    · exact False.elim (hqS (by rw [h,M.mate_mate,hxa]; exact haS))
    · exact False.elim (hqS (by rw [h,M.mate_mate,hya]; exact haS))
    · exact False.elim (hqS (by simpa only [h] using hsS))
    · exact h
  exact ⟨U,hsub,hdis,by simpa only [hqt] using hcut⟩

/-- The extra label in any chosen paired-star encoding is fixed by the
actual old source charges; no label-fixing premise is assumed. -/
theorem selected_extra_label_unique_of_double_cell_loss_two (M : Molecule V D) (hM : M.IsMolecule)
    (hloop : ∀ q, M.atom q ≠ M.atom (M.mate q))
    {a b : V} (hab : a ≠ b) (ha3 : M.deg a = 3) (hb4 : M.deg b = 4)
    (hdouble : M.bondsBetween a b = 2) {S : Finset V}
    (hS : IsLadderCell M S) (hmeet : ¬ Disjoint S {a,b})
    (hloss : (eraseAtoms M {a,b}).circuitRank = M.circuitRank - 2)
    {x y s t : D} (hB : M.dartsAt b = {M.mate x,M.mate y,s,t})
    (hxa : M.atom x = a) (hya : M.atom y = a) (hsS : M.atom (M.mate s) ∈ S)
    {d : ℕ} {L : ℝ} (hL : L ≠ 0) {w : Mom d} {c : V → Mom d}
    {κ κ' : D → (Fin d → ℤ)} (hd : M.IsDecoration L w c κ) (hd' : M.IsDecoration L w c κ') :
    κ t = κ' t := by
  obtain ⟨U,_hsub,_hdis,hcut⟩ := exists_extra_old_single_boundary_of_selected_star M hM hloop
    hab ha3 hb4 hdouble hS hmeet hloss hB hxa hya hsS
  exact incident_label_unique_of_single_boundary M hL hd hd' hcut

end WaveTurbulence.MoleProp
