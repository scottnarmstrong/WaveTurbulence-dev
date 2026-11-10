/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Degen.LadderDeletionGeometry
public import WaveTurbulence.Foundations.FinalCount.Degen.LadderRestriction
import Mathlib.Tactic

/-! # Physical rail-gap propagation along selected source ladders

TARGET defdiff and ladderl1old: every consecutive parallel rail pair
carries the same gap norm. Actual interior two-atom conservation supplies
the equality up to sign, including same-direction double rungs.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.Degen
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The actual physical gap on a chosen consecutive rail pair. -/
def RailGapAt (M : Molecule V D) {d m : ℕ} (L : ℝ) (w : Mom d)
    (κ : D → (Fin d → ℤ)) (u v : Fin (m+1) → V) (j : Fin m) (r : Mom d) : Prop :=
  ∃ x y : D, M.atom x = u j.castSucc ∧ M.atom (M.mate x) = u j.succ ∧
    M.atom y = v j.castSucc ∧ M.atom (M.mate y) = v j.succ ∧
    r = Molecule.gapAt L w κ x y

/-- Two rung darts and the actual left/right rail darts exhaust an interior
atom's four incidences; this is derived from the degree cap. -/
theorem interior_darts_eq (M : Molecule V D) (hM : M.IsMolecule)
    {a b l r : V} (hab : a ≠ b) (hbl : b ≠ l) (hbr : b ≠ r) (hlr : l ≠ r)
    (hrung : M.bondsBetween a b = 2) {x y : D}
    (hx : M.atom x = a ∧ M.atom (M.mate x) = l)
    (hy : M.atom y = a ∧ M.atom (M.mate y) = r) :
    M.dartsAt a = neighborDarts M a b ∪ {x,y} ∧ M.deg a = 4 := by
  have hxy : x ≠ y := by
    intro he
    subst y
    exact hlr (hx.2.symm.trans hy.2)
  have hdis : Disjoint (neighborDarts M a b) ({x,y} : Finset D) := by
    apply disjoint_left.mpr
    intro z hz hzp
    have hzn := (mem_neighborDarts M a b z).mp hz
    rcases mem_insert.mp hzp with rfl | hzy
    · exact hbl (hzn.2.symm.trans hx.2)
    · have he : z = y := mem_singleton.mp hzy
      subst z
      exact hbr (hzn.2.symm.trans hy.2)
  have hsub : neighborDarts M a b ∪ {x,y} ⊆ M.dartsAt a := by
    intro z hz
    rcases mem_union.mp hz with hz | hz
    · exact (mem_filter.mp hz).1
    · rcases mem_insert.mp hz with hzx | hz
      · subst z
        exact (Mole.mem_dartsAt M a x).mpr hx.1
      · have he : z = y := mem_singleton.mp hz
        subst z
        exact (Mole.mem_dartsAt M a y).mpr hy.1
  have hcard : (neighborDarts M a b ∪ {x,y}).card = 4 := by
    rw [card_union_of_disjoint hdis, card_neighborDarts M hab, hrung, card_pair hxy]
  have haM : a ∈ M.atoms := hx.1 ▸ M.atom_mem x
  have hcap := Mole.deg_le_four M hM haM
  have heq : neighborDarts M a b ∪ {x,y} = M.dartsAt a :=
    eq_of_subset_of_card_le hsub (by change M.deg a ≤ _; rw [hcard]; exact hcap)
  exact ⟨heq.symm, by rw [Molecule.deg, ← heq, hcard]⟩

omit [DecidableEq D] in
/-- A single crossing bond has exactly one dart at its prescribed endpoint. -/
theorem neighbor_dart_eq_of_single (M : Molecule V D) {a b : V} (hab : a ≠ b)
    (hbond : M.bondsBetween a b = 1) {x y : D}
    (hx : M.atom x = a ∧ M.atom (M.mate x) = b)
    (hy : M.atom y = a ∧ M.atom (M.mate y) = b) : x = y := by
  have hc : (neighborDarts M a b).card ≤ 1 := by rw [card_neighborDarts M hab,hbond]
  exact card_le_one.mp hc x ((mem_neighborDarts M a b x).mpr hx)
    y ((mem_neighborDarts M a b y).mpr hy)

/-- The direction predicate of a single rail is the actual dart's orientation. -/
theorem directed_iff_out_of_single (M : Molecule V D) {a b : V} (hab : a ≠ b)
    (hbond : M.bondsBetween a b = 1) {x : D}
    (hx : M.atom x = a ∧ M.atom (M.mate x) = b) :
    M.Directed a b ↔ M.out x = true := by
  constructor
  · rintro ⟨y,hout,hy,hym⟩
    have he := neighbor_dart_eq_of_single M hab hbond ⟨hy,hym⟩ hx
    exact he ▸ hout
  · intro hout
    exact ⟨x,hout,hx⟩

/-- The source's opposite-direction clause becomes an equality of actual
Boolean rail orientations. -/
theorem rail_out_opposite (M : Molecule V D) {a b c d : V}
    (hab : a ≠ b) (hcd : c ≠ d) (h1 : M.bondsBetween a b = 1)
    (h2 : M.bondsBetween c d = 1)
    (hdir : M.Directed a b ↔ M.Directed d c) {x y : D}
    (hx : M.atom x = a ∧ M.atom (M.mate x) = b)
    (hy : M.atom y = c ∧ M.atom (M.mate y) = d) : M.out y = !M.out x := by
  have h2' : M.bondsBetween d c = 1 := by rw [bondsBetween_comm]; exact h2
  have hym : M.atom (M.mate y) = d ∧ M.atom (M.mate (M.mate y)) = c :=
    ⟨hy.2, by rw [M.mate_mate]; exact hy.1⟩
  rw [directed_iff_out_of_single M hab h1 hx,
    directed_iff_out_of_single M hcd.symm h2' hym, M.out_mate] at hdir
  cases hxout : M.out x <;> cases hyout : M.out y <;> simp_all

/-- Two-atom rung cut: once the actual stars are exhausted by the rung and
four rails, its boundary contains exactly the four actual rail darts. -/
theorem boundary_pair_eq_rails (M : Molecule V D) {a b l r l' r' : V}
    {x y z t : D}
    (hx : M.atom x = a ∧ M.atom (M.mate x) = l)
    (hy : M.atom y = a ∧ M.atom (M.mate y) = r)
    (hz : M.atom z = b ∧ M.atom (M.mate z) = l')
    (ht : M.atom t = b ∧ M.atom (M.mate t) = r')
    (hl : l ∉ ({a,b} : Finset V)) (hr : r ∉ ({a,b} : Finset V))
    (hl' : l' ∉ ({a,b} : Finset V)) (hr' : r' ∉ ({a,b} : Finset V))
    (hstarA : M.dartsAt a = neighborDarts M a b ∪ {x,y})
    (hstarB : M.dartsAt b = neighborDarts M b a ∪ {z,t}) :
    boundaryDarts M {a,b} = {x,y} ∪ {z,t} := by
  ext q
  constructor
  · intro hq
    have hq' : M.atom q ∈ ({a,b} : Finset V) ∧ M.atom (M.mate q) ∉ ({a,b} : Finset V) :=
      (mem_filter.mp hq).2
    have haorb : M.atom q = a ∨ M.atom q = b := by simpa only [mem_insert,mem_singleton] using hq'.1
    rcases haorb with hqa | hqb
    · have hqa' := (Mole.mem_dartsAt M a q).mpr hqa
      rw [hstarA] at hqa'
      rcases mem_union.mp hqa' with hqn | hqr
      · have hn := (mem_neighborDarts M a b q).mp hqn
        exact False.elim (hq'.2 (by rw [hn.2]; simp))
      · exact mem_union_left _ hqr
    · have hqb' := (Mole.mem_dartsAt M b q).mpr hqb
      rw [hstarB] at hqb'
      rcases mem_union.mp hqb' with hqn | hqr
      · have hn := (mem_neighborDarts M b a q).mp hqn
        exact False.elim (hq'.2 (by rw [hn.2]; simp))
      · exact mem_union_right _ hqr
  · intro hq
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    rcases mem_union.mp hq with hq | hq
    · rcases mem_insert.mp hq with rfl | hq
      · exact ⟨by rw [hx.1]; simp,by simpa only [hx.2] using hl⟩
      · have he : q = y := mem_singleton.mp hq
        subst q
        exact ⟨by rw [hy.1]; simp,by simpa only [hy.2] using hr⟩
    · rcases mem_insert.mp hq with rfl | hq
      · exact ⟨by rw [hz.1]; simp,by simpa only [hz.2] using hl'⟩
      · have he : q = t := mem_singleton.mp hq
        subst q
        exact ⟨by rw [ht.1]; simp,by simpa only [ht.2] using hr'⟩

omit [DecidableEq V] [Fintype D] [DecidableEq D] in
private theorem abs_dartSign (M : Molecule V D) (x : D) : |M.dartSign x| = 1 := by
  unfold Molecule.dartSign
  split_ifs <;> norm_num

/-- Actual two-atom conservation propagates the gap norm across an
interior rung. Neither a zero-gap condition nor a cancellation estimate
is an input: the signed four-rail identity is derived from cut_momentum. -/
theorem interior_rail_gap_norm_eq (M : Molecule V D) (hM : M.IsMolecule)
    {d : ℕ} {L : ℝ} {w : Mom d} {κ : D → (Fin d → ℤ)} {c : V → Mom d}
    (hd : M.IsDecoration L w c κ) (hc : ∀ v ∈ M.atoms, M.deg v = 4 → c v = 0)
    {a b l r l' r' : V} (hab : a ≠ b)
    (hbl : b ≠ l) (hbr : b ≠ r) (hal : a ≠ l') (har : a ≠ r')
    (hlr : l ≠ r) (hlr' : l' ≠ r')
    (hl : l ∉ ({a,b} : Finset V)) (hr : r ∉ ({a,b} : Finset V))
    (hl' : l' ∉ ({a,b} : Finset V)) (hr' : r' ∉ ({a,b} : Finset V))
    (hrung : M.bondsBetween a b = 2) {x y z t : D}
    (hx : M.atom x = a ∧ M.atom (M.mate x) = l)
    (hy : M.atom y = a ∧ M.atom (M.mate y) = r)
    (hz : M.atom z = b ∧ M.atom (M.mate z) = l')
    (ht : M.atom t = b ∧ M.atom (M.mate t) = r')
    (hleft : M.out z = !M.out x) (hright : M.out t = !M.out y) :
    ‖Molecule.kvec L w κ x - Molecule.kvec L w κ z‖ =
      ‖Molecule.kvec L w κ y - Molecule.kvec L w κ t‖ := by
  obtain ⟨hstarA,hdegA⟩ := interior_darts_eq M hM hab hbl hbr hlr hrung hx hy
  have hrung' : M.bondsBetween b a = 2 := by rw [bondsBetween_comm]; exact hrung
  obtain ⟨hstarB,hdegB⟩ := interior_darts_eq M hM hab.symm hal har hlr' hrung' hz ht
  have haM : a ∈ M.atoms := hx.1 ▸ M.atom_mem x
  have hbM : b ∈ M.atoms := hz.1 ▸ M.atom_mem z
  have hS : ({a,b} : Finset V) ⊆ M.atoms := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact haM
    · exact (mem_singleton.mp hv).symm ▸ hbM
  have hcut := cut_momentum M hd {a,b} hS
  rw [boundary_pair_eq_rails M hx hy hz ht hl hr hl' hr' hstarA hstarB] at hcut
  have hxy : x ≠ y := by intro he; subst y; exact hlr (hx.2.symm.trans hy.2)
  have hzt : z ≠ t := by intro he; subst t; exact hlr' (hz.2.symm.trans ht.2)
  have hpairA (q : D) (hq : q ∈ ({x,y} : Finset D)) : M.atom q = a := by
    rcases mem_insert.mp hq with rfl | hq
    · exact hx.1
    · exact (mem_singleton.mp hq).symm ▸ hy.1
  have hpairB (q : D) (hq : q ∈ ({z,t} : Finset D)) : M.atom q = b := by
    rcases mem_insert.mp hq with rfl | hq
    · exact hz.1
    · exact (mem_singleton.mp hq).symm ▸ ht.1
  have hdis : Disjoint ({x,y} : Finset D) {z,t} := by
    apply disjoint_left.mpr
    intro q hqa hqb
    exact hab ((hpairA q hqa).symm.trans (hpairB q hqb))
  rw [sum_union hdis, sum_pair hxy, sum_pair hzt,
    sum_pair hab, hc a haM hdegA, hc b hbM hdegB, zero_add] at hcut
  have hsignz : M.dartSign z = -M.dartSign x := by
    unfold Molecule.dartSign
    rw [hleft]
    cases hout : M.out x <;> norm_num
  have hsignt : M.dartSign t = -M.dartSign y := by
    unfold Molecule.dartSign
    rw [hright]
    cases hout : M.out y <;> norm_num
  rw [hsignz, hsignt, neg_smul, neg_smul] at hcut
  have heq : M.dartSign x • (Molecule.kvec L w κ x - Molecule.kvec L w κ z) =
      -(M.dartSign y • (Molecule.kvec L w κ y - Molecule.kvec L w κ t)) := by
    apply eq_neg_of_add_eq_zero_left
    calc
      _ = (M.dartSign x • Molecule.kvec L w κ x + M.dartSign y • Molecule.kvec L w κ y) +
          (-(M.dartSign x • Molecule.kvec L w κ z) + -(M.dartSign y • Molecule.kvec L w κ t)) := by
        simp only [smul_sub]
        abel
      _ = 0 := hcut
  have hn := congrArg norm heq
  simpa only [norm_neg, norm_smul, Real.norm_eq_abs, abs_dartSign, one_mul] using hn

/-- Each selected pair of consecutive single rails has an actual physical gap. -/
theorem sourceLadder_exists_railGapAt (M : Molecule V D) {d m : ℕ}
    (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) {u v : Fin (m+1) → V}
    (hL : SourceLadder M u v) (j : Fin m) : ∃ r, RailGapAt M L w κ u v j r := by
  obtain ⟨hu,hv,_⟩ := Sum.elim_injective.mp hL.2.1
  have hne : j.castSucc ≠ j.succ := by
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.val_castSucc,Fin.val_succ] at hh
    omega
  have ha := adj_of_bondsBetween_pos M (fun he => hne (hu he)) (by rw [(hL.2.2.2.2 j).1]; omega)
  have hb := adj_of_bondsBetween_pos M (fun he => hne (hv he)) (by rw [(hL.2.2.2.2 j).2.1]; omega)
  obtain ⟨x,hx,hxm⟩ := ha
  obtain ⟨y,hy,hym⟩ := hb
  exact ⟨Molecule.gapAt L w κ x y,x,y,hx,hxm,hy,hym,rfl⟩

/-- The gap on a fixed pair of selected single rails is unique. -/
theorem sourceLadder_railGapAt_unique (M : Molecule V D) {d m : ℕ}
    (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) {u v : Fin (m+1) → V}
    (hL : SourceLadder M u v) (j : Fin m) {r s : Mom d}
    (hr : RailGapAt M L w κ u v j r) (hs : RailGapAt M L w κ u v j s) : r = s := by
  obtain ⟨x,y,hx,hxm,hy,hym,rfl⟩ := hr
  obtain ⟨x',y',hx',hxm',hy',hym',rfl⟩ := hs
  obtain ⟨hu,hv,_⟩ := Sum.elim_injective.mp hL.2.1
  have hne : j.castSucc ≠ j.succ := by
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.val_castSucc,Fin.val_succ] at hh
    omega
  have hxe := neighbor_dart_eq_of_single M (fun he => hne (hu he)) (hL.2.2.2.2 j).1 ⟨hx,hxm⟩ ⟨hx',hxm'⟩
  have hye := neighbor_dart_eq_of_single M (fun he => hne (hv he)) (hL.2.2.2.2 j).2.1 ⟨hy,hym⟩ ⟨hy',hym'⟩
  rw [hxe,hye]

/-- Consecutive rail pairs have equal physical gap norms. The actual
intermediate rung is proved to consist of two degree-four atoms. -/
theorem sourceLadder_consecutive_gap_norm_eq (M : Molecule V D) (hM : M.IsMolecule)
    {d m : ℕ} {L : ℝ} {w : Mom d} {κ : D → (Fin d → ℤ)} {c : V → Mom d}
    (hd : M.IsDecoration L w c κ) (hc : ∀ a ∈ M.atoms, M.deg a = 4 → c a = 0)
    {u v : Fin (m+1) → V} (hL : SourceLadder M u v)
    (i j : Fin m) (hij : i.val + 1 = j.val) {r s : Mom d}
    (hr : RailGapAt M L w κ u v i r) (hs : RailGapAt M L w κ u v j s) : ‖r‖ = ‖s‖ := by
  obtain ⟨x,z,hx,hxm,hz,hzm,hr⟩ := hr
  obtain ⟨y,t,hy,hym,ht,htm,hs⟩ := hs
  obtain ⟨hu,hv,hcross⟩ := Sum.elim_injective.mp hL.2.1
  have hmid : i.succ = j.castSucc := Fin.ext hij
  have h01 : i.castSucc ≠ i.succ := by
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.val_castSucc,Fin.val_succ] at hh
    omega
  have h02 : i.castSucc ≠ j.succ := by
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.val_castSucc,Fin.val_succ] at hh
    omega
  have h12 : i.succ ≠ j.succ := by
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.val_succ] at hh
    omega
  have hleft := rail_out_opposite M (fun he => h01 (hu he)) (fun he => h01 (hv he))
    (hL.2.2.2.2 i).1 (hL.2.2.2.2 i).2.1 (hL.2.2.2.2 i).2.2 ⟨hx,hxm⟩ ⟨hz,hzm⟩
  have hjne : j.castSucc ≠ j.succ := by
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.val_castSucc,Fin.val_succ] at hh
    omega
  have hright := rail_out_opposite M (fun he => hjne (hu he)) (fun he => hjne (hv he))
    (hL.2.2.2.2 j).1 (hL.2.2.2.2 j).2.1 (hL.2.2.2.2 j).2.2 ⟨hy,hym⟩ ⟨ht,htm⟩
  have hya : M.atom y = u i.succ := hy.trans (congrArg u hmid).symm
  have htb : M.atom t = v i.succ := ht.trans (congrArg v hmid).symm
  have hlout : M.out (M.mate z) = !M.out (M.mate x) := by rw [M.out_mate,M.out_mate,hleft]
  have hgap := interior_rail_gap_norm_eq M hM hd hc (hcross _ _)
    ((hcross _ _).symm) ((hcross _ _).symm) (hcross _ _) (hcross _ _)
    (fun he => h02 (hu he)) (fun he => h02 (hv he))
    (by simp only [mem_insert,mem_singleton,not_or]; exact ⟨fun he => h01 (hu he),hcross _ _⟩)
    (by simp only [mem_insert,mem_singleton,not_or]; exact ⟨fun he => h12.symm (hu he),hcross _ _⟩)
    (by simp only [mem_insert,mem_singleton,not_or]; exact ⟨(hcross _ _).symm,fun he => h01 (hv he)⟩)
    (by simp only [mem_insert,mem_singleton,not_or]; exact ⟨(hcross _ _).symm,fun he => h12.symm (hv he)⟩)
    (hL.2.2.2.1 i.succ)
    ⟨hxm,by rw [M.mate_mate]; exact hx⟩ ⟨hya,hym⟩
    ⟨hzm,by rw [M.mate_mate]; exact hz⟩ ⟨htb,htm⟩ hlout hright
  rw [hr,hs]
  change ‖Molecule.kvec L w κ x - Molecule.kvec L w κ z‖ =
    ‖Molecule.kvec L w κ y - Molecule.kvec L w κ t‖
  simpa only [Molecule.kvec,hd.1 x,hd.1 z] using hgap

/-- Every selected rail pair along the ladder has the same physical gap
norm, by induction through the actual interior rungs. -/
theorem sourceLadder_railGapAt_norm_eq (M : Molecule V D) (hM : M.IsMolecule)
    {d m : ℕ} {L : ℝ} {w : Mom d} {κ : D → (Fin d → ℤ)} {c : V → Mom d}
    (hd : M.IsDecoration L w c κ) (hc : ∀ a ∈ M.atoms, M.deg a = 4 → c a = 0)
    {u v : Fin (m+1) → V} (hL : SourceLadder M u v)
    (i j : Fin m) {r s : Mom d}
    (hr : RailGapAt M L w κ u v i r) (hs : RailGapAt M L w κ u v j s) : ‖r‖ = ‖s‖ := by
  have hm : 0 < m := by have hm := hL.1; omega
  let z : Fin m := ⟨0,hm⟩
  obtain ⟨q,hq⟩ := sourceLadder_exists_railGapAt M L w κ hL z
  have hall (n : ℕ) : ∀ (hn : n < m) (r : Mom d), RailGapAt M L w κ u v ⟨n,hn⟩ r → ‖r‖ = ‖q‖ := by
    induction n with
    | zero =>
      intro hn r hr
      have he : (⟨0,hn⟩ : Fin m) = z := Fin.ext rfl
      rw [he] at hr
      exact congrArg norm (sourceLadder_railGapAt_unique M L w κ hL z hr hq)
    | succ n ih =>
      intro hn r hr
      have hn' : n < m := by omega
      obtain ⟨p,hp⟩ := sourceLadder_exists_railGapAt M L w κ hL ⟨n,hn'⟩
      have hstep := sourceLadder_consecutive_gap_norm_eq M hM hd hc hL ⟨n,hn'⟩ ⟨n+1,hn⟩ rfl hp hr
      exact hstep.symm.trans (ih hn' p hp)
  exact (hall i.val i.isLt r hr).trans (hall j.val j.isLt s hs).symm

omit [DecidableEq V] [Fintype D] [DecidableEq D] in
/-- The draft/source first-rail gap predicate is the literal zero-indexed
physical rail gap. No direction convention or magnitude is changed. -/
theorem isLadderGap_iff_railGapAt_zero (M : Molecule V D) {d m : ℕ}
    (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (u v : Fin (m+1) → V)
    (hm : 1 ≤ m) (r : Mom d) :
    M.IsLadderGap L w κ u v hm r ↔ RailGapAt M L w κ u v ⟨0,by omega⟩ r := by
  constructor
  · rintro ⟨x,y,hx,hy,hax,hay,hr⟩
    have hxm : M.atom (M.mate x) = u ⟨1,by omega⟩ := by
      rcases Sym2.eq_iff.mp hx with ⟨_,h⟩ | ⟨h,h'⟩
      · exact h
      · exact h'.trans (hax.symm.trans h)
    have hym : M.atom (M.mate y) = v ⟨1,by omega⟩ := by
      rcases Sym2.eq_iff.mp hy with ⟨_,h⟩ | ⟨h,h'⟩
      · exact h
      · exact h'.trans (hay.symm.trans h)
    exact ⟨x,y,hax,hxm,hay,hym,hr⟩
  · rintro ⟨x,y,hx,hxm,hy,hym,hr⟩
    refine ⟨x,y,?_,?_,hx,hy,hr⟩
    · change s(M.atom x,M.atom (M.mate x)) = _
      rw [hx,hxm]
      rfl
    · change s(M.atom y,M.atom (M.mate y)) = _
      rw [hy,hym]
      rfl

end WaveTurbulence.Degen
