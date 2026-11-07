/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.MoleculeBasic
public import WaveTurbulence.Foundations.FinalCount.Degen.LadderDeletionGeometry
import Mathlib.Tactic
/-! # Independent selected-ladder geometry, extracted unchanged from the legacy module.
The legacy induced-ladder counterexample remains a recorded STOP item. -/
@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.Degen
section SelectedLadderGeometry
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- Opposite orientations of a single actual bond are mutually exclusive. -/
theorem directed_reverse_iff_not (M : Molecule V D) {a b : V} (hab : a ≠ b)
    (hcard : M.bondsBetween a b = 1) : M.Directed b a ↔ ¬M.Directed a b := by
  classical
  have hset : ∃ e, (M.bonds.filter fun x => M.ends x = s(a,b)) = {e} := card_eq_one.mp hcard
  obtain ⟨e, he⟩ := hset
  have hboth : ¬(M.Directed a b ∧ M.Directed b a) := by
    classical
    rintro ⟨⟨x, hxo, hxa, hxb⟩, ⟨y, hyo, hyb, hya⟩⟩
    have hx : x ∈ M.bonds.filter (fun x => M.ends x = s(a,b)) := by
      classical
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hxo⟩, ?_⟩
      change s(M.atom x, M.atom (M.mate x)) = s(a,b)
      rw [hxa,hxb]
    have hy : y ∈ M.bonds.filter (fun x => M.ends x = s(a,b)) := by
      classical
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hyo⟩, ?_⟩
      change s(M.atom y, M.atom (M.mate y)) = s(a,b)
      rw [hyb,hya]
      exact Sym2.eq_swap
    rw [he] at hx hy
    have hxy : x = y := (mem_singleton.mp hx).trans (mem_singleton.mp hy).symm
    exact hab (hxa.symm.trans ((congrArg M.atom hxy).trans hyb))
  have hex : M.Directed a b ∨ M.Directed b a := by
    classical
    have hemem : e ∈ M.bonds.filter (fun x => M.ends x = s(a,b)) := by rw [he]; exact mem_singleton_self _
    obtain ⟨heout, heends⟩ := mem_filter.mp hemem
    have hout : M.out e = true := (mem_filter.mp heout).2
    rcases Sym2.eq_iff.mp heends with ⟨ha,hb⟩ | ⟨hb,ha⟩
    · exact Or.inl ⟨e,hout,ha,hb⟩
    · exact Or.inr ⟨e,hout,hb,ha⟩
  tauto

/-- Three distinct actual neighbor fibers are disjoint subsets of the
incident darts, with all parallel multiplicities retained. -/
theorem three_neighbor_bonds_le_degree (M : Molecule V D) {a b c e : V}
    (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e)
    (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e) :
    M.bondsBetween a b + M.bondsBetween a c + M.bondsBetween a e ≤ M.deg a := by
  classical
  have hdis (x y : V) (hxy : x ≠ y) : Disjoint (neighborDarts M a x) (neighborDarts M a y) := by
    classical
    apply disjoint_left.mpr
    intro z hz hw
    exact hxy (((mem_neighborDarts M a x z).mp hz).2.symm.trans ((mem_neighborDarts M a y z).mp hw).2)
  have hd1 := hdis b c hbc
  have hd2 : Disjoint (neighborDarts M a b ∪ neighborDarts M a c) (neighborDarts M a e) :=
    disjoint_union_left.mpr ⟨hdis b e hbe, hdis c e hce⟩
  have hsub : (neighborDarts M a b ∪ neighborDarts M a c) ∪ neighborDarts M a e ⊆ M.dartsAt a := by
    classical
    intro z hz
    rcases mem_union.mp hz with hz | hz
    · rcases mem_union.mp hz with hz | hz
      · exact (mem_filter.mp hz).1
      · exact (mem_filter.mp hz).1
    · exact (mem_filter.mp hz).1
  have hc := card_le_card hsub
  rw [card_union_of_disjoint hd2, card_union_of_disjoint hd1,
    card_neighborDarts M hab, card_neighborDarts M hac, card_neighborDarts M hae] at hc
  exact hc

/-- In a molecule, an atom with a double rung and a single rail has only
one possible double-bond partner. -/
theorem unique_double_partner_of_single_rail (M : Molecule V D) (hM : ∀ x ∈ M.atoms, M.deg x ≤ 4)
    {a b c e : V} (ha : a ∈ M.atoms) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hdouble : M.bondsBetween a b = 2) (hsingle : M.bondsBetween a c = 1)
    (hae : a ≠ e) (he : M.bondsBetween a e = 2) : e = b := by
  classical
  by_contra heb
  by_cases hec : e = c
  · rw [hec, hsingle] at he
    omega
  have hbd : b ≠ e := Ne.symm heb
  have hcd : c ≠ e := Ne.symm hec
  have hh := three_neighbor_bonds_le_degree M hab hac hae hbc hbd hcd
  have hdeg := hM _ ha
  rw [hdouble, hsingle, he] at hh
  omega

/-- A selected source ladder supplies a single rail at each atom. -/
theorem sourceLadder_u_single_neighbor (M : Molecule V D) {m : ℕ}
    {u v : Fin (m+1) → V} (h : SourceLadder M u v) (j : Fin (m+1)) :
    ∃ k : Fin (m+1), k ≠ j ∧ M.bondsBetween (u j) (u k) = 1 := by
  classical
  by_cases hj : j.val < m
  · let i : Fin m := ⟨j.val,hj⟩
    have he : i.castSucc = j := Fin.ext rfl
    refine ⟨i.succ, ?_, ?_⟩
    · intro hh
      have hh' := congrArg Fin.val hh
      simp only [Fin.val_succ] at hh'
      dsimp only [i] at hh'
      omega
    · rw [← he]
      exact (h.2.2.2.2 i).1
  · have hm : 0 < m := h.1
    let i : Fin m := ⟨m-1, by omega⟩
    have he : i.succ = j := Fin.ext (by change (m-1)+1 = j.val; have := j.isLt; omega)
    refine ⟨i.castSucc, ?_, ?_⟩
    · intro hh
      have hh' := congrArg Fin.val hh
      simp only [Fin.val_castSucc] at hh'
      dsimp only [i] at hh'
      omega
    · rw [← he, bondsBetween_comm M]
      exact (h.2.2.2.2 i).1


/-- Reversing both single rails preserves the opposite-direction condition. -/
theorem opposite_single_rails_flip (M : Molecule V D) {a b c e : V}
    (hab : a ≠ b) (hce : c ≠ e)
    (h1 : M.bondsBetween a b = 1) (h2 : M.bondsBetween c e = 1)
    (hdir : M.Directed a b ↔ M.Directed e c) :
    M.Directed c e ↔ M.Directed b a := by
  classical
  have hu := directed_reverse_iff_not M hab h1
  have hv := directed_reverse_iff_not M hce h2
  tauto

/-- Exchanging the two rows preserves a selected ladder. -/
theorem sourceLadder_swap (M : Molecule V D) {m : ℕ} {u v : Fin (m+1) → V}
    (h : SourceLadder M u v) : SourceLadder M v u := by
  classical
  obtain ⟨hu, hv, huv⟩ := Sum.elim_injective.mp h.2.1
  refine ⟨h.1, Sum.elim_injective.mpr ⟨hv, hu, fun i j => (huv j i).symm⟩,
    fun j => ⟨(h.2.2.1 j).2, (h.2.2.1 j).1⟩, ?_, ?_⟩
  · intro j
    rw [bondsBetween_comm M]
    exact h.2.2.2.1 j
  · intro j
    obtain ⟨h1,h2,hdir⟩ := h.2.2.2.2 j
    refine ⟨h2,h1,?_⟩
    apply opposite_single_rails_flip M _ _ h1 h2 hdir
    · exact hu.ne (by intro he; have hh := congrArg Fin.val he; simp only [Fin.val_castSucc, Fin.val_succ] at hh; omega)
    · exact hv.ne (by intro he; have hh := congrArg Fin.val he; simp only [Fin.val_castSucc, Fin.val_succ] at hh; omega)

/-- Traversing a selected ladder in reverse preserves it. -/
theorem sourceLadder_reverse (M : Molecule V D) {m : ℕ} {u v : Fin (m+1) → V}
    (h : SourceLadder M u v) : SourceLadder M (fun j => u j.rev) (fun j => v j.rev) := by
  classical
  obtain ⟨hu, hv, huv⟩ := Sum.elim_injective.mp h.2.1
  have hrev : Function.Injective (Fin.rev : Fin (m+1) → Fin (m+1)) := fun i j hij => by
    have he := congrArg Fin.rev hij
    simpa only [Fin.rev_rev] using he
  refine ⟨h.1, Sum.elim_injective.mpr ⟨hu.comp hrev, hv.comp hrev, fun i j => huv _ _⟩,
    fun j => h.2.2.1 j.rev, fun j => h.2.2.2.1 j.rev, ?_⟩
  intro j
  let k := j.rev
  have he1 : j.castSucc.rev = k.succ := Fin.ext (by simp only [Fin.val_rev, Fin.val_castSucc, Fin.val_succ, k]; omega)
  have he2 : j.succ.rev = k.castSucc := Fin.ext (by simp only [Fin.val_rev, Fin.val_castSucc, Fin.val_succ, k]; omega)
  dsimp only
  rw [he1,he2]
  obtain ⟨h1,h2,hdir⟩ := h.2.2.2.2 k
  have hne : k.castSucc ≠ k.succ := by
    classical
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.val_castSucc, Fin.val_succ] at hh
    omega
  refine ⟨?_,?_,?_⟩
  · rw [bondsBetween_comm M]; exact h1
  · rw [bondsBetween_comm M]; exact h2
  · exact (opposite_single_rails_flip M (hu.ne hne) (hv.ne hne) h1 h2 hdir).symm

/-- Row exchange leaves the actual atom set unchanged. -/
theorem ladderAtoms_swap {m : ℕ} (u v : Fin (m+1) → V) :
    Molecule.ladderAtoms v u = Molecule.ladderAtoms u v := by
  classical
  exact union_comm _ _

/-- Reversal leaves the actual atom set unchanged. -/
theorem ladderAtoms_reverse {m : ℕ} (u v : Fin (m+1) → V) :
    Molecule.ladderAtoms (fun j => u j.rev) (fun j => v j.rev) = Molecule.ladderAtoms u v := by
  classical
  have himage (f : Fin (m+1) → V) : (univ : Finset (Fin (m+1))).image (fun j : Fin (m+1) => f j.rev) = univ.image f := by
    classical
    ext x
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨j,hj⟩
      exact ⟨j.rev,hj⟩
    · rintro ⟨j,hj⟩
      exact ⟨j.rev,by simpa only [Fin.rev_rev] using hj⟩
  unfold Molecule.ladderAtoms
  rw [himage u,himage v]

/-- A matched new rung extends the end of a selected ladder; additional
end-to-end chords are deliberately permitted by the adopted source reading. -/
theorem sourceLadder_snoc (M : Molecule V D) {m : ℕ} {u v : Fin (m+1) → V}
    (h : SourceLadder M u v) {a b : V}
    (ha : a ∉ Molecule.ladderAtoms u v) (hb : b ∉ Molecule.ladderAtoms u v)
    (hab : a ≠ b) (haM : a ∈ M.atoms) (hbM : b ∈ M.atoms)
    (hrung : M.bondsBetween a b = 2)
    (h1 : M.bondsBetween (u (Fin.last m)) a = 1)
    (h2 : M.bondsBetween (v (Fin.last m)) b = 1)
    (hdir : M.Directed (u (Fin.last m)) a ↔ M.Directed b (v (Fin.last m))) :
    SourceLadder M (Fin.snoc u a) (Fin.snoc v b) := by
  classical
  obtain ⟨hu,hv,huv⟩ := Sum.elim_injective.mp h.2.1
  have hau (j : Fin (m+1)) : u j ≠ a := fun he => ha (mem_union_left _ (mem_image.mpr ⟨j,mem_univ _,he⟩))
  have hav (j : Fin (m+1)) : v j ≠ a := fun he => ha (mem_union_right _ (mem_image.mpr ⟨j,mem_univ _,he⟩))
  have hbu (j : Fin (m+1)) : u j ≠ b := fun he => hb (mem_union_left _ (mem_image.mpr ⟨j,mem_univ _,he⟩))
  have hbv (j : Fin (m+1)) : v j ≠ b := fun he => hb (mem_union_right _ (mem_image.mpr ⟨j,mem_univ _,he⟩))
  have hu' : Function.Injective (Fin.snoc u a) := Fin.snoc_injective_iff.mpr ⟨hu,by rintro ⟨j,hj⟩; exact hau j hj⟩
  have hv' : Function.Injective (Fin.snoc v b) := Fin.snoc_injective_iff.mpr ⟨hv,by rintro ⟨j,hj⟩; exact hbv j hj⟩
  refine ⟨by omega, Sum.elim_injective.mpr ⟨hu',hv',?_⟩, ?_, ?_, ?_⟩
  · intro i j
    induction i using Fin.lastCases with
    | cast i =>
      induction j using Fin.lastCases with
      | cast j => simpa only [Fin.snoc_castSucc] using huv i j
      | last => simpa only [Fin.snoc_castSucc,Fin.snoc_last] using hbu i
    | last =>
      induction j using Fin.lastCases with
      | cast j => simpa only [Fin.snoc_castSucc,Fin.snoc_last] using (hav j).symm
      | last => simpa only [Fin.snoc_last] using hab
  · intro j
    induction j using Fin.lastCases with
    | cast j => simpa only [Fin.snoc_castSucc] using h.2.2.1 j
    | last => simpa only [Fin.snoc_last] using And.intro haM hbM
  · intro j
    induction j using Fin.lastCases with
    | cast j => simpa only [Fin.snoc_castSucc] using h.2.2.2.1 j
    | last => simpa only [Fin.snoc_last] using hrung
  · intro j
    induction j using Fin.lastCases with
    | cast j =>
      have he : j.castSucc.succ = j.succ.castSucc := Fin.ext rfl
      simpa only [he,Fin.snoc_castSucc] using h.2.2.2.2 j
    | last =>
      have he : (Fin.last m).succ = Fin.last (m+1) := Fin.ext rfl
      simpa only [he,Fin.snoc_castSucc,Fin.snoc_last] using And.intro h1 (And.intro h2 hdir)


/-- Summing actual bond multiplicities over any finite set of distinct
neighbors never exceeds the half-edge degree at the fixed atom. -/
theorem sum_neighbor_bonds_le_degree (M : Molecule V D) (a : V) (N : Finset V) (ha : a ∉ N) :
    (∑ b ∈ N, M.bondsBetween a b) ≤ M.deg a := by
  classical
  let F := (M.dartsAt a).filter (fun x => M.atom (M.mate x) ∈ N)
  have he := card_eq_sum_card_fiberwise (s := F) (t := N)
    (f := fun x => M.atom (M.mate x)) (fun x hx => (mem_filter.mp hx).2)
  have hf (b : V) (hb : b ∈ N) :
      F.filter (fun x => M.atom (M.mate x) = b) = neighborDarts M a b := by
    classical
    ext x
    simp only [F,neighborDarts,mem_filter]
    constructor
    · rintro ⟨⟨hx,_⟩,heq⟩
      exact ⟨hx,heq⟩
    · rintro ⟨hx,heq⟩
      exact ⟨⟨hx,heq.symm ▸ hb⟩,heq⟩
  calc
    _ = ∑ b ∈ N, (F.filter (fun x => M.atom (M.mate x) = b)).card := by
      classical
      apply sum_congr rfl
      intro b hb
      rw [hf b hb,card_neighborDarts M (by intro heq; exact ha (heq.symm ▸ hb))]
    _ = F.card := he.symm
    _ ≤ _ := card_filter_le _ _

/-- Every selected rung is the unique possible double partner of its atom. -/
theorem sourceLadder_double_partner_eq (M : Molecule V D) (hM : ∀ x ∈ M.atoms, M.deg x ≤ 4)
    {m : ℕ} {u v : Fin (m+1) → V} (h : SourceLadder M u v) (j : Fin (m+1))
    {e : V} (hne : u j ≠ e) (he : M.bondsBetween (u j) e = 2) : e = v j := by
  classical
  obtain ⟨k,hkj,hrail⟩ := sourceLadder_u_single_neighbor M h j
  obtain ⟨hu,hv,huv⟩ := Sum.elim_injective.mp h.2.1
  exact unique_double_partner_of_single_rail M hM (h.2.2.1 j).1 (huv j j)
    (hu.ne hkj.symm) (huv k j).symm (h.2.2.2.1 j) hrail hne he

/-- Membership of one end of a selected rung forces membership of the other
end in every intersecting source ladder. -/
theorem sourceLadder_partner_mem (M : Molecule V D) (hM : ∀ x ∈ M.atoms, M.deg x ≤ 4)
    {m : ℕ} {u v : Fin (m+1) → V} (h : SourceLadder M u v)
    {a b : V} (ha : a ∈ Molecule.ladderAtoms u v) (hab : a ≠ b)
    (hdouble : M.bondsBetween a b = 2) : b ∈ Molecule.ladderAtoms u v := by
  classical
  rcases mem_union.mp ha with ha | ha
  · obtain ⟨j,_,rfl⟩ := mem_image.mp ha
    rw [sourceLadder_double_partner_eq M hM h j hab hdouble]
    exact mem_union_right _ (mem_image.mpr ⟨j,mem_univ _,rfl⟩)
  · obtain ⟨j,_,rfl⟩ := mem_image.mp ha
    rw [sourceLadder_double_partner_eq M hM (sourceLadder_swap M h) j hab hdouble]
    exact mem_union_left _ (mem_image.mpr ⟨j,mem_univ _,rfl⟩)


/-- An edge leaving a selected ladder at one of its atoms can only leave
at an end rung: an interior atom already has all four incident darts. -/
theorem sourceLadder_index_end_of_outside_rail (M : Molecule V D) (hM : ∀ x ∈ M.atoms, M.deg x ≤ 4)
    {m : ℕ} {u v : Fin (m+1) → V} (h : SourceLadder M u v) (j : Fin (m+1))
    {a : V} (ha : a ∉ Molecule.ladderAtoms u v) (hsingle : M.bondsBetween (u j) a = 1) :
    j = 0 ∨ j = Fin.last m := by
  classical
  by_contra hends
  have hj0 : j ≠ 0 := (not_or.mp hends).1
  have hjm : j ≠ Fin.last m := (not_or.mp hends).2
  have hlo : 0 < j.val := by
    classical
    by_contra hh
    exact hj0 (Fin.ext (by change j.val = 0; omega))
  have hhi : j.val < m := by
    classical
    by_contra hh
    exact hjm (Fin.ext (by change j.val = m; have := j.isLt; omega))
  let l : Fin m := ⟨j.val-1,by omega⟩
  let r : Fin m := ⟨j.val,hhi⟩
  have hel : l.succ = j := Fin.ext (by change (j.val-1)+1 = j.val; omega)
  have her : r.castSucc = j := Fin.ext rfl
  have hleft : M.bondsBetween (u j) (u l.castSucc) = 1 := by
    classical
    rw [← hel,bondsBetween_comm M]
    exact (h.2.2.2.2 l).1
  have hright : M.bondsBetween (u j) (u r.succ) = 1 := by
    classical
    rw [← her]
    exact (h.2.2.2.2 r).1
  obtain ⟨hu,hv,huv⟩ := Sum.elim_injective.mp h.2.1
  have hjl : j ≠ l.castSucc := by
    classical
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.val_castSucc] at hh
    dsimp only [l] at hh
    omega
  have hjr : j ≠ r.succ := by
    classical
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.val_succ] at hh
    dsimp only [r] at hh
    omega
  have hlr : l.castSucc ≠ r.succ := by
    classical
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.val_castSucc,Fin.val_succ] at hh
    dsimp only [l,r] at hh
    omega
  have hau (k : Fin (m+1)) : a ≠ u k := by
    classical
    intro he
    apply ha
    exact mem_union_left _ (mem_image.mpr ⟨k,mem_univ _,he.symm⟩)
  have hav (k : Fin (m+1)) : a ≠ v k := by
    classical
    intro he
    apply ha
    exact mem_union_right _ (mem_image.mpr ⟨k,mem_univ _,he.symm⟩)
  have hnot : u j ∉ ({v j,u l.castSucc,u r.succ,a} : Finset V) := by
    classical
    simp only [mem_insert,mem_singleton,not_or]
    exact ⟨huv j j,hu.ne hjl,hu.ne hjr,(hau j).symm⟩
  have hrung := h.2.2.2.1 j
  have hdeg := hM _ (h.2.2.1 j).1
  have hn1 : v j ∉ ({u l.castSucc,u r.succ,a} : Finset V) := by
    classical
    simp only [mem_insert,mem_singleton,not_or]
    exact ⟨(huv l.castSucc j).symm,(huv r.succ j).symm,(hav j).symm⟩
  have hn2 : u l.castSucc ∉ ({u r.succ,a} : Finset V) := by
    classical
    simp only [mem_insert,mem_singleton,not_or]
    exact ⟨hu.ne hlr,(hau l.castSucc).symm⟩
  have hn3 : u r.succ ≠ a := (hau r.succ).symm
  have hsum : (∑ b ∈ ({v j,u l.castSucc,u r.succ,a} : Finset V), M.bondsBetween (u j) b) = 5 := by
    classical
    rw [sum_insert hn1,sum_insert hn2,sum_pair hn3]
    rw [hrung,hleft,hright,hsingle]
    norm_num
  have hbound := sum_neighbor_bonds_le_degree M (u j) {v j,u l.castSucc,u r.succ,a} hnot
  rw [hsum] at hbound
  omega


/-- Maximality excludes a fresh matched rung beyond an end. -/
theorem no_new_end_rung_of_source_maximal (M : Molecule V D) {m : ℕ}
    {u v : Fin (m+1) → V} (h : SourceLadder M u v)
    (hmax : Molecule.ladderAtoms u v ∈ sourceMaximalLadders M)
    {a b : V} (ha : a ∉ Molecule.ladderAtoms u v) (hb : b ∉ Molecule.ladderAtoms u v)
    (hab : a ≠ b) (haM : a ∈ M.atoms) (hbM : b ∈ M.atoms)
    (hrung : M.bondsBetween a b = 2)
    (h1 : M.bondsBetween (u (Fin.last m)) a = 1)
    (h2 : M.bondsBetween (v (Fin.last m)) b = 1)
    (hdir : M.Directed (u (Fin.last m)) a ↔ M.Directed b (v (Fin.last m))) : False := by
  classical
  have hnew := sourceLadder_snoc M h ha hb hab haM hbM hrung h1 h2 hdir
  let S' := Molecule.ladderAtoms (Fin.snoc u a) (Fin.snoc v b)
  have hsub : Molecule.ladderAtoms u v ⊆ S' := by
    classical
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · obtain ⟨j,_,rfl⟩ := mem_image.mp hx
      exact mem_union_left _ (mem_image.mpr ⟨j.castSucc,mem_univ _,by simp only [Fin.snoc_castSucc]⟩)
    · obtain ⟨j,_,rfl⟩ := mem_image.mp hx
      exact mem_union_right _ (mem_image.mpr ⟨j.castSucc,mem_univ _,by simp only [Fin.snoc_castSucc]⟩)
  have hS' : SourceLadderSet M S' := ⟨m+1,Fin.snoc u a,Fin.snoc v b,hnew,rfl⟩
  have hmax' := hmax
  simp only [sourceMaximalLadders,mem_filter,mem_powerset] at hmax'
  have he : S' = Molecule.ladderAtoms u v := hmax'.2.2 S' hS' hsub
  apply ha
  rw [← he]
  exact mem_union_left _ (mem_image.mpr ⟨Fin.last (m+1),mem_univ _,by simp only [Fin.snoc_last]⟩)

/-- Matched rail continuation from any rung of a maximal source ladder
stays in its atom set. The degree cap handles interior rungs, and actual
one-rung extension handles ends. -/
theorem source_maximal_closed_at_index (M : Molecule V D) (hM : ∀ x ∈ M.atoms, M.deg x ≤ 4)
    {m : ℕ} {u v : Fin (m+1) → V} (h : SourceLadder M u v)
    (hmax : Molecule.ladderAtoms u v ∈ sourceMaximalLadders M) (j : Fin (m+1))
    {a b : V} (hab : a ≠ b) (haM : a ∈ M.atoms) (hbM : b ∈ M.atoms)
    (hrung : M.bondsBetween a b = 2)
    (h1 : M.bondsBetween (u j) a = 1) (h2 : M.bondsBetween (v j) b = 1)
    (hdir : M.Directed (u j) a ↔ M.Directed b (v j)) :
    a ∈ Molecule.ladderAtoms u v := by
  classical
  by_contra ha
  have hb : b ∉ Molecule.ladderAtoms u v := by
    classical
    intro hb
    have hh := sourceLadder_partner_mem M hM h hb hab.symm (by rw [bondsBetween_comm M]; exact hrung)
    exact ha hh
  rcases sourceLadder_index_end_of_outside_rail M hM h j ha h1 with hj | hj
  · subst j
    have hrev := sourceLadder_reverse M h
    have hmrev : Molecule.ladderAtoms (fun i => u i.rev) (fun i => v i.rev) ∈ sourceMaximalLadders M := by
      classical
      rw [ladderAtoms_reverse]
      exact hmax
    apply no_new_end_rung_of_source_maximal M hrev hmrev
      (by rw [ladderAtoms_reverse]; exact ha) (by rw [ladderAtoms_reverse]; exact hb)
      hab haM hbM hrung
    · simpa only [Fin.rev_last] using h1
    · simpa only [Fin.rev_last] using h2
    · simpa only [Fin.rev_last] using hdir
  · subst j
    exact no_new_end_rung_of_source_maximal M h hmax ha hb hab haM hbM hrung h1 h2 hdir


/-- A maximal selected ladder is closed under every actual matched
rung/rail step meeting it. -/
theorem source_maximal_closed_step (M : Molecule V D) (hM : ∀ x ∈ M.atoms, M.deg x ≤ 4)
    {m : ℕ} {u v : Fin (m+1) → V} (h : SourceLadder M u v)
    (hmax : Molecule.ladderAtoms u v ∈ sourceMaximalLadders M)
    {a b c e : V} (ha : a ∈ Molecule.ladderAtoms u v) (hab : a ≠ b) (hce : c ≠ e)
    (hcM : c ∈ M.atoms) (heM : e ∈ M.atoms)
    (hab2 : M.bondsBetween a b = 2) (hce2 : M.bondsBetween c e = 2)
    (hac1 : M.bondsBetween a c = 1) (hbe1 : M.bondsBetween b e = 1)
    (hdir : M.Directed a c ↔ M.Directed e b) :
    c ∈ Molecule.ladderAtoms u v := by
  classical
  rcases mem_union.mp ha with ha | ha
  · obtain ⟨j,_,rfl⟩ := mem_image.mp ha
    have hb := sourceLadder_double_partner_eq M hM h j hab hab2
    subst b
    exact source_maximal_closed_at_index M hM h hmax j hce hcM heM hce2 hac1 hbe1 hdir
  · obtain ⟨j,_,rfl⟩ := mem_image.mp ha
    have hs := sourceLadder_swap M h
    have hm : Molecule.ladderAtoms v u ∈ sourceMaximalLadders M := by
      classical
      rw [ladderAtoms_swap]
      exact hmax
    have hb := sourceLadder_double_partner_eq M hM hs j hab hab2
    subst b
    have hh := source_maximal_closed_at_index M hM hs hm j hce hcM heM hce2 hac1 hbe1 hdir
    simpa only [ladderAtoms_swap] using hh

/-- Any selected ladder which meets a maximal selected ladder is contained
in it. This is the substantive continuation/propagation statement. -/
theorem sourceLadder_subset_maximal_of_intersects (M : Molecule V D) (hM : ∀ x ∈ M.atoms, M.deg x ≤ 4)
    {S : Finset V} (hS : S ∈ sourceMaximalLadders M)
    {n : ℕ} {p q : Fin (n+1) → V} (hT : SourceLadder M p q)
    (hmeet : ∃ x, x ∈ S ∧ x ∈ Molecule.ladderAtoms p q) :
    Molecule.ladderAtoms p q ⊆ S := by
  classical
  have hSmem : S ∈ sourceMaximalLadders M := hS
  have hS' := hSmem
  simp only [sourceMaximalLadders,mem_filter,mem_powerset] at hS'
  obtain ⟨m,u,v,hL,hLS⟩ := hS'.2.1
  subst S
  obtain ⟨hp,hq,hpq⟩ := Sum.elim_injective.mp hT.2.1
  let P := fun j : Fin (n+1) => p j ∈ Molecule.ladderAtoms u v ∧ q j ∈ Molecule.ladderAtoms u v
  have hforward (i : Fin n) (hPi : P i.castSucc) : P i.succ := by
    classical
    obtain ⟨h1,h2,hdir⟩ := hT.2.2.2.2 i
    have hfirst := source_maximal_closed_step M hM hL hS hPi.1 (hpq _ _) (hpq _ _)
      (hT.2.2.1 i.succ).1 (hT.2.2.1 i.succ).2
      (hT.2.2.2.1 i.castSucc) (hT.2.2.2.1 i.succ) h1 h2 hdir
    exact ⟨hfirst,sourceLadder_partner_mem M hM hL hfirst (hpq _ _) (hT.2.2.2.1 i.succ)⟩
  have hbackward (i : Fin n) (hPi : P i.succ) : P i.castSucc := by
    classical
    obtain ⟨h1,h2,hdir⟩ := hT.2.2.2.2 i
    have hne : i.castSucc ≠ i.succ := by
      classical
      intro he
      have hh := congrArg Fin.val he
      simp only [Fin.val_castSucc,Fin.val_succ] at hh
      omega
    have hd := (opposite_single_rails_flip M (hp.ne hne) (hq.ne hne) h1 h2 hdir).symm
    have h1' : M.bondsBetween (p i.succ) (p i.castSucc) = 1 := by rw [bondsBetween_comm M]; exact h1
    have h2' : M.bondsBetween (q i.succ) (q i.castSucc) = 1 := by rw [bondsBetween_comm M]; exact h2
    have hfirst := source_maximal_closed_step M hM hL hS hPi.1 (hpq _ _) (hpq _ _)
      (hT.2.2.1 i.castSucc).1 (hT.2.2.1 i.castSucc).2
      (hT.2.2.2.1 i.succ) (hT.2.2.2.1 i.castSucc) h1' h2' hd
    exact ⟨hfirst,sourceLadder_partner_mem M hM hL hfirst (hpq _ _) (hT.2.2.2.1 i.castSucc)⟩
  have hex : ∃ j : Fin (n+1), P j := by
    classical
    obtain ⟨x,hx,hxT⟩ := hmeet
    rcases mem_union.mp hxT with hxT | hxT
    · obtain ⟨j,_,rfl⟩ := mem_image.mp hxT
      exact ⟨j,hx,sourceLadder_partner_mem M hM hL hx (hpq _ _) (hT.2.2.2.1 j)⟩
    · obtain ⟨j,_,rfl⟩ := mem_image.mp hxT
      have hfirst := sourceLadder_partner_mem M hM hL hx (hpq _ _).symm
        (by rw [bondsBetween_comm M]; exact hT.2.2.2.1 j)
      exact ⟨j,hfirst,hx⟩
  have hdown : ∀ j : Fin (n+1), P j → P 0 := by
    classical
    intro j
    induction j using Fin.induction with
    | zero => exact id
    | succ j ih => exact fun hj => ih (hbackward j hj)
  obtain ⟨j,hj⟩ := hex
  have hzero := hdown j hj
  have hall : ∀ j : Fin (n+1), P j := by
    classical
    intro j
    induction j using Fin.induction with
    | zero => exact hzero
    | succ j ih => exact hforward j ih
  intro x hx
  rcases mem_union.mp hx with hx | hx
  · obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    exact (hall i).1
  · obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    exact (hall i).2

/-- Distinct maximal selected source ladders are disjoint, for the actual
molecule carrier and source-reading ladder predicate. -/
theorem sourceMaximalLadders_pairwiseDisjoint_of_degree_le_four (M : Molecule V D) (hM : ∀ x ∈ M.atoms, M.deg x ≤ 4) :
    (sourceMaximalLadders M : Set (Finset V)).PairwiseDisjoint id := by
  classical
  intro S hS T hT hST
  apply disjoint_left.mpr
  intro x hxS hxT
  have hTmem : T ∈ sourceMaximalLadders M := hT
  have hT' := hTmem
  simp only [sourceMaximalLadders,mem_filter,mem_powerset] at hT'
  obtain ⟨n,p,q,hL,hLT⟩ := hT'.2.1
  have hsub : T ⊆ S := by
    classical
    rw [← hLT]
    exact sourceLadder_subset_maximal_of_intersects M hM hS hL ⟨x,hxS,by rw [hLT]; exact hxT⟩
  have hSmem : S ∈ sourceMaximalLadders M := hS
  have hS' := hSmem
  simp only [sourceMaximalLadders,mem_filter,mem_powerset] at hS'
  have heq : S = T := hT'.2.2 S hS'.2.1 hsub
  exact hST heq


/-- Maximal selected source ladders are disjoint in every actual molecule. -/
theorem sourceMaximalLadders_pairwiseDisjoint (M : Molecule V D) (hM : M.IsMolecule) :
    (sourceMaximalLadders M : Set (Finset V)).PairwiseDisjoint id :=
  sourceMaximalLadders_pairwiseDisjoint_of_degree_le_four M
    (fun _ hx => Mole.deg_le_four M hM hx)

end SelectedLadderGeometry
end WaveTurbulence.Degen
