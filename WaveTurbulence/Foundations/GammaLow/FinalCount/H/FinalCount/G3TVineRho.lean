/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VrHyper2
public import WaveTurbulence.Foundations.FinalCount.CutLad2
public import WaveTurbulence.Foundations.Molecule.MoleculeGroups
public import WaveTurbulence.Foundations.Molecule.MoleculeBondsBetween
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.InputsG3
import Mathlib.Combinatorics.Enumerative.DoubleCounting
/-! # H-G3: the ρ-loss of a member of the low family (packet L6-HG3; hand-written, new module)

Main's VINE-RHO bound `VineRho.vine_ladderLoss_le_of_agree` (`FinalCount/VrHyper2.lean`, sha256 in
`H-G3-COPIED-SHA256SUMS`): if `S` is a vine of a molecule `M'` which agrees with `M` away from the joints, then
`ladderLoss M (M.atoms \ S) ≤ 42` (at most `42` maximal ladders of `M` meeting `S` and free atoms of `S`). Main proves it
for the drawn vines from their template realization (`≤ 21` representative atoms). In the low family `𝒱_{γL}` a member is
of type (I), (II) (main's bound) or a T-vine; for a T-vine the representatives are the `≤ 13` atoms left by the `≤ 3`
ladders of L3's N3 Theorem 6 (iv) (`Src.G3Inputs.ladders`) and one atom of each ladder: `≤ 16`, so the loss is `≤ 32`.

* `three_le_degIn`, `degIn_ge_of_mem_ladder`: a ladder atom inside `S` has internal degree `≥ 3` (a rung and a rail), so
  the joints of a block (internal degree `2`) lie on no ladder inside the block;
* `ladderLoss_le_of_cover`: the counting step of main's proof (copied: covered atoms lie on a maximal ladder through a
  representative; the maximal ladders are disjoint, `≤ 4` degrees);
* `tvine_ladderLoss_le_of_agree`, `someVine_ladderLoss_le_of_agree` (the low-family form used by `VrHyper3`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountAsm WaveTurbulence.VineRho Finset

universe u1 u2 u3
variable {V : Type u1} [DecidableEq V] {D : Type u2} [Fintype D] [DecidableEq D] {D' : Type u3} [Fintype D']
  [DecidableEq D']

/-- An atom with a double bond to `y` and a single bond to `z ≠ y`, all inside `S`, has internal degree `≥ 3`. -/
theorem three_le_degIn {M : Molecule V D} {S : Finset V} {x y z : V} (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (h2 : M.bondsBetween x y = 2) (h1 : M.bondsBetween x z = 1) :
    3 ≤ M.degIn S x := by
  rw [Mole.bondsBetween_eq_card_darts M hxy] at h2
  rw [Mole.bondsBetween_eq_card_darts M hxz] at h1
  have hsub : ((M.dartsAt x).filter (fun d => M.atom (M.mate d) = y)) ∪
      ((M.dartsAt x).filter (fun d => M.atom (M.mate d) = z)) ⊆
        (M.dartsAt x).filter (fun d => M.InGroup S d) := by
    intro d hd
    rw [mem_union, mem_filter, mem_filter] at hd
    rw [mem_filter]
    rcases hd with ⟨hd, he⟩ | ⟨hd, he⟩
    · exact ⟨hd, by rw [(Mole.mem_dartsAt M x d).1 hd]; exact hx, by rw [he]; exact hy⟩
    · exact ⟨hd, by rw [(Mole.mem_dartsAt M x d).1 hd]; exact hx, by rw [he]; exact hz⟩
  have hdisj : Disjoint ((M.dartsAt x).filter (fun d => M.atom (M.mate d) = y))
      ((M.dartsAt x).filter (fun d => M.atom (M.mate d) = z)) := by
    rw [disjoint_filter]
    intro d _ e1 e2
    exact hyz (e1.symm.trans e2)
  have hc := card_le_card hsub
  rw [card_union_of_disjoint hdisj, h2, h1] at hc
  unfold Molecule.degIn
  omega

/-- **A ladder atom inside `S` has internal degree `≥ 3`** (its rung and one rail). -/
theorem degIn_ge_of_mem_ladder {M : Molecule V D} {S : Finset V} {m : ℕ} {u w : Fin (m + 1) → V}
    (hL : M.IsLadder u w) (hLS : Molecule.ladderAtoms u w ⊆ S) {x : V} (hx : x ∈ Molecule.ladderAtoms u w) :
    3 ≤ M.degIn S x := by
  obtain ⟨hm, hinj, -, hrung, hrail⟩ := hL
  have hmemu : ∀ i, u i ∈ S := fun i => hLS (mem_union_left _ (mem_image_of_mem u (mem_univ i)))
  have hmemw : ∀ i, w i ∈ S := fun i => hLS (mem_union_right _ (mem_image_of_mem w (mem_univ i)))
  have hnb : ∀ i : Fin (m + 1), ∃ i' : Fin (m + 1), i' ≠ i ∧ M.bondsBetween (u i) (u i') = 1 ∧
      M.bondsBetween (w i) (w i') = 1 := by
    intro i
    by_cases hi : i.val < m
    · refine ⟨⟨i.val + 1, by omega⟩, fun h => by have := congrArg Fin.val h; simp at this, ?_⟩
      have h := hrail ⟨i.val, hi⟩
      have e1 : (⟨i.val, hi⟩ : Fin m).castSucc = i := Fin.ext rfl
      have e2 : (⟨i.val, hi⟩ : Fin m).succ = ⟨i.val + 1, by omega⟩ := Fin.ext rfl
      rw [e1, e2] at h
      exact ⟨h.1, h.2.1⟩
    · have hi' : i.val = m := by omega
      refine ⟨⟨m - 1, by omega⟩, fun h => by have := congrArg Fin.val h; simp at this; omega, ?_⟩
      have h := hrail ⟨m - 1, by omega⟩
      have e1 : (⟨m - 1, by omega⟩ : Fin m).castSucc = ⟨m - 1, by omega⟩ := Fin.ext rfl
      have e2 : (⟨m - 1, by omega⟩ : Fin m).succ = i := Fin.ext (by simp; omega)
      rw [e1, e2] at h
      exact ⟨by rw [Mole.bondsBetween_symm]; exact h.1, by rw [Mole.bondsBetween_symm]; exact h.2.1⟩
  have hne : ∀ s t : Fin (m + 1) ⊕ Fin (m + 1), s ≠ t → Sum.elim u w s ≠ Sum.elim u w t :=
    fun s t h e => h (hinj e)
  rw [Molecule.ladderAtoms, mem_union, mem_image, mem_image] at hx
  rcases hx with ⟨i, -, rfl⟩ | ⟨i, -, rfl⟩
  · obtain ⟨i', hi', h1, -⟩ := hnb i
    exact three_le_degIn (hmemu i) (hmemw i) (hmemu i') (hne (.inl i) (.inr i) Sum.inl_ne_inr)
      (hne (.inl i) (.inl i') (fun h => hi' (Sum.inl_injective h).symm)) (hne (.inr i) (.inl i') Sum.inr_ne_inl)
      (hrung i) h1
  · obtain ⟨i', hi', -, h1⟩ := hnb i
    exact three_le_degIn (hmemw i) (hmemu i) (hmemw i') (hne (.inr i) (.inl i) Sum.inr_ne_inl)
      (hne (.inr i) (.inr i') (fun h => hi' (Sum.inr_injective h).symm)) (hne (.inl i) (.inr i') Sum.inl_ne_inr)
      (by rw [Mole.bondsBetween_symm]; exact hrung i) h1

/-- **The counting step of VINE-RHO** (main's `vine_ladderLoss_le_of_agree`, after its cover `hcover`; copied): if every
atom of `S` is a representative or lies on a maximal ladder through a representative, the loss is at most twice the
number of representatives. -/
theorem ladderLoss_le_of_cover (M : Molecule V D) (hM : M.IsMolecule) (S Rep : Finset V)
    (hcover : ∀ c ∈ S, c ∈ Rep ∨ ∃ N ∈ M.maximalLadders, c ∈ N ∧ ∃ r ∈ Rep, r ∈ N) :
    ladderLoss M (M.atoms \ S) ≤ 2 * Rep.card := by
  have hdeg : ∀ x ∈ M.atoms, M.deg x ≤ 4 := fun x hx => Mole.deg_le_four M hM hx
  have hdis := LadderDisjoint.maximalLadders_pairwiseDisjoint_of_degree_le_four M hdeg
  unfold ladderLoss
  have hA' : (M.maximalLadders.filter fun N => ¬ N ⊆ M.atoms \ S).card ≤ Rep.card := by
    refine card_le_card_of_forall_subsingleton (fun N r => r ∈ N) ?_ ?_
    · intro N hN
      rw [mem_filter] at hN
      obtain ⟨hNm, hNS⟩ := hN
      have hNatoms := isLadderSet_subset M ((mem_maximalLadders_iff M).1 hNm).1
      obtain ⟨c, hcN, hcS⟩ := Finset.not_subset.1 hNS
      have hcS' : c ∈ S := by
        by_contra h
        exact hcS (mem_sdiff.2 ⟨hNatoms hcN, h⟩)
      rcases hcover c hcS' with h | ⟨N₀, hN₀, hcN₀, r, hr, hrN₀⟩
      · exact ⟨c, h, hcN⟩
      · have hNN : N = N₀ := by
          by_contra hne
          exact Finset.disjoint_left.1 (hdis hNm hN₀ hne) hcN hcN₀
        exact ⟨r, hr, hNN ▸ hrN₀⟩
    · intro r _ N hN N' hN'
      have h1 : N ∈ M.maximalLadders.filter (fun N => ¬ N ⊆ M.atoms \ S) := hN.1
      have h2 : N' ∈ M.maximalLadders.filter (fun N => ¬ N ⊆ M.atoms \ S) := hN'.1
      by_contra hne
      exact Finset.disjoint_left.1 (hdis (mem_filter.1 h1).1 (mem_filter.1 h2).1 hne) hN.2 hN'.2
  have hF : (M.atoms.filter fun v => v ∉ M.atoms \ S ∧ ∀ N ∈ M.maximalLadders, v ∉ N).card ≤ Rep.card := by
    apply card_le_card
    intro v hv
    rw [mem_filter] at hv
    have hvS : v ∈ S := by
      by_contra h
      exact hv.2.1 (mem_sdiff.2 ⟨hv.1, h⟩)
    rcases hcover v hvS with h | ⟨N₀, hN₀, hvN₀, _⟩
    · exact h
    · exact absurd hvN₀ (hv.2.2 N₀ hN₀)
  omega

theorem mem_unionAll_iff {l : List (Finset V)} {x : V} : x ∈ TVine.Struct.unionAll l ↔ ∃ P ∈ l, x ∈ P := by
  induction l with
  | nil =>
    have e : TVine.Struct.unionAll ([] : List (Finset V)) = ∅ := rfl
    simp [e]
  | cons a l ih =>
    have e : TVine.Struct.unionAll (a :: l) = a ∪ TVine.Struct.unionAll l := rfl
    rw [e, mem_union, ih]
    simp

/-- **The ρ-loss of a T-vine** (T-analogue of main's `VineRho.vine_ladderLoss_le_of_agree`, from N3 Thm 6 (iv)). -/
theorem tvine_ladderLoss_le_of_agree [Src.G3Inputs V D'] (M : Molecule V D) (hM : M.IsMolecule)
    (M' : Molecule V D') (hM' : M'.IsMolecule) {S : Finset V} {a b p q : V} (hA : Agree M M' p q)
    (hV : M'.IsTVine S a b) (hp : p ∈ S → p = a ∨ p = b) (hq : q ∈ S → q = a ∨ q = b) :
    ladderLoss M (M.atoms \ S) ≤ 42 := by
  have hlad : TVine.Struct.LaddersStatement.{u1, u3} := Src.G3Inputs.ladders (V := V) (D := D')
  obtain ⟨ls, hlen, hls, -, hout⟩ := hlad M' hM' S a b hV
  obtain ⟨da, db⟩ := Mole.block_joint_degrees M' hV.1
  classical
  let pick : Finset V → V := fun L => if h : L.Nonempty then h.choose else a
  set Rep := (S \ TVine.Struct.unionAll ls) ∪ ls.toFinset.image pick with hRep
  have hRc : Rep.card ≤ 16 := by
    rw [hRep]
    have h1 := card_union_le (S \ TVine.Struct.unionAll ls) (ls.toFinset.image pick)
    have h2 := card_image_le (s := ls.toFinset) (f := pick)
    have h3 := List.toFinset_card_le ls
    omega
  have hcover : ∀ c ∈ S, c ∈ Rep ∨ ∃ N ∈ M.maximalLadders, c ∈ N ∧ ∃ r ∈ Rep, r ∈ N := by
    intro c hc
    by_cases hcu : c ∈ TVine.Struct.unionAll ls
    · right
      obtain ⟨L, hL, hcL⟩ := mem_unionAll_iff.1 hcu
      obtain ⟨hLS, m, u, w, hLad, rfl⟩ := hls L hL
      have hjoint : ∀ x ∈ Molecule.ladderAtoms u w, x ≠ a ∧ x ≠ b := by
        intro x hx
        have h3 := degIn_ge_of_mem_ladder hLad hLS hx
        constructor
        · rintro rfl; omega
        · rintro rfl; omega
      have hpq : ∀ x ∈ Molecule.ladderAtoms u w, x ≠ p ∧ x ≠ q := by
        intro x hx
        have hxS := hLS hx
        have hj := hjoint x hx
        constructor
        · rintro rfl
          rcases hp hxS with h | h
          exacts [hj.1 h, hj.2 h]
        · rintro rfl
          rcases hq hxS with h | h
          exacts [hj.1 h, hj.2 h]
      have hu : ∀ j, u j ≠ p ∧ u j ≠ q ∧ w j ≠ p ∧ w j ≠ q := fun j => by
        have h1 := hpq (u j) (mem_union_left _ (mem_image_of_mem u (mem_univ j)))
        have h2 := hpq (w j) (mem_union_right _ (mem_image_of_mem w (mem_univ j)))
        exact ⟨h1.1, h1.2, h2.1, h2.2⟩
      have hLM : M.IsLadderSet (Molecule.ladderAtoms u w) := ⟨m, u, w, ladder_of_agree hA hLad hu, rfl⟩
      obtain ⟨N₀, hN₀, hLN⟩ := exists_maximal_ladder_ge M hLM
      have hne : (Molecule.ladderAtoms u w).Nonempty := ⟨c, hcL⟩
      refine ⟨N₀, hN₀, hLN hcL, pick (Molecule.ladderAtoms u w),
        mem_union_right _ (mem_image_of_mem pick (List.mem_toFinset.2 hL)), hLN ?_⟩
      show (if h : (Molecule.ladderAtoms u w).Nonempty then h.choose else a) ∈ Molecule.ladderAtoms u w
      rw [dif_pos hne]
      exact hne.choose_spec
    · left
      exact mem_union_left _ (mem_sdiff.2 ⟨hc, hcu⟩)
  have := ladderLoss_le_of_cover M hM S Rep hcover
  omega

/-- **The ρ-loss of a member of the low family** (main's `vine_ladderLoss_le_of_agree` for (I), (II); the T-vine bound
`tvine_ladderLoss_le_of_agree`). -/
theorem someVine_ladderLoss_le_of_agree [Src.G3Inputs V D'] (M : Molecule V D) (hM : M.IsMolecule)
    (M' : Molecule V D') (hM' : M'.IsMolecule) {S : Finset V} {a b p q : V} (hA : Agree M M' p q)
    (hV : Src.IsSomeVine Src.γL M' S a b) (hp : p ∈ S → p = a ∨ p = b) (hq : q ∈ S → q = a ∨ q = b) :
    ladderLoss M (M.atoms \ S) ≤ 42 := by
  rcases hV.cases with h | h | h
  · exact vine_ladderLoss_le_of_agree M hM M' hM' hA h hp hq
  · exact vine_ladderLoss_le_of_agree M hM M' hM' hA h hp hq
  · exact tvine_ladderLoss_le_of_agree M hM M' hM' hA h hp hq

end WaveTurbulence.GammaLow.FinalCount.H
