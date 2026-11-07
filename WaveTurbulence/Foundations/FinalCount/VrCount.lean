/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.VrSlotDir
public import WaveTurbulence.Foundations.FinalCount.AsmRho1
import Mathlib.Tactic

/-! # VINE-RHO (5): removing a vine changes `ρ` by at most a constant (TARGET L2226)

For `S` a vine of type `X` in a molecule `M`, `ladderLoss M (M.atoms \ S) ≤ 42`.

The inserted rung chains with at least two rungs are ladders (`slot_ladder`: each slot is a 2-cut, so the net rail flow
vanishes and the rails are antiparallel).  Hence every maximal ladder meeting `S`, and every free atom of `S`,
contains or is one of the `≤ 15` template atoms or the `≤ 6` first-rung atoms of the `≤ 3` slots. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineRho
open WaveTurbulence WaveTurbulence.Vine WaveTurbulence.FinalCount WaveTurbulence.FinalCountAsm Finset
open scoped Classical
set_option linter.unusedSectionVars false
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The atoms of `S` of the template. -/
@[expose] noncomputable def tmplAtoms {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (R : VineRealization M X S a b) : Finset V := S.filter (fun v => R.f v < X.template.n)

/-- The first-rung atoms of the inserted chains. -/
@[expose] noncomputable def firstAtoms {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (R : VineRealization M X S a b) : Finset V :=
  S.filter (fun v => ∃ A : RealizedSlot R, 1 ≤ A.k ∧ (v = A.Q.u 1 ∨ v = A.Q.v 1))

theorem tmplAtoms_card {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (R : VineRealization M X S a b) : (tmplAtoms R).card ≤ 15 := by
  have h : (tmplAtoms R).card ≤ (range X.template.n).card := by
    apply Finset.card_le_card_of_injOn R.f
    · intro v hv
      simp only [tmplAtoms, coe_filter, Set.mem_setOf_eq] at hv
      simp only [coe_range, Set.mem_Iio]
      exact hv.2
    · intro v hv w hw hvw
      simp only [tmplAtoms, coe_filter, Set.mem_setOf_eq] at hv hw
      exact R.injOn hv.1 hw.1 hvw
  rw [card_range] at h
  exact h.trans (template_n_le X)

theorem firstAtoms_card {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (R : VineRealization M X S a b) : (firstAtoms R).card ≤ 6 := by
  set Z := X.template.slots.zip R.k with hZ
  let off : ℕ → ℕ := fun j => ((Z.take j).foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n
  let kk : ℕ → ℕ := fun j => (Z.getD j default).2
  let Offs : Finset ℕ := (range 3).image off ∪ (range 3).image (fun j => off j + kk j)
  have hOffs : Offs.card ≤ 6 := by
    refine (card_union_le _ _).trans ?_
    have h1 := (card_image_le (s := range 3) (f := off))
    have h2 := (card_image_le (s := range 3) (f := fun j => off j + kk j))
    simp only [card_range] at h1 h2
    omega
  have hmap : ∀ v ∈ firstAtoms R, R.f v ∈ Offs := by
    intro v hv
    simp only [firstAtoms, mem_filter] at hv
    obtain ⟨_, A, hk, hvA⟩ := hv
    have hpre : Z.take A.pre.length = A.pre := by
      rw [hZ, A.loc]; exact List.take_left
    have hlen : A.pre.length < 3 := by
      have h1 : A.pre.length < Z.length := by
        rw [hZ, A.loc]; simp
      have h2 : Z.length ≤ X.template.slots.length := by
        rw [hZ, List.length_zip]; exact Nat.min_le_left _ _
      have := template_slots_le X
      omega
    have hkk : kk A.pre.length = A.k := by
      simp only [kk]
      have : Z.getD A.pre.length default = (A.s, A.k) := by
        rw [hZ, A.loc]
        simp [List.getD_eq_getElem?_getD]
      rw [this]
    have hoff : off A.pre.length = (A.pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n := by
      simp only [off]; rw [hpre]
    simp only [Offs, mem_union, mem_image]
    rcases hvA with rfl | rfl
    · left
      refine ⟨A.pre.length, mem_range.2 hlen, ?_⟩
      rw [hoff, (A.labels 1 le_rfl hk).1]; rfl
    · right
      refine ⟨A.pre.length, mem_range.2 hlen, ?_⟩
      rw [hoff, hkk, (A.labels 1 le_rfl hk).2]; rfl
  have := Finset.card_le_card_of_injOn R.f (s := firstAtoms R) (t := Offs)
    (fun v hv => hmap v hv) (fun v hv w hw hvw => R.injOn (mem_filter.1 hv).1 (mem_filter.1 hw).1 hvw)
  omega

/-- **Removing a vine changes `ρ` by at most a constant**: `ladderLoss M (M.atoms \ S) ≤ 42`
(TARGET L2226, "each of Operations 1-4 changes the value of `ρ` by at most `C₀`", for Operation 1's vine removal). -/
theorem vine_ladderLoss_le (M : Molecule V D) (hM : M.IsMolecule) {X : VineType} {S : Finset V} {a b : V}
    (hV : M.IsVine X S a b) : ladderLoss M (M.atoms \ S) ≤ 42 := by
  obtain ⟨hB, ⟨R⟩⟩ := isVine_iff_realization.1 hV
  have hdeg : ∀ x ∈ M.atoms, M.deg x ≤ 4 := fun x hx => Mole.deg_le_four M hM hx
  have hdis := LadderDisjoint.maximalLadders_pairwiseDisjoint_of_degree_le_four M hdeg
  set Rep := tmplAtoms R ∪ firstAtoms R with hRep
  have hRepcard : Rep.card ≤ 21 := by
    rw [hRep]
    have := card_union_le (tmplAtoms R) (firstAtoms R)
    have := tmplAtoms_card R
    have := firstAtoms_card R
    omega
  have hRepS : Rep ⊆ S := by
    intro v hv
    rw [hRep, mem_union] at hv
    rcases hv with hv | hv <;> exact (mem_filter.1 hv).1
  -- every atom of `S` is a template atom, a first-rung atom, or lies in a chain ladder
  have hcover : ∀ c ∈ S, c ∈ Rep ∨ ∃ N ∈ M.maximalLadders, c ∈ N ∧ ∃ r ∈ Rep, r ∈ N := by
    intro c hc
    by_cases hlow : R.f c < X.template.n
    · exact Or.inl (mem_union_left _ (mem_filter.2 ⟨hc, hlow⟩))
    · obtain ⟨A, i, h1, h2, hcA⟩ := R.fresh_slot hc (not_lt.1 hlow)
      have hu1 : A.Q.u 1 ∈ Rep := mem_union_right _ (mem_filter.2 ⟨(A.mem 1).1, A, by omega, Or.inl rfl⟩)
      by_cases hk : A.k = 1
      · left
        have hi : i = 1 := by omega
        subst hi
        rcases hcA with rfl | rfl
        · exact hu1
        · exact mem_union_right _ (mem_filter.2 ⟨(A.mem 1).2, A, by omega, Or.inr rfl⟩)
      · right
        obtain ⟨L, hL, hLmem⟩ := slot_ladder M hM R hB A (by omega)
        obtain ⟨N₀, hN₀, hLN⟩ := exists_maximal_ladder_ge M hL
        have hcL : c ∈ L := by
          rcases hcA with rfl | rfl
          · exact (hLmem i h1 h2).1
          · exact (hLmem i h1 h2).2
        exact ⟨N₀, hN₀, hLN hcL, A.Q.u 1, hu1, hLN (hLmem 1 le_rfl (by omega)).1⟩
  unfold ladderLoss
  -- ladders meeting `S`
  have hA : (M.maximalLadders.filter fun N => ¬ N ⊆ M.atoms \ S).card ≤ Rep.card := by
    have hex : ∀ N ∈ M.maximalLadders.filter (fun N => ¬ N ⊆ M.atoms \ S), ∃ r ∈ Rep, r ∈ N := by
      intro N hN
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
    have : Nonempty V := ⟨a⟩
    choose! r hr using hex
    refine card_le_card_of_injOn r (fun N hN => (hr N hN).1) ?_
    intro N hN N' hN' e
    have hN1 := (mem_filter.1 hN).1
    have hN1' := (mem_filter.1 hN').1
    by_contra hne
    exact Finset.disjoint_left.1 (hdis hN1 hN1' hne) (hr N hN).2 (e ▸ (hr N' hN').2)
  -- free atoms of `S`
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

end WaveTurbulence.VineRho
