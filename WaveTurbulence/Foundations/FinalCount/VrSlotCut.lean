/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.VrFoldCut
public import WaveTurbulence.Foundations.Molecule.VineRealizedSlot
public import WaveTurbulence.Foundations.Molecule.VineBlockBalance
import Mathlib.Tactic

/-! # VINE-RHO (2): every actual slot is a two-bond cut of the vine

For a realized slot `A` of a vine realization with `k ≥ 1` rungs, the atoms of `S` whose label lies in the
extended near side form a subset `T ⊆ S` containing the starting rail atoms `u₀, v₀`, excluding the first
rung `u₁, v₁`, whose boundary in the induced group has at most two darts. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineRho
open WaveTurbulence WaveTurbulence.Vine Finset
set_option linter.unusedSectionVars false
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- The boundary of `T` in the induced group is counted by the cut weights of the group bonds. -/
theorem induced_boundary_card_eq (M : Molecule V D) {T S : Finset V} (hTS : T ⊆ S) :
    (boundary (Mole.induced M S) T).card = ((M.groupBonds S).map (cutWeight T)).sum := by
  let weight : D → ℕ := fun d => if M.atom d ∈ T ∧ M.atom (M.mate d) ∉ T then 1 else 0
  have hh := sum_internal_darts M S weight
  have he : ((univ.filter (M.InGroup S)).filter
      (fun d => M.atom d ∈ T ∧ M.atom (M.mate d) ∉ T)).card = (boundary (Mole.induced M S) T).card := by
    symm
    apply Finset.card_bij (fun x _ => x.1)
    · intro x hx
      simp only [boundary, mem_filter, mem_univ, true_and] at hx
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨x.2, hx⟩
    · intro x _ y _ hxy
      exact Subtype.ext hxy
    · intro d hd
      simp only [mem_filter, mem_univ, true_and] at hd
      exact ⟨⟨d, hd.1⟩, mem_filter.2 ⟨mem_univ _, hd.2⟩, rfl⟩
  have hl : (∑ d ∈ univ.filter (M.InGroup S), weight d) = (boundary (Mole.induced M S) T).card := by
    simp only [weight, sum_boole, Nat.cast_id]
    exact he
  rw [hl] at hh
  rw [hh]
  simp only [Molecule.groupBonds, Multiset.map_map, Function.comp_def]
  change _ = ∑ d ∈ univ.filter (fun d => M.out d = true ∧ M.InGroup S d), cutWeight T (M.ends d)
  apply sum_congr rfl
  intro d _hd
  simp only [weight, Molecule.ends, cutWeight_pair, M.mate_mate]

theorem template_slot_ne (X : VineType) : ∀ s ∈ X.template.slots, s.1.1 ≠ s.2.1 := by
  cases X <;> decide

omit [DecidableEq D] in
theorem slotFold_eq (X : VineType) (ks : List ℕ) :
    X.expand ks = (X.template.slots.zip ks).foldl (fun U sk => insertRungs U sk.1 sk.2) X.template := rfl

/-- **Every actual slot with `k ≥ 1` is a 2-cut.** -/
theorem slot_cut (M : Molecule V D) {X : VineType} {S : Finset V} {a b : V}
    (R : VineRealization M X S a b) (A : RealizedSlot R) (hk : 1 ≤ A.k) :
    ∃ T : Finset V, T ⊆ S ∧ A.Q.u 0 ∈ T ∧ A.Q.v 0 ∈ T ∧ A.Q.u 1 ∉ T ∧ A.Q.v 1 ∉ T ∧
      (boundary (Mole.induced M S) T).card ≤ 2 := by
  have hzs : (A.s, A.k) ∈ X.template.slots.zip R.k := by
    rw [A.loc]; exact List.mem_append_right _ List.mem_cons_self
  have hsl : A.s ∈ X.template.slots := (List.of_mem_zip hzs).1
  obtain ⟨hs1, hs2, hs3, hs4, hsub, hcut, hyall⟩ := template_side X A.s hsl
  have hrd := expand_slotMembers_ready X R.k R.length_eq
  obtain ⟨W, hWsub, hWold, hWcut, hWnew⟩ := fold_cut_ext (X.template.slots.zip R.k) X.template
    (sideOf X A.s) hrd.1 hrd.2 (template_endpoints X)
    (fun sk hsk => template_slot_endpoints X sk.1 (List.of_mem_zip hsk).1)
    (fun sk hsk => hyall sk.1 (List.of_mem_zip hsk).1) hsub
  have hep := template_slot_endpoints X A.s hsl
  set T := S.filter (fun v => R.f v ∈ W) with hT
  have hTS : T ⊆ S := filter_subset _ _
  have himg : T.image R.f = W := by
    have h1 : S.image R.f = range (X.expand R.k).n := R.image_eq
    ext ℓ
    simp only [hT, mem_image, mem_filter]
    constructor
    · rintro ⟨v, ⟨_, hv⟩, rfl⟩; exact hv
    · intro hℓ
      have : ℓ ∈ S.image R.f := by
        rw [h1]; exact hWsub hℓ
      obtain ⟨v, hv, rfl⟩ := mem_image.mp this
      exact ⟨v, ⟨hv, hℓ⟩, rfl⟩
  have hcard : (boundary (Mole.induced M S) T).card ≤ 2 := by
    rw [induced_boundary_card_eq M hTS]
    have he := mapped_cutWeight_sum M hTS R.f R.injOn
    rw [R.bonds_eq] at he
    have hraw : rawCut (T.image R.f) (X.expand R.k).bonds =
        ((M.groupBonds S).map (cutWeight T)).sum := by
      simpa only [rawCut, Multiset.map_coe, List.map_map, Function.comp_def, Multiset.sum_coe] using he
    rw [← hraw, himg]
    have := hWcut
    rw [hcut] at this
    rw [slotFold_eq]
    exact this.le
  refine ⟨T, hTS, ?_, ?_, ?_, ?_, hcard⟩
  · rw [hT, mem_filter]
    refine ⟨(A.mem 0).1, ?_⟩
    rw [A.ports.1, hWold _ hep.1]; exact hs1
  · rw [hT, mem_filter]
    refine ⟨(A.mem 0).2, ?_⟩
    rw [A.ports.2.1, hWold _ hep.2.2.1]; exact hs2
  · rw [hT, mem_filter]
    rintro ⟨_, h⟩
    rw [(A.labels 1 le_rfl hk).1,
      hWnew _ _ _ _ A.loc _ (by omega) (by omega)] at h
    exact hs3 h
  · rw [hT, mem_filter]
    rintro ⟨_, h⟩
    rw [(A.labels 1 le_rfl hk).2,
      hWnew _ _ _ _ A.loc _ (by omega) (by omega)] at h
    exact hs3 h

end WaveTurbulence.VineRho
