/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.SplitGeom

/-! # Supports of a split CL block (V5 Step 4b, P2.3)

Tree-order description of the realization nodes (`mem_real_iff`) and the support identity
`clLocalSupport RU = splitA RS ∪ clLocalSupport RT` with `splitA RS ∩ clLocalSupport RT ⊆ {b, b.child kept}`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree
variable {w : ℕ} {G : Garden w} {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}

/-! ## Tree-order helpers -/

theorem isDesc_cases (v : GBranch G.tree) {y : GNode G.tree} (h : v.toNode.IsDesc y) :
    y = v.toNode ∨ ∃ i, (v.child i).IsDesc y := by
  obtain ⟨hj, r, hr⟩ := h
  have hj' : v.1.1 = y.1.1 := hj
  have hr' : v.1.2 ++ r = y.1.2 := hr
  rcases r with _ | ⟨i, r⟩
  · left
    apply Subtype.ext
    have hy : y.1.2 = v.1.2 := by simpa using hr'.symm
    exact Prod.ext hj'.symm hy
  · right
    refine ⟨i, hj', r, ?_⟩
    show v.1.2 ++ [i] ++ r = y.1.2
    simpa using hr'

theorem isDesc_child_cases {u : GNode G.tree} (v : GBranch G.tree) (j : Fin 3) (h : u.IsDesc (v.child j)) :
    u.IsDesc v.toNode ∨ u = v.child j := by
  obtain ⟨hj, hp⟩ := h
  have hp' : u.1.2 <+: v.1.2 ++ [j] := hp
  rcases List.prefix_concat_iff.mp hp' with h | h
  · right
    exact Subtype.ext (Prod.ext hj h)
  · left
    exact ⟨hj, h⟩

theorem child_eq_child {v u : GBranch G.tree} {i j : Fin 3} (h : v.child i = u.child j) : v = u := by
  have h1 : v.1.1 = u.1.1 := congrArg (fun z : GNode G.tree => z.1.1) h
  have h2 : v.1.2 ++ [i] = u.1.2 ++ [j] := congrArg (fun z : GNode G.tree => z.1.2) h
  have h3 := (List.append_inj' h2 rfl).1
  exact Subtype.ext (Prod.ext h1 h3)

theorem isDesc_trans' {x y z : GNode G.tree} (h1 : x.IsDesc y) (h2 : y.IsDesc z) : x.IsDesc z :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

theorem isDesc_refl' (x : GNode G.tree) : x.IsDesc x := ⟨rfl, List.prefix_refl _⟩

theorem isDesc_antisymm' {x y : GNode G.tree} (h1 : x.IsDesc y) (h2 : y.IsDesc x) : x = y :=
  Subtype.ext (Prod.ext h1.1 (h1.2.eq_of_length (le_antisymm h1.2.length_le h2.2.length_le)))

theorem isDesc_child' (v : GBranch G.tree) (i : Fin 3) : v.toNode.IsDesc (v.child i) :=
  ⟨rfl, List.prefix_append _ _⟩

/-! ## Realization nodes by descendants -/

theorem mem_real_iff (hB : G.molecule.IsBlock S a b) (R : CLRegionData G S a b) (x : GNode G.tree) :
    x ∈ clRealizationNodes G S ↔ a.toNode.IsDesc x ∧ ¬ (a.child R.excluded).IsDesc x ∧
      ∀ i : Fin 3, i ≠ R.kept → ¬ (b.child i).IsDesc x :=
  (mem_clRealizationNodes x).trans ((Mole.cl_node_realization_iff G hB R.parentPattern x).trans
    (Mole.cl_pruned_region_explicit G R.upper R.lower x))

/-- The part of the support of `RU` that belongs to the upper block `S` (without the two excluded children of `b`). -/
@[expose] noncomputable def splitA (RS : CLRegionData G S a b) : Finset (GNode G.tree) :=
  clRealizationNodes G S ∪ {a.toNode, a.child RS.excluded}

section Split2
variable (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c) (hi : S ∩ T = {b})
  (hU : G.molecule.IsBlock (S ∪ T) a c)
include hS hT hi hU

theorem split_excluded_b (RS : CLRegionData G S a b) (RT : CLRegionData G T b c) :
    RT.excluded = RS.kept := by
  have hb : b ∈ S ∪ T := Finset.mem_union_left _ hS.2.2.1
  have hd := hU.2.2.2.2.2.2.2.2.1 b hb hS.2.2.2.1.symm hT.2.2.2.1
  have he : Mole.internalPositions G (S ∪ T) b = Finset.univ :=
    Finset.eq_univ_of_card _ ((Mole.card_internalPositions G (S ∪ T) b).trans hd)
  have hmem : RT.excluded.succ ∈ Mole.internalPositions G (S ∪ T) b := he ▸ Finset.mem_univ _
  rw [split_internalPositions hS hT hi hU] at hmem
  rcases Finset.mem_union.mp hmem with h | h
  · exact (RS.lower RT.excluded).mp h
  · exact absurd rfl ((RT.upper RT.excluded).mp h)

theorem splitA_desc (RS : CLRegionData G S a b) {x : GNode G.tree} (hx : x ∈ splitA RS) :
    a.toNode.IsDesc x ∧ ∀ i : Fin 3, i ≠ RS.kept → ¬ (b.child i).IsDesc x := by
  have hab : a.toNode.IsDesc b.toNode := ((mem_real_iff hS RS _).mp
    ((branch_mem_clRealizationNodes b).mpr hS.2.2.1)).1
  have hbn : ¬ (a.child RS.excluded).IsDesc b.toNode := ((mem_real_iff hS RS _).mp
    ((branch_mem_clRealizationNodes b).mpr hS.2.2.1)).2.1
  have hne : a.toNode ≠ b.toNode := fun h => hS.2.2.2.1 (Mole.branch_toNode_injective h)
  rcases Finset.mem_union.mp hx with h | h
  · obtain ⟨h1, _, h3⟩ := (mem_real_iff hS RS x).mp h
    exact ⟨h1, h3⟩
  · rcases Finset.mem_insert.mp h with rfl | h
    · refine ⟨isDesc_refl' _, fun i _ hd => hne (isDesc_antisymm' hab (isDesc_trans' (isDesc_child' b i) hd))⟩
    · have h := Finset.mem_singleton.mp h
      subst h
      refine ⟨isDesc_child' a _, fun i _ hd => ?_⟩
      have hb := isDesc_trans' (isDesc_child' b i) hd
      rcases isDesc_child_cases a RS.excluded hb with h1 | h1
      · exact hne (isDesc_antisymm' hab h1)
      · exact hbn (h1 ▸ isDesc_refl' _)

theorem split_support (RU : CLRegionData G (S ∪ T) a c) (RS : CLRegionData G S a b) (RT : CLRegionData G T b c) :
    clLocalSupport RU = splitA RS ∪ clLocalSupport RT := by
  have hex := split_excluded_a hS hT hi hU RU RS
  have hpn := split_positive_c hS hT hi hU RU RT
  have hkb := split_excluded_b hS hT hi hU RS RT
  have hRS : ∀ x, x ∈ clRealizationNodes G S → x ∈ splitA RS := fun x hx => Finset.mem_union_left _ hx
  have hA0 : a.toNode ∈ splitA RS := Finset.mem_union_right _ (by simp)
  have hA1 : a.child RS.excluded ∈ splitA RS := Finset.mem_union_right _ (by simp)
  have hRT : ∀ x, x ∈ clRealizationNodes G T → x ∈ clLocalSupport RT := fun x hx =>
    cl_realization_mem_support RT hx
  have hB : ∀ j, clBoundaryNodes RT j ∈ clLocalSupport RT := clBoundaryNodes_mem_support RT
  have hrealU : ∀ x, x ∈ clRealizationNodes G (S ∪ T) ↔ x ∈ clRealizationNodes G S ∨ x ∈ clRealizationNodes G T :=
    split_realization hS hT hi hU
  have hb0 : clBoundaryNodes RU 0 = a.toNode := rfl
  have hb1 : clBoundaryNodes RU 1 = a.child RS.excluded := by
    show a.child RU.excluded = _
    rw [hex]
  have hb2 : clBoundaryNodes RU 2 = clBoundaryNodes RT 2 := by
    show c.child RU.positive = c.child RT.positive
    rw [hpn.1]
  have hb3 : clBoundaryNodes RU 3 = clBoundaryNodes RT 3 := by
    show c.child RU.negative = c.child RT.negative
    rw [hpn.2]
  apply Finset.Subset.antisymm
  · intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · rcases (hrealU x).mp h with h | h
      · exact Finset.mem_union_left _ (hRS x h)
      · exact Finset.mem_union_right _ (hRT x h)
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp h
      fin_cases j
      · exact Finset.mem_union_left _ (by rw [show clBoundaryNodes RU ((fun i => i) ⟨0, by omega⟩) = _ from hb0]; exact hA0)
      · exact Finset.mem_union_left _ (by rw [show clBoundaryNodes RU ((fun i => i) ⟨1, by omega⟩) = _ from hb1]; exact hA1)
      · exact Finset.mem_union_right _ (by rw [show clBoundaryNodes RU ((fun i => i) ⟨2, by omega⟩) = _ from hb2]; exact hB 2)
      · exact Finset.mem_union_right _ (by rw [show clBoundaryNodes RU ((fun i => i) ⟨3, by omega⟩) = _ from hb3]; exact hB 3)
  · intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact cl_realization_mem_support RU ((hrealU x).mpr (Or.inl h))
      · rcases Finset.mem_insert.mp h with rfl | h
        · exact clBoundaryNodes_mem_support RU 0
        · rw [Finset.mem_singleton.mp h]
          exact hb1 ▸ clBoundaryNodes_mem_support RU 1
    · rcases Finset.mem_union.mp h with h | h
      · exact cl_realization_mem_support RU ((hrealU x).mpr (Or.inr h))
      · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp h
        fin_cases j
        · exact cl_realization_mem_support RU ((hrealU _).mpr (Or.inr
            ((branch_mem_clRealizationNodes b).mpr hT.2.1)))
        · have : b.child RT.excluded ∈ clRealizationNodes G S := by
            rw [hkb]
            exact cl_child_mem_realization_of_internal hS RS hS.2.2.1 RS.kept ((RS.lower RS.kept).mpr rfl)
          exact cl_realization_mem_support RU ((hrealU _).mpr (Or.inl this))
        · exact hb2 ▸ clBoundaryNodes_mem_support RU 2
        · exact hb3 ▸ clBoundaryNodes_mem_support RU 3

theorem split_overlap (RS : CLRegionData G S a b) (RT : CLRegionData G T b c) {x : GNode G.tree}
    (hxA : x ∈ splitA RS) (hxB : x ∈ clLocalSupport RT) : x = b.toNode ∨ x = b.child RS.kept := by
  have hkb := split_excluded_b hS hT hi hU RS RT
  obtain ⟨_, hA2⟩ := splitA_desc hS hT hi hU RS hxA
  have hcT : c.toNode ∈ clRealizationNodes G T := (branch_mem_clRealizationNodes c).mpr hT.2.2.1
  obtain ⟨hbc, hbc2, _⟩ := (mem_real_iff hT RT _).mp hcT
  have hbx : b.toNode.IsDesc x := by
    unfold clLocalSupport at hxB
    rcases Finset.mem_union.mp hxB with h | h
    · exact ((mem_real_iff hT RT x).mp h).1
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp h
      fin_cases j
      · exact isDesc_refl' _
      · exact isDesc_child' b _
      · exact isDesc_trans' hbc (isDesc_child' c _)
      · exact isDesc_trans' hbc (isDesc_child' c _)
  rcases isDesc_cases b hbx with h | ⟨i, hi'⟩
  · exact Or.inl h
  · have hik : i = RS.kept := by
      by_contra hne
      exact hA2 i hne hi'
    subst hik
    right
    unfold clLocalSupport at hxB
    rcases Finset.mem_union.mp hxB with h | h
    · exact absurd hi' (hkb ▸ ((mem_real_iff hT RT x).mp h).2.1)
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp h
      fin_cases j
      · exfalso
        have hh : b.toNode.IsDesc (b.child RS.kept) ∧ (b.child RS.kept).IsDesc b.toNode := ⟨isDesc_child' b _, hi'⟩
        have := isDesc_antisymm' hh.1 hh.2
        have h1 : (b.toNode).1.2.length = (b.child RS.kept).1.2.length := by rw [this]
        simp [GBranch.child, GBranch.toNode] at h1
      · show b.child RT.excluded = _
        rw [hkb]
      · exfalso
        rcases isDesc_child_cases c RT.positive (show (b.child RS.kept).IsDesc (c.child RT.positive) from hi') with h | h
        · exact hbc2 (hkb ▸ h)
        · exact hT.2.2.2.1 (child_eq_child h)
      · exfalso
        rcases isDesc_child_cases c RT.negative (show (b.child RS.kept).IsDesc (c.child RT.negative) from hi') with h | h
        · exact hbc2 (hkb ▸ h)
        · exact hT.2.2.2.1 (child_eq_child h)

theorem splitA_node (RS : CLRegionData G S a b) {v : GBranch G.tree} (hv : v ∈ S) : v.toNode ∈ splitA RS :=
  Finset.mem_union_left _ ((branch_mem_clRealizationNodes v).mpr hv)

/-- The children of an atom of `S` other than the lower joint `b` lie in `splitA`. -/
theorem splitA_child (RS : CLRegionData G S a b) {v : GBranch G.tree} (hv : v ∈ S) (hvb : v ≠ b) (i : Fin 3) :
    v.child i ∈ splitA RS := by
  by_cases hint : i.succ ∈ Mole.internalPositions G S v
  · exact Finset.mem_union_left _ (cl_child_mem_realization_of_internal hS RS hv i hint)
  · by_cases hva : v = a
    · subst hva
      have : i = RS.excluded := by
        by_contra hne
        exact hint ((RS.upper i).mpr hne)
      subst this
      exact Finset.mem_union_right _ (by simp)
    · exfalso
      have hd := hS.2.2.2.2.2.2.2.2.1 v hv hva hvb
      have he : Mole.internalPositions G S v = Finset.univ :=
        Finset.eq_univ_of_card _ ((Mole.card_internalPositions G S v).trans hd)
      exact hint (he ▸ Finset.mem_univ _)

end Split2

end WaveTurbulence.VineEstS4
