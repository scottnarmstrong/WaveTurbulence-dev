/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepUG2
import Mathlib.Tactic

/-!
# S2 REPRESENTS, UnitGap (5): every balanced boundary has an interior (local decorations exist)

`exists_clLocalDecoration`: for a unit `u` and boundary labels `n : Fin 4 → ℤ^d` with the signed balance
`ζ_u (n 0 - n 1) = n 2 - n 3`, there is a `CLLocalDecoration` with the boundary momenta `base + latticePoint L (n j)`.
Construction (no flows): with the signed labels `s(x) = sign(x) κ(x)` additive over the children, take
`s(x) = Σ_{crown nodes y below x} sign(y) n_y` and `κ(x) = sign(x) s(x)`; internal leaves get `0`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Represents
open Finset TTree WaveTurbulence WaveTurbulence.Mole WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine

variable {w d : ℕ} {S : Garden w}

/-- A leaf has no strict descendants (for arbitrary nodes). -/
theorem leaf_isDesc_eq {ℓ : GLeaf S.tree} {y : GNode S.tree} (h : ℓ.toNode.IsDesc y) : y = ℓ.toNode := by
  obtain ⟨hj, r, hr⟩ := h
  have hj' : ℓ.1.1 = y.1.1 := hj
  have hr' : ℓ.1.2 ++ r = y.1.2 := hr
  rcases r with _ | ⟨i, r⟩
  · rw [List.append_nil] at hr'
    exact Subtype.ext (Prod.ext hj'.symm hr'.symm)
  · exfalso
    have hn : ℓ.1.2 ++ [i] ∈ (S.tree ℓ.1.1).nodes := by
      refine TTree.mem_nodes_of_prefix _ (q := y.1.2) ?_ ⟨r, ?_⟩
      · rw [hj']
        exact y.2
      · rw [← hr']
        simp
    exact TTree.not_mem_branching_of_mem_leaves _ ℓ.2 (TTree.branching_of_append_mem _ hn)

/-- Exactly one child of `v` lies above a strict descendant `y` of `v`. -/
theorem desc_child_count (v : GBranch S.tree) (y : GNode S.tree) (hne : y ≠ v.toNode) :
    (∑ i : Fin 3, if (v.child i).IsDesc y then (1 : ℤ) else 0) = if v.toNode.IsDesc y then 1 else 0 := by
  classical
  by_cases hv : v.toNode.IsDesc y
  · rw [if_pos hv]
    obtain ⟨hj, r, hr⟩ := hv
    have hj' : v.1.1 = y.1.1 := hj
    have hr' : v.1.2 ++ r = y.1.2 := hr
    rcases r with _ | ⟨i0, r'⟩
    · rw [List.append_nil] at hr'
      exact absurd (Subtype.ext (Prod.ext hj'.symm hr'.symm)) hne
    · have hdesc : ∀ i : Fin 3, (v.child i).IsDesc y ↔ i = i0 := by
        intro i
        constructor
        · rintro ⟨-, h2⟩
          have h2' : v.1.2 ++ [i] <+: y.1.2 := h2
          rw [← hr'] at h2'
          have := (List.prefix_append_right_inj v.1.2).mp h2'
          simpa using this
        · rintro rfl
          refine ⟨hj', r', ?_⟩
          change v.1.2 ++ [i] ++ r' = y.1.2
          rw [← hr']
          simp
      simp only [hdesc]
      simp
  · rw [if_neg hv]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg]
    intro h
    exact hv ((GBranch.isDesc_child v i).trans h)

/-- The three crown nodes `u11, u21, u22` as a `Fin 3`-family. -/
noncomputable def crownNode (u : CLBlock S) (k : Fin 3) : GNode S.tree := bnodes u k.succ

theorem crownNode_mem (u : CLBlock S) (k : Fin 3) : crownNode u k ∈ crownSet u := by
  fin_cases k
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem crownNode_inj (u : CLBlock S) : Function.Injective (crownNode u) := by
  obtain ⟨h1, h2, h3⟩ := crown_distinct u
  intro k k' h
  fin_cases k <;> fin_cases k' <;> first | rfl | (exfalso; first | exact h1 h | exact h2 h | exact h3 h | exact h1 h.symm | exact h2 h.symm | exact h3 h.symm)

theorem crownNode_not_real (u : CLBlock S) (k : Fin 3) : crownNode u k ∉ clRealizationNodes S u.atoms :=
  crown_not_real u (crownNode_mem u k)

theorem crownNode_not_isDesc_real (u : CLBlock S) (k : Fin 3) {x : GNode S.tree}
    (hx : x ∈ clRealizationNodes S u.atoms) : ¬ (crownNode u k).IsDesc x := by
  have h := (real_iff u x).mp hx
  fin_cases k
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

theorem real_isDesc_crownNode (u : CLBlock S) (k : Fin 3) : u.upper.toNode.IsDesc (crownNode u k) := by
  fin_cases k
  · exact GBranch.isDesc_child _ _
  · exact (real_desc u ((branch_real_iff u u.lower).mpr (lower_mem u))).trans (GBranch.isDesc_child _ _)
  · exact (real_desc u ((branch_real_iff u u.lower).mpr (lower_mem u))).trans (GBranch.isDesc_child _ _)

theorem crownNode_isDesc_iff (u : CLBlock S) (k k' : Fin 3) :
    (crownNode u k).IsDesc (crownNode u k') ↔ k = k' := by
  constructor
  · intro h
    have hm := crownNode_mem u k'
    -- `crownNode u k'` is a child of an atom of `u`
    have key : ∃ (v : GBranch S.tree) (i : Fin 3), v ∈ u.atoms ∧ crownNode u k' = v.child i := by
      fin_cases k'
      · exact ⟨u.upper, _, upper_mem u, rfl⟩
      · exact ⟨u.lower, _, lower_mem u, rfl⟩
      · exact ⟨u.lower, _, lower_mem u, rfl⟩
    obtain ⟨v, i, hv, he⟩ := key
    rw [he] at h
    rcases (isDesc_child_iff v i).mp h with h1 | h1
    · exact crownNode_inj u (h1.trans he.symm)
    · exact absurd h1 (crownNode_not_isDesc_real u k ((branch_real_iff u v).mpr hv))
  · rintro rfl
    exact GNode.isDesc_refl _

/-- The signed crown sum below `x`. -/
noncomputable def crownVal (u : CLBlock S) (n : Fin 4 → (Fin d → ℤ)) (x : GNode S.tree) : Fin d → ℤ :=
  ∑ k : Fin 3, if x.IsDesc (crownNode u k) then ((S.sign (crownNode u k) : ℤˣ) : ℤ) • n k.succ else 0

/-- The local labels. -/
noncomputable def sdec (u : CLBlock S) (n : Fin 4 → (Fin d → ℤ)) (x : GNode S.tree) : Fin d → ℤ :=
  ((S.sign x : ℤˣ) : ℤ) • crownVal u n x

theorem crownVal_branch (u : CLBlock S) (n : Fin 4 → (Fin d → ℤ)) {v : GBranch S.tree} (hv : v ∈ u.atoms) :
    crownVal u n v.toNode = ∑ i : Fin 3, crownVal u n (v.child i) := by
  classical
  have hreal := (branch_real_iff u v).mpr hv
  unfold crownVal
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hne : crownNode u k ≠ v.toNode := fun h => crownNode_not_real u k (h ▸ hreal)
  have hc := desc_child_count v (crownNode u k) hne
  by_cases hd : v.toNode.IsDesc (crownNode u k)
  · rw [if_pos hd]
    rw [if_pos hd] at hc
    have : ∀ i : Fin 3, (if (v.child i).IsDesc (crownNode u k) then ((S.sign (crownNode u k) : ℤˣ) : ℤ) • n k.succ else 0) =
        (if (v.child i).IsDesc (crownNode u k) then (1 : ℤ) else 0) • (((S.sign (crownNode u k) : ℤˣ) : ℤ) • n k.succ) := by
      intro i; split_ifs <;> simp
    simp only [this]
    rw [← Finset.sum_smul, hc, one_smul]
  · rw [if_neg hd]
    refine (Finset.sum_eq_zero fun i _ => ?_).symm
    rw [if_neg]
    intro h
    exact hd ((GBranch.isDesc_child v i).trans h)

theorem sdec_conservation (u : CLBlock S) (n : Fin 4 → (Fin d → ℤ)) {v : GBranch S.tree} (hv : v ∈ u.atoms) :
    sdec u n v.toNode = sdec u n (v.child 0) - sdec u n (v.child 1) + sdec u n (v.child 2) := by
  have h := crownVal_branch u n hv
  rw [Fin.sum_univ_three] at h
  have s0 : S.sign (v.child 0) = S.sign v.toNode := by
    rw [WaveTurbulence.Mole.child_sign_formula]; simp
  have s1 : S.sign (v.child 1) = -S.sign v.toNode := by
    rw [WaveTurbulence.Mole.child_sign_formula]; simp
  have s2 : S.sign (v.child 2) = S.sign v.toNode := by
    rw [WaveTurbulence.Mole.child_sign_formula]; simp
  unfold sdec
  rw [h, s0, s1, s2]
  simp only [Units.val_neg, neg_smul, smul_add, sub_neg_eq_add]

theorem crownVal_leaf (u : CLBlock S) (n : Fin 4 → (Fin d → ℤ)) {ℓ : GLeaf S.tree}
    (hℓ : ℓ.toNode ∈ clRealizationNodes S u.atoms) : crownVal u n ℓ.toNode = 0 := by
  unfold crownVal
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [if_neg]
  intro h
  exact crownNode_not_real u k (by rw [leaf_isDesc_eq h]; exact hℓ)

theorem sdec_bnode (u : CLBlock S) (n : Fin 4 → (Fin d → ℤ)) (k : Fin 3) :
    sdec u n (crownNode u k) = n k.succ := by
  classical
  unfold sdec crownVal
  have : ∀ k' : Fin 3, (if (crownNode u k).IsDesc (crownNode u k') then
      ((S.sign (crownNode u k') : ℤˣ) : ℤ) • n k'.succ else 0) =
      if k' = k then ((S.sign (crownNode u k) : ℤˣ) : ℤ) • n k.succ else 0 := by
    intro k'
    by_cases h : k' = k
    · subst h; simp [GNode.isDesc_refl]
    · rw [if_neg h, if_neg]
      intro hd
      exact h ((crownNode_isDesc_iff u k k').mp hd).symm
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← mul_smul]
  have : ((S.sign (crownNode u k) : ℤˣ) : ℤ) * ((S.sign (crownNode u k) : ℤˣ) : ℤ) = 1 := by
    rcases Int.units_eq_one_or (S.sign (crownNode u k)) with h | h <;> rw [h] <;> simp
  rw [this, one_smul]

theorem sdec_upper (u : CLBlock S) (n : Fin 4 → (Fin d → ℤ))
    (hbal : ((S.sign u.upper.toNode : ℤˣ) : ℤ) • (n 0 - n 1) = n 2 - n 3) :
    sdec u n u.upper.toNode = n 0 := by
  classical
  unfold sdec crownVal
  simp only [real_isDesc_crownNode, if_true, Fin.sum_univ_three]
  have e1 : S.sign (crownNode u 0) = S.sign u.upper.toNode := by
    show S.sign (u.upper.child (regionOf u).excluded) = _
    rw [WaveTurbulence.Mole.child_sign_formula, if_neg (regionOf u).excluded_ne_middle]
  have e2 : S.sign (crownNode u 1) = 1 := (regionOf u).positive_sign
  have e3 : S.sign (crownNode u 2) = -1 := (regionOf u).negative_sign
  rw [e1, e2, e3]
  have hz : ∀ k : Fin d, n 0 k = n 1 k + ((S.sign u.upper.toNode : ℤˣ) : ℤ) * (n 2 k - n 3 k) := by
    intro k
    have := congrFun hbal k
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at this
    rcases Int.units_eq_one_or (S.sign u.upper.toNode) with h | h <;> rw [h] at this ⊢ <;> simp at this ⊢ <;> omega
  funext k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Units.val_one, Units.val_neg, Pi.neg_apply]
  rw [hz k]
  rcases Int.units_eq_one_or (S.sign u.upper.toNode) with h | h <;> rw [h] <;> simp <;> ring

/-- **Local decorations exist for every balanced boundary.** -/
theorem exists_clLocalDecoration (u : CLBlock S) (L : ℝ) (base : Mom d) (n : Fin 4 → (Fin d → ℤ))
    (hbal : ((S.sign u.upper.toNode : ℤˣ) : ℤ) • (n 0 - n 1) = n 2 - n 3) :
    Nonempty (CLLocalDecoration (regionOf u) L base (fun j => base + latticePoint L (n j))) := by
  classical
  have hsupp : ∀ x, x ∈ clRealizationNodes S u.atoms → x ∈ clLocalSupport (regionOf u) :=
    fun x hx => cl_realization_mem_support _ hx
  have hext : ∀ x (hx : x ∈ clLocalSupport (regionOf u)),
      clExtendIndices (regionOf u) (fun y : ↥(clLocalSupport (regionOf u)) => sdec u n y.1) x = sdec u n x :=
    fun x hx => clExtendIndices_apply _ _ x hx
  refine ⟨⟨fun y => sdec u n y.1, ?_, ?_, ?_⟩⟩
  · intro v hv
    rw [hext _ (hsupp _ ((branch_real_iff u v).mpr hv)), hext _ (cl_child_mem_support u.isBlock _ hv 0),
      hext _ (cl_child_mem_support u.isBlock _ hv 1), hext _ (cl_child_mem_support u.isBlock _ hv 2)]
    exact sdec_conservation u n hv
  · intro ℓ hℓ
    have hℓ' := (leaf_mem_clRealizationNodes ℓ).mpr hℓ
    have hℓ2 := (leaf_mem_clRealizationNodes (S.pair ℓ)).mpr ((Mole.internal_leaf_pair_iff S u.atoms ℓ).mpr hℓ)
    rw [hext _ (hsupp _ hℓ'), hext _ (hsupp _ hℓ2)]
    unfold sdec
    rw [crownVal_leaf u n hℓ', crownVal_leaf u n hℓ2]
    simp
  · intro j
    have hj : ∀ j, clExtendIndices (regionOf u) (fun y : ↥(clLocalSupport (regionOf u)) => sdec u n y.1)
        (clBoundaryNodes (regionOf u) j) = n j := by
      intro j
      rw [hext _ (clBoundaryNodes_mem_support _ j)]
      fin_cases j
      · exact sdec_upper u n hbal
      · exact sdec_bnode u n 0
      · exact sdec_bnode u n 1
      · exact sdec_bnode u n 2
    rw [hj j]

end WaveTurbulence.Represents
