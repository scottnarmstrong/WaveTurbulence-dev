/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtGeo.Couple

/-! # D2b PROT-GEO (9): pinned objects that meet no stem branching node (o104 Prop 7.2 (G1)(ii), (P8))

Every `fixCap` pin that is not a capped stem node is the root of its tree (`dRoot`) or the pinned child
`m = 𝔣^pr ++ [i]` (`dChild i`). Hence a regular object that meets no capped stem branching node carries at most its
root(s) as pinned vertices (`offStem_pin_root_tree`, `offStem_pin_root_cpl`): these are the root-trace objects of
o104 Prop 7.4 ((P8)), with the root pinned at `t` (`dRoot`) or at `s` (`dChild`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.Flower.MkDefs

namespace WaveTurbulence.Flower.ProtGeo

variable {w : ℕ} {LG : LayeredGarden w} {J : Finset (Fin w)}

theorem fp_onStem {c : GBranch LG.garden.tree} (hc : IsCapFlowerParent LG J c) : OnCapStem LG J c.toNode := by
  obtain ⟨f, hf, h1, i, h2⟩ := hc
  exact ⟨f, hf, h1.symm, by show c.1.2 <+: f.1.2; rw [h2]; exact List.prefix_append _ _⟩

/-- **Off-stem pins.** A pinned branch that is not a capped stem node is a tree root (`dRoot`) or a pinned child
`c ++ [i]` of a capped flower parent `c` (`dChild i`). -/
theorem offStem_pin {pat : Fin w → FixPat} {t s : ℝ} {b : GBranch LG.garden.tree}
    (hpin : (fixCap LG J pat t s b).isSome) (hns : ¬ OnCapStem LG J b.toNode) :
    (pat b.1.1 = FixPat.dRoot ∧ b.1.2 = [] ∧ fixCap LG J pat t s b = some t) ∨
      ∃ (i : Fin 3) (c : GBranch LG.garden.tree), pat b.1.1 = FixPat.dChild i ∧ IsCapFlowerParent LG J c ∧
        b.1 = (c.1.1, c.1.2 ++ [i]) ∧ fixCap LG J pat t s b = some s := by
  unfold fixCap at hpin ⊢
  have hnf : ¬ IsCapFlowerParent LG J b := fun h => hns (fp_onStem h)
  rw [ite_eq_right hnf] at hpin ⊢
  cases hp : pat b.1.1 with
  | plain => simp only [hp] at hpin; simp at hpin
  | dRoot =>
    simp only [hp] at hpin ⊢
    by_cases h0 : b.1.2 = []
    · left; simp [h0]
    · simp [h0] at hpin
  | dParent =>
    simp only [hp] at hpin
    by_cases hc : ∃ c : GBranch LG.garden.tree, IsCapFlowerParent LG J c ∧ c.IsChildOf b
    · exfalso
      obtain ⟨c, hcf, hc1, k, hck⟩ := hc
      obtain ⟨f, hf, hfd⟩ := fp_onStem hcf
      have h2 : c.1.2 <+: f.1.2 := hfd.2
      rw [hck] at h2
      exact hns ⟨f, hf, hc1.symm.trans hfd.1, (List.prefix_append _ _).trans h2⟩
    · simp [hc] at hpin
  | dChild i =>
    simp only [hp] at hpin ⊢
    by_cases hc : ∃ c : GBranch LG.garden.tree, IsCapFlowerParent LG J c ∧ b.1.1 = c.1.1 ∧ b.1.2 = c.1.2 ++ [i]
    · obtain ⟨c, hcf, h1, h2⟩ := hc
      refine Or.inr ⟨i, c, rfl, hcf, Prod.ext h1 h2, ?_⟩
      rw [ite_eq_left ⟨c, hcf, h1, h2⟩]
    · simp [hc] at hpin

/-- **(G1)(ii), paired trees.** A paired-tree object meeting no capped stem branching node has no pinned branching
vertex other than its root. -/
theorem offStem_pin_root_tree {pat : Fin w → FixPat} {t s : ℝ} {X : RegChain} {ζ : ℤˣ} {u : Fin w × Path}
    (hns : ¬ MeetsStem LG J (branchAddresses (X.plug ζ .leaf) u)) {b : GBranch LG.garden.tree}
    (hb : b.1 ∈ branchAddresses (X.plug ζ .leaf) u) (hpin : (fixCap LG J pat t s b).isSome) : b.1 = u := by
  have hbns : ¬ OnCapStem LG J b.toNode := fun h' => hns ⟨b, hb, h'⟩
  obtain ⟨q, hq, hbq⟩ := mem_branchAddresses'.mp hb
  rcases offStem_pin hpin hbns with ⟨-, h0, -⟩ | ⟨i, c, -, hcf, hbc, -⟩
  · rw [hbq] at h0 ⊢
    have : q = [] := (List.append_eq_nil_iff.mp h0).2
    rw [this, addrExt_nil']
  · by_cases hq0 : q = []
    · rw [hbq, hq0, addrExt_nil']
    · exfalso
      have hqd : q.dropLast ++ [q.getLast hq0] = q := List.dropLast_append_getLast hq0
      have hdb : q.dropLast ∈ (X.plug ζ .leaf).branching :=
        Comb.TreePath.branching_of_append_mem _ (by rw [hqd]; exact TTree.branching_subset_nodes _ hq)
      have hce : c.1 = addrExt u q.dropLast := by
        have e : (u.1, u.2 ++ q) = (c.1.1, c.1.2 ++ [i]) := hbq.symm.trans hbc
        simp only [Prod.mk.injEq] at e
        rw [← hqd, ← List.append_assoc] at e
        exact Prod.ext e.1.symm (List.append_inj' e.2 rfl).1.symm
      exact hns ⟨c, by rw [hce]; exact addrExt_mem_branchAddresses.mpr hdb, fp_onStem hcf⟩

/-- **(G1)(ii), couples.** A couple object meeting no capped stem branching node has no pinned branching vertex
other than its roots. -/
theorem offStem_pin_root_cpl {pat : Fin w → FixPat} {t s : ℝ} {Q : RegCpl} {a b : Fin w × Path}
    (hns : ¬ MeetsStem LG J (branchAddresses Q.trees.1 a ∪ branchAddresses Q.trees.2 b))
    {v : GBranch LG.garden.tree} (hv : v.1 ∈ branchAddresses Q.trees.1 a ∪ branchAddresses Q.trees.2 b)
    (hpin : (fixCap LG J pat t s v).isSome) : v.1 = a ∨ v.1 = b := by
  have hvns : ¬ OnCapStem LG J v.toNode := fun h' => hns ⟨v, hv, h'⟩
  -- the parent of a non-root pinned child is a branching vertex of the same tree of the object
  have key : ∀ (x : Fin w × Path) (T : TTree), branchAddresses T x ⊆
      branchAddresses Q.trees.1 a ∪ branchAddresses Q.trees.2 b → v.1 ∈ branchAddresses T x → v.1 = x := by
    intro x T hsub hx
    obtain ⟨q, hq, hvq⟩ := mem_branchAddresses'.mp hx
    rcases offStem_pin hpin hvns with ⟨-, h0, -⟩ | ⟨i, c, -, hcf, hvc, -⟩
    · rw [hvq] at h0 ⊢
      have : q = [] := (List.append_eq_nil_iff.mp h0).2
      rw [this, addrExt_nil']
    · by_cases hq0 : q = []
      · rw [hvq, hq0, addrExt_nil']
      · exfalso
        have hqd : q.dropLast ++ [q.getLast hq0] = q := List.dropLast_append_getLast hq0
        have hdb : q.dropLast ∈ T.branching :=
          Comb.TreePath.branching_of_append_mem _ (by rw [hqd]; exact TTree.branching_subset_nodes _ hq)
        have hce : c.1 = addrExt x q.dropLast := by
          have e : (x.1, x.2 ++ q) = (c.1.1, c.1.2 ++ [i]) := hvq.symm.trans hvc
          simp only [Prod.mk.injEq] at e
          rw [← hqd, ← List.append_assoc] at e
          exact Prod.ext e.1.symm (List.append_inj' e.2 rfl).1.symm
        exact hns ⟨c, hsub (by rw [hce]; exact addrExt_mem_branchAddresses.mpr hdb), fp_onStem hcf⟩
  rcases Finset.mem_union.mp hv with h1 | h1
  · exact Or.inl (key a _ Finset.subset_union_left h1)
  · exact Or.inr (key b _ Finset.subset_union_right h1)

end WaveTurbulence.Flower.ProtGeo
