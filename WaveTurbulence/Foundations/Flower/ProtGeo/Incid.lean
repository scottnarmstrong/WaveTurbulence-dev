/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtGeo.Sel

/-! # D2b PROT-GEO (7): item (iv), regular kernels at a selected residual vertex (o73 §17)

A regular kernel has at most two time arguments: for a paired tree, the parent of its root and its lone position;
for a couple, the parents of its two roots (`TreeBoundary`, `CplBoundary`).
* `card_boundary_le_seven`: in a family of objects with pairwise disjoint root sets and distinct lone positions, at
  most `4 ≤ 7` objects have a given vertex as a time argument (the lone position, or a root at one of its three
  children).
* `selBoundary_tree`, `selBoundary_cpl`: an object with a selected vertex as a time argument contains no selected
  branching vertex (one selection per tree; a couple containing a stem vertex is a cap couple, o73 Prop 3.1).
* `objCfg_selBoundary_tree`, `objCfg_selBoundary_cpl`: such a protected object has configuration `none` or `term`, so
  the `θ = 1/4` branch of `ProtBoundAt` applies to it. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.Flower.MkDefs
  WaveTurbulence.Flower.ProtDefs

namespace WaveTurbulence.Flower.ProtGeo

variable {w : ℕ}

/-- The parent address of a non-root address. -/
def parentAddr (r : Fin w × Path) : Fin w × Path := (r.1, r.2.dropLast)

/-- Boundary arguments of a paired-tree object (chain `X` at root `u`): its lone position, or the parent of its root. -/
def TreeBoundary (X : RegChain) (u v : Fin w × Path) : Prop :=
  v = addrExt u X.lonePath ∨ (u.2 ≠ [] ∧ v = parentAddr u)

/-- Boundary arguments of a couple object (roots `a`, `b`): the parents of its roots. -/
def CplBoundary (a b v : Fin w × Path) : Prop :=
  (a.2 ≠ [] ∧ v = parentAddr a) ∨ (b.2 ≠ [] ∧ v = parentAddr b)

/-- A vertex is a time argument of an object with root set `R` and optional lone position `P`. -/
def IsBoundaryOf (v : Fin w × Path) (R : Finset (Fin w × Path)) (P : Option (Fin w × Path)) : Prop :=
  P = some v ∨ ∃ r ∈ R, r.2 ≠ [] ∧ parentAddr r = v

theorem eq_child_of_parentAddr {r v : Fin w × Path} (hr : r.2 ≠ []) (h : parentAddr r = v) :
    r = addrExt v [r.2.getLast hr] := by
  subst h
  exact Prod.ext rfl (List.dropLast_append_getLast hr).symm

/-- **o73 §17, incidence count.** At most `7` (indeed `4`) objects of a family with pairwise disjoint root sets and
distinct lone positions have a given vertex as a time argument. -/
theorem card_boundary_le_seven {ι : Type*} (O : Finset ι) (R : ι → Finset (Fin w × Path))
    (P : ι → Option (Fin w × Path)) (hR : ∀ i ∈ O, ∀ j ∈ O, i ≠ j → Disjoint (R i) (R j))
    (hP : ∀ i ∈ O, ∀ j ∈ O, P i = P j → (P i).isSome → i = j) (v : Fin w × Path) :
    (O.filter fun i => IsBoundaryOf v (R i) (P i)).card ≤ 7 := by
  let A := O.filter fun i => P i = some v
  let B : Fin 3 → Finset ι := fun k => O.filter fun i => addrExt v [k] ∈ R i
  have hsub : (O.filter fun i => IsBoundaryOf v (R i) (P i)) ⊆ A ∪ (Finset.univ : Finset (Fin 3)).biUnion B := by
    intro i hi
    obtain ⟨hiO, hb⟩ := Finset.mem_filter.mp hi
    rcases hb with hb | ⟨r, hr, hr0, hrv⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hiO, hb⟩)
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r.2.getLast hr0, Finset.mem_univ _, ?_⟩)
      refine Finset.mem_filter.mpr ⟨hiO, ?_⟩
      rw [← eq_child_of_parentAddr hr0 hrv]; exact hr
  have hA : A.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro i hi j hj
    obtain ⟨hiO, hi'⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjO, hj'⟩ := Finset.mem_filter.mp hj
    exact hP i hiO j hjO (hi'.trans hj'.symm) (by rw [hi']; rfl)
  have hB : ∀ k, (B k).card ≤ 1 := by
    intro k
    rw [Finset.card_le_one]
    intro i hi j hj
    obtain ⟨hiO, hi'⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjO, hj'⟩ := Finset.mem_filter.mp hj
    by_contra hne
    exact Finset.disjoint_left.mp (hR i hiO j hjO hne) hi' hj'
  calc (O.filter fun i => IsBoundaryOf v (R i) (P i)).card
      ≤ (A ∪ (Finset.univ : Finset (Fin 3)).biUnion B).card := Finset.card_le_card hsub
    _ ≤ A.card + ((Finset.univ : Finset (Fin 3)).biUnion B).card := Finset.card_union_le _ _
    _ ≤ 1 + ∑ k : Fin 3, (B k).card := Nat.add_le_add hA Finset.card_biUnion_le
    _ ≤ 1 + ∑ _k : Fin 3, 1 := Nat.add_le_add_left (Finset.sum_le_sum fun k _ => hB k) _
    _ ≤ 7 := by simp

/-! ## No other selected vertex inside a kernel at a selected vertex -/

theorem parentAddr_ne_addrExt {u : Fin w × Path} (hu : u.2 ≠ []) (q : Path) : parentAddr u ≠ addrExt u q := by
  intro h
  have := congrArg (fun x : Fin w × Path => x.2.length) h
  simp only [parentAddr, addrExt, List.length_dropLast, List.length_append] at this
  have : u.2.length ≠ 0 := fun h0 => hu (List.length_eq_zero_iff.mp h0)
  omega

variable {LG : LayeredGarden w} {J : Finset (Fin w)} {kSel : Fin w → Option ℕ}

/-- **o73 §17, paired trees.** A paired-tree object with a selected time argument has no selected branching
vertex. -/
theorem selBoundary_tree {X : RegChain} {ζ : ℤˣ} {u : Fin w × Path} {v : GBranch LG.garden.tree}
    (hv : v ∈ selSetCap LG J kSel) (hvb : TreeBoundary X u v.1) :
    ∀ b ∈ selSetCap LG J kSel, b.1 ∉ branchAddresses (X.plug ζ .leaf) u := by
  intro b hb hbO
  obtain ⟨q, hq, hbq⟩ := mem_branchAddresses'.mp hbO
  have hvt : v.1.1 = u.1 := by
    rcases hvb with h | ⟨-, h⟩ <;> rw [h] <;> rfl
  have hbt : b.1.1 = u.1 := by rw [hbq]; rfl
  have he := selSetCap_eq_of_tree hb hv (hbt.trans hvt.symm)
  subst he
  rcases hvb with h | ⟨hu, h⟩
  · rw [hbq] at h
    have hq' := addrExt_injective u h
    exact lone_not_prefix_branch X ζ hq (hq' ▸ List.prefix_refl _)
  · rw [hbq] at h
    exact parentAddr_ne_addrExt hu q h.symm

/-- **o73 §17, couples.** A couple object with a selected time argument has no selected branching vertex. -/
theorem selBoundary_cpl (hcap : ∀ j ∈ J, LG.garden.tree j = TTree.leaf) {Q : RegCpl} {a b : Fin w × Path}
    (hQ : Q.wf = true) (hE : Embeds LG.garden Q a b) {v : GBranch LG.garden.tree}
    (hv : v ∈ selSetCap LG J kSel) (hvb : CplBoundary a b v.1) :
    ∀ b' ∈ selSetCap LG J kSel, b'.1 ∉ branchAddresses Q.trees.1 a ∪ branchAddresses Q.trees.2 b := by
  intro b' hb' hbO
  have hm : MeetsStem LG J (branchAddresses Q.trees.1 a ∪ branchAddresses Q.trees.2 b) :=
    ⟨b', hbO, (selSetCap_spec hb').2.2.1⟩
  -- the parent of a root `x` in whose subtree `b'` lies is selected in the same tree, hence equals `b'`
  have key : ∀ (x : Fin w × Path) (T : TTree), b'.1 ∈ branchAddresses T x → x.2 ≠ [] →
      v.1 = parentAddr x → False := by
    intro x T hx hx0 hvx
    obtain ⟨q, -, hq⟩ := mem_branchAddresses'.mp hx
    have he := selSetCap_eq_of_tree hb' hv (by rw [hq, hvx]; rfl)
    rw [he, hvx] at hq
    exact parentAddr_ne_addrExt hx0 q hq
  obtain ⟨X, c, ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩⟩ := embeds_stem_cap hcap hQ hE hm
  · have hb2 : b'.1 ∈ branchAddresses (RegCpl.type2 X .nil .triv).trees.1 a := by
      rcases Finset.mem_union.mp hbO with h | h
      · exact h
      · simp [RegCpl.trees, RegChain.plug, branchAddresses, TTree.branching] at h
    rcases hvb with ⟨ha, hva⟩ | ⟨hb0, -⟩
    · exact key a _ hb2 ha hva
    · exact hb0 rfl
  · have hb2 : b'.1 ∈ branchAddresses (RegCpl.type2 .nil X .triv).trees.2 b := by
      rcases Finset.mem_union.mp hbO with h | h
      · simp [RegCpl.trees, RegChain.plug, branchAddresses, TTree.branching] at h
      · exact h
    rcases hvb with ⟨ha0, -⟩ | ⟨hb, hvb⟩
    · exact ha0 rfl
    · exact key b _ hb2 hb hvb

/-- **θ = 1/4 applies at a selected time argument (paired trees).** -/
theorem objCfg_selBoundary_tree {pat : Fin w → FixPat} (hplain : ∀ j, (kSel j).isSome → pat j = FixPat.plain)
    {X : RegChain} {u : Fin w × Path} {v : GBranch LG.garden.tree} (hv : v ∈ selSetCap LG J kSel)
    (hvb : TreeBoundary X u v.1) : objCfg LG J pat X u = .none ∨ objCfg LG J pat X u = .term := by
  have hvt : v.1.1 = u.1 := by
    rcases hvb with h | ⟨-, h⟩ <;> rw [h] <;> rfl
  rw [objCfg_of_sel hplain hv hvt]
  split_ifs <;> simp

/-- **θ = 1/4 applies at a selected time argument (cap couples:** the time argument is the parent of the subtree
root `u`). -/
theorem objCfg_selBoundary_cpl {pat : Fin w → FixPat} (hplain : ∀ j, (kSel j).isSome → pat j = FixPat.plain)
    {X : RegChain} {u : Fin w × Path} {v : GBranch LG.garden.tree} (hv : v ∈ selSetCap LG J kSel)
    (hu : u.2 ≠ []) (hvb : v.1 = parentAddr u) :
    objCfg LG J pat X u = .none ∨ objCfg LG J pat X u = .term :=
  objCfg_selBoundary_tree hplain hv (Or.inr ⟨hu, hvb⟩)

end WaveTurbulence.Flower.ProtGeo
