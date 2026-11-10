/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkMark.Transport
public import WaveTurbulence.Foundations.IncohInst.Links.Coherence

/-! # CAPS-STABLE: paths and layer-`p` counts across a correspondence off a region

For a correspondence `I : OutIso LG LG' R R'` (B2b, `MkMark/Transport.lean`) with inverse `I'`:
* `OutIso.map_addrExt`: along an `R`-free path, `I.f (z ++ q) = I.f z ++ q`;
* `OutIso.free_image`: if the subtree below `z` avoids `R`, the subtree below `I.f z` avoids `R'`;
* `OutIso.map_rootFree`: an address whose ancestors all avoid `R` is fixed by `I.f`;
* `OutIso.full_image`: if every vertex of `R` in the tree of `z` lies below `z`, the same holds for `R'` and `z`.

With a layer transport off `R`, the layer-`p` counts below a node `z` are preserved in both situations
(`count_free`: the subtree below `z` avoids `R`; `count_full`: all of `R` in the tree of `z` lies below `z`, using
the top orders). These are the two cases of o75 Lemma 2(b) (labels rooted at vertices of `Π`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkMark WaveTurbulence.Reg.Skeleton
  WaveTurbulence.Links

namespace WaveTurbulence.Flower.CapsStable

variable {w : ℕ}

section Basic
variable {LG : LayeredGarden w}

theorem addrExt_nil (z : Address w) : addrExt z [] = z := by
  simp [addrExt]

theorem addrExt_append (z : Address w) (r q : TTree.Path) : addrExt z (r ++ q) = addrExt (addrExt z r) q := by
  simp [addrExt, List.append_assoc]

theorem nodeAt_prefix {z : Address w} {r q : TTree.Path} (h : NodeAt LG (addrExt z q)) (hr : r <+: q) :
    NodeAt LG (addrExt z r) :=
  TTree.mem_nodes_of_prefix _ h ((List.prefix_append_right_inj z.2).mpr hr)

theorem nodeAt_root {z : Address w} (h : NodeAt LG z) : NodeAt LG (z.1, []) :=
  TTree.mem_nodes_of_prefix _ h List.nil_prefix

/-- An address below `z` is `z` extended by the remaining path. -/
theorem eq_addrExt_of_prefix {z y : Address w} (h1 : z.1 = y.1) (h2 : z.2 <+: y.2) :
    y = addrExt z (y.2.drop z.2.length) := by
  obtain ⟨r, hr⟩ := h2
  refine Prod.ext h1.symm ?_
  show y.2 = z.2 ++ y.2.drop z.2.length
  rw [← hr, List.drop_left]

end Basic

/-! ## One correspondence -/

section One
variable {LG LG' : LayeredGarden w} {R R' : Set (Address w)} (I : OutIso LG LG' R R')

/-- **Along an `R`-free path the correspondence is a translation.** -/
theorem map_addrExt (z : Address w) :
    ∀ q : TTree.Path, NodeAt LG (addrExt z q) → (∀ r, r <+: q → addrExt z r ∉ R) →
      I.f (addrExt z q) = addrExt (I.f z) q := by
  intro q
  induction q using List.reverseRecOn with
  | nil => intro _ _; rw [addrExt_nil, addrExt_nil]
  | append_singleton r i ih =>
    intro hn hR
    have hpr : r <+: r ++ [i] := List.prefix_append _ _
    have hnr : NodeAt LG (addrExt z r) := nodeAt_prefix hn hpr
    have hRr : ∀ r', r' <+: r → addrExt z r' ∉ R := fun r' h => hR r' (h.trans hpr)
    have e := ih hnr hRr
    rw [addrExt_append] at hn ⊢
    rw [I.child (addrExt z r) i hnr (hRr r (List.prefix_refl _)) hn (by
      rw [← addrExt_append]; exact hR _ (List.prefix_refl _)), e, ← addrExt_append]

/-- An address whose ancestors all avoid `R` is fixed. -/
theorem map_rootFree {y : Address w} (hn : NodeAt LG y) (hR : ∀ r, r <+: y.2 → (y.1, r) ∉ R) :
    I.f y = y := by
  have hroot := nodeAt_root hn
  have hR0 : (y.1, ([] : TTree.Path)) ∉ R := hR [] List.nil_prefix
  have h1 := I.tree _ hroot hR0
  have h2 := (I.root _ hroot hR0).mpr rfl
  have hf0 : I.f (y.1, []) = (y.1, []) := Prod.ext h1 h2
  have e : addrExt (y.1, ([] : TTree.Path)) y.2 = y := by simp [addrExt]
  have := map_addrExt I (y.1, []) y.2 (by rw [e]; exact hn) (fun r hr => by
    simpa [addrExt] using hR r hr)
  rw [e, hf0] at this
  exact this

variable (I' : OutIso LG' LG R' R)

/-- **The image of an `R`-free subtree is `R'`-free.** -/
theorem free_image (hinv' : ∀ z, NodeAt LG z → z ∉ R → I'.f (I.f z) = z)
    {z : Address w} (hz : NodeAt LG z) (hzR : z ∉ R)
    (hfree : ∀ q, NodeAt LG (addrExt z q) → addrExt z q ∉ R) :
    ∀ q, NodeAt LG' (addrExt (I.f z) q) → addrExt (I.f z) q ∉ R' := by
  suffices H : ∀ n q, q.length ≤ n → NodeAt LG' (addrExt (I.f z) q) → addrExt (I.f z) q ∉ R' from
    fun q => H q.length q le_rfl
  intro n
  induction n with
  | zero =>
    intro q hq _
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hq), addrExt_nil]
    exact (I.node z hz hzR).2
  | succ n ih =>
    intro q hq hn hR'
    rcases List.eq_nil_or_concat q with h0 | ⟨r, i, hq0⟩
    · subst h0
      rw [addrExt_nil] at hR'
      exact (I.node z hz hzR).2 hR'
    rw [List.concat_eq_append] at hq0
    subst hq0
    have hrl : r.length ≤ n := by simp at hq; omega
    have hpr : r <+: r ++ [i] := List.prefix_append _ _
    have hnr : NodeAt LG' (addrExt (I.f z) r) := nodeAt_prefix hn hpr
    have hRr : ∀ r', r' <+: r → addrExt (I.f z) r' ∉ R' := fun r' h =>
      ih r' ((h.length_le).trans hrl) (nodeAt_prefix hnr h)
    have e : I'.f (addrExt (I.f z) r) = addrExt z r := by
      rw [map_addrExt I' (I.f z) r hnr hRr, hinv' z hz hzR]
    rw [addrExt_append] at hn hR'
    have hc := (I'.childR (addrExt (I.f z) r) i hnr (hRr r (List.prefix_refl _))).mp ⟨hn, hR'⟩
    rw [e, ← addrExt_append] at hc
    exact hfree _ hc.1 hc.2

/-- **If all of `R` in the tree of `z` lies below `z`, the same holds for `R'`** (the root path to `z` avoids `R`). -/
theorem full_image (J : OutIso LG' LG R' R) (hR' : RegionOK LG' R') {z : Address w}
    (hfull : ∀ y, NodeAt LG y → y.1 = z.1 → y ∈ R → z.2 <+: y.2) :
    ∀ y', NodeAt LG' y' → y'.1 = z.1 → y' ∈ R' → z.2 <+: y'.2 := by
  suffices H : ∀ n (y' : Address w), y'.2.length ≤ n → NodeAt LG' y' → y'.1 = z.1 → y' ∈ R' → z.2 <+: y'.2 from
    fun y' => H y'.2.length y' le_rfl
  intro n
  induction n with
  | zero =>
    intro y' hl hn _ hR
    exact absurd (List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)) (hR'.root y' hR hn)
  | succ n ih =>
    intro y' hl hn hj hR
    by_cases hex : ∃ r, r <+: y'.2.dropLast ∧ (y'.1, r) ∈ R'
    · obtain ⟨r, hr, hrR⟩ := hex
      have hr' : r <+: y'.2 := hr.trans (List.dropLast_prefix _)
      have hnr : NodeAt LG' (y'.1, r) := TTree.mem_nodes_of_prefix _ hn hr'
      have hrl : r.length ≤ n := by
        have := hr.length_le
        rw [List.length_dropLast] at this
        omega
      exact (ih (y'.1, r) hrl hnr hj hrR).trans hr'
    · push Not at hex
      have hne : y'.2 ≠ [] := hR'.root y' hR hn
      set u : Address w := (y'.1, y'.2.dropLast)
      have hy : y' = addrExt u [y'.2.getLast hne] := addrExt_parent hne
      have hnu : NodeAt LG' u := TTree.mem_nodes_of_prefix _ hn (List.dropLast_prefix _)
      have hfu : J.f u = u := map_rootFree J hnu (fun r hr => hex r hr)
      have hc := (J.childR u (y'.2.getLast hne) hnu (hex _ (List.prefix_refl _))).mp
        ⟨by rw [← hy]; exact hn, by rw [← hy]; exact hR⟩
      rw [hfu, ← hy] at hc
      exact hfull y' hc.1 hj hc.2

end One

/-! ## Top orders split at a node -/

/-- The count below `z` plus the count off the subtree is the top order. -/
theorem topCountBelow_add (L : LayeredGarden w) (p : ℕ) (z : GNode L.garden.tree) :
    L.topCountBelow p z + (Finset.univ.filter fun b : GBranch L.garden.tree =>
        b.1.1 = z.1.1 ∧ ¬ z.IsDesc b.toNode ∧ L.layer b.toNode = p).card = L.topOrder p z.1.1 := by
  unfold LayeredGarden.topCountBelow LayeredGarden.topOrder
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext b
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (h | h)
      · exact ⟨h.1.1.symm, h.2⟩
      · exact ⟨h.1, h.2.2⟩
    · rintro ⟨h1, h2⟩
      by_cases hd : z.IsDesc b.toNode
      · exact Or.inl ⟨hd, h2⟩
      · exact Or.inr ⟨h1, hd, h2⟩
  · rw [Finset.disjoint_left]
    intro b h1 h2
    exact (Finset.mem_filter.mp h2).2.2.1 (Finset.mem_filter.mp h1).2.1

/-- The count below `z` is the top order minus the count off the subtree. -/
theorem topCountBelow_eq_sub (L : LayeredGarden w) (p : ℕ) (z : GNode L.garden.tree) :
    L.topCountBelow p z = L.topOrder p z.1.1 -
      (Finset.univ.filter fun b : GBranch L.garden.tree =>
        b.1.1 = z.1.1 ∧ ¬ z.IsDesc b.toNode ∧ L.layer b.toNode = p).card := by
  have := topCountBelow_add L p z
  omega

/-! ## Layer-`p` counts -/

section Count
variable {LG LG' : LayeredGarden w} {R R' : Set (Address w)} (I : OutIso LG LG' R R') (I' : OutIso LG' LG R' R)
  (hinv : ∀ z', NodeAt LG' z' → z' ∉ R' → I.f (I'.f z') = z')
  (hinv' : ∀ z, NodeAt LG z → z ∉ R → I'.f (I.f z) = z)
  (hlay : ∀ z, NodeAt LG z → z ∉ R → layerAt LG' (I.f z) = layerAt LG z)
include hinv hinv' hlay

omit hinv' in
/-- The reverse layer transport. -/
theorem layer_symm {z' : Address w} (hn : NodeAt LG' z') (hR : z' ∉ R') :
    layerAt LG (I'.f z') = layerAt LG' z' := by
  obtain ⟨hn', hR'⟩ := I'.node z' hn hR
  rw [← hlay _ hn' hR', hinv z' hn hR]

/-- **Counts below an `R`-free subtree.** -/
theorem count_free (p : ℕ) (z : GNode LG.garden.tree) (hzR : z.1 ∉ R)
    (hfree : ∀ q, NodeAt LG (addrExt z.1 q) → addrExt z.1 q ∉ R)
    (z' : GNode LG'.garden.tree) (hz' : z'.1 = I.f z.1) :
    LG'.topCountBelow p z' = LG.topCountBelow p z := by
  have hzn : NodeAt LG z.1 := z.2
  have hfree' := free_image I I' hinv' hzn hzR hfree
  have hj : z'.1.1 = z.1.1 := by rw [hz']; exact I.tree _ hzn hzR
  -- the forward facts
  have F : ∀ b : GBranch LG.garden.tree, z.IsDesc b.toNode →
      b.1 ∉ R ∧ I.f b.1 = addrExt z'.1 (b.1.2.drop z.1.2.length) := by
    intro b hb
    have hy : b.1 = addrExt z.1 (b.1.2.drop z.1.2.length) := eq_addrExt_of_prefix hb.1 hb.2
    have hq : NodeAt LG (addrExt z.1 (b.1.2.drop z.1.2.length)) := by rw [← hy]; exact nodeAt_of_branchAt b.2
    refine ⟨by rw [hy]; exact hfree _ hq, ?_⟩
    have e := map_addrExt I z.1 _ hq (fun r hr => hfree r (nodeAt_prefix hq hr))
    rw [← hy] at e
    rw [e, hz']
  have F' : ∀ b' : GBranch LG'.garden.tree, z'.IsDesc b'.toNode →
      b'.1 ∉ R' ∧ I'.f b'.1 = addrExt z.1 (b'.1.2.drop z'.1.2.length) := by
    intro b' hb'
    have hy : b'.1 = addrExt (I.f z.1) (b'.1.2.drop z'.1.2.length) := by
      rw [← hz']; exact eq_addrExt_of_prefix hb'.1 hb'.2
    have hq : NodeAt LG' (addrExt (I.f z.1) (b'.1.2.drop z'.1.2.length)) := by
      rw [← hy]; exact nodeAt_of_branchAt b'.2
    refine ⟨by rw [hy]; exact hfree' _ hq, ?_⟩
    have e := map_addrExt I' (I.f z.1) _ hq (fun r hr => hfree' r (nodeAt_prefix hq hr))
    rw [← hy, hinv' _ hzn hzR] at e
    exact e
  have B : ∀ b : GBranch LG.garden.tree, z.IsDesc b.toNode → BranchAt LG' (I.f b.1) := fun b hb =>
    (I.branch (nodeAt_of_branchAt b.2) (F b hb).1).mpr b.2
  have B' : ∀ b' : GBranch LG'.garden.tree, z'.IsDesc b'.toNode → BranchAt LG (I'.f b'.1) := fun b' hb' =>
    (I'.branch (nodeAt_of_branchAt b'.2) (F' b' hb').1).mpr b'.2
  unfold LayeredGarden.topCountBelow
  symm
  refine Finset.card_bij' (fun b hb => (⟨I.f b.1, B b (Finset.mem_filter.mp hb).2.1⟩ : GBranch LG'.garden.tree))
    (fun b' hb' => (⟨I'.f b'.1, B' b' (Finset.mem_filter.mp hb').2.1⟩ : GBranch LG.garden.tree)) ?_ ?_ ?_ ?_
  · intro b hb
    replace hb := (Finset.mem_filter.mp hb).2
    obtain ⟨hbR, e⟩ := F b hb.1
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨?_, ?_⟩, ?_⟩
    · show z'.1.1 = (I.f b.1).1
      rw [e]; rfl
    · show z'.1.2 <+: (I.f b.1).2
      rw [e]; exact List.prefix_append _ _
    · show LG'.layer ⟨I.f b.1, _⟩ = p
      exact ((layerAt_node LG' _).symm.trans ((hlay _ (nodeAt_of_branchAt b.2) hbR).trans
        (layerAt_node LG b.toNode))).trans hb.2
  · intro b' hb'
    replace hb' := (Finset.mem_filter.mp hb').2
    obtain ⟨hbR, e⟩ := F' b' hb'.1
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨?_, ?_⟩, ?_⟩
    · show z.1.1 = (I'.f b'.1).1
      rw [e]; rfl
    · show z.1.2 <+: (I'.f b'.1).2
      rw [e]; exact List.prefix_append _ _
    · show LG.layer ⟨I'.f b'.1, _⟩ = p
      exact ((layerAt_node LG _).symm.trans ((layer_symm I I' hinv hlay (nodeAt_of_branchAt b'.2) hbR).trans
        (layerAt_node LG' b'.toNode))).trans hb'.2
  · intro b hb
    replace hb := (Finset.mem_filter.mp hb).2
    exact Subtype.ext (hinv' _ (nodeAt_of_branchAt b.2) (F b hb.1).1)
  · intro b' hb'
    replace hb' := (Finset.mem_filter.mp hb').2
    exact Subtype.ext (hinv _ (nodeAt_of_branchAt b'.2) (F' b' hb'.1).1)

/-- **Counts below a node above all of `R` in its tree.** -/
theorem count_full (hR' : RegionOK LG' R') (p : ℕ) (z : GNode LG.garden.tree) (hzR : z.1 ∉ R)
    (hfull : ∀ y, NodeAt LG y → y.1 = z.1.1 → y ∈ R → z.1.2 <+: y.2)
    (htop : LG'.topOrder p z.1.1 = LG.topOrder p z.1.1)
    (z' : GNode LG'.garden.tree) (hz' : z'.1 = I.f z.1) :
    LG'.topCountBelow p z' = LG.topCountBelow p z := by
  have hzn : NodeAt LG z.1 := z.2
  -- the root path to `z` avoids `R`
  have hzfree : ∀ r, r <+: z.1.2 → (z.1.1, r) ∉ R := by
    intro r hr hrR
    have hn : NodeAt LG (z.1.1, r) := TTree.mem_nodes_of_prefix _ hzn hr
    have h2 := hfull _ hn rfl hrR
    have : r = z.1.2 := hr.eq_of_length (le_antisymm hr.length_le h2.length_le)
    apply hzR
    have e : z.1 = (z.1.1, r) := Prod.ext rfl this.symm
    rw [e]; exact hrR
  have hfz : I.f z.1 = z.1 := map_rootFree I hzn hzfree
  have hz'v : z'.1 = z.1 := hz'.trans hfz
  have hj : z'.1.1 = z.1.1 := congrArg Prod.fst hz'v
  have hfull' := full_image I' hR' hfull
  -- off the subtree everything is fixed
  have F : ∀ b : GBranch LG.garden.tree, b.1.1 = z.1.1 → ¬ z.IsDesc b.toNode → b.1 ∉ R ∧ I.f b.1 = b.1 := by
    intro b hbj hnd
    have hbn : NodeAt LG b.1 := nodeAt_of_branchAt b.2
    refine ⟨fun h => hnd ⟨hbj.symm, hfull _ hbn hbj h⟩, map_rootFree I hbn fun r hr hrR => ?_⟩
    have hn : NodeAt LG (b.1.1, r) := TTree.mem_nodes_of_prefix _ hbn hr
    exact hnd ⟨hbj.symm, (hfull _ hn hbj hrR).trans hr⟩
  have F' : ∀ b' : GBranch LG'.garden.tree, b'.1.1 = z.1.1 → ¬ z'.IsDesc b'.toNode →
      b'.1 ∉ R' ∧ I'.f b'.1 = b'.1 := by
    intro b' hbj hnd
    have hbn : NodeAt LG' b'.1 := nodeAt_of_branchAt b'.2
    have hnd' : ¬ z.1.2 <+: b'.1.2 := fun h => hnd ⟨by rw [hz'v]; exact hbj.symm, by rw [hz'v]; exact h⟩
    refine ⟨fun h => hnd' (hfull' _ hbn hbj h), map_rootFree I' hbn fun r hr hrR => ?_⟩
    have hn : NodeAt LG' (b'.1.1, r) := TTree.mem_nodes_of_prefix _ hbn hr
    exact hnd' ((hfull' _ hn hbj hrR).trans hr)
  have B : ∀ b : GBranch LG.garden.tree, b.1.1 = z.1.1 → ¬ z.IsDesc b.toNode → BranchAt LG' (I.f b.1) :=
    fun b hbj hnd => (I.branch (nodeAt_of_branchAt b.2) (F b hbj hnd).1).mpr b.2
  have B' : ∀ b' : GBranch LG'.garden.tree, b'.1.1 = z.1.1 → ¬ z'.IsDesc b'.toNode → BranchAt LG (I'.f b'.1) :=
    fun b' hbj hnd => (I'.branch (nodeAt_of_branchAt b'.2) (F' b' hbj hnd).1).mpr b'.2
  rw [topCountBelow_eq_sub, topCountBelow_eq_sub, hj, htop]
  congr 1
  symm
  refine Finset.card_bij'
    (fun b hb => (⟨I.f b.1, B b (Finset.mem_filter.mp hb).2.1 (Finset.mem_filter.mp hb).2.2.1⟩ :
      GBranch LG'.garden.tree))
    (fun b' hb' => (⟨I'.f b'.1, B' b' (Finset.mem_filter.mp hb').2.1 (Finset.mem_filter.mp hb').2.2.1⟩ :
      GBranch LG.garden.tree)) ?_ ?_ ?_ ?_
  · intro b hb
    replace hb := (Finset.mem_filter.mp hb).2
    obtain ⟨hbR, e⟩ := F b hb.1 hb.2.1
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
    · show (I.f b.1).1 = z.1.1
      rw [e]; exact hb.1
    · rintro ⟨h1, h2⟩
      apply hb.2.1
      have h1' : z'.1.1 = (I.f b.1).1 := h1
      have h2' : z'.1.2 <+: (I.f b.1).2 := h2
      rw [e, hz'v] at h1' h2'
      exact ⟨h1', h2'⟩
    · show LG'.layer ⟨I.f b.1, _⟩ = p
      exact ((layerAt_node LG' _).symm.trans ((hlay _ (nodeAt_of_branchAt b.2) hbR).trans
        (layerAt_node LG b.toNode))).trans hb.2.2
  · intro b' hb'
    replace hb' := (Finset.mem_filter.mp hb').2
    obtain ⟨hbR, e⟩ := F' b' hb'.1 hb'.2.1
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
    · show (I'.f b'.1).1 = z.1.1
      rw [e]; exact hb'.1
    · rintro ⟨h1, h2⟩
      apply hb'.2.1
      have h1' : z.1.1 = (I'.f b'.1).1 := h1
      have h2' : z.1.2 <+: (I'.f b'.1).2 := h2
      rw [e] at h1' h2'
      exact ⟨by rw [hz'v]; exact h1', by rw [hz'v]; exact h2'⟩
    · show LG.layer ⟨I'.f b'.1, _⟩ = p
      exact ((layerAt_node LG _).symm.trans ((layer_symm I I' hinv hlay (nodeAt_of_branchAt b'.2) hbR).trans
        (layerAt_node LG' b'.toNode))).trans hb'.2.2
  · intro b hb
    replace hb := (Finset.mem_filter.mp hb).2
    exact Subtype.ext (hinv' _ (nodeAt_of_branchAt b.2) (F b hb.1 hb.2.1).1)
  · intro b' hb'
    replace hb' := (Finset.mem_filter.mp hb').2
    exact Subtype.ext (hinv _ (nodeAt_of_branchAt b'.2) (F' b' hb'.1 hb'.2.1).1)

end Count

/-! ## A one-step correspondence -/

/-- A correspondence of two layered gardens off two good regions, with its inverse and the layer transport. -/
structure StepIso (LG LG' : LayeredGarden w) where
  R : Set (Address w)
  R' : Set (Address w)
  I : OutIso LG LG' R R'
  I' : OutIso LG' LG R' R
  hinv : ∀ z', NodeAt LG' z' → z' ∉ R' → I.f (I'.f z') = z'
  hinv' : ∀ z, NodeAt LG z → z ∉ R → I'.f (I.f z) = z
  hR : RegionOK LG R
  hR' : RegionOK LG' R'
  hlay : ∀ z, NodeAt LG z → z ∉ R → layerAt LG' (I.f z) = layerAt LG z

end WaveTurbulence.Flower.CapsStable
