/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.LayerRegDraft.Part2

/-!
# TARGET Prop `layerreg2` for regular trees

TARGET Prop `layerreg2` (L932–L948), regular trees: a regular tree `𝒯` of order `2m` embedded in a
layered garden satisfying the canonicity criterion, with root `𝔫` (parent layer `q`) and lone leaf at `𝔫'`
(layer `q'`), and incoherency index `g`: the number of layerings induced on `𝒯` is at most
`C₂^g C₀^{m + |q - q'|}`.

Here the tree is a chain code `X` (sign `ζ` at the root) embedded at `a` (`ChainEmb`, with any subtree `h`
at the lone position); the induced layering is the restriction to the nodes of `X` other than its lone
position (`chainNodesSet`), whose layer is the fixed `q'`. **`layerreg2_tree`**: at most
`(2^{9p})^g · 2^{n(𝒯)} · 2^{q - q'}` (so `C₀ = 4`, `C₂ = 2^{9p}`), by the drop budget `chain_budget` and
the determination of the layering by its drops on the branching nodes, as for couples.
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg

variable {w : ℕ}

/-- **The layerings induced on an embedded regular tree** (TARGET `layerreg2`). -/
def inducedTreeLayerings (p : ℕ) (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) (q q' g : ℕ) :
    Set (Fin w × Path → ℕ) :=
  {f | ∃ LG : LayeredGarden w, ∃ h : TTree, LG.CanonCriterion p ∧ LG.garden.IsPlain ∧
    ChainEmb LG.garden X ζ a h ∧ parAt LG p a = q ∧ layerAt LG (addrExt a X.lonePath) = q' ∧
    incohCount LG (X.linksAt ζ a) = g ∧
    ∀ z, f z = if z ∈ chainNodesSet X ζ a then layerAt LG z else 0}

/-- The parent value of an address, read from a layering `f` (`q` at the root). -/
def parT (a : Fin w × Path) (q : ℕ) (f : Fin w × Path → ℕ) (z : Fin w × Path) : ℕ :=
  if z = a then q else f (parentAddr z)

/-- The drops of a layering at the addresses of `B`. -/
def dropT (B : Finset (Fin w × Path)) (a : Fin w × Path) (q : ℕ) (f : Fin w × Path → ℕ)
    (z : Fin w × Path) : ℕ :=
  if z ∈ B then parT a q f z - f z else 0

section Garden

variable {G : Garden w}

/-- The pair endpoints of an embedded chain are leaves. -/
theorem ChainEmb.leaf_of_mem {X : RegChain} {ζ : ℤˣ} {a : Fin w × Path} {h : TTree}
    (hC : ChainEmb G X ζ a h) {z : Fin w × Path} (hz : z ∈ pairEndpoints (X.pairsAt ζ a)) :
    z.2 ∈ (G.tree z.1).leaves := by
  have : z ∈ leafAddresses (X.plug ζ h) a := by
    rw [chain_leafAddresses]; exact Finset.mem_union_left _ hz
  obtain ⟨q, hq, rfl⟩ := mem_image_addrExt this
  exact (node_iff_of_subtree hC.node hC.tree q).2.1.2 hq

/-- The decoded pairs of an embedded chain give embedded trivial couples. -/
theorem ChainEmb.triv_of_pair (hplain : G.IsPlain) {X : RegChain} {ζ : ℤˣ} {a : Fin w × Path}
    {h : TTree} (hC : ChainEmb G X ζ a h) {q : (Fin w × Path) × (Fin w × Path)}
    (hq : q ∈ X.pairsAt ζ a) : Embeds G .triv q.1 q.2 := by
  have l1 := hC.leaf_of_mem ((mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inl rfl⟩)
  have l2 := hC.leaf_of_mem ((mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inr rfl⟩)
  have hp := hC.pairs q hq ⟨q.1, l1⟩ rfl
  have hne : q.1 ≠ q.2 := by
    intro e
    apply (fun hh => ((G.pair_eq_iff ⟨q.1, l1⟩).1 hh) (hplain _))
    exact Subtype.ext (hp.trans e.symm)
  refine ⟨indep_of_leaves l1 l2 hne, TTree.leaves_subset_nodes _ l1, TTree.leaves_subset_nodes _ l2,
    subtreeAt_of_mem_leaves _ _ l1, subtreeAt_of_mem_leaves _ _ l2, ?_⟩
  intro p' hp' ℓ hℓ
  simp only [RegCpl.pairsAt, List.mem_singleton] at hp'
  subst hp'
  have : ℓ = ⟨q.1, l1⟩ := Subtype.ext hℓ
  rw [this]; exact hp

end Garden

/-- **Every non-root node of an embedded chain is a child of a branching node of the chain.** -/
theorem chain_parent_mem {X : RegChain} {ζ : ℤˣ} {a z : Fin w × Path} (h : TTree)
    (hz : z ∈ chainNodesSet X ζ a) (ha : z ≠ a) :
    parentAddr z ∈ pairEndpoints (X.linksAt ζ a) ∧ ∃ i : Fin 3, z = addrExt (parentAddr z) [i] := by
  have hreg := chain_endpoints_region X ζ a z hz
  have hz' : z ∈ branchAddresses (X.plug ζ h) a ∪ leafAddresses (X.plug ζ h) a := by
    rw [chain_branchAddresses, chain_leafAddresses]
    unfold chainNodesSet at hz
    rcases Finset.mem_union.1 hz with h1 | h1
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ h1)
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ h1)
  have gen : ∀ t, t ∈ (X.plug ζ h).nodes → z = addrExt a t →
      parentAddr z ∈ branchAddresses (X.plug ζ h) a ∧ ∃ i : Fin 3, z = addrExt (parentAddr z) [i] := by
    intro t ht hzt
    subst hzt
    obtain ⟨t', i, rfl⟩ := (List.eq_nil_or_concat t).resolve_left (by
      rintro rfl; exact ha (by simp [addrExt]))
    have hpre : parentAddr (addrExt a (t'.concat i)) = addrExt a t' := by
      simp [parentAddr, addrExt, List.concat_eq_append, ← List.append_assoc]
    rw [hpre]
    refine ⟨Finset.mem_image_of_mem _ (Comb.TreePath.branching_of_append_mem _
      (by rwa [List.concat_eq_append] at ht)), i, ?_⟩
    rw [addrExt_append, List.concat_eq_append]
  obtain ⟨hpb, hi⟩ : parentAddr z ∈ branchAddresses (X.plug ζ h) a ∧
      ∃ i : Fin 3, z = addrExt (parentAddr z) [i] := by
    rcases Finset.mem_union.1 hz' with h1 | h1
    · obtain ⟨t, ht, hzt⟩ := mem_image_addrExt h1
      exact gen t (TTree.branching_subset_nodes _ ht) hzt
    · obtain ⟨t, ht, hzt⟩ := mem_image_addrExt h1
      exact gen t (TTree.leaves_subset_nodes _ ht) hzt
  refine ⟨?_, hi⟩
  rw [chain_branchAddresses] at hpb
  rcases Finset.mem_union.1 hpb with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨t, -, ht⟩ := mem_image_addrExt h1
    obtain ⟨i, hzi⟩ := hi
    have e2 : z = addrExt (addrExt a X.lonePath) (t ++ [i]) := by
      rw [hzi, ht, addrExt_append]
    apply hreg.2
    refine ⟨by rw [e2]; exact under_ext _ _, ne_of_under_ext (q := t ++ [i]) (by simp) ?_⟩
    rw [e2]; exact under_refl _

variable {p : ℕ} {X : RegChain} {ζ : ℤˣ} {a : Fin w × Path} {q q' g : ℕ}

theorem chain_links_sub_nodes {z : Fin w × Path} (hz : z ∈ pairEndpoints (X.linksAt ζ a)) :
    z ∈ chainNodesSet X ζ a := Finset.mem_union_left _ hz

theorem chain_pairs_sub_nodes {z : Fin w × Path} (hz : z ∈ pairEndpoints (X.pairsAt ζ a)) :
    z ∈ chainNodesSet X ζ a := Finset.mem_union_right _ hz

/-- Facts about an induced tree layering, read through a witness. -/
theorem tree_witness_facts {f : Fin w × Path → ℕ} {LG : LayeredGarden w} {h : TTree}
    (hC : ChainEmb LG.garden X ζ a h) (ha : parAt LG p a = q)
    (hf : ∀ z, f z = if z ∈ chainNodesSet X ζ a then layerAt LG z else 0) :
    (∀ z ∈ chainNodesSet X ζ a, f z = layerAt LG z) ∧
    (∀ z ∈ chainNodesSet X ζ a, parT a q f z = parAt LG p z) := by
  have W1 : ∀ z ∈ chainNodesSet X ζ a, f z = layerAt LG z := fun z hz => by rw [hf z, ite_pos_of hz]
  refine ⟨W1, fun z hz => ?_⟩
  unfold parT
  by_cases hza : z = a
  · rw [ite_pos_of hza, hza, ha]
  · rw [ite_neg_of hza]
    obtain ⟨hpm, i, hzi⟩ := chain_parent_mem h hz hza
    rw [W1 _ (chain_links_sub_nodes hpm)]
    have hn := hC.mem_nodes hz
    have hn' : (addrExt (parentAddr z) [i]).2 ∈
        (LG.garden.tree (addrExt (parentAddr z) [i]).1).nodes := by
      rw [← hzi]; exact hn
    have := parAt_child LG p i hn'
    rw [← hzi] at this
    exact this.symm

/-- **The tree layering is determined by its drops** (given `q`). -/
theorem tree_layering_determined {f f' : Fin w × Path → ℕ}
    (hf : f ∈ inducedTreeLayerings p X ζ a q q' g) (hf' : f' ∈ inducedTreeLayerings p X ζ a q q' g)
    (hd : dropT (pairEndpoints (X.linksAt ζ a)) a q f = dropT (pairEndpoints (X.linksAt ζ a)) a q f') :
    f = f' := by
  obtain ⟨LG, h, hcan, hplain, hC, ha, -, -, hfz⟩ := hf
  obtain ⟨LG', h', hcan', hplain', hC', ha', -, -, hfz'⟩ := hf'
  obtain ⟨W1, W2⟩ := tree_witness_facts hC ha hfz
  obtain ⟨W1', W2'⟩ := tree_witness_facts hC' ha' hfz'
  set B := pairEndpoints (X.linksAt ζ a)
  have hpar : ∀ z ∈ chainNodesSet X ζ a, (z ≠ a → f (parentAddr z) = f' (parentAddr z)) →
      parT a q f z = parT a q f' z := by
    intro z _ hh
    unfold parT
    by_cases hza : z = a
    · simp [hza]
    · simp only [hza, ↓reduceIte]; exact hh hza
  have hbr : ∀ n, ∀ z ∈ B, z.2.length ≤ n → f z = f' z := by
    intro n
    induction n with
    | zero =>
      intro z hz hl
      have hzn := chain_links_sub_nodes hz
      have e1 : f z = parT a q f z - dropT B a q f z := by
        unfold dropT; rw [ite_pos_of hz, W2 z hzn, W1 z hzn]
        have := layerAt_le_parAt LG p hcan.1 (hC.mem_nodes hzn); omega
      have e2 : f' z = parT a q f' z - dropT B a q f' z := by
        unfold dropT; rw [ite_pos_of hz, W2' z hzn, W1' z hzn]
        have := layerAt_le_parAt LG' p hcan'.1 (hC'.mem_nodes hzn); omega
      rw [e1, e2, hd]
      congr 1
      apply hpar z hzn
      intro hza
      exfalso
      obtain ⟨-, i, hzi⟩ := chain_parent_mem h hzn hza
      have := congrArg (fun x : Fin w × Path => x.2.length) hzi
      simp [addrExt] at this; omega
    | succ n ih =>
      intro z hz hl
      have hzn := chain_links_sub_nodes hz
      have e1 : f z = parT a q f z - dropT B a q f z := by
        unfold dropT; rw [ite_pos_of hz, W2 z hzn, W1 z hzn]
        have := layerAt_le_parAt LG p hcan.1 (hC.mem_nodes hzn); omega
      have e2 : f' z = parT a q f' z - dropT B a q f' z := by
        unfold dropT; rw [ite_pos_of hz, W2' z hzn, W1' z hzn]
        have := layerAt_le_parAt LG' p hcan'.1 (hC'.mem_nodes hzn); omega
      rw [e1, e2, hd]
      congr 1
      apply hpar z hzn
      intro hza
      obtain ⟨hpm, i, hzi⟩ := chain_parent_mem h hzn hza
      apply ih _ hpm
      have := congrArg (fun x : Fin w × Path => x.2.length) hzi
      simp [addrExt] at this
      simp [parentAddr]; omega
  have hbr' : ∀ z ∈ B, f z = f' z := fun z hz => hbr _ z hz le_rfl
  have hpar' : ∀ z ∈ chainNodesSet X ζ a, parT a q f z = parT a q f' z := fun z hz =>
    hpar z hz fun hza => hbr' _ (chain_parent_mem h hz hza).1
  funext z
  by_cases hz : z ∈ chainNodesSet X ζ a
  · rcases Finset.mem_union.1 hz with hl | hl
    · exact hbr' z hl
    · obtain ⟨qq, hq, hzq⟩ := (mem_pairEndpoints_iff _ _).1 hl
      have T := hC.triv_of_pair hplain hq
      have T' := hC'.triv_of_pair hplain' hq
      have L1 := (cpl_coherent hcan hplain .triv qq.1 qq.2 rfl T (by simp [CohOn, RegCpl.linksAt])).1
        rfl
      have L1' := (cpl_coherent hcan' hplain' .triv qq.1 qq.2 rfl T'
        (by simp [CohOn, RegCpl.linksAt])).1 rfl
      have m1 : qq.1 ∈ chainNodesSet X ζ a :=
        chain_pairs_sub_nodes ((mem_pairEndpoints_iff _ _).2 ⟨qq, hq, Or.inl rfl⟩)
      have m2 : qq.2 ∈ chainNodesSet X ζ a :=
        chain_pairs_sub_nodes ((mem_pairEndpoints_iff _ _).2 ⟨qq, hq, Or.inr rfl⟩)
      have hz' : z ∈ cplNodes RegCpl.triv qq.1 qq.2 := by
        rw [mem_cplNodes_triv]; exact hzq
      rw [W1 z hz, W1' z hz, L1 z hz', L1' z hz', ← W2 _ m1, ← W2 _ m2, ← W2' _ m1, ← W2' _ m2,
        hpar' _ m1, hpar' _ m2]
  · rw [hfz z, hfz' z, ite_neg_of hz, ite_neg_of hz]

/-- **TARGET Prop `layerreg2` (regular trees)**: the number of layerings that layered gardens
satisfying the canonicity criterion `CanonCriterion p` induce on an embedded regular tree of order
`n(𝒯)` (code `X`), with root parent layer `q`, lone leaf layer `q'` and incoherency index `g`, is at
most `(2^{9p})^g · 2^{n(𝒯)} · 2^{q - q'}` (TARGET: `C₂^g C₀^{m + |q - q'|}` with `2m = n(𝒯)`; here
`C₀ = 4`, `C₂ = 2^{9p}`; `q ≥ q'` holds automatically). -/
theorem layerreg2_tree (X : RegChain) (hwf : X.wf = true) (ζ : ℤˣ) (a : Fin w × Path)
    (p q q' g : ℕ) :
    (inducedTreeLayerings p X ζ a q q' g).ncard ≤ (2 ^ (9 * p)) ^ g * 2 ^ X.size * 2 ^ (q - q') := by
  set B := pairEndpoints (X.linksAt ζ a)
  set T := (q - q') + 9 * p * g
  have hmap : ∀ f ∈ inducedTreeLayerings p X ζ a q q' g, dropT B a q f ∈ boundedVecs B T := by
    rintro f ⟨LG, h, hcan, hplain, hC, ha, hl, hg, hfz⟩
    obtain ⟨W1, W2⟩ := tree_witness_facts hC ha hfz
    refine ⟨fun z hz => by unfold dropT; rw [ite_neg_of hz], ?_⟩
    have hbud : budget LG p B ≤ _ := chain_budget hcan hplain X ζ a h hwf hC
    have hlone : q' ≤ parAt LG p (addrExt a X.lonePath) := by
      rw [← hl]; exact layerAt_le_parAt LG p hcan.1 (nodeOfChainEmb hC)
    have hinc := incohCount_chain (LG := LG) X ζ a
    rw [ha] at hbud
    have hT : budget LG p B ≤ (q - q') + 9 * p * g := by
      rw [← hg, hinc]
      simp only [Nat.mul_assoc, Nat.mul_add] at hbud ⊢
      omega
    calc ∑ z ∈ B, dropT B a q f z = budget LG p B :=
          Finset.sum_congr rfl fun z hz => by
            unfold dropT dropAt
            rw [ite_pos_of hz, W2 z (chain_links_sub_nodes hz), W1 z (chain_links_sub_nodes hz)]
      _ ≤ T := hT
  have hinj : Set.InjOn (dropT B a q ·) (inducedTreeLayerings p X ζ a q q' g) :=
    fun f hf f' hf' hd => tree_layering_determined hf hf' hd
  have hcard := Set.ncard_le_ncard_of_injOn _ hmap hinj (boundedVecs_spec B T).1
  have hB : B.card ≤ X.size := by
    have h1 : B.card ≤ 2 * (X.linksAt ζ a).length := pairEndpoints_card_le _
    have h2 := chain_linksAt_length X ζ a
    omega
  calc (inducedTreeLayerings p X ζ a q q' g).ncard ≤ (boundedVecs B T).ncard := hcard
    _ ≤ 2 ^ (B.card + T) := (boundedVecs_spec B T).2
    _ ≤ 2 ^ (X.size + T) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = (2 ^ (9 * p)) ^ g * 2 ^ X.size * 2 ^ (q - q') := by
      rw [← pow_mul, ← pow_add, ← pow_add]
      congr 1
      ring

end WaveTurbulence.Links
