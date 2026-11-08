/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtGeo.Extract

/-! # D2b PROT-GEO (3): o73 Proposition 3.1 for embedded couples

An embedded regular couple `Embeds LG.garden Q a b` (well-formed code) with a branching vertex on a capped stem
consists of a subtree of the original tree paired with its trivial cap (o73 Prop 3.1, first paragraph):
* `Q = type2 X nil triv`, the cap at the `-` root `b = (c, [])`, the chain `X` at `a` with sign `1`; or
* `Q = type2 nil X triv`, the cap at the `+` root `a = (c, [])`, the chain `X` at `b` with sign `-1`;
in both cases a `CapChain` (`embeds_stem_cap`). With `objCpl` this gives item (i) for couples
(`embeds_protShape`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.Flower.MkDefs
  WaveTurbulence.Flower.ProtDefs

namespace WaveTurbulence.Flower.ProtGeo

variable {w : ℕ}

/-- The partner of a decoded couple leaf is a decoded couple leaf. -/
theorem embeds_pair_endpoint {G : Garden w} {Q : RegCpl} {a b : Fin w × Path} (hE : Embeds G Q a b)
    (ℓ : GLeaf G.tree) (hℓ : ℓ.1 ∈ pairEndpoints (Q.pairsAt a b)) :
    (G.pair ℓ).1 ∈ pairEndpoints (Q.pairsAt a b) := by
  obtain ⟨p, hp, h1 | h1⟩ := (mem_pairEndpoints_iff _ _).mp hℓ
  · rw [hE.pairs p hp ℓ h1]
    exact (mem_pairEndpoints_iff _ _).mpr ⟨p, hp, Or.inr rfl⟩
  · have hm : p.1 ∈ pairEndpoints (Q.pairsAt a b) := (mem_pairEndpoints_iff _ _).mpr ⟨p, hp, Or.inl rfl⟩
    let g : GLeaf G.tree := ⟨p.1, hE.leaf_of_mem hm⟩
    have hg : G.pair g = ℓ := Subtype.ext ((hE.pairs p hp g rfl).trans h1.symm)
    rw [← hg, G.pair_pair]
    exact hm

/-- A regular couple code with a trivial `-` tree and a nontrivial `+` tree is `type2 X nil triv`. -/
theorem code_of_trees2_leaf {Q : RegCpl} (hQ : Q.wf = true) (h2 : Q.trees.2 = .leaf) (h1 : Q.trees.1 ≠ .leaf) :
    ∃ X : RegChain, Q = .type2 X .nil .triv ∧ X.wf = true := by
  cases Q with
  | triv => exact absurd rfl h1
  | type1 c Q₁ Q₂ Q₃ =>
    simp only [RegCpl.trees] at h2
    split_ifs at h2
  | type2 Xp Xm Qlp =>
    cases Xm with
    | pair m Qr Qg inner rest =>
      simp only [RegCpl.trees, RegChain.plug, node3] at h2; cases h2
    | nil =>
      cases Qlp with
      | triv =>
        refine ⟨Xp, rfl, ?_⟩
        simp only [RegCpl.wf, Bool.and_eq_true] at hQ
        exact hQ.1.1.1.1
      | type1 c Q₁ Q₂ Q₃ =>
        simp only [RegCpl.trees, RegChain.plug] at h2
        split_ifs at h2
      | type2 _ _ _ =>
        simp [RegCpl.wf, RegCpl.isType2] at hQ

/-- A regular couple code with a trivial `+` tree and a nontrivial `-` tree is `type2 nil X triv`. -/
theorem code_of_trees1_leaf {Q : RegCpl} (hQ : Q.wf = true) (h1 : Q.trees.1 = .leaf) (h2 : Q.trees.2 ≠ .leaf) :
    ∃ X : RegChain, Q = .type2 .nil X .triv ∧ X.wf = true := by
  cases Q with
  | triv => exact absurd rfl h2
  | type1 c Q₁ Q₂ Q₃ =>
    simp only [RegCpl.trees] at h1; cases h1
  | type2 Xp Xm Qlp =>
    cases Xp with
    | pair m Qr Qg inner rest =>
      simp only [RegCpl.trees, RegChain.plug, node3] at h1; cases h1
    | nil =>
      cases Qlp with
      | triv =>
        refine ⟨Xm, rfl, ?_⟩
        simp only [RegCpl.wf, Bool.and_eq_true] at hQ
        exact hQ.1.1.1.2
      | type1 c Q₁ Q₂ Q₃ =>
        simp only [RegCpl.trees, RegChain.plug] at h1; cases h1
      | type2 _ _ _ =>
        simp [RegCpl.wf, RegCpl.isType2] at hQ

theorem ne_leaf_of_branch {t : TTree} {q : Path} (hq : q ∈ t.branching) : t ≠ .leaf := by
  rintro rfl; simp [TTree.branching] at hq

/-- The partner of a capped flower is a cap root. -/
theorem capFlower_partner {LG : LayeredGarden w} {J : Finset (Fin w)}
    (hcap : ∀ j ∈ J, LG.garden.tree j = TTree.leaf) {f : GLeaf LG.garden.tree} (hf : IsCapFlower LG J f) :
    (LG.garden.pair f).1 = ((LG.garden.pair f).1.1, []) ∧ (LG.garden.pair f).1.1 ∈ J := by
  have h2 := (LG.garden.pair f).2
  rw [hcap _ hf.2] at h2
  simp only [TTree.leaves, Finset.mem_singleton] at h2
  exact ⟨Prod.ext rfl h2, hf.2⟩

/-- A leaf address `(c, [])` below `x` forces `x = (c, [])`. -/
theorem eq_of_root_mem_leafAddresses {T : TTree} {x : Fin w × Path} {c : Fin w}
    (h : (c, ([] : Path)) ∈ leafAddresses T x) : x = (c, []) := by
  obtain ⟨q, -, he⟩ := mem_leafAddresses'.mp h
  have e2 : ([] : Path) = x.2 ++ q := congrArg Prod.snd he
  exact Prod.ext (congrArg Prod.fst he).symm (List.append_eq_nil_iff.mp e2.symm).1

/-- The cap root of a capped flower of an embedded couple is one of its two roots, not the one above the flower. -/
theorem cap_root_other {LG : LayeredGarden w} {J : Finset (Fin w)}
    (hcap : ∀ j ∈ J, LG.garden.tree j = TTree.leaf) {Q : RegCpl} {a b : Fin w × Path}
    (hE : Embeds LG.garden Q a b) {f : GLeaf LG.garden.tree} (hf : IsCapFlower LG J f)
    (hfx : Under a f.1 ∨ Under b f.1) :
    (Under a f.1 → b = ((LG.garden.pair f).1.1, [])) ∧ (Under b f.1 → a = ((LG.garden.pair f).1.1, [])) := by
  have hp := embeds_pair_endpoint hE f (hE.leaf_mem f hfx)
  rw [← couple_leafAddresses] at hp
  obtain ⟨hc1, hcJ⟩ := capFlower_partner hcap hf
  rw [hc1] at hp
  rcases Finset.mem_union.mp hp with h | h
  · have ha := eq_of_root_mem_leafAddresses h
    refine ⟨fun hfa => absurd (by rw [← hfa.1, ha]; exact hcJ) hf.1, fun _ => ha⟩
  · have hb := eq_of_root_mem_leafAddresses h
    refine ⟨fun _ => hb, fun hfb => absurd (by rw [← hfb.1, hb]; exact hcJ) hf.1⟩

/-- The cap couple at a cap root `(c, [])` has a trivial tree there. -/
theorem cap_tree {LG : LayeredGarden w} {J : Finset (Fin w)} (hcap : ∀ j ∈ J, LG.garden.tree j = TTree.leaf)
    {c : Fin w} (hc : c ∈ J) {T : TTree} (hT : (LG.garden.tree (c, ([] : Path)).1).subtreeAt (c, ([] : Path)).2 = T) :
    T = .leaf := by
  rw [← hT]; show (LG.garden.tree c).subtreeAt [] = _; rw [hcap c hc]; rfl

/-- **o73 Prop 3.1 (couples).** An embedded couple meeting a capped stem branching node is a cap couple. -/
theorem embeds_stem_cap {LG : LayeredGarden w} {J : Finset (Fin w)}
    (hcap : ∀ j ∈ J, LG.garden.tree j = TTree.leaf) {Q : RegCpl} {a b : Fin w × Path}
    (hQ : Q.wf = true) (hE : Embeds LG.garden Q a b)
    (hm : MeetsStem LG J (branchAddresses Q.trees.1 a ∪ branchAddresses Q.trees.2 b)) :
    ∃ (X : RegChain) (c : Fin w),
      (Q = .type2 X .nil .triv ∧ b = (c, []) ∧ CapChain LG J X 1 a c) ∨
      (Q = .type2 .nil X .triv ∧ a = (c, []) ∧ CapChain LG J X (-1) b c) := by
  obtain ⟨v, hv, f, hf, hvf⟩ := hm
  obtain ⟨hc1, hcJ⟩ := capFlower_partner hcap hf
  set c := (LG.garden.pair f).1.1 with hcdef
  rcases Finset.mem_union.mp hv with hv | hv
  · -- the vertex is in the `+` tree: the cap is the `-` root
    obtain ⟨q, hq, hvq⟩ := mem_branchAddresses'.mp hv
    have hv1 : v.1.1 = f.1.1 := hvf.1
    have hv2 : v.1.2 <+: f.1.2 := hvf.2
    rw [hvq] at hv1 hv2
    have hfa : Under a f.1 := ⟨hv1, (List.prefix_append a.2 q).trans hv2⟩
    have hb := (cap_root_other hcap hE hf (Or.inl hfa)).1 hfa
    have h2 : Q.trees.2 = .leaf := cap_tree hcap hcJ (hb ▸ hE.treeB)
    obtain ⟨X, rfl, hX⟩ := code_of_trees2_leaf hQ h2 (ne_leaf_of_branch hq)
    obtain ⟨hC, -, hlp⟩ := hE.type2
    refine ⟨X, c, Or.inl ⟨rfl, hb, ⟨hC, hX, v, hv, f, hf, hvf⟩, hcJ, fun ℓ hℓ => ?_⟩⟩
    have e := hlp.pairs _ (List.mem_singleton_self _) ℓ hℓ
    rw [e, hb]; rfl
  · -- the vertex is in the `-` tree: the cap is the `+` root
    obtain ⟨q, hq, hvq⟩ := mem_branchAddresses'.mp hv
    have hv1 : v.1.1 = f.1.1 := hvf.1
    have hv2 : v.1.2 <+: f.1.2 := hvf.2
    rw [hvq] at hv1 hv2
    have hfb : Under b f.1 := ⟨hv1, (List.prefix_append b.2 q).trans hv2⟩
    have ha := (cap_root_other hcap hE hf (Or.inr hfb)).2 hfb
    have h1 : Q.trees.1 = .leaf := cap_tree hcap hcJ (ha ▸ hE.treeA)
    obtain ⟨X, rfl, hX⟩ := code_of_trees1_leaf hQ h1 (ne_leaf_of_branch hq)
    obtain ⟨-, hC, hlp⟩ := hE.type2
    refine ⟨X, c, Or.inr ⟨rfl, ha, ⟨hC, hX, v, hv, f, hf, hvf⟩, hcJ, fun ℓ hℓ => ?_⟩⟩
    -- the cap leaf at `a` is paired with the lone leaf at `b ++ X.lonePath`
    have hal : a.2 ∈ (LG.garden.tree a.1).leaves := by
      rw [ha]; show [] ∈ (LG.garden.tree c).leaves; rw [hcap c hcJ]; simp [TTree.leaves]
    let g : GLeaf LG.garden.tree := ⟨a, hal⟩
    have e := hlp.pairs _ (List.mem_singleton_self _) g
      (by show a = addrExt a RegChain.nil.lonePath; simp [addrExt, RegChain.lonePath])
    have hg : LG.garden.pair g = ℓ := Subtype.ext (e.trans hℓ.symm)
    rw [← hg, LG.garden.pair_pair]
    exact ha

end WaveTurbulence.Flower.ProtGeo
