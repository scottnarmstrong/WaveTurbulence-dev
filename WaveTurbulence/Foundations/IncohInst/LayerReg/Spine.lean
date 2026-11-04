/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.IncohInst.LayerReg.Embed2
public import WaveTurbulence.Foundations.IncohInst.Links.Construct4

/-!
# Spines of chains, and node decompositions (packet C4)

* `spinePos X a`: the first nodes of the top-level pairs of a chain (top to bottom), then its lone
  position. These are the positions at which the tail of the chain can be cut: the subtree at a spine
  position is closed under the chain's leaf pairs (`spine_closed`), so for a type-2 couple the union of
  the subtrees at a spine position of each chain is closed under all its pairs (`type2_pairedUnder`).
* `spine_cut` (proof of TARGET Prop `layerreg1`, "choose the smallest `a(ε)` with `𝔏 = q_*`"): a
  coherent embedded chain whose lone position is in layer `q` and whose root's parent is above `q` has a
  spine position in layer `q` whose parent is above `q`.
* Membership decompositions of `cplNodes` / `chainNodesSet` along the structure.
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg

variable {w : ℕ}

/-- **The spine positions of a chain**: the first nodes `𝔫_a` of its top-level pairs, top to bottom,
followed by its lone position. -/
def spinePos : RegChain → (Fin w × Path) → List (Fin w × Path)
  | .nil, a => [a]
  | .pair m _ _ inner rest, a => a :: spinePos rest (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone]))

theorem spinePos_under : ∀ (X : RegChain) (a : Fin w × Path), ∀ s ∈ spinePos X a,
    Under a s ∧ Under s (addrExt a X.lonePath)
  | .nil, a, s, hs => by
    simp only [spinePos, List.mem_singleton] at hs
    subst hs
    exact ⟨under_refl _, by rw [RegChain.lonePath, addrExt_nil]; exact under_refl _⟩
  | .pair m Qr Qg inner rest, a, s, hs => by
    simp only [spinePos, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact ⟨under_refl _, under_ext _ _⟩
    · obtain ⟨h1, h2⟩ := spinePos_under rest _ s hs
      refine ⟨under_trans (under_ext _ _) h1, ?_⟩
      rw [chain_lonePath_eq m Qr Qg inner rest a]
      exact h2

theorem endpoints_oriented_under {Q : RegCpl} {x y : Fin w × Path} {P : Prop} [Decidable P] {z : Fin w × Path}
    (hz : z ∈ pairEndpoints (if P then Q.pairsAt x y else Q.pairsAt y x)) : Under x z ∨ Under y z := by
  split_ifs at hz
  · exact cpl_endpoints_under Q x y z (Finset.mem_union_right _ hz)
  · exact (cpl_endpoints_under Q y x z (Finset.mem_union_right _ hz)).symm

/-- The local pairs of a chain pair (red, green, inner) are not below the start of the rest. -/
theorem local_not_under_rest (m : MiniTreeCode) (Qr Qg : RegCpl) (inner : RegChain) (ζ : ℤˣ)
    (a z : Fin w × Path)
    (hz : z ∈ pairEndpoints (if slotSign ζ m.red.1 = 1 then
        Qr.pairsAt (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
      else Qr.pairsAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1])) ∨
      z ∈ pairEndpoints (if slotSign ζ m.green.1 = 1 then
        Qg.pairsAt (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
      else Qg.pairsAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1])) ∨
      z ∈ pairEndpoints (inner.pairsAt (slotSign ζ m.c) (addrExt a [m.c]))) :
    ¬ Under (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) z := by
  intro hu
  rcases hz with hz | hz | hz
  · exact (chain_regions.1 hu).1 (endpoints_oriented_under hz)
  · exact (chain_regions.1 hu).2 (endpoints_oriented_under hz)
  · obtain ⟨h1, h2⟩ := chain_endpoints_region inner _ _ z (Finset.mem_union_right _ hz)
    rw [addrExt_append] at h2
    exact (chain_inner_region h1 h2).2.2.2 hu

/-- **The subtree at a spine position is closed under the chain's leaf pairs.** -/
theorem spine_closed : ∀ (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path), ∀ s ∈ spinePos X a,
    ∀ q ∈ X.pairsAt ζ a, (Under s q.1 ↔ Under s q.2)
  | .nil, _, _, _, _, q, hq => by simp [RegChain.pairsAt] at hq
  | .pair m Qr Qg inner rest, ζ, a, s, hs, q, hq => by
    have hreg : ∀ z ∈ pairEndpoints ((RegChain.pair m Qr Qg inner rest).pairsAt ζ a), Under a z :=
      fun z hz => (chain_endpoints_region _ ζ a z (Finset.mem_union_right _ hz)).1
    have e1 : q.1 ∈ pairEndpoints ((RegChain.pair m Qr Qg inner rest).pairsAt ζ a) :=
      (mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inl rfl⟩
    have e2 : q.2 ∈ pairEndpoints ((RegChain.pair m Qr Qg inner rest).pairsAt ζ a) :=
      (mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inr rfl⟩
    simp only [spinePos, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact ⟨fun _ => hreg _ e2, fun _ => hreg _ e1⟩
    · have hsu := (spinePos_under rest _ s hs).1
      simp only [RegChain.pairsAt, List.mem_append] at hq
      rcases hq with ((hq | hq) | hq) | hq
      · have n1 := local_not_under_rest m Qr Qg inner ζ a q.1
          (Or.inl ((mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inl rfl⟩))
        have n2 := local_not_under_rest m Qr Qg inner ζ a q.2
          (Or.inl ((mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inr rfl⟩))
        exact ⟨fun h => absurd (under_trans hsu h) n1, fun h => absurd (under_trans hsu h) n2⟩
      · have n1 := local_not_under_rest m Qr Qg inner ζ a q.1
          (Or.inr (Or.inl ((mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inl rfl⟩)))
        have n2 := local_not_under_rest m Qr Qg inner ζ a q.2
          (Or.inr (Or.inl ((mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inr rfl⟩)))
        exact ⟨fun h => absurd (under_trans hsu h) n1, fun h => absurd (under_trans hsu h) n2⟩
      · have n1 := local_not_under_rest m Qr Qg inner ζ a q.1
          (Or.inr (Or.inr ((mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inl rfl⟩)))
        have n2 := local_not_under_rest m Qr Qg inner ζ a q.2
          (Or.inr (Or.inr ((mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inr rfl⟩)))
        exact ⟨fun h => absurd (under_trans hsu h) n1, fun h => absurd (under_trans hsu h) n2⟩
      · exact spine_closed rest _ _ s hs q hq

theorem indep_of_under {a b x y : Fin w × Path} (hab : Indep a b) (hx : Under a x) (hy : Under b y) :
    Indep x y :=
  ⟨fun h => hab.not_both (under_trans hx h) hy, fun h => hab.not_both hx (under_trans hy h)⟩

/-- **For a type-2 couple, cutting both chains at spine positions gives a closed pair of subtrees.** -/
theorem type2_pairedUnder (Xp Xm : RegChain) (Qlp : RegCpl) {a b : Fin w × Path} (hab : Indep a b)
    {sP sM : Fin w × Path} (hP : sP ∈ spinePos Xp a) (hM : sM ∈ spinePos Xm b) :
    PairedUnder ((RegCpl.type2 Xp Xm Qlp).pairsAt a b) sP sM := by
  have uP := spinePos_under Xp a sP hP
  have uM := spinePos_under Xm b sM hM
  intro q hq
  simp only [RegCpl.pairsAt, List.mem_append] at hq
  rcases hq with (hq | hq) | hq
  · have r1 := (chain_endpoints_region Xp 1 a q.1 (Finset.mem_union_right _
      ((mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inl rfl⟩))).1
    have r2 := (chain_endpoints_region Xp 1 a q.2 (Finset.mem_union_right _
      ((mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inr rfl⟩))).1
    have c := spine_closed Xp 1 a sP hP q hq
    have m1 : ¬ Under sM q.1 := fun h => hab.not_both r1 (under_trans uM.1 h)
    have m2 : ¬ Under sM q.2 := fun h => hab.not_both r2 (under_trans uM.1 h)
    simp only [m1, m2, or_false]
    exact c
  · have r1 := (chain_endpoints_region Xm (-1) b q.1 (Finset.mem_union_right _
      ((mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inl rfl⟩))).1
    have r2 := (chain_endpoints_region Xm (-1) b q.2 (Finset.mem_union_right _
      ((mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inr rfl⟩))).1
    have c := spine_closed Xm (-1) b sM hM q hq
    have m1 : ¬ Under sP q.1 := fun h => hab.not_both (under_trans uP.1 h) r1
    have m2 : ¬ Under sP q.2 := fun h => hab.not_both (under_trans uP.1 h) r2
    simp only [m1, m2, false_or]
    exact c
  · have r1 := cpl_endpoints_under Qlp _ _ q.1 (Finset.mem_union_right _
      ((mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inl rfl⟩))
    have r2 := cpl_endpoints_under Qlp _ _ q.2 (Finset.mem_union_right _
      ((mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inr rfl⟩))
    constructor
    · intro _
      rcases r2 with h | h
      · exact Or.inl (under_trans uP.2 h)
      · exact Or.inr (under_trans uM.2 h)
    · intro _
      rcases r1 with h | h
      · exact Or.inl (under_trans uP.2 h)
      · exact Or.inr (under_trans uM.2 h)

/-! ### Membership decompositions -/

theorem mem_cplNodes_triv {a b z : Fin w × Path} :
    z ∈ cplNodes .triv a b ↔ z = a ∨ z = b := by
  simp [cplNodes, RegCpl.linksAt, RegCpl.pairsAt]

theorem mem_cplNodes_type1 {c : MiniCplCode} {Q₁ Q₂ Q₃ : RegCpl} {a b z : Fin w × Path} :
    z ∈ cplNodes (.type1 c Q₁ Q₂ Q₃) a b ↔ z = a ∨ z = b ∨
      z ∈ cplNodes Q₁ (addrExt a [0]) (addrExt b [c.partner 0]) ∨
      z ∈ cplNodes Q₂ (addrExt b [1]) (addrExt a [1]) ∨
      z ∈ cplNodes Q₃ (addrExt a [2]) (addrExt b [c.partner 2]) := by
  simp only [cplNodes, RegCpl.linksAt, RegCpl.pairsAt, pairEndpoints_cons, pairEndpoints_append,
    Finset.mem_union, Finset.mem_singleton]
  tauto

theorem mem_cplNodes_type2 {Xp Xm : RegChain} {Qlp : RegCpl} {a b z : Fin w × Path} :
    z ∈ cplNodes (.type2 Xp Xm Qlp) a b ↔ z ∈ chainNodesSet Xp 1 a ∨ z ∈ chainNodesSet Xm (-1) b ∨
      z ∈ cplNodes Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath) := by
  simp only [cplNodes, chainNodesSet, RegCpl.linksAt, RegCpl.pairsAt, pairEndpoints_append,
    Finset.mem_union]
  tauto

/-- The nodes of the red (or green) couple of a chain pair, in the decoding orientation. -/
def orientedNodes (P : Prop) [Decidable P] (Q : RegCpl) (x y : Fin w × Path) : Finset (Fin w × Path) :=
  if P then cplNodes Q x y else cplNodes Q y x

theorem mem_oriented_of_links {P : Prop} [Decidable P] {Q : RegCpl} {x y z : Fin w × Path}
    (h : z ∈ pairEndpoints (if P then Q.linksAt x y else Q.linksAt y x)) :
    z ∈ orientedNodes P Q x y := by
  unfold orientedNodes cplNodes; split_ifs at h ⊢ <;> exact Finset.mem_union_left _ h

theorem mem_oriented_of_pairs {P : Prop} [Decidable P] {Q : RegCpl} {x y z : Fin w × Path}
    (h : z ∈ pairEndpoints (if P then Q.pairsAt x y else Q.pairsAt y x)) :
    z ∈ orientedNodes P Q x y := by
  unfold orientedNodes cplNodes; split_ifs at h ⊢ <;> exact Finset.mem_union_right _ h

theorem mem_chainNodesSet_pair {m : MiniTreeCode} {Qr Qg : RegCpl} {inner rest : RegChain}
    {ζ : ℤˣ} {a z : Fin w × Path} (h : z ∈ chainNodesSet (.pair m Qr Qg inner rest) ζ a) :
      z = a ∨ z = addrExt a ([m.c] ++ inner.lonePath) ∨
      z ∈ orientedNodes (slotSign ζ m.red.1 = 1) Qr (addrExt a [m.red.1])
        (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) ∨
      z ∈ orientedNodes (slotSign ζ m.green.1 = 1) Qg (addrExt a [m.green.1])
        (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) ∨
      z ∈ chainNodesSet inner (slotSign ζ m.c) (addrExt a [m.c]) ∨
      z ∈ chainNodesSet rest (slotSign (slotSign ζ m.c) m.lone)
        (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) := by
  unfold chainNodesSet at h
  rw [Finset.mem_union, RegChain.linksAt, RegChain.pairsAt, pairEndpoints_cons, pairEndpoints_append,
    pairEndpoints_append, pairEndpoints_append, pairEndpoints_append, pairEndpoints_append,
    pairEndpoints_append] at h
  simp only [Finset.mem_union, Finset.mem_singleton] at h
  rcases h with (h | h | (((h | h) | h) | h)) | (((h | h) | h) | h)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl (mem_oriented_of_links h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (mem_oriented_of_links h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Finset.mem_union_left _ h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Finset.mem_union_left _ h)))))
  · exact Or.inr (Or.inr (Or.inl (mem_oriented_of_pairs h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (mem_oriented_of_pairs h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Finset.mem_union_right _ h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Finset.mem_union_right _ h)))))

theorem root_mem_chainNodesSet (m : MiniTreeCode) (Qr Qg : RegCpl) (inner rest : RegChain) (ζ : ℤˣ)
    (a : Fin w × Path) : a ∈ chainNodesSet (.pair m Qr Qg inner rest) ζ a := by
  unfold chainNodesSet
  rw [RegChain.linksAt, pairEndpoints_cons]
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton_self _))

/-- The roots of a placed couple are among its nodes. -/
theorem left_mem_cplNodes : ∀ (Q : RegCpl) (a b : Fin w × Path), a ∈ cplNodes Q a b
  | .triv, a, b => mem_cplNodes_triv.2 (Or.inl rfl)
  | .type1 .., a, b => mem_cplNodes_type1.2 (Or.inl rfl)
  | .type2 Xp Xm Qlp, a, b => by
    rw [mem_cplNodes_type2]
    cases Xp with
    | nil =>
      right; right
      have h := left_mem_cplNodes Qlp (addrExt a RegChain.nil.lonePath) (addrExt b Xm.lonePath)
      exact (congrArg (· ∈ cplNodes Qlp (addrExt a RegChain.nil.lonePath) (addrExt b Xm.lonePath))
        (addrExt_nil a)).mp h
    | pair m Qr Qg inner rest => exact Or.inl (root_mem_chainNodesSet m Qr Qg inner rest 1 a)

theorem right_mem_cplNodes : ∀ (Q : RegCpl) (a b : Fin w × Path), b ∈ cplNodes Q a b
  | .triv, a, b => mem_cplNodes_triv.2 (Or.inr rfl)
  | .type1 .., a, b => mem_cplNodes_type1.2 (Or.inr (Or.inl rfl))
  | .type2 Xp Xm Qlp, a, b => by
    rw [mem_cplNodes_type2]
    cases Xm with
    | nil =>
      right; right
      have h := right_mem_cplNodes Qlp (addrExt a Xp.lonePath) (addrExt b RegChain.nil.lonePath)
      exact (congrArg (· ∈ cplNodes Qlp (addrExt a Xp.lonePath) (addrExt b RegChain.nil.lonePath))
        (addrExt_nil b)).mp h
    | pair m Qr Qg inner rest => exact Or.inr (Or.inl (root_mem_chainNodesSet m Qr Qg inner rest _ b))

/-! ### Cutting a chain at the first spine position of a given layer -/

/-- The links `(𝔫_a, 𝔫_b)` of the top-level pairs of a chain. -/
def spineLinks : RegChain → (Fin w × Path) → List ((Fin w × Path) × (Fin w × Path))
  | .nil, _ => []
  | .pair m _ _ inner rest, a => (a, addrExt a ([m.c] ++ inner.lonePath)) ::
      spineLinks rest (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone]))

theorem spineLinks_sub : ∀ (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path),
    ∀ l ∈ spineLinks X a, l ∈ X.linksAt ζ a
  | .nil, _, _, l, hl => by simp [spineLinks] at hl
  | .pair m Qr Qg inner rest, ζ, a, l, hl => by
    simp only [spineLinks, List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact List.mem_cons_self
    · have := spineLinks_sub rest (slotSign (slotSign ζ m.c) m.lone) _ l hl
      simp only [RegChain.linksAt, List.mem_cons, List.mem_append]
      tauto

variable {LG : LayeredGarden w} {p : ℕ}

theorem nodeOfChainEmb {X : RegChain} {ζ : ℤˣ} {a : Fin w × Path} {h : TTree}
    (hC : ChainEmb LG.garden X ζ a h) :
    (addrExt a X.lonePath).2 ∈ (LG.garden.tree (addrExt a X.lonePath).1).nodes :=
  node_ext hC.node hC.tree (lonePath_mem_plug _ _ _)

/-- A spine position of an embedded chain is a node. -/
theorem spinePos_node {X : RegChain} {ζ : ℤˣ} {a : Fin w × Path} {h : TTree}
    (hC : ChainEmb LG.garden X ζ a h) {s : Fin w × Path} (hs : s ∈ spinePos X a) :
    s.2 ∈ (LG.garden.tree s.1).nodes := by
  obtain ⟨-, h2⟩ := spinePos_under X a s hs
  have hl := nodeOfChainEmb hC
  obtain ⟨e1, q, hq⟩ := h2
  rw [← e1] at hl
  exact Comb.TreePath.mem_nodes_of_prefix _ hl ⟨q, hq⟩

/-- **The cut** (proof of TARGET `layerreg1`): the first spine position in layer `q`. -/
theorem spine_cut : ∀ (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) (h : TTree),
    ChainEmb LG.garden X ζ a h → (∀ l ∈ spineLinks X a, layerAt LG l.1 = layerAt LG l.2) →
    ∀ q : ℕ, layerAt LG (addrExt a X.lonePath) = q → q < parAt LG p a →
      ∃ s ∈ spinePos X a, layerAt LG s = q ∧ q < parAt LG p s
  | .nil, _, a, _, _, _, q, hl, hP => ⟨a, List.mem_singleton_self _, by rwa [RegChain.lonePath,
      addrExt_nil] at hl, hP⟩
  | .pair m Qr Qg inner rest, ζ, a, h, hC, hcoh, q, hl, hP => by
    by_cases ha : layerAt LG a = q
    · exact ⟨a, List.mem_cons_self, ha, hP⟩
    · have hlone := nodeOfChainEmb hC
      have hle : layerAt LG (addrExt a (RegChain.pair m Qr Qg inner rest).lonePath) ≤ layerAt LG a :=
        layerAt_le_of_under LG hC.node hlone (under_ext _ _)
      have hgt : q < layerAt LG a := lt_of_le_of_ne (hl ▸ hle) (Ne.symm ha)
      obtain ⟨-, -, -, hR⟩ := hC.parts
      have hnb : layerAt LG a = layerAt LG (addrExt a ([m.c] ++ inner.lonePath)) :=
        hcoh _ List.mem_cons_self
      have e : addrExt a ([m.c] ++ inner.lonePath ++ [m.lone]) =
          addrExt (addrExt a ([m.c] ++ inner.lonePath)) [m.lone] := by rw [addrExt_append]
      have hpar : parAt LG p (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) =
          layerAt LG (addrExt a ([m.c] ++ inner.lonePath)) := by
        rw [e]; exact parAt_child LG p _ (e ▸ hR.node)
      have hcoh' : ∀ l ∈ spineLinks rest (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])),
          layerAt LG l.1 = layerAt LG l.2 :=
        fun l hl' => hcoh l (List.mem_cons_of_mem _ hl')
      have hl' : layerAt LG (addrExt (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) rest.lonePath)
          = q := by rw [← chain_lonePath_eq]; exact hl
      obtain ⟨s, hs, hs1, hs2⟩ := spine_cut rest _ _ h hR hcoh' q hl' (by rw [hpar, ← hnb]; exact hgt)
      exact ⟨s, List.mem_cons_of_mem _ hs, hs1, hs2⟩

end WaveTurbulence.Links
