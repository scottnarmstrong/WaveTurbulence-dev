/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.IntWeight
public import WaveTurbulence.Foundations.Flower.MkSlots.IntSplit
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CollapsedDecorations
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourcePairAtSides
public import WaveTurbulence.Foundations.WeylSums.ThreeVectorReduction

/-! # B3s MK-SLOTS (integration): the remaining dagger weight is constant on its support

On the reconstruction `LG = layeredReconstruction D hS layer hLayer` of a skeleton `S` with cap trees `J`
(`CapGeo LG J p`: cap trees are single leaves, one capped flower per tree), the remaining dagger weight
`restW … (some cc) k` (`MkSlots/IntSplit.lean`) is the product of the node-local dagger weights `dagNodeW` over the
"case b" nodes outside cap natives: the core branch `D.coreBranch hS b` of every skeleton branch `b` that is a capped
flower parent, and its children other than the capped flower.

**Constancy** (`restW_cosetDecoration`). On every decoration `κ` at coset base `0`,
`restW … (some cc) (cosetDecoration … κ) = if RestInd … (collapseGenDecoration D hS κ) then restConst … else 0`:
* `RestInd κS` (skeleton level): at every skeleton branch `b` whose core is a capped flower parent, every child `i`
  that is not the capped flower carries the prescribed sibling momentum, `k^S_{b.child i} = cc b.1.1 i`;
* `restConst` (a unimodular constant, `norm_restConst`): the product over these `b` of
  `exp(i θ_b ‖k_b‖²) · ∏_{i ≠ flower} exp(-i θ_b ε_i ‖cc b.1.1 i‖²)`, `θ_b = capTheta … (D.coreBranch hS b)`,
  `k_b = Σ_i ε_i k_i` (`ε = childSign`), `k_i = cc b.1.1 i` for the siblings and `latticePoint L (roots j)` for the
  flower (`j` its cap tree): `restChildMom`.
With no dagger datum, `restW … none … = 1` (`restW_none`).

Proof: no case-b node lies in a cap native (`not_inCapNative_of_isCaseB`: a core branch lies in its chain slot; a
non-flower child of a core capped flower parent lies in a chain slot or in the native couple of a non-cap pair, since a
cap couple at that child would contain a second capped flower of the same tree); one capped flower parent per tree
(`cfp_eq_of_tree_eq`) makes `dagNodeW` explicit at the case-b nodes (`dagNodeW_at_cfp`, `dagNodeW_at_child`); the
product is reindexed by the skeleton branches (`restW_some_eq`); the child momenta are read on the collapsed skeleton
decoration (`attachedNode_child`), the flower momentum is the cap root label (`genDec_cap`), and the core momentum is
given by conservation (`IsDecoration`, `latticePoint` additivity). The constancy is first proved for an arbitrary
momentum assignment with the two momentum properties as hypotheses (`IntRest.restW_eq_ind`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
open WaveTurbulence.Flower.MkDefs

namespace WaveTurbulence.Flower.MkSlots

variable {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
variable (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)

/-! ### The skeleton-level objects -/

/-- Child `i` of the core branch of the skeleton branch `b` is a capped flower. -/
def IsCoreFlowerChild (J : Finset (Fin w)) (b : GBranch S.tree) (i : Fin 3) : Prop :=
  ∃ ℓ : GLeaf (D.forest hS), IsCapFlower (layeredReconstruction D hS layer hLayer) J ℓ ∧
    ℓ.toNode = (D.coreBranch hS b).child i

/-- **The support of the remaining dagger weight** (skeleton level): at every skeleton branch `b` whose core is a
capped flower parent, every child `i` that is not the capped flower carries the prescribed sibling momentum. -/
def RestInd (L : ℝ) (J : Finset (Fin w)) (cc : Fin w → Fin 3 → Mom d) {roots : Fin w → (Fin d → ℤ)}
    (κS : GenDecoration S d roots 0) : Prop :=
  ∀ b : GBranch S.tree, IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS b) →
    ∀ i : Fin 3, ¬ IsCoreFlowerChild D hS layer hLayer J b i → cosetDecoration S L 0 κS.1 (b.child i) = cc b.1.1 i

/-- The momentum of child `i` of the core of `b` on the support: the prescribed sibling momentum `cc b.1.1 i`, or the
cap momentum `latticePoint L (roots j)` at the capped flower (`j` the cap tree of its partner). -/
def restChildMom (L : ℝ) (J : Finset (Fin w)) (roots : Fin w → (Fin d → ℤ)) (cc : Fin w → Fin 3 → Mom d)
    (b : GBranch S.tree) (i : Fin 3) : Mom d :=
  if h : IsCoreFlowerChild D hS layer hLayer J b i then
    latticePoint L (roots ((layeredReconstruction D hS layer hLayer).garden.pair h.choose).1.1)
  else cc b.1.1 i

/-- **The constant value of the remaining dagger weight** on its support: over the skeleton branches `b` whose core is
a capped flower parent, `exp(i θ_b ‖k_b‖²) · ∏_{i ≠ flower} exp(-i θ_b ε_i ‖cc b.1.1 i‖²)` with
`θ_b = capTheta … (D.coreBranch hS b)` and `k_b = Σ_i ε_i k_i` (`restChildMom`). -/
def restConst (L γ δ s : ℝ) (J : Finset (Fin w)) (roots : Fin w → (Fin d → ℤ)) (cc : Fin w → Fin 3 → Mom d) : ℂ :=
  ∏ b ∈ univ.filter (fun b : GBranch S.tree =>
      IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS b)),
    Complex.exp (((capTheta L γ δ s (layeredReconstruction D hS layer hLayer).garden (D.coreBranch hS b) *
        ‖∑ i : Fin 3, childSign i • restChildMom D hS layer hLayer L J roots cc b i‖ ^ 2 : ℝ) : ℂ) * Complex.I) *
    ∏ i : Fin 3, if IsCoreFlowerChild D hS layer hLayer J b i then 1 else
      Complex.exp (((-(capTheta L γ δ s (layeredReconstruction D hS layer hLayer).garden (D.coreBranch hS b) *
        childSign i * ‖cc b.1.1 i‖ ^ 2) : ℝ) : ℂ) * Complex.I)

/-- The constant is unimodular. -/
theorem norm_restConst (L γ δ s : ℝ) (J : Finset (Fin w)) (roots : Fin w → (Fin d → ℤ))
    (cc : Fin w → Fin 3 → Mom d) : ‖restConst D hS layer hLayer L γ δ s J roots cc‖ = 1 := by
  unfold restConst
  rw [norm_prod]
  refine Finset.prod_eq_one fun b _ => ?_
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  split_ifs
  · exact norm_one
  · exact Complex.norm_exp_ofReal_mul_I _

/-- With no dagger datum the remaining dagger weight is `1`. -/
theorem restW_none (L γ δ s : ℝ) (J : Finset (Fin w)) (k : GNode (D.forest hS) → Mom d) :
    restW D hS layer hLayer L γ δ s J none k = 1 := by
  unfold restW
  refine Finset.prod_eq_one fun z _ => ?_
  split_ifs <;> rfl

namespace IntRest

open IntWeight

/-! ### One capped flower parent per tree -/

/-- With one capped flower per tree, a tree has at most one capped flower parent. -/
theorem cfp_eq_of_tree_eq (LG : LayeredGarden w) (J : Finset (Fin w))
    (hone : ∀ ℓ ℓ' : GLeaf LG.garden.tree, IsCapFlower LG J ℓ → IsCapFlower LG J ℓ' → ℓ.1.1 = ℓ'.1.1 → ℓ = ℓ')
    {B B' : GBranch LG.garden.tree} (hB : IsCapFlowerParent LG J B) (hB' : IsCapFlowerParent LG J B')
    (h : B.1.1 = B'.1.1) : B = B' := by
  obtain ⟨ℓ, hℓ, h1, i, h2⟩ := hB
  obtain ⟨ℓ', hℓ', h1', i', h2'⟩ := hB'
  have he : ℓ = ℓ' := hone ℓ ℓ' hℓ hℓ' (h1.trans (h.trans h1'.symm))
  subst he
  have hp : B.1.2 ++ [i] = B'.1.2 ++ [i'] := h2.symm.trans h2'
  exact Subtype.ext (Prod.ext h (List.append_inj_left' hp rfl))

/-- A capped flower parent is never a child of a capped flower parent. -/
theorem cfp_toNode_ne_child (LG : LayeredGarden w) (J : Finset (Fin w))
    (hone : ∀ ℓ ℓ' : GLeaf LG.garden.tree, IsCapFlower LG J ℓ → IsCapFlower LG J ℓ' → ℓ.1.1 = ℓ'.1.1 → ℓ = ℓ')
    {B B' : GBranch LG.garden.tree} (hB : IsCapFlowerParent LG J B) (hB' : IsCapFlowerParent LG J B')
    (i : Fin 3) : B.toNode ≠ B'.child i := by
  intro h
  have hv : B.1 = (B'.1.1, B'.1.2 ++ [i]) := congrArg Subtype.val h
  have h1 : B.1.1 = B'.1.1 := by have h' := congrArg Prod.fst hv; exact h'
  have h2 : B.1.2 = B'.1.2 ++ [i] := by have h' := congrArg Prod.snd hv; exact h'
  have he := cfp_eq_of_tree_eq LG J hone hB hB' h1
  subst he
  have hl := congrArg List.length h2
  simp at hl

variable {L γ δ s : ℝ}

/-- The node-local dagger weight at a capped flower parent is its parent phase factor. -/
theorem dagNodeW_at_cfp (LG : LayeredGarden w) (J : Finset (Fin w))
    (hone : ∀ ℓ ℓ' : GLeaf LG.garden.tree, IsCapFlower LG J ℓ → IsCapFlower LG J ℓ' → ℓ.1.1 = ℓ'.1.1 → ℓ = ℓ')
    (cc : Fin w → Fin 3 → Mom d) {B₀ : GBranch LG.garden.tree} (hB₀ : IsCapFlowerParent LG J B₀) (x : Mom d) :
    dagNodeW L γ δ s LG J (some cc) B₀.toNode x = dagParF L γ δ s LG B₀ x := by
  rw [dagNodeW_some]
  have h1 : ∏ B ∈ univ.filter (IsCapFlowerParent LG J),
      (if B.toNode = B₀.toNode then dagParF L γ δ s LG B x else 1) = dagParF L γ δ s LG B₀ x := by
    rw [Finset.prod_eq_single B₀]
    · exact ite_eq_left rfl
    · intro B _ hne
      exact ite_eq_right fun he => hne (toNode_inj he)
    · intro hn
      exact absurd (mem_filter.2 ⟨mem_univ _, hB₀⟩) hn
  have h2 : ∏ B ∈ univ.filter (IsCapFlowerParent LG J), ∏ i : Fin 3,
      (if B.child i = B₀.toNode then dagChE L γ δ s LG B i x * dagChI LG J cc B i B₀.toNode x else 1) = 1 :=
    Finset.prod_eq_one fun B hB => Finset.prod_eq_one fun i _ =>
      ite_eq_right fun he => cfp_toNode_ne_child LG J hone hB₀ (mem_filter.1 hB).2 i he.symm
  rw [h1, h2, mul_one]

/-- The node-local dagger weight at a non-flower child of a capped flower parent is its child phase factor times the
sibling indicator. -/
theorem dagNodeW_at_child (LG : LayeredGarden w) (J : Finset (Fin w))
    (hone : ∀ ℓ ℓ' : GLeaf LG.garden.tree, IsCapFlower LG J ℓ → IsCapFlower LG J ℓ' → ℓ.1.1 = ℓ'.1.1 → ℓ = ℓ')
    (cc : Fin w → Fin 3 → Mom d) {B₀ : GBranch LG.garden.tree} (hB₀ : IsCapFlowerParent LG J B₀) (i₀ : Fin 3)
    (hfl : ¬ ∃ ℓ : GLeaf LG.garden.tree, IsCapFlower LG J ℓ ∧ ℓ.toNode = B₀.child i₀) (j₀ : Fin w)
    (hj₀ : B₀.1.1 = j₀) (x : Mom d) :
    dagNodeW L γ δ s LG J (some cc) (B₀.child i₀) x =
      dagChE L γ δ s LG B₀ i₀ x * (if x = cc j₀ i₀ then 1 else 0) := by
  rw [dagNodeW_some]
  have h1 : ∏ B ∈ univ.filter (IsCapFlowerParent LG J),
      (if B.toNode = B₀.child i₀ then dagParF L γ δ s LG B x else 1) = 1 :=
    Finset.prod_eq_one fun B hB => ite_eq_right fun he =>
      cfp_toNode_ne_child LG J hone (mem_filter.1 hB).2 hB₀ i₀ he
  have h2 : ∏ B ∈ univ.filter (IsCapFlowerParent LG J), ∏ i : Fin 3,
      (if B.child i = B₀.child i₀ then dagChE L γ δ s LG B i x * dagChI LG J cc B i (B₀.child i₀) x else 1) =
      dagChE L γ δ s LG B₀ i₀ x * dagChI LG J cc B₀ i₀ (B₀.child i₀) x := by
    rw [Finset.prod_eq_single B₀]
    · rw [Finset.prod_eq_single i₀]
      · exact ite_eq_left rfl
      · intro i _ hne
        exact ite_eq_right fun he => hne (child_inj he).2
      · intro hn
        exact absurd (mem_univ _) hn
    · intro B _ hne
      exact Finset.prod_eq_one fun i _ => ite_eq_right fun he => hne (child_inj he).1
    · intro hn
      exact absurd (mem_filter.2 ⟨mem_univ _, hB₀⟩) hn
  rw [h1, h2, one_mul]
  unfold dagChI
  rw [ite_eq_right hfl, hj₀]

/-! ### Slots of the core branches and of their children -/

/-- The core branch of a skeleton branch is a native node of its chain slot. -/
theorem slotOf_core (b : GBranch S.tree) : slotOf D hS (D.coreBranch hS b).toNode = Sum.inr b := by
  rw [← chainContextNode_lone D hS b]
  exact slotOf_nativeNodeAt D hS (Sum.inr b) _

theorem coreBranch_injective : Function.Injective (D.coreBranch hS) := by
  intro b b' h
  have h1 := slotOf_core D hS b
  rw [h, slotOf_core D hS b'] at h1
  exact (Sum.inr_injective h1).symm

theorem coreBranch_fst (b : GBranch S.tree) : (D.coreBranch hS b).1.1 = b.1.1 :=
  inflatedPosition_index S D.tree b.toNode

/-- The attached node of a skeleton branch is the root of its chain. -/
theorem slotOf_attached_branch (b : GBranch S.tree) :
    slotOf D hS (attachedNode D hS b.toNode) = Sum.inr b := by
  rw [← chainContextNode_root D hS b]
  exact slotOf_nativeNodeAt D hS (Sum.inr b) _

theorem pairOfLeaf_sides (σ : GLeaf S.tree) :
    ((pairOfLeaf S hS σ).firstLeaf hS = σ ∧ (pairOfLeaf S hS σ).secondLeaf hS = S.pair σ) ∨
    ((pairOfLeaf S hS σ).firstLeaf hS = S.pair σ ∧ (pairOfLeaf S hS σ).secondLeaf hS = σ) := by
  by_cases hs : nodeSign S.sig σ.1 = 1
  · exact Or.inl (pairOfLeaf_sides_pos S hS σ hs)
  · exact Or.inr (pairOfLeaf_sides_neg S hS σ hs)

/-- The two roots of the native couple of the pair of a skeleton leaf `σ` are the attached nodes of `σ` and of its
partner. -/
theorem nativeRoot_cases (σ : GLeaf S.tree) (i : Fin 2) :
    (nativeCoupleForest D hS (pairOfLeaf S hS σ)).root i = attachedNode D hS σ.toNode ∨
      (nativeCoupleForest D hS (pairOfLeaf S hS σ)).root i = attachedNode D hS (S.pair σ).toNode := by
  have h0 : (nativeCoupleForest D hS (pairOfLeaf S hS σ)).root 0 =
      attachedNode D hS ((pairOfLeaf S hS σ).firstLeaf hS).toNode := rfl
  have h1 : (nativeCoupleForest D hS (pairOfLeaf S hS σ)).root 1 =
      attachedNode D hS ((pairOfLeaf S hS σ).secondLeaf hS).toNode := rfl
  fin_cases i
  · rcases pairOfLeaf_sides hS σ with ⟨e1, -⟩ | ⟨e1, -⟩
    · exact Or.inl (h0.trans (by rw [e1]))
    · exact Or.inr (h0.trans (by rw [e1]))
  · rcases pairOfLeaf_sides hS σ with ⟨-, e2⟩ | ⟨-, e2⟩
    · exact Or.inr (h1.trans (by rw [e2]))
    · exact Or.inl (h1.trans (by rw [e2]))

theorem exists_nativeRoot_eq (σ : GLeaf S.tree) (τ : GLeaf S.tree) (hτ : τ = σ ∨ τ = S.pair σ) :
    ∃ i : Fin 2, (nativeCoupleForest D hS (pairOfLeaf S hS σ)).root i = attachedNode D hS τ.toNode := by
  have h0 : (nativeCoupleForest D hS (pairOfLeaf S hS σ)).root 0 =
      attachedNode D hS ((pairOfLeaf S hS σ).firstLeaf hS).toNode := rfl
  have h1 : (nativeCoupleForest D hS (pairOfLeaf S hS σ)).root 1 =
      attachedNode D hS ((pairOfLeaf S hS σ).secondLeaf hS).toNode := rfl
  rcases pairOfLeaf_sides hS σ with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hτ with rfl | rfl
  · exact ⟨0, by rw [h0, e1]⟩
  · exact ⟨1, by rw [h1, e2]⟩
  · exact ⟨1, by rw [h1, e2]⟩
  · exact ⟨0, by rw [h0, e1]⟩

/-- The attached node of a skeleton leaf is a root of the native couple of its pair. -/
theorem slotOf_attached_leaf (σ : GLeaf S.tree) :
    slotOf D hS (attachedNode D hS σ.toNode) = Sum.inl (pairOfLeaf S hS σ) := by
  obtain ⟨i, hi⟩ := exists_nativeRoot_eq D hS σ σ (Or.inl rfl)
  rw [← hi, ← subforest_node_root]
  exact slotOf_nativeNodeAt D hS (Sum.inl _) _

theorem isCapPair_pairOfLeaf (J : Finset (Fin w)) (σ : GLeaf S.tree)
    (h : IsCapPair S hS J (pairOfLeaf S hS σ)) : σ.1.1 ∈ J ∨ (S.pair σ).1.1 ∈ J := by
  unfold IsCapPair at h
  rcases pairOfLeaf_sides hS σ with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] at h
  · exact h
  · exact h.symm

/-- Every node of a single-leaf reconstructed tree is its root. -/
theorem path_eq_nil_of_leafTree {j : Fin w} (hj : D.forest hS j = TTree.leaf) (z : GNode (D.forest hS))
    (hz : z.1.1 = j) : z.1.2 = [] := by
  have h := z.2
  rw [hz, hj] at h
  simpa [TTree.nodes] using h

/-- A core branch is not in a cap tree. -/
theorem core_tree_not_mem (J : Finset (Fin w)) (hcap : ∀ j ∈ J, (D.garden hS).tree j = TTree.leaf)
    (b : GBranch S.tree) : (D.coreBranch hS b).1.1 ∉ J := by
  intro hJ
  have h := (D.coreBranch hS b).2
  have hj : D.forest hS (D.coreBranch hS b).1.1 = TTree.leaf := hcap _ hJ
  rw [hj] at h
  simp [TTree.branching] at h

/-- **A core branch is not in a cap native.** -/
theorem not_inCapNative_core (J : Finset (Fin w)) (b : GBranch S.tree) :
    ¬ InCapNative D hS J (D.coreBranch hS b).toNode := by
  rintro ⟨q, hq, -⟩
  rw [slotOf_core] at hq
  exact Sum.inr_ne_inl hq

/-- **A non-flower child of a core capped flower parent is not in a cap native**: otherwise the native couple of the
pair of the skeleton child (a leaf paired with a cap root) would contain a second capped flower of the same tree. -/
theorem not_inCapNative_child {p : ℕ} (J : Finset (Fin w))
    (hG : CapGeo (layeredReconstruction D hS layer hLayer) J p) (b : GBranch S.tree)
    (hb : IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS b)) (i : Fin 3)
    (hfl : ¬ IsCoreFlowerChild D hS layer hLayer J b i) :
    ¬ InCapNative D hS J ((D.coreBranch hS b).child i) := by
  rintro ⟨q, hq, hcp⟩
  have hq' : slotOf D hS (attachedNode D hS (b.child i)) = Sum.inl q := by
    rw [attachedNode_child]; exact hq
  rcases (Comb.TreePath.mem_nodes_iff _ _).mp (b.child i).2 with hl | hbr
  · let σ : GLeaf S.tree := ⟨(b.child i).1, hl⟩
    have hσ : σ.toNode = b.child i := rfl
    rw [← hσ, slotOf_attached_leaf] at hq'
    have hqq : pairOfLeaf S hS σ = q := Sum.inl_injective hq'
    subst hqq
    have hzσ : attachedNode D hS σ.toNode = (D.coreBranch hS b).child i := attachedNode_child D hS b i
    -- the tree of `σ` is the tree of the core of `b`, not a cap tree
    have hσt : σ.1.1 = (D.coreBranch hS b).1.1 :=
      (inflatedPosition_index S D.tree σ.toNode).symm.trans (congrArg (fun a : GNode (D.forest hS) => a.1.1) hzσ)
    have hσJ : σ.1.1 ∉ J := by rw [hσt]; exact core_tree_not_mem D hS J hG.cap_leaf b
    have hpJ : (S.pair σ).1.1 ∈ J := (isCapPair_pairOfLeaf hS J σ hcp).resolve_left hσJ
    -- the attached node of the partner is the cap root `cL`
    have hj : D.forest hS (S.pair σ).1.1 = TTree.leaf := hG.cap_leaf _ hpJ
    have hc1 : (attachedNode D hS (S.pair σ).toNode).1.1 = (S.pair σ).1.1 :=
      inflatedPosition_index S D.tree (S.pair σ).toNode
    have hc2 : (attachedNode D hS (S.pair σ).toNode).1.2 = [] := path_eq_nil_of_leafTree D hS hj _ hc1
    let cL : GLeaf (D.forest hS) :=
      ⟨((S.pair σ).1.1, []), by show [] ∈ (D.forest hS (S.pair σ).1.1).leaves; rw [hj]; simp [TTree.leaves]⟩
    obtain ⟨ic, hic⟩ := exists_nativeRoot_eq D hS σ (S.pair σ) (Or.inr rfl)
    have hmem : cL ∈ Comb.RootedSubforest.leafSet (G := D.garden hS)
        (nativeCoupleForest D hS (pairOfLeaf S hS σ)) := by
      have h1 : ((nativeCoupleForest D hS (pairOfLeaf S hS σ)).root ic).1.1 = (S.pair σ).1.1 :=
        (congrArg (fun a : GNode (D.forest hS) => a.1.1) hic).trans hc1
      have h2 : ((nativeCoupleForest D hS (pairOfLeaf S hS σ)).root ic).1.2 = [] :=
        (congrArg (fun a : GNode (D.forest hS) => a.1.2) hic).trans hc2
      exact (Comb.RootedSubforest.mem_leafSet_iff (G := D.garden hS) _ _).mpr
        ⟨ic, And.intro h1 (List.prefix_nil.mpr h2)⟩
    have hcl := nativeCoupleForest_closed D hS (pairOfLeaf S hS σ) cL hmem
    obtain ⟨i', hi'⟩ := (Comb.RootedSubforest.mem_leafSet_iff (G := D.garden hS) _ _).mp hcl.2
    obtain ⟨hi1, hi2⟩ := hi'
    have hi1' : ((nativeCoupleForest D hS (pairOfLeaf S hS σ)).root i').1.1 = ((D.garden hS).pair cL).1.1 := hi1
    have hi2' : ((nativeCoupleForest D hS (pairOfLeaf S hS σ)).root i').1.2 <+: ((D.garden hS).pair cL).1.2 := hi2
    rcases nativeRoot_cases D hS σ i' with hr | hr
    · -- the partner of the cap root lies below the child: a second capped flower in the tree of `b`
      have hr1 : ((nativeCoupleForest D hS (pairOfLeaf S hS σ)).root i').1.1 = (D.coreBranch hS b).1.1 :=
        congrArg (fun a : GNode (D.forest hS) => a.1.1) (hr.trans hzσ)
      have hr2 : ((nativeCoupleForest D hS (pairOfLeaf S hS σ)).root i').1.2 = (D.coreBranch hS b).1.2 ++ [i] :=
        congrArg (fun a : GNode (D.forest hS) => a.1.2) (hr.trans hzσ)
      have hA1 : ((D.garden hS).pair cL).1.1 = (D.coreBranch hS b).1.1 := hi1'.symm.trans hr1
      have hA2 : (D.coreBranch hS b).1.2 ++ [i] <+: ((D.garden hS).pair cL).1.2 := by rw [← hr2]; exact hi2'
      have hPJ : ((D.garden hS).pair cL).1.1 ∉ J := by
        rw [hA1]; exact core_tree_not_mem D hS J hG.cap_leaf b
      have hPf : IsCapFlower (layeredReconstruction D hS layer hLayer) J ((D.garden hS).pair cL) := by
        refine ⟨hPJ, ?_⟩
        show ((D.garden hS).pair ((D.garden hS).pair cL)).1.1 ∈ J
        rw [(D.garden hS).pair_pair cL]
        exact hpJ
      obtain ⟨ℓ₀, hℓ₀, h01, i₀, h02⟩ := hb
      have he : ((D.garden hS).pair cL : GLeaf (layeredReconstruction D hS layer hLayer).garden.tree) = ℓ₀ :=
        hG.one_flower _ ℓ₀ hPf hℓ₀ (hA1.trans h01.symm)
      have hP2 : ((D.garden hS).pair cL).1.2 = ℓ₀.1.2 :=
        congrArg (fun x : GLeaf (layeredReconstruction D hS layer hLayer).garden.tree => x.1.2) he
      have hpre : (D.coreBranch hS b).1.2 ++ [i] <+: ℓ₀.1.2 := by rw [← hP2]; exact hA2
      have hlen : ((D.coreBranch hS b).1.2 ++ [i]).length = ℓ₀.1.2.length := by
        rw [h02, List.length_append, List.length_append]; rfl
      have hpe := hpre.eq_of_length hlen
      exact hfl ⟨ℓ₀, hℓ₀, Subtype.ext (Prod.ext h01 hpe.symm)⟩
    · -- the partner of the cap root lies below the cap root: it is the cap root itself, impossible
      have hr1 : ((nativeCoupleForest D hS (pairOfLeaf S hS σ)).root i').1.1 = (S.pair σ).1.1 :=
        (congrArg (fun a : GNode (D.forest hS) => a.1.1) hr).trans hc1
      have hP1 : ((D.garden hS).pair cL).1.1 = (S.pair σ).1.1 := hi1'.symm.trans hr1
      have hP2 : ((D.garden hS).pair cL).1.2 = [] :=
        path_eq_nil_of_leafTree D hS hj ((D.garden hS).pair cL).toNode hP1
      exact hcl.1 (Subtype.ext (Prod.ext hP1 hP2))
  · let b' : GBranch S.tree := ⟨(b.child i).1, hbr⟩
    have hb' : b'.toNode = b.child i := rfl
    rw [← hb', slotOf_attached_branch] at hq'
    exact Sum.inr_ne_inl hq'

/-- **No case-b node lies in a cap native.** -/
theorem not_inCapNative_of_isCaseB {p : ℕ} (J : Finset (Fin w))
    (hG : CapGeo (layeredReconstruction D hS layer hLayer) J p) (z : GNode (D.forest hS))
    (hz : IsCaseB D hS layer hLayer J z) : ¬ InCapNative D hS J z := by
  obtain ⟨b, hb, rfl | ⟨i, rfl, hfl⟩⟩ := hz
  · exact not_inCapNative_core D hS J b
  · exact not_inCapNative_child D hS layer hLayer J hG b hb i hfl

/-! ### The remaining dagger weight as a product over the skeleton branches -/

/-- Pointwise form of the factor of `restW` at a node. -/
theorem caseB_factor {p : ℕ} (J : Finset (Fin w)) (hG : CapGeo (layeredReconstruction D hS layer hLayer) J p)
    (cc : Fin w → Fin 3 → Mom d) (z : GNode (D.forest hS)) (x : Mom d) :
    (if IsCaseB D hS layer hLayer J z then
        dagNodeW L γ δ s (layeredReconstruction D hS layer hLayer) J (some cc) z x else 1) =
      (∏ b ∈ univ.filter (fun b : GBranch S.tree =>
          IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS b)),
        if (D.coreBranch hS b).toNode = z then
          dagParF L γ δ s (layeredReconstruction D hS layer hLayer) (D.coreBranch hS b) x else 1) *
      ∏ b ∈ univ.filter (fun b : GBranch S.tree =>
          IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS b)),
        ∏ i : Fin 3, if (D.coreBranch hS b).child i = z ∧ ¬ IsCoreFlowerChild D hS layer hLayer J b i then
          dagChE L γ δ s (layeredReconstruction D hS layer hLayer) (D.coreBranch hS b) i x *
            (if x = cc b.1.1 i then 1 else 0) else 1 := by
  have hone := hG.one_flower
  by_cases hz : IsCaseB D hS layer hLayer J z
  · rw [ite_eq_left hz]
    obtain ⟨b₀, hb₀, hz' | ⟨i₀, hz', hfl⟩⟩ := hz
    · subst hz'
      refine (dagNodeW_at_cfp (layeredReconstruction D hS layer hLayer) J hone cc hb₀ x).trans ?_
      have h1 : ∏ b ∈ univ.filter (fun b : GBranch S.tree =>
            IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS b)),
          (if (D.coreBranch hS b).toNode = (D.coreBranch hS b₀).toNode then
            dagParF L γ δ s (layeredReconstruction D hS layer hLayer) (D.coreBranch hS b) x else 1) =
          dagParF L γ δ s (layeredReconstruction D hS layer hLayer) (D.coreBranch hS b₀) x := by
        rw [Finset.prod_eq_single b₀]
        · exact ite_eq_left rfl
        · intro b _ hne
          exact ite_eq_right fun he => hne (coreBranch_injective D hS (toNode_inj he))
        · intro hn
          exact (hn (mem_filter.2 ⟨mem_univ b₀, hb₀⟩)).elim
      have h2 : ∏ b ∈ univ.filter (fun b : GBranch S.tree =>
            IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS b)),
          ∏ i : Fin 3, (if (D.coreBranch hS b).child i = (D.coreBranch hS b₀).toNode ∧
              ¬ IsCoreFlowerChild D hS layer hLayer J b i then
            dagChE L γ δ s (layeredReconstruction D hS layer hLayer) (D.coreBranch hS b) i x *
              (if x = cc b.1.1 i then 1 else 0) else 1) = 1 :=
        Finset.prod_eq_one fun b hb => Finset.prod_eq_one fun i _ => ite_eq_right fun he =>
          cfp_toNode_ne_child (layeredReconstruction D hS layer hLayer) J hone hb₀ (mem_filter.1 hb).2 i he.1.symm
      rw [h1, h2, mul_one]
    · subst hz'
      have hfl' : ¬ IsCoreFlowerChild D hS layer hLayer J b₀ i₀ := hfl
      refine (dagNodeW_at_child (layeredReconstruction D hS layer hLayer) J hone cc hb₀ i₀ hfl b₀.1.1
        (coreBranch_fst D hS b₀) x).trans ?_
      have h1 : ∏ b ∈ univ.filter (fun b : GBranch S.tree =>
            IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS b)),
          (if (D.coreBranch hS b).toNode = (D.coreBranch hS b₀).child i₀ then
            dagParF L γ δ s (layeredReconstruction D hS layer hLayer) (D.coreBranch hS b) x else 1) = 1 :=
        Finset.prod_eq_one fun b hb => ite_eq_right fun he =>
          cfp_toNode_ne_child (layeredReconstruction D hS layer hLayer) J hone (mem_filter.1 hb).2 hb₀ i₀ he
      have h2 : ∏ b ∈ univ.filter (fun b : GBranch S.tree =>
            IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS b)),
          ∏ i : Fin 3, (if (D.coreBranch hS b).child i = (D.coreBranch hS b₀).child i₀ ∧
              ¬ IsCoreFlowerChild D hS layer hLayer J b i then
            dagChE L γ δ s (layeredReconstruction D hS layer hLayer) (D.coreBranch hS b) i x *
              (if x = cc b.1.1 i then 1 else 0) else 1) =
          dagChE L γ δ s (layeredReconstruction D hS layer hLayer) (D.coreBranch hS b₀) i₀ x *
            (if x = cc b₀.1.1 i₀ then 1 else 0) := by
        rw [Finset.prod_eq_single b₀]
        · rw [Finset.prod_eq_single i₀]
          · exact ite_eq_left ⟨rfl, hfl'⟩
          · intro i _ hne
            exact ite_eq_right fun he => hne (child_inj he.1).2
          · intro hn
            exact absurd (mem_univ _) hn
        · intro b _ hne
          exact Finset.prod_eq_one fun i _ => ite_eq_right fun he =>
            hne (coreBranch_injective D hS (child_inj he.1).1)
        · intro hn
          exact (hn (mem_filter.2 ⟨mem_univ b₀, hb₀⟩)).elim
      rw [h1, h2, one_mul]
  · rw [ite_eq_right hz]
    symm
    rw [Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
    · intro b hb
      refine Finset.prod_eq_one fun i _ => ite_eq_right fun he => ?_
      exact hz ⟨b, (mem_filter.1 hb).2, Or.inr ⟨i, he.1.symm, by rw [← he.1]; exact he.2⟩⟩
    · intro b hb
      exact ite_eq_right fun he => hz ⟨b, (mem_filter.1 hb).2, Or.inl he.symm⟩

/-- **The remaining dagger weight as a product over the skeleton branches** whose core is a capped flower parent:
the parent phase factor at the core, and the child phase factor times the sibling indicator at each non-flower
child. -/
theorem restW_some_eq {p : ℕ} (J : Finset (Fin w)) (hG : CapGeo (layeredReconstruction D hS layer hLayer) J p)
    (cc : Fin w → Fin 3 → Mom d) (k : GNode (D.forest hS) → Mom d) :
    restW D hS layer hLayer L γ δ s J (some cc) k =
      (∏ b ∈ univ.filter (fun b : GBranch S.tree =>
          IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS b)),
        dagParF L γ δ s (layeredReconstruction D hS layer hLayer) (D.coreBranch hS b)
          (k (D.coreBranch hS b).toNode)) *
      ∏ b ∈ univ.filter (fun b : GBranch S.tree =>
          IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS b)),
        ∏ i : Fin 3, if IsCoreFlowerChild D hS layer hLayer J b i then 1 else
          dagChE L γ δ s (layeredReconstruction D hS layer hLayer) (D.coreBranch hS b) i
              (k ((D.coreBranch hS b).child i)) *
            (if k ((D.coreBranch hS b).child i) = cc b.1.1 i then 1 else 0) := by
  unfold restW
  have h1 : ∀ z : GNode (D.forest hS),
      (if ¬ InCapNative D hS J z ∧ IsCaseB D hS layer hLayer J z then
        dagNodeW L γ δ s (layeredReconstruction D hS layer hLayer) J (some cc) z (k z) else 1) =
      (if IsCaseB D hS layer hLayer J z then
        dagNodeW L γ δ s (layeredReconstruction D hS layer hLayer) J (some cc) z (k z) else 1) := by
    intro z
    by_cases hz : IsCaseB D hS layer hLayer J z
    · rw [ite_eq_left hz, ite_eq_left ⟨not_inCapNative_of_isCaseB D hS layer hLayer J hG z hz, hz⟩]
    · rw [ite_eq_right hz, ite_eq_right fun h => hz h.2]
  rw [Finset.prod_congr rfl fun z _ => (h1 z).trans (caseB_factor D hS layer hLayer J hG cc z (k z)),
    Finset.prod_mul_distrib]
  congr 1
  · rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [Finset.prod_ite_eq, ite_eq_left (mem_univ _)]
  · rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hf : IsCoreFlowerChild D hS layer hLayer J b i
    · rw [ite_eq_left hf]
      exact Finset.prod_eq_one fun z _ => ite_eq_right fun he => he.2 hf
    · rw [ite_eq_right hf]
      simp only [hf, not_false_eq_true, and_true]
      rw [Finset.prod_ite_eq, ite_eq_left (mem_univ _)]

/-! ### The momenta on a decoration -/

theorem latticePoint_sub_add (L : ℝ) (a b c : Fin d → ℤ) :
    latticePoint L (a - b + c) = latticePoint L a - latticePoint L b + latticePoint L c := by
  rw [WeylSums.latticePoint_add_eq]
  congr 1
  rw [eq_sub_iff_add_eq, ← WeylSums.latticePoint_add_eq, sub_add_cancel]

/-- On the support, the momentum of every child of a core capped flower parent is `restChildMom`. -/
theorem latticePoint_child {p : ℕ} (J : Finset (Fin w)) (hG : CapGeo (layeredReconstruction D hS layer hLayer) J p)
    (cc : Fin w → Fin 3 → Mom d) {roots : Fin w → (Fin d → ℤ)} (κ : GenDecoration (D.garden hS) d roots 0)
    (hI : RestInd D hS layer hLayer L J cc (collapseGenDecoration D hS κ)) (b : GBranch S.tree)
    (hb : IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS b)) (i : Fin 3) :
    latticePoint L (κ.1 ((D.coreBranch hS b).child i)) = restChildMom D hS layer hLayer L J roots cc b i := by
  unfold restChildMom
  by_cases hf : IsCoreFlowerChild D hS layer hLayer J b i
  · rw [dite_eq_left hf]
    obtain ⟨hs1, hs2⟩ := hf.choose_spec
    have e1 : κ.1 ((D.coreBranch hS b).child i) = κ.1 hf.choose.toNode :=
      congrArg (fun a : GNode (D.forest hS) => κ.1 a) hs2.symm
    have e2 : κ.1 hf.choose.toNode =
        roots ((layeredReconstruction D hS layer hLayer).garden.pair hf.choose).1.1 :=
      (κ.2.1.2 hf.choose).trans (genDec_cap (D.garden hS) J hG.cap_leaf κ _ hs1.2)
    exact congrArg (latticePoint L) (e1.trans e2)
  · rw [dite_eq_right hf]
    refine Eq.trans ?_ (hI b hb i hf)
    show latticePoint L (κ.1 ((D.coreBranch hS b).child i)) =
      0 + latticePoint L (κ.1 (attachedNode D hS (b.child i)))
    rw [zero_add]
    exact congrArg (fun a : GNode (D.forest hS) => latticePoint L (κ.1 a)) (attachedNode_child D hS b i).symm

/-- On the support, the momentum of a core capped flower parent is `Σ_i ε_i k_i`. -/
theorem coset_core {p : ℕ} (J : Finset (Fin w)) (hG : CapGeo (layeredReconstruction D hS layer hLayer) J p)
    (cc : Fin w → Fin 3 → Mom d) {roots : Fin w → (Fin d → ℤ)} (κ : GenDecoration (D.garden hS) d roots 0)
    (hI : RestInd D hS layer hLayer L J cc (collapseGenDecoration D hS κ)) (b : GBranch S.tree)
    (hb : IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS b)) :
    cosetDecoration (D.garden hS) L 0 κ.1 (D.coreBranch hS b).toNode =
      ∑ i : Fin 3, childSign i • restChildMom D hS layer hLayer L J roots cc b i := by
  have e1 : κ.1 (D.coreBranch hS b).toNode = κ.1 ((D.coreBranch hS b).child 0) -
      κ.1 ((D.coreBranch hS b).child 1) + κ.1 ((D.coreBranch hS b).child 2) := κ.2.1.1 (D.coreBranch hS b)
  show 0 + latticePoint L (κ.1 (D.coreBranch hS b).toNode) = _
  rw [e1, zero_add, latticePoint_sub_add,
    latticePoint_child D hS layer hLayer J hG cc κ hI b hb 0,
    latticePoint_child D hS layer hLayer J hG cc κ hI b hb 1,
    latticePoint_child D hS layer hLayer J hG cc κ hI b hb 2, Fin.sum_univ_three]
  have h0 : childSign 0 = 1 := by simp [childSign]
  have h1 : childSign 1 = -1 := by simp [childSign]
  have h2 : childSign 2 = 1 := by simp [childSign]
  rw [h0, h1, h2, one_smul, one_smul, neg_one_smul, sub_eq_add_neg]

/-- **The remaining dagger weight on a momentum assignment** whose non-flower children of core capped flower parents
carry `cc` exactly when `Ind` holds, and whose core capped flower parents carry `Σ_i ε_i k_i` when `Ind` holds. -/
theorem restW_eq_ind {p : ℕ} (J : Finset (Fin w)) (hG : CapGeo (layeredReconstruction D hS layer hLayer) J p)
    (cc : Fin w → Fin 3 → Mom d) (roots : Fin w → (Fin d → ℤ)) (k : GNode (D.forest hS) → Mom d) (Ind : Prop)
    (hInd : Ind ↔ ∀ b : GBranch S.tree,
      IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS b) → ∀ i : Fin 3,
        ¬ IsCoreFlowerChild D hS layer hLayer J b i → k ((D.coreBranch hS b).child i) = cc b.1.1 i)
    (hcore : Ind → ∀ b : GBranch S.tree,
      IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS b) →
        k (D.coreBranch hS b).toNode = ∑ i : Fin 3, childSign i • restChildMom D hS layer hLayer L J roots cc b i) :
    restW D hS layer hLayer L γ δ s J (some cc) k =
      if Ind then restConst D hS layer hLayer L γ δ s J roots cc else 0 := by
  rw [restW_some_eq D hS layer hLayer J hG cc k]
  by_cases hI : Ind
  · rw [ite_eq_left hI]
    have hI' := hInd.1 hI
    unfold restConst
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun b hb => ?_
    have hbT := (mem_filter.1 hb).2
    congr 1
    · unfold dagParF
      rw [hcore hI b hbT]
    · refine Finset.prod_congr rfl fun i _ => ?_
      by_cases hf : IsCoreFlowerChild D hS layer hLayer J b i
      · rw [ite_eq_left hf, ite_eq_left hf]
      · rw [ite_eq_right hf, ite_eq_right hf, hI' b hbT i hf, ite_eq_left rfl, mul_one]
        rfl
  · rw [ite_eq_right hI]
    rw [hInd] at hI
    push Not at hI
    obtain ⟨b, hb, i, hf, hne⟩ := hI
    apply mul_eq_zero_of_right
    refine Finset.prod_eq_zero (i := b) (mem_filter.2 ⟨mem_univ b, hb⟩) ?_
    refine Finset.prod_eq_zero (i := i) (mem_univ i) ?_
    rw [ite_eq_right hf, ite_eq_right hne, mul_zero]

end IntRest

open IntRest in
/-- **Constancy of the remaining dagger weight.** On every decoration `κ` of the reconstruction at coset base `0`, the
remaining dagger weight is the indicator of the skeleton-level sibling condition `RestInd` on the collapsed skeleton
decoration, times the unimodular constant `restConst`. -/
theorem restW_cosetDecoration {p : ℕ} (J : Finset (Fin w))
    (hG : CapGeo (layeredReconstruction D hS layer hLayer) J p) (L γ δ s : ℝ) (roots : Fin w → (Fin d → ℤ))
    (cc : Fin w → Fin 3 → Mom d) (κ : GenDecoration (D.garden hS) d roots 0) :
    restW D hS layer hLayer L γ δ s J (some cc) (cosetDecoration (D.garden hS) L 0 κ.1) =
      if RestInd D hS layer hLayer L J cc (collapseGenDecoration D hS κ) then
        restConst D hS layer hLayer L γ δ s J roots cc else 0 := by
  have hch : ∀ (b : GBranch S.tree) (i : Fin 3),
      cosetDecoration (D.garden hS) L 0 κ.1 ((D.coreBranch hS b).child i) =
        cosetDecoration S L 0 (collapseGenDecoration D hS κ).1 (b.child i) := by
    intro b i
    show 0 + latticePoint L (κ.1 ((D.coreBranch hS b).child i)) =
      0 + latticePoint L (κ.1 (attachedNode D hS (b.child i)))
    exact congrArg (fun a : GNode (D.forest hS) => 0 + latticePoint L (κ.1 a)) (attachedNode_child D hS b i).symm
  refine restW_eq_ind D hS layer hLayer J hG cc roots (cosetDecoration (D.garden hS) L 0 κ.1) _ ?_ ?_
  · constructor
    · intro h b hb i hf
      exact (hch b i).trans (h b hb i hf)
    · intro h b hb i hf
      exact (hch b i).symm.trans (h b hb i hf)
  · intro hI b hb
    exact coset_core D hS layer hLayer J hG cc κ hI b hb

end WaveTurbulence.Flower.MkSlots
