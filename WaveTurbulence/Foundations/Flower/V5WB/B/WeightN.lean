/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceB.Weight
public import WaveTurbulence.Foundations.Flower.V5W.Weight
public import WaveTurbulence.Foundations.VineEst.ZpSurj.Coh3
public import WaveTurbulence.Foundations.VineEst.RowSel.Coherent

/-! # V5W-B-WORLD B4: the masked, normalized bond weight of a state and its exact transport

The multiplier of V5W-0's pinned kernel is the R135 bond product over the darts of the region whose row is coherent
(`regionWeightFW`), and the row product carries the normalization `rowNorm` of the incoherent rows
(`V5WB.clLocalStarProductFW_eq`).  Both are products over the bonds of the region (the PC bond of a nonroot branch `c`
carries the tree row of `c`, the LP bond of a leaf the couple row of its pair), so both ride on one per-dart weight:

* `ΨX W X y`: at a dart `y` of the state `X` whose row is coherent, the bond factor `W.ψ`; at a dart whose row is
  incoherent, the constant `W.c ^ (e / 2)`, `e = 2·order + 2` (couples) / `2·order + 1` (trees) of the row
  (`nodeRowExp`), so that the two darts of the bond give the row's normalization.
* `bondWD`: V5-SPACE-EXT's `bondW` with a dart-indexed weight; `bWN W κ X U`: the weight of the block `U` of `X`.

Transport (`bWN_false`, `bWN_rigid`, `bWN_twist`, `bWN_twNode`, the masked forms of V5-SPACE-EXT's `bW_*`): along an
operation the dart map is the naive one off the four exceptional incidences, and there the rows are ordinary, so their
incoherency and order are kept (`treeIncoh_LF`, `coupleIncoh_LF`, `native_tree_eq`, `native_couple_eq`); at the
exceptional incidences the rows are the exceptional tree and couple, coherent in the source (`htc`, `hcc`, through
`ZpSurj.nativeCoh_of_cohOn`) and in the output (`ZpSurj.nativeCoh_op`), so both sides carry the bond factor.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.Flower.V5WB
open WaveTurbulence TTree Twist LFTwist RegRed Reg.Skeleton VineEstS4 VineEstS5B Links
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts layX layX_true layX_false twistDartEquiv_eq_naive
  dartNode_naive regionDarts_union regionDarts_disjoint dartNode_mem_splitA dartNode_mem_support)
open WaveTurbulence.Flower.V5W (nodeRowIncoh nodeRowIncoh_branch nodeRowIncoh_leaf coupleIncoh treeIncoh
  treeIncoh_LF coupleIncoh_LF tp_pairOfLeaf pairOfLeaf_ne_exceptional eq_or_pair_of_pairOfLeaf)

/-! ## The exponent of the row of a node -/

section Exp
variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer)

open Classical in
/-- The normalization exponent of the row carried by a skeleton node (a branch: `2·order + 1` of its tree; a leaf:
`2·order + 2` of the couple of its source pair). -/
def nodeRowExp (x : GNode S.tree) : ℕ :=
  if h : ∃ c : GBranch S.tree, c.toNode = x then 2 * (nativeChainLayered D hS layer hLayer h.choose).garden.order + 1
  else if h' : ∃ pr : SourcePair S, (pr.firstLeaf hS).toNode = x ∨ (pr.secondLeaf hS).toNode = x then
    2 * (nativeCoupleLayered D hS layer hLayer h'.choose).garden.order + 2
  else 0

theorem nodeRowExp_branch (c : GBranch S.tree) :
    nodeRowExp D hS layer hLayer c.toNode = 2 * (nativeChainLayered D hS layer hLayer c).garden.order + 1 := by
  have h : ∃ c' : GBranch S.tree, c'.toNode = c.toNode := ⟨c, rfl⟩
  unfold nodeRowExp
  rw [dif_pos h, Mole.branch_toNode_injective h.choose_spec]

theorem nodeRowExp_leaf (l : GLeaf S.tree) :
    nodeRowExp D hS layer hLayer l.toNode =
      2 * (nativeCoupleLayered D hS layer hLayer (pairOfLeaf S hS l)).garden.order + 2 := by
  have hb : ¬ ∃ c : GBranch S.tree, c.toNode = l.toNode := fun ⟨c, hc⟩ => Mole.branch_toNode_ne_leaf c l hc
  have hq : ∃ pr : SourcePair S, (pr.firstLeaf hS).toNode = l.toNode ∨ (pr.secondLeaf hS).toNode = l.toNode := by
    refine ⟨pairOfLeaf S hS l, ?_⟩
    by_cases hs : nodeSign S.sig l.1 = 1
    · exact Or.inl (congrArg GLeaf.toNode (pairOfLeaf_sides_pos S hS l hs).1)
    · exact Or.inr (congrArg GLeaf.toNode (pairOfLeaf_sides_neg S hS l hs).2)
  unfold nodeRowExp
  rw [dif_neg hb, dif_pos hq]
  have he : hq.choose = pairOfLeaf S hS l := by
    rcases hq.choose_spec with h1 | h1
    · exact (pairOfLeaf_firstLeaf S hS _).symm.trans (congrArg (pairOfLeaf S hS) (Mole.leaf_toNode_injective h1))
    · exact (pairOfLeaf_secondLeaf S hS _).symm.trans (congrArg (pairOfLeaf S hS) (Mole.leaf_toNode_injective h1))
  rw [he]

end Exp

/-! ## The dart weight -/

/-- The data of the dart weight: the bond factor `ψ` of a coherent row and the normalization constant `c`. -/
structure WD (d : ℕ) where
  ψ : ℕ → ℕ → Mom d → ℂ
  c : ℝ

variable {w d : ℕ} {ι : Type*}

/-- **The dart weight of a state**: the bond factor on a coherent row, `c ^ (e/2)` on an incoherent one. -/
def ΨX (W : WD d) (X : FamilyReconstruction w ι) (y : GardenDart X.skeleton) (q q' : ℕ) (k : Mom d) : ℂ :=
  if nodeRowIncoh X.data X.plain (stateLayer X) (stateLayer_isLayering X) (Mole.dartNode X.skeleton y) = 0 then
    W.ψ q q' k
  else ((W.c ^ ((nodeRowExp X.data X.plain (stateLayer X) (stateLayer_isLayering X)
    (Mole.dartNode X.skeleton y) : ℝ) / 2) : ℝ) : ℂ)

/-- V5-SPACE-EXT's `bondW` with a dart-indexed weight. -/
def bondWD (G : Garden w) (Ψ : GardenDart G → ℕ → ℕ → Mom d → ℂ) (L : ℝ) (base : Mom d)
    (lay : GBranch G.tree → ℕ) (U : Finset (GBranch G.tree)) (x : GNode G.tree → Fin d → ℤ) : ℂ :=
  ∏ y ∈ regionDarts G U, Ψ y (lay (G.molecule.atom (G.molecule.mate y))) (lay (G.molecule.atom y))
    (cosetDecoration G L base x (Mole.dartNode G y))

/-- **The masked, normalized bond weight of the block `U` of a state.** -/
def bWN (W : WD d) (κ : KPar d) (X : FamilyReconstruction w ι) (U : Finset (GBranch X.skeleton.tree)) :
    (GNode X.skeleton.tree → Fin d → ℤ) → ℂ :=
  bondWD X.skeleton (ΨX W X) κ.L κ.base (layX X) U

/-- The bound of the weight of a block (independent of the labels). -/
def bWNB (W : WD d) (X : FamilyReconstruction w ι) (U : Finset (GBranch X.skeleton.tree)) (C : ℝ) : ℝ :=
  ∏ y ∈ regionDarts X.skeleton U, max C |W.c ^ ((nodeRowExp X.data X.plain (stateLayer X) (stateLayer_isLayering X)
    (Mole.dartNode X.skeleton y) : ℝ) / 2)|

theorem bWNB_nonneg (W : WD d) (X : FamilyReconstruction w ι) (U : Finset (GBranch X.skeleton.tree)) {C : ℝ}
    (hC : 0 ≤ C) : 0 ≤ bWNB W X U C :=
  Finset.prod_nonneg fun _ _ => le_max_of_le_left hC

theorem norm_bWN_le (W : WD d) (κ : KPar d) (X : FamilyReconstruction w ι) (U : Finset (GBranch X.skeleton.tree))
    (C : ℝ) (hψ : ∀ q q' k, ‖W.ψ q q' k‖ ≤ C) (x : GNode X.skeleton.tree → Fin d → ℤ) :
    ‖bWN W κ X U x‖ ≤ bWNB W X U C := by
  unfold bWN bondWD bWNB
  rw [norm_prod]
  gcongr with y hy
  unfold ΨX
  split_ifs
  · exact (hψ _ _ _).trans (le_max_left _ _)
  · rw [Complex.norm_real, Real.norm_eq_abs]
    exact le_max_right _ _

section Bond
variable {G : Garden w}

theorem bondWD_congr (Ψ : GardenDart G → ℕ → ℕ → Mom d → ℂ) (L : ℝ) (base : Mom d)
    {lay lay' : GBranch G.tree → ℕ} (U : Finset (GBranch G.tree)) {x x' : GNode G.tree → Fin d → ℤ}
    (hl : ∀ v ∈ U, lay v = lay' v) (hx : ∀ y ∈ regionDarts G U, x (Mole.dartNode G y) = x' (Mole.dartNode G y)) :
    bondWD G Ψ L base lay U x = bondWD G Ψ L base lay' U x' := by
  unfold bondWD
  refine Finset.prod_congr rfl fun y hy => ?_
  have hy' := mem_regionDarts.mp hy
  rw [hl _ hy'.1, hl _ hy'.2]
  unfold cosetDecoration
  rw [hx y hy]

/-- **Exact transport along a unit twist**, given the dart weights, bond labels and core layers. -/
theorem bondWD_transport (Ψ : GardenDart G → ℕ → ℕ → Mom d → ℂ) (L : ℝ) (base : Mom d) (P : CorePlacement G)
    (Ψ' : GardenDart (unitTwistGarden G P) → ℕ → ℕ → Mom d → ℂ)
    (lay : GBranch G.tree → ℕ) (lay' : GBranch (unitTwistGarden G P).tree → ℕ) (U : Finset (GBranch G.tree))
    (κ : GNode G.tree → Fin d → ℤ) (κ' : GNode (unitTwistGarden G P).tree → Fin d → ℤ)
    (hΨ : ∀ y ∈ regionDarts G U, Ψ' (twistDartEquiv G P y) = Ψ y)
    (hlab : ∀ y ∈ regionDarts G U,
      Mole.restrictLabels (unitTwistGarden G P) κ' (twistDartEquiv G P y) = Mole.restrictLabels G κ y)
    (hlay : ∀ v ∈ U, lay' (coreBranchEquiv G P v) = lay v) :
    bondWD (unitTwistGarden G P) Ψ' L base lay' (twistedAtoms G P U) κ' = bondWD G Ψ L base lay U κ := by
  unfold bondWD
  symm
  refine Finset.prod_equiv (twistDartEquiv G P) (fun y => ?_) (fun y hy => ?_)
  · simp only [mem_regionDarts, Molecule.InGroup, twistDartEquiv_atom, twistDartEquiv_mate]
    exact and_congr (mem_twistedAtoms G P U _).symm (mem_twistedAtoms G P U _).symm
  · have hy' := mem_regionDarts.mp hy
    rw [twistDartEquiv_mate, twistDartEquiv_atom, twistDartEquiv_atom, hlay _ hy'.1, hlay _ hy'.2, hΨ y hy]
    unfold cosetDecoration
    have h := hlab y hy
    unfold Mole.restrictLabels at h
    rw [h]

theorem bondWD_union (Ψ : GardenDart G → ℕ → ℕ → Mom d → ℂ) (L : ℝ) (base : Mom d) (lay : GBranch G.tree → ℕ)
    {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}
    (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c) (hi : S ∩ T = {b})
    (hU : G.molecule.IsBlock (S ∪ T) a c) (x : GNode G.tree → Fin d → ℤ) :
    bondWD G Ψ L base lay (S ∪ T) x = bondWD G Ψ L base lay S x * bondWD G Ψ L base lay T x := by
  unfold bondWD
  rw [regionDarts_union hS hT hi hU, Finset.prod_union (regionDarts_disjoint hS hT hi hU)]

variable (Ψ : GardenDart G → ℕ → ℕ → Mom d → ℂ) (L : ℝ) (base : Mom d) (lay : GBranch G.tree → ℕ)

theorem bondWD_rA {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} (RS : CLRegionData G S a b)
    (x : GNode G.tree → Fin d → ℤ) : bondWD G Ψ L base lay S (rA RS x) = bondWD G Ψ L base lay S x :=
  bondWD_congr Ψ L base S (fun _ _ => rfl) (fun _y hy => by
    simp only [rA, dartNode_mem_splitA RS hy, ite_true])

theorem bondWD_rB {T : Finset (GBranch G.tree)} {b c : GBranch G.tree} (RT : CLRegionData G T b c)
    (x : GNode G.tree → Fin d → ℤ) : bondWD G Ψ L base lay T (rB RT x) = bondWD G Ψ L base lay T x :=
  bondWD_congr Ψ L base T (fun _ _ => rfl) (fun _y hy => by
    simp only [rB, dartNode_mem_support RT hy, ite_true])

theorem bondWD_glue_S {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} (RS : CLRegionData G S a b)
    (xS xT : GNode G.tree → Fin d → ℤ) :
    bondWD G Ψ L base lay S (glue RS xS xT) = bondWD G Ψ L base lay S xS :=
  bondWD_congr Ψ L base S (fun _ _ => rfl) (fun _y hy => glue_A RS xS xT (dartNode_mem_splitA RS hy))

theorem bondWD_glue_T {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}
    (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c) (hi : S ∩ T = {b})
    (hU : G.molecule.IsBlock (S ∪ T) a c) (RS : CLRegionData G S a b) (RT : CLRegionData G T b c)
    {L' : ℝ} (hL : L' ≠ 0) {base' : Mom d} {xS xT : GNode G.tree → Fin d → ℤ} {β2 β3 : Mom d}
    (hc : BdAt RT L' base' (bdT RT L' base' xS β2 β3) xT) :
    bondWD G Ψ L base lay T (glue RS xS xT) = bondWD G Ψ L base lay T xT :=
  bondWD_congr Ψ L base T (fun _ _ => rfl) (fun _y hy =>
    glue_B hS hT hi hU RS RT hL hc (dartNode_mem_support RT hy))

end Bond

end WaveTurbulence.Flower.V5WB
