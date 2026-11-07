/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.BranchSplit
import Mathlib.Tactic

/-!
# VINE-B: splitting the decorations of the skeleton

A `(k_1, …, k_{2R})`-decoration of `S = G_sk` is the same as a decoration `z` of `G_sb` together with, for every unit
`U_j`, a local decoration of the realization `G_sk[U_j]` (V5's `CLLocalDecoration`) whose four boundary momenta are
`(k_{u1}, k_{u11}, k_{u21}, k_{u22})` read off `z` (`decSplit`, TARGET L1950–L1957: the decorations of the
realizations are summed inside `K^{U_j}`).  Conservation at a hinge of `G_sb` is the signed conservation of the whole
block (`block_signed_conservation`), and the boundary momenta of a unit are retained nodes.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineB
open TTree WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S}
  {Gsb : Garden w}

/-! ## The three boundary nodes -/

theorem crown_distinct (u : CLBlock S) :
    u.upper.child (regionOf u).excluded ≠ u.lower.child (regionOf u).positive ∧
      u.upper.child (regionOf u).excluded ≠ u.lower.child (regionOf u).negative ∧
        u.lower.child (regionOf u).positive ≠ u.lower.child (regionOf u).negative := by
  have hab : u.upper ≠ u.lower := u.isBlock.2.2.2.1
  refine ⟨fun h => hab (child_inj h).1, fun h => hab (child_inj h).1, fun h => ?_⟩
  exact (regionOf u).distinct (child_inj h).2

/-- A sum over any injective enumeration of the three boundary nodes. -/
theorem sum_crown (u : CLBlock S) {M : Type*} [AddCommMonoid M] (g : Fin 3 → GNode S.tree)
    (hg : Function.Injective g) (hc : ∀ i, g i ∈ crownSet u) (f : GNode S.tree → M) :
    ∑ i, f (g i) = f (u.upper.child (regionOf u).excluded) + f (u.lower.child (regionOf u).positive) +
      f (u.lower.child (regionOf u).negative) := by
  classical
  obtain ⟨h1, h2, h3⟩ := crown_distinct u
  set T : Finset (GNode S.tree) := {u.upper.child (regionOf u).excluded, u.lower.child (regionOf u).positive,
    u.lower.child (regionOf u).negative} with hT
  have hcard : T.card = 3 := by
    rw [hT, Finset.card_insert_of_notMem (by simp [h1, h2]), Finset.card_pair h3]
  have hsub : univ.image g ⊆ T := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    rcases hc i with h | h | h <;> simp [hT, h]
  have heq : univ.image g = T := Finset.eq_of_subset_of_card_le hsub (by
    rw [hcard, Finset.card_image_of_injective _ hg]; simp)
  rw [← Finset.sum_image (fun i _ j _ h => hg h), heq, hT, Finset.sum_insert (by simp [h1, h2]),
    Finset.sum_pair h3, add_assoc]

/-- The signed conservation of a whole block: `ζ_{u1} k_{u1} = ζ_{u11} k_{u11} + k_{u21} - k_{u22}`. -/
theorem block_signed_conservation (u : CLBlock S) (κ : GNode S.tree → (Fin d → ℤ)) (hκ : IsDecoration S κ) :
    ((S.sign u.upper.toNode : ℤˣ) : ℤ) • κ u.upper.toNode =
      ((S.sign (u.upper.child (regionOf u).excluded) : ℤˣ) : ℤ) • κ (u.upper.child (regionOf u).excluded) +
      ((S.sign (u.lower.child (regionOf u).positive) : ℤˣ) : ℤ) • κ (u.lower.child (regionOf u).positive) +
      ((S.sign (u.lower.child (regionOf u).negative) : ℤˣ) : ℤ) • κ (u.lower.child (regionOf u).negative) := by
  have hA : ∀ ℓ : GLeaf S.tree, (fun k => (κ ℓ.toNode k : ℝ)) = (fun k => (κ (S.pair ℓ).toNode k : ℝ)) :=
    fun ℓ => by rw [hκ.2 ℓ]
  have h := cl_slotSum_boundary u.isBlock (regionOf u) (fun x k => (κ x k : ℝ)) hA
  have h0 : ∑ v ∈ u.atoms, Mole.slotSum S (fun x k => (κ x k : ℝ)) v = 0 := by
    refine Finset.sum_eq_zero fun v _ => (Mole.slotSum_eq_zero_iff S _ v).mpr ?_
    funext k
    show (κ v.toNode k : ℝ) = (κ (v.child 0) k : ℝ) - (κ (v.child 1) k : ℝ) + (κ (v.child 2) k : ℝ)
    rw [hκ.1 v]
    simp only [Pi.add_apply, Pi.sub_apply]
    push_cast; ring
  rw [h0] at h
  funext k
  have hk := congrFun h k
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply] at hk
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have : ((((S.sign u.upper.toNode : ℤˣ) : ℤ) * κ u.upper.toNode k : ℤ) : ℝ) =
      (((((S.sign (u.upper.child (regionOf u).excluded) : ℤˣ) : ℤ) * κ (u.upper.child (regionOf u).excluded) k +
      ((S.sign (u.lower.child (regionOf u).positive) : ℤˣ) : ℤ) * κ (u.lower.child (regionOf u).positive) k +
      ((S.sign (u.lower.child (regionOf u).negative) : ℤˣ) : ℤ) * κ (u.lower.child (regionOf u).negative) k) : ℤ) : ℝ) := by
    push_cast
    simp only [smul_eq_mul] at hk
    push_cast at hk
    linarith
  exact_mod_cast this

theorem conservation_of_signed {E : Type*} [AddCommGroup E] (σ : ℤˣ) (x y0 y1 y2 : E)
    (h : (σ : ℤ) • x = (σ : ℤ) • y0 + ((-σ : ℤˣ) : ℤ) • y1 + (σ : ℤ) • y2) : x = y0 - y1 + y2 := by
  rcases Int.units_eq_one_or σ with rfl | rfl
  · simpa [sub_eq_add_neg] using h
  · simp only [Units.val_neg, Units.val_one, neg_smul, one_smul, neg_neg] at h
    have := congrArg Neg.neg h
    simp only [neg_neg, neg_add_rev] at this
    rw [this]; abel

namespace SpliceShape
variable (Φ : SpliceShape blk Gsb)

include Φ in
theorem plain (hS : S.IsPlain) : Gsb.IsPlain := by
  intro ℓ
  by_contra h
  have hp : Gsb.pair ℓ = ℓ := (Gsb.pair_eq_iff ℓ).mpr h
  have h1 := Φ.pair ℓ
  rw [hp] at h1
  exact ((S.pair_eq_iff (Φ.leaf ℓ)).mp h1.symm) (hS _)

/-- A function on `G_sb` nodes, extended by `0` to the skeleton (its value at a retained node). -/
noncomputable def ext {V : Type*} [Zero V] (z : GNode Gsb.tree → V) (x : GNode S.tree) : V := by
  classical
  exact if h : Ret blk x then z (Φ.nodeEquiv.symm ⟨x, h⟩) else 0

theorem ext_node {V : Type*} [Zero V] (z : GNode Gsb.tree → V) (y : GNode Gsb.tree) : Φ.ext z (Φ.node y) = z y := by
  classical
  unfold ext
  rw [dite_eq_left (Φ.ret_node y)]
  congr 1
  apply Φ.nodeEquiv.injective
  rw [Equiv.apply_symm_apply]
  rfl

/-- The four boundary momenta of unit `j` read off a decoration `z` of `G_sb`. -/
noncomputable def bdry (L : ℝ) (base : Mom d) (z : GNode Gsb.tree → (Fin d → ℤ)) (j : J) : Fin 4 → Mom d :=
  fun i => base + latticePoint L (Φ.ext z (clBoundaryNodes (regionOf (blk j)) i))

include Φ in
/-- The boundary nodes of a unit are retained. -/
theorem ret_bdryNode (hd : Disj blk) (j : J) (i : Fin 4) : Ret blk (clBoundaryNodes (regionOf (blk j)) i) := by
  fin_cases i
  · exact ret_upper hd j
  · exact ret_crown hd j (Or.inl rfl)
  · exact ret_crown hd j (Or.inr (Or.inl rfl))
  · exact ret_crown hd j (Or.inr (Or.inr rfl))

/-! ## Restriction -/

theorem restrict_isDecoration (hd : Disj blk) (κ : GNode S.tree → (Fin d → ℤ)) (hκ : IsDecoration S κ) :
    IsDecoration Gsb (fun y => κ (Φ.node y)) := by
  refine ⟨fun c => ?_, fun ℓ => ?_⟩
  · by_cases hh : ∀ j, Φ.br c ≠ (blk j).upper
    · simp only [Φ.child c _ hh, ← Φ.br_node]
      exact hκ.1 (Φ.br c)
    · push Not at hh
      obtain ⟨j, hj⟩ := hh
      apply conservation_of_signed (Gsb.sign c.toNode)
      have hs : ∀ i, Gsb.sign (c.child i) = if i = 1 then -Gsb.sign c.toNode else Gsb.sign c.toNode :=
        Mole.child_sign_formula c
      have hsum := sum_crown (blk j) (fun i => Φ.node (c.child i))
        (fun i i' h => (child_inj (Φ.inj h)).2) (Φ.crown c j hj)
        (fun x => ((S.sign x : ℤˣ) : ℤ) • κ x)
      simp only [Fin.sum_univ_three, Φ.sign, hs] at hsum
      rw [← block_signed_conservation (blk j) κ hκ, ← hj, Φ.br_node, Φ.sign] at hsum
      simpa using hsum.symm
  · have h1 := Φ.pair ℓ
    have h2 := Φ.leaf_node (Gsb.pair ℓ)
    rw [h1] at h2
    simp only [← Φ.leaf_node]
    rw [Φ.pair]
    exact hκ.2 _

/-- The restriction of a skeleton decoration to `G_sb`. -/
noncomputable def resDec (hS : S.IsPlain) (hd : Disj blk) {roots : Fin w → (Fin d → ℤ)}
    (κ : GenDecoration S d roots 0) : GenDecoration Gsb d roots 0 :=
  ⟨fun y => κ.1 (Φ.node y), Φ.restrict_isDecoration hd κ.1 κ.2.1,
    fun i => by simp only [Φ.root]; exact κ.2.2.1 i,
    fun ℓ hℓ => (absurd hℓ (by simp [Garden.IsFlower, Φ.plain hS ℓ]))⟩

theorem ext_resDec (hS : S.IsPlain) (hd : Disj blk) {roots : Fin w → (Fin d → ℤ)}
    (κ : GenDecoration S d roots 0) {x : GNode S.tree} (hx : Ret blk x) :
    Φ.ext (Φ.resDec hS hd κ).1 x = κ.1 x := by
  obtain ⟨y, rfl⟩ := (Φ.range x).mpr hx
  exact Φ.ext_node _ y

/-- The local decoration of unit `j` induced by a skeleton decoration. -/
noncomputable def resLoc (hS : S.IsPlain) (hd : Disj blk) {L : ℝ} {base : Mom d}
    {roots : Fin w → (Fin d → ℤ)} (κ : GenDecoration S d roots 0) (j : J) :
    CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base (Φ.resDec hS hd κ).1 j) := by
  refine ⟨fun x => κ.1 x.1, ?_, ?_, ?_⟩
  · intro v hv
    have hp := cl_realization_mem_support (regionOf (blk j)) ((branch_mem_clRealizationNodes v).mpr hv)
    rw [clExtendIndices_restrict _ κ.1 _ hp,
      clExtendIndices_restrict _ κ.1 _ (cl_child_mem_support (blk j).isBlock _ hv 0),
      clExtendIndices_restrict _ κ.1 _ (cl_child_mem_support (blk j).isBlock _ hv 1),
      clExtendIndices_restrict _ κ.1 _ (cl_child_mem_support (blk j).isBlock _ hv 2)]
    exact κ.2.1.1 v
  · intro ℓ hℓ
    have hp := cl_realization_mem_support (regionOf (blk j)) ((leaf_mem_clRealizationNodes ℓ).mpr hℓ)
    have hq := cl_realization_mem_support (regionOf (blk j)) ((leaf_mem_clRealizationNodes (S.pair ℓ)).mpr
      ((Mole.internal_leaf_pair_iff S _ ℓ).mpr hℓ))
    rw [clExtendIndices_restrict _ κ.1 _ hp, clExtendIndices_restrict _ κ.1 _ hq]
    exact κ.2.1.2 ℓ
  · intro i
    rw [clExtendIndices_restrict _ κ.1 _ (clBoundaryNodes_mem_support _ i)]
    unfold bdry
    rw [Φ.ext_resDec hS hd κ (Φ.ret_bdryNode hd j i)]

end SpliceShape

end WaveTurbulence.VineB
