/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.Align.Boundary
public import WaveTurbulence.Foundations.Vine.Align.Route
/-! The actual lower-parent routing is determined by the common boundary nodes. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineAlign
open VineEstS4 VineA VineB VineC RedSplice Stage1 Twist RegRed Represents LFTwist Reg.Skeleton
variable {w : ℕ} {S S' G : Garden w} {J : Type} [Fintype J] [DecidableEq J]
  {blk : J → CLBlock S} {blk' : J → CLBlock S'}

omit [Fintype J] [DecidableEq J] in
/-- A retained node reads a lower-joint clock exactly at the two lower boundary children. -/
theorem retained_clk_lower_iff (x : GNode S.tree) (hx : Ret blk x) (j : J) :
    clkOfNode S x = Sum.inr (blk j).lower ↔
      x = (blk j).lower.child (regionOf (blk j)).positive ∨
        x = (blk j).lower.child (regionOf (blk j)).negative := by
  constructor
  · intro hc
    have hn : x.1.2 ≠ [] := by
      intro hn
      rw [SpliceShape.clkOfNode_root x hn] at hc
      cases hc
    have hp : x.parent hn = (blk j).lower := Sum.inr.inj ((clkOfNode_nonroot x hn).symm.trans hc)
    have hnot : x ∉ clRealizationNodes S (blk j).atoms := by
      rcases hx j with hh | he
      · exact hh
      · subst x
        exact (upper_parent_not_mem (blk j) hn (hp ▸ lower_mem _)).elim
    obtain ⟨k, hk⟩ := VineB.child_parent x hn
    rw [hp] at hk
    have he := (ext_child_lower (blk j) (lower_mem _) (blk j).isBlock.2.2.2.1.symm k
      (hk.symm ▸ hnot)).2
    rcases he with rfl | rfl
    · exact Or.inl hk.symm
    · exact Or.inr hk.symm
  · rintro (rfl | rfl)
    · rw [clkOfNode_nonroot _ (VineB.child_nonroot _ _), VineB.parent_child]
    · rw [clkOfNode_nonroot _ (VineB.child_nonroot _ _), VineB.parent_child]

/-- Lower-clock incidence is exactly incidence with the shape's two lower momentum nodes. -/
theorem node_clk_lower_iff (Φ : SpliceShape blk G) (hd : Disj blk) (x : GNode G.tree) (j : J) :
    clkOfNode S (Φ.node x) = Sum.inr (blk j).lower ↔ x = Φ.hmom hd j 2 ∨ x = Φ.hmom hd j 3 := by
  rw [retained_clk_lower_iff _ (Φ.ret_node x) j]
  constructor
  · rintro (h | h)
    · exact Or.inl (Φ.inj (h.trans (Φ.node_hmom hd j 2).symm))
    · exact Or.inr (Φ.inj (h.trans (Φ.node_hmom hd j 3).symm))
  · rintro (rfl | rfl)
    · exact Or.inl (Φ.node_hmom hd j 2)
    · exact Or.inr (Φ.node_hmom hd j 3)

omit [Fintype J] [DecidableEq J] in
/-- An outer branch itself can never be a lower joint. -/
theorem br_ne_lower (Φ : SpliceShape blk G) (c : GBranch G.tree) (j : J) : Φ.br c ≠ (blk j).lower := by
  intro he
  have hr := Φ.ret_br c
  rw [he, ret_branch_iff] at hr
  exact (hr j).elim (fun h => h (lower_mem _)) (blk j).isBlock.2.2.2.1.symm

/-- Identical actual boundary nodes imply identical lower-parent routing. -/
theorem route_eq_of_hmom (Φ : SpliceShape blk G) (hd : Disj blk)
    (Ψ : SpliceShape blk' G) (hd' : Disj blk') (hS : S.IsPlain) (hS' : S'.IsPlain) (hG : G.IsPlain)
    (hm : Φ.hmom hd = Ψ.hmom hd') : Φ.route hS hG = Ψ.route hS' hG := by
  apply route_eq_of_lower_incidence Φ hd Ψ hd' hS hS' hG
  intro s i j
  rcases s with q | c
  · fin_cases i
    · simp only [SpliceShape.iota, argSrc, Fin.zero_eta, Fin.isValue, ↓reduceIte,
        SpliceShape.iota_first, SpliceShape.leaf_node]
      rw [node_clk_lower_iff Φ hd, node_clk_lower_iff Ψ hd', hm]
    · simp only [SpliceShape.iota, argSrc, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte,
        SpliceShape.iota_second, SpliceShape.leaf_node]
      rw [node_clk_lower_iff Φ hd, node_clk_lower_iff Ψ hd', hm]
  · fin_cases i
    · simp only [SpliceShape.iota, argSrc, Fin.zero_eta, Fin.isValue, ↓reduceIte, SpliceShape.br_node]
      rw [node_clk_lower_iff Φ hd, node_clk_lower_iff Ψ hd', hm]
    · change Sum.inr (Φ.br c) = Sum.inr (blk j).lower ↔ Sum.inr (Ψ.br c) = Sum.inr (blk' j).lower
      simp only [Sum.inr.injEq, br_ne_lower, iff_self]

variable {p : ℕ} {kind : Bool}
  (hM : S.molecule.IsMolecule) (σ : Prescription S)
  (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  {Y : FamilyReconstruction w (UnitsIndex (alignedAssembly hM σ))}
  {vs : ∀ j, UnitAt Y.skeleton Y.family ((unitsSplit (alignedAssembly hM σ)).Q j)}
  {L : List (UnitsIndex (alignedAssembly hM σ))}
  (hr : ReachU p kind (unitsSplit (alignedAssembly hM σ)).Q L
    (unitsStart (alignedAssembly hM σ) (unitBlk_disj hM σ) D hS layer hLayer)
    (unitsRegion (alignedAssembly hM σ) (unitBlk_disj hM σ)) Y vs) (hn : L.Nodup)

/-- R-GSB: the actual per-member route is the representative's route. -/
theorem commonShape_route (hG : (stSt S σ).G.IsPlain) :
    (commonShape hM σ D hS layer hLayer hr hn).route Y.plain hG = (stShape hM σ).route hS hG :=
  route_eq_of_hmom _ (member_disj hM σ D hS layer hLayer hr hn) _ (unitBlk_disj hM σ) Y.plain hS hG
    (commonShape_hmom hM σ D hS layer hLayer hr hn)

end WaveTurbulence.VineAlign
