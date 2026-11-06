/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamSpliceDecoder
import Mathlib.Tactic

/-! # Fixed physical representatives on either side of an insertion cut -/

public section
namespace WaveTurbulence.Vine.Param.RungSpliceGeometry
variable {V β E : Type*} [DecidableEq V] [Fintype β] [DecidableEq β] [AddCommGroup E]
variable (G : RungSpliceGeometry V β)

/-- An old cut occurrence has representatives before and after the cell;
an uncut occurrence keeps its own new occurrence. All choices are geometric. -/
@[expose] def representative (e : β) (inside : Bool) : SpliceEdge G.i G.j :=
  if hi : e=G.i then .inr (if inside then if G.pattern.reversesPorts then 5 else 4 else 0)
  else if hj : e=G.j then .inr (if inside then if G.pattern.reversesPorts then 4 else 5 else 1)
  else .inl ⟨e,hi,hj⟩

/-- The first marked occurrence has its two prescribed rail representatives. -/
theorem representative_first (side : Bool) :
    G.representative G.i side=Sum.inr (if side then if G.pattern.reversesPorts then 5 else 4 else 0) := by
  unfold representative SpliceEdge
  simp


/-- The second marked occurrence keeps its independently marked rails. -/
theorem representative_second (side : Bool) :
    G.representative G.j side=Sum.inr (if side then if G.pattern.reversesPorts then 4 else 5 else 1) := by
  unfold representative SpliceEdge
  simp [Ne.symm G.distinct]


/-- Every remaining occurrence retains its own actual bond representative. -/
theorem representative_rest (e : β) (hi : e ≠ G.i) (hj : e ≠ G.j) (side : Bool) :
    G.representative e side=Sum.inl ⟨e,hi,hj⟩ := by
  unfold representative SpliceEdge
  simp [hi,hj]


/-- The side of an uncut occurrence is fixed by its endpoints. A cut
occurrence admits both physical representatives. -/
@[expose] def AdmissibleSide (e : β) (side : Bool) : Prop :=
  ∀ (hi : e ≠ G.i) (hj : e ≠ G.j),side=G.inside ⟨e,hi,hj⟩

/-- Every admissible representative equals the old label, up to the same
uniform translation on the chosen cap side. -/
theorem representative_label (a b : V) (hab : a ≠ b) (ha : G.σ a=a) (hb : G.σ b=b)
    (r : E) (k : DirectedRootFiber G.ends a b r) (xy : E×E) (e : β) (side : Bool)
    (hside : G.AdmissibleSide e side) :
    k.1 e=((G.globalSourceChart a b hab ha hb r).symm (k,xy)).1 (G.representative e side)+
      (if side then G.pattern.correction (spliceGap G.cap a b r) xy else 0) := by
  rw [G.globalSourceChart_decode]
  have hgap := G.source_cut_gap a b hab r k
  have hm := G.pattern.cap_ports_match (spliceGap G.cap a b r) (k.1 G.j) xy
  by_cases hi : e=G.i
  · subst e
    rw [G.representative_first]
    cases side
    · simpa only [Bool.false_eq_true,ite_false,
        rungSpliceLabels,Sum.elim_inr,spliceChartLabels,Matrix.cons_val_zero,add_zero] using hgap
    · cases hr : G.pattern.reversesPorts
      · simp only [hr,Bool.false_eq_true,ite_false] at hm ⊢
        change k.1 G.i=G.pattern.upperAfter (spliceGap G.cap a b r) (k.1 G.j) xy+
          G.pattern.correction (spliceGap G.cap a b r) xy
        exact hgap.trans hm.1.symm
      · simp only [hr,ite_true] at hm ⊢
        change k.1 G.i=G.pattern.lowerAfter (k.1 G.j) xy+
          G.pattern.correction (spliceGap G.cap a b r) xy
        exact hgap.trans hm.1.symm
  · by_cases hj : e=G.j
    · subst e
      rw [G.representative_second]
      cases side
      · simp [rungSpliceLabels,spliceChartLabels]
      · cases hr : G.pattern.reversesPorts
        · simp only [hr,Bool.false_eq_true,ite_false] at hm ⊢
          change k.1 G.j=G.pattern.lowerAfter (k.1 G.j) xy+
            G.pattern.correction (spliceGap G.cap a b r) xy
          exact hm.2.symm
        · simp only [hr,ite_true] at hm ⊢
          change k.1 G.j=G.pattern.upperAfter (spliceGap G.cap a b r) (k.1 G.j) xy+
            G.pattern.correction (spliceGap G.cap a b r) xy
          exact hm.2.symm
    · have hs := hside hi hj
      rw [G.representative_rest e hi hj]
      simp only [rungSpliceLabels,Sum.elim_inl]
      rw [hs]
      simp only [inside,decide_eq_true_eq]
      exact (sub_add_cancel _ _).symm

/-- Two old labels sharing a cap side remain a difference of fixed actual
new bond labels. The uniform correction cancels exactly. -/
theorem representative_difference (a b : V) (hab : a ≠ b) (ha : G.σ a=a) (hb : G.σ b=b)
    (r : E) (k : DirectedRootFiber G.ends a b r) (xy : E×E) (e f : β) (side : Bool)
    (he : G.AdmissibleSide e side) (hf : G.AdmissibleSide f side) :
    k.1 e-k.1 f=
      ((G.globalSourceChart a b hab ha hb r).symm (k,xy)).1 (G.representative e side)-
      ((G.globalSourceChart a b hab ha hb r).symm (k,xy)).1 (G.representative f side) := by
  rw [G.representative_label a b hab ha hb r k xy e side he,
    G.representative_label a b hab ha hb r k xy f side hf]
  abel

end WaveTurbulence.Vine.Param.RungSpliceGeometry
