/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamSpliceSourceFiber
import Mathlib.Tactic

/-! # One-rung parametrization of the whole actual source conservation fiber -/

public section
namespace WaveTurbulence.Vine.Param
variable {V β E : Type*} [DecidableEq V] [Fintype β] [DecidableEq β] [AddCommGroup E]

omit [Fintype β] [DecidableEq β] in
/-- A joint-fixing atom permutation preserves the exact source forcing. -/
theorem rootForcing_relabel (σ : V ≃ V) (a b : V) (ha : σ a=a) (hb : σ b=b) (r : E) (v : V) :
    rootForcing a b r (σ v)=rootForcing a b r v := by
  have h1 : σ v=a ↔ v=a := by simpa only [ha] using (σ.injective.eq_iff : σ v=σ a ↔ v=a)
  have h2 : σ v=b ↔ v=b := by simpa only [hb] using (σ.injective.eq_iff : σ v=σ b ↔ v=b)
  simp only [rootForcing,h1,h2]

namespace RungSpliceGeometry
variable (G : RungSpliceGeometry V β)

/-- The local presentation of the full source fiber, including all uncut labels. -/
@[expose] def LocalSourceFiber (a b : V) (r : E) :=
  {q : ({e : β // e ≠ G.i ∧ e ≠ G.j} → E)×SixLabelFiber G.pattern (spliceGap G.cap a b r) //
    G.LocalRootRows a b r (spliceGap G.cap a b r) q}

/-- Every actual global source labeling gives a full local fiber. Conservation
forces the local physical gap, and every other bond is retained verbatim. -/
@[expose] def sourceLocal (a b : V) (hab : a ≠ b) (ha : G.σ a=a) (hb : G.σ b=b) (r : E)
    (k : DirectedRootFiber G.newEnds (.inl a) (.inl b) r) : G.LocalSourceFiber a b r := by
  let old : {e : β // e ≠ G.i ∧ e ≠ G.j} → E := fun e => k.1 (.inl e)
  let z : Fin 6 → E := fun e => k.1 (.inr e)
  have heq : rungSpliceLabels G.i G.j old z=k.1 := by
    funext e
    cases e <;> rfl
  have hsa : directedFlow G.newEnds (.inl a) (rungSpliceLabels G.i G.j old z)= -r := by
    rw [heq]
    simpa only [rootForcing,ite_true] using k.2 (.inl a)
  have hsb : directedFlow G.newEnds (.inl b) (rungSpliceLabels G.i G.j old z)=r := by
    rw [heq]
    simpa [rootForcing,hab,Ne.symm hab] using k.2 (.inl b)
  have hsz : ∀ v,v ≠ .inl a → v ≠ .inl b →
      directedFlow G.newEnds v (rungSpliceLabels G.i G.j old z)=0 := by
    intro v hva hvb
    rw [heq]
    simpa only [rootForcing,hva,hvb,ite_false] using k.2 v
  let q := sixLabelFiberOfSource G.ends G.i G.j G.σ G.p G.q G.c G.d a b hab G.pattern
    G.cap G.preserves_cap G.uncut G.outer_p G.outer_q G.inner_c G.inner_d old z r hsa hsb hsz
  refine ⟨(old,q),?_⟩
  intro v
  change directedFlow G.newEnds (.inl (G.σ v)) (rungSpliceLabels G.i G.j old z)=_
  rw [heq]
  have h : directedFlow G.newEnds (.inl (G.σ v)) k.1=rootForcing a b r (G.σ v) := by
    simpa only [rootForcing,Sum.inl.injEq] using k.2 (.inl (G.σ v))
  rw [rootForcing_relabel G.σ a b ha hb] at h
  exact h

/-- The local presentation satisfies every actual global source equation. -/
@[expose] def localSource (a b : V) (ha : G.σ a=a) (hb : G.σ b=b) (r : E)
    (q : G.LocalSourceFiber a b r) : DirectedRootFiber G.newEnds (.inl a) (.inl b) r := by
  refine ⟨G.labels q.1,?_⟩
  intro v
  cases v with
  | inl v =>
    have h := q.2 (G.σ.symm v)
    rw [← rootForcing_relabel G.σ a b ha hb r (G.σ.symm v)] at h
    simpa only [Equiv.apply_symm_apply,rootForcing,Sum.inl.injEq] using h
  | inr v =>
    fin_cases v
    · change directedFlow (rungSpliceEnds G.ends G.i G.j G.σ G.p G.q G.c G.d G.pattern)
        (.inr 0) (rungSpliceLabels G.i G.j q.1.1 q.1.2.1)=_
      rw [rungSpliceFlow_upper,q.1.2.2.2.1]
      simp [rootForcing]
    · change directedFlow (rungSpliceEnds G.ends G.i G.j G.σ G.p G.q G.c G.d G.pattern)
        (.inr 1) (rungSpliceLabels G.i G.j q.1.1 q.1.2.1)=_
      rw [rungSpliceFlow_lower,q.1.2.2.2.2,neg_zero]
      simp [rootForcing]

/-- The global and local presentations are inverse on every individual label. -/
@[expose] def globalLocalChart (a b : V) (hab : a ≠ b) (ha : G.σ a=a) (hb : G.σ b=b) (r : E) :
    DirectedRootFiber G.newEnds (.inl a) (.inl b) r ≃ G.LocalSourceFiber a b r where
  toFun := G.sourceLocal a b hab ha hb r
  invFun := G.localSource a b ha hb r
  left_inv := by
    intro k
    apply Subtype.ext
    funext e
    cases e <;> simp only [sourceLocal,localSource,labels,rungSpliceLabels,sixLabelFiberOfSource,Sum.elim_inl,Sum.elim_inr]
  right_inv := by
    intro q
    apply Subtype.ext
    apply Prod.ext
    · funext e
      simp only [sourceLocal,localSource,labels,rungSpliceLabels,sixLabelFiberOfSource,Sum.elim_inl,Sum.elim_inr]
    · apply Subtype.ext
      funext e
      simp only [sourceLocal,localSource,labels,rungSpliceLabels,sixLabelFiberOfSource,Sum.elim_inl,Sum.elim_inr]

/-- An arbitrary one-rung insertion has exactly the full old source fiber
and two independent integral difference coordinates. -/
@[expose] def globalSourceChart (a b : V) (hab : a ≠ b) (ha : G.σ a=a) (hb : G.σ b=b) (r : E) :
    DirectedRootFiber G.newEnds (.inl a) (.inl b) r ≃
      (DirectedRootFiber G.ends a b r×(E×E)) :=
  (G.globalLocalChart a b hab ha hb r).trans (G.localSourceChart a b hab r)

end RungSpliceGeometry
end WaveTurbulence.Vine.Param
