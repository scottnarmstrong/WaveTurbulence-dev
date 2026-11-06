/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamContractedGraph
public import WaveTurbulenceVineParam.VineParamSpliceDegreeTransport
public import WaveTurbulenceVineParam.VineParamDirectedIsoDegrees
import Mathlib.Tactic

/-! # Geometric splice data recovered from a balanced actual source cell -/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {V β : Type*} [DecidableEq V] [Fintype V] [Fintype β] [DecidableEq β]

/-- Contraction of the actual six-edge source cell gives the precise
RungSpliceGeometry used by the checked full-chart insertion theorem.
Balanced degrees of the old graph are proved from the actual new graph. -/
@[expose] def contractedGeometry (rest : β → V×V) (σ : V ≃ V)
    (p q c d : V) (P : RungPattern) (C : Finset V)
    (hp : p ∉ C) (hq : q ∉ C) (hc : c ∈ C) (hd : d ∈ C)
    (hσp : σ p=p) (hσq : σ q=q)
    (hσc : σ c=if P.reversesPorts then d else c)
    (hσd : σ d=if P.reversesPorts then c else d)
    (hσ : ∀ v,σ v ∈ C ↔ v ∈ C)
    (hr : ∀ e,(rest e).1 ∈ C ↔ (rest e).2 ∈ C)
    (hsource : ∀ v,(∑ e,-energySign (sourceCellEnds rest p q c d P) v e)=0) :
    RungSpliceGeometry V (β ⊕ Fin 2) := by
  have hsInv : ∀ v,σ.symm v ∈ C ↔ v ∈ C := by
    intro v
    have h := hσ (σ.symm v)
    simpa only [Equiv.apply_symm_apply] using h.symm
  have hrest : ∀ e : β ⊕ Fin 2,e ≠ .inr 0 → e ≠ .inr 1 →
      ((contractedEnds rest σ p q c d P e).1 ∈ C ↔
        (contractedEnds rest σ p q c d P e).2 ∈ C) := by
    intro e h0 h1
    cases e with
    | inl e =>
      change σ.symm (rest e).1 ∈ C ↔ σ.symm (rest e).2 ∈ C
      rw [hsInv,hsInv]
      exact hr e
    | inr j =>
      fin_cases j
      · exact (h0 rfl).elim
      · exact (h1 rfl).elim
  refine {
    ends := contractedEnds rest σ p q c d P
    i := .inr 0
    j := .inr 1
    distinct := by intro h; exact (by decide : (0 : Fin 2) ≠ 1) (Sum.inr.inj h)
    pattern := P
    cap := C
    p := p
    q := q
    c := c
    d := d
    outer_p := hp
    outer_q := hq
    inner_c := hc
    inner_d := hd
    σ := σ
    fixed_p := hσp
    fixed_q := hσq
    port_c := hσc
    port_d := hσd
    first := rfl
    second := rfl
    uncut := hrest
    preserves_cap := hσ
    balanced := ?_ }
  intro v
  have hi := (contractedSpliceIso rest σ p q c d P).degree_eq (.inl (σ v))
  have hn : (∑ e,-energySign
      (rungSpliceEnds (contractedEnds rest σ p q c d P) (.inr 0) (.inr 1) σ p q c d P)
      (.inl (σ v)) e)=0 := hi.symm.trans (hsource (.inl (σ v)))
  have ht := splice_old_degree (contractedEnds rest σ p q c d P) (.inr 0) (.inr 1)
    (by intro h; exact (by decide : (0 : Fin 2) ≠ 1) (Sum.inr.inj h)) σ p q c d v P C hp hq hc hd hσp hσq hσc hσd rfl rfl hrest
  exact ht.symm.trans hn

end WaveTurbulence.Vine.Param
