/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBSpecialEnds
public import WaveTurbulence.Foundations.FinalCount.AppBCombinedCoordinates
import Mathlib.Tactic

/-! # Five distinct physical coordinates for the indirect 3R-2G gain -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def appbR32FiveIndices {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.r3.pattern)
    (s : AppbRealization r.post AppbPatternKind.s33new3.pattern) (j : Fin 3) (which : Bool) :
    Fin 5 ↪ Fin (r.combinedPattern s).edges.length := by
  let π : Equiv.Perm (Fin 3) := Equiv.swap j 0
  let left : Fin 3 ↪ Fin (r.combinedPattern s).edges.length :=
    π.toEmbedding.trans ⟨r.combinedLeftIndex s,r.combinedLeftIndex_injective s⟩
  let right : Fin 2 ↪ Fin (r.combinedPattern s).edges.length :=
    ((Fin.succEmb 2).trans (s.specialFrame which).index).trans
      ⟨r.combinedRightIndex s,r.combinedRightIndex_injective s⟩
  let f : Fin 3 ⊕ Fin 2 → Fin (r.combinedPattern s).edges.length := Sum.elim left right
  have hf : Function.Injective f := by
    rintro (a|a) (b|b) h
    · exact congrArg Sum.inl (left.injective h)
    · exact False.elim (r.combinedLeftRight_ne s (π a) ((s.specialFrame which).index b.succ) h)
    · exact False.elim (r.combinedLeftRight_ne s (π b) ((s.specialFrame which).index a.succ) h.symm)
    · exact congrArg Sum.inr (right.injective h)
  exact finSumFinEquiv.symm.toEmbedding.trans ⟨f,hf⟩

theorem appb_r32_five_indices_left {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.r3.pattern)
    (s : AppbRealization r.post AppbPatternKind.s33new3.pattern) (j k : Fin 3) (which : Bool) :
    appbR32FiveIndices r s j which (Fin.castAdd 2 k) = r.combinedLeftIndex s ((Equiv.swap j 0) k) := by
  change Sum.elim (fun k : Fin 3 => r.combinedLeftIndex s ((Equiv.swap j 0) k))
    (fun k : Fin 2 => r.combinedRightIndex s ((s.specialFrame which).index k.succ))
    (finSumFinEquiv.symm (Fin.castAdd 2 k)) = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

theorem appb_r32_five_indices_right {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.r3.pattern)
    (s : AppbRealization r.post AppbPatternKind.s33new3.pattern) (j : Fin 3) (which : Bool) (k : Fin 2) :
    appbR32FiveIndices r s j which (Fin.natAdd 3 k) =
      r.combinedRightIndex s ((s.specialFrame which).index k.succ) := by
  change Sum.elim (fun k : Fin 3 => r.combinedLeftIndex s ((Equiv.swap j 0) k))
    (fun k : Fin 2 => r.combinedRightIndex s ((s.specialFrame which).index k.succ))
    (finSumFinEquiv.symm (Fin.natAdd 3 k)) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

noncomputable def appbR32TripleIndices {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.r3.pattern)
    (s : AppbRealization r.post AppbPatternKind.s33new3.pattern) (j : Fin 3) (which : Bool) :
    Fin 3 ↪ Fin (r.combinedPattern s).edges.length :=
  (⟨![0,3,4],by decide⟩ : Fin 3 ↪ Fin 5).trans (appbR32FiveIndices r s j which)

theorem appb_r32_triple_indices {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.r3.pattern)
    (s : AppbRealization r.post AppbPatternKind.s33new3.pattern) (j : Fin 3) (which : Bool) :
    appbR32TripleIndices r s j which 0 = r.combinedLeftIndex s j ∧
    appbR32TripleIndices r s j which 1 = r.combinedRightIndex s (s.specialFirst which) ∧
    appbR32TripleIndices r s j which 2 = r.combinedRightIndex s (s.specialSecond which) := by
  constructor
  · change r.combinedLeftIndex s ((Equiv.swap j 0) 0) = _
    rw [Equiv.swap_apply_right]
  · constructor
    · change r.combinedRightIndex s ((s.specialFrame which).index 1) = _
      rw [(s.specialFrame_indices which).2.1]
    · change r.combinedRightIndex s ((s.specialFrame which).index 2) = _
      rw [(s.specialFrame_indices which).2.2]

end WaveTurbulence.Mole
