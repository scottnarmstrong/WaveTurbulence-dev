/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLInternalDartNodes
public import WaveTurbulence.Foundations.VineEst.VineEstS2.InternalDartLabelConsistency
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLBoundaryLeaves

/-! # Reconstructing literal local node labels from internal bonds -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem clInternalDart_node_ne_boundary (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (x : InternalDart G.molecule U) (j : Fin 4) : Mole.dartNode G x.1 ≠ clBoundaryNodes R j := by
  by_cases hj : j = 0
  · subst j
    exact clInternalDart_node_ne_upper R x
  · let k : Fin 3 := ⟨j.1-1,by omega⟩
    have hk : j = k.succ := Fin.ext (by change j.1 = (j.1-1)+1; omega)
    intro he
    have hr := internalDart_node_realization x
    rw [he,hk] at hr
    exact clOutBoundary_not_realization hU R k hr

/-- Actual internal incidences are used first; boundary labels occupy
precisely the four remaining prescribed nodes. All other labels are zero. -/
noncomputable def clRebuildLabels {E : Type*} [Zero E] (R : CLRegionData G U a b)
    (k : Bond G.molecule U → E) (β : Fin 4 → E) (x : GNode G.tree) : E := by
  classical
  exact if hd : ∃ d : InternalDart G.molecule U, Mole.dartNode G d.1 = x then
    internalDartValue G.molecule U k (Classical.choose hd)
  else if hb : ∃ j, clBoundaryNodes R j = x then β (Classical.choose hb) else 0

theorem clRebuildLabels_internal {E : Type*} [Zero E] (R : CLRegionData G U a b)
    (k : Bond G.molecule U → E) (β : Fin 4 → E) (d : InternalDart G.molecule U) :
    clRebuildLabels R k β (Mole.dartNode G d.1) = internalDartValue G.molecule U k d := by
  classical
  have hd : ∃ z : InternalDart G.molecule U, Mole.dartNode G z.1 = Mole.dartNode G d.1 := ⟨d,rfl⟩
  unfold clRebuildLabels
  rw [dite_eq_left hd]
  exact internalDartValue_eq_of_node_eq k (Classical.choose hd) d (Classical.choose_spec hd)

theorem clRebuildLabels_boundary {E : Type*} [Zero E]
    (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (k : Bond G.molecule U → E) (β : Fin 4 → E) (j : Fin 4) :
    clRebuildLabels R k β (clBoundaryNodes R j) = β j := by
  classical
  have hd : ¬ ∃ d : InternalDart G.molecule U, Mole.dartNode G d.1 = clBoundaryNodes R j := by
    rintro ⟨d,hd⟩
    exact clInternalDart_node_ne_boundary hU R d j hd
  have hb : ∃ c, clBoundaryNodes R c = clBoundaryNodes R j := ⟨j,rfl⟩
  unfold clRebuildLabels
  rw [dite_eq_right hd,dite_eq_left hb]
  exact congrArg β (clBoundaryNodes_injective hU R (Classical.choose_spec hb))

theorem clRebuildLabels_bond {E : Type*} [Zero E] (R : CLRegionData G U a b)
    (k : Bond G.molecule U → E) (β : Fin 4 → E) (e : Bond G.molecule U) :
    Mole.restrictLabels G (clRebuildLabels R k β) e.1 = k e := by
  have he := clRebuildLabels_internal R k β (internalBondDart G.molecule U (e,false))
  exact he.trans (internalDartValue_bondDart G.molecule U k (e,false))

theorem clRebuildLabels_matching {E : Type*} [Zero E] (R : CLRegionData G U a b)
    (k : Bond G.molecule U → E) (β : Fin 4 → E) (ℓ : GLeaf G.tree)
    (hℓ : Mole.IsInternalLeaf G U ℓ) :
    clRebuildLabels R k β ℓ.toNode = clRebuildLabels R k β (G.pair ℓ).toNode := by
  obtain ⟨hm,hn,hp,hg⟩ := hℓ
  let d : InternalDart G.molecule U := ⟨.inr ⟨ℓ,hm,hn,hp⟩,hg⟩
  exact (clRebuildLabels_internal R k β d).trans
    ((internalDartValue_mate G.molecule U k d).symm.trans
      (clRebuildLabels_internal R k β (internalDartMate G.molecule U d)).symm)

end WaveTurbulence.VineEstS2
