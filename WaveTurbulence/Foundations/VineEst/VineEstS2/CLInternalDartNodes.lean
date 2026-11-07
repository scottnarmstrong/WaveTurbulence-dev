/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLIntegerFlow

/-! # Internal incidences recover every non-upper realized node -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- Every node whose integer label is summed has an actual internal dart;
the upper joint is the sole exception and its label is fixed at the boundary. -/
theorem clNode_internalDart_exists (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (x : GNode G.tree) (hx : x ∈ clRealizationNodes G U) (hne : x ≠ a.toNode) :
    ∃ d : InternalDart G.molecule U, Mole.dartNode G d.1 = x := by
  rcases (mem_clRealizationNodes x).mp hx with ⟨v,hv,rfl⟩ | ⟨ℓ,hℓ,rfl⟩
  · obtain ⟨hn,hp⟩ := cl_realization_parent hU R v.toNode hx hne
    exact ⟨⟨.inl (⟨v,hn⟩,false),⟨hv,hp⟩⟩,rfl⟩
  · obtain ⟨hm,hn,hp,hg⟩ := hℓ
    exact ⟨⟨.inr ⟨ℓ,hm,hn,hp⟩,hg⟩,rfl⟩

theorem internalDart_node_realization (x : InternalDart G.molecule U) :
    Mole.InIncidenceRealization G U (Mole.dartNode G x.1) := by
  rcases x with ⟨x,hx⟩
  rcases x with ⟨c,s⟩ | ℓ
  · cases s
    · exact Or.inl ⟨c.1,hx.1,rfl⟩
    · exact Or.inl ⟨c.1,hx.2,rfl⟩
  · exact Or.inr ⟨ℓ.1,⟨ℓ.2.1,ℓ.2.2.1,ℓ.2.2.2,hx⟩,rfl⟩

theorem clInternalDart_node_ne_upper (R : CLRegionData G U a b) (x : InternalDart G.molecule U) :
    Mole.dartNode G x.1 ≠ a.toNode := by
  rcases x with ⟨x,hx⟩
  rcases x with ⟨c,s⟩ | ℓ
  · intro he
    have hc : c.1 = a := Mole.branch_toNode_injective he
    have hp : GNode.parent c.1.toNode c.2 ∈ U := by
      cases s
      · exact hx.2
      · exact hx.1
    subst a
    exact R.parentPattern.1 ⟨c.2,hp⟩
  · exact Ne.symm (Mole.branch_toNode_ne_leaf a ℓ.1)

end WaveTurbulence.VineEstS2
