/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLOriginIncidences
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLExternalSlots

/-! # Every non-upper source slot has an actual chart origin -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem internalDart_origin {V D : Type*} [DecidableEq V] [Fintype D]
    (M : Molecule V D) (S : Finset V) (b : V) (d : InternalDart M S) :
    ∃ p : Bond M S ⊕ Fin 2, OriginAt M S b p (M.atom d.1) (M.out d.1) ∧
      ∀ {E : Type*} [AddCommGroup E] (k : Bond M S → E) (g r : E),
        origin M S k g r p = internalDartValue M S k d := by
  obtain ⟨⟨e,s⟩,rfl⟩ := (internalBondDartEquiv M S).surjective d
  refine ⟨.inl e,?_,?_⟩
  · cases s
    · exact Or.inl ⟨rfl,rfl⟩
    · exact Or.inr ⟨rfl,rfl⟩
  · intro E _ k g r
    exact (internalDartValue_bondDart M S k (e,s)).symm

/-- All four slots of every interior branch are chart origins. The only
missing internal incidences are the two prescribed lower boundary labels. -/
theorem clSlot_origin (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (v : GBranch G.tree) (hv : v ∈ U) (ha : v ≠ a) (i : Fin 4) :
    ∃ (p : Bond G.molecule U ⊕ Fin 2) (out : Bool),
      OriginAt G.molecule U b p v out ∧ Mole.slotWeight G v i = (if out then 1 else -1) ∧
      ∀ {E : Type} [AddCommGroup E] (κ : GNode G.tree → E),
        (∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode) →
        origin G.molecule U (fun e => Mole.restrictLabels G κ e.1)
          (κ (clBoundaryNodes R 2)) (κ (clBoundaryNodes R 2)-κ (clBoundaryNodes R 3)) p =
          κ (Mole.slotNode G v i) := by
  classical
  by_cases hi : i ∈ Mole.internalPositions G U v
  · obtain ⟨d,hd,hgroup,hpos⟩ := (Mole.mem_internalPositions G).mp hi
    obtain ⟨p,hp,hvalue⟩ := internalDart_origin G.molecule U b ⟨d,hgroup⟩
    refine ⟨p,G.molecule.out d,?_,?_,?_⟩
    · exact hd ▸ hp
    · have he := Mole.slotWeight_dart G d
      rw [hd,hpos] at he
      exact he.trans (by simp only [Molecule.dartSign])
    · intro E _ κ hmatch
      have he := Mole.slotNode_dart G d
      rw [hd,hpos] at he
      exact (hvalue _ _ _).trans ((gardenInternalDartValue κ hmatch ⟨d,hgroup⟩).trans (congrArg κ he.symm))
  · have hb : v = b := by
      by_contra hb
      have hdeg := hU.2.2.2.2.2.2.2.2.1 v hv ha hb
      have hall := Finset.eq_univ_of_card _ ((Mole.card_internalPositions G U v).trans hdeg)
      exact hi (hall ▸ Finset.mem_univ i)
    subst v
    have he : i ∈ ({R.positive.succ,R.negative.succ} : Finset (Fin 4)) := by
      rw [← cl_externalPositions_lower hU R]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩
    rcases Finset.mem_insert.mp he with rfl | he
    · refine ⟨.inr 0,false,⟨rfl,rfl⟩,?_,?_⟩
      · rw [slotWeight_child,R.positive_sign]
        norm_num
      · intro E _ κ _
        simp only [origin,ite_true]
        rfl
    · have he := Finset.mem_singleton.mp he
      subst i
      refine ⟨.inr 1,true,⟨rfl,by decide⟩,?_,?_⟩
      · rw [slotWeight_child,R.negative_sign]
        norm_num
      · intro E _ κ _
        simp only [origin,show (1 : Fin 2) ≠ 0 by decide,ite_false,sub_sub_cancel]
        rfl

end WaveTurbulence.VineEstS2
