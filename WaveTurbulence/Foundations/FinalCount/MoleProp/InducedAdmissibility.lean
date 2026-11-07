/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.DiscardComponents
public import WaveTurbulence.Foundations.FinalCount.MoleProp.BondDartReindex
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103CoreGeometry
import Mathlib.Tactic

/-! # Literal selected-component source counts

The final induced dart carrier is identified with the actual complement
erasure. Admissibility retains an old completion satisfying every original
constraint; the atom/energy supremum remains the genuine source supremum.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def inducedFreeAdmissibility (M : Molecule V D) (S : Finset V) {d : ℕ}
    (Adm : (D → (Fin d → ℤ)) → Prop) (κ' : {x : D // M.InGroup S x} → (Fin d → ℤ)) : Prop :=
  ∃ κ, Adm κ ∧ (∀ x, κ (M.mate x)=κ x) ∧ (fun x : {x : D // M.InGroup S x} => κ x.val)=κ'

def eraseComplementDartEquiv (M : Molecule V D) (S : Finset V) :
    Degen.RetainedDart M (M.atoms \ S) ≃ {x : D // M.InGroup S x} where
  toFun x := ⟨x.val,by
    constructor
    · by_contra hn
      exact x.property.1 (mem_sdiff.mpr ⟨M.atom_mem _,hn⟩)
    · by_contra hn
      exact x.property.2 (mem_sdiff.mpr ⟨M.atom_mem _,hn⟩)⟩
  invFun x := ⟨x.val,by
    constructor
    · intro hx
      exact (mem_sdiff.mp hx).2 x.property.1
    · intro hx
      exact (mem_sdiff.mp hx).2 x.property.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

theorem countAFree_erase_complement_le_induced (M : Molecule V D) (S : Finset V)
    (hS : S ⊆ M.atoms) {d : ℕ} (L γ δ C1 : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) :
    countAFree (Degen.eraseAtoms M (M.atoms \ S)) L γ δ C1 w
      (erasedFreeAdmissibility M (M.atoms \ S) Adm) P ≤
    countAFree (Mole.induced M S) L γ δ C1 w (inducedFreeAdmissibility M S Adm) P := by
  apply countAFree_le_of_dart_equiv _ _ (eraseComplementDartEquiv M S)
  · change M.atoms \ (M.atoms \ S) = S
    exact Finset.sdiff_sdiff_eq_self hS
  · intro x; rfl
  · intro x; exact Subtype.ext rfl
  · intro x; rfl
  · intro κ hκ
    obtain ⟨κ0,h0,hb,rfl⟩ := hκ
    exact ⟨κ0,h0,hb,by funext x; rfl⟩

theorem inducedFreeAdmissibility_largeGap (M : Molecule V D) (S : Finset V) {d : ℕ}
    (L γ η : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (hAdm : ∀ κ, Adm κ → LargeGap M L γ η w κ) :
    ∀ κ, inducedFreeAdmissibility M S Adm κ → LargeGap (Mole.induced M S) L γ η w κ := by
  intro κ hκ
  obtain ⟨κ0,h0,_hb,rfl⟩ := hκ
  intro x y hxy hdir
  exact hAdm κ0 h0 x.val y.val hxy hdir

/-- Selected-component bound by actual neutral atom removals and the actual
induced-carrier relabeling, with no component-product count assumed. -/
theorem countAFree_le_induced_component (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1-γ)/2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∃ R : ℝ, ∀ L ≥ R, 1 ≤ Real.log L →
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule →
      (∀ a b, a ≠ b → M.bondsBetween a b ≤ 1) → ∀ v : V,
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      (∀ κ, Adm κ → LargeGap M L γ η (0 : Mom d) κ) →
      countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
        countAFree (Mole.induced M (Degen.componentSet M v)) L γ δ C1 (0 : Mom d)
          (inducedFreeAdmissibility M (Degen.componentSet M v) Adm) P := by
  obtain ⟨C,hC,hB⟩ := countAFree_le_discard_components d hd γ hγ η hη hηmax
  refine ⟨C,hC,?_⟩
  intro C1 hC1 δ hδ
  obtain ⟨R,hR⟩ := hB C1 hC1 δ hδ
  refine ⟨R,?_⟩
  intro L hL hlog V D _ _ _ M hM hsimp v Adm P hAdm
  have hsub : Degen.componentSet M v ⊆ M.atoms := by
    intro a ha
    exact (Degen.mem_componentSet M v a).mp ha |>.1
  have hclose : ∀ a ∈ Degen.componentSet M v, ∀ b, M.SameComponent a b → b ∈ Degen.componentSet M v := by
    intro a ha b hab
    have h := (Degen.mem_componentSet M v a).mp ha
    exact (Degen.mem_componentSet M v b).mpr ⟨(Mole.sameComponent_mem_iff M hab).mp h.1,
      Relation.EqvGen.trans _ _ _ h.2 hab⟩
  exact (hR L hL hlog M hM hsimp _ hsub hclose Adm P hAdm).trans
    (countAFree_erase_complement_le_induced M _ hsub L γ δ C1 (0 : Mom d) Adm P)

end WaveTurbulence.MoleProp
