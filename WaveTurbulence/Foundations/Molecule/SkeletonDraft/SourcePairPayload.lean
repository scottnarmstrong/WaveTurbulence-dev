/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionData

/-! # Actual source leaves are exactly canonical leaf pairs with their two endpoint slots -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

def sourcePairLeaf {w : ℕ} (G : Garden w) (hG : G.IsPlain) (p : SourcePair G) (i : Fin 2) : GLeaf G.tree :=
  if i = 0 then p.firstLeaf hG else p.secondLeaf hG

theorem sourcePairAt_sourcePairLeaf {w : ℕ} (G : Garden w) (hG : G.IsPlain)
    (p : SourcePair G) (i : Fin 2) : sourcePairAt G (sourcePairLeaf G hG p i) = p.1 := by
  symm
  apply sourcePairs_eq_at G hG _ p.2
  by_cases hi : i = 0
  · exact Or.inl (by rw [sourcePairLeaf,ite_eq_left hi]; rfl)
  · exact Or.inr (by rw [sourcePairLeaf,ite_eq_right hi]; rfl)

theorem sourcePairLeaf_injective {w : ℕ} (G : Garden w) (hG : G.IsPlain) :
    Function.Injective (fun z : SourcePair G × Fin 2 => sourcePairLeaf G hG z.1 z.2) := by
  intro z t he
  have hp : z.1 = t.1 := Subtype.ext (by
    have hh := congrArg (sourcePairAt G) he
    simpa only [sourcePairAt_sourcePairLeaf] using hh)
  apply Prod.ext hp
  have hs := congrArg (fun ℓ : GLeaf G.tree => nodeSign G.sig ℓ.1) he
  obtain ⟨p,i⟩ := z
  obtain ⟨q,j⟩ := t
  change i = j
  fin_cases i <;> fin_cases j
  · rfl
  · have hv := (rawOfGarden_valid G hG).1 p.1 p.2
    have hw := (rawOfGarden_valid G hG).1 q.1 q.2
    simp only [rawOfGarden] at hv hw
    change nodeSign G.sig p.1.1 = nodeSign G.sig q.1.2 at hs
    rw [hv.2.2.1,hw.2.2.2] at hs
    contradiction
  · have hv := (rawOfGarden_valid G hG).1 p.1 p.2
    have hw := (rawOfGarden_valid G hG).1 q.1 q.2
    simp only [rawOfGarden] at hv hw
    change nodeSign G.sig p.1.2 = nodeSign G.sig q.1.1 at hs
    rw [hv.2.2.2,hw.2.2.1] at hs
    contradiction
  · rfl

theorem sourcePairLeaf_surjective {w : ℕ} (G : Garden w) (hG : G.IsPlain) :
    Function.Surjective (fun z : SourcePair G × Fin 2 => sourcePairLeaf G hG z.1 z.2) := by
  intro ℓ
  by_cases hs : nodeSign G.sig ℓ.1 = 1
  · refine ⟨(pairOfLeaf G hG ℓ,0),Subtype.ext ?_⟩
    change (sourcePairAt G ℓ).1 = ℓ.1
    rw [sourcePairAt,ite_eq_left hs]
  · refine ⟨(pairOfLeaf G hG ℓ,1),Subtype.ext ?_⟩
    change (sourcePairAt G ℓ).2 = ℓ.1
    rw [sourcePairAt,ite_eq_right hs]

end WaveTurbulence.Reg.Skeleton
