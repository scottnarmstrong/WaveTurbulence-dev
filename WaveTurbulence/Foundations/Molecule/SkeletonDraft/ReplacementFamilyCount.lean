/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReplacementWordLengths

/-! # Uniform exponential count for fixed regular replacement slots

This counts actual well-formed assignment data. Transfer to source gardens uses
the reconstruction theorem and its order identity, not assumed here.
-/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

/-- The fixed branch and leaf-pair slots, with their native regular code well-formedness. -/
structure ReplacementFamily (n q : ℕ) where
  trees : Fin n → RegChain
  couples : Fin q → RegCpl
  trees_wf : ∀ i, (trees i).wf = true
  couples_wf : ∀ i, (couples i).wf = true

def ReplacementFamily.size {n q : ℕ} (D : ReplacementFamily n q) : ℕ :=
  (∑ i, (D.trees i).size) + ∑ i, (D.couples i).size

def ReplacementFamily.word {n q : ℕ} (D : ReplacementFamily n q) : List (Fin 11) :=
  replacementWord D.trees D.couples

theorem ReplacementFamily.word_injective {n q : ℕ} :
    Function.Injective (ReplacementFamily.word (n := n) (q := q)) := by
  intro D E he
  obtain ⟨ht,hc⟩ := replacementWord_injective D.trees E.trees D.couples E.couples he
  cases D
  cases E
  cases ht
  cases hc
  rfl

def boundedReplacementWord {n q : ℕ} (m : ℕ) (D : {D : ReplacementFamily n q // D.size ≤ m}) :
    {l : List (Fin 11) // l.length ≤ 4 * m + n + q} :=
  ⟨D.1.word,by
    have he := replacementWord_length D.1.trees D.1.couples D.1.trees_wf D.1.couples_wf
    change (replacementWord D.1.trees D.1.couples).length ≤ _
    change _ ≤ 4 * D.1.size + n + q at he
    have hm := D.2
    omega⟩

theorem boundedReplacementWord_injective {n q : ℕ} (m : ℕ) :
    Function.Injective (boundedReplacementWord (n := n) (q := q) m) := by
  intro D E he
  exact Subtype.ext (ReplacementFamily.word_injective (congrArg Subtype.val he))

/-- Bounded actual replacement assignments form a finite type by their bounded word injection. -/
instance instFiniteBoundedReplacementFamily (n q m : ℕ) :
    Finite {D : ReplacementFamily n q // D.size ≤ m} :=
  Finite.of_injective (fun D => wordSlots (4*m+n+q) (boundedReplacementWord m D))
    ((wordSlots_injective _).comp (boundedReplacementWord_injective m))

/-- All size compositions are counted at once by a single padded word. -/
theorem replacementFamilyCount_le (n q m : ℕ) :
    Nat.card {D : ReplacementFamily n q // D.size ≤ m} ≤ 12 ^ (4 * m + n + q) := by
  have he := Nat.card_le_card_of_injective
    (fun D => wordSlots (4*m+n+q) (boundedReplacementWord m D))
    ((wordSlots_injective _).comp (boundedReplacementWord_injective m))
  simpa only [Nat.card_fun,Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_option,Fintype.card_fin] using he

end WaveTurbulence.Reg.Skeleton
