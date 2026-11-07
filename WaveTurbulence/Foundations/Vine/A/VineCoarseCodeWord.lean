/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineNormalizationNames
/-! Fixed-carrier encoding of the exact quotient support qG[S]. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Stage1 RedSplice Represents
variable {w : ℕ} {G H : Garden w}

/-- The entire quotient support, encoded by its literal ordered addresses. -/
noncomputable def wordGroupCode (G : Garden w) (S : {S // S ∈ maximalGroups G.molecule}) :
    Finset (List ℕ) := by
  classical
  exact S.1.image (coarseAtomWord G)

/-- This is an injective address encoding of codeG(S) = qG[S]. -/
theorem wordGroupCode_eq (S : {S // S ∈ maximalGroups G.molecule}) :
    wordGroupCode G S = (coarseGroupCode G S).image (fun a => addressWord a.1) := by
  classical
  simp only [wordGroupCode, coarseGroupCode, Finset.image_image]
  rfl

theorem wordGroupCode_injective (G : Garden w) : Function.Injective (wordGroupCode G) := by
  classical
  intro S T h
  apply coarseGroupCode_injective G
  rw [wordGroupCode_eq, wordGroupCode_eq] at h
  exact Finset.image_injective (fun a b he => Subtype.ext (addressWord_injective he)) h

/-- The fixed-carrier group code commutes with any proved atom-word diagram. -/
theorem wordGroupCode_map (F : MolIso G.molecule H.molecule)
    (hd : ∀ v, coarseAtomWord H (F.e v) = coarseAtomWord G v)
    (S : {S // S ∈ maximalGroups G.molecule}) :
    wordGroupCode H (groupEquiv F S) = wordGroupCode G S := by
  classical
  change (S.1.image F.e).image (coarseAtomWord H) = S.1.image (coarseAtomWord G)
  rw [Finset.image_image]
  exact Finset.image_congr fun v _ => hd v

/-- A prescription as its graph on exact normalized support codes. -/
def codedPrescription (G : Garden w) (σ : GroupPrescription G) : Set (Finset (List ℕ) × Molecule.GapKind) :=
  Set.range (fun S => (wordGroupCode G S, σ S))

/-- No local colors are identified or discarded by the code. -/
theorem codedPrescription_injective (G : Garden w) : Function.Injective (codedPrescription G) := by
  intro σ τ h
  funext S
  have hm : (wordGroupCode G S, σ S) ∈ codedPrescription G τ := h ▸ ⟨S, rfl⟩
  obtain ⟨T, he⟩ := hm
  have ht : T = S := wordGroupCode_injective G (congrArg Prod.fst he)
  subst T
  exact (congrArg Prod.snd he).symm

/-- Transport preserves the complete graph of group colors whenever the actual words commute. -/
theorem codedPrescription_map (F : MolIso G.molecule H.molecule)
    (hd : ∀ v, coarseAtomWord H (F.e v) = coarseAtomWord G v) (σ : GroupPrescription G) :
    codedPrescription H (transportGroupPrescription F σ) = codedPrescription G σ := by
  ext t
  constructor
  · rintro ⟨T, rfl⟩
    obtain ⟨S, rfl⟩ := (groupEquiv F).surjective T
    exact ⟨S, Prod.ext (wordGroupCode_map F hd S).symm (transportGroupPrescription_apply F σ S).symm⟩
  · rintro ⟨S, rfl⟩
    exact ⟨groupEquiv F S, Prod.ext (wordGroupCode_map F hd S) (transportGroupPrescription_apply F σ S)⟩

end WaveTurbulence.VineA
