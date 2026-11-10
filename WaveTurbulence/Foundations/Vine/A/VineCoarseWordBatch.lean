/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineCoarseCodeWord
public import WaveTurbulence.Foundations.Vine.A.VineFineOperation
/-! Actual coarse and fine LF traces preserve the entire normalized group support. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Stage1 RedSplice LFTwist
variable {w p : ℕ} {kind : Bool} {ι : Type*} {L : List ι}

/-- All of V is selected by the constant SG prescription. -/
theorem mem_allSG {G : Garden w} {c : CLVine G} (h : c ∈ vinesV G) :
    c ∈ vinesV0 G (fun _ => .SG) := by
  have hh := h
  obtain ⟨S, hS, hi, _⟩ := hh
  exact ⟨h, S, hS, hi, rfl, fun h => h⟩

/-- Fine operations have the same sigma-independent quotient-word diagram. -/
theorem operation_fine_coarseAtomWord {A : FamilyReconstruction w ι} {i : ι}
    {σ : Prescription A.skeleton} (hF : IsV0Fam A.family σ)
    (op : FamilyOperation (p := p) (kind := kind) A i) (v : GBranch A.skeleton.tree) :
    coarseAtomWord op.output.skeleton ((operationMolIso op).e v) = coarseAtomWord A.skeleton v := by
  cases op with
  | mk hc he ht hq ε C =>
    cases ε
    · rfl
    · exact coarseAtomWord_twist (selectedMemberSite hF i)
        ⟨familyVine A.family i, mem_allSG (hF.1 i).1, rfl⟩ v

/-- Fold actual fine operation maps, retaining the transported prescription. -/
theorem BatchIso.fine_coarseAtomWord {A B : FamilyReconstruction w ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule}
    (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton) (hA : IsV0Fam A.family σ)
    (v : GBranch A.skeleton.tree) :
    VineA.coarseAtomWord B.skeleton (F.e v) = VineA.coarseAtomWord A.skeleton v := by
  induction h with
  | nil => rfl
  | skip _ _ ih => exact ih σ hA v
  | apply op _ ih =>
    exact (ih _ (isV0Fam_operation hA op) ((operationMolIso op).e v)).trans
      (operation_fine_coarseAtomWord hA op v)

end WaveTurbulence.VineA
