/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CurrentBlocks
public import WaveTurbulence.Foundations.VineEst.VineEstS2.ChainInteriorPartition
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.ChainPieces
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.ChainPieces` (sha256 7480e55ca28b4e1f…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Actual vine-chain ingredients partition its interior branches -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2
variable {γF : ℝ}
open Finset
variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- One actual source ingredient of the chain, a member of `𝒱_γ` (L6's carrier `Src.IsSomeVine`) with ordered
joints. Main's `ChainPiece` records a drawn type `vineType` with `IsVine vineType`; here the chart label `label` is
derived (below). -/
structure ChainPieceΓ (γF : ℝ) (M : Molecule V D) where
  atoms : Finset V
  upper : V
  lower : V
  vine : FinalCount.Src.IsSomeVine γF M atoms upper lower

namespace ChainPieceΓ

variable {M : Molecule V D}

/-- An ingredient is a block with its joints. -/
theorem isBlock (P : ChainPieceΓ γF M) : M.IsBlock P.atoms P.upper P.lower :=
  FinalCount.Src.isBlock_of_isSomeVine P.vine

open Classical in
/-- **The chart label of an ingredient**: `I`, `II` for the bad vines, and otherwise a normal type labelling a
grouped full chart (`LabelCharted`; for a T-vine `III` or `VII`, from L4's de-indexed chart, `Family`). The label of a
normal ingredient is a typing index of its chart, not a claim about the vine. -/
noncomputable def label (P : ChainPieceΓ γF M) : VineType :=
  if M.IsVine .I P.atoms P.upper P.lower then .I
  else if M.IsVine .II P.atoms P.upper P.lower then .II
  else @Classical.epsilon VineType ⟨.III⟩ fun X => X.IsBad = false ∧ LabelCharted γF M X P.atoms P.upper P.lower

theorem label_of_I (P : ChainPieceΓ γF M) (h : M.IsVine .I P.atoms P.upper P.lower) : P.label = .I := by
  unfold label; simp only [h, ↓reduceIte]

theorem label_of_II (P : ChainPieceΓ γF M) (h1 : ¬ M.IsVine .I P.atoms P.upper P.lower)
    (h : M.IsVine .II P.atoms P.upper P.lower) : P.label = .II := by
  unfold label; simp only [h1, h, ↓reduceIte]

/-- The label of an ingredient labels a grouped chart (main's catalogue for (I), (II); the supply otherwise). -/
theorem labelCharted (hM9 : NormalChartSupply γF) (hM : M.IsMolecule) (P : ChainPieceΓ γF M) :
    LabelCharted γF M P.label P.atoms P.upper P.lower := by
  by_cases hI : M.IsVine .I P.atoms P.upper P.lower
  · rw [P.label_of_I hI]
    obtain ⟨F, hF⟩ := Vine.Param.vineparam_grouped V D M hM .I _ _ _ hI (VineEstS2.chosenRealization hI)
    refine ⟨F, hF.trans ?_⟩
    unfold famGroups; simp only [hI, ↓reduceDIte]
  · by_cases hII : M.IsVine .II P.atoms P.upper P.lower
    · rw [P.label_of_II hI hII]
      obtain ⟨F, hF⟩ := Vine.Param.vineparam_grouped V D M hM .II _ _ _ hII (VineEstS2.chosenRealization hII)
      refine ⟨F, hF.trans ?_⟩
      unfold famGroups; simp only [hI, hII, ↓reduceDIte]
    · have hN : M.IsNormalVineGamma γF P.atoms P.upper P.lower := ⟨P.vine, fun h => h.elim hI hII⟩
      obtain ⟨F, hF⟩ := hM9 V D M hM _ _ _ hN
      have hl : P.label = @Classical.epsilon VineType ⟨.III⟩
          (fun X => X.IsBad = false ∧ LabelCharted γF M X P.atoms P.upper P.lower) := by
        unfold label; simp only [hI, hII, ↓reduceIte]
      rw [hl]
      exact (@Classical.epsilon_spec VineType _ (exists_label_of_chart F hF)).2

/-- A label is bad exactly for the bad vines (I), (II), and then it is the type of the ingredient. -/
theorem label_isBad (hM9 : NormalChartSupply γF) (hM : M.IsMolecule) (P : ChainPieceΓ γF M) :
    (P.label.IsBad = true ↔ M.IsBadVine P.atoms P.upper P.lower) := by
  by_cases hI : M.IsVine .I P.atoms P.upper P.lower
  · rw [P.label_of_I hI]; exact ⟨fun _ => Or.inl hI, fun _ => rfl⟩
  · by_cases hII : M.IsVine .II P.atoms P.upper P.lower
    · rw [P.label_of_II hI hII]; exact ⟨fun _ => Or.inr hII, fun _ => rfl⟩
    · have hN : M.IsNormalVineGamma γF P.atoms P.upper P.lower := ⟨P.vine, fun h => h.elim hI hII⟩
      obtain ⟨F, hF⟩ := hM9 V D M hM _ _ _ hN
      have hl : P.label = @Classical.epsilon VineType ⟨.III⟩
          (fun X => X.IsBad = false ∧ LabelCharted γF M X P.atoms P.upper P.lower) := by
        unfold label; simp only [hI, hII, ↓reduceIte]
      have hs := (@Classical.epsilon_spec VineType _ (exists_label_of_chart F hF)).1
      rw [hl, hs]
      exact ⟨fun h => absurd h (by decide), fun h => h.elim (fun h => absurd h hI) (fun h => absurd h hII)⟩

/-- A bad label is the drawn type of the ingredient. -/
theorem isVine_label_of_bad (hM9 : NormalChartSupply γF) (hM : M.IsMolecule) (P : ChainPieceΓ γF M)
    (h : P.label.IsBad = true) : M.IsVine P.label P.atoms P.upper P.lower := by
  by_cases hI : M.IsVine .I P.atoms P.upper P.lower
  · rw [P.label_of_I hI]; exact hI
  · by_cases hII : M.IsVine .II P.atoms P.upper P.lower
    · rw [P.label_of_II hI hII]; exact hII
    · exact absurd ((P.label_isBad hM9 hM).mp h) (fun h' => h'.elim hI hII)

end ChainPieceΓ

end WaveTurbulence.GammaLow.Famb.VineEstS2
