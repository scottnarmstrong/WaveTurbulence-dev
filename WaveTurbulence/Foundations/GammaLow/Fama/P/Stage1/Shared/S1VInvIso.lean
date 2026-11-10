/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Stage1.Shared.S1VInvIso` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.MolIso
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.Molecule.GardenDirectedIso
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Shared.S1VInvIso
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects


/-!
# Abstract molecule isomorphisms and transport of blocks and vines

A generic isomorphism of molecules `MolIso M N` (a bijection of atoms and of darts commuting with
`atom`, `mate`, `out`), and the transport of groups, degrees, blocks and vines.  This is the generic
form of `Twist.iso_isBlock`/`iso_isVine`, needed because the adjoint molecule `eraseBond M e` is not
a garden molecule.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.Stage1 WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.GammaLow.FinalCount

variable {V V' D D' : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]
  [DecidableEq V'] [Fintype D'] [DecidableEq D']


namespace MolIso
variable {M : Molecule V D} {N : Molecule V' D'} (F : MolIso M N)




















theorem isSomeVine_img {S : Finset V} {a b : V} (h : Src.IsSomeVine γ M S a b) :
    Src.IsSomeVine γ N (F.img S) (F.e a) (F.e b) :=
  isSomeVine_molIso F h

theorem chain_img {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain γ M S a b n) :
    Src.Chain γ N (F.img S) (F.e a) (F.e b) n := by
  induction h with
  | single hv => exact Src.Chain.single (MolIso.isSomeVine_img F hv)
  | append _ hT hi hne ih =>
    rw [F.img_union]
    refine Src.Chain.append ih (MolIso.isSomeVine_img F hT) ?_ (F.e.injective.ne hne)
    rw [← F.img_inter, hi, F.img_singleton]





theorem isVC_img {S : Finset V} {a b : V} (h : Src.IsVC γ M S a b) :
    Src.IsVC γ N (F.img S) (F.e a) (F.e b) :=
  ⟨F.isBlock_img h.1, h.2.elim fun n hn => ⟨n, MolIso.chain_img F hn⟩⟩

theorem isHV_img {S : Finset V} {a b : V} (h : Src.IsHV γ M S a b) :
    Src.IsHV γ N (F.img S) (F.e a) (F.e b) := by
  obtain ⟨x, hx, hv⟩ := h
  exact ⟨F.d x, F.ends_img hx, MolIso.isSomeVine_img (F.erase x) hv⟩

theorem isHVC_img {S : Finset V} {a b : V} (h : Src.IsHVC γ M S a b) :
    Src.IsHVC γ N (F.img S) (F.e a) (F.e b) := by
  obtain ⟨x, hx, hb, n, hn, hc⟩ := h
  exact ⟨F.d x, F.ends_img hx, (F.erase x).isBlock_img hb, n, hn, MolIso.chain_img (F.erase x) hc⟩

theorem isStage1Group_img {S : Finset V} (h : IsStage1GroupG γ M S) : IsStage1GroupG γ N (F.img S) := by
  obtain ⟨a, b, h | h | h | h⟩ := h
  · exact ⟨F.e a, F.e b, Or.inl (MolIso.isHV_img F h)⟩
  · exact ⟨F.e a, F.e b, Or.inr (Or.inl (MolIso.isVC_img F h))⟩
  · exact ⟨F.e a, F.e b, Or.inr (Or.inr (Or.inl (MolIso.isHVC_img F h)))⟩
  · exact ⟨F.e a, F.e b, Or.inr (Or.inr (Or.inr (isDV_molIso F h)))⟩




theorem maximalGroups_img {S : Finset V} (h : S ∈ maximalGroupsG γ M) : F.img S ∈ maximalGroupsG γ N := by
  refine ⟨MolIso.isStage1Group_img F h.1, fun T hT hST => ?_⟩
  have hT' : IsStage1GroupG γ M (F.symm.img T) := MolIso.isStage1Group_img F.symm hT
  have hsub : S ⊆ F.symm.img T := by
    have := (F.symm.img_subset_iff (S := F.img S) (T := T)).mpr hST
    rwa [F.img_img_symm] at this
  have := h.2 _ hT' hsub
  rw [← this, F.img_symm_img]

theorem maximalGroups_img_iff {S : Finset V} : F.img S ∈ maximalGroupsG γ N ↔ S ∈ maximalGroupsG γ M := by
  refine ⟨fun h => ?_, MolIso.maximalGroups_img F⟩
  simpa [F.img_img_symm] using MolIso.maximalGroups_img F.symm h

theorem vchain_img {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain γ M S a b n) :
    Src.Chain γ N (F.img S) (F.e a) (F.e b) n := by
  induction h with
  | single hv => exact Src.Chain.single (MolIso.isSomeVine_img F hv)
  | append _ hT hi hne ih =>
    rw [F.img_union]
    refine Src.Chain.append ih (MolIso.isSomeVine_img F hT) ?_ (F.e.injective.ne hne)
    rw [← F.img_inter, hi, F.img_singleton]

theorem chainIngredient_img {S A : Finset V} {a b x y : V} {n : ℕ}
    (h : ChainIngredientG γ M S a b n A x y) :
    ChainIngredientG γ N (F.img S) (F.e a) (F.e b) n (F.img A) (F.e x) (F.e y) := by
  induction h with
  | single hv => exact ChainIngredientG.single (MolIso.isSomeVine_img F hv)
  | append_left _ hT hi hne ih =>
    rw [F.img_union]
    refine ChainIngredientG.append_left ih (MolIso.isSomeVine_img F hT) ?_ (F.e.injective.ne hne)
    rw [← F.img_inter, hi, F.img_singleton]
  | append_last hS hT hi hne =>
    rw [F.img_union]
    refine ChainIngredientG.append_last (MolIso.vchain_img F hS) (MolIso.isSomeVine_img F hT) ?_
      (F.e.injective.ne hne)
    rw [← F.img_inter, hi, F.img_singleton]

theorem isIngredient_img {S T : Finset V} (h : IsIngredientG γ M S T) :
    IsIngredientG γ N (F.img S) (F.img T) := by
  rcases h with ⟨a, b, n, x, y, hb, hc⟩ | ⟨a, b, x, n, p, q, hx, hn, hb, hc⟩
  · exact Or.inl ⟨F.e a, F.e b, n, F.e x, F.e y, F.isBlock_img hb, MolIso.chainIngredient_img F hc⟩
  · exact Or.inr ⟨F.e a, F.e b, F.d x, n, F.e p, F.e q, F.ends_img hx, hn,
      (F.erase x).isBlock_img hb, MolIso.chainIngredient_img (F.erase x) hc⟩

theorem isIngredient_img_iff {S T : Finset V} : IsIngredientG γ N (F.img S) (F.img T) ↔ IsIngredientG γ M S T := by
  refine ⟨fun h => ?_, MolIso.isIngredient_img F⟩
  simpa [F.img_img_symm] using MolIso.isIngredient_img F.symm h


theorem isSomeVine_img_iff {S : Finset V} {a b : V} :
    Src.IsSomeVine γ N (F.img S) (F.e a) (F.e b) ↔ Src.IsSomeVine γ M S a b := by
  refine ⟨fun h => ?_, MolIso.isSomeVine_img F⟩
  have := MolIso.isSomeVine_img F.symm h
  rw [F.img_img_symm] at this
  simpa [Stage1.MolIso.symm] using this

theorem isVC_img_iff {S : Finset V} {a b : V} : Src.IsVC γ N (F.img S) (F.e a) (F.e b) ↔ Src.IsVC γ M S a b := by
  refine ⟨fun h => ?_, MolIso.isVC_img F⟩
  have := MolIso.isVC_img F.symm h
  rw [F.img_img_symm] at this
  simpa [Stage1.MolIso.symm] using this

theorem isHVC_img_iff {S : Finset V} {a b : V} :
    Src.IsHVC γ N (F.img S) (F.e a) (F.e b) ↔ Src.IsHVC γ M S a b := by
  refine ⟨fun h => ?_, MolIso.isHVC_img F⟩
  have := MolIso.isHVC_img F.symm h
  rw [F.img_img_symm] at this
  simpa [Stage1.MolIso.symm] using this

end MolIso
end WaveTurbulence.GammaLow.Fama
