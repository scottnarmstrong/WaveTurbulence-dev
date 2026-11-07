/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepPr8
public import WaveTurbulence.Foundations.Stage1.Geometry.RedSpliceCoverThm
import Mathlib.Tactic

/-!
# S2 REPRESENTS: the class-member sum of a vine-free piece is a single garden's value

For a piece `π` whose representative point `b` has no unit (`unitBlocks b.prime.skeleton b.totalSigma = []`), `vinesV0` is empty, so
the fine tau class of `b` is `{b.layered}` (`outputs_subset_of_unitBlocks_nil`), the selection `selP π` is supported on `b.layered`
and equals `selAt` there (`Related` preserves the normalized code, `eq_of_layered_code`), and
`Σ_{LG ∈ members} F.valueSel LG (selP π LG) = F.valueSel b.layered (selAt …)`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset WaveTurbulence TTree WaveTurbulence.LGSpine WaveTurbulence.RedSplice WaveTurbulence.Reg
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed Set WaveTurbulence.VineA WaveTurbulence.LFTwist WaveTurbulence.VineA.PrescribedPrimeGarden

theorem allCoreOutputs_subset_of_isEmpty {w p : ℕ} {kind : Bool} {ι : Type*} [Fintype ι] [IsEmpty ι]
    (A : FamilyReconstruction w ι) : A.allCoreOutputs (p := p) (kind := kind) ⊆ {A.layered} := by
  rintro LH ⟨M, B, hM, h, rfl⟩
  have h0 : (Finset.univ : Finset ι).toList = [] := by simp [Finset.univ_eq_empty]
  rw [h0] at hM
  have : M = [] := List.Perm.eq_nil hM
  subst this
  cases h
  rfl

theorem outputs_subset_of_unitBlocks_nil {w p : ℕ} {kind : Bool} (b : PrescribedPrimeGarden w)
    (hnv : unitBlocks b.prime.skeleton b.totalSigma = []) :
    b.outputs (p := p) (kind := kind) ⊆ {b.layered} := by
  have hE : IsEmpty (CoreIndex (vinesV0 b.prime.skeleton b.totalSigma)) := by
    refine ⟨fun c => ?_⟩
    obtain ⟨u, hu, -⟩ := vinesV0_cover (Mole.garden_isMolecule _) b.totalSigma c.2.1
    rw [hnv] at hu
    exact absurd hu (List.not_mem_nil)
  have h1 := allCoreOutputs_subset_of_isEmpty (p := p) (kind := kind) b.state
  have h2 := b.mem_outputs_self (p := p) (kind := kind)
  intro LG hLG
  have e := h1 h2
  have := h1 hLG
  rw [Set.mem_singleton_iff] at e this ⊢
  exact this.trans e.symm


variable {R : ℕ} {p : ℕ} {kind : Bool} {A : Finset (LayeredGarden (2 * R))}

/-- Over a vine-free representative the selection `selP π` is `selAt` on `b.layered` and false elsewhere. -/
theorem selP_noVine (P : WTParams) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (π : PcA R p kind A)
    (hnv : unitBlocks (repPt π).prime.skeleton (repPt π).totalSigma = [])
    (LG : LayeredGarden (2 * R)) (κ : GenDecoration LG.garden P.d roots 0) :
    selP p kind A P base roots π LG κ ↔
      ∃ h : (repPt π).layered = LG, selAt P base (repPt π).prime (repPt π).sigma (h ▸ κ) := by
  constructor
  · rintro ⟨b', h, hrel, hs⟩
    have hout := outputs_subset_of_unitBlocks_nil (p := p) (kind := kind) (repPt π) hnv
    have hb' : b'.layered ∈ (repPt π).outputs (p := p) (kind := kind) := by
      rw [hrel.outputs_eq]; exact b'.mem_outputs_self
    have hl : b'.layered = (repPt π).layered := hout hb'
    have hbb : repPt π = b' := eq_of_layered_code hl.symm (Related.code_eq hrel)
    subst hbb
    exact ⟨h, hs⟩
  · rintro ⟨h, hs⟩
    exact ⟨repPt π, h, Relation.EqvGen.refl _, hs⟩

theorem noVine_members_sum (P : WTParams) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (tt : Fin (2 * R) → ℝ) (F : LeafFamily P (2 * R)) (π : PcA R p kind A)
    (hnv : unitBlocks (repPt π).prime.skeleton (repPt π).totalSigma = []) :
    ∑ LG ∈ membersP (clsP π), F.valueSel tt base roots LG (selP p kind A P base roots π LG) =
      F.valueSel tt base roots (repPt π).layered (fun κ => selAt P base (repPt π).prime (repPt π).sigma κ) := by
  classical
  have hmem : (repPt π).layered ∈ membersP (clsP π) := by
    refine Finset.mem_filter.2 ⟨repPt_layered_mem π, ?_⟩
    show (repPt π).layered ∈ coarseOf p kind (repPt π)
    rw [coarseOf_empty]
    exact (repPt π).prime.mem_coarse_outputs_self
  rw [Finset.sum_eq_single (repPt π).layered]
  · congr 1
    funext κ
    exact propext ((selP_noVine P base roots π hnv _ κ).trans ⟨fun ⟨h, hs⟩ => hs, fun hs => ⟨rfl, hs⟩⟩)
  · intro LG _ hne
    have hnone : ∀ κ : GenDecoration LG.garden P.d roots 0, ¬ selP p kind A P base roots π LG κ := by
      intro κ hκ
      obtain ⟨h, -⟩ := (selP_noVine P base roots π hnv LG κ).1 hκ
      exact hne h.symm
    simp [LeafFamily.valueSel, kernelLeavesSel, hnone]
  · intro h; exact absurd hmem h

end WaveTurbulence.Represents
