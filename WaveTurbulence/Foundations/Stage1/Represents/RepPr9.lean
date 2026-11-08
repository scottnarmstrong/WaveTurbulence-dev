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

/-- B1b-2 (Mk-general form of `outputs_subset_of_unitBlocks_nil`): without runs/units at the marking the fine′ output
set is the point's own garden. -/
theorem outputs_subset_of_unitBlocks_nilMk {w p : ℕ} {kind : Bool} (mk : Stage1Mk.MarkFn w)
    (b : PrescribedPrimeGarden w) (hnv : unitBlocks b.prime.skeleton b.totalSigma (mk b.prime) = []) :
    b.outputs (p := p) (kind := kind) mk ⊆ {b.layered} := by
  haveI := isEmpty_coreIndex_of_unitBlocks_nil hnv
  have h1 := allCoreOutputs_subset_of_isEmpty (p := p) (kind := kind) (b.state mk)
  have h2 := mem_outputs_selfMk (p := p) (kind := kind) mk b
  intro LG hLG
  have e := h1 h2
  have := h1 hLG
  rw [Set.mem_singleton_iff] at e this ⊢
  exact this.trans e.symm

theorem outputs_subset_of_unitBlocks_nil {w p : ℕ} {kind : Bool} (b : PrescribedPrimeGarden w)
    (hnv : unitBlocks b.prime.skeleton b.totalSigma = []) :
    b.outputs (p := p) (kind := kind) ⊆ {b.layered} :=
  outputs_subset_of_unitBlocks_nilMk (fun _ => ∅) b hnv


variable {R : ℕ} {p : ℕ} {kind : Bool} {A : Finset (LayeredGarden (2 * R))}

/-- B1b-2 (Mk-general form of `selP_noVine`): over a representative without units at the fine marking (carried by
every fine batch), the fine′ selection is `selAt` on its garden and false elsewhere. -/
theorem selP_noVineMk (P : WTParams) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    {mk : Stage1Mk.MarkFn (2 * R)} (hT : ∀ c : PrescribedPrimeGarden (2 * R), c.FineTransportedAt mk)
    (π : PcA R p kind A mk)
    (hnv : unitBlocks (repPt π).prime.skeleton (repPt π).totalSigma (mk (repPt π).prime) = [])
    (LG : LayeredGarden (2 * R)) (κ : GenDecoration LG.garden P.d roots 0) :
    selPMk p kind A P base roots mk π LG κ ↔
      ∃ h : (repPt π).layered = LG, selAt P base (repPt π).prime (repPt π).sigma (h ▸ κ) := by
  constructor
  · rintro ⟨b', h, hrel, hs⟩
    have hbb : b' = repPt π := related_eq_of_unitBlocks_nil hT hnv hrel
    subst hbb
    exact ⟨h, hs⟩
  · rintro ⟨h, hs⟩
    exact ⟨repPt π, h, Relation.EqvGen.refl _, hs⟩

/-- B1b-2 (Mk-general form of `noVine_members_sum`): the coarse′ class sum of a unit-free fine′ piece. -/
theorem noVine_members_sumMk (P : WTParams) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (tt : Fin (2 * R) → ℝ) (F : LeafFamily P (2 * R)) {mkF : Stage1Mk.MarkFn (2 * R)} (mkC : Stage1Mk.MarkFn (2 * R))
    (hT : ∀ c : PrescribedPrimeGarden (2 * R), c.FineTransportedAt mkF) (π : PcA R p kind A mkF)
    (hnv : unitBlocks (repPt π).prime.skeleton (repPt π).totalSigma (mkF (repPt π).prime) = []) :
    ∑ LG ∈ membersP (clsPMk mkC π), F.valueSel tt base roots LG (selPMk p kind A P base roots mkF π LG) =
      F.valueSel tt base roots (repPt π).layered (fun κ => selAt P base (repPt π).prime (repPt π).sigma κ) := by
  classical
  have hmem : (repPt π).layered ∈ membersP (clsPMk mkC π) :=
    Finset.mem_filter.2 ⟨repPt_layered_memMk π, (repPt π).prime.mem_coarse_outputs_selfMk (mkC (repPt π).prime)⟩
  rw [Finset.sum_eq_single (repPt π).layered]
  · congr 1
    funext κ
    exact propext ((selP_noVineMk P base roots hT π hnv _ κ).trans ⟨fun ⟨h, hs⟩ => hs, fun hs => ⟨rfl, hs⟩⟩)
  · intro LG _ hne
    have hnone : ∀ κ : GenDecoration LG.garden P.d roots 0, ¬ selPMk p kind A P base roots mkF π LG κ := by
      intro κ hκ
      obtain ⟨h, -⟩ := (selP_noVineMk P base roots hT π hnv LG κ).1 hκ
      exact hne h.symm
    simp [LeafFamily.valueSel, kernelLeavesSel, hnone]
  · intro h; exact absurd hmem h

/-- Over a vine-free representative the selection `selP π` is `selAt` on `b.layered` and false elsewhere. -/
theorem selP_noVine (P : WTParams) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (π : PcA R p kind A)
    (hnv : unitBlocks (repPt π).prime.skeleton (repPt π).totalSigma = [])
    (LG : LayeredGarden (2 * R)) (κ : GenDecoration LG.garden P.d roots 0) :
    selP p kind A P base roots π LG κ ↔
      ∃ h : (repPt π).layered = LG, selAt P base (repPt π).prime (repPt π).sigma (h ▸ κ) :=
  selP_noVineMk (mk := fun _ => ∅) P base roots fineTransportedAt_empty π hnv LG κ

theorem noVine_members_sum (P : WTParams) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (tt : Fin (2 * R) → ℝ) (F : LeafFamily P (2 * R)) (π : PcA R p kind A)
    (hnv : unitBlocks (repPt π).prime.skeleton (repPt π).totalSigma = []) :
    ∑ LG ∈ membersP (clsP π), F.valueSel tt base roots LG (selP p kind A P base roots π LG) =
      F.valueSel tt base roots (repPt π).layered (fun κ => selAt P base (repPt π).prime (repPt π).sigma κ) :=
  noVine_members_sumMk (mkF := fun _ => ∅) P base roots tt F (fun _ => ∅)
    fineTransportedAt_empty π hnv

end WaveTurbulence.Represents
