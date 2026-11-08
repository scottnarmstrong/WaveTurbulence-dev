/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepPr2
import Mathlib.Tactic

/-!
# S2 REPRESENTS: the producer, part 3 (`Stage1Partition`)

`stage1Partition_prod`: the coarse classes partition `A`, and every garden of a class carries, for every decoration,
exactly one piece whose selection holds (the `σ` of the decoration, TARGET L1950, and the tau class of that prescribed
point).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.VineA WaveTurbulence.LGSpine WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  WaveTurbulence.VineA.PrescribedPrimeGarden

variable {R : ℕ}

/-- Two prescribed points over the same garden whose `σ` both holds at `κ` coincide. -/
theorem eq_of_selAt (P : WTParams) (base : Mom P.d) {roots : Fin (2 * R) → (Fin P.d → ℤ)}
    (LG : LayeredGarden (2 * R)) (κ : GenDecoration LG.garden P.d roots 0)
    (b b' : PrescribedPrimeGarden (2 * R)) (h : b.layered = LG) (h' : b'.layered = LG)
    (hs : selAt P base b.prime b.sigma (h ▸ κ)) (hs' : selAt P base b'.prime b'.sigma (h' ▸ κ)) : b = b' := by
  subst h
  rcases b with ⟨LG1, pr1, σ1⟩
  rcases b' with ⟨LG2, pr2, σ2⟩
  change LG2 = LG1 at h'
  subst h'
  have e : pr1 = pr2 := primeData_unique _ _
  subst e
  have : σ1 = σ2 := NormalizedSplice.selOf_unique P.L P.γ P.η base _ hs hs'
  subst this
  rfl

/-- B1b-2 (Mk-general form of `stage1Partition_prod`): the coarse′ classes (coarse marking `mkC`) partition `A`, and every
garden of a class carries, for every decoration, exactly one fine′ piece (fine marking `mkF ⊇ mkC`) whose selection holds.
Hypotheses: the coarse marking is carried by every batch (the world's `markInvariantBatchV_markI0`) and lies below the
fine marking (`Π₀ ⊆ Π`).  The selection `selAt` is the decoration's own `σ` (unchanged, B1a D5): this statement does not
read the gap specification (ruling R171). -/
theorem stage1Partition_prodMk (p : ℕ) (kind : Bool) (A : Finset (LayeredGarden (2 * R)))
    (hplain : ∀ LG ∈ A, LG.garden.IsPlain) (P : WTParams) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) {mkF mkC : Stage1Mk.MarkFn (2 * R)}
    (hV : Stage1Mk.MarkInvariantBatchV mkC fun _ => True)
    (hsub : ∀ {LG : LayeredGarden (2 * R)} (B : PrimeData LG), mkC B ⊆ mkF B) :
    Stage1Partition roots A (membersP (p := p) (kind := kind) (A := A) (mk := mkC)) (clsPMk (mkF := mkF) mkC)
      (selPMk p kind A P base roots mkF) := by
  classical
  refine ⟨fun LG => ⟨fun hLG => ?_, fun ⟨c, hc⟩ => (Finset.mem_filter.1 hc).1⟩, ?_, ?_⟩
  · have hp := hplain LG hLG
    let b0 : PrescribedPrimeGarden (2 * R) := ⟨LG, primeDataOf LG hp, fun _ => .ZG⟩
    refine ⟨⟨coarseOf p kind b0 mkC, ⟨⟨b0, hLG⟩, rfl⟩⟩, Finset.mem_filter.2 ⟨hLG, ?_⟩⟩
    exact b0.prime.mem_coarse_outputs_selfMk (mkC b0.prime)
  · rintro ⟨_, ⟨x, rfl⟩⟩ ⟨_, ⟨x', rfl⟩⟩ hne
    rcases x.1.prime.coarse_outputs_disjoint_or_eqMk (p := p) (kind := kind) hV x'.1.prime with hd | he
    · rw [Finset.disjoint_left]
      intro LG h1 h2
      exact Set.disjoint_left.1 hd (Finset.mem_filter.1 h1).2 (Finset.mem_filter.1 h2).2
    · exact (hne (Subtype.ext he)).elim
  · intro c LG hLG κ
    obtain ⟨hLGA, hLGc⟩ := Finset.mem_filter.1 hLG
    have hp := hplain LG hLGA
    obtain ⟨σ0, hσ0, hu⟩ := selAt_exists_unique P base (primeDataOf LG hp) κ
    let b0 : PrescribedPrimeGarden (2 * R) := ⟨LG, primeDataOf LG hp, σ0⟩
    let π0 : PcA R p kind A mkF := Quotient.mk _ (⟨b0, hLGA⟩ : PtA R A)
    have hrel0 : Related (p := p) (kind := kind) (repPt π0) b0 mkF :=
      Quotient.mk_out (s := ptSetoid p kind A mkF) ⟨b0, hLGA⟩
    have hsel0 : selPMk p kind A P base roots mkF π0 LG κ := ⟨b0, rfl, hrel0, hσ0⟩
    refine ⟨π0, ⟨?_, hsel0⟩, ?_⟩
    · obtain ⟨_, ⟨z, rfl⟩⟩ := c
      refine Subtype.ext ?_
      change coarseOf p kind (repPt π0) mkC = coarseOf p kind z.1 mkC
      rw [coarse_eq_of_relatedMk hV hsub hrel0]
      have hLGc' : LG ∈ coarseOf p kind z.1 mkC := hLGc
      exact (z.1.prime.coarse_outputs_rebaseMk (p := p) (kind := kind) hV b0.prime hLGc').symm
    · intro π' ⟨_, b, h, hrel, hs⟩
      have hbb : b = b0 := eq_of_selAt P base LG κ b b0 h rfl hs hσ0
      subst hbb
      rw [← Quotient.out_eq π', ← Quotient.out_eq π0]
      exact Quotient.sound (Relation.EqvGen.trans _ _ _ hrel (Relation.EqvGen.symm _ _ hrel0))

theorem stage1Partition_prod (p : ℕ) (kind : Bool) (A : Finset (LayeredGarden (2 * R)))
    (hplain : ∀ LG ∈ A, LG.garden.IsPlain) (P : WTParams) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) :
    Stage1Partition roots A (membersP (p := p) (kind := kind) (A := A)) clsP (selP p kind A P base roots) :=
  stage1Partition_prodMk p kind A hplain P base roots (mkF := fun _ => ∅) (mkC := fun _ => ∅)
    (Stage1Mk.markInvariantBatchV_empty fun _ => True) (fun _ => subset_rfl)

end WaveTurbulence.Represents
