/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.CarriesW
public import WaveTurbulence.Foundations.Stage1.Represents.RepVD11
public import WaveTurbulence.Foundations.Stage1.Represents.RepVC1
public import WaveTurbulence.Foundations.Stage1.Represents.RepS10c
import Mathlib.Tactic

/-!
# S2 REPRESENTS, session 12: members of the unit class lie in `A` (twist closure), the class sum over `membersP`
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA
  WaveTurbulence.VineEstS4 WaveTurbulence.VineC WaveTurbulence.LFTwist WaveTurbulence.VineAlign
  WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic

variable {p : ℕ}

/-- B1b-2: closure of `A` under the LF batches of *admissible* families (`Adm`). `TwistClosed` is the case
`Adm := True` (`twistClosedAdm_of_twistClosed`); the world's `MarkedTwistClosed p A protSk` is the case
`Adm B := ∀ i, ∀ b ∈ B.family.atoms i, b ≠ B.family.upper i → ¬ protSk B b` (same body). -/
def TwistClosedAdm {w : ℕ} (p : ℕ) (A : Finset (LayeredGarden w))
    (Adm : ∀ {ι : Type}, LFTwist.FamilyReconstruction w ι → Prop) : Prop :=
  ∀ (kind : Bool) (ι : Type) (B : LFTwist.FamilyReconstruction w ι) (L : List ι),
    Reg.Skeleton.IsPrimeGarden B.skeleton → LFTwist.CanonicalObject p kind B.layered → B.layered ∈ A → Adm B →
    ∀ LH ∈ B.outputs p kind L, LH ∈ A

theorem twistClosedAdm_of_twistClosed {w : ℕ} {A : Finset (LayeredGarden w)} (h : TwistClosed p A)
    (Adm : ∀ {ι : Type}, LFTwist.FamilyReconstruction w ι → Prop) : TwistClosedAdm p A Adm :=
  fun kind ι B L hp hc hA _ => h kind ι B L hp hc hA

/-- B1b-2 (Mk-general form of `outputs_mem_A`): members of the run class at the marking `mk` lie in `A`, when `A` is
closed under batches of admissible families and the run assembly's start state is admissible. -/
theorem outputs_mem_AMk {R : ℕ} {A : Finset (LayeredGarden (2 * R))}
    {Adm : ∀ {ι : Type}, LFTwist.FamilyReconstruction (2 * R) ι → Prop} (hcl : TwistClosedAdm p A Adm)
    (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R)) (hadm : Adm (sourceStart a mk))
    (haA : a.layered ∈ A) (hcan : IsCanonGC (p + 1) a.layered)
    (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p (objKind (2 * R)) mk) :
    y.1.layered ∈ A := by
  obtain ⟨M, hM, hr⟩ := member_traceMk a mk y hy
  have hB : (sourceStart a mk).layered = a.layered := sourceLayer_reconstructs a
  refine hcl (objKind (2 * R)) (UnitsIndex (sourceAssemblyMk a mk)) (sourceStart a mk) M a.prime.prime
    (canonicalObject_of_isCanonGC (by rw [hB]; exact hcan)) (by rw [hB]; exact haA) hadm y.1.layered
    ⟨M, y.1, List.Perm.refl _, hr.batch, rfl⟩

theorem outputs_mem_A {R : ℕ} {A : Finset (LayeredGarden (2 * R))} (hcl : TwistClosed p A)
    (a : PrescribedPrimeGarden (2 * R)) (haA : a.layered ∈ A) (hcan : IsCanonGC (p + 1) a.layered)
    (y : UState (2 * R) (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p (objKind (2 * R))) :
    y.1.layered ∈ A :=
  outputs_mem_AMk (twistClosedAdm_of_twistClosed hcl fun _ => True) a (fun _ => ∅) trivial haA hcan y hy

theorem member_isCanon {R : ℕ} {A : Finset (LayeredGarden (2 * R))} {P : WTParams} {N : ℕ}
    (hA : ∀ LG ∈ A, Stage1Carries P p N LG) (hcl : TwistClosed p A)
    (a : PrescribedPrimeGarden (2 * R)) (haA : a.layered ∈ A)
    (y : UState (2 * R) (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p (objKind (2 * R))) :
    IsCanonGC (p + 1) y.1.layered :=
  (hA _ (outputs_mem_A hcl a haA (hA _ haA).1 y hy)).1

theorem member_stateLayer_le {R : ℕ} {A : Finset (LayeredGarden (2 * R))} {P : WTParams} {N : ℕ}
    (hA : ∀ LG ∈ A, Stage1Carries P p N LG) (hcl : TwistClosed p A)
    (a : PrescribedPrimeGarden (2 * R)) (haA : a.layered ∈ A)
    (y : UState (2 * R) (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p (objKind (2 * R))) (x) :
    stateLayer y.1 x ≤ p := by
  have h := Canon.layer_le_of_isCanonGC (member_isCanon hA hcl a haA y hy)
  rw [← stateLayer_spec y.1] at h
  exact h x


/-- B1b-2 (Mk-general form of `exists_outputs_finset`). -/
theorem exists_outputs_finsetMk {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R)) :
    ∃ T : Finset (LayeredGarden (2 * R)), (T : Set (LayeredGarden (2 * R))) =
      a.outputs (p := p) (kind := objKind (2 * R)) mk := by
  have h := prescribed_outputs_eq_unitsStartMk (p := p) (kind := objKind (2 * R)) a mk (sourceLayer a)
    (sourceLayer_isLayering a) (sourceLayer_reconstructs a)
  refine ⟨(allCoreOutputs_finite (p := p) (kind := objKind (2 * R)) (sourceStart a mk)).toFinset, ?_⟩
  rw [h]
  simp

theorem exists_outputs_finset {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) :
    ∃ T : Finset (LayeredGarden (2 * R)), (T : Set (LayeredGarden (2 * R))) =
      a.outputs (p := p) (kind := objKind (2 * R)) :=
  exists_outputs_finsetMk a fun _ => ∅

theorem valueSel_false {P : WTParams} {w : ℕ} (F : LeafFamily P w) (tt : Fin w → ℝ) (base : Mom P.d)
    (roots : Fin w → (Fin P.d → ℤ)) (LG : LayeredGarden w) :
    F.valueSel tt base roots LG (fun _ => False) = 0 := by
  unfold LeafFamily.valueSel kernelLeavesSel
  simp

open scoped Classical in
open PrescribedPrimeGarden in
theorem sum_members_eq {R : ℕ} {A : Finset (LayeredGarden (2 * R))} (hcl : TwistClosed p A)
    (π : PcA R p (objKind (2 * R)) A) (hcan : IsCanonGC (p + 1) (repPt π).layered) (P : WTParams)
    (F : LeafFamily P (2 * R)) (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (T : Finset (LayeredGarden (2 * R)))
    (hT : (T : Set (LayeredGarden (2 * R))) = (repPt π).outputs (p := p) (kind := objKind (2 * R))) :
    ∑ LG ∈ membersP (clsP π), F.valueSel tt base roots LG (selP p (objKind (2 * R)) A P base roots π LG) =
      ∑ LG ∈ T, F.valueSel tt base roots LG (selP p (objKind (2 * R)) A P base roots π LG) := by
  have hzero : ∀ LG, LG ∉ T → F.valueSel tt base roots LG (selP p (objKind (2 * R)) A P base roots π LG) = 0 := by
    intro LG hLG
    have hf : selP p (objKind (2 * R)) A P base roots π LG = fun _ => False := by
      funext κ
      apply propext
      constructor
      · rintro ⟨b, hb, hrel, -⟩
        refine absurd ?_ hLG
        rw [← Finset.mem_coe, hT, ← hb]
        rw [← tauClass_image (repPt π)]
        exact ⟨b, hrel, rfl⟩
      · exact False.elim
    rw [hf]
    exact valueSel_false F tt base roots LG
  have hsub : T ⊆ membersP (clsP π) := by
    intro LG hLG
    have hout : LG ∈ (repPt π).outputs (p := p) (kind := objKind (2 * R)) := by
      rw [← hT]; exact hLG
    unfold membersP
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · have h := prescribed_outputs_eq_unitsStart (p := p) (kind := objKind (2 * R)) (repPt π) (sourceLayer (repPt π))
        (sourceLayer_isLayering (repPt π)) (sourceLayer_reconstructs (repPt π))
      rw [h] at hout
      obtain ⟨M, B', hM, hB, hLB⟩ := hout
      have hB0 : (sourceStart (repPt π)).layered = (repPt π).layered := sourceLayer_reconstructs (repPt π)
      exact hcl (objKind (2 * R)) (UnitsIndex (sourceAssembly (repPt π))) (sourceStart (repPt π))
        (Finset.univ.toList) (repPt π).prime.prime
        (canonicalObject_of_isCanonGC (by rw [hB0]; exact hcan)) (by rw [hB0]; exact repPt_layered_mem π) LG
        ⟨M, B', hM, hB, hLB⟩
    · show LG ∈ coarseOf p (objKind (2 * R)) (repPt π)
      rw [coarseOf_empty]
      exact (repPt π).prime.fine_outputs_subset_coarse (repPt π).totalSigma hout
  exact (Finset.sum_subset hsub (fun LG _ hLG => hzero LG hLG)).symm

end WaveTurbulence.Represents
