/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.Align.Export
public import WaveTurbulence.Foundations.Stage1.Represents.RepVC0
public import WaveTurbulence.Foundations.Stage1.Represents.RepPr2
import Mathlib.Tactic

/-!
# S2 REPRESENTS, session 11: the prescribed point of a unit-class member

For `y` in the unit class `sourceClass a p kind`, the prescribed prime garden `memberPoint a y` (actual layered garden, prime data
and the actual sigma transport along the unit batch) has the code of `a`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA
  WaveTurbulence.VineEstS4 WaveTurbulence.VineC WaveTurbulence.LFTwist WaveTurbulence.VineAlign

variable {w p : ℕ} {kind : Bool}

/-- B1b-2 (Mk-general form of `member_trace`): a member of the run class at the marking `mk` is reached by a full
batch of the run assembly. -/
theorem member_traceMk (a : PrescribedPrimeGarden w) (mk : Stage1Mk.MarkFn w)
    (y : UState w (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk) :
    ∃ M : List (UnitsIndex (sourceAssemblyMk a mk)), M.Perm Finset.univ.toList ∧
      ReachU p kind (unitsSplit (sourceAssemblyMk a mk)).Q M (sourceStart a mk) (sourceUnitsMk a mk) y.1 y.2 :=
  (mem_classU a.prime.prime).mp hy

theorem member_trace (a : PrescribedPrimeGarden w) (y : UState w (unitsSplit (sourceAssembly a)))
    (hy : y ∈ sourceClass a p kind) :
    ∃ M : List (UnitsIndex (sourceAssembly a)), M.Perm Finset.univ.toList ∧
      ReachU p kind (unitsSplit (sourceAssembly a)).Q M (sourceStart a) (sourceUnits a) y.1 y.2 :=
  (mem_classU a.prime.prime).mp hy

/-- The prescribed point carried by a class member along its (chosen) full batch. -/
noncomputable def memberPoint (a : PrescribedPrimeGarden w) (y : UState w (unitsSplit (sourceAssembly a)))
    (M : List (UnitsIndex (sourceAssembly a)))
    (hr : ReachU p kind (unitsSplit (sourceAssembly a)).Q M (sourceStart a) (sourceUnits a) y.1 y.2) :
    PrescribedPrimeGarden w :=
  ⟨y.1.layered, ⟨y.1.skeleton, VineA.batch_prime hr.batch a.prime.prime, y.1.data, y.1.decodes⟩,
    transportGroupPrescription (batchMolIso hr.batch) a.sigma⟩

theorem memberPoint_code (a : PrescribedPrimeGarden w) (y : UState w (unitsSplit (sourceAssembly a)))
    (M : List (UnitsIndex (sourceAssembly a)))
    (hr : ReachU p kind (unitsSplit (sourceAssembly a)).Q M (sourceStart a) (sourceUnits a) y.1 y.2) :
    (memberPoint a y M hr).code = a.code := by
  have hword := BatchIso.fine_coarseAtomWord (batchMolIso_spec hr.batch) a.totalSigma
    (unitsFamily_isV0Fam (Mole.garden_isMolecule _) a.totalSigma)
  exact codedPrescription_map (batchMolIso hr.batch) hword a.sigma

open PrescribedPrimeGarden in
theorem memberPoint_related (a : PrescribedPrimeGarden w) (y : UState w (unitsSplit (sourceAssembly a)))
    (M : List (UnitsIndex (sourceAssembly a))) (hM : M.Perm Finset.univ.toList)
    (hr : ReachU p kind (unitsSplit (sourceAssembly a)).Q M (sourceStart a) (sourceUnits a) y.1 y.2) :
    Related (p := p) (kind := kind) a (memberPoint a y M hr) := by
  have hmem : y.1.layered ∈ a.outputs (p := p) (kind := kind) := by
    rw [prescribed_outputs_eq_unitsStart a (sourceLayer a) (sourceLayer_isLayering a) (sourceLayer_reconstructs a)]
    exact ⟨M, y.1, hM, hr.batch, rfl⟩
  obtain ⟨c, hc, hce⟩ := (Set.ext_iff.mp (tauClass_image a) y.1.layered).mpr hmem
  have hcode : c.code = (memberPoint a y M hr).code := (Related.code_eq hc).symm.trans (memberPoint_code a y M hr).symm
  have : c = memberPoint a y M hr := eq_of_layered_code hce hcode
  rw [← this]
  exact hc

open PrescribedPrimeGarden in
/-- The member's `A4` data are the representative's. -/
theorem memberPoint_fullProfile {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (y : UState (2 * R) (unitsSplit (sourceAssembly a)))
    (M : List (UnitsIndex (sourceAssembly a))) (hM : M.Perm Finset.univ.toList)
    (hr : ReachU p kind (unitsSplit (sourceAssembly a)).Q M (sourceStart a) (sourceUnits a) y.1 y.2) :
    (memberPoint a y M hr).fullProfile = a.fullProfile :=
  Related.fullProfile_eq (memberPoint_related a y M hM hr)

open PrescribedPrimeGarden in
/-- Selection of a piece at a garden `LG` is the selection of any related prescribed point over `LG`. -/
theorem selP_iff_related {R : ℕ} {A : Finset (LayeredGarden (2 * R))} (P : WTParams) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (π : PcA R p kind A) (b : PrescribedPrimeGarden (2 * R))
    (hb : Related (p := p) (kind := kind) (repPt π) b) (LG : LayeredGarden (2 * R)) (hLG : b.layered = LG)
    (κ : GenDecoration LG.garden P.d roots 0) :
    selP p kind A P base roots π LG κ ↔ selAt P base b.prime b.sigma (hLG ▸ κ) := by
  constructor
  · rintro ⟨b', h', hrel', hs'⟩
    have hcode : b'.code = b.code := (Related.code_eq hrel').symm.trans (Related.code_eq hb)
    have : b' = b := eq_of_layered_code (h'.trans hLG.symm) hcode
    subst this
    subst hLG
    exact hs'
  · intro hs
    exact ⟨b, hLG, hb, hs⟩

end WaveTurbulence.Represents
