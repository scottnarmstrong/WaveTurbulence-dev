/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmP1Basic
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase2d
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Anc
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Flat
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HInv
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Hist
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3NoTriple
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Run
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Steps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3URun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3UStep
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Vine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineF
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceCountingData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Ops
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Statement
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCAdm
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCAll1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCAll2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCAll3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCoords
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCount1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCount2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCount3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCount4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCDict
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCExcess
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCFlow
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCGain
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCHyper1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCHyper2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCHyper3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCHyper4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCInj
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCLadProd
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCScale
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCSource
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCStmt
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineBase
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineCover
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineCover2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDev
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble7
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineExcess3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineExcess5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineRank
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineRank2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmP1Basic`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY, phase 1 (a): the state after a vine removal (Step 1).**  Atoms, classes, `ε`-count, `apProd`, `vBeta`
and the positivity of the labels of `vineSt`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem vineSt_atoms (s : St.{u} V D₀) (K : Step1.VineCut Src.γL s.M) (c : Cls) :
    (vineSt s K c).M.atoms = (insert K.fb (insert K.fa s.M.atoms)).filter (fun a => a ∉ K.C.atoms) := rfl

theorem vineSt_cls (s : St.{u} V D₀) (K : Step1.VineCut Src.γL s.M) (c : Cls) :
    (vineSt s K c).cls = Function.update (Function.update (Function.update (Function.update s.cls K.C.upper c) K.fa c)
      K.C.lower c) K.fb c := rfl

theorem vineSt_cls_old_AsmP1Basic (s : St.{u} V D₀) (K : Step1.VineCut Src.γL s.M) (c : Cls) {a : V} (ha : a ∈ s.M.atoms) (haC : a ∉ K.C.atoms) :
    (vineSt s K c).cls a = s.cls a := by
  have h1 : a ≠ K.C.upper := fun e => haC (e ▸ K.a_mem)
  have h2 : a ≠ K.C.lower := fun e => haC (e ▸ K.b_mem)
  have h3 : a ≠ K.fa := fun e => K.fa_fresh (e ▸ ha)
  have h4 : a ≠ K.fb := fun e => K.fb_fresh (e ▸ ha)
  rw [vineSt_cls, Function.update_of_ne h4, Function.update_of_ne h2, Function.update_of_ne h3, Function.update_of_ne h1]

theorem vineSt_cls_fa_AsmP1Basic (s : St.{u} V D₀) (K : Step1.VineCut Src.γL s.M) (c : Cls) : (vineSt s K c).cls K.fa = c := by
  rw [vineSt_cls, Function.update_of_ne K.fa_ne_fb, Function.update_of_ne K.fa_ne_b]
  rw [Function.update_self]

theorem vineSt_cls_fb_AsmP1Basic (s : St.{u} V D₀) (K : Step1.VineCut Src.γL s.M) (c : Cls) : (vineSt s K c).cls K.fb = c := by
  rw [vineSt_cls, Function.update_self]

theorem fa_mem_vineSt (s : St.{u} V D₀) (K : Step1.VineCut Src.γL s.M) (c : Cls) : K.fa ∈ (vineSt s K c).M.atoms := by
  rw [vineSt_atoms, Finset.mem_filter]
  exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), fun h => K.fa_fresh (Step1.objectAtoms_sub K.C h)⟩

theorem fb_mem_vineSt (s : St.{u} V D₀) (K : Step1.VineCut Src.γL s.M) (c : Cls) : K.fb ∈ (vineSt s K c).M.atoms := by
  rw [vineSt_atoms, Finset.mem_filter]
  exact ⟨Finset.mem_insert_self _ _, fun h => K.fb_fresh (Step1.objectAtoms_sub K.C h)⟩

/-- Every atom of the removed object is `ε` (the joints by hypothesis, the interior by degree). -/
theorem vine_atoms_eps {s : St.{u} V D₀} {R : ℕ} (hI : Inv R s) (K : Step1.VineCut Src.γL s.M) (hu : s.cls K.C.upper = .eps)
    (hl : s.cls K.C.lower = .eps) : ∀ a ∈ K.C.atoms, s.cls a = .eps := by
  intro a haC
  by_cases h1 : a = K.C.upper
  · rw [h1]; exact hu
  by_cases h2 : a = K.C.lower
  · rw [h2]; exact hl
  by_contra hne
  have haM : a ∈ s.M.atoms := Step1.objectAtoms_sub K.C haC
  have := (hI.ab a haM hne).1
  have h4 := vine_interior_deg K hI.bounds haC h1 h2
  omega

/-- Number of `ε` atoms drops under a vine removal. -/
theorem epsCount_vineSt_lt {s : St.{u} V D₀} (K : Step1.VineCut Src.γL s.M) (hu : s.cls K.C.upper = .eps) (c : Cls) (hc : c ≠ .eps) :
    epsCount (vineSt s K c) < epsCount s := by
  unfold epsCount
  have hsub : (vineSt s K c).M.atoms.filter (fun a => (vineSt s K c).cls a = .eps) ⊆
      (s.M.atoms.filter (fun a => s.cls a = .eps)).erase K.C.upper := by
    intro a ha
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.1 ha
    rw [vineSt_atoms, Finset.mem_filter] at ha1
    obtain ⟨ha1, haC⟩ := ha1
    have hfa : a ≠ K.fa := fun e => by
      rw [e, vineSt_cls_fa_AsmP1Basic] at ha2; exact hc ha2
    have hfb : a ≠ K.fb := fun e => by
      rw [e, vineSt_cls_fb_AsmP1Basic] at ha2; exact hc ha2
    have haM : a ∈ s.M.atoms := by
      rcases Finset.mem_insert.1 ha1 with h | h
      · exact absurd h hfb
      · rcases Finset.mem_insert.1 h with h | h
        · exact absurd h hfa
        · exact h
    rw [vineSt_cls_old_AsmP1Basic s K c haM haC] at ha2
    exact Finset.mem_erase.2 ⟨fun e => haC (e ▸ K.a_mem), Finset.mem_filter.2 ⟨haM, ha2⟩⟩
  refine lt_of_le_of_lt (Finset.card_le_card hsub) ?_
  exact Finset.card_erase_lt_of_mem (Finset.mem_filter.2 ⟨K.a_atom, hu⟩)

end WaveTurbulence.GammaLow.FinalCount.H
