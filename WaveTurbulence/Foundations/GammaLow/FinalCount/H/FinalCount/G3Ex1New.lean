/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Ex1New
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3NewComp2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Anc
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Flat
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HInv
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Hist
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3NoTriple
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Run
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Step5c
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Steps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3URun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3UStep
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Vine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineF
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLikeConnected
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
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3NewComp1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Gamma
public import WaveTurbulence.Foundations.TVine.Chart.Unconditional
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3Ex1New`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3: excessprop1 (2) for Step 1** (DH23/TARGET Prop `excessprop1` (2), L2154--L2177), glued to VINE-COUNT
`prop94_vine_newcomp` (`ΔF = 1`, `ΔV_β = 2`, no new `α`-atom).

Step 1 either keeps the number of components (the `α`-case, `UStep1.excess`) or creates exactly one (`vine_F_cases`).  In the second case the
removed object is a single vine: a `DoubleShape` would stay connected outside (`doubleShape_F_le`, hypothesis `hconn`, the output of `subsetvc`).
`NewCompFixed` (L2174) is PROVED from the flux identity through the bridge (`newCompFixed_exists`), with `ν = |A| + (m - 2) ≤ |M_cur atoms|`;
the caller supplies `ν ≥ |atoms|` (`ν = n_sb ≤ (log L)^{C₂}`, L2175, via `UCtx.card_atoms_le`).  Named inputs: `hcls`, `hconn`, `hnl` (no loops;
`Good.noloop`), `hν`.

Low-range change (L6-HG3, PLAN-L6 §3e "Step 1"): main's `hvp : VINEPARAM` is replaced by L4's Theorem C, proved
unconditionally (`TVine.Chart.tvineChartExists_holds`; no hypothesis), and the removed single vine is a member of the low family
(`Step1.SingleVineVCGamma K`, as in L6-STEP1's `prop94_vine_all_gamma` / `prop94_vine_newcomp_gamma`); the proof is
`prop94_vine_newcomp_gamma`'s: L6-STEP1's `prop94_vine_newcomp` at the family `Src.γL` with `singleVineVC_of_gamma`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc Icc)
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.VineCount WaveTurbulence.LGSpine.SourceVine

variable {d : ℕ}

theorem newCompFixed_mono {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {K : Step1.VineCut Src.γL M}
    {L γ δ ν ν' : ℝ} {w : Mom d} {Adm : (D → (Fin d → ℤ)) → Prop} (hL : 0 < L) (hδ : 0 < δ) (h : ν ≤ ν')
    (hN : Step1.NewCompFixed M K L γ δ ν w Adm) : Step1.NewCompFixed M K L γ δ ν' w Adm := by
  intro c β k0 hP
  obtain ⟨n₀, hn₀, e₀, hh⟩ := hN c β k0 hP
  refine ⟨n₀, hn₀, e₀, fun κ hκ => ⟨(hh κ hκ).1, (hh κ hκ).2.trans ?_⟩⟩
  have : 0 ≤ δ⁻¹ * L ^ (-2 * γ) := by positivity
  nlinarith

/-- A new component excludes the hyper shape: the deleted bond joins the fresh joints. -/
theorem vc_block_of_new {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} (K : Step1.VineCut Src.γL M)
    (hnc : ¬ K.post.SameComponent K.fa K.fb) : M.IsBlock K.C.atoms K.C.upper K.C.lower := by
  have ha := K.in_a
  have hb := K.in_b
  unfold Src.Object.ContainsDart at ha hb
  rcases hsh : K.C.shape with h | R
  · exact h.1
  · exfalso
    rw [hsh] at ha hb
    obtain ⟨a1, a1', -⟩ := ha.1
    obtain ⟨a2, a2', -⟩ := ha.2
    obtain ⟨b1, b1', -⟩ := hb.1
    obtain ⟨b2, b2', -⟩ := hb.2
    have hG : ∀ z ∈ ({K.x₁, K.x₂, K.y₁, K.y₂} : Finset D), z ∈ ({K.x₁, K.x₂, K.y₁, K.y₂} : Finset D) :=
      fun _ h => h
    have hnot : ∀ z, z ≠ R.added → z ≠ M.mate R.added → z ∉ ({K.x₁, K.x₂, K.y₁, K.y₂} : Finset D) → True :=
      fun _ _ _ _ => trivial
    have hz : ∀ z, (z = R.added ∨ z = M.mate R.added) →
        z ∉ ({K.x₁, K.x₂, K.y₁, K.y₂} : Finset D) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      rcases hz with rfl | rfl
      · exact ⟨fun e => a1 e.symm, fun e => a2 e.symm, fun e => b1 e.symm, fun e => b2 e.symm⟩
      · exact ⟨fun e => a1' e.symm, fun e => a2' e.symm, fun e => b1' e.symm, fun e => b2' e.symm⟩
    have hends := R.ends_eq
    unfold Molecule.ends at hends
    rw [Sym2.eq_iff] at hends
    have key : ∃ z, (z = R.added ∨ z = M.mate R.added) ∧ M.atom z = K.C.upper ∧ M.atom (M.mate z) = K.C.lower := by
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨R.added, Or.inl rfl, h1, h2⟩
      · exact ⟨M.mate R.added, Or.inr rfl, h2, by rw [M.mate_mate]; exact h1⟩
    obtain ⟨z, hzc, hz1, hz2⟩ := key
    have hzm : (M.mate z = R.added ∨ M.mate z = M.mate R.added) := by
      rcases hzc with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl (M.mate_mate _)
    have e1 := cutMol_atom_outside K hG (hz z hzc)
    have e2 := cutMol_atom_outside K hG (hz (M.mate z) hzm)
    rw [hz1] at e1; rw [hz2] at e2
    have h1 : hPost K K.C.upper = K.fa := by simp [hPost]
    have h2 : hPost K K.C.lower = K.fb := by simp [hPost, K.ab_ne.symm]
    rw [h1] at e1; rw [h2] at e2
    have hn1 : K.cutMol.atom z ∉ K.C.atoms := by
      rw [e1]; exact fun h => K.fa_fresh (Step1.objectAtoms_sub K.C h)
    exact hnc (Relation.EqvGen.rel _ _ (show K.post.Adj K.fa K.fb from ⟨⟨z, hn1⟩, e1, e2⟩))


end WaveTurbulence.GammaLow.FinalCount.H
