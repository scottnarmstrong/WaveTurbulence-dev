/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (item I, with L5a tool) of main `WaveTurbulence.Foundations.Stage1.Geometry.SubproCrossIsoR83` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproSubst
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproContainedR83
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproBlockGeo
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproCrossIsoR83
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Desig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Final
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Gap
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Greg
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Group
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVC
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.IP
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Ingr
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj3
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Rev
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Runs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK3
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Skip
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Split
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.SurvData
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.SurvMK
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Top
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.TripleDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.V0
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.VC
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.SubproGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.SubproIso2
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproObjMap
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIng
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvMap
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineChainNoCN
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineCoarseGroupCode
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineDVGroupKey
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupPickCarrier
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupPickSpec
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineHVGroupKey
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizationNames
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedPiece
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceHingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceObj2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSplicePairs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineRunChain
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineRunSelected
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSelectedTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineSkipSelected
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitCover
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitCoverOne
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitSelected
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitSelectedMK
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineWholeUnit
-- R83 port of sp-src/SubproCrossIso.lean (FLOWER-P6 R83): successor designations, see HANDOFF


/-!
# SUBPRO (S4): the substitution isomorphism for `crossing` (R28 session 2)

`crossing_iso`: `P` a set of atoms of `G_sb`, `jfun` replaces every hinge `v ∈ P` by a joint of its unit (and is `ob` elsewhere).
Given the data (J1) (hinges go to Fama.ChainL.joints of their units), (J2) (the darts of `N'` inside `P` at a hinge sit at that joint) and
(J4) (every dart of `G_sb` whose image lies inside the image set is a dart of `N'`), the induced subgraph of `N'` on `P` is
isomorphic to that of the original molecule on `P.image jfun`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.Subpro.VineA.NormalizedSplice.Subpro
open WaveTurbulence.VineA.NormalizedSplice.Subpro WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.Fama.VineA WaveTurbulence.GammaLow.Fama.VineA.NormalizedSplice WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.Subpro WaveTurbulence.VineA.NormalizedSplice WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
  WaveTurbulence.Stage1 WaveTurbulence.Mole

variable {R : ℕ} {G : Garden (2 * R)} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- B1b (Mk-general form of `crossing_iso`). -/
theorem crossing_isoMk (hM : G.molecule.IsMolecule) (σ : Prescription G)
    {D' : Type} [Fintype D'] [DecidableEq D'] {Mk : Set (CLVineG γ _)} (N' : Molecule (GBranch (stSt γ (Mk := Mk) G σ).G.tree) D')
    (ι : D' → GardenDart (stSt γ (Mk := Mk) G σ).G) (hι : Function.Injective ι)
    (hι_atom : ∀ x, (stSt γ (Mk := Mk) G σ).G.molecule.atom (ι x) = N'.atom x)
    (hι_mate : ∀ x, ι (N'.mate x) = (stSt γ (Mk := Mk) G σ).G.molecule.mate (ι x))
    (hι_out : ∀ x, (stSt γ (Mk := Mk) G σ).G.molecule.out (ι x) = N'.out x)
    (P : Finset (GBranch (stSt γ (Mk := Mk) G σ).G.tree)) (jfun : GBranch (stSt γ (Mk := Mk) G σ).G.tree → GBranch G.tree)
    (hjnon : ∀ c ∈ P, c ∉ (stSt γ (Mk := Mk) G σ).hinges → jfun c = (stSt γ (Mk := Mk) G σ).M.ob c)
    (J1 : ∀ v ∈ P, v ∈ (stSt γ (Mk := Mk) G σ).hinges → ∃ u ∈ Fama.unitBlocks γ (Mk := Mk) G σ, (stSt γ (Mk := Mk) G σ).M.ob v = u.upper ∧
      (jfun v = u.upper ∨ jfun v = u.lower))
    (J2 : ∀ v ∈ P, v ∈ (stSt γ (Mk := Mk) G σ).hinges → ∀ x : D', N'.InGroup P x → N'.atom x = v →
      G.molecule.atom ((stSt γ (Mk := Mk) G σ).M.od (ι x)) = jfun v)
    (J4 : ∀ x0 : GardenDart (stSt γ (Mk := Mk) G σ).G, G.molecule.InGroup (P.image jfun) ((stSt γ (Mk := Mk) G σ).M.od x0) →
      ∃ x : D', ι x = x0) :
    ∃ I : InducedIso N' G.molecule P (P.image jfun), I.π = jfun := by
  classical
  have hcls := (stSt γ (Mk := Mk) G σ).hcls
  -- merged / unmerged values of `jfun`
  have hjmerged : ∀ v ∈ P, v ∈ (stSt γ (Mk := Mk) G σ).hinges → ∃ u ∈ Fama.unitBlocks γ (Mk := Mk) G σ, jfun v ∈ u.atoms ∧
      (stSt γ (Mk := Mk) G σ).M.ob v = u.upper ∧ (stSt γ (Mk := Mk) G σ).cls (jfun v) = some u.upper := by
    intro v hv hh
    obtain ⟨u, hu, hob, hj⟩ := J1 v hv hh
    have hjm : jfun v ∈ u.atoms := by rcases hj with h | h <;> rw [h]; exacts [u.isBlock.2.1, u.isBlock.2.2.1]
    exact ⟨u, hu, hjm, hob, Fama.stSt_cls_memMk (Mk := Mk) hM σ hu hjm⟩
  have hjnone : ∀ c ∈ P, c ∉ (stSt γ (Mk := Mk) G σ).hinges → (stSt γ (Mk := Mk) G σ).cls (jfun c) = none := by
    intro c hc hh
    rw [hjnon c hc hh]
    by_contra hne
    exact hh (((stSt γ (Mk := Mk) G σ).mem_hinges c).mpr hne)
  have hrepj : ∀ c ∈ P, repC (stSt γ (Mk := Mk) G σ).cls (jfun c) = (stSt γ (Mk := Mk) G σ).M.ob c := by
    intro c hc
    by_cases hh : c ∈ (stSt γ (Mk := Mk) G σ).hinges
    · obtain ⟨u, hu, hjm, hob, -⟩ := hjmerged c hc hh
      rw [Fama.stSt_repC_memMk (Mk := Mk) hM σ hu hjm, hob]
    · rw [repC_of_none (hjnone c hc hh), hjnon c hc hh]
  -- injectivity
  have hinj : Set.InjOn jfun (P : Set (GBranch (stSt γ (Mk := Mk) G σ).G.tree)) := by
    intro c1 hc1 c2 hc2 h
    apply (stSt γ (Mk := Mk) G σ).M.ob_inj
    rw [← hrepj c1 hc1, ← hrepj c2 hc2, h]
  refine exists_iso_subst (stSt γ (Mk := Mk) G σ).M N' ι hι hι_atom hι_mate hι_out P jfun hinj ?_ ?_
  · -- R2
    intro x hx
    set c := N'.atom x with hc
    have hcP : c ∈ P := hx.1
    by_cases hh : c ∈ (stSt γ (Mk := Mk) G σ).hinges
    · exact J2 c hcP hh x hx hc.symm
    · rw [hjnon c hcP hh]
      have h1 := (stSt γ (Mk := Mk) G σ).M.ob_atom (ι x)
      rw [hι_atom, ← hc] at h1
      have hz : (stSt γ (Mk := Mk) G σ).cls (G.molecule.atom ((stSt γ (Mk := Mk) G σ).M.od (ι x))) = none := by
        rcases hz : (stSt γ (Mk := Mk) G σ).cls (G.molecule.atom ((stSt γ (Mk := Mk) G σ).M.od (ι x))) with _ | r
        · rfl
        · exfalso
          have hr : repC (stSt γ (Mk := Mk) G σ).cls (G.molecule.atom ((stSt γ (Mk := Mk) G σ).M.od (ι x))) = r := by simp [repC, hz]
          rw [hr] at h1
          apply hh
          rw [(stSt γ (Mk := Mk) G σ).mem_hinges, h1, hcls _ r hz]
          simp
      rw [repC_of_none hz] at h1
      exact h1.symm
  · -- R3
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    obtain ⟨c1, hc1, hj1⟩ := Finset.mem_image.mp hy1
    obtain ⟨c2, hc2, hj2⟩ := Finset.mem_image.mp hy2
    have hno : ¬ ∃ a, (stSt γ (Mk := Mk) G σ).cls (G.molecule.atom y) = some a ∧
        (stSt γ (Mk := Mk) G σ).cls (G.molecule.atom (G.molecule.mate y)) = some a := by
      rintro ⟨a, ha1, ha2⟩
      rw [← hj1] at ha1
      rw [← hj2] at ha2
      by_cases hh1 : c1 ∈ (stSt γ (Mk := Mk) G σ).hinges
      swap
      · rw [hjnone c1 hc1 hh1] at ha1; cases ha1
      by_cases hh2 : c2 ∈ (stSt γ (Mk := Mk) G σ).hinges
      swap
      · rw [hjnone c2 hc2 hh2] at ha2; cases ha2
      obtain ⟨u1, hu1, hjm1, hob1, hcl1⟩ := hjmerged c1 hc1 hh1
      obtain ⟨u2, hu2, hjm2, hob2, hcl2⟩ := hjmerged c2 hc2 hh2
      rw [hcl1] at ha1
      rw [hcl2] at ha2
      have hu12 : u1.upper = u2.upper := (Option.some.inj ha1).trans (Option.some.inj ha2).symm
      have hc12 : c1 = c2 := (stSt γ (Mk := Mk) G σ).M.ob_inj (hob1.trans (hu12.trans hob2.symm))
      subst hc12
      have hu : u1 = u2 := by
        have : u1.upper = u2.upper := hu12
        exact Fama.VineA.NormalizedSplice.unit_eq_of_memMk (Mk := Mk) hM σ hu1 hu2 u1.isBlock.2.1 (this ▸ u2.isBlock.2.1)
      subst hu
      -- both ends of `y` are the joint `jfun c1` of the unit: a loop at a joint
      have hyg : G.molecule.InGroup u1.atoms y := ⟨hj1 ▸ hjm1, hj2 ▸ hjm2⟩
      have hj12 : G.molecule.atom (G.molecule.mate y) = G.molecule.atom y := by rw [← hj1, ← hj2]
      rcases (J1 c1 hc1 hh1) with ⟨u', hu', hob', hjj⟩
      have hu'u : u' = u1 := Fama.VineA.NormalizedSplice.unit_eq_of_memMk (Mk := Mk) hM σ hu' hu1 u'.isBlock.2.1 (by
        have : u'.upper = u1.upper := hob'.symm.trans hob1
        exact this ▸ u1.isBlock.2.1)
      subst hu'u
      rcases hjj with h | h
      · exact block_no_loop u'.isBlock hyg (hj1.symm ▸ h) (hj12.trans (hj1.symm ▸ h))
      · exact block_no_loop (block_swap_joints _ u'.isBlock) hyg (hj1.symm ▸ h) (hj12.trans (hj1.symm ▸ h))
    obtain ⟨x0, hx0⟩ := ((stSt γ (Mk := Mk) G σ).M.od_range y).mpr hno
    have hIn : G.molecule.InGroup (P.image jfun) ((stSt γ (Mk := Mk) G σ).M.od x0) := hx0 ▸ ⟨hy1, hy2⟩
    obtain ⟨x, hx⟩ := J4 x0 hIn
    refine ⟨x, ⟨?_, ?_⟩, by rw [hx]; exact hx0⟩
    · have h1 : (stSt γ (Mk := Mk) G σ).M.ob (N'.atom x) = (stSt γ (Mk := Mk) G σ).M.ob c1 := by
        rw [← hι_atom, hx, (stSt γ (Mk := Mk) G σ).M.ob_atom, hx0, ← hj1, hrepj c1 hc1]
      rw [(stSt γ (Mk := Mk) G σ).M.ob_inj h1]; exact hc1
    · have h1 : (stSt γ (Mk := Mk) G σ).M.ob (N'.atom (N'.mate x)) = (stSt γ (Mk := Mk) G σ).M.ob c2 := by
        rw [← hι_atom, hι_mate, hx, (stSt γ (Mk := Mk) G σ).M.ob_atom, (stSt γ (Mk := Mk) G σ).M.od_mate, hx0, ← hj2, hrepj c2 hc2]
      rw [(stSt γ (Mk := Mk) G σ).M.ob_inj h1]; exact hc2

theorem crossing_iso (hM : G.molecule.IsMolecule) (σ : Prescription G)
    {D' : Type} [Fintype D'] [DecidableEq D'] (N' : Molecule (GBranch (stSt γ G σ).G.tree) D')
    (ι : D' → GardenDart (stSt γ G σ).G) (hι : Function.Injective ι)
    (hι_atom : ∀ x, (stSt γ G σ).G.molecule.atom (ι x) = N'.atom x)
    (hι_mate : ∀ x, ι (N'.mate x) = (stSt γ G σ).G.molecule.mate (ι x))
    (hι_out : ∀ x, (stSt γ G σ).G.molecule.out (ι x) = N'.out x)
    (P : Finset (GBranch (stSt γ G σ).G.tree)) (jfun : GBranch (stSt γ G σ).G.tree → GBranch G.tree)
    (hjnon : ∀ c ∈ P, c ∉ (stSt γ G σ).hinges → jfun c = (stSt γ G σ).M.ob c)
    (J1 : ∀ v ∈ P, v ∈ (stSt γ G σ).hinges → ∃ u ∈ Fama.unitBlocks γ G σ, (stSt γ G σ).M.ob v = u.upper ∧
      (jfun v = u.upper ∨ jfun v = u.lower))
    (J2 : ∀ v ∈ P, v ∈ (stSt γ G σ).hinges → ∀ x : D', N'.InGroup P x → N'.atom x = v →
      G.molecule.atom ((stSt γ G σ).M.od (ι x)) = jfun v)
    (J4 : ∀ x0 : GardenDart (stSt γ G σ).G, G.molecule.InGroup (P.image jfun) ((stSt γ G σ).M.od x0) →
      ∃ x : D', ι x = x0) :
    ∃ I : InducedIso N' G.molecule P (P.image jfun), I.π = jfun := crossing_isoMk (Mk := ∅) hM σ N' ι hι hι_atom hι_mate hι_out P jfun hjnon J1 J2 J4

end WaveTurbulence.GammaLow.Famc.Subpro.VineA.NormalizedSplice.Subpro
