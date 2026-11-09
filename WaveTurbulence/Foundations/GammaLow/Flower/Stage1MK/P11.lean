/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Defs
public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Gates
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Inputs
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P1
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P2
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P3
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P4
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P6
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P7
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P8
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P9
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P10
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Iface
public import WaveTurbulence.Foundations.Flower.MkDefs.Intrinsic
public import WaveTurbulence.Foundations.Flower.MkMark.Batch
public import WaveTurbulence.Foundations.Flower.MkMark.BatchSel
public import WaveTurbulence.Foundations.Flower.MkMark.CountBound
public import WaveTurbulence.Foundations.Flower.MkMarkX.Transport
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Assembly
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Gate
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.SurvCount
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Unclean
public import WaveTurbulence.Foundations.Stage1.Geometry.RedSpliceTripleDesigMK
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproContainedMK
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproItemsMK
public import WaveTurbulence.Foundations.Stage1.Geometry.SurvConnMK
public import WaveTurbulence.Foundations.Vine.A.VineHingePairMK
public import WaveTurbulence.Foundations.Vine.A.VineMarkedGapMK3
public import WaveTurbulence.Foundations.Vine.A.VineSurvChainMK
public import WaveTurbulence.Foundations.Vine.A.VineSurvChainMK3
public import WaveTurbulence.Foundations.Vine.A.VineSurvSGMK
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineOperation
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceGapKind
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceHingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSplicePairs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescribedPoints
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSelectedTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.SurvData
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.SurvMK
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineSkipSelected
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.VineNormalizedRedSpliceGapKind
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects

/-! # FLOWER-LOW (packet L8), item I (wave 11): declarations deferred from waves 1–10

Item-I declarations of L8's sub-areas that failed in their first wave (missing inputs at the time or generator
issues since fixed), copied by source (sha256 in COPIED-SHA256SUMS) by `tools/itool/gen_i_spec.py`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false

namespace WaveTurbulence.GammaLow.Flower

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkMarkX
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkMark WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}

theorem markX_eq_MXLow (J : Finset (Fin w)) {ι : Type} (A : FamilyReconstruction w ι)
    (hA : Reg.Skeleton.IsPrimeGarden A.skeleton) :
    markXLow (γF := γF) J (⟨A.skeleton, hA, A.data, A.decodes⟩ : VineA.PrimeData A.layered) = MXLow (γF := γF) J A := by
  ext c
  exact and_congr Iff.rfl (not_congr (stemCleanAt_iff J _ _ _))

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical
open WaveTurbulence WaveTurbulence.Stage1 WaveTurbulence.RedSplice Finset
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}
variable {G : Garden w} {S : Finset (GBranch G.tree)} {Mk : Set (Fama.CLVineG γF G)}

/-- A (CL) vine that is an ingredient of a maximal group `S` but not a vine of `𝒱`: `S` has no (CN) ingredient
and the vine is the top ingredient of `S`. -/
theorem top_of_not_vinesVLow (hS : S ∈ Fama.maximalGroupsG γF G.molecule) {c : Fama.CLVineG γF G}
    (hi : Fama.IsIngredientG γF G.molecule S c.atoms) (hc : c ∉ Fama.vinesVG γF G) :
    ¬ (∃ T, Fama.IsIngredientG γF G.molecule S T ∧ Fama.IsCNVineG γF G T) ∧ Fama.IsTopIngredientG S c := by
  have hvl : ∃ a b, Src.IsVC γF G.molecule S a b ∨ Src.IsHVC γF G.molecule S a b := by
    rcases isIngredient_vc_or_hvcLow hi with ⟨a, b, h⟩ | ⟨a, b, h⟩
    · exact ⟨a, b, Or.inl h⟩
    · exact ⟨a, b, Or.inr h⟩
  have hnocn : ¬ (∃ T, Fama.IsIngredientG γF G.molecule S T ∧ Fama.IsCNVineG γF G T) := fun hcn =>
    hc (Famc.VineA.cl_mem_vinesV_of_CN hS hvl hcn c hi)
  refine ⟨hnocn, ?_⟩
  by_contra htop
  apply hc
  obtain ⟨a, b, hvc | hhvc⟩ := hvl
  · by_cases hr : Fama.IsRootVCG γF G S
    · exact ⟨S, hS, hi, Or.inr ⟨Or.inr hr, Or.inr htop⟩⟩
    · exact ⟨S, hS, hi, Or.inl ⟨a, b, hvc, hr⟩⟩
  · exact ⟨S, hS, hi, Or.inr ⟨Or.inl ⟨a, b, hhvc⟩, Or.inr htop⟩⟩

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.Stage1 WaveTurbulence.LFTwist WaveTurbulence.Reg.Skeleton
open WaveTurbulence.RedSplice (Prescription vinesV0 mem_vinesV0)
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}

/-- One LF operation from a selected family (any marking) keeps `𝒱₀` in correspondence. -/
theorem operation_v0CorrLow {p : ℕ} {kind : Bool} {ι : Type*} {A : FamilyReconstruction w ι} {i : ι}
    {σ : Prescription A.skeleton} {Mk : Set (Fama.CLVineG γF A.skeleton)} (hF : Fama.VineA.IsV0Fam γF A.family σ Mk)
    (op : FamilyOperation (p := p) (kind := kind) A i) : V0CorrLow (γF := γF) (operationMolIso op) σ := by
  cases op with
  | mk hc he ht hq ε C =>
    cases ε
    · exact v0Corr_reflLow A.skeleton σ
    · exact ⟨fun c hc' => (Fama.VineA.vinesV0_image (Fama.VineA.selectedMemberSite γF hF i) σ hc').imp fun c' h => ⟨h.1, h.2.1⟩,
        fun c' hc' => (Fama.VineA.vinesV0_preimage (Fama.VineA.selectedMemberSite γF hF i) σ hc').imp fun c h => ⟨h.1, h.2.1⟩⟩

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.Stage1 WaveTurbulence.LFTwist WaveTurbulence.Reg.Skeleton
open WaveTurbulence.RedSplice (Prescription vinesV0 mem_vinesV0)
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}

/-- **Along a batch from a selected family, `𝒱₀` corresponds.** -/
theorem batchIso_v0CorrLow {p : ℕ} {kind : Bool} {ι : Type*} {L : List ι} {A B : FamilyReconstruction w ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule} (h : BatchIso p kind L A B F) :
    ∀ (σ : Prescription A.skeleton) (Mk : Set (Fama.CLVineG γF A.skeleton)), Fama.VineA.IsV0Fam γF A.family σ Mk → V0CorrLow (γF := γF) F σ := by
  induction h with
  | nil A => exact fun σ _ _ => v0Corr_reflLow A.skeleton σ
  | skip _ _ ih => exact ih
  | @apply L A B i op J h ih =>
    intro σ Mk hF
    exact v0Corr_transLow _ _ σ (operation_v0CorrLow hF op)
      (ih _ _ (Fama.VineA.isV0Fam_operationMk hF op (markTransported_imgMarkLow (operationMolIso op) Mk)))

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
include hM

/-- The preimage of an unmerged atom: `π w = π z` with `z` unmerged forces `w = z`. -/
theorem eq_of_pi_eq_unmergedLow {z w : GBranch G.tree} (hz : (Fama.stSt γF G σ Mk).cls z = none)
    (h : (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls w = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls z) : w = z := by
  have hr := repC_eq_of_pi_eqLow hM σ h
  have hz' : repC (Fama.stSt γF G σ Mk).cls z = z := by simp [repC, hz]
  rw [hz'] at hr
  by_cases hw : (Fama.stSt γF G σ Mk).cls w = none
  · simpa [repC, hw] using hr
  · obtain ⟨u, hu, hwu⟩ := unit_of_clsLow hM σ hw
    rw [Fama.stSt_repC_memMk (Mk := Mk) hM σ hu hwu] at hr
    have := Fama.stSt_cls_memMk (Mk := Mk) hM σ hu u.isBlock.2.1
    rw [hr, hz] at this
    cases this

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

/-- A group with a designated atom is unmarked. -/
theorem not_marked_of_groupJointLow {Mk : Set (Fama.CLVineG γF G)} {S : Finset (GBranch G.tree)} {a : GBranch G.tree}
    (ha : Fama.VineA.NormalizedSplice.groupJoint γF G S Mk = some a) : ¬ Fama.markedGroup γF G Mk S := by
  intro hm
  rw [groupJoint_of_markedLow hm] at ha
  cases ha

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

theorem hingeOrigPair_of_not_markedLow {S : Finset (GBranch G.tree)} {Mk : Set (Fama.CLVineG γF G)} (h : ¬ Fama.markedGroup γF G Mk S) :
    Fama.VineA.NormalizedSplice.hingeOrigPair γF G S Mk = Fama.VineA.NormalizedSplice.hingeOrigPair γF G S := by
  unfold Fama.VineA.NormalizedSplice.hingeOrigPair
  rw [groupJoint_of_not_markedLow h]

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

theorem designatedObject_of_not_markedLow {S : Finset (GBranch G.tree)} {Mk : Set (Fama.CLVineG γF G)}
    (h : ¬ Fama.markedGroup γF G Mk S) : Fama.VineA.NormalizedSplice.designatedObject γF G S Mk = Fama.VineA.NormalizedSplice.designatedObject γF G S := by
  classical
  unfold Fama.VineA.NormalizedSplice.designatedObject
  by_cases h1 : ∃ a, Fama.VineA.NormalizedSplice.groupJoint γF G S = some a ∧ ∃ O, Fama.VineA.NormalizedSplice.IsDesig γF G S a O
  · have h0 : ∃ a, Fama.VineA.NormalizedSplice.groupJoint γF G S Mk = some a ∧ ∃ O, Fama.VineA.NormalizedSplice.IsDesig γF G S a O := by
      rw [groupJoint_of_not_markedLow h]; exact h1
    rw [dite_eq_left h0, dite_eq_left h1]
    have ha : h0.choose = h1.choose := by
      have e0 : Fama.VineA.NormalizedSplice.groupJoint γF G S = some h0.choose := (groupJoint_of_not_markedLow h).symm.trans h0.choose_spec.1
      exact Option.some.inj (e0.symm.trans h1.choose_spec.1)
    exact congrArg some (choose_eq_of_eq (by rw [ha]) _ _)
  · have h0 : ¬ ∃ a, Fama.VineA.NormalizedSplice.groupJoint γF G S Mk = some a ∧ ∃ O, Fama.VineA.NormalizedSplice.IsDesig γF G S a O := by
      rw [groupJoint_of_not_markedLow h]; exact h1
    rw [dite_eq_right h0, dite_eq_right h1]

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

theorem intPairOrig_of_not_markedLow {S : Finset (GBranch G.tree)} {Mk : Set (Fama.CLVineG γF G)} (h : ¬ Fama.markedGroup γF G Mk S) :
    Fama.VineA.NormalizedSplice.intPairOrig γF G S Mk = Fama.VineA.NormalizedSplice.intPairOrig γF G S := by
  classical
  have hspec : (fun p => Fama.VineA.NormalizedSplice.IntSpec γF G S p Mk) = (fun p => Fama.VineA.NormalizedSplice.IntSpec γF G S p) := by
    funext p
    unfold Fama.VineA.NormalizedSplice.IntSpec
    rw [groupJoint_of_not_markedLow h, designatedObject_of_not_markedLow h]
  unfold Fama.VineA.NormalizedSplice.intPairOrig
  by_cases h1 : ∃ p, Fama.VineA.NormalizedSplice.IntSpec γF G S p
  · have h0 : ∃ p, Fama.VineA.NormalizedSplice.IntSpec γF G S p Mk := by
      obtain ⟨p, hp⟩ := h1; exact ⟨p, (congrFun hspec p).mpr hp⟩
    rw [dite_eq_left h0, dite_eq_left h1]
    exact congrArg some (choose_eq_of_eq hspec _ _)
  · have h0 : ¬ ∃ p, Fama.VineA.NormalizedSplice.IntSpec γF G S p Mk := fun ⟨p, hp⟩ => h1 ⟨p, (congrFun hspec p).mp hp⟩
    rw [dite_eq_right h0, dite_eq_right h1]

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
include hM

/-- An atom carrying a group's designated atom lies, through `repC`, in the group. -/
theorem groupAtom_memLow {T : Finset (GBranch G.tree)} {v : GBranch (Fama.stSt γF G σ Mk).G.tree}
    (hT : Fama.VineA.NormalizedSplice.groupAtom γF G σ T Mk = some v) :
    ¬ Fama.markedGroup γF G Mk T ∧ ∃ a, Fama.VineA.NormalizedSplice.groupJoint γF G T = some a ∧ a ∈ T ∧ (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a = v := by
  unfold Fama.VineA.NormalizedSplice.groupAtom at hT
  by_cases hm : Fama.markedGroup γF G Mk T
  · rw [groupJoint_of_markedLow hm] at hT; cases hT
  · rw [groupJoint_of_not_markedLow hm] at hT
    cases hg : Fama.VineA.NormalizedSplice.groupJoint γF G T with
    | none => rw [hg] at hT; cases hT
    | some a =>
      rw [hg] at hT
      exact ⟨hm, a, rfl, (Fama.VineA.NormalizedSplice.groupJoint_kind hg).1, Option.some.inj hT⟩

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
include hM

/-- Atoms of `G_sb` that are images of atoms of two groups determine the group. -/
theorem group_eq_of_pi_eqLow {S S' : Finset (GBranch G.tree)} (hS : S ∈ Fama.maximalGroupsG γF G.molecule)
    (hS' : S' ∈ Fama.maximalGroupsG γF G.molecule) {a a' : GBranch G.tree} (ha : a ∈ S) (ha' : a' ∈ S')
    (h : (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a') : S = S' := by
  by_contra hne
  have e := repC_eq_of_pi_eqLow hM σ h
  exact Finset.disjoint_left.mp (Fama.VineA.NormalizedSplice.groups_disjoint hM hS hS' hne) (Fama.VineA.NormalizedSplice.repC_mem_groupMk hM σ hS ha)
    (e ▸ Fama.VineA.NormalizedSplice.repC_mem_groupMk hM σ hS' ha')

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
include hM

theorem groupAtom_injMkLow {S S' : Finset (GBranch G.tree)} (hS : S ∈ Fama.maximalGroupsG γF G.molecule)
    (hS' : S' ∈ Fama.maximalGroupsG γF G.molecule) {v : GBranch (Fama.stSt γF G σ Mk).G.tree}
    (h : Fama.VineA.NormalizedSplice.groupAtom γF G σ S Mk = some v) (h' : Fama.VineA.NormalizedSplice.groupAtom γF G σ S' Mk = some v) : S = S' := by
  obtain ⟨-, a, -, haS, hav⟩ := groupAtom_memLow hM σ h
  obtain ⟨-, a', -, haS', hav'⟩ := groupAtom_memLow hM σ h'
  exact group_eq_of_pi_eqLow hM σ hS hS' haS haS' (hav.trans hav'.symm)

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
include hM

/-- Main's `Fama.VineA.NormalizedSplice.gapSpecification_of` with `Mk`. -/
theorem gapSpecificationMk_ofLow {S : Finset (GBranch G.tree)} (hS : S ∈ Fama.maximalGroupsG γF G.molecule)
    {v : GBranch (Fama.stSt γF G σ Mk).G.tree} (hv : Fama.VineA.NormalizedSplice.groupAtom γF G σ S Mk = some v)
    {x y : GardenDart (Fama.stSt γF G σ Mk).G} (hp : Fama.VineA.NormalizedSplice.gapPair γF G σ S v = some (x, y))
    (hT : TripleAt (Fama.stSt γF G σ Mk).G v x y) :
    Fama.VineA.NormalizedSplice.gapSpecificationMk γF G σ Mk v = some ⟨x, y, hT.1, hT.2.1, hT.2.2.1, hT.2.2.2, σ S⟩ := by
  classical
  have h : ∃ S' ∈ Fama.maximalGroupsG γF G.molecule, Fama.VineA.NormalizedSplice.groupAtom γF G σ S' Mk = some v := ⟨S, hS, hv⟩
  have hc : h.choose = S := groupAtom_injMkLow hM σ h.choose_spec.1 hS h.choose_spec.2 hv
  unfold Fama.VineA.NormalizedSplice.gapSpecificationMk
  rw [dite_eq_left h]
  simp only [hc, hp, dite_eq_left hT]

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
include hM

/-- **Main's `Fama.VineA.NormalizedSplice.gapSpecification_group` for an unmarked group.** -/
theorem gapSpecificationMk_groupLow {S : Finset (GBranch G.tree)} (hS : S ∈ Fama.maximalGroupsG γF G.molecule)
    (hnm : ¬ Fama.markedGroup γF G Mk S) :
    ∃ a, Fama.VineA.NormalizedSplice.groupJoint γF G S = some a ∧
      ∃ e : LocalGapSpecification (Fama.stSt γF G σ Mk).G ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a),
      Fama.VineA.NormalizedSplice.gapSpecificationMk γF G σ Mk ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a) = some e ∧ e.kind = σ S ∧
      ∃ p, (Fama.stSt γF G σ Mk).M.od e.first = p.1 ∧ (Fama.stSt γF G σ Mk).M.od e.second = p.2 ∧
        (((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a ∈ (Fama.stSt γF G σ Mk).hinges →
            Fama.VineA.NormalizedSplice.hingeOrigPair γF G S = some p ∧ Fama.VineA.NormalizedSplice.HingeSpec γF G S a p) ∧
          ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a ∉ (Fama.stSt γF G σ Mk).hinges →
            Fama.VineA.NormalizedSplice.intPairOrig γF G S = some p ∧ Fama.VineA.NormalizedSplice.IntSpec γF G S p)) := by
  classical
  obtain ⟨a, ha⟩ := Fama.VineA.NormalizedSplice.exists_groupJoint_eq hS
  have hatom : Fama.VineA.NormalizedSplice.groupAtom γF G σ S Mk = some ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a) := by
    unfold Fama.VineA.NormalizedSplice.groupAtom; rw [groupJoint_of_not_markedLow hnm, ha]; rfl
  refine ⟨a, ha, ?_⟩
  by_cases hh : (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a ∈ (Fama.stSt γF G σ Mk).hinges
  · obtain ⟨hσ, u0, hu0, hau0⟩ := hinge_unitMkLow hM σ hS hnm ha hh
    obtain ⟨p, hp, hsp⟩ := Fama.VineA.NormalizedSplice.hingeOrigPair_spec ha ⟨u0, hu0, hau0⟩
    have hsp' := hsp
    unfold Fama.VineA.NormalizedSplice.HingeSpec at hsp'
    obtain ⟨u, hu, hau, j, hj, hT, hn1, hn2, -⟩ := hsp'
    have huB : u ∈ Fama.unitBlocks γF G σ Mk :=
      (Fama.mem_unitBlocksMk (Mk := Mk)).mpr ⟨S, hS, hσ, by rw [Fama.groupUnitsMk_of_not_marked hnm]; exact hu⟩
    have hrepj : repC (Fama.stSt γF G σ Mk).cls j = u.upper := Fama.stSt_repC_memMk hM σ huB hj
    have hrepc : repC (Fama.stSt γF G σ Mk).cls (G.molecule.atom p.1) =
        (Fama.stSt γF G σ Mk).M.ob ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a) := by
      rw [(Fama.stSt γF G σ Mk).M.ob_pi, Fama.stSt_repC_memMk hM σ huB hau, hT.1, hrepj]
    have hrepc2 : repC (Fama.stSt γF G σ Mk).cls (G.molecule.atom p.2) =
        (Fama.stSt γF G σ Mk).M.ob ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a) := by
      rw [(Fama.stSt γF G σ Mk).M.ob_pi, Fama.stSt_repC_memMk hM σ huB hau, hT.2.1, hrepj]
    have hnint : ∀ d : GardenDart G, G.molecule.atom d = j → ¬ G.molecule.InGroup u.atoms d →
        ¬ ∃ a', (Fama.stSt γF G σ Mk).cls (G.molecule.atom d) = some a' ∧
          (Fama.stSt γF G σ Mk).cls (G.molecule.atom (G.molecule.mate d)) = some a' := by
      intro d hd hnd ⟨a', ha', ha''⟩
      rw [hd, Fama.stSt_cls_memMk hM σ Mk huB hj] at ha'
      have : a' = u.upper := (Option.some.inj ha').symm
      subst this
      exact hnd ⟨hd ▸ hj, Fama.VineA.NormalizedSplice.mem_of_cls_eqMk hM σ huB ha''⟩
    obtain ⟨y1, y2, hy1, hy2, hT'⟩ := (Fama.stSt γF G σ Mk).M.tripleAt_of_lift
      (c := (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a) (d1 := p.1) (d2 := p.2) hrepc hrepc2
      (hnint p.1 hT.1 hn1) (hnint p.2 hT.2.1 hn2) hT.2.2.2 hT.2.2.1
    obtain ⟨q, hq, hq1, hq2, hqT⟩ := Fama.VineA.NormalizedSplice.liftPair_of_existsMk (σ := σ)
      (v := (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a) (p := p) ⟨(y1, y2), hy1, hy2, hT'⟩
    have hgp : Fama.VineA.NormalizedSplice.gapPair γF G σ S ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a) = some q := by
      unfold Fama.VineA.NormalizedSplice.gapPair; rw [ite_eq_left hh]; unfold Fama.VineA.NormalizedSplice.hingeEntryPair
      rw [hingeOrigPair_of_not_markedLow hnm, hp, Option.bind_some]; exact hq
    exact ⟨_, gapSpecificationMk_ofLow hM σ hS hatom hgp hqT, rfl, p, hq1, hq2, ⟨fun _ => ⟨hp, hsp⟩,
      fun h => absurd hh h⟩⟩
  · have hcls : (Fama.stSt γF G σ Mk).cls a = none := by
      have h1 := ((Fama.stSt γF G σ Mk).mem_hinges ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a)).not.mp hh
      rw [not_not, (Fama.stSt γF G σ Mk).M.ob_pi (Fama.stSt γF G σ Mk).hcls] at h1
      rcases hc : (Fama.stSt γF G σ Mk).cls a with _ | r
      · rfl
      · exfalso
        have hr : repC (Fama.stSt γF G σ Mk).cls a = r := by simp [repC, hc]
        rw [hr] at h1
        rw [(Fama.stSt γF G σ Mk).hcls a r hc] at h1
        cases h1
    have hrep : repC (Fama.stSt γF G σ Mk).cls a = a := by simp [repC, hcls]
    obtain ⟨p, hp, hsp⟩ := Fama.VineA.NormalizedSplice.intPairOrig_spec hS
    have hsp' := hsp
    unfold Fama.VineA.NormalizedSplice.IntSpec at hsp'
    obtain ⟨a1, O, ha1, hO, hOj, hT0, hx0, hy0⟩ := hsp'
    rw [ha] at ha1
    cases ha1
    obtain ⟨y1, y2, hy1, hy2, hT⟩ := (Fama.stSt γF G σ Mk).M.tripleAt_of_lift
      (c := (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a) (d1 := p.1) (d2 := p.2)
      (by rw [hT0.1, (Fama.stSt γF G σ Mk).M.ob_pi, hrep]) (by rw [hT0.2.1, (Fama.stSt γF G σ Mk).M.ob_pi, hrep])
      (by rw [hT0.1, hcls]; simp) (by rw [hT0.2.1, hcls]; simp) hT0.2.2.2 hT0.2.2.1
    obtain ⟨q, hq, hq1, hq2, hqT⟩ := Fama.VineA.NormalizedSplice.liftPair_of_existsMk (σ := σ)
      (v := (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a) (p := p) ⟨(y1, y2), hy1, hy2, hT⟩
    have hgp : Fama.VineA.NormalizedSplice.gapPair γF G σ S ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a) = some q := by
      unfold Fama.VineA.NormalizedSplice.gapPair; rw [ite_eq_right hh]; unfold Fama.VineA.NormalizedSplice.internalPair
      rw [intPairOrig_of_not_markedLow hnm, hp, Option.bind_some]; exact hq
    exact ⟨_, gapSpecificationMk_ofLow hM σ hS hatom hgp hqT, rfl, p, hq1, hq2, ⟨fun h => absurd h hh,
      fun _ => ⟨hp, hsp⟩⟩⟩

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
include hM

/-- **Main's `Fama.VineA.NormalizedSplice.gapSpecification_indicator_iff` for an unmarked group.** -/
theorem gapSpecificationMk_indicator_iffLow {S : Finset (GBranch G.tree)} (hS : S ∈ Fama.maximalGroupsG γF G.molecule)
    (hnm : ¬ Fama.markedGroup γF G Mk S) {d : ℕ}
    (L γ η : ℝ) (w : Mom d) (c : GBranch G.tree → Mom d) (κ : GardenDart G → (Fin d → ℤ))
    (hκ : G.molecule.IsDecoration L w c κ) (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0)
    (κsb : GardenDart (Fama.stSt γF G σ Mk).G → (Fin d → ℤ)) (hlab : ∀ y, κsb y = κ ((Fama.stSt γF G σ Mk).M.od y)) :
    ∃ a O, Fama.VineA.NormalizedSplice.groupJoint γF G S = some a ∧ Fama.VineA.NormalizedSplice.designatedObject γF G S = some O ∧
      ∃ e : LocalGapSpecification (Fama.stSt γF G σ Mk).G ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a),
        Fama.VineA.NormalizedSplice.gapSpecificationMk γF G σ Mk ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a) = some e ∧
        ∀ k, O.HasGapKind L γ η w κ k →
          (Molecule.gapKind L γ η ((w + latticePoint L (κsb e.first)) - (w + latticePoint L (κsb e.second))) = e.kind
            ↔ k = σ S) := by
  obtain ⟨a, ha, e, he, hk, p, h1, h2, hnh⟩ := gapSpecificationMk_groupLow hM σ hS hnm
  obtain ⟨a', O, ha', hO, hd⟩ := Fama.VineA.NormalizedSplice.designatedObject_spec hS
  rw [ha] at ha'
  cases ha'
  refine ⟨a, O, ha, hO, e, he, fun k hOk => ?_⟩
  have hgap : (w + latticePoint L (κsb e.first)) - (w + latticePoint L (κsb e.second)) =
      Molecule.gapAt L w κ p.1 p.2 := by
    simp only [Molecule.gapAt, Molecule.kvec, hlab, h1, h2]
  rw [hgap, hk]
  have hkind : Molecule.gapKind L γ η (Molecule.gapAt L w κ p.1 p.2) = k := by
    by_cases hh : (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a ∈ (Fama.stSt γF G σ Mk).hinges
    · obtain ⟨_, hsp⟩ := hnh.1 hh
      exact Fama.VineA.NormalizedSplice.hingeOrig_gapKind hM L γ η w c κ hκ hc0 hsp hd hOk
    · obtain ⟨hp, hsp⟩ := hnh.2 hh
      unfold Fama.VineA.NormalizedSplice.IntSpec at hsp
      obtain ⟨a1, O1, ha1, hO1, hOj, hT, hx, hy⟩ := hsp
      rw [hO] at hO1; cases hO1
      rw [ha] at ha1; cases ha1
      exact Fama.VineA.NormalizedSplice.obj_pair_gapKind G.molecule hM L γ η w c κ hκ hc0 O hOk hOj hT.1 hT.2.1 hx hy hT.2.2.2
  rw [hkind]

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
include hM

/-- **Distinct atoms with one image lie in one run.** -/
theorem run_of_pi_eqLow {S : Finset (GBranch G.tree)} (hS : S ∈ Fama.maximalGroupsG γF G.molecule) (h : Fama.markedGroup γF G Mk S)
    {z z' : GBranch G.tree} (hz : z ∈ S) (hne : z ≠ z')
    (he : (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls z = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls z') :
    ∃ u ∈ (markedUnitsOfMKLow h).runs, z ∈ u.atoms ∧ z' ∈ u.atoms := by
  classical
  have hrep := repC_eq_of_pi_eqLow hM σ he
  -- a classified atom has the crown of its unit as representative; the crown lies in the unit
  have crown : ∀ x (u : CLBlock G), u ∈ Fama.unitBlocks γF G σ Mk → x ∈ u.atoms → repC (Fama.stSt γF G σ Mk).cls x = u.upper := by
    intro x u hu hx
    simp [repC, Fama.stSt_cls_memMk hM σ Mk hu hx]
  have none_ne_crown : ∀ x (u : CLBlock G), u ∈ Fama.unitBlocks γF G σ Mk → (Fama.stSt γF G σ Mk).cls x = none → x ≠ u.upper := by
    intro x u hu hx hxu
    rw [hxu, Fama.stSt_cls_memMk hM σ Mk hu u.isBlock.2.1] at hx
    cases hx
  by_cases hcz : (Fama.stSt γF G σ Mk).cls z = none
  · exfalso
    by_cases hcz' : (Fama.stSt γF G σ Mk).cls z' = none
    · apply hne
      simpa [repC, hcz, hcz'] using hrep
    · obtain ⟨u', hu', hzu'⟩ := unit_of_clsLow hM σ hcz'
      have h1 : repC (Fama.stSt γF G σ Mk).cls z = z := by simp [repC, hcz]
      rw [h1, crown z' u' hu' hzu'] at hrep
      exact none_ne_crown z u' hu' hcz hrep
  · obtain ⟨u, hu, hzu⟩ := unit_of_clsLow hM σ hcz
    have hcz' : (Fama.stSt γF G σ Mk).cls z' ≠ none := by
      intro hcz'
      have h1 : repC (Fama.stSt γF G σ Mk).cls z' = z' := by simp [repC, hcz']
      rw [h1, crown z u hu hzu] at hrep
      exact none_ne_crown z' u hu hcz' hrep.symm
    obtain ⟨u', hu', hzu'⟩ := unit_of_clsLow hM σ hcz'
    have hup : u.upper = u'.upper := by rw [← crown z u hu hzu, ← crown z' u' hu' hzu', hrep]
    have huu : u = u' := by
      by_contra hne'
      have hdj := pairwise_symm_forallMK (fun x y h => Disjoint.symm h) (Fama.unitBlocks_pairwiseMk hM σ Mk) hu hu' hne'
      exact Finset.disjoint_left.mp hdj u.isBlock.2.1 (hup ▸ u'.isBlock.2.1)
    subst huu
    obtain ⟨S'', hS'', -, hmem⟩ := (Fama.mem_unitBlocksMk (Mk := Mk)).mp hu
    have hSS : S = S'' := by
      by_contra hne''
      exact Finset.disjoint_left.mp (Fama.VineA.NormalizedSplice.groups_disjoint hM hS hS'' hne'') hz (Fama.groupUnitsMk_sub hmem hzu)
    subst hSS
    rw [groupUnitsMk_of_markedMKLow h] at hmem
    exact ⟨u, hmem, hzu, hzu'⟩

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

theorem groupSurvMk_nodupLow {Mk : Set (Fama.CLVineG γF G)} (S : Finset (GBranch G.tree)) : (Fama.groupSurvMk γF G Mk S).Nodup := by
  by_cases hm : Fama.markedGroup γF G Mk S
  · rw [groupSurvMk_eq_unitsLow hm]
    obtain ⟨D', _, _, N, L, a, b, -, hs, -, -, -, -, -, hsub, -⟩ := (markedUnitsOfMKLow hm).surv_spine
    exact hsub.nodup (Famc.SpineG.nodupMK hs)
  · rw [Fama.groupSurvMk_of_not_marked hm]
    exact List.nodup_nil

end

end WaveTurbulence.GammaLow.Flower
