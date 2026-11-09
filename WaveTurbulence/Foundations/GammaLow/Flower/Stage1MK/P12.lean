/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Defs
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Bridge
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
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P11
public import WaveTurbulence.Foundations.FinalCount.RedSpliceSurvMK3
public import WaveTurbulence.Foundations.Flower.MkDefs.Intrinsic
public import WaveTurbulence.Foundations.Flower.MkDefs.Stage1MK
public import WaveTurbulence.Foundations.Flower.FinalMKDefs.Count
public import WaveTurbulence.Foundations.Flower.FinalMKDefs.Piece
public import WaveTurbulence.Foundations.Flower.FinalMKDefs.PieceSel
public import WaveTurbulence.Foundations.Flower.MkDefs.Stage1MKFull
public import WaveTurbulence.Foundations.Flower.MkMark.Batch
public import WaveTurbulence.Foundations.Flower.MkMark.BatchSel
public import WaveTurbulence.Foundations.Flower.MkMark.CountBound
public import WaveTurbulence.Foundations.Flower.MkMarkX.Transport
public import WaveTurbulence.Foundations.Vine.A.VineMarkedGapMK
public import WaveTurbulence.Foundations.Vine.A.VineMarkedGapMK2
public import WaveTurbulence.Foundations.Vine.A.VineMarkedGapMK3
public import WaveTurbulence.Foundations.Vine.A.VineSurvMK
public import WaveTurbulence.Foundations.Vine.A.VineSurvChainMK
public import WaveTurbulence.Foundations.Vine.A.VineSurvChainMK2
public import WaveTurbulence.Foundations.Vine.A.VineSurvChainMK3
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceHingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVC
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Ingr
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.SurvData
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.SurvMK
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.TVine.Struct.Drawn.VCMember

/-! # FLOWER-LOW (packet L8), item I (wave 12): marked Stage-1′ declarations over `𝒱_γ`

Item-I declarations of L8's sub-areas (I-BASE, I-GATE) that became portable after the latest publications, copied
by source (sha256 in COPIED-SHA256SUMS) by `tools/itool/gen_i_spec.py`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false

namespace WaveTurbulence.GammaLow.Flower

section
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

/-- **o75 Lemma 3 (ii), with 75-W1**: the image of a survivor of a marked SG group in `G_sb`. -/
theorem survivor_imageMKLow {σ : Prescription G} {Mk : Set (Fama.CLVineG γF G)} {S : Finset (GBranch G.tree)}
    (hS : S ∈ Fama.maximalGroupsG γF G.molecule) (hσ : σ S = Molecule.GapKind.SG) (h : Fama.markedGroup γF G Mk S)
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ (markedUnitsOfMKLow h).surv) :
    ∃ O : Src.Object γF (Fama.stSt γF G σ Mk).G.molecule,
      O.atoms = t.1.image ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls) ∧
      O.upper = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls t.2.1 ∧
      O.lower = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls t.2.2 ∧
      Set.InjOn ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls) t.1 ∧
      (∀ c, (Fama.stSt γF G σ Mk).cls ((Fama.stSt γF G σ Mk).M.ob c) ≠ none → c ∈ O.atoms → c = O.upper ∨ c = O.lower) ∧
      (∀ z ∈ t.1, z ≠ t.2.1 → z ≠ t.2.2 → (Fama.stSt γF G σ Mk).cls z = none) ∧
      ((Src.IsSomeVine γF (Fama.stSt γF G σ Mk).G.molecule O.atoms O.upper O.lower ∧
          ∃ hvc, O.shape = Src.VineLikeObject.vc hvc) ∨
        (Src.AllowedCollectionObject γF (Fama.stSt γF G σ Mk).G O ∧ (∃ R, O.shape = Src.VineLikeObject.hyper R) ∧
          ∀ t' ∈ (markedUnitsOfMKLow h).surv, t'.1 = t.1)) := by
  classical
  have hM : G.molecule.IsMolecule := Mole.garden_isMolecule G
  have hvt : Src.IsSomeVine γF G.molecule t.1 t.2.1 t.2.2 := ((markedUnitsOfMKLow h).surv_spec t ht).1
  -- the common conclusion from a decomposition in the garden molecule
  have fromVine : ∀ (UR L0 R0 : Finset (GBranch G.tree)) (a' b' : GBranch G.tree),
      SDecomp G.molecule (Fama.stSt γF G σ Mk).cls UR t.1 L0 R0 a' b' t.2.1 t.2.2 → ∃ O : Src.Object γF (Fama.stSt γF G σ Mk).G.molecule,
      O.atoms = t.1.image ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls) ∧
      O.upper = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls t.2.1 ∧
      O.lower = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls t.2.2 ∧
      Set.InjOn ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls) t.1 ∧
      (∀ c, (Fama.stSt γF G σ Mk).cls ((Fama.stSt γF G σ Mk).M.ob c) ≠ none → c ∈ O.atoms → c = O.upper ∨ c = O.lower) ∧
      (∀ z ∈ t.1, z ≠ t.2.1 → z ≠ t.2.2 → (Fama.stSt γF G σ Mk).cls z = none) ∧
      ((Src.IsSomeVine γF (Fama.stSt γF G σ Mk).G.molecule O.atoms O.upper O.lower ∧
          ∃ hvc, O.shape = Src.VineLikeObject.vc hvc) ∨
        (Src.AllowedCollectionObject γF (Fama.stSt γF G σ Mk).G O ∧ (∃ R, O.shape = Src.VineLikeObject.hyper R) ∧
          ∀ t' ∈ (markedUnitsOfMKLow h).surv, t'.1 = t.1)) := by
    intro UR L0 R0 a' b' H
    obtain ⟨O, hOa, hOu, hOl, hOv, hOs⟩ := vine_objectStMKLow (Fama.stSt γF G σ Mk) H hvt
    refine ⟨O, hOa, hOu, hOl, H.injOn_piMK _, fun c hcn hcO => ?_, H.interior_noneMK, Or.inl ⟨hOv, hOs⟩⟩
    rw [hOu, hOl]
    exact H.hinge_imageMK _ c hcn (hOa ▸ hcO)
  have h' := h
  obtain ⟨c, -, -, hci⟩ := h'
  rcases hci with ⟨a, b, n, x, y, hB, hI⟩ | ⟨a, b, e, n, x, y, hends, hn2, hBe, hI⟩
  · -- a VC
    obtain ⟨L, hs⟩ := Fama.Spine.of_chain (Fama.chainIngredientG_spec hI).1
    obtain ⟨UR, L0, R0, a', b', H, -, -⟩ := surv_sdecompMKLow hM hs hB (fun t ht => ((Famc.SpineG.mem_vine'MK hs) ht).1)
      (fun t ht => Or.inl ⟨a, b, L.length, t.2.1, t.2.2, hB, hs.ingredient_of_mem ht⟩)
      (fun T hT => Fama.isIngredient_vc hM hB hs hT) hS hσ h ht
    exact fromVine UR L0 R0 a' b' H
  · -- an HVC
    have hab : a ≠ b := hBe.2.2.2.1
    have hne : G.molecule.atom e ≠ G.molecule.atom (G.molecule.mate e) := by
      intro h0
      unfold Molecule.ends at hends
      rw [h0] at hends
      rcases Sym2.eq_iff.mp hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hab (h1.symm.trans h2)
      · exact hab (h2.symm.trans h1)
    have hN := Vine.eraseBond_isMolecule G.molecule hM e hne
    obtain ⟨L, hs, hlen⟩ := Fama.Spine.of_chain_len (Fama.chainIngredientG_spec hI).1
    have hlen2 : 2 ≤ L.length := hlen ▸ hn2
    have hmemb : ∀ T, Fama.IsIngredientG γF G.molecule S T → ∃ p q, (T, p, q) ∈ L ∨ (T, q, p) ∈ L :=
      fun T hT => Fama.isIngredient_hvc hM hends hBe hs hlen2 hT
    obtain ⟨UR, L0, R0, a', b', H, hURS, hfin⟩ := surv_sdecompMKLow hN hs hBe
      (fun t ht => (Fama.vine_transfer G.molecule hends (hs.not_both hlen2 ht) t.2.1 t.2.2).mp ((Famc.SpineG.mem_vine'MK hs) ht).1)
      (fun t ht => Or.inr ⟨a, b, e, L.length, t.2.1, t.2.2, hends, hlen2, hBe, hs.ingredient_of_mem ht⟩)
      hmemb hS hσ h ht
    by_cases hab' : a ∈ UR ∧ b ∈ UR
    · -- 75-W1: the only survivor of an HVC; its image is an HV
      obtain ⟨-, hab'', hsame⟩ := hfin hab'
      have hnot : ¬ (a ∈ t.1 ∧ b ∈ t.1) := by
        obtain ⟨p, q, hm | hm⟩ := hmemb _ ((markedUnitsOfMKLow h).surv_spec t ht).2.1
        · exact hs.not_both hlen2 hm
        · exact hs.not_both hlen2 hm
      have hvN : Src.IsSomeVine γF (Mole.eraseBond G.molecule e) t.1 t.2.1 t.2.2 :=
        (Fama.vine_transfer G.molecule hends hnot t.2.1 t.2.2).mpr hvt
      obtain ⟨O, hOA, hOa, hOu, hOl, R, hR, -⟩ :=
        hyper_objectStMKLow (Fama.stSt γF G σ Mk) H (hends.trans hab''.symm) hvN
      refine ⟨O, hOa, hOu, hOl, H.injOn_piMK _, fun c hcn hcO => ?_, H.interior_noneMK,
        Or.inr ⟨hOA, ⟨R, hR⟩, hsame⟩⟩
      rw [hOu, hOl]
      exact H.hinge_imageMK _ c hcn (hOa ▸ hcO)
    · -- the decomposition lives in the garden molecule
      have htr : ∀ X x' y', X ⊆ UR → (Mole.eraseBond G.molecule e).IsBlock X x' y' → G.molecule.IsBlock X x' y' :=
        fun X x' y' hX hb => (block_transfer G.molecule hends (fun hh => hab' ⟨hX hh.1, hX hh.2⟩) x' y').mp hb
      exact fromVine UR L0 R0 a' b'
        { toSkelDecomp := H.toSkelDecomp.transferMK hM htr
          hcls := H.hcls
          hLcl := H.hLcl
          hRcl := H.hRcl
          hLc := H.hLc
          hRc := H.hRc
          hNone := H.hNone }

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

/-- **The darts of a survivor are not internal to a class**: a dart inside a survivor `t` of a marked group, at a joint
of `t`, lifts to `G_sb`. -/
theorem survDart_not_internalLow (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
    {S : Finset (GBranch G.tree)} (hS : S ∈ Fama.maximalGroupsG γF G.molecule) (hmk : Fama.markedGroup γF G Mk S)
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ (markedUnitsOfMKLow hmk).surv)
    {d : GardenDart G} (hd : G.molecule.InGroup t.1 d) (hdj : G.molecule.atom d = t.2.1 ∨ G.molecule.atom d = t.2.2) :
    ¬ ∃ a, (Fama.stSt γF G σ Mk).cls (G.molecule.atom d) = some a ∧
      (Fama.stSt γF G σ Mk).cls (G.molecule.atom (G.molecule.mate d)) = some a := by
  rintro ⟨a, ha1, ha2⟩
  obtain ⟨hvine, hI, -⟩ := (markedUnitsOfMKLow hmk).surv_spec t ht
  have htS : t.1 ⊆ S := isIngredient_subsetLow hI
  by_cases hσ : σ S = Molecule.GapKind.SG
  · have hX := hvine
    have hloop := isSomeVine_noLoopLow hX d hd.1
    obtain ⟨O, hOat, hOu, hOl, hinj, -, hint, -⟩ := survivor_imageMKLow hS hσ hmk ht
    have hm : G.molecule.atom (G.molecule.mate d) ∈ t.1 := hd.2
    by_cases hmi : G.molecule.atom (G.molecule.mate d) ≠ t.2.1 ∧ G.molecule.atom (G.molecule.mate d) ≠ t.2.2
    · rw [hint _ hm hmi.1 hmi.2] at ha2; cases ha2
    · -- both ends are joints of `t`: they are distinct atoms in one class, against injectivity of `π`
      have hpi : (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls (G.molecule.atom d) =
          (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls (G.molecule.atom (G.molecule.mate d)) := by
        apply (Fama.stSt γF G σ Mk).M.ob_inj
        rw [(Fama.stSt γF G σ Mk).M.ob_pi, (Fama.stSt γF G σ Mk).M.ob_pi]
        unfold repC
        rw [ha1, ha2]
        rfl
      exact hloop (hinj hd.1 hm hpi)
  · rw [cls_none_of_not_SGLow hM σ hS hσ (htS hd.1)] at ha1
    cases ha1

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

/-- A survivor carrying a marked entry is a survivor of a marked group, and its upper joint lies in the group. -/
theorem markedEntryAt_memLow {T : Finset (GBranch G.tree)}
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} {v : GBranch (Fama.stSt γF G σ Mk).G.tree}
    (hT : Fama.VineA.NormalizedSplice.MarkedEntryAt γF G σ T t v) :
    ∃ hmk : Fama.markedGroup γF G Mk T, t ∈ (markedUnitsOfMKLow hmk).surv ∧ t.2.1 ∈ T := by
  obtain ⟨ht, -⟩ := hT
  by_cases hm : Fama.markedGroup γF G Mk T
  · rw [Fama.groupSurvMk_of_marked hm (Fama.exists_markedGroupUnits hm)] at ht
    obtain ⟨hX, hI, -⟩ := (markedUnitsOfMKLow hm).surv_spec t ht
    exact ⟨hm, ht, isIngredient_subsetLow hI (Src.isBlock_of_isSomeVine hX).2.1⟩
  · rw [Fama.groupSurvMk_of_not_marked hm] at ht; cases ht

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

theorem markedEntryAt_group_eqLow {S S' : Finset (GBranch G.tree)} (hS : S ∈ Fama.maximalGroupsG γF G.molecule)
    (hS' : S' ∈ Fama.maximalGroupsG γF G.molecule) {t t' : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree}
    {v : GBranch (Fama.stSt γF G σ Mk).G.tree} (h : Fama.VineA.NormalizedSplice.MarkedEntryAt γF G σ S t v) (h' : Fama.VineA.NormalizedSplice.MarkedEntryAt γF G σ S' t' v) : S = S' := by
  obtain ⟨-, -, htS⟩ := markedEntryAt_memLow hM σ h
  obtain ⟨-, -, htS'⟩ := markedEntryAt_memLow hM σ h'
  exact group_eq_of_pi_eqLow hM σ hS hS' htS htS' (h.2.trans h'.2.symm)

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

theorem not_groupAtom_of_markedEntryAtLow {S : Finset (GBranch G.tree)} (hS : S ∈ Fama.maximalGroupsG γF G.molecule)
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} {v : GBranch (Fama.stSt γF G σ Mk).G.tree}
    (h : Fama.VineA.NormalizedSplice.MarkedEntryAt γF G σ S t v) :
    ¬ ∃ S' ∈ Fama.maximalGroupsG γF G.molecule, Fama.VineA.NormalizedSplice.groupAtom γF G σ S' Mk = some v := by
  rintro ⟨S', hS', h'⟩
  obtain ⟨hmk, -, htS⟩ := markedEntryAt_memLow hM σ h
  obtain ⟨hnm, a, -, haS, hav⟩ := groupAtom_memLow hM σ h'
  have hSS := group_eq_of_pi_eqLow hM σ hS hS' htS haS (h.2.trans hav.symm)
  subst hSS
  exact hnm hmk

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

theorem survObj_spec'Low {σ : Prescription G} {Mk : Set (Fama.CLVineG γF G)}
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ Fama.survivorsMk γF G σ Mk) :
    (survObjLow ht).atoms = t.1.image ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls) ∧
      (survObjLow ht).upper = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls t.2.1 ∧
      (survObjLow ht).lower = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls t.2.2 ∧
      Set.InjOn ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls) t.1 ∧
      (∀ c, (Fama.stSt γF G σ Mk).cls ((Fama.stSt γF G σ Mk).M.ob c) ≠ none → c ∈ (survObjLow ht).atoms →
        c = (survObjLow ht).upper ∨ c = (survObjLow ht).lower) ∧
      (∀ z ∈ t.1, z ≠ t.2.1 → z ≠ t.2.2 → (Fama.stSt γF G σ Mk).cls z = none) ∧
      ((Src.IsSomeVine γF (Fama.stSt γF G σ Mk).G.molecule (survObjLow ht).atoms (survObjLow ht).upper (survObjLow ht).lower ∧
          ∃ hvc, (survObjLow ht).shape = Src.VineLikeObject.vc hvc) ∨
        (Src.AllowedCollectionObject γF (Fama.stSt γF G σ Mk).G (survObjLow ht) ∧ ∃ R, (survObjLow ht).shape = Src.VineLikeObject.hyper R ∧
          ¬ G.molecule.InGroup t.1 ((Fama.stSt γF G σ Mk).M.od R.added))) :=
  Classical.choose_spec (survivorsMk_imageMK'Low ht)

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

/-- The added bond of a 75-W1 survivor HV is not a bond of the survivor. -/
theorem survObj_hyper_addedLow {σ : Prescription G} {Mk : Set (Fama.CLVineG γF G)}
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ Fama.survivorsMk γF G σ Mk)
    {R : Src.HyperLikeRealization γF (Fama.stSt γF G σ Mk).G.molecule (survObjLow ht).atoms (survObjLow ht).upper (survObjLow ht).lower}
    (hR : (survObjLow ht).shape = Src.VineLikeObject.hyper R) :
    ¬ G.molecule.InGroup t.1 ((Fama.stSt γF G σ Mk).M.od R.added) := by
  obtain ⟨-, -, -, -, -, -, h⟩ := survObj_spec'Low ht
  rcases h with ⟨-, hvc, hs⟩ | ⟨-, R', hs, hn⟩
  · rw [hR] at hs; cases hs
  · rw [hR] at hs
    cases hs
    exact hn

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

theorem survObj_specLow {σ : Prescription G} {Mk : Set (Fama.CLVineG γF G)}
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ Fama.survivorsMk γF G σ Mk) :
    (survObjLow ht).atoms = t.1.image ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls) ∧
      (survObjLow ht).upper = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls t.2.1 ∧
      (survObjLow ht).lower = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls t.2.2 ∧
      Set.InjOn ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls) t.1 ∧
      (∀ c, (Fama.stSt γF G σ Mk).cls ((Fama.stSt γF G σ Mk).M.ob c) ≠ none → c ∈ (survObjLow ht).atoms →
        c = (survObjLow ht).upper ∨ c = (survObjLow ht).lower) ∧
      (∀ z ∈ t.1, z ≠ t.2.1 → z ≠ t.2.2 → (Fama.stSt γF G σ Mk).cls z = none) ∧
      ((Src.IsSomeVine γF (Fama.stSt γF G σ Mk).G.molecule (survObjLow ht).atoms (survObjLow ht).upper (survObjLow ht).lower ∧
          ∃ hvc, (survObjLow ht).shape = Src.VineLikeObject.vc hvc) ∨
        (Src.AllowedCollectionObject γF (Fama.stSt γF G σ Mk).G (survObjLow ht) ∧ ∃ R, (survObjLow ht).shape = Src.VineLikeObject.hyper R)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := survObj_spec'Low ht
  exact ⟨h1, h2, h3, h4, h5, h6, h7.imp id fun hh => ⟨hh.1, hh.2.imp fun _ hR => hR.1⟩⟩

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

theorem survObjs_lengthLow (G : Garden w) (σ : Prescription G) (Mk : Set (Fama.CLVineG γF G)) :
    (survObjsLow G σ Mk).length = (Fama.survivorsMk γF G σ Mk).length := by
  simp [survObjsLow]

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

/-- **No hinge is interior to a survivor.** -/
theorem survObj_not_interiorLow {σ : Prescription G} {Mk : Set (Fama.CLVineG γF G)}
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ Fama.survivorsMk γF G σ Mk)
    {v : GBranch (Fama.stSt γF G σ Mk).G.tree} (hv : v ∈ (Fama.stSt γF G σ Mk).hinges) : ¬ (survObjLow ht).IsInterior v := by
  rintro ⟨hva, hu, hl⟩
  obtain ⟨-, -, -, -, hj, -⟩ := survObj_specLow ht
  rcases hj v (((Fama.stSt γF G σ Mk).mem_hinges v).mp hv) hva with h | h
  · exact hu h
  · exact hl h

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

/-- **Survivors are disjoint from the Fama.VineA.NormalizedSplice.objects γF of `𝒞₁`** (o75 Theorem 7.5′(2)). -/
theorem objects_disjoint_survObjLow (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
    {O : Src.Object γF (Fama.stSt γF G σ Mk).G.molecule} (hO : O ∈ Fama.VineA.NormalizedSplice.objects γF G σ Mk)
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ Fama.survivorsMk γF G σ Mk) :
    Disjoint O.atoms (survObjLow ht).atoms := by
  obtain ⟨S', hS', hnm, hsub⟩ := mem_objects_groupLow hO
  obtain ⟨S, hS, -, hmk, -, htS⟩ := survivorsMk_groupLow ht
  obtain ⟨hat, -⟩ := survObj_specLow ht
  rw [Finset.disjoint_left]
  intro v hvO hvt
  rw [hat] at hvt
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hvt
  obtain ⟨z', hz', he⟩ := hsub _ hvO
  have hSS := group_eq_of_pi_eqLow hM σ hS hS' (htS hz) hz' he
  subst hSS
  exact hnm hmk

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
variable {S : Finset (GBranch G.tree)} (hS : S ∈ Fama.maximalGroupsG γF G.molecule) (hσ : σ S = Molecule.GapKind.SG)
  (h : Fama.markedGroup γF G Mk S) {D' : Type} [Fintype D'] [DecidableEq D'] {N : Molecule (GBranch G.tree) D'}
  {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)} {a b : GBranch G.tree}
  (hs : Fama.Spine γF N L S a b) (hvineM : ∀ t ∈ L, Src.IsSomeVine γF G.molecule t.1 t.2.1 t.2.2)
  (hingr : ∀ t ∈ L, Fama.IsIngredientG γF G.molecule S t.1)
  (hmemb : ∀ T, Fama.IsIngredientG γF G.molecule S T → ∃ p q, (T, p, q) ∈ L ∨ (T, q, p) ∈ L)
  (hsurvL : ∀ t ∈ L, (t ∈ (markedUnitsOfMKLow h).surv ↔ ¬ Fama.UnmMemMK γF G Mk t))
include hS hσ hs hvineM hingr hmemb hsurvL

/-- **A common image atom is a joint of the survivor.** -/
theorem common_jointLow {x y : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree}
    (hx : x ∈ (markedUnitsOfMKLow h).surv) (hxL : x ∈ L) (hyL : y ∈ L) (hxy : x ≠ y)
    {z z' : GBranch G.tree} (hz : z ∈ x.1) (hz' : z' ∈ y.1)
    (he : (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls z = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls z') :
    z = x.2.1 ∨ z = x.2.2 := by
  classical
  by_contra hzj
  push Not at hzj
  obtain ⟨-, -, -, -, -, -, hint, -⟩ := survivor_imageMKLow hS hσ h hx
  have hcz := hint z hz hzj.1 hzj.2
  by_cases hzz : z = z'
  · subst hzz
    obtain ⟨P0, Q0, hL⟩ := List.append_of_mem hxL
    rw [hL] at hyL hs
    rcases List.mem_append.mp hyL with hyP | hyQ
    · exact hzj.1 ((Famc.SpineG.joint_leftMK hs) hyP hz' hz)
    · rcases List.mem_cons.mp hyQ with hyx | hyQ
      · exact hxy hyx.symm
      · exact hzj.2 ((Famc.SpineG.joint_rightMK hs) hyQ hz' hz)
  · have hzS : z ∈ S := isIngredient_subsetLow (hingr x hxL) hz
    obtain ⟨u, hu, hzu, -⟩ := run_of_pi_eqLow hM σ hS h hzS hzz he
    have hub : u ∈ Fama.unitBlocks γF G σ Mk := (Fama.mem_unitBlocksMk (Mk := Mk)).mpr
      ⟨S, hS, hσ, by rw [groupUnitsMk_of_markedMKLow h]; exact hu⟩
    rw [Fama.stSt_cls_memMk hM σ Mk hub hzu] at hcz
    cases hcz

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

/-- A survivor of a group lies in the group. -/
theorem groupSurvMk_subLow {Mk : Set (Fama.CLVineG γF G)} {S : Finset (GBranch G.tree)}
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ Fama.groupSurvMk γF G Mk S) :
    t.1 ⊆ S ∧ t.2.1 ∈ t.1 := by
  have hm := marked_of_mem_groupSurvMkLow ht
  rw [groupSurvMk_eq_unitsLow hm] at ht
  obtain ⟨hX, hI, -⟩ := (markedUnitsOfMKLow hm).surv_spec t ht
  exact ⟨isIngredient_subsetLow hI, (Src.isBlock_of_isSomeVine hX).2.1⟩

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

theorem survivorsMk_nodupLow : (Fama.survivorsMk γF G σ Mk).Nodup := by
  rw [Fama.survivorsMk_eq, List.nodup_flatMap]
  refine ⟨fun S _ => groupSurvMk_nodupLow S, (sgGroups_nodupLow G σ).pairwise_of_forall_ne ?_⟩
  intro S hS S' hS' hne t ht ht'
  obtain ⟨hsub, hj⟩ := groupSurvMk_subLow ht
  obtain ⟨hsub', -⟩ := groupSurvMk_subLow ht'
  exact Finset.disjoint_left.mp (Fama.VineA.NormalizedSplice.groups_disjoint hM (Fama.mem_sgGroups.mp hS).1 (Fama.mem_sgGroups.mp hS').1 hne)
    (hsub hj) (hsub' hj)

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

theorem survObjs_getLow {σ : Prescription G} {Mk : Set (Fama.CLVineG γF G)} (i : Fin (survObjsLow G σ Mk).length) :
    ∃ (j : Fin (Fama.survivorsMk γF G σ Mk).length) (hj : (Fama.survivorsMk γF G σ Mk).get j ∈ Fama.survivorsMk γF G σ Mk),
      j.val = i.val ∧ (survObjsLow G σ Mk).get i = survObjLow hj := by
  refine ⟨⟨i.val, by simpa [survObjsLow] using i.2⟩, List.get_mem _ _, rfl, ?_⟩
  rw [List.get_eq_getElem]
  simp only [survObjsLow, List.getElem_map, List.getElem_attach, List.get_eq_getElem]

end

end WaveTurbulence.GammaLow.Flower
