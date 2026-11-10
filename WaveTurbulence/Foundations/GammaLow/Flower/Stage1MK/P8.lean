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
public import WaveTurbulence.Foundations.Stage1.Shared.ClassCountStmt
public import WaveTurbulence.Foundations.FinalCount.RedSpliceSkipMK
public import WaveTurbulence.Foundations.Flower.FinalMKDefs.PieceSel
public import WaveTurbulence.Foundations.Flower.MkDefs.Stage1MKFull
public import WaveTurbulence.Foundations.Flower.MkMark.MarkStepSel
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproEntryMK
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproContainedMK
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Zero
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Assembly
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedPiece
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescribedPoints
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.V0
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects

/-! # FLOWER-LOW (packet L8), item I (wave 8): marked skips, the selected piece data and the zero/assembly layer of
the marked Stage-1′ gate over `𝒱_γ`

Main's `FinalCount.RedSpliceSkipMK`, `Flower.{FinalMKDefs.PieceSel, MkDefs.Stage1MKFull, MkMark.MarkStepSel,
Stage1MKGate.Zero, Stage1MKGate.Assembly}`, `Stage1.Geometry.Subpro{Entry,Contained}MK` declarations on item I's path,
copied by source (sha256 in COPIED-SHA256SUMS) by `tools/itool/gen_i_spec.py`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false

namespace WaveTurbulence.GammaLow.Flower

section
open WaveTurbulence.ClassCount
open WaveTurbulence.Induct
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RedSplice WaveTurbulence.Reg.Skeleton
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]

/-- B1b-2: an admissibility predicate for marked vine sets (`Adm LG S Mk`: `Mk` may be used on the skeleton `S` of
the layered garden `LG`). `fun _ _ Mk => Mk = ∅` is main's Stage 1; the world chooses the markings of Stage 1′. -/
abbrev MarkAdmLow := ∀ {R : ℕ} (_LG : LayeredGarden (2 * R)) (S : Garden (2 * R)), Set (Fama.CLVineG γF S) → Prop

end

section
open WaveTurbulence.ClassCount
open WaveTurbulence.Induct
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RedSplice WaveTurbulence.Reg.Skeleton
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]

/-- B1b-2: `LG` carries a Stage 1′ piece (`Fama.stage1PieceOf γF … σ Mk`, runs spliced at the admissible marked set `Mk`) with
data `(ḡ, ρ̄) = (g, r)`. -/
def HasPieceDataMkLow (Adm : MarkAdmLow (γF := γF)) (d : ℕ) {R : ℕ} (LG : LayeredGarden (2 * R)) (g r : ℕ) : Prop :=
  ∃ (S : Garden (2 * R)) (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS LG.garden)
    (σ : Prescription S) (Mk : Set (Fama.CLVineG γF S)), Adm LG S Mk ∧
    (Fama.stage1PieceOf γF d hS LG hd σ Mk).gbar = g ∧ (Fama.stage1PieceOf γF d hS LG hd σ Mk).rbar = r

end

section
open WaveTurbulence.ClassCount
open WaveTurbulence.Induct
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RedSplice WaveTurbulence.Reg.Skeleton
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkMark
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}
variable {S : Garden w} (hS : S.IsPlain) (Z : Fama.TwistGroupSite γF S) (D : ReconstructionData S)
  (X : RegChain) (Q : RegCpl) (hX : X.wf = true) (hQ : Q.wf = true)

/-- Marked branches for `Π` correspond along one LF step, for any branch map compatible with the near relation. -/
theorem markedBranchILow (ε : Bool) {LG LG' : LayeredGarden w} (hd : D.Decodes hS LG.garden)
    (hd' : (lfReconstructionChoice S Z.P hS D ε X Q hX hQ).Decodes (chosenSkeleton_plain S Z.P hS ε) LG'.garden)
    {J : Finset (Fin w)} {pat : Fin w → FixPat} (t s : ℝ) (kSel : Fin w → Option ℕ)
    (hn : ∀ a ∈ protI LG J pat t s kSel, a.1 ∉ nearRegion S D.tree Z.P.lower)
    (hs : StemAvoid LG J (ownedBy S D.tree (replacedNodes Z.P)))
    (νB : GBranch S.tree → GBranch (chosenSkeleton S Z.P ε).tree)
    (hnear : ∀ o, o ∉ replacedNodes Z.P → ∀ b, NearRel S o b ↔ NearRel (chosenSkeleton S Z.P ε)
      ((lfCoord hS Z.P D X Q hX hQ (pair_retained_tree' Z.P Z.hB Z.hCL Z.hP) ε).ν o) (νB b))
    (b : GBranch S.tree) :
    MarkedBranch S D.tree (protI LG J pat t s kSel) b ↔
      MarkedBranch (chosenSkeleton S Z.P ε) (lfReconstructionChoice S Z.P hS D ε X Q hX hQ).tree
        (protI LG' J pat t s kSel) (νB b) := by
  have hsame := pair_retained_tree' Z.P Z.hB Z.hCL Z.hP
  set C := lfCoord hS Z.P D X Q hX hQ hsame ε
  have hp1 : ∀ z ∈ ownedBy S D.tree C.Rsk, ¬ ProtG LG (SeedSel LG J pat kSel) z := by
    rw [lfCoord_rsk]
    exact noProtSel_of_near Z.P D t s kSel hn
  have hs1 : StemAvoid LG J (ownedBy S D.tree C.Rsk) := by
    rw [lfCoord_rsk]
    exact hs
  obtain ⟨hp', hiff⟩ := C.step_protSel (lfPair hS Z.P D X Q hX hQ hsame ε) hd hd' kSel
    (lfCoord_root hS Z.P D X Q hX hQ hsame ε) (lfCoord_pairR hS Z.P D X Q hX hQ hsame ε)
    (lfCoord_root' hS Z.P D X Q hX hQ hsame ε) (lfCoord_pairR' hS Z.P D X Q hX hQ hsame ε) hp1 hs1
  exact C.markedBranch_transport_gen hd hd' (mem_protI_iff pat t s kSel) (mem_protI_iff pat t s kSel) νB
    (fun o ho => hnear o (by rw [lfCoord_rsk] at ho; exact ho)) hp1 hp' hiff b

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkMark
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}
variable {S : Garden w} (hS : S.IsPlain) (Z : Fama.TwistGroupSite γF S) (D : ReconstructionData S)
  (X : RegChain) (Q : RegCpl) (hX : X.wf = true) (hQ : Q.wf = true)

/-- **One LF step transports the fine marking** (either choice), at a member unmarked for `Π` whose replaced region
the capped stems avoid. -/
theorem mark_stepILow (ε : Bool) {LG LG' : LayeredGarden w} (hd : D.Decodes hS LG.garden)
    (hd' : (lfReconstructionChoice S Z.P hS D ε X Q hX hQ).Decodes (chosenSkeleton_plain S Z.P hS ε) LG'.garden)
    {J : Finset (Fin w)} {pat : Fin w → FixPat} (t s : ℝ) (kSel : Fin w → Option ℕ)
    (hn : ∀ a ∈ protI LG J pat t s kSel, a.1 ∉ nearRegion S D.tree Z.P.lower)
    (hs : StemAvoid LG J (ownedBy S D.tree (replacedNodes Z.P))) :
    Fama.Stage1Mk.MarkTransported γF (VineA.chosenMolIso S Z.P ε) (markedVinesRawLow (γF := γF) S D.tree (protI LG J pat t s kSel))
      (markedVinesRawLow (γF := γF) (chosenSkeleton S Z.P ε) (lfReconstructionChoice S Z.P hS D ε X Q hX hQ).tree
        (protI LG' J pat t s kSel)) := by
  have hsame := pair_retained_tree' Z.P Z.hB Z.hCL Z.hP
  cases ε with
  | false =>
    have hMB := markedBranchILow hS Z D X Q hX hQ false hd hd' t s kSel hn hs id (fun o _ b => Iff.rfl)
    intro c c' hc'
    have hcc : c' = c := by
      apply Fama.VineA.clVine_eq_of_atoms
      rw [hc']
      exact Finset.image_id
    subst hcc
    exact ⟨fun ⟨hv, b, hb, hbu, hm⟩ => ⟨hv, b, hb, hbu, (hMB b).mp hm⟩,
      fun ⟨hv, b, hb, hbu, hm⟩ => ⟨hv, b, hb, hbu, (hMB b).mpr hm⟩⟩
  | true =>
    have hMB := markedBranchILow hS Z D X Q hX hQ true hd hd' t s kSel hn hs (coreBranchEquiv S Z.P)
      (fun o ho b => twist_nearRel hS Z.P D X Q hX hQ hsame o ho b)
    intro c c' hc'
    rw [mem_markedVinesRawLow, mem_markedVinesRawLow]
    constructor
    · rintro ⟨hv, b, hb, hbu, hm⟩
      obtain ⟨c'', hc''V, hc''a, hc''u, -⟩ := Z.vinesV_image hv
      have e : c'' = c' := Fama.VineA.clVine_eq_of_atoms (hc''a.trans hc'.symm)
      subst e
      refine ⟨hc''V, coreBranchEquiv S Z.P b, ?_, ?_, (hMB b).mp hm⟩
      · rw [hc''a]
        exact (VineA.chosenMolIso S Z.P true).mem_img _ b |>.mpr hb
      · rw [hc''u]
        exact fun h => hbu ((coreBranchEquiv S Z.P).injective h)
    · rintro ⟨hv', b', hb', hbu', hm'⟩
      obtain ⟨c₀, hc₀V, hc₀a, hc₀u, -⟩ := Z.vinesV_preimage hv'
      have hae : c₀.atoms = c.atoms := (VineA.chosenMolIso S Z.P true).img_injective (hc₀a.trans hc')
      have e : c₀ = c := Fama.VineA.clVine_eq_of_atoms hae
      subst e
      set b := (coreBranchEquiv S Z.P).symm b'
      have hbb : coreBranchEquiv S Z.P b = b' := Equiv.apply_symm_apply _ _
      refine ⟨hc₀V, b, ?_, ?_, ?_⟩
      · apply ((VineA.chosenMolIso S Z.P true).mem_img c₀.atoms b).mp
        have h1 : (VineA.chosenMolIso S Z.P true).img c₀.atoms = c'.atoms := hc₀a
        have h2 : (VineA.chosenMolIso S Z.P true).e b = b' := hbb
        rw [h1, h2]
        exact hb'
      · intro h
        apply hbu'
        rw [← hbb, h, hc₀u]
      · rw [hMB b, hbb]
        exact hm'

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.VineA.NormalizedSplice.Subpro
open WaveTurbulence.Induct
open WaveTurbulence.Subpro WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {R : ℕ} {G : Garden (2 * R)}

theorem left_trivialMkLow (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ Fama.maximalGroupsG γF G.molecule) (hσ : σ S = Molecule.GapKind.SG) {Mk : Set (Fama.CLVineG γF G)}
    (hmkS : ¬ Fama.markedGroup γF G Mk S)
    (sk : Fama.SkipData γF G S) (hsk : (Fama.groupUnitsOf γF G S).skip = some sk)
    (hnh : (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls sk.a ∉ (Fama.stSt γF G σ Mk).hinges) : sk.x = sk.a := by
  rcases sk.left with ⟨-, hx⟩ | ⟨-, haL, -, -⟩
  · exact hx
  · exfalso
    apply hnh
    rcases ((Fama.groupUnitsOf γF G S).skip_units sk hsk).2.1 with h0 | ⟨u, hu, hL⟩
    · rw [h0] at haL; cases haL
    · have hau : sk.a ∈ u.atoms := hL ▸ haL
      have huB : u ∈ Fama.unitBlocks γF G σ Mk :=
        Fama.mem_unitBlocksMk.mpr ⟨S, hSm, hσ, (Fama.groupUnitsMk_of_not_marked hmkS).symm ▸ hu⟩
      rw [(Fama.stSt γF G σ Mk).mem_hinges, (Fama.stSt γF G σ Mk).M.ob_pi, Fama.stSt_repC_memMk (Mk := Mk) hM σ huB hau,
        Fama.stSt_cls_memMk (Mk := Mk) hM σ huB u.isBlock.2.1]
      simp

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.VineA.NormalizedSplice.Subpro
open WaveTurbulence.Induct
open WaveTurbulence.Subpro WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {R : ℕ} {G : Garden (2 * R)}

/-- **R173**: if every marked vine lies in `𝒱₀` (an SG group), every marked group is SG. -/
theorem sg_of_markedGroupLow {σ : Prescription G} {Mk : Set (Fama.CLVineG γF G)} (hMkSG : Mk ⊆ Fama.vinesV0 γF G σ)
    {S : Finset (GBranch G.tree)} (hS : S ∈ Fama.maximalGroupsG γF G.molecule) (hmk : Fama.markedGroup γF G Mk S) :
    σ S = Molecule.GapKind.SG := by
  obtain ⟨c, hc, -, hI⟩ := hmk
  obtain ⟨-, S', hS', hI', hσ', -⟩ := hMkSG hc
  have hM : G.molecule.IsMolecule := WaveTurbulence.Mole.garden_isMolecule G
  obtain ⟨z, hz⟩ : c.atoms.Nonempty := by
    rcases hI with ⟨_, _, _, _, _, _, hCI⟩ | ⟨_, _, _, _, _, _, _, _, _, hCI⟩
    · have hX := (Fama.chainIngredientG_spec hCI).2.1
      exact ⟨_, (Src.isBlock_of_isSomeVine hX).2.1⟩
    · have hX := (Fama.chainIngredientG_spec hCI).2.1
      exact ⟨_, (Src.isBlock_of_isSomeVine hX).2.1⟩
  by_cases hSS : S = S'
  · rw [hSS]; exact hσ'
  · exact absurd (isIngredient_subsetLow hI' hz)
      (Finset.disjoint_left.mp (Fama.VineA.NormalizedSplice.groups_disjoint hM hS hS' hSS) (isIngredient_subsetLow hI hz))

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents
open WaveTurbulence.RedSplice (Prescription stSt vinesV0)
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]

/-- The mass bound's prefactor is nonnegative. -/
theorem massBound_nonnegLow {P : WTParams} [Fact (P.γ ≤ 1 / 2)] {R : ℕ} (π : Stage1PieceMKG P R) (n : ℕ) (cP x s : ℝ)
    (hC : 0 ≤ P.C₁) (hL : 0 ≤ P.L) (hs : 0 ≤ s) :
    0 ≤ (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
      P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ)) *
      P.L ^ (cP * P.d * (π.nProt : ℝ)) * P.L ^ x * s := by
  have h1 := pow_nonneg (mul_nonneg hC (Real.sqrt_nonneg P.δ)) (n - π.Gsb.order)
  have h2 := pow_nonneg hC (π.Gsb.order + 2 * R)
  have h3 := Real.rpow_nonneg hL (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) +
    P.η ^ 7 * (π.Cs.hinges.card : ℝ))
  have h4 := Real.rpow_nonneg hL (cP * P.d * (π.nProt : ℝ))
  have h5 := Real.rpow_nonneg hL x
  positivity

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents
open WaveTurbulence.RedSplice (Prescription stSt vinesV0)
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]

/-- **The value `0` is represented** (an empty superposition), for every piece, selection and mass. -/
theorem representsIntMKSel_zeroLow {P : WTParams} [Fact (P.γ ≤ 1 / 2)] {R : ℕ} (π : Stage1PieceMKG P R)
    (sel : Finset (GBranch π.Gsb.tree)) (n : ℕ) (cP : ℝ) (tt : Fin (2 * R) → ℝ) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (s : ℝ) (hC : 0 ≤ P.C₁) (hL : 0 ≤ P.L) (hs : 0 ≤ s) :
    RepresentsIntMKSelG π sel n cP tt base roots s 0 := by
  refine ⟨Empty, ⊤, 0, fun e => e.elim, fun e => e.elim, fun e => e.elim, fun e => e.elim, fun e => e.elim,
    integrable_zero_measure, by simp, integrable_zero_measure, ?_, fun e => e.elim⟩
  rw [integral_zero_measure]
  exact massBound_nonnegLow π n cP _ s hC hL hs

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents
open WaveTurbulence.RedSplice (Prescription stSt vinesV0)
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]

theorem representsIntMK_zeroLow {P : WTParams} [Fact (P.γ ≤ 1 / 2)] {R : ℕ} (π : Stage1PieceMKG P R) (n : ℕ) (cP : ℝ)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (s : ℝ)
    (hC : 0 ≤ P.C₁) (hL : 0 ≤ P.L) (hs : 0 ≤ s) : π.RepresentsIntMK n cP tt base roots s 0 :=
  (representsIntMKSel_emptyG π n cP tt base roots s 0).mp (representsIntMKSel_zeroLow π ∅ n cP tt base roots s hC hL hs)

end

end WaveTurbulence.GammaLow.Flower
