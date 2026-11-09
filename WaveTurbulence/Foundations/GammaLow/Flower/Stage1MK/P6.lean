/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Defs
public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Gates
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Inputs
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P1
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P2
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P3
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P4
public import WaveTurbulence.Foundations.Flower.MkSubpro.Piece
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Hyp
public import WaveTurbulence.Foundations.Flower.ProtGeo.Vine
public import WaveTurbulence.Foundations.Flower.Stage1WVine.WAssembly
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Marking
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.SurvCount
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Pieces
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Gate
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Prefix
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Unclean
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepPr2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvMap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkFn
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkedClasses
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescribedPoints
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.V0
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainAssembly
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects

/-! # FLOWER-LOW (packet L8), item I (wave 6): the marked Stage-1′ gate layer over `𝒱_γ`

Main's `Flower.Stage1MKGate.*`, `Flower.MkSubpro.*`, `Flower.ProtGeo.*`, `Flower.Stage1WVine.*` and the remaining
base declarations (`WaveTurbulenceVineParam.VineParamFinal`, …) on item I's path that build on published inputs,
copied by source (sha256 in COPIED-SHA256SUMS) by `tools/itool/gen_i_spec.py`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false

namespace WaveTurbulence.GammaLow.Flower

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkSubpro
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Finset WaveTurbulence.Reg.Skeleton
open WaveTurbulence.RedSplice (Prescription stSt vinesV0)
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]

/-- The fields of `SoundMKG`/`SoundMKFullG` that are not geometric (copied from them verbatim): the survivor and
protected counts (B4) and the pin, filter and indicator facts (B3s/B4). -/
structure MkPieceRestLow {P : WTParams} [Fact (P.γ ≤ 1 / 2)] {R : ℕ} (π : Stage1PieceMKG P R) (cθ : ℝ) : Prop where
  survivors_card : π.surv.m ≤ 6 * π.nProt
  prot_card : π.surv.prot.card ≤ 2 * π.nProt
  fix_prot : ∀ b, (π.fix b).isSome → b ∈ π.surv.prot
  fix_layer : ∀ b t, π.fix b = some t → (π.layer b : ℝ) ≤ t ∧ t ≤ π.layer b + 1
  filt_ok : ∀ a q, π.filt a = some q → a ∉ π.Cs.hinges ∧ 1 ≤ q.1 ∧ (∀ u, ‖q.2 u‖ ≤ 1) ∧ filterB ⇑q.2 ≤ cθ
  ind_ok : ∀ k, 0 ≤ π.ind k ∧ π.ind k ≤ 1
  ind_local : ∀ k k', (∀ a ∈ π.surv.joints ∪ π.surv.prot, ∀ i : Fin 3,
    k (a.child i) = k' (a.child i) ∧ k a.toNode = k' a.toNode) → π.ind k = π.ind k'
  lb_free : ∀ b, (π.lb b).isSome → π.fix b = none
  lb_prot : ∀ b, (π.lb b).isSome → b ∈ π.surv.prot
  lb_layer : ∀ b x, π.lb b = some x → (π.layer b : ℝ) ≤ x ∧ x ≤ π.layer b + 1

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
variable {w : ℕ}

/-- **The marked set of the piece of a prescribed point** (ruling R173 at the piece): the fine marking restricted to
the selected collection `𝒱₀(σ)` of the point. -/
def classMkLow (mkF : Fama.Stage1Mk.MarkFn γF w) (a : Fama.VineA.PrescribedPrimeGarden γF w) : Set (Fama.CLVineG γF a.prime.skeleton) :=
  mkF a.prime ∩ Fama.vinesV0 γF a.prime.skeleton a.totalSigma

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
variable {w : ℕ}

/-- R173 instance: the marked set of a class piece lies in `𝒱₀(σ)`. -/
theorem classMk_sub_vinesV0Low (mkF : Fama.Stage1Mk.MarkFn γF w) (a : Fama.VineA.PrescribedPrimeGarden γF w) :
    classMkLow mkF a ⊆ Fama.vinesV0 γF a.prime.skeleton a.totalSigma :=
  Set.inter_subset_right

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
variable {w : ℕ}

/-- A stem-clean prescribed point: the capped stems avoid the active set of every vine of `𝒱₀(σ)`. -/
def CleanPtLow (J : Finset (Fin w)) (a : Fama.VineA.PrescribedPrimeGarden γF w) : Prop :=
  ∀ c ∈ Fama.vinesV0 γF a.prime.skeleton a.totalSigma, MkMark.StemCleanAt J a.prime c.atoms c.upper

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
variable {w : ℕ}

/-- **The fine marking of Stage 1′** (F-B4-4 (b)), characterized: it contains `markILow` (`Π`-marked vines); for a
stem-dependent weight it contains every stem-unclean vine of `𝒱`; it contains nothing else; and every fine′ batch
from every prescribed point carries it. -/
structure FineMarkingLow (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (kSel σ : Fin w → Option ℕ)
    (mkF : Fama.Stage1Mk.MarkFn γF w) : Prop where
  sub : ∀ {LG : LayeredGarden w} (B : PrimeData LG), markILow J pat t s kSel B ⊆ mkF B
  stem : StemDep σ kSel → ∀ {LG : LayeredGarden w} (B : PrimeData LG), ∀ c ∈ Fama.vinesVG γF B.skeleton,
    ¬ MkMark.StemCleanAt J B c.atoms c.upper → c ∈ mkF B
  le : ∀ {LG : LayeredGarden w} (B : PrimeData LG), ∀ c ∈ mkF B, c ∈ markILow J pat t s kSel B ∨
    (StemDep σ kSel ∧ c ∈ Fama.vinesVG γF B.skeleton ∧ ¬ MkMark.StemCleanAt J B c.atoms c.upper)
  fine : ∀ a : Fama.VineA.PrescribedPrimeGarden γF w, a.FineTransportedAt γF mkF

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
variable {w : ℕ}

/-- **The value of a fine′ class**: the `kernelKgenSel` sum (coset base `0`) over the coarse′ class (`markI0Low`) of the
class, restricted to the decorations selected by the class (`Fama.Represents.selPMk P.γ` at the fine marking). -/
def classValueLow (P : WTParams) [Fact (P.γ ≤ 1 / 2)] {R : ℕ} (p : ℕ) (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat)
    (kSel : Fin (2 * R) → Option ℕ) (t s : ℝ) (A : Finset (LayeredGarden (2 * R)))
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ)
    (Rf : Fin (2 * R) → Option ℝ) (σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ)
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (mkF : Fama.Stage1Mk.MarkFn P.γ (2 * R))
    (π : Fama.Represents.PcA P.γ R p (objKind (2 * R)) A mkF) : ℂ :=
  ∑ LG ∈ Fama.Represents.membersP P.γ (Fama.Represents.clsPMk P.γ (markI0Low J pat t s) π),
    kernelKgenSel P.L P.γ P.δ LG (fixCap LG J pat t s) (offCap LG J dag.isSome)
      (markedWt P J p kSel h Rf σ Rs dag LG) (fun _ => t) 0 roots
      (Fama.Represents.selPMk P.γ p (objKind (2 * R)) A P 0 roots mkF π LG)

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
variable {w : ℕ}

/-- The fields of `MkPieceRest` that B3s supplies (all except `survivors_card`, which is B4's), verbatim. -/
structure PieceRestB3sLow {P : WTParams} [Fact (P.γ ≤ 1 / 2)] {R : ℕ} (π : Stage1PieceMKG P R) (cθ : ℝ) : Prop where
  prot_card : π.surv.prot.card ≤ 2 * π.nProt
  fix_prot : ∀ b, (π.fix b).isSome → b ∈ π.surv.prot
  fix_layer : ∀ b t, π.fix b = some t → (π.layer b : ℝ) ≤ t ∧ t ≤ π.layer b + 1
  filt_ok : ∀ a q, π.filt a = some q → a ∉ π.Cs.hinges ∧ 1 ≤ q.1 ∧ (∀ u, ‖q.2 u‖ ≤ 1) ∧ filterB ⇑q.2 ≤ cθ
  ind_ok : ∀ k, 0 ≤ π.ind k ∧ π.ind k ≤ 1
  ind_local : ∀ k k', (∀ a ∈ π.surv.joints ∪ π.surv.prot, ∀ i : Fin 3,
    k (a.child i) = k' (a.child i) ∧ k a.toNode = k' a.toNode) → π.ind k = π.ind k'
  /-- Ruling R187: the lower-bounded atoms are free, protected, and bounded inside their layer window. -/
  lb_free : ∀ b, (π.lb b).isSome → π.fix b = none
  lb_prot : ∀ b, (π.lb b).isSome → b ∈ π.surv.prot
  lb_layer : ∀ b x, π.lb b = some x → (π.layer b : ℝ) ≤ x ∧ x ≤ π.layer b + 1

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
variable {w : ℕ}

/-- **What B3s provides for one class piece**: `RepresentsIntMKSelG` of the class value at the mass `selMassMK`
(residual selected vertices `selR`), the six non-survivor `MkPieceRest` fields, and the residual-selection facts of
`Stage1ReductionAtMKFullG`. -/
structure ClassPieceOKLow {P : WTParams} [Fact (P.γ ≤ 1 / 2)] {R : ℕ} (π : Stage1PieceMKG P R) (selR : Finset (GBranch π.Gsb.tree))
    (N : ℕ) (cP cθ t b : ℝ) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (kSel : Fin (2 * R) → Option ℕ)
    (Rs : Fin (2 * R) → ℝ) (val : ℂ) : Prop where
  rep : RepresentsIntMKSelG π selR N cP (fun _ => t) 0 roots (selMassMK N b Rs kSel (selR.image fun v => v.1.1)) val
  rest : PieceRestB3sLow π cθ
  sel_spec : ∀ v ∈ selR, (kSel v.1.1).isSome ∧ π.fix v = none ∧
    ∃ ψ : SchwartzMap ℝ ℂ, π.filt v = some (Rs v.1.1, ψ) ∧ ∀ u, ψ u = (chiDN u : ℂ)
  sel_inj : ∀ v ∈ selR, ∀ v' ∈ selR, v.1.1 = v'.1.1 → v = v'
  sel_card : selR.card ≤ π.nProt
  /-- For the frozen form `MkDefs.Stage1ReductionAtMK` only: plain `RepresentsIntMK` at `cP + 343` and mass `b^N`.
  (It follows from `rep` when the weight `w` of the representation is measurable: `∏ (1+|ξ_v|)^{1/18} ≥ 1`,
  `selMassMK ≤ b^N`, `L^{7(47d+2)·#selR} ≤ L^{343·d·nProt}` for `d ≥ 1`; `RepresentsIntMKSelG` alone does not give the
  integrability of `‖w‖`.) -/
  repMK : π.RepresentsIntMK N (cP + 343) (fun _ => t) 0 roots (b ^ N) val
  /-- Ruling R187 (LB-RESTORE-2): no residual selected vertex carries a lower bound (lower bounds sit on `dParent`
  trees; selected trees are plain). -/
  sel_lb : ∀ v ∈ selR, π.lb v = none

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.ProtGeo
open scoped Classical
open WaveTurbulence TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.Flower.MkDefs WaveTurbulence.Reg.Skeleton
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}
variable {LG : LayeredGarden w} {J : Finset (Fin w)}

/-- **The upper joint of a (CL) vine has a child toward the vine**: a branching child that is a non-upper atom, or a
leaf child whose partner's parent is a non-upper atom (block axioms: connectedness, parent outside). -/
theorem upper_internal_childLow {S : Garden w} (c : Fama.CLVineG γF S) :
    ∃ (i : Fin 3) (b : GBranch S.tree), b ∈ c.atoms ∧ b ≠ c.upper ∧
      (b.toNode = c.upper.child i ∨ ∃ ℓ : GLeaf S.tree, ℓ.toNode = c.upper.child i ∧ b.IsParentOf (S.pair ℓ)) := by
  have hV := c.isVine
  have hB := (Src.isBlock_of_isSomeVine hV)
  have hup : c.upper ∈ c.atoms := hB.2.1
  have hlow : c.lower ∈ c.atoms := hB.2.2.1
  have hne : c.upper ≠ c.lower := hB.2.2.2.1
  have hconn := hB.2.2.2.2.2.2.2.2.2 c.upper hup c.lower hlow
  have hx : ∃ x, S.molecule.InGroup c.atoms x ∧ S.molecule.atom x = c.upper ∧
      S.molecule.atom (S.molecule.mate x) ≠ c.upper := by
    by_contra hno
    push Not at hno
    have key : ∀ a b, Relation.EqvGen (fun a b => ∃ x, S.molecule.InGroup c.atoms x ∧ S.molecule.atom x = a ∧
        S.molecule.atom (S.molecule.mate x) = b) a b → (a = c.upper ↔ b = c.upper) := by
      intro a b hab
      induction hab with
      | rel a b hr =>
        obtain ⟨x, hxg, hxa, hxb⟩ := hr
        constructor
        · intro ha; rw [← hxb]; exact hno x hxg (hxa.trans ha)
        · intro hb
          have hyg : S.molecule.InGroup c.atoms (S.molecule.mate x) := by
            refine ⟨hxg.2, ?_⟩; rw [S.molecule.mate_mate]; exact hxg.1
          have := hno _ hyg (hxb.trans hb)
          rw [S.molecule.mate_mate] at this
          rw [← hxa]; exact this
      | refl => exact Iff.rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
    exact hne ((key _ _ hconn).mp rfl).symm
  obtain ⟨x, hxg, hxa, hxb⟩ := hx
  have hbS := hxg.2
  rcases x with ⟨⟨c', hc'⟩, bb⟩ | ⟨ℓ, hm, hl1, hl2⟩
  · cases bb with
    | false =>
      -- the dart at the child end: its partner is the parent of the upper joint, inside the vine
      exfalso
      apply c.notParentUpper
      change c' = c.upper at hxa
      subst hxa
      exact ⟨hc', hbS⟩
    | true =>
      change GNode.parent c'.toNode hc' = c.upper at hxa
      refine ⟨c'.1.2.getLast hc', c', hbS, hxb, Or.inl ?_⟩
      exact node_eq_child_of_parent (c := c'.toNode) hc' hxa
  · change GNode.parent ℓ.toNode hl1 = c.upper at hxa
    refine ⟨ℓ.1.2.getLast hl1, GNode.parent (S.pair ℓ).toNode hl2, hbS, hxb, Or.inr ⟨ℓ, ?_, ?_⟩⟩
    · exact node_eq_child_of_parent (c := ℓ.toNode) hl1 hxa
    · exact ⟨rfl, (S.pair ℓ).1.2.getLast hl2, (List.dropLast_append_getLast hl2).symm⟩

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1WVine
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA WaveTurbulence.VineEstS4 WaveTurbulence.VineC WaveTurbulence.LFTwist WaveTurbulence.VineAlign WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.PL2330 WaveTurbulence.VineEstS5C VineParamContract WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.Represents WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W
open scoped ENNReal Classical
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]

/-- The VINEEST mass of a unit with its weight power (without the top filter mass). -/
def unitMassCLow (P : WTParams) [Fact (P.γ ≤ 1 / 2)] {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {R : CLRegionData G U a b} {n : ℕ} (hM9 : Famb.NormalChartSupply P.γ) (B : Famb.VineEstS2.CLChainAssemblyΓ P.γ G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (cψ B₀ : ℝ) : ℝ :=
  cψ ^ (9 * U.card + 4 * clLocalOrder2 RD hG R) * unitMassLow P hM9 B RD hG layer hLayer B₀

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical
open WaveTurbulence WaveTurbulence.Stage1 WaveTurbulence.RedSplice Finset
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}

/-- A vine has at least two atoms. -/
theorem two_le_card_of_isSomeVineLow {G : Garden w} {T : Finset (GBranch G.tree)} {p q : GBranch G.tree}
    (h : Src.IsSomeVine γF G.molecule T p q) : 2 ≤ T.card := by
  have hX := h
  have hB := (Src.isBlock_of_isSomeVine hX)
  exact Finset.one_lt_card.2 ⟨p, hB.2.1, q, hB.2.2.1, hB.2.2.2.1⟩

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical
open WaveTurbulence WaveTurbulence.Stage1 WaveTurbulence.RedSplice Finset
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}

/-- The marked `𝒱`-ingredients of a group. -/
def mkIngrLow (G : Garden w) (Mk : Set (Fama.CLVineG γF G)) (S : Finset (GBranch G.tree)) : Finset (Fama.CLVineG γF G) :=
  (Set.toFinite Mk).toFinset.filter fun c => c ∈ Fama.vinesVG γF G ∧ Fama.IsIngredientG γF G.molecule S c.atoms

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

/-- Survivors of a marked group are pairwise distinct in their atom sets (as list entries). -/
theorem surv_pairwise_fstLow (U : Fama.MarkedGroupUnits γF G S Mk) : U.surv.Pairwise (fun t t' => t.1 ≠ t'.1) := by
  refine List.Pairwise.imp_of_mem ?_ U.surv_meet
  intro a b ha _ hab he
  have h2 := two_le_card_of_isSomeVineLow (U.surv_spec a ha).1
  rw [he, Finset.inter_self] at hab
  rw [he] at h2
  omega

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

theorem surv_fst_nodupLow (U : Fama.MarkedGroupUnits γF G S Mk) : (U.surv.map Prod.fst).Nodup :=
  List.pairwise_map.2 (surv_pairwise_fstLow U)

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

theorem surv_nodupLow (U : Fama.MarkedGroupUnits γF G S Mk) : U.surv.Nodup :=
  (surv_pairwise_fstLow U).imp fun h he => h (congrArg Prod.fst he)

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

/-- Distinct survivors of a marked group have distinct atom sets. -/
theorem surv_fst_neLow (U : Fama.MarkedGroupUnits γF G S Mk) {t t' : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree}
    (ht : t ∈ U.surv) (ht' : t' ∈ U.surv) (hne : t ≠ t') : t.1 ≠ t'.1 :=
  fun he => hne (List.inj_on_of_nodup_map (surv_fst_nodupLow U) ht ht' he)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical
open WaveTurbulence WaveTurbulence.Stage1 WaveTurbulence.RedSplice Finset
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}

/-- The marked `𝒱`-ingredients of distinct maximal groups are disjoint. -/
theorem mkIngr_disjointLow {G : Garden w} (Mk : Set (Fama.CLVineG γF G)) {S S' : Finset (GBranch G.tree)}
    (hS : S ∈ Fama.maximalGroupsG γF G.molecule) (hS' : S' ∈ Fama.maximalGroupsG γF G.molecule) (hne : S ≠ S') :
    Disjoint (mkIngrLow G Mk S) (mkIngrLow G Mk S') := by
  rw [Finset.disjoint_left]
  intro c h h'
  simp only [mkIngrLow, Finset.mem_filter] at h h'
  have hd := Fama.maximalGroups_disjoint (Mole.garden_isMolecule G) hS hS' hne
  exact Finset.disjoint_left.1 hd (Fama.ing_subset h.2.2 c.upper_mem) (Fama.ing_subset h'.2.2 c.upper_mem)

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
variable {w : ℕ}

/-- **The fine′ marking of Stage 1′.** -/
def fineMkLow (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (kSel σ : Fin w → Option ℕ) :
    Fama.Stage1Mk.MarkFn γF w :=
  fun {_} B => if StemDep σ kSel then markIXLow J pat t s kSel B else markILow J pat t s kSel B

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
variable {w : ℕ}

/-- **Zero classes vanish**: under the gate's hypotheses, the class value of a fine′ class (at `fineMkLow`) of a
stem-dependent weight that contains a stem-unclean point is `0` (FL-SEP). -/
def ZeroVanishLow (P : WTParams) [Fact (P.γ ≤ 1 / 2)] : Prop :=
  ∀ p, p < P.D → ∀ R, 1 ≤ R → R ≤ 10 * P.R (p + 1) → ∀ N, 1 ≤ N → N ≤ P.N (p + 1) ^ 4 →
  ∀ (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (kSel : Fin (2 * R) → Option ℕ),
  ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t,
  ∀ A : Finset (LayeredGarden (2 * R)),
    (∀ LG ∈ A, MkCarries P p N LG ∧ (∀ h : 2 * R = 2, ¬ IsRegularCouple (h ▸ LG.garden : Garden 2)) ∧
      LG.garden.Irreducible ∧ (∀ j ∈ J, LG.garden.tree j = TTree.leaf) ∧ CapGeo LG J p ∧ CapPatValid LG J pat p) →
  ∀ (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ) (Rf : Fin (2 * R) → Option ℝ)
    (σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)),
    (∀ j r, Rf j = some r → P.L / 2 ≤ r) →
    (((∃ i, σ i ≠ none) ∨ ∃ i, kSel i ≠ none) → ∀ j, j ∉ J → ∃ r, Rf j = some r ∧
      (∀ j' x, ‖x‖ ≥ r → h p j j' x = 0 ∧ h p j' j x = 0) ∧ r ^ 10 ≤ ‖latticePoint P.L (roots j)‖) →
  ∀ π : Fama.Represents.PcA P.γ R p (objKind (2 * R)) A (fineMkLow J pat t s kSel σ), StemDep σ kSel →
    (∃ a : Fama.VineA.PrescribedPrimeGarden P.γ (2 * R),
      Fama.VineA.PrescribedPrimeGarden.Related P.γ (p := p) (kind := objKind (2 * R)) (Fama.Represents.repPt P.γ π) a (fineMkLow J pat t s kSel σ) ∧ ¬ CleanPtLow J a) →
    classValueLow P p J pat kSel t s A roots h Rf σ Rs dag (fineMkLow J pat t s kSel σ) π = 0

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

/-- The image of a marked set along a molecule isomorphism. -/
def imgMarkLow {S S' : Garden w} (F : MolIso S.molecule S'.molecule) (M : Set (Fama.CLVineG γF S)) : Set (Fama.CLVineG γF S') :=
  {c' | ∃ c ∈ M, c'.atoms = F.img c.atoms}

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

theorem markTransported_imgMarkLow {S S' : Garden w} (F : MolIso S.molecule S'.molecule) (M : Set (Fama.CLVineG γF S)) :
    Fama.Stage1Mk.MarkTransported γF F M (imgMarkLow F M) := by
  intro c c' h
  refine ⟨fun hc => ⟨c, hc, h⟩, fun ⟨c₀, hc₀, h₀⟩ => ?_⟩
  have e : c₀.atoms = c.atoms := F.img_injective (h₀.symm.trans h)
  rwa [← Fama.VineA.clVine_eq_of_atoms e]

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

/-- `𝒱₀(σ)` of the source and of the target correspond along `F`. -/
def V0CorrLow {S S' : Garden w} (F : MolIso S.molecule S'.molecule) (σ : Prescription S) : Prop :=
  (∀ c ∈ Fama.vinesV0 γF S σ, ∃ c' ∈ Fama.vinesV0 γF S' (transportPrescription F σ), c'.atoms = F.img c.atoms) ∧
  (∀ c' ∈ Fama.vinesV0 γF S' (transportPrescription F σ), ∃ c ∈ Fama.vinesV0 γF S σ, c'.atoms = F.img c.atoms)

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
variable (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (kSel σf : Fin w → Option ℕ)

/-- A stem-unclean point: some vine of `𝒱₀(σ)` has its active set on the capped stem. -/
theorem not_cleanPt_iffLow (a : Fama.VineA.PrescribedPrimeGarden γF w) :
    ¬ CleanPtLow J a ↔ ∃ c ∈ Fama.vinesV0 γF a.prime.skeleton a.totalSigma, c ∈ markXLow J a.prime := by
  simp only [CleanPtLow, not_forall, exists_prop, mem_markX_iffLow]
  exact ⟨fun ⟨c, hc, hn⟩ => ⟨c, hc, (Fama.mem_vinesV0.mp hc).1.1, hn⟩, fun ⟨c, hc, _, hn⟩ => ⟨c, hc, hn⟩⟩

end

end WaveTurbulence.GammaLow.Flower
