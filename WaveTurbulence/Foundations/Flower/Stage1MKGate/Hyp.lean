/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkDefs.Stage1MKFull
public import WaveTurbulence.Foundations.Flower.MkDefs.ChiDNorm
public import WaveTurbulence.Foundations.Flower.MkSubpro.Piece
public import WaveTurbulence.Foundations.Flower.MkMark.StemZero
public import WaveTurbulence.Foundations.Stage1.Represents.RepPr2
public import WaveTurbulence.Foundations.Stage1.Represents.RepE3

/-! # B4 STAGE1MK-GATE: the isolated hypothesis on the marked class pieces (B3 + B3s)

`MarkedClassRepresentsMK cP cθ P` is the ONE hypothesis of the marked Stage-1′ gate on the analytic side (ruling R177,
design step 7). Packet B3s (protected slots and pins, on B3's marked units) proves it. It speaks about main's marked
producer (fine′ classes `PcA … mkF`, coarse′ classes at `markI0`, selections `selPMk … mkF`) at a FINE MARKING
`mkF`, and about the piece of a fine′ class built from its representative `repPt π`:

* the marked set of the piece is `classMk mkF a := mkF a.prime ∩ vinesV0 a.prime.skeleton a.totalSigma` (ruling R173
  supplied at the piece, F-B4-3: a `MarkFn` cannot see the prescription);
* the piece is B2c's `MkSubpro.stage1PieceMKOf` at the representative, with `nProt := |Π(rep)|`
  (`(protI (repPt π).layered J pat t s kSel).card`, F-B4-2 (ii)), and with B3s's protected atoms `prot`, pins `fix`,
  filters `filt`, indicator `ind` and residual selected vertices `selR` (existential);
* the class value is the `kernelKgenSel` class sum at coset base `0` (F-B4-1).

The fine marking is quantified over every `mkF` satisfying `FineMarking`, which pins it down extensionally: `markI`
when the weight is stem-free (`¬ StemDep σ kSel`), and `markI ∪ X` (B2e's `markIX`, `X` = stem-unclean vines of `𝒱`)
when it is stem-dependent (F-B4-4 (b)). The hypothesis is claimed only for the non-zero classes: stem-free weight,
or every point of the fine′ class is stem-clean (`CleanPt`); the other classes are B4's zero pieces (FL-SEP). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents
open WaveTurbulence.RedSplice (Prescription stSt vinesV0)

namespace WaveTurbulence.Flower.Stage1MKGate

variable {w : ℕ}

/-! ## The marked set of a class piece, stem dependence, clean points, fine markings -/

/-- **The marked set of the piece of a prescribed point** (ruling R173 at the piece): the fine marking restricted to
the selected collection `𝒱₀(σ)` of the point. -/
def classMk (mkF : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w) : Set (Stage1.CLVine a.prime.skeleton) :=
  mkF a.prime ∩ vinesV0 a.prime.skeleton a.totalSigma

/-- R173 instance: the marked set of a class piece lies in `𝒱₀(σ)`. -/
theorem classMk_sub_vinesV0 (mkF : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w) :
    classMk mkF a ⊆ vinesV0 a.prime.skeleton a.totalSigma :=
  Set.inter_subset_right

/-- The weight is stem-dependent: a capped-stem filter or a depth selection is present (the case in which
`MarkedWeightClassI` imposes high roots). -/
def StemDep (σ kSel : Fin w → Option ℕ) : Prop := (∃ i, σ i ≠ none) ∨ ∃ i, kSel i ≠ none

/-- A stem-clean prescribed point: the capped stems avoid the active set of every vine of `𝒱₀(σ)`. -/
def CleanPt (J : Finset (Fin w)) (a : PrescribedPrimeGarden w) : Prop :=
  ∀ c ∈ vinesV0 a.prime.skeleton a.totalSigma, MkMark.StemCleanAt J a.prime c.atoms c.upper

/-- **The fine marking of Stage 1′** (F-B4-4 (b)), characterized: it contains `markI` (`Π`-marked vines); for a
stem-dependent weight it contains every stem-unclean vine of `𝒱`; it contains nothing else; and every fine′ batch
from every prescribed point carries it. -/
structure FineMarking (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (kSel σ : Fin w → Option ℕ)
    (mkF : Stage1Mk.MarkFn w) : Prop where
  sub : ∀ {LG : LayeredGarden w} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B
  stem : StemDep σ kSel → ∀ {LG : LayeredGarden w} (B : PrimeData LG), ∀ c ∈ Stage1.vinesV B.skeleton,
    ¬ MkMark.StemCleanAt J B c.atoms c.upper → c ∈ mkF B
  le : ∀ {LG : LayeredGarden w} (B : PrimeData LG), ∀ c ∈ mkF B, c ∈ markI J pat t s kSel B ∨
    (StemDep σ kSel ∧ c ∈ Stage1.vinesV B.skeleton ∧ ¬ MkMark.StemCleanAt J B c.atoms c.upper)
  fine : ∀ a : PrescribedPrimeGarden w, a.FineTransportedAt mkF

/-! ## The piece and the value of a fine′ class -/

/-- **The marked piece of a prescribed point** (B2c's `stage1PieceMKOf` at the point, marked set `classMk mkF a`). -/
def classPiece (P : WTParams) {R : ℕ} (mkF : Stage1Mk.MarkFn (2 * R)) (a : PrescribedPrimeGarden (2 * R))
    (prot : Finset (GBranch (stSt a.prime.skeleton a.totalSigma (classMk mkF a)).G.tree)) (nProt : ℕ)
    (fix : GBranch (stSt a.prime.skeleton a.totalSigma (classMk mkF a)).G.tree → Option ℝ)
    (filt : GBranch (stSt a.prime.skeleton a.totalSigma (classMk mkF a)).G.tree → Option (ℝ × SchwartzMap ℝ ℂ))
    (ind : (GNode (stSt a.prime.skeleton a.totalSigma (classMk mkF a)).G.tree → Mom P.d) → ℝ) :
    Stage1PieceMK P.d R :=
  MkSubpro.stage1PieceMKOf P a.prime.prime.1 a.layered a.prime.decodes a.totalSigma (classMk mkF a) prot nProt fix
    filt ind

/-- The intrinsic marked weight with explicit data (`selOK · markedWeight`). -/
def markedWt (P : WTParams) {R : ℕ} (J : Finset (Fin (2 * R))) (p : ℕ) (kSel : Fin (2 * R) → Option ℕ)
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (Rf : Fin (2 * R) → Option ℝ) (σ : Fin (2 * R) → Option ℕ)
    (Rs : Fin (2 * R) → ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (LG : LayeredGarden (2 * R)) :
    (GNode LG.garden.tree → Mom P.d) → ℝ :=
  fun k => selOK LG J kSel * markedWeight LG J p P.L Rf σ (selCap LG J kSel) Rs h dag k

/-- **The value of a fine′ class**: the `kernelKgenSel` sum (coset base `0`) over the coarse′ class (`markI0`) of the
class, restricted to the decorations selected by the class (`selPMk` at the fine marking). -/
def classValue (P : WTParams) {R : ℕ} (p : ℕ) (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat)
    (kSel : Fin (2 * R) → Option ℕ) (t s : ℝ) (A : Finset (LayeredGarden (2 * R)))
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ)
    (Rf : Fin (2 * R) → Option ℝ) (σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ)
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (mkF : Stage1Mk.MarkFn (2 * R))
    (π : PcA R p (objKind (2 * R)) A mkF) : ℂ :=
  ∑ LG ∈ membersP (clsPMk (markI0 J pat t s) π),
    kernelKgenSel P.L P.γ P.δ LG (fixCap LG J pat t s) (offCap LG J dag.isSome)
      (markedWt P J p kSel h Rf σ Rs dag LG) (fun _ => t) 0 roots
      (selPMk p (objKind (2 * R)) A P 0 roots mkF π LG)

/-- The fields of `MkPieceRest` that B3s supplies (all except `survivors_card`, which is B4's), verbatim. -/
structure PieceRestB3s {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R) (cθ : ℝ) : Prop where
  prot_card : π.surv.prot.card ≤ 2 * π.nProt
  fix_prot : ∀ b, (π.fix b).isSome → b ∈ π.surv.prot
  fix_layer : ∀ b t, π.fix b = some t → (π.layer b : ℝ) ≤ t ∧ t ≤ π.layer b + 1
  filt_ok : ∀ a q, π.filt a = some q → a ∉ π.Cs.hinges ∧ 1 ≤ q.1 ∧ (∀ u, ‖q.2 u‖ ≤ 1) ∧ filterB ⇑q.2 ≤ cθ
  ind_ok : ∀ k, 0 ≤ π.ind k ∧ π.ind k ≤ 1
  ind_local : ∀ k k', (∀ a ∈ π.surv.joints ∪ π.surv.prot, ∀ i : Fin 3,
    k (a.child i) = k' (a.child i) ∧ k a.toNode = k' a.toNode) → π.ind k = π.ind k'

/-- **What B3s provides for one class piece**: `RepresentsIntMKSel` of the class value at the mass `selMassMK`
(residual selected vertices `selR`), the six non-survivor `MkPieceRest` fields, and the residual-selection facts of
`Stage1ReductionAtMKFull`. -/
structure ClassPieceOK {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R) (selR : Finset (GBranch π.Gsb.tree))
    (N : ℕ) (cP cθ t b : ℝ) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (kSel : Fin (2 * R) → Option ℕ)
    (Rs : Fin (2 * R) → ℝ) (val : ℂ) : Prop where
  rep : RepresentsIntMKSel π selR N cP (fun _ => t) 0 roots (selMassMK N b Rs kSel (selR.image fun v => v.1.1)) val
  rest : PieceRestB3s π cθ
  sel_spec : ∀ v ∈ selR, (kSel v.1.1).isSome ∧ π.fix v = none ∧
    ∃ ψ : SchwartzMap ℝ ℂ, π.filt v = some (Rs v.1.1, ψ) ∧ ∀ u, ψ u = (chiDN u : ℂ)
  sel_inj : ∀ v ∈ selR, ∀ v' ∈ selR, v.1.1 = v'.1.1 → v = v'
  sel_card : selR.card ≤ π.nProt
  /-- For the frozen form `MkDefs.Stage1ReductionAtMK` only: plain `RepresentsIntMK` at `cP + 343` and mass `b^N`.
  (It follows from `rep` when the weight `w` of the representation is measurable: `∏ (1+|ξ_v|)^{1/18} ≥ 1`,
  `selMassMK ≤ b^N`, `L^{7(47d+2)·#selR} ≤ L^{343·d·nProt}` for `d ≥ 1`; `RepresentsIntMKSel` alone does not give the
  integrability of `‖w‖`.) -/
  repMK : π.RepresentsIntMK N (cP + 343) (fun _ => t) 0 roots (b ^ N) val

/-! ## The hypothesis -/

/-- **`MarkedClassRepresentsMK cP cθ P`** (B3 + B3s; ruling R177, B4 design step 7). Binders: those of
`Stage1ReductionAtMKFull` (coset base `0`), then a fine marking `mkF` (`FineMarking`), then a fine′ class `π` that is
non-zero (stem-free weight, or every point of the class is stem-clean). Conclusion: for the piece of `repPt π` at
the marked set `classMk mkF (repPt π)` and `nProt = |Π(repPt π)|`, B3s's data `prot, fix, filt, ind, selR` exist with
`ClassPieceOK` for the class value `classValue`. -/
def MarkedClassRepresentsMK (cP cθ : ℝ) (P : WTParams) : Prop :=
  ∀ p, p < P.D → ∀ R, 1 ≤ R → R ≤ 10 * P.R (p + 1) → ∀ N, 1 ≤ N → N ≤ P.N (p + 1) ^ 4 →
  ∀ (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (kSel : Fin (2 * R) → Option ℕ),
  ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t,
  ∀ A : Finset (LayeredGarden (2 * R)),
    (∀ LG ∈ A, MkCarries P p N LG ∧ (∀ h : 2 * R = 2, ¬ IsRegularCouple (h ▸ LG.garden : Garden 2)) ∧
      LG.garden.Irreducible ∧ (∀ j ∈ J, LG.garden.tree j = TTree.leaf) ∧ CapGeo LG J p ∧ CapPatValid LG J pat p) →
    (∀ j, (kSel j).isSome → pat j = FixPat.plain) →
    MarkedTwistClosed p A (protSkOf R J (fun LG => fixCap LG J pat t s) (fun LG => selSetCap LG J kSel)) →
  ∀ (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ) (Rf : Fin (2 * R) → Option ℝ)
    (σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)),
    1 ≤ b → (∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b) →
    (∀ j r, Rf j = some r → P.L / 2 ≤ r) → (∀ j, P.L ≤ Rs j) →
    (((∃ i, σ i ≠ none) ∨ ∃ i, kSel i ≠ none) → ∀ j, j ∉ J → ∃ r, Rf j = some r ∧
      (∀ j' x, ‖x‖ ≥ r → h p j j' x = 0 ∧ h p j' j x = 0) ∧ r ^ 10 ≤ ‖latticePoint P.L (roots j)‖) →
  ∀ (mkF : Stage1Mk.MarkFn (2 * R)), FineMarking J pat t s kSel σ mkF →
  ∀ π : PcA R p (objKind (2 * R)) A mkF,
    (¬ StemDep σ kSel ∨ ∀ a : PrescribedPrimeGarden (2 * R),
      Related (p := p) (kind := objKind (2 * R)) (repPt π) a mkF → CleanPt J a) →
  ∃ (prot : Finset (GBranch (stSt (repPt π).prime.skeleton (repPt π).totalSigma (classMk mkF (repPt π))).G.tree))
    (fix : GBranch (stSt (repPt π).prime.skeleton (repPt π).totalSigma (classMk mkF (repPt π))).G.tree → Option ℝ)
    (filt : GBranch (stSt (repPt π).prime.skeleton (repPt π).totalSigma (classMk mkF (repPt π))).G.tree →
      Option (ℝ × SchwartzMap ℝ ℂ))
    (ind : (GNode (stSt (repPt π).prime.skeleton (repPt π).totalSigma (classMk mkF (repPt π))).G.tree → Mom P.d) →
      ℝ)
    (selR : Finset (GBranch (stSt (repPt π).prime.skeleton (repPt π).totalSigma (classMk mkF (repPt π))).G.tree)),
    ClassPieceOK (classPiece P mkF (repPt π) prot (protI (repPt π).layered J pat t s kSel).card fix filt ind) selR
      N cP cθ t b roots kSel Rs (classValue P p J pat kSel t s A roots h Rf σ Rs dag mkF π)

end WaveTurbulence.Flower.Stage1MKGate
