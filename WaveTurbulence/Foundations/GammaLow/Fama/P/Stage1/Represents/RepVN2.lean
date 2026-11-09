/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Stage1.Represents.RepVN2` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepH13
public import WaveTurbulence.Foundations.Stage1.Represents.RepOuterM2
public import WaveTurbulence.Foundations.Stage1.Represents.RepVN1
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Represents.RepVN2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Amend7
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Deg
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Desig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Final
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceFlowKind
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
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Pairs
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Rev
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Runs
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Skip
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Split
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.SurvData
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Top
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.TripleDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.TripleHinge
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
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainFlows
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Spine.VineDelObjects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNV2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNV3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNV4
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepRep1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepRep3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel


/-!
# S2 REPRESENTS, VINE-D (per-mode `AsmCtxH`): one outer slot mode, hinge families from VINEEST

For one mode `ξ` of the outer slots (an amplitude `amp s` and the frequencies `frqR frq route s` of the clocks that stay
in `G_sb` for every replacement slot `s`), `asmHMode` is the vine assembly context with the singleton slot family
`Λ_s = Unit`, `w = 1` and the hinge families `H` of the units for the modulation `modLam frq route j`.  `repIntC_mode`:
the per-mode outer form `outerValM` of a piece `π` is a spliced-kernel superposition of mass at most
`Cχ^b ballCard^n Π_j Mh_j` (`RepIntC`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
namespace WaveTurbulence.GammaLow.Fama.Represents
open WaveTurbulence.Represents WaveTurbulence.GammaLow.FinalCount
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RepAnalytic WaveTurbulence.GammaLow.FinalCount
  WaveTurbulence.VineEstS3.FS MeasureTheory Set
open scoped ENNReal WaveTurbulence.GammaLow.FinalCount

variable {w d : ℕ} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]


/-- The hinge superposition property of the vine factors `Hk` (the field `hHk` of `AsmCtxH`). -/
abbrev HHkProp {P : WTParams} {R : ℕ} {J : Type} (π : Stage1PieceG P R) (tt : Fin (2 * R) → ℝ) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (selSk : GenDecoration π.Gsb P.d roots 0 → Prop)
    (hclk : J → Fin 3 → ClkSrc π.Gsb) (hmom : J → Fin 4 → GNode π.Gsb.tree)
    (Hk : J → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ) (H : HingeFam J P.d) : Prop :=
  ∀ κ : GenDecoration π.Gsb P.d roots 0, selSk κ → ∀ τ ∈ splicedTimeDomain π.Gsb π.layer tt, ∀ j c,
    (∀ i, ‖(base + latticePoint P.L (κ.1 (hmom j i))) - latPt P.d (c i)‖ ≤ 1) →
    HasSum (fun l => (H.w j c l : ℂ) * H.a j c l (fun i => base + latticePoint P.L (κ.1 (hmom j i))) *
      fsPhase (H.m j c l) (fun i => clockOf π.Gsb tt τ (hclk j i)))
      (Hk j (fun i => clockOf π.Gsb tt τ (hclk j i)) (fun i => base + latticePoint P.L (κ.1 (hmom j i))))

open scoped Classical in
/-- **The per-mode representation of a vine piece.**  One outer slot mode `(amp, frq)` with natural routing, unit
factors `HkM j (modLam frq route j)` superposed by the hinge families `H` (valid in the unit balls on the selected
decorations and the spliced domain, `hHk`), has a `RepIntC` representation of mass `Cχ^b ballCard^n Π_j Mh_j`. -/
theorem repIntC_mode {P : WTParams} {R : ℕ} (hd1 : 1 ≤ P.d) (hL0 : 0 < P.L) (π : Stage1PieceG P R)
    (hS : π.Gsb.IsPlain) (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (selSk : GenDecoration π.Gsb P.d roots 0 → Prop)
    (hgsp : ∀ D' : SplicedKernelData π.Gsb P.d, D'.gapSpecification = π.gapSpecification →
      ∀ z : GenDecoration π.Gsb P.d roots 0,
        splicedGapIndicator π.Gsb D' P.L P.γ P.η base z.1 = if selSk z then 1 else 0)
    (amp : ReplacementSlot π.Gsb → Mom P.d → ℂ) (ctr : ReplacementSlot π.Gsb → Fin P.d → ℤ)
    (h1 : ∀ s k, ‖amp s k‖ ≤ 1) (h2 : ∀ s, SNorm (30 * P.d) 0 (amp s) ≤ 1)
    (h3 : ∀ p k, amp (Sum.inl p) k ≠ 0 → ‖k - latPt P.d (ctr (Sum.inl p))‖ ≤ 1)
    (frq : ReplacementSlot π.Gsb → Fin 2 → ℤ) {J : Type} [Fintype J] [DecidableEq J]
    (route : ReplacementSlot π.Gsb → Fin 2 → ClkSrc π.Gsb ⊕ J)
    (hroute : ∀ s i, route s i = Sum.inl (argSrc hS s i) ∨ ∃ j, route s i = Sum.inr j)
    (hclk : J → Fin 3 → ClkSrc π.Gsb) (hmom : J → Fin 4 → GNode π.Gsb.tree)
    (HkM : J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ)
    (H : HingeFam J P.d) (Mh : J → ℝ) (hMh : ∀ j c, ∑' l, H.w j c l ≤ Mh j)
    (hHk : HHkProp π tt base roots selSk hclk hmom (fun j => HkM j (modLam frq route j)) H)
    (src : J → Fin 4 → HingeDarts π.Gsb π.Cs.hinges ⊕ Fin (2 * R))
    (src_dart : ∀ j i x, src j i = Sum.inl x → ∀ z : GenDecoration π.Gsb P.d roots 0,
      bondIndex π.Gsb z.1 x.1 = z.1 (hmom j i))
    (src_root : ∀ j i r, src j i = Sum.inr r → ∀ z : GenDecoration π.Gsb P.d roots 0, z.1 (hmom j i) = roots r) :
    RepIntC π tt base roots
      (outerValM π.Gsb P.L P.γ P.δ base roots tt π.layer π.Cs.hinges (fun z => if selSk z then 1 else 0) hS
        amp frq route hclk hmom HkM)
      (Cchi P.d ^ Fintype.card (GBranch π.Gsb.tree) * ((nodeBallCard P.d ^ ∑ j, (π.Gsb.tree j).order : ℕ) : ℝ) *
        ∏ j, Mh j) := by
  obtain ⟨hCge, hCspec⟩ := Cchi_spec hd1
  have hCpos : 0 < Cchi P.d := lt_of_lt_of_le zero_lt_one hCge
  let fam := slotFamMode amp ctr (frqR frq route) h1 h2 h3
  let A : AsmCtxH π.Gsb P.d :=
    { hS := hS, hd := hd1, L := P.L, hL := hL0, γ := P.γ, δ := P.δ, η := P.η, base := base, roots := roots,
      tt := tt, layer0 := π.layer, gs := π.gapSpecification, selSk := selSk, hgs := hgsp, fam := fam,
      Cχ := Cchi P.d, hCpos := hCpos, hC := hCspec,
      Fn := fun s ts k => amp s k * fsPhase (frqR frq route s) ts, Box := fun _ => Set.univ,
      hFn := fun s ts _ k => by
        have := hasSum_fintype (fun _ : Unit => ((1 : ℝ) : ℂ) * amp s k * fsPhase (frqR frq route s) ts)
        simp [fam, slotFamMode],
      hbox := fun _ _ _ => Set.mem_univ _,
      hinges := π.Cs.hinges, J := J, fJ := inferInstance, dJ := inferInstance, H := H,
      hmom := hmom, hclk := hclk, Hk := fun j => HkM j (modLam frq route j), Mh := Mh, hMh := hMh,
      hHk := hHk, src := src, src_dart := src_dart, src_root := src_root }
  have hB0 : 0 ≤ Cchi P.d ^ Fintype.card (GBranch π.Gsb.tree) * ((nodeBallCard P.d ^ ∑ j, (π.Gsb.tree j).order : ℕ) : ℝ) *
      ∏ j, Mh j := by
    have hM : ∀ j, 0 ≤ Mh j := fun j => A.Mh_nonneg j (fun _ _ => 0)
    have hMp : 0 ≤ ∏ j, Mh j := Finset.prod_nonneg fun j _ => hM j
    exact mul_nonneg (mul_nonneg (pow_nonneg hCpos.le _) (by positivity)) hMp
  have hval : outerValM π.Gsb P.L P.γ P.δ base roots tt π.layer π.Cs.hinges (fun z => if selSk z then 1 else 0) hS
        amp frq route hclk hmom HkM =
      (coupling P.d A.L A.γ A.δ : ℂ) ^ π.Gsb.order * π.Gsb.zeta *
      ∑' κ : GenDecoration π.Gsb P.d A.roots 0,
        (if A.selSk κ then ((splicedEpsilon π.Gsb A.hinges κ.1 : ℝ) : ℂ) else 0) *
          ∫ τ, (splicedTimeDomain π.Gsb A.layer0 A.tt).indicator (fun τ =>
            phaseProd A.L A.γ A.δ π.Gsb (cosetDecoration π.Gsb A.L A.base κ.1) τ * (A.skel κ τ * A.hk κ τ)) τ := by
    rw [A.value_eqH, outerValM_eq_outerVal _ _ _ _ _ _ _ _ _ _ hS amp frq route hroute hclk hmom HkM]
    exact A.outerVal_eq_tsum
  refine repIntC_of_asmH π A tt base roots rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl _ hB0 ?_ _ hval
  have hmass : ∏ s, ∑' l : fam.Λ s, ENNReal.ofReal (A.fam.w s l) = 1 := by
    simp [A, fam, slotFamMode]
  rw [hmass, one_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_prod_of_nonneg (fun j _ => A.Mh_nonneg j (fun _ _ => 0)),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by have := hCpos.le; positivity)]

end WaveTurbulence.GammaLow.Fama.Represents
