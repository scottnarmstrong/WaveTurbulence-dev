/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkDefs.Intrinsic
public import WaveTurbulence.Foundations.Spine.SourceSplicedKernel
public import WaveTurbulence.Foundations.Spine.SourceVineData
public import WaveTurbulence.Foundations.Spine.SourceSubproObjects
public import WaveTurbulence.Foundations.Spine.Stage1Interface
public import WaveTurbulence.Foundations.Spine.Stage1Gate
public import WaveTurbulence.Foundations.Spine.Stage1SumBound
public import WaveTurbulence.Foundations.FlowerTop.Port.SplicedKernelST

/-! # MK-DEFS (A2-R, from B0 S-STAGE1MK): Stage 1′ / Stage 2′ interfaces and the corrected component target

Copied by source from `scope/B0-STAGE1MK/probe/Stage1MKProbe.lean` (sha256 `dab37b30…6c6b`), lines 222–288,
294–406 and 416–449, into namespace `WaveTurbulence.Flower.MkDefs` (see COPIED-SHA256SUMS). Not copied: lines
289–292 (`MkCarries`; the single definition is `MkDefs.Defs.MkCarries`, ruling R156) and 407–415 (`MarkedPieceBound`,
C0 finding F-C0-4). One added hypothesis in `MarkedComponentBoundAtI` (D0 finding F-D0-8, see its docstring). Lines 128–221 (unmarked `𝒱₀`, runs,
survivors) are not copied: packet B1a puts them on main.

`MarkedComponentBoundAtI` is the per-component target (B0 finding F-B0-1); it replaces S-MARKED's
`MarkedComponentBoundAt`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory

namespace WaveTurbulence.Flower.MkDefs

variable {w : ℕ}

/-! ## Copied by source from S-MARKED `probe/MarkedProbe.lean` (sha256 94102f8c…7a6, §4/§5/§9), `lb` removed by B0
and restored as a defaulted last field by ruling R187. -/

open WaveTurbulence.LGSpine.SourceVine in
/-- Survivor data of a marked piece: the collection `𝒞_E` and the protected atoms `Π_sb`. -/
structure SurvivorData {w : ℕ} (G : Garden w) where
  m : ℕ
  surv : Fin m → Object G.molecule
  prot : Finset (GBranch G.tree)

/-- The exceptional joints `B` (joints of survivors). -/
noncomputable def SurvivorData.joints {w : ℕ} {G : Garden w} (S : SurvivorData G) : Finset (GBranch G.tree) :=
  Finset.univ.biUnion fun i => {(S.surv i).upper, (S.surv i).lower}

open WaveTurbulence.LGSpine.SourceVine in
def SurvivorData.Structural {w : ℕ} {G : Garden w} (C : SubproChoices G) (S : SurvivorData G) : Prop :=
  (∀ i, WaveTurbulence.FinalCountAsm.ObjVine G.molecule (S.surv i)) ∧
  (∀ i j, Disjoint (C.collection i).atoms (S.surv j).atoms) ∧
  (∀ i j, i ≠ j → ((S.surv i).atoms ∩ (S.surv j).atoms).card ≤ 1) ∧
  (∀ v ∈ C.hinges, ∀ i, ¬ (S.surv i).IsInterior v)

open scoped FourierTransform in
noncomputable def filterB (ψ : ℝ → ℂ) : ℝ :=
  ∫ ξ : ℝ, (1 + |ξ|) ^ 2 * ‖𝓕 ψ ξ‖

/-- Spliced kernel data with arbitrary designated times (pins at `s` or `t`). With the enlarged marking no lower slot
is protected, so U-clock's hinge boundary `t_{a_j} > s` never occurs. Ruling R187 (F-H3-1; R184's design re-applied):
constant lower bounds `lb` (`x < t_v` whenever `lb v = some x`) on free atoms, for the free parent of a
`dParent`-pinned object top (`lb π = some s`). The default `fun _ => none` keeps every existing construction. -/
structure SplicedKernelDataMK {w : ℕ} (G : Garden w) (d : ℕ) extends SplicedKernelData G d where
  fix : GBranch G.tree → Option ℝ
  filt : GBranch G.tree → Option (ℝ × SchwartzMap ℝ ℂ)
  ind : (GNode G.tree → Mom d) → ℝ
  lb : GBranch G.tree → Option ℝ := fun _ => none

noncomputable def SplicedKernelDataMK.atomW {w d : ℕ} {G : Garden w} (D : SplicedKernelDataMK G d)
    (k : GNode G.tree → Mom d) : ℂ :=
  (∏ a : GBranch G.tree, (D.filt a).elim 1 fun q => q.2 (omegaNode G k a / q.1)) * (D.ind k : ℂ)

/-- The constant lower bounds (ruling R187): `x < t v` whenever `lb v = some x`. -/
def splicedLBDomain {w : ℕ} {G : Garden w} (lb : GBranch G.tree → Option ℝ) : Set (GBranch G.tree → ℝ) :=
  {t | ∀ v x, lb v = some x → x < t v}

/-- The pinned time integral over the pinned domain intersected with the lower bounds (ruling R187). -/
noncomputable def splicedTimeIntegralMK {w d : ℕ} (G : Garden w) (D : SplicedKernelDataMK G d)
    (L γ δ : ℝ) (base : Mom d) (z : GNode G.tree → (Fin d → ℤ)) : ℂ :=
  ∫ τ : {b : GBranch G.tree // D.fix b = none} → ℝ,
    (splicedTimeDomainFix G D.layer D.rootTime D.fix ∩ splicedLBDomain D.lb).indicator
      (fun t => phaseProd L γ δ G (cosetDecoration G L base z) t *
        ∏ v : GBranch G.tree, Complex.exp ((Real.pi * D.frequency v * t v : ℝ) * Complex.I))
      (G.extendFix D.fix τ)

/-- No lower bounds: the lower-bound domain is everything. -/
theorem splicedLBDomain_none {w : ℕ} {G : Garden w} :
    splicedLBDomain (G := G) (fun _ => none) = Set.univ := by
  ext t; simp [splicedLBDomain]

/-- **`lb`-free data have the old time integral** (the pinned domain alone), so proofs about `lb`-free pieces
transfer. -/
theorem splicedTimeIntegralMK_lb_none {w d : ℕ} (G : Garden w) (D : SplicedKernelDataMK G d)
    (hlb : D.lb = fun _ => none) (L γ δ : ℝ) (base : Mom d) (z : GNode G.tree → (Fin d → ℤ)) :
    splicedTimeIntegralMK G D L γ δ base z =
      ∫ τ : {b : GBranch G.tree // D.fix b = none} → ℝ,
        (splicedTimeDomainFix G D.layer D.rootTime D.fix).indicator
          (fun t => phaseProd L γ δ G (cosetDecoration G L base z) t *
            ∏ v : GBranch G.tree, Complex.exp ((Real.pi * D.frequency v * t v : ℝ) * Complex.I))
          (G.extendFix D.fix τ) := by
  unfold splicedTimeIntegralMK
  rw [hlb, splicedLBDomain_none, Set.inter_univ]

noncomputable def splicedKernelMK {w d : ℕ} (G : Garden w) (D : SplicedKernelDataMK G d)
    (L γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) : ℂ :=
  (coupling d L γ δ : ℂ) ^ G.order *
    ∑' z : GenDecoration G d roots 0,
      (D.atomW (cosetDecoration G L base z.1) *
        (splicedEpsilon G D.hinges z.1 : ℂ) * (splicedGapIndicator G D.toSplicedKernelData L γ η base z.1 : ℂ) *
        (∏ x ∈ G.molecule.bonds, D.edgeAmplitude x (base + latticePoint L (bondIndex G z.1 x))) *
        D.hingeAmplitude (fun x => base + latticePoint L (bondIndex G z.1 x.1)) *
        splicedTimeIntegralMK G D L γ δ base z.1)

noncomputable def kernelKgenSel (L γ δ : ℝ) {w d : ℕ} (LG : LayeredGarden w)
    (fix : GBranch LG.garden.tree → Option ℝ) (off : Finset (GBranch LG.garden.tree))
    (wt : (GNode LG.garden.tree → Mom d) → ℝ) (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (sel : GenDecoration LG.garden d nroot 0 → Prop) : ℂ :=
  (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
    ∑' κ : GenDecoration LG.garden d nroot 0, if sel κ then
      (epsDec LG.garden κ.1 : ℂ) * (wt (cosetDecoration LG.garden L k₀ κ.1) : ℂ) *
        (∫ τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ,
          (kDomainFix LG up fix).indicator
            (phaseProdOff L γ δ LG.garden off (cosetDecoration LG.garden L k₀ κ.1))
            (LG.garden.extendFix fix τ)) else 0

/-! ## Carriers (ruling R156). -/

/-- The truncation-free carrier that main's Stage-1 producer actually uses (it never reads `IsTrunc`). -/
def Stage1CarriesW (P : WTParams) (p N : ℕ) {w : ℕ} (LG : LayeredGarden w) : Prop :=
  IsCanonGC (p + 1) LG ∧ LG.garden.order = N ∧ IsBalancedSig LG.garden.sig ∧
    (∀ h : w = 2, ¬ IsRegularCouple (h ▸ LG.garden : Garden 2))

theorem stage1CarriesW_of_stage1Carries {P : WTParams} {p N w : ℕ} {LG : LayeredGarden w}
    (h : Stage1Carries P p N LG) : Stage1CarriesW P p N LG :=
  ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem stage1CarriesW_of_mkCarries {P : WTParams} {p N w : ℕ} {LG : LayeredGarden w}
    (h : MkCarries P p N LG) (hnr : ∀ h : w = 2, ¬ IsRegularCouple (h ▸ LG.garden : Garden 2)) :
    Stage1CarriesW P p N LG :=
  ⟨h.1, h.2.2.1, h.2.2.2, hnr⟩

/-! ## The Stage-1′ piece, soundness, weight class and gate (corrected: intrinsic data, `nProt`; `lb` restored by
ruling R187). -/

/-- A marked Stage-1′ piece. `nProt` is `|Π|` of the class (o75 `b`); `surv.prot` is `Π_sb`. `lb` (ruling R187):
constant lower bounds on free atoms, default none. -/
structure Stage1PieceMK (d R : ℕ) extends Stage1PieceD d R where
  surv : SurvivorData Gsb
  nProt : ℕ
  fix : GBranch Gsb.tree → Option ℝ
  filt : GBranch Gsb.tree → Option (ℝ × SchwartzMap ℝ ℂ)
  ind : (GNode Gsb.tree → Mom d) → ℝ
  lb : GBranch Gsb.tree → Option ℝ := fun _ => none

def Stage1PieceMK.dataMK {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R) (tt : Fin (2 * R) → ℝ)
    (center : GardenDart π.Gsb → Mom P.d) (edge : GardenDart π.Gsb → Mom P.d → ℂ)
    (hinge : (HingeDarts π.Gsb π.Cs.hinges → Mom P.d) → ℂ)
    (freq : GBranch π.Gsb.tree → ℝ) : SplicedKernelDataMK π.Gsb P.d where
  toSplicedKernelData := Stage1Piece.data π.toStage1PieceD tt center edge hinge freq
  fix := π.fix
  filt := π.filt
  ind := π.ind
  lb := π.lb

/-- `RepresentsInt` with pins, survivors and the protected-object loss `L^{cP·d·nProt}`. -/
def Stage1PieceMK.RepresentsIntMK {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R) (n : ℕ) (cP : ℝ)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (s : ℝ) (val : ℂ) : Prop :=
  ∃ (Ξ : Type) (_ : MeasurableSpace Ξ) (μ : Measure Ξ) (w : Ξ → ℂ)
    (ctr : Ξ → GardenDart π.Gsb → Mom P.d)
    (edge : Ξ → GardenDart π.Gsb → Mom P.d → ℂ)
    (hinge : Ξ → (HingeDarts π.Gsb π.Cs.hinges → Mom P.d) → ℂ)
    (freq : Ξ → GBranch π.Gsb.tree → ℝ),
    Integrable (fun ξ => w ξ * splicedKernelMK π.Gsb (π.dataMK tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))
      P.L P.γ P.η P.δ base roots) μ ∧
    val = ∫ ξ, w ξ * splicedKernelMK π.Gsb (π.dataMK tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))
      P.L P.γ P.η P.δ base roots ∂μ ∧
    Integrable (fun ξ => ‖w ξ‖) μ ∧
    (∫ ξ, ‖w ξ‖ ∂μ ≤ (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
      P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) +
        P.η ^ 7 * (π.Cs.hinges.card : ℝ)) * P.L ^ (cP * P.d * (π.nProt : ℝ)) * s) ∧
    ∀ ξ, SplicedAmplitudeBounds π.Gsb (Stage1Piece.data π.toStage1PieceD tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))

/-- Structural soundness of a marked piece (enlarged marking: `N_E ≤ 6b`, `|Π_sb| ≤ 2b`). -/
structure SoundMK {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R) (p : ℕ) : Prop where
  plain : π.Gsb.IsPlain
  irreducible : π.Gsb.Irreducible
  balanced : IsBalancedSig π.Gsb.sig
  order_pos : 1 ≤ π.Gsb.order
  order_le : π.Gsb.order ≤ P.N (p + 1) ^ 4
  layer_le : ∀ v, π.layer v ≤ p
  survivors : π.surv.Structural π.Cs
  survivors_card : π.surv.m ≤ 6 * π.nProt
  prot_card : π.surv.prot.card ≤ 2 * π.nProt

structure Stage1DataMK (P : WTParams) (R : ℕ) where
  Pc : Type
  fin : Fintype Pc
  piece : Pc → Stage1PieceMK P.d R
  val : Pc → ℂ

def Stage1DataMK.toData {P : WTParams} {R : ℕ} (S : Stage1DataMK P R) : Stage1Data P R :=
  ⟨S.Pc, S.fin, fun π => (S.piece π).toStage1PieceD, S.val⟩

/-- The intrinsic marked weight class: `markedWeight` at the depth-selected stem vertices (weight `0` if a requested
selected vertex is absent), anchored profiles bounded by `b`, frontier scales `≥ L/2`, high roots when filters or
selections are present. -/
def MarkedWeightClassI (P : WTParams) (p : ℕ) {R : ℕ} (J : Finset (Fin (2 * R))) (dag : Bool)
    (kSel : Fin (2 * R) → Option ℕ) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (wt : ∀ LG : LayeredGarden (2 * R), (GNode LG.garden.tree → Mom P.d) → ℝ) (b : ℝ) : Prop :=
  1 ≤ b ∧ ∃ (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (Rf : Fin (2 * R) → Option ℝ)
    (σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (dagv : Option (Fin (2 * R) → Fin 3 → Mom P.d)),
    dagv.isSome = dag ∧
    (∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b) ∧
    (∀ j r, Rf j = some r → P.L / 2 ≤ r) ∧ (∀ j, P.L ≤ Rs j) ∧
    (∀ LG, wt LG = fun k => selOK LG J kSel * markedWeight LG J p P.L Rf σ (selCap LG J kSel) Rs h dagv k) ∧
    (((∃ i, σ i ≠ none) ∨ ∃ i, kSel i ≠ none) → ∀ j, j ∉ J → ∃ r, Rf j = some r ∧
      (∀ j' x, ‖x‖ ≥ r → h p j j' x = 0 ∧ h p j' j x = 0) ∧ r ^ 10 ≤ ‖latticePoint P.L (roots j)‖)

/-- **Stage1ReductionAtMK** (Stage 1′, o75 §2.5 + Theorem 7.5′(1)–(6′) + U-clock with the enlarged marking): the
analogue of main's `Stage1ReductionAt` for capped, pinned, marked component families closed under twists at
unmarked vines, with intrinsic pins `fixCap`, dagger `offCap` and depth selections `kSel`.
Ruling R177 (B4, findings F-B4-1/F-B4-2): stated at coset base `0` (the high-root clause of `MarkedWeightClassI`
reads `latticePoint P.L (roots j)`, the root momentum only at base `0`; the consumer's `compValue` has `k₀ = 0`),
with the protected count bounded at ONE member of the class, and with the plain-pattern hypothesis on selected
trees of `MarkedComponentBoundAtI` (F-D0-8; needed to derive this form from `Stage1ReductionAtMKFull`). Ruling R185
(F-B3s-8): `J.card = R` after the cap set, as in `MarkedComponentBoundAtI`. -/
def Stage1ReductionAtMK (C₀ : ℕ) (cP : ℝ) (P : WTParams) : Prop :=
  ∀ p, p < P.D → ∀ R, 1 ≤ R → R ≤ 10 * P.R (p + 1) → ∀ N, 1 ≤ N → N ≤ P.N (p + 1) ^ 4 →
  ∀ (J : Finset (Fin (2 * R))), J.card = R →
  ∀ (pat : Fin (2 * R) → FixPat) (dag : Bool) (kSel : Fin (2 * R) → Option ℕ),
  ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t,
  ∀ A : Finset (LayeredGarden (2 * R)),
    (∀ LG ∈ A, MkCarries P p N LG ∧ (∀ h : 2 * R = 2, ¬ IsRegularCouple (h ▸ LG.garden : Garden 2)) ∧
      LG.garden.Irreducible ∧ (∀ j ∈ J, LG.garden.tree j = TTree.leaf) ∧ CapGeo LG J p ∧ CapPatValid LG J pat p) →
    (∀ j, (kSel j).isSome → pat j = FixPat.plain) →
    MarkedTwistClosed p A (protSkOf R J (fun LG => fixCap LG J pat t s) (fun LG => selSetCap LG J kSel)) →
  ∀ (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (wt : ∀ LG : LayeredGarden (2 * R), (GNode LG.garden.tree → Mom P.d) → ℝ) (b : ℝ),
    MarkedWeightClassI P p J dag kSel roots wt b →
  ∃ (S : Stage1DataMK P R) (Cl : Type) (hCl : Fintype Cl) (cls : S.Pc → Cl)
    (members : Cl → Finset (LayeredGarden (2 * R)))
    (sel : S.Pc → ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → Prop),
    Stage1Partition roots A members cls sel ∧
    (∀ π, S.val π = ∑ LG ∈ members (cls π),
        kernelKgenSel P.L P.γ P.δ LG (fixCap LG J pat t s) (offCap LG J dag) (wt LG) (fun _ => t) 0 roots
          (sel π LG) ∧
      (S.piece π).RepresentsIntMK N cP (fun _ => t) 0 roots (b ^ N) (S.val π) ∧
      ∃ LG ∈ members (cls π), (S.piece π).nProt ≤ (protI LG J pat t s kSel).card) ∧
    (∀ π, SoundMK (P := P) (S.piece π) p) ∧ (∀ π, (S.piece π).Gsb.order ≤ N) ∧
    Stage1Counts C₀ P R N S.toData Cl hCl cls

/- (A2-R) B0's `MarkedPieceBound` (probe lines 407–415) is NOT copied: C0 finding F-C0-4 (false as an unconditional
`∀ P`, drops gains); C0 restates it as `MarkedPieceBoundAt` in its own statement module. -/

/-- **MarkedComponentBoundAt, corrected** (S-MARKED §2.3 with intrinsic pins/dagger/selection, `|J| = R`, carrier
`MkCarries` of R156; width-2 regular classes go to D6 inside its proof). A2-R deviation from the B0 probe text
(finding F-D0-8): the hypothesis `∀ j, (kSel j).isSome → pat j = .plain` after the carrier hypothesis (a selection
at a pattern-pinned stem vertex has no integrated time, hence no `R^{-1/18}` gain); dropping the twist-closure
hypothesis gives D0's `RegularComponentBoundAtI` shape. A2-R2 deviation (ruling R163, D2b): the carrier conjunction
also has `CapGeo LG J p ∧ CapPatValid LG J pat p` (as in `Stage1ReductionAtMK`). -/
def MarkedComponentBoundAtI (B : ℝ) (Pm : ℕ) (P : WTParams) : Prop :=
  1 / 2 < P.γ → ∀ p : ℕ, p < P.D → ∀ R : ℕ, 1 ≤ R → R ≤ 2 * Pm → ∀ n : ℕ, 1 ≤ n → n ≤ P.N (p + 1) ^ 4 →
  ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ (J : Finset (Fin (2 * R))) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
  J.card = R →
  ∀ (pat : Fin (2 * R) → FixPat) (kSel : Fin (2 * R) → Option ℕ) (A : Finset (LayeredGarden (2 * R))),
    (∀ LG ∈ A, MkCarries P p n LG ∧ LG.garden.Irreducible ∧ (∀ j ∈ J, LG.garden.tree j = TTree.leaf) ∧
      CapGeo LG J p ∧ CapPatValid LG J pat p) →
    (∀ j, (kSel j).isSome → pat j = FixPat.plain) →
    MarkedTwistClosed p A (protSkOf R J (fun LG => fixCap LG J pat t s) (fun LG => selSetCap LG J kSel)) →
  ∀ (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ), 1 ≤ b →
    (∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b) →
  ∀ (Rf : Fin (2 * R) → Option ℝ) (σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ)
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)),
    (∀ j r, Rf j = some r → P.L / 2 ≤ r) → (∀ j, P.L ≤ Rs j) →
    (((∃ i, σ i ≠ none) ∨ ∃ i, kSel i ≠ none) → ∀ j, j ∉ J → ∃ r, Rf j = some r ∧
      (∀ j' x, ‖x‖ ≥ r → h p j j' x = 0 ∧ h p j' j x = 0) ∧ r ^ 10 ≤ ‖latticePoint P.L (roots j)‖) →
    ‖∑ LG ∈ A, compValue P LG (fixCap LG J pat t s) (offCap LG J dag.isSome)
        (fun k => selOK LG J kSel * markedWeight LG J p P.L Rf σ (selCap LG J kSel) Rs h dag k) t roots‖ ≤
      P.L ^ (B * P.d * (2 * R : ℕ)) * P.δ ^ (7 * P.ν * n) * b ^ n *
        ∏ j : Fin (2 * R), (if (kSel j).isSome then (Rs j)⁻¹ * (Rs j) ^ (-(1 / 18 : ℝ)) else 1)

/-! ## The budget with the enlarged marking (math check, §5 of SCOPE). -/

/-- Per protected vertex: split `(60d+2)·14`, survivors `2·6`, Theorem 7.3′ `400d`, Theorem 8.2′ `47d+5`; with
`|Π| ≤ 25R` per component of width `2R` this is inside `L^{B·d·2R}` for `B = 16500`, and `4B ≤ 10⁵ = BcMK/d`. -/
theorem enlarged_budget (d : ℕ) (hd : 3 ≤ d) :
    ((60 * d + 2) * 14 + 2 * 6 + 400 * d + (47 * d + 5)) * 25 ≤ 16500 * 2 * d ∧ 4 * 16500 ≤ 100000 := by
  constructor <;> omega

/-- The unenlarged rule (o75 as printed), same accounting: split `(60d+2)·6`, survivors `2·2`. -/
theorem printed_budget (d : ℕ) (hd : 3 ≤ d) :
    ((60 * d + 2) * 6 + 2 * 2 + 400 * d + (47 * d + 5)) * 25 ≤ 10500 * 2 * d := by
  omega

end WaveTurbulence.Flower.MkDefs
