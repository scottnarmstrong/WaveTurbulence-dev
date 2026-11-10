/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Fama.Gate
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Gate
public import WaveTurbulence.Foundations.Flower.FinalMKDefs.Fine

/-! # FLOWER-LOW (packet L8), item E (1/2): the marked carrier over `𝒱_γ`

Main's marked Stage-1′/Stage-2′ vocabulary (`Flower.MkDefs.Stage1MK`: `SurvivorData`, `Stage1PieceMK`, `dataMK`,
`RepresentsIntMK`, `SoundMK`, `Stage1DataMK`; `Flower.FinalMKDefs.Count`: the survivor vocabulary, `SubproSupportMK`,
`forbiddenMK`, `SecondCollectionOKMK`, `CriticalSGMK`, `AdmissibleMK`, `splicedCountingAdmissibleMK`,
`FinalCountAtMK`), copied by source (sha256 in `COPIED-SHA256SUMS`), with the vine family made a parameter `γ` and
instantiated at `𝒱_γ`:
* survivors, collection objects and second-collection objects are L6's `FinalCount.Src.Object γ` (family
  `IsVineGamma γ`, ruling D11); the double vine is `DV′` (`Src.IsDV γ`);
* a marked piece extends L5a's `Fama.Stage1PieceGD γ` (subpro choices `Src.SubproChoices γ`);
* `ObjVineG` is main's `FinalCountAsm.ObjVine` over `Src.Object γ`.
Following L6's convention, the family parameter is `γ` and the analytic gap exponent is `γ'` in generic
definitions; statements at a parameter record use `P.γ` for both. Everything family-free (spliced kernels, pins,
filters, `kernelKgenSel`, `filterB`, …) is main's, by import. -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale)

namespace WaveTurbulence.GammaLow.Flower

open WaveTurbulence.GammaLow.FinalCount

variable {w d : ℕ}

/-! ## Survivors (main `MkDefs.Stage1MK`, `FinalCountAsm.ObjVine`) -/

/-- Main's `FinalCountAsm.ObjVine` over `𝒱_γ`: the object is a single `𝒱_γ` vine (resp. its hyper-adjoint is). -/
def ObjVineG {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {γ : ℝ} (M : Molecule V D)
    (U : Src.Object γ M) : Prop :=
  match U.shape with
  | .vc _ => Src.IsSomeVine γ M U.atoms U.upper U.lower
  | .hyper R => Src.IsSomeVine γ (Molecule.eraseBond M R.added) U.atoms U.upper U.lower

/-- Survivor data of a marked piece over `𝒱_γ`: the collection `𝒞_E` and the protected atoms `Π_sb`. -/
structure SurvivorDataG (γ : ℝ) {w : ℕ} (G : Garden w) where
  m : ℕ
  surv : Fin m → Src.Object γ G.molecule
  prot : Finset (GBranch G.tree)

/-- The exceptional joints `B` (joints of survivors). -/
noncomputable def SurvivorDataG.joints {γ : ℝ} {w : ℕ} {G : Garden w} (S : SurvivorDataG γ G) :
    Finset (GBranch G.tree) :=
  Finset.univ.biUnion fun i => {(S.surv i).upper, (S.surv i).lower}

def SurvivorDataG.Structural {γ : ℝ} {w : ℕ} {G : Garden w} (C : Src.SubproChoices γ G) (S : SurvivorDataG γ G) :
    Prop :=
  (∀ i, ObjVineG G.molecule (S.surv i)) ∧
  (∀ i j, Disjoint (C.collection i).atoms (S.surv j).atoms) ∧
  (∀ i j, i ≠ j → ((S.surv i).atoms ∩ (S.surv j).atoms).card ≤ 1) ∧
  (∀ v ∈ C.hinges, ∀ i, ¬ (S.surv i).IsInterior v)

/-- `v` is a joint of the `i`-th survivor. -/
def SurvJointG {γ : ℝ} {G : Garden w} (S : SurvivorDataG γ G) (i : Fin S.m) (v : GBranch G.tree) : Prop :=
  v = (S.surv i).upper ∨ v = (S.surv i).lower

/-- `i` is the first survivor (in removal order) with joint `v` (75-F1: its bonds are the designated pair). -/
def SurvFirstJointG {γ : ℝ} {G : Garden w} (S : SurvivorDataG γ G) (i : Fin S.m) (v : GBranch G.tree) : Prop :=
  SurvJointG S i v ∧ ∀ j, j < i → ¬ SurvJointG S j v

/-- The removal order: survivors meet only index-consecutive survivors (o75 §4.6, Theorem 7.5′(7)). -/
def SurvChainOrderG {γ : ℝ} {G : Garden w} (S : SurvivorDataG γ G) : Prop :=
  ∀ i j, i ≠ j → ¬ Disjoint (S.surv i).atoms (S.surv j).atoms → i.val + 1 = j.val ∨ j.val + 1 = i.val

/-! ## The marked piece over `𝒱_γ` (main `MkDefs.Stage1MK`) -/

/-- A marked Stage-1′ piece over `𝒱_γ` (main's `Stage1PieceMK`, extending L5a's `Fama.Stage1PieceGD γ`). `nProt` is
`|Π|` of the class (o75 `b`); `surv.prot` is `Π_sb`; `lb` (ruling R187): constant lower bounds, default none. -/
structure Stage1PieceMKGD (γ : ℝ) (d R : ℕ) extends Fama.Stage1PieceGD γ d R where
  surv : SurvivorDataG γ Gsb
  nProt : ℕ
  fix : GBranch Gsb.tree → Option ℝ
  filt : GBranch Gsb.tree → Option (ℝ × SchwartzMap ℝ ℂ)
  ind : (GNode Gsb.tree → Mom d) → ℝ
  lb : GBranch Gsb.tree → Option ℝ := fun _ => none

/-- A marked piece at `γ = P.γ` (as L5a's `Fama.Stage1PieceG`). -/
abbrev Stage1PieceMKG (P : WTParams) (R : ℕ) := Stage1PieceMKGD P.γ P.d R

def Stage1PieceMKG.dataMK {P : WTParams} {R : ℕ} (π : Stage1PieceMKG P R) (tt : Fin (2 * R) → ℝ)
    (center : GardenDart π.Gsb → Mom P.d) (edge : GardenDart π.Gsb → Mom P.d → ℂ)
    (hinge : (HingeDarts π.Gsb π.Cs.hinges → Mom P.d) → ℂ)
    (freq : GBranch π.Gsb.tree → ℝ) : SplicedKernelDataMK π.Gsb P.d where
  toSplicedKernelData := Fama.Stage1PieceG.data π.toStage1PieceGD tt center edge hinge freq
  fix := π.fix
  filt := π.filt
  ind := π.ind
  lb := π.lb

/-- `RepresentsInt` with pins, survivors and the protected-object loss `L^{cP·d·nProt}` (main's
`Stage1PieceMK.RepresentsIntMK`, verbatim). -/
def Stage1PieceMKG.RepresentsIntMK {P : WTParams} {R : ℕ} (π : Stage1PieceMKG P R) (n : ℕ) (cP : ℝ)
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
    ∀ ξ, SplicedAmplitudeBounds π.Gsb
      (Fama.Stage1PieceG.data π.toStage1PieceGD tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))

/-- Structural soundness of a marked piece (enlarged marking: `N_E ≤ 6b`, `|Π_sb| ≤ 2b`; main's `SoundMK`). -/
structure SoundMKG {P : WTParams} {R : ℕ} (π : Stage1PieceMKG P R) (p : ℕ) : Prop where
  plain : π.Gsb.IsPlain
  irreducible : π.Gsb.Irreducible
  balanced : IsBalancedSig π.Gsb.sig
  order_pos : 1 ≤ π.Gsb.order
  order_le : π.Gsb.order ≤ P.N (p + 1) ^ 4
  layer_le : ∀ v, π.layer v ≤ p
  survivors : π.surv.Structural π.Cs
  survivors_card : π.surv.m ≤ 6 * π.nProt
  prot_card : π.surv.prot.card ≤ 2 * π.nProt

structure Stage1DataMKG (P : WTParams) (R : ℕ) where
  Pc : Type
  fin : Fintype Pc
  piece : Pc → Stage1PieceMKG P R
  val : Pc → ℂ

/-- The forgetful data (L5a's `Fama.Stage1DataG`), for the class count `Fama.Stage1CountsG`. -/
def Stage1DataMKG.toData {P : WTParams} {R : ℕ} (S : Stage1DataMKG P R) : Fama.Stage1DataG P R :=
  ⟨S.Pc, S.fin, fun π => (S.piece π).toStage1PieceGD, S.val⟩

/-! ## The Stage-2′ count over `𝒱_γ` (main `FinalMKDefs.Count`, interface part) -/

/-- Theorem 7.5′ (4), (5) (incl. 75-F1), (6), (6′) on one decoration (main's `SubproSupportMK`; objects over
`𝒱_γ`, `DV` read as `DV′`). -/
structure SubproSupportMKG {γ : ℝ} (G : Garden w) (C : Src.SubproChoices γ G) (S : SurvivorDataG γ G) (L γ' η : ℝ)
    (base : Mom d) (kFix : Finset (Mom d)) (κ : GardenDart G → (Fin d → ℤ)) : Prop where
  selectedSG : ∀ i, (C.collection i).HasGapKind L γ' η base κ .SG
  survivorSG : ∀ i, (S.surv i).HasGapKind L γ' η base κ .SG
  zeroTame : ∀ v, v ∉ C.hinges →
    (∃ x y, TripleAt G v x y ∧ Molecule.gapAt L base κ x y = 0) → G.molecule.IsTame L base kFix κ v
  contained : ∀ P : Src.Object γ G.molecule,
    P.HasGapKind L γ' η base κ .SG → C.OutsideAtoms P → (∀ i, ¬ P.atoms ⊆ (S.surv i).atoms) →
      Disjoint P.atoms (C.hinges ∪ S.joints) →
    (∃ S' a b, Src.IsDV γ G.molecule S' a b ∧ P.atoms ⊆ S' ∧ Disjoint S' (C.hinges ∪ S.joints) ∧
      (∀ i, Disjoint S' (C.collection i).atoms) ∧ ∀ i, Disjoint S' (S.surv i).atoms) ∨
    ∃ Q : Src.Object γ G.molecule, P.atoms ⊆ Q.atoms ∧
      (Q.HasGapKind L γ' η base κ .LG ∨ Q.HasGapKind L γ' η base κ .ZG) ∧
      Disjoint Q.atoms (C.hinges ∪ S.joints) ∧ (∀ i, Disjoint Q.atoms (C.collection i).atoms) ∧
      ∀ i, Disjoint Q.atoms (S.surv i).atoms
  hingeSG : ∀ v ∈ C.hinges, HasChosenPair (C.first v) (C.second v) (fun x y =>
    TripleAt G v x y ∧ Molecule.gapKind L γ' η (Molecule.gapAt L base κ x y) = .SG)
  hingeJoint : ∀ v ∈ C.hinges, ∀ i,
    (v = (C.collection i).upper ∨ v = (C.collection i).lower) →
      HasChosenPair (C.first v) (C.second v) (fun x y =>
        (C.collection i).ContainsDart x ∧ (C.collection i).ContainsDart y)
  jointPair : ∀ i v, SurvFirstJointG S i v →
      HasChosenPair (C.first v) (C.second v) (fun x y => (S.surv i).ContainsDart x ∧ (S.surv i).ContainsDart y)
  crossing : ∀ P : Src.Object γ G.molecule,
    P.HasGapKind L γ' η base κ .SG → C.OutsideAtoms P → (∀ i, ¬ P.atoms ⊆ (S.surv i).atoms) →
      Disjoint P.atoms S.joints → ¬ Disjoint P.atoms C.hinges →
    ∃ v ∈ C.hinges, v ∈ P.atoms ∧
      ((v ≠ P.upper ∧ v ≠ P.lower) ∨
        ((v = P.upper ∨ v = P.lower) ∧
          HasChosenPair (C.first v) (C.second v) (fun x y => Xor (P.ContainsDart x) (P.ContainsDart y))))
  meetB : ∀ P : Src.Object γ G.molecule, P.HasGapKind L γ' η base κ .SG → ¬ Disjoint P.atoms S.joints →
    (∃ i, P.atoms ⊆ (S.surv i).atoms) ∨ (∃ i x, P.ContainsDart x ∧ (S.surv i).ContainsDart x) ∨
    ∃ v ∈ C.hinges, v ∈ P.atoms ∧ ((v ≠ P.upper ∧ v ≠ P.lower) ∨
        ((v = P.upper ∨ v = P.lower) ∧
          HasChosenPair (C.first v) (C.second v) (fun x y => Xor (P.ContainsDart x) (P.ContainsDart y))))

/-- The forbidden atoms of the second collection with survivors (Theorem 7.5′(7)). -/
def forbiddenMKG {γ : ℝ} {G : Garden w} (C : Src.SubproChoices γ G) (S : SurvivorDataG γ G) :
    Set (GBranch G.tree) :=
  C.forbidden ∪ ⋃ i, (↑(S.surv i).atoms : Set (GBranch G.tree))

def SecondCollectionOKMKG {γ : ℝ} {G : Garden w} (C : Src.CountingChoices γ G d) (S : SurvivorDataG γ G)
    (L γ' η : ℝ) (base : Mom d) (κ : GardenDart G → (Fin d → ℤ)) : Prop :=
  ∃ rk : GardenDart G → ℕ, Function.Injective rk ∧ ∃ K : Set (Src.Object γ G.molecule),
    Src.IsSourceSecondCollection γ G L γ' η base κ (forbiddenMKG C.subpro S) C.omittedDVConstituents K ∧
    C.secondCollection = Src.canonicalSub rk K

/-- Requirement (f) with survivors (Theorem 7.5′(7)): SG atoms not interior to `𝒞₁ ∪ 𝒞₂ ∪ 𝒞_E`. -/
def CriticalSGMKG {γ : ℝ} {G : Garden w} (C : Src.CountingChoices γ G d) (S : SurvivorDataG γ G)
    (v : GBranch G.tree) : Prop :=
  C.CriticalSG v ∧ ∀ i, ¬ (S.surv i).IsInterior v

noncomputable def numCriticalSGMKG {γ : ℝ} {G : Garden w} (C : Src.CountingChoices γ G d)
    (S : SurvivorDataG γ G) : ℕ :=
  ((univ : Finset (GBranch G.tree)).filter (CriticalSGMKG C S)).card

/-- Requirements (b)–(f) with survivors (main's `AdmissibleMK`). -/
def AdmissibleMKG {γ : ℝ} {G : Garden w} (C : Src.CountingChoices γ G d) (S : SurvivorDataG γ G) (L γ' η : ℝ)
    (base : Mom d) (κ : GardenDart G → (Fin d → ℤ)) : Prop :=
  SubproSupportMKG G C.subpro S L γ' η base C.fixedRoots κ ∧
  SecondCollectionOKMKG C S L γ' η base κ ∧
  (∀ v, atomGapKind G L γ' η base κ v = C.atomLabel v) ∧
  (∀ v, C.atomLabel v = .SG → HasChosenPair (C.first v) (C.second v) (fun x y =>
    TripleAt G v x y ∧ Molecule.gapKind L γ' η (Molecule.gapAt L base κ x y) = .SG)) ∧
  (∀ v ∈ C.subpro.hinges, C.first v = C.subpro.first v ∧ C.second v = C.subpro.second v) ∧
  (∀ i v, (v = (C.subpro.collection i).upper ∨ v = (C.subpro.collection i).lower) →
    HasChosenPair (C.first v) (C.second v) (fun x y =>
      (C.subpro.collection i).ContainsDart x ∧ (C.subpro.collection i).ContainsDart y)) ∧
  (∀ i v, SurvFirstJointG S i v →
    HasChosenPair (C.first v) (C.second v) (fun x y => (S.surv i).ContainsDart x ∧ (S.surv i).ContainsDart y)) ∧
  (∀ P ∈ C.secondCollection, ∀ v, (v = P.upper ∨ v = P.lower) →
    HasChosenPair (C.first v) (C.second v) (fun x y => P.ContainsDart x ∧ P.ContainsDart y)) ∧
  (∀ v, CriticalSGMKG C S v → IsDyadicScale (C.atomScale v) ∧
    L⁻¹ ≤ C.atomScale v ∧ C.atomScale v ≤ L ^ (-γ' + η) ∧
    HasChosenPair (C.first v) (C.second v) (fun x y =>
      C.atomScale v / 2 ≤ ‖Molecule.gapAt L base κ x y‖ ∧
        ‖Molecule.gapAt L base κ x y‖ ≤ 2 * C.atomScale v)) ∧
  C.LadderGaps L γ' η base κ

/-- Marked admissibility (the actual ε/gap support plus `AdmissibleMKG`). -/
def splicedCountingAdmissibleMKG {γ : ℝ} (G : Garden w) (D : SplicedKernelData G d)
    (C : Src.CountingChoices γ G d) (S : SurvivorDataG γ G) (L γ' η : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (κ : GardenDart G → (Fin d → ℤ)) : Prop :=
  (∃ z : GenDecoration G d roots 0, (∀ x, bondIndex G z.1 x = κ x) ∧
    splicedEpsilon G D.hinges z.1 ≠ 0 ∧ splicedGapIndicator G D L γ' η base z.1 ≠ 0) ∧
  AdmissibleMKG C S L γ' η base κ

/-- **`FinalCountAtMKG`** (o75 (finalcount1′) over `𝒱_γ`): main's `FinalCountAtMK` with the `𝒱_γ` counting choices
`Src.CountingChoices P.γ` and survivors `SurvivorDataG P.γ`; extra `L^{2 N_E}`, the critical count excludes survivor
interiors. -/
abbrev FinalCountAtMKG (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ, 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ G : Garden (2 * R), G.IsPlain → G.Irreducible → IsBalancedSig G.sig →
    1 ≤ G.order → G.order ≤ P.N (p + 1) ^ 4 →
  ∀ (D : SplicedKernelData G P.d) (C : Src.CountingChoices P.γ G P.d) (S : SurvivorDataG P.γ G),
    D.hinges = C.subpro.hinges → Src.CountingGeometry G C → S.Structural C.subpro → SurvChainOrderG S →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
  ∀ Adm : (GardenDart G → (Fin P.d → ℤ)) → Prop,
    (∀ κ, Adm κ → splicedCountingAdmissibleMKG G D C S P.L P.γ P.η base roots κ) →
    G.molecule.countA P.L P.γ P.δ P.C₁ base Adm C.ladderScale ≤
      ENNReal.ofReal
        (P.L ^ (2 * (S.m : ℝ)) * P.L ^ (-4 * P.η ^ 6 * (G.molecule.rho + numCriticalSGMKG C S)) *
          P.L ^ (((R : ℝ) - 1) * ((P.d : ℝ) - P.γ - 1 / 4 - 1 / 40)))

/-- **The marked final-count gate for `0 < γ ≤ 1/2`** (PLAN-L8 item H's target; main's `FinalCountGateHalfMK`). -/
abbrev FinalCountGateLowMK : Prop := WTPrefix fun P => P.γ ≤ 1 / 2 → FinalCountAtMKG P

end WaveTurbulence.GammaLow.Flower
