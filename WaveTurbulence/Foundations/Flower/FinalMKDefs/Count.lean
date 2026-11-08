/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkDefs.Stage1MK
public import WaveTurbulence.Foundations.FinalCount.LowIface3
public import WaveTurbulence.Foundations.FinalCount.LowChain3
public import WaveTurbulence.Foundations.FinalCount.AsmPrefix

/-! # FINALMK-DEFS / Count (packet C1a): the Stage-2′ count statements (C0 design, SCOPE §4.1)

Copied by source from `scope/C0-FINALMK/probe/FinalMKProbe.lean` (sha256 `49bf9d1e…6025`, 939 lines), lines 1–569
(probe parts 1 and 2: survivor vocabulary, `FinalCountAtMK`, the C1a re-cut step, the C1b/C1c statements), into
namespace `WaveTurbulence.Flower.FinalMKDefs`; recorded in `COPIED-SHA256SUMS`. Only the namespace line changed. The B0
vocabulary (`SurvivorData`, `SurvivorData.joints`, `SurvivorData.Structural`) is the world's `MkDefs.Stage1MK`. -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-! C0-FINALMK probe, part 1: the Stage-2′ count, on the world's `MkDefs.SurvivorData` (R158). -/

open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs

variable {w d : ℕ}

/-- No survivors, nothing protected (on the world's `MkDefs.SurvivorData`). -/
def survEmpty (G : Garden w) : SurvivorData G := ⟨0, Fin.elim0, ∅⟩

/-- `v` is a joint of the `i`-th survivor. -/
def SurvJoint {G : Garden w} (S : SurvivorData G) (i : Fin S.m) (v : GBranch G.tree) : Prop :=
  v = (S.surv i).upper ∨ v = (S.surv i).lower

/-- `i` is the first survivor (in removal order) with joint `v` (75-F1: its bonds are the designated pair). -/
def SurvFirstJoint {G : Garden w} (S : SurvivorData G) (i : Fin S.m) (v : GBranch G.tree) : Prop :=
  SurvJoint S i v ∧ ∀ j, j < i → ¬ SurvJoint S j v

/-- **The removal order (C0 design, new)**: survivors meet only index-consecutive survivors (chain order of o75 §4.6
and Thm 7.5′(7)), so each survivor removal re-cuts at most one joint. B2c/B4 list the survivors chain by chain. -/
def SurvChainOrder {G : Garden w} (S : SurvivorData G) : Prop :=
  ∀ i j, i ≠ j → ¬ Disjoint (S.surv i).atoms (S.surv j).atoms → i.val + 1 = j.val ∨ j.val + 1 = i.val

theorem chainOrder_empty (G : Garden w) : SurvChainOrder (survEmpty G) := fun i => Fin.elim0 i

theorem structural_empty {G : Garden w} (C : SubproChoices G) : (survEmpty G).Structural C :=
  ⟨fun i => Fin.elim0 i, fun _ j => Fin.elim0 j, fun i => Fin.elim0 i, fun _ _ i => Fin.elim0 i⟩

/-- Theorem 7.5′ (4), (5) (incl. 75-F1), (6), (6′) on one decoration. -/
structure SubproSupportMK (G : Garden w) (C : SubproChoices G) (S : SurvivorData G) (L γ η : ℝ)
    (base : Mom d) (kFix : Finset (Mom d)) (κ : GardenDart G → (Fin d → ℤ)) : Prop where
  selectedSG : ∀ i, (C.collection i).HasGapKind L γ η base κ .SG
  survivorSG : ∀ i, (S.surv i).HasGapKind L γ η base κ .SG
  zeroTame : ∀ v, v ∉ C.hinges →
    (∃ x y, TripleAt G v x y ∧ Molecule.gapAt L base κ x y = 0) → G.molecule.IsTame L base kFix κ v
  contained : ∀ P : Object G.molecule,
    P.HasGapKind L γ η base κ .SG → C.OutsideAtoms P → (∀ i, ¬ P.atoms ⊆ (S.surv i).atoms) →
      Disjoint P.atoms (C.hinges ∪ S.joints) →
    (∃ S' a b, IsDV G.molecule S' a b ∧ P.atoms ⊆ S' ∧ Disjoint S' (C.hinges ∪ S.joints) ∧
      (∀ i, Disjoint S' (C.collection i).atoms) ∧ ∀ i, Disjoint S' (S.surv i).atoms) ∨
    ∃ Q : Object G.molecule, P.atoms ⊆ Q.atoms ∧
      (Q.HasGapKind L γ η base κ .LG ∨ Q.HasGapKind L γ η base κ .ZG) ∧
      Disjoint Q.atoms (C.hinges ∪ S.joints) ∧ (∀ i, Disjoint Q.atoms (C.collection i).atoms) ∧
      ∀ i, Disjoint Q.atoms (S.surv i).atoms
  hingeSG : ∀ v ∈ C.hinges, HasChosenPair (C.first v) (C.second v) (fun x y =>
    TripleAt G v x y ∧ Molecule.gapKind L γ η (Molecule.gapAt L base κ x y) = .SG)
  hingeJoint : ∀ v ∈ C.hinges, ∀ i,
    (v = (C.collection i).upper ∨ v = (C.collection i).lower) →
      HasChosenPair (C.first v) (C.second v) (fun x y =>
        (C.collection i).ContainsDart x ∧ (C.collection i).ContainsDart y)
  jointPair : ∀ i v, SurvFirstJoint S i v →
      HasChosenPair (C.first v) (C.second v) (fun x y => (S.surv i).ContainsDart x ∧ (S.surv i).ContainsDart y)
  crossing : ∀ P : Object G.molecule,
    P.HasGapKind L γ η base κ .SG → C.OutsideAtoms P → (∀ i, ¬ P.atoms ⊆ (S.surv i).atoms) →
      Disjoint P.atoms S.joints → ¬ Disjoint P.atoms C.hinges →
    ∃ v ∈ C.hinges, v ∈ P.atoms ∧
      ((v ≠ P.upper ∧ v ≠ P.lower) ∨
        ((v = P.upper ∨ v = P.lower) ∧
          HasChosenPair (C.first v) (C.second v) (fun x y => Xor (P.ContainsDart x) (P.ContainsDart y))))
  meetB : ∀ P : Object G.molecule, P.HasGapKind L γ η base κ .SG → ¬ Disjoint P.atoms S.joints →
    (∃ i, P.atoms ⊆ (S.surv i).atoms) ∨ (∃ i x, P.ContainsDart x ∧ (S.surv i).ContainsDart x) ∨
    ∃ v ∈ C.hinges, v ∈ P.atoms ∧ ((v ≠ P.upper ∧ v ≠ P.lower) ∨
        ((v = P.upper ∨ v = P.lower) ∧
          HasChosenPair (C.first v) (C.second v) (fun x y => Xor (P.ContainsDart x) (P.ContainsDart y))))

theorem joints_empty {G : Garden w} : (survEmpty G).joints = ∅ := by
  ext x; simp [SurvivorData.joints, survEmpty]

theorem subproSupportMK_of_empty (G : Garden w) (C : SubproChoices G) (L γ η : ℝ)
    (base : Mom d) (kFix : Finset (Mom d)) (κ : GardenDart G → (Fin d → ℤ))
    (h : SubproSupport G C L γ η base kFix κ) :
    SubproSupportMK G C (survEmpty G) L γ η base kFix κ := by
  have hj := joints_empty (G := G)
  refine ⟨h.selectedSG, fun i => Fin.elim0 i, h.zeroTame, ?_, h.hingeSG, h.hingeJoint,
    fun i => Fin.elim0 i, ?_, ?_⟩
  · intro P hP hout _ hdis
    rw [hj, Finset.union_empty] at hdis ⊢
    rcases h.contained P hP hout hdis with ⟨S', a, b, h1, h2, h3, h4⟩ | ⟨Q, h1, h2, h3, h4⟩
    · exact Or.inl ⟨S', a, b, h1, h2, h3, h4, fun i => Fin.elim0 i⟩
    · exact Or.inr ⟨Q, h1, h2, h3, h4, fun i => Fin.elim0 i⟩
  · intro P hP hout _ _ hmeet
    exact h.crossing P hP hout hmeet
  · intro P _ hmeet
    rw [hj] at hmeet
    simp at hmeet

/-- The forbidden atoms of the second collection with survivors (Theorem 7.5′(7): `𝒞₂` from the containers of (4),
disjoint from `𝒞₁ ∪ 𝒞_E` and `H ∪ B`; `B` ⊆ survivor atoms). -/
def forbiddenMK {G : Garden w} (C : SubproChoices G) (S : SurvivorData G) : Set (GBranch G.tree) :=
  C.forbidden ∪ ⋃ i, (↑(S.surv i).atoms : Set (GBranch G.tree))

theorem forbiddenMK_empty {G : Garden w} (C : SubproChoices G) :
    forbiddenMK C (survEmpty G) = C.forbidden := by
  simp [forbiddenMK, survEmpty]

def SecondCollectionOKMK {G : Garden w} (C : CountingChoices G d) (S : SurvivorData G) (L γ η : ℝ)
    (base : Mom d) (κ : GardenDart G → (Fin d → ℤ)) : Prop :=
  ∃ rk : GardenDart G → ℕ, Function.Injective rk ∧ ∃ K : Set (Object G.molecule),
    IsSourceSecondCollection G L γ η base κ (forbiddenMK C.subpro S) C.omittedDVConstituents K ∧
    C.secondCollection = canonicalSub rk K

/-- Requirement (f) with survivors (Theorem 7.5′(7)): SG atoms not interior to `𝒞₁ ∪ 𝒞₂ ∪ 𝒞_E`. -/
def CriticalSGMK {G : Garden w} (C : CountingChoices G d) (S : SurvivorData G) (v : GBranch G.tree) : Prop :=
  C.CriticalSG v ∧ ∀ i, ¬ (S.surv i).IsInterior v

noncomputable def numCriticalSGMK {G : Garden w} (C : CountingChoices G d) (S : SurvivorData G) : ℕ :=
  ((univ : Finset (GBranch G.tree)).filter (CriticalSGMK C S)).card

theorem numCriticalSGMK_empty {G : Garden w} (C : CountingChoices G d) :
    numCriticalSGMK C (survEmpty G) = C.numCriticalSG := by
  unfold numCriticalSGMK CountingChoices.numCriticalSG CriticalSGMK
  congr 1
  ext v
  simp [survEmpty]

/-- Requirements (b)–(f) with survivors. -/
def AdmissibleMK {G : Garden w} (C : CountingChoices G d) (S : SurvivorData G) (L γ η : ℝ)
    (base : Mom d) (κ : GardenDart G → (Fin d → ℤ)) : Prop :=
  SubproSupportMK G C.subpro S L γ η base C.fixedRoots κ ∧
  SecondCollectionOKMK C S L γ η base κ ∧
  (∀ v, atomGapKind G L γ η base κ v = C.atomLabel v) ∧
  (∀ v, C.atomLabel v = .SG → HasChosenPair (C.first v) (C.second v) (fun x y =>
    TripleAt G v x y ∧ Molecule.gapKind L γ η (Molecule.gapAt L base κ x y) = .SG)) ∧
  (∀ v ∈ C.subpro.hinges, C.first v = C.subpro.first v ∧ C.second v = C.subpro.second v) ∧
  (∀ i v, (v = (C.subpro.collection i).upper ∨ v = (C.subpro.collection i).lower) →
    HasChosenPair (C.first v) (C.second v) (fun x y =>
      (C.subpro.collection i).ContainsDart x ∧ (C.subpro.collection i).ContainsDart y)) ∧
  (∀ i v, SurvFirstJoint S i v →
    HasChosenPair (C.first v) (C.second v) (fun x y => (S.surv i).ContainsDart x ∧ (S.surv i).ContainsDart y)) ∧
  (∀ P ∈ C.secondCollection, ∀ v, (v = P.upper ∨ v = P.lower) →
    HasChosenPair (C.first v) (C.second v) (fun x y => P.ContainsDart x ∧ P.ContainsDart y)) ∧
  (∀ v, CriticalSGMK C S v → IsDyadicScale (C.atomScale v) ∧
    L⁻¹ ≤ C.atomScale v ∧ C.atomScale v ≤ L ^ (-γ + η) ∧
    HasChosenPair (C.first v) (C.second v) (fun x y =>
      C.atomScale v / 2 ≤ ‖Molecule.gapAt L base κ x y‖ ∧
        ‖Molecule.gapAt L base κ x y‖ ≤ 2 * C.atomScale v)) ∧
  C.LadderGaps L γ η base κ

theorem admissibleMK_of_empty {G : Garden w} (C : CountingChoices G d) (L γ η : ℝ) (base : Mom d)
    (κ : GardenDart G → (Fin d → ℤ)) (h : C.Admissible L γ η base κ) :
    AdmissibleMK C (survEmpty G) L γ η base κ := by
  obtain ⟨h1, ⟨rk, hrk, K, hK, hC⟩, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨subproSupportMK_of_empty G C.subpro L γ η base C.fixedRoots κ h1,
    ⟨rk, hrk, K, by rw [forbiddenMK_empty]; exact hK, hC⟩, h3, h4, h5, h6, fun i => Fin.elim0 i, h7,
    fun v hv => h8 v hv.1, h9⟩

/-- Marked admissibility (the actual ε/gap support plus `AdmissibleMK`). -/
def splicedCountingAdmissibleMK (G : Garden w) (D : SplicedKernelData G d)
    (C : CountingChoices G d) (S : SurvivorData G) (L γ η : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (κ : GardenDart G → (Fin d → ℤ)) : Prop :=
  (∃ z : GenDecoration G d roots 0, (∀ x, bondIndex G z.1 x = κ x) ∧
    splicedEpsilon G D.hinges z.1 ≠ 0 ∧ splicedGapIndicator G D L γ η base z.1 ≠ 0) ∧
  AdmissibleMK C S L γ η base κ

/-- **FinalCountAtMK** (o75 (finalcount1′)): `FinalCountAt` with survivors; extra `L^{2 N_E}`, the critical count
excludes survivor interiors. -/
abbrev FinalCountAtMK (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ, 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ G : Garden (2 * R), G.IsPlain → G.Irreducible → IsBalancedSig G.sig →
    1 ≤ G.order → G.order ≤ P.N (p + 1) ^ 4 →
  ∀ (D : SplicedKernelData G P.d) (C : CountingChoices G P.d) (S : SurvivorData G),
    D.hinges = C.subpro.hinges → CountingGeometry G C → S.Structural C.subpro → SurvChainOrder S →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
  ∀ Adm : (GardenDart G → (Fin P.d → ℤ)) → Prop,
    (∀ κ, Adm κ → splicedCountingAdmissibleMK G D C S P.L P.γ P.η base roots κ) →
    G.molecule.countA P.L P.γ P.δ P.C₁ base Adm C.ladderScale ≤
      ENNReal.ofReal
        (P.L ^ (2 * (S.m : ℝ)) * P.L ^ (-4 * P.η ^ 6 * (G.molecule.rho + numCriticalSGMK C S)) *
          P.L ^ (((R : ℝ) - 1) * ((P.d : ℝ) - P.γ - 1 / 4 - 1 / 40)))

/-- The C1 deliverable (the gate, `γ > 1/2` as on main). -/
abbrev FinalCountGateHalfMK : Prop := WTPrefix fun P => 1 / 2 < P.γ → FinalCountAtMK P

/-- **Non-vacuity bridge**: at no survivors `FinalCountAtMK` is `FinalCountAt`. -/
theorem finalCountAt_of_MK (P : WTParams) (h : FinalCountAtMK P) : FinalCountAt P := by
  intro p hp R h1 h2 G hpl hirr hbal ho1 ho2 D C hD hgeo base roots Adm hAdm
  have := h p hp R h1 h2 G hpl hirr hbal ho1 ho2 D C (survEmpty G) hD hgeo
    (structural_empty C.subpro) (chainOrder_empty G) base roots Adm (fun κ hκ => by
      obtain ⟨hz, hadm⟩ := hAdm κ hκ
      exact ⟨hz, admissibleMK_of_empty C P.L P.γ P.η base κ hadm⟩)
  rw [numCriticalSGMK_empty] at this
  simpa [survEmpty] using this

theorem finalCountGateHalf_of_MK (h : FinalCountGateHalfMK) : FinalCountGateHalf := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, h⟩ := h d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin hφin τ hτ φ hφ => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, h⟩ := h η hη φin hφin τ hτ φ hφ
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, h⟩ := h ν hν
  refine ⟨δ₀, hδ₀, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, h⟩ := h δ hδ D hD hτD
  exact ⟨C₂, hC₂, L₀, hL₀, fun L hL hγ' => finalCountAt_of_MK _ (h L hL hγ')⟩


/-! C0-FINALMK probe, part 2: C1 internal statements (LOW chain with survivors). Appended after part 1. -/
section C1
open WaveTurbulence.VineParamContract
open WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.VineCount WaveTurbulence.FinalCountAsm
open Set (Ioo Ioc)

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-! ### C1a: the re-cut step (o75 75-F2) on main's run vocabulary -/

/-- **C1a. The re-cut step on a class** (o75 Lemma 5 + 75-F2): Step 1 at a survivor whose joints are each either
`ε` or an `α/β` remnant of degree `2` (an already cut shared joint), at least one of them a remnant. The post state is
main's `vinePostG` (both cuts, ghost halves of degree-`2` joints and the object deleted). Same data as main's
`UStepD1` except the joint-class clauses. -/
inductive UStepRC {M₀ : Molecule V D₀} (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (Adm0 : (D₀ → (Fin d → ℤ)) → Prop) :
    HSt V D₀ → HSt V D₀ → Prop
  | vine (h : HSt V D₀) (K : VineCut h.s.M)
      (hu : h.s.cls K.C.upper = .eps ∨ ((h.s.cls K.C.upper).IsAB ∧ h.s.M.deg K.C.upper = 2))
      (hl : h.s.cls K.C.lower = .eps ∨ ((h.s.cls K.C.lower).IsAB ∧ h.s.M.deg K.C.lower = 2))
      (hrc : h.s.cls K.C.upper ≠ .eps ∨ h.s.cls K.C.lower ≠ .eps)
      (htwin : ∀ k0, Adm0 k0 → (pgap L w k0 (h.s.pr K.y₁ K.y₂) = pgap L w k0 (h.s.pr K.x₁ K.x₂) ∨
        pgap L w k0 (h.s.pr K.y₁ K.y₂) = -pgap L w k0 (h.s.pr K.x₁ K.x₂)))
      (hsg : ∀ k0, Adm0 k0 → Molecule.gapKind L γ η (Molecule.gapAt L w (k0 ∘ h.s.down) K.x₁ K.x₂) = .SG)
      (hdu : Desig C (h.anc K.C.upper) (h.s.pr K.x₁ K.x₂)) (hdl : Desig C (h.anc K.C.lower) (h.s.pr K.y₁ K.y₂)) :
      UStepRC C L γ η w Adm0 h (h.vinePostG K)

/-- The re-cut step for one decoration (the `HStepD1` analogue). -/
inductive HStepRC {M₀ : Molecule V D₀} (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) :
    HSt V D₀ → HSt V D₀ → Prop
  | vine (h : HSt V D₀) (K : VineCut h.s.M)
      (hu : h.s.cls K.C.upper = .eps ∨ ((h.s.cls K.C.upper).IsAB ∧ h.s.M.deg K.C.upper = 2))
      (hl : h.s.cls K.C.lower = .eps ∨ ((h.s.cls K.C.lower).IsAB ∧ h.s.M.deg K.C.lower = 2))
      (hrc : h.s.cls K.C.upper ≠ .eps ∨ h.s.cls K.C.lower ≠ .eps)
      (htwin : pgap L w κ (h.s.pr K.y₁ K.y₂) = pgap L w κ (h.s.pr K.x₁ K.x₂) ∨
        pgap L w κ (h.s.pr K.y₁ K.y₂) = -pgap L w κ (h.s.pr K.x₁ K.x₂))
      (hsg : Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ h.s.down) K.x₁ K.x₂) = .SG)
      (hdu : Desig C (h.anc K.C.upper) (h.s.pr K.x₁ K.x₂)) (hdl : Desig C (h.anc K.C.lower) (h.s.pr K.y₁ K.y₂)) :
      HStepRC C L γ η w κ h (h.vinePostG K)

theorem UStepRC.hstep {M₀ : Molecule V D₀} {C : CollData M₀} {L γ η : ℝ} {w : Mom d}
    {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} {κ : D₀ → (Fin d → ℤ)} {h h' : HSt V D₀}
    (hs : UStepRC C L γ η w Adm0 h h') (hk : Adm0 κ) : HStepRC C L γ η w κ h h' := by
  cases hs with
  | vine K hu hl hrc htwin hsg hdu hdl => exact HStepRC.vine h K hu hl hrc (htwin κ hk) (hsg κ hk) hdu hdl

/-- **C1a target 1: the re-cut deviation** (o75 75-F2 "bound for the re-cut step"; `Ex1D` with `UStepRC`). The RHS is
main's D1 RHS `excessRHS2 L γ η [] 1 2 = L^{γ₀+η²-η³} ≥ L^{γ₀+2η³}` (o75's bound). Proof route: `ex1D_uniform`'s, from
the class-free count `prop94_vine_newcomp`. -/
def Ex1RC (L γ η δ C₁ : ℝ) (w : Mom d) (M₀ : Molecule V D₀) (C : CollData M₀) (P : Finset V → ℝ) (CD ν : ℝ) : Prop :=
  (∀ S, 0 ≤ P S) → LadderHered M₀ P → M₀.IsMolecule →
  ∀ (Adm0 : (D₀ → (Fin d → ℤ)) → Prop), (∃ k0, Adm0 k0) → (∀ k0, Adm0 k0 → SourceLadderGaps M₀ L w P k0) →
    (∀ k0, Adm0 k0 → ∃ c0, M₀.IsDecoration L w c0 k0 ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0) →
    ∀ {h h' : HSt V D₀}, UStepRC C L γ η w Adm0 h h' → LCtx M₀ h.s → AtomRelU Adm0 L w h → h.s.M.IsMolecule →
      (∀ x, h.s.M.atom x ≠ h.s.M.atom (h.s.M.mate x)) → (h.s.M.atoms.card : ℝ) ≤ ν →
      ∃ (K : VineCut h.s.M), h' = h.vinePostG K ∧
        ((SingleVineVC K ∨ Nonempty (DoubleShape K)) →
        (Nonempty (DoubleShape K) →
          ∃ G : Finset h.s.D, (∀ z ∈ ({K.x₁, K.x₂, K.y₁, K.y₂} : Finset h.s.D), z ∈ G) ∧ VineOutsideConn K G) →
          IsDeviation (h.s.M.countA L γ δ C₁ w (AdmS Adm0 h.s) P) (h'.s.M.countA L γ δ C₁ w (AdmS Adm0 h'.s) P)
            (ENNReal.ofReal (CD * excessRHS2 L γ η [] 1 2)))

/-- **C1a target 2 (statement): the uniform re-cut deviation**, the `ex1D_uniform` form. -/
def Ex1RCUniform (d : ℕ) : Prop :=
  ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
    ∃ Cs C₂ : ℝ, 0 ≤ Cs ∧ 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ C₁ η ν : ℝ, C₂ ≤ C₁ → 0 < η → η < 1 → 1 ≤ ν →
      ∀ {V D₀ : Type} [DecidableEq V] [Fintype D₀] [DecidableEq D₀] (w : Mom d) (M₀ : Molecule V D₀) (C : CollData M₀)
        (P : Finset V → ℝ),
      Ex1RC L γ η δ C₁ w M₀ C P (Cs * ν * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8)) ν

/-- **C1a target 3: the invariant along a re-cut** (index non-increasing; it drops only at an `ε` joint of degree 2). -/
def InvLStepRC (M₀ : Molecule V D₀) (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) : Prop :=
  ∀ {R : ℕ} {h h' : HSt V D₀}, HStepRC C L γ η w κ h h' → InvL M₀ R L γ η w κ h →
    ∃ R', R' ≤ R ∧ InvL M₀ R' L γ η w κ h'

/-- The LOW run's Step-1 step with re-cuts (`HStep1L` of GL6 plus `HStepRC`). -/
inductive HStep1LE {M₀ : Molecule V D₀} (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) :
    HSt V D₀ → HSt V D₀ → Prop
  | base {h h' : HSt V D₀} (hs : HStep1L C L γ η w κ h h') : HStep1LE C L γ η w κ h h'
  | recut {h h' : HSt V D₀} (hs : HStepRC C L γ η w κ h h') : HStep1LE C L γ η w κ h h'

/-- **The LOW run with re-cuts** (main's `HRunL`, GL6, with `HStep1LE` in Operation 1). C1a proves the run-level facts of
G3-LOWDEG (`HRunL.inv`, `prop95L`, `no_SGL` inputs) for it. -/
def HRunLE {M₀ : Molecule V D₀} (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (h₀ hf : HSt V D₀) : Prop :=
  ∃ h₁ h₂ h₃ h₄ : HSt V D₀,
    Relation.ReflTransGen (HStep1LE C L γ η w κ) h₀ h₁ ∧ NoTripleCut C L γ η w κ h₁ ∧
    Relation.ReflTransGen (HStepD3 C L γ η w κ) h₁ h₂ ∧ NoD3 C L w κ h₂ ∧
    Relation.ReflTransGen (HStep2C C L γ η w κ) h₂ h₃ ∧ NoEligibleTriangle C L γ η w κ h₃ ∧
    Relation.ReflTransGen (HStep3C C L γ η w κ) h₃ h₄ ∧ NoSGLeft L γ η w κ h₀.s h₄.s ∧
    Relation.ReflTransGen (HStep4 L w κ) h₄ hf ∧ NoBetaCut L w κ hf.s

theorem HRunL.toE {M₀ : Molecule V D₀} {C : CollData M₀} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}
    {h₀ hf : HSt V D₀} (h : HRunL C L γ η w κ h₀ hf) : HRunLE C L γ η w κ h₀ hf := by
  obtain ⟨h₁, h₂, h₃, h₄, a, b, c, e, f, g, i, j, k, l⟩ := h
  exact ⟨h₁, h₂, h₃, h₄, Relation.ReflTransGen.mono (fun _ _ hs => HStep1LE.base hs) _ _ a, b, c, e, f, g, i, j, k, l⟩

/-! ### C1b: survivors in the LOW Step 1 (molecule level) -/

section mol
variable {M₀ : Molecule V D₀} {m : ℕ}

/-- Molecule-level survivor joints `B`. -/
noncomputable def survJointsM (E : Fin m → Object M₀) : Finset V :=
  Finset.univ.biUnion fun i => {(E i).upper, (E i).lower}

/-- `i` is the first survivor (removal order) with joint `v`. -/
def SurvFirstJointM (E : Fin m → Object M₀) (i : Fin m) (v : V) : Prop :=
  (v = (E i).upper ∨ v = (E i).lower) ∧ ∀ j, j < i → ¬ (v = (E j).upper ∨ v = (E j).lower)

/-- The cut `K` removes the survivor `E i` (node darts in `E i`, at its joints): `HStep1R`'s `hUK hUD hUJ`, with the
atoms compared through the ancestor map (R164, C1b1's F-C1b1-1): after the earlier survivor at a shared joint `v` is
removed, `E i`'s darts at `v` sit on the fresh remnant `K.fa`/`K.fb` with `anc = v`; on an intact survivor `anc = id`. -/
def SurvCut (E : Fin m → Object M₀) (i : Fin m) (h : HSt V D₀) (K : VineCut h.s.M) : Prop :=
  (E i).atoms = K.C.atoms.image h.anc ∧
  ((E i).ContainsDart (h.s.down K.x₁) ∧ (E i).ContainsDart (h.s.down K.x₂) ∧ (E i).ContainsDart (h.s.down K.y₁) ∧
    (E i).ContainsDart (h.s.down K.y₂)) ∧
  ((M₀.atom (h.s.down K.x₁) = (E i).upper ∧ M₀.atom (h.s.down K.y₁) = (E i).lower) ∨
    (M₀.atom (h.s.down K.x₁) = (E i).lower ∧ M₀.atom (h.s.down K.y₁) = (E i).upper))

/-- Removal order (o75 Thm 7.5′(7)): survivors after the first stage, in index (chain) order. -/
def SurvOrder (Fst : Set (Object M₀)) (E : Fin m → Object M₀) (i : Fin m) (h : HSt V D₀) : Prop :=
  (∀ U' ∈ Fst, Dartless U' h) ∧ ∀ j, j < i → Dartless (E j) h

/-! #### The forbidden pool (R164 (a)): the molecule-level second collection avoids the survivor atoms -/

/-- Molecule-level survivor atoms (the survivor part of the garden's `forbiddenMK`). -/
noncomputable def survAtomsM (E : Fin m → Object M₀) : Finset V :=
  Finset.univ.biUnion fun i => (E i).atoms

/-- **MK collection data**: main's `CollData` plus the forbidden atoms `forb` of the second collection (hinges
unchanged). `LowLoopClassHypsMK` pins `forb = survAtomsM E`. -/
structure CollDataMK (M₀ : Molecule V D₀) extends CollData M₀ where
  forb : Finset V

/-- Main's `CollData.Host` with the containers also avoiding `forb`. -/
def CollDataMK.HostF (C : CollDataMK M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (P : Object M₀) : Prop :=
  (∃ S a b, IsDV M₀ S a b ∧ P.atoms ⊆ S ∧ Disjoint S (C.hinges ∪ C.forb) ∧ ∀ i, Disjoint S (C.collection i).atoms) ∨
    ∃ Q : Object M₀, P.atoms ⊆ Q.atoms ∧
      (Q.HasGapKind L γ η w κ .LG ∨ Q.HasGapKind L γ η w κ .ZG) ∧
      Disjoint Q.atoms (C.hinges ∪ C.forb) ∧ ∀ i, Disjoint Q.atoms (C.collection i).atoms

/-- Main's pool `CollData.InP`, avoiding `forb`. -/
def CollDataMK.InPF (C : CollDataMK M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (P : Object M₀) : Prop :=
  P.HasGapKind L γ η w κ .SG ∧ C.Outside P ∧ Disjoint P.atoms (C.hinges ∪ C.forb) ∧ C.HostF L γ η w κ P

/-- Main's `CollData.C2Of` on the forbidden pool. -/
def CollDataMK.C2OfF (C : CollDataMK M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (Unsel : Set (Object M₀)) :
    Set (Object M₀) :=
  {U | (C.InPF L γ η w κ U ∧ U ∉ Unsel) ∧
    ∀ Q, (C.InPF L γ η w κ Q ∧ Q ∉ Unsel) → U.atoms ⊆ Q.atoms → Q.atoms ⊆ U.atoms}

/-- Main's `CollData.C2Can` (one designation per atom set) on the forbidden pool. -/
def CollDataMK.C2CanF (C : CollDataMK M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (Unsel : Set (Object M₀)) :
    Set (Object M₀) :=
  {U | U ∈ C.C2OfF L γ η w κ Unsel ∧ ∀ Q ∈ C.C2OfF L γ η w κ Unsel, Q.atoms = U.atoms → (∃ R, U.shape = .hyper R) →
    (∃ R, Q.shape = .hyper R) → U.hyperRankG ≤ Q.hyperRankG}

/-- Main's `Collected` (`𝒞₁` and `𝒞₂`) on the forbidden pool. -/
def CollectedF (C : CollDataMK M₀) (Un : Set (Object M₀)) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ))
    (U : Object M₀) : Prop :=
  (∃ i, U = C.collection i) ∨ U ∈ C.C2CanF L γ η w κ Un

/-- Main's `CollData.UnselOK` on the forbidden pool. -/
structure CollDataMK.UnselOKF (C : CollDataMK M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ))
    (Unsel : Set (Object M₀)) : Prop where
  dv : ∀ B ∈ Unsel, C.InPF L γ η w κ B ∧ ((∃ U ∈ C.C2CanF L γ η w κ Unsel, B.atoms ⊆ U.atoms) ∨
    ∃ A a b, M₀.IsVine .V A a b ∧ M₀.IsVine .V B.atoms a b ∧ A ∩ B.atoms = {a, b} ∧
    ∃ U ∈ C.C2CanF L γ η w κ Unsel, U.atoms = A ∧ ∃ h, U.shape = VineLikeObject.vc h)

/-- Main's `PieceData` with `CollectedF`. -/
def PieceDataF (C : CollDataMK M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)) (L γ η : ℝ) (w : Mom d)
    (κ : D₀ → (Fin d → ℤ)) (p : Object M₀ × Quad D₀) : Prop :=
  CollectedF C (Un κ) L γ η w κ p.1 ∧
    (p.1.ContainsDart p.2.1 ∧ p.1.ContainsDart p.2.2.1 ∧ p.1.ContainsDart p.2.2.2.1 ∧ p.1.ContainsDart p.2.2.2.2) ∧
    ((M₀.atom p.2.1 = p.1.upper ∧ M₀.atom p.2.2.2.1 = p.1.lower) ∨
      (M₀.atom p.2.1 = p.1.lower ∧ M₀.atom p.2.2.2.1 = p.1.upper)) ∧
    (M₀.atom p.2.2.1 = M₀.atom p.2.1 ∧ M₀.atom p.2.2.2.2 = M₀.atom p.2.2.2.1 ∧ p.2.1 ≠ p.2.2.1 ∧ p.2.2.2.1 ≠ p.2.2.2.2)

/-- Main's `CnBound` (`AsmEnd3`) on the forbidden pool (R164b, C1b1's F-C1b1-2): the first-stage pieces are
`PieceDataF` (`fst : Fst ⊆ CollectedF`), and `C2CanF ⊄ C2Can`. -/
def CnBoundF (M₀ : Molecule V D₀) (C : CollDataMK M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀))
    (Fst : Set (Object M₀)) (L γ η : ℝ) (w : Mom d) (A0 : Set (D₀ → (Fin d → ℤ))) (Rn : ℕ) : Prop :=
  ∀ κ ∈ A0, ∀ ps : List (Object M₀ × Quad D₀), (∀ p ∈ ps, PieceDataF C Un L γ η w κ p ∧ p.1 ∈ Fst) →
    ps.Pairwise (fun p q => Disjoint p.1.atoms q.1.atoms) →
    (remMol M₀ ps).numComponents ≤ 2 * Rn ∧
      ((remMol M₀ ps).numComponents = 2 * Rn → ∃ v ∈ (remMol M₀ ps).atoms, (remMol M₀ ps).deg v = 0)

/-- **C1b. The LOW restricted Step 1 with survivors** (R164: over `CollDataMK`): main's `HStep1R`/`HStep1RL`
constructors with `CollectedF` (triple cuts only once every collected object and every survivor is gone), plus
survivor removals by an ordinary vine cut, a Step D1 cut, or a re-cut. -/
inductive HStep1RLE (C : CollDataMK M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)) (Fst : Set (Object M₀))
    (E : Fin m → Object M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) : HSt V D₀ → HSt V D₀ → Prop
  | vine (h : HSt V D₀) (K : VineCut h.s.M) (R : ℝ) (kp : ℕ)
      (hs : HStep1C C.toCollData L γ η w κ h (h.vinePost K R kp))
      (U : Object M₀) (hU : CollectedF C (Un κ) L γ η w κ U) (hUK : U.atoms = K.C.atoms)
      (hUD : U.ContainsDart (h.s.down K.x₁) ∧ U.ContainsDart (h.s.down K.x₂) ∧ U.ContainsDart (h.s.down K.y₁) ∧
        U.ContainsDart (h.s.down K.y₂))
      (hUJ : (M₀.atom (h.s.down K.x₁) = U.upper ∧ M₀.atom (h.s.down K.y₁) = U.lower) ∨
        (M₀.atom (h.s.down K.x₁) = U.lower ∧ M₀.atom (h.s.down K.y₁) = U.upper))
      (hord : U ∈ Fst ∨ ∀ U' ∈ Fst, Dartless U' h) : HStep1RLE C Un Fst E L γ η w κ h (h.vinePost K R kp)
  | d1 (h : HSt V D₀) (K : VineCut h.s.M) (hs : HStepD1 C.toCollData L γ η w κ h (h.vinePostG K))
      (U : Object M₀) (hU : CollectedF C (Un κ) L γ η w κ U) (hUK : U.atoms = K.C.atoms)
      (hUD : U.ContainsDart (h.s.down K.x₁) ∧ U.ContainsDart (h.s.down K.x₂) ∧ U.ContainsDart (h.s.down K.y₁) ∧
        U.ContainsDart (h.s.down K.y₂))
      (hUJ : (M₀.atom (h.s.down K.x₁) = U.upper ∧ M₀.atom (h.s.down K.y₁) = U.lower) ∨
        (M₀.atom (h.s.down K.x₁) = U.lower ∧ M₀.atom (h.s.down K.y₁) = U.upper))
      (hord : U ∈ Fst ∨ ∀ U' ∈ Fst, Dartless U' h) : HStep1RLE C Un Fst E L γ η w κ h (h.vinePostG K)
  | triple (h h' : HSt V D₀) (hs : HStep1C C.toCollData L γ η w κ h h') (hs3 : HStep3C C.toCollData L γ η w κ h h')
      (hall : ∀ U, CollectedF C (Un κ) L γ η w κ U → Dartless U h) (hallE : ∀ i, Dartless (E i) h)
      (hF : h'.s.M.numComponents ≤ h.s.M.numComponents) : HStep1RLE C Un Fst E L γ η w κ h h'
  | survVine (h : HSt V D₀) (K : VineCut h.s.M) (R : ℝ) (kp : ℕ) (i : Fin m)
      (hs : HStep1C C.toCollData L γ η w κ h (h.vinePost K R kp)) (hc : SurvCut E i h K) (ho : SurvOrder Fst E i h) :
      HStep1RLE C Un Fst E L γ η w κ h (h.vinePost K R kp)
  | survD1 (h : HSt V D₀) (K : VineCut h.s.M) (i : Fin m)
      (hs : HStepD1 C.toCollData L γ η w κ h (h.vinePostG K)) (hc : SurvCut E i h K) (ho : SurvOrder Fst E i h) :
      HStep1RLE C Un Fst E L γ η w κ h (h.vinePostG K)
  | survRC (h : HSt V D₀) (K : VineCut h.s.M) (i : Fin m)
      (hs : HStepRC C.toCollData L γ η w κ h (h.vinePostG K)) (hc : SurvCut E i h K) (ho : SurvOrder Fst E i h) :
      HStep1RLE C Un Fst E L γ η w κ h (h.vinePostG K)

/-- Reach of the survivor-aware Step 1. -/
def Reach1LE (C : CollDataMK M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)) (Fst : Set (Object M₀))
    (E : Fin m → Object M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀) : Prop :=
  Relation.ReflTransGen (HStep1RLE C Un Fst E L γ η w κ) (HSt.init M₀) h

/-- Step 1 with survivors is stuck: no triple cut, every `CollectedF` object and every survivor removed. -/
def Stuck1E (C : CollDataMK M₀) (L γ η : ℝ) (w : Mom d) (Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀))
    (E : Fin m → Object M₀) (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀) : Prop :=
  NoTripleCut C.toCollData L γ η w κ h ∧ (∀ U, CollectedF C (Un κ) L γ η w κ U → Dartless U h) ∧
    ∀ i, Dartless (E i) h

/-- **C1b target (end of Step 1, o75 Prop 4.7(3))**: at most `2R - 1 + m` components. -/
def HendAtLE (M₀ : Molecule V D₀) (C : CollDataMK M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀))
    (Fst : Set (Object M₀)) (E : Fin m → Object M₀) (L γ η : ℝ) (w : Mom d) (A0 : Set (D₀ → (Fin d → ℤ))) (R : ℕ) :
    Prop :=
  ∀ κ ∈ A0, ∀ h : HSt V D₀, Reach1LE C Un Fst E L γ η w κ h → Stuck1E C L γ η w Un E κ h →
    (h.s.M.numComponents : ℝ) ≤ 2 * (R : ℝ) - 1 + m

/-- The pending re-cuts of a state: survivors still present that share a joint with an earlier survivor. -/
noncomputable def pendRC (E : Fin m → Object M₀) (h : HSt V D₀) : ℕ :=
  (Finset.univ.filter fun i : Fin m => ¬ Dartless (E i) h ∧ ∃ j, j < i ∧ ¬ Disjoint (E j).atoms (E i).atoms).card

/-- **The survivor-budget exponent** (C0 design for the 75-F2 ledger in main's potential form): main's `g1` with
`Fmax = 2R - 1 + m`, minus one unit per pending re-cut. `WPot … (g1E …)` gains `L^1` at each re-cut, which pays the
re-cut deviation `L^{γ₀+η²-η³}` against main's `stepRHS` (ghost deleted, `ΔF = 0`, `ΔV_β ≤ 1`, label refund `≥ 1`);
initially it costs `L^{pendRC} ≤ L^m`, so the total extra is `L^{(1+γ₀)m} ≤ L^{2m}`. -/
noncomputable def g1E (γ η : ℝ) (crit : V → Prop) (Fmax : ℝ) (E : Fin m → Object M₀) (h : HSt V D₀) : ℝ :=
  g1 γ η crit Fmax h - (pendRC E h : ℝ)

/-- Host with survivors (the conclusion of 7.5′(4) at molecule level). -/
def HostE (C : CollData M₀) (E : Fin m → Object M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (P : Object M₀) :
    Prop :=
  (∃ S a b, IsDV M₀ S a b ∧ P.atoms ⊆ S ∧ Disjoint S (C.hinges ∪ survJointsM E) ∧
      (∀ i, Disjoint S (C.collection i).atoms) ∧ ∀ i, Disjoint S (E i).atoms) ∨
    ∃ Q : Object M₀, P.atoms ⊆ Q.atoms ∧ (Q.HasGapKind L γ η w κ .LG ∨ Q.HasGapKind L γ η w κ .ZG) ∧
      Disjoint Q.atoms (C.hinges ∪ survJointsM E) ∧ (∀ i, Disjoint Q.atoms (C.collection i).atoms) ∧
      ∀ i, Disjoint Q.atoms (E i).atoms

/-- **The molecule-level obligations with survivors** (main's `SubproOblG` + 7.5′ (4), (5) with 75-F1, (6), (6′)). -/
structure SubproOblGMK (C : CollData M₀) (E : Fin m → Object M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) :
    Prop where
  survSG : ∀ i, (E i).HasGapKind L γ η w κ .SG
  contained : ∀ P : Object M₀, P.HasGapKind L γ η w κ .SG → C.Outside P → (∀ i, ¬ P.atoms ⊆ (E i).atoms) →
    Disjoint P.atoms (C.hinges ∪ survJointsM E) → HostE C E L γ η w κ P
  hingeSG : ∀ v ∈ C.hinges, HasChosenPair (C.first v) (C.second v) (fun x y =>
    TripleAtM M₀ v x y ∧ Molecule.gapKind L γ η (Molecule.gapAt L w κ x y) = .SG)
  hingeJoint : ∀ v ∈ C.hinges, ∀ i, (v = (C.collection i).upper ∨ v = (C.collection i).lower) →
    HasChosenPair (C.first v) (C.second v) (fun x y => (C.collection i).ContainsDart x ∧ (C.collection i).ContainsDart y)
  jointPair : ∀ i v, SurvFirstJointM E i v →
    HasChosenPair (C.first v) (C.second v) (fun x y => (E i).ContainsDart x ∧ (E i).ContainsDart y)
  crossing : ∀ P : Object M₀, P.HasGapKind L γ η w κ .SG → C.Outside P → (∀ i, ¬ P.atoms ⊆ (E i).atoms) →
    Disjoint P.atoms (survJointsM E) → ¬ Disjoint P.atoms C.hinges →
    ∃ v ∈ C.hinges, v ∈ P.atoms ∧ ((v ≠ P.upper ∧ v ≠ P.lower) ∨
      ((v = P.upper ∨ v = P.lower) ∧
        HasChosenPair (C.first v) (C.second v) (fun x y => Xor (P.ContainsDart x) (P.ContainsDart y))))
  meetB : ∀ P : Object M₀, P.HasGapKind L γ η w κ .SG → ¬ Disjoint P.atoms (survJointsM E) →
    (∃ i, P.atoms ⊆ (E i).atoms) ∨ (∃ i x, P.ContainsDart x ∧ (E i).ContainsDart x) ∨
    ∃ v ∈ C.hinges, v ∈ P.atoms ∧ ((v ≠ P.upper ∧ v ≠ P.lower) ∨
      ((v = P.upper ∨ v = P.lower) ∧
        HasChosenPair (C.first v) (C.second v) (fun x y => Xor (P.ContainsDart x) (P.ContainsDart y))))

/-- Node-dart data of a removed survivor piece (`PieceData` without `Collected`). -/
def PieceDataS (E : Fin m → Object M₀) (p : Object M₀ × Quad D₀) : Prop :=
  (∃ i, p.1 = E i) ∧
    (p.1.ContainsDart p.2.1 ∧ p.1.ContainsDart p.2.2.1 ∧ p.1.ContainsDart p.2.2.2.1 ∧ p.1.ContainsDart p.2.2.2.2) ∧
    ((M₀.atom p.2.1 = p.1.upper ∧ M₀.atom p.2.2.2.1 = p.1.lower) ∨
      (M₀.atom p.2.1 = p.1.lower ∧ M₀.atom p.2.2.2.1 = p.1.upper)) ∧
    (M₀.atom p.2.2.1 = M₀.atom p.2.1 ∧ M₀.atom p.2.2.2.2 = M₀.atom p.2.2.2.1 ∧ p.2.1 ≠ p.2.2.1 ∧ p.2.2.2.1 ≠ p.2.2.2.2)

/-- Main's `HostConn` (S4 shape) on the forbidden pool, after earlier survivor removals `qs`. -/
def HostConnMK (M₀ : Molecule V D₀) (C : CollDataMK M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀))
    (E : Fin m → Object M₀) (L γ η : ℝ) (w : Mom d) (A0 : Set (D₀ → (Fin d → ℤ))) : Prop :=
  ∀ κ ∈ A0, ∀ (qs ps : List (Object M₀ × Quad D₀)) (U : Object M₀) (a x b : V),
    (∀ q ∈ qs, PieceDataS E q) → (∀ p ∈ ps, PieceDataF C Un L γ η w κ p) →
    ps.Pairwise (fun p q => Disjoint p.1.atoms q.1.atoms) →
    (∀ p ∈ ps, Disjoint p.1.atoms U.atoms) → CollectedF C (Un κ) L γ η w κ U → U.atoms = {a, x, b} →
    a ≠ x → x ≠ b → a ≠ b → (∀ z, M₀.atom z = x → M₀.atom (M₀.mate z) = a ∨ M₀.atom (M₀.mate z) = b) →
    ConnAvoid M₀ ((⋃ p ∈ ps, PieceKill p.1 p.2) ∪ KillS qs ∪ {z | M₀.atom z = x}) a b

end mol

section stmts
variable {V : Type} [DecidableEq V] [Infinite V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀]

/-- **C1b. The LOW class premises with survivors** (main's `LowLoopClassHyps`, R79 treatment A; R164: over
`CollDataMK` with `forb = survAtomsM E`, collected objects from the forbidden pool (R164b: `cnBound` too), `obl`
replaced by `SubproOblGMK`, survivor fields; `HostConn`/`HostConnFL` allow earlier survivor removals).
`survDisjC` is derivable at the garden level (`C2CanF ⊆ InPF` avoids `forb`; `𝒞₁` avoids survivors by
`Structural`) and kept for C1b's use. -/
structure LowLoopClassHypsMK (M : Molecule V D₀) (R : ℕ) (P : Finset V → ℝ) (A0 : Set (NonLoop M → Fin d → ℤ))
    (C : CollDataMK M.unloop) {m : ℕ} (E : Fin m → Object M.unloop)
    (Un : (NonLoop M → Fin d → ℤ) → Set (Object M.unloop))
    (Fst : Set (Object M.unloop)) (crit Tm : V → Prop) (L γ η : ℝ) (mm : ℕ) : Prop where
  subHypLoop : SubHypLoop R M
  subHypL : SubHypL (R + M.loopBonds.card) M.unloop
  card_loopAtoms : (loopAtoms M).card = M.loopBonds.card
  isMol : M.unloop.IsMolecule
  hP : LadderHered M.unloop P
  hP0 : ∀ S, 0 ≤ P S
  pinned : PinnedM0 (fun k => k ∈ A0) L (0 : Mom d) M.unloop
  forbE : C.forb = survAtomsM E
  oblE : ∀ κ ∈ A0, SubproOblGMK C.toCollData E L γ η (0 : Mom d) κ
  trip : TripleDesig C.toCollData
  unsel : ∀ κ ∈ A0, C.UnselOKF L γ η (0 : Mom d) κ (Un κ)
  degen : ∀ κ ∈ A0, DegenSGT M.unloop L γ η (0 : Mom d) κ Tm
  h0 : ∀ κ ∈ A0, ∀ a ∈ M.unloop.atoms, M.unloop.deg a = 4 →
    ∑ x ∈ M.unloop.dartsAt a, M.unloop.dartSign x • Molecule.kvec L (0 : Mom d) κ x = 0
  tameEq : ∀ k0 ∈ A0, ∀ v ∈ M.atoms, Tm v → ∀ x y, M.unloop.atom x = v → M.unloop.atom y = v → k0 x = k0 y
  mate : ∀ k0 ∈ A0, ∀ x, k0 (M.unloop.mate x) = k0 x
  fixEff : ∀ v ∈ M.atoms, Tm v → effDeg M v < 4 → ∃ k, ∀ k0 ∈ A0, ∀ x, M.unloop.atom x = v → k0 x = k
  loopTame : ∀ v ∈ loopAtoms M, Tm v
  noLoopSG : ∀ κ ∈ A0, ∀ U : Object M.unloop, U.HasGapKind L γ η (0 : Mom d) κ .SG → ∀ v ∈ U.atoms, v ∉ loopAtoms M
  critSG : ∀ κ ∈ A0, ∀ a, crit a → SGat M.unloop L γ η (0 : Mom d) κ a
  card : ((2 * M.unloop.atoms.card : ℕ) : ℝ) ≤ (1 + Real.log L) ^ mm
  kle : ((M.loopBonds.card : ℕ) : ℝ) ≤ (1 + Real.log L) ^ mm
  srcGaps : ∀ k ∈ A0, SourceLadderGaps M.unloop L (0 : Mom d) P k
  dec : ∀ k ∈ A0, ∃ c0, M.unloop.IsDecoration L (0 : Mom d) c0 k ∧ ∀ x ∈ M.unloop.atoms, M.unloop.deg x = 4 → c0 x = 0
  disj : ∀ κ ∈ A0, ∀ U U' : Object M.unloop, CollectedF C (Un κ) L γ η (0 : Mom d) κ U →
    CollectedF C (Un κ) L γ η (0 : Mom d) κ U' → SameDes U U' ∨ Disjoint U.atoms U'.atoms
  fst : ∀ κ ∈ A0, ∀ U ∈ Fst, CollectedF C (Un κ) L γ η (0 : Mom d) κ U
  sgC : ∀ κ ∈ A0, ∀ U, CollectedF C (Un κ) L γ η (0 : Mom d) κ U → U.HasGapKind L γ η (0 : Mom d) κ .SG
  desC : ∀ κ ∈ A0, ∀ U, CollectedF C (Un κ) L γ η (0 : Mom d) κ U → HingeData C.toCollData U
  shape : ∀ κ ∈ A0, ∀ U, CollectedF C (Un κ) L γ η (0 : Mom d) κ U → U.atoms.card = 3 ∨ ObjVine M.unloop U
  hostConn : HostConnMK M.unloop C Un E L γ η (0 : Mom d) A0
  critInt : ∀ κ ∈ A0, ∀ U, CollectedF C (Un κ) L γ η (0 : Mom d) κ U → ∀ a ∈ U.atoms, a ≠ U.upper → a ≠ U.lower →
    ¬ crit a
  cnBound : CnBoundF M.unloop C Un Fst L γ η (0 : Mom d) A0 R
  -- survivors
  survDisjC : ∀ κ ∈ A0, ∀ U, CollectedF C (Un κ) L γ η (0 : Mom d) κ U → ∀ i, Disjoint U.atoms (E i).atoms
  survChain : ∀ i j, i ≠ j → ¬ Disjoint (E i).atoms (E j).atoms →
    (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ ((E i).atoms ∩ (E j).atoms).card = 1
  survShape : ∀ i, ObjVine M.unloop (E i)
  survCritInt : ∀ i, ∀ a ∈ (E i).atoms, a ≠ (E i).upper → a ≠ (E i).lower → ¬ crit a
  survHinge : ∀ v ∈ C.hinges, ∀ i, ¬ (E i).IsInterior v
  survFst : ∀ i, E i ∉ Fst
  /-- `HostConnFL` on the forbidden pool after earlier survivor removals `qs` (`qs = []` is main's `HostConnFL`). -/
  hostConnFLE : ∀ κ ∈ A0, ∀ (qs ps : List (Object M.unloop × Quad (NonLoop M))) (p : Object M.unloop × Quad (NonLoop M)),
    (∀ q ∈ qs, PieceDataS E q) → (∀ q ∈ ps, PieceDataF C Un L γ η (0 : Mom d) κ q) →
    PieceDataF C Un L γ η (0 : Mom d) κ p → p.1 ∉ Fst → (p :: ps).Pairwise (fun p q => Disjoint p.1.atoms q.1.atoms) →
    (∃ z, M.unloop.atom z = p.1.upper ∧ z ∉ KillS qs ∪ KillS ps ∪ PieceKill p.1 p.2 ∧
      M.unloop.mate z ∉ KillS qs ∪ KillS ps ∪ PieceKill p.1 p.2) →
    (∃ z, M.unloop.atom z = p.1.lower ∧ z ∉ KillS qs ∪ KillS ps ∪ PieceKill p.1 p.2 ∧
      M.unloop.mate z ∉ KillS qs ∪ KillS ps ∪ PieceKill p.1 p.2) →
    ConnAvoid M.unloop (KillS qs ∪ KillS ps ∪ PieceKill p.1 p.2) p.1.upper p.1.lower

/-- **C1b target: the LOW class bound with survivors** (`LowLoopClassBound` with `L^{2m}`). -/
def LowLoopClassBoundMK (d : ℕ) (γ η : ℝ) : Prop :=
  ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ mm : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
    ∀ {V : Type} [DecidableEq V] [Infinite V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {M : Molecule V D₀} {R : ℕ}
      {P : Finset V → ℝ} {A0 : Set (NonLoop M → Fin d → ℤ)} {C : CollDataMK M.unloop} {m : ℕ}
      {E : Fin m → Object M.unloop}
      {Un : (NonLoop M → Fin d → ℤ) → Set (Object M.unloop)} {Fst : Set (Object M.unloop)} {crit Tm : V → Prop},
      LowLoopClassHypsMK (d := d) M R P A0 C E Un Fst crit Tm L γ η mm →
      ENNReal.ofReal (loopGain d γ L δ C1 ^ M.loopBonds.card) *
        M.unloop.countA L γ δ C1 (0 : Mom d) (fun k => k ∈ A0) P ≤
        ENNReal.ofReal (L ^ (2 * (m : ℝ)) *
          L ^ (-4 * η ^ 6 * ((M.unloop.rho : ℝ) + ((M.unloop.atoms.filter crit).card : ℝ))) *
          L ^ (((R : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40 - 1 / 20) - (η ^ 5 - 4 * η ^ 6) / 4))

/-- The C1b deliverable in smallness form. -/
def LowLoopClassBoundMKAll : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (1 / 2 : ℝ) 1 → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η ∈ Ioc (0 : ℝ) η₀, LowLoopClassBoundMK d γ η

end stmts

/-! ### C1c: the garden route and the gate -/

/-- **C1c. The all-garden bound with survivors** (the LOW route serves every garden: probe part 0). -/
def AllGardenBoundMK (d : ℕ) (γ η : ℝ) : Prop :=
  ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m c : ℕ, ∀ C1 ≥ 4 * Cstar, ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
    ∀ {R : ℕ} (G : Garden (2 * R)), G.IsPlain → G.Irreducible → IsBalancedSig G.sig → 1 ≤ G.order →
      1 ≤ R → (R : ℝ) ≤ (1 + Real.log L) ^ c → ((2 * G.order : ℕ) : ℝ) ≤ (1 + Real.log L) ^ m →
    ∀ (D : SplicedKernelData G d) (C : CountingChoices G d) (S : SurvivorData G),
      D.hinges = C.subpro.hinges → CountingGeometry G C → S.Structural C.subpro → SurvChainOrder S →
    ∀ (base : Mom d) (roots : Fin (2 * R) → (Fin d → ℤ)) (Adm : (GardenDart G → (Fin d → ℤ)) → Prop),
      (∀ κ, Adm κ → splicedCountingAdmissibleMK G D C S L γ η base roots κ) →
      G.molecule.countA L γ δ C1 base Adm C.ladderScale ≤
        ENNReal.ofReal (L ^ (2 * (S.m : ℝ)) * L ^ (-4 * η ^ 6 * (G.molecule.rho + numCriticalSGMK C S)) *
          L ^ (((R : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40)))

/-- **C1c assembly (proved here)**: the gate from the all-garden bound; main's LOW-GLUE prefix proof verbatim. -/
theorem finalCountGateHalfMK_of_all
    (hall : ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, 1 / 2 < γ → γ < 1 →
      ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → AllGardenBoundMK d γ η) : FinalCountGateHalfMK := by
  intro d hd γ hγ
  by_cases hγh : 1 / 2 < γ
  swap
  · exact ⟨1, one_pos, fun η _ φin _ τ _ φ _ => ⟨1, le_rfl, 1, one_pos, fun ν _ => ⟨1, one_pos, fun δ _ D _ _ =>
      ⟨1, le_rfl, 2, le_rfl, fun L _ h => absurd h hγh⟩⟩⟩⟩
  obtain ⟨η₀, hη₀, hall⟩ := hall d hd γ hγh hγ.2
  refine ⟨η₀, hη₀, fun η hη φin _ τ _ φ _ => ?_⟩
  obtain ⟨Cs, hCs, hb⟩ := hall η hη.1 hη.2
  refine ⟨4 * Cs, by linarith, 1, one_pos, fun ν _ => ⟨1, one_pos, fun δ hδ D hD htime => ?_⟩⟩
  obtain ⟨R₀, hR₀, hR⟩ := hb (4 * (40 * d) ^ (2 * D + 2) + 1) ((40 * d) ^ (2 * D + 1) + 4) (4 * Cs) le_rfl δ
    ⟨hδ.1, hδ.2⟩
  refine ⟨1, le_rfl, max (max R₀ 2) (Real.exp 1), le_trans (le_max_right _ _) (le_max_left _ _), fun L hL _ => ?_⟩
  have hLR₀ : R₀ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hLe : Real.exp 1 ≤ L := le_trans (le_max_right _ _) hL
  have hlog : 1 ≤ Real.log L := by
    have := Real.log_le_log (Real.exp_pos 1) hLe
    rwa [Real.log_exp] at this
  intro p hp R hR1 hRm G hpl hirr hbal hn hnm D' C S hh hg hS hO base roots Adm hAdm
  have hRc : (R : ℝ) ≤ (1 + Real.log L) ^ ((40 * d) ^ (2 * D + 1) + 4) := by
    have h2 := Rdown_le_log_pow ⟨d, γ, η, φin, τ, φ, 4 * Cs, ν, δ, D, 1, L⟩ (D - (p + 1))
    have hexp : (40 * d) ^ (2 * (D - (p + 1)) + 1) ≤ (40 * d) ^ (2 * D + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h1 : (WTParams.Rdown ⟨d, γ, η, φin, τ, φ, 4 * Cs, ν, δ, D, 1, L⟩ (D - (p + 1)) : ℝ) ≤
        Real.log L ^ ((40 * d) ^ (2 * D + 1)) :=
      le_trans h2 (pow_le_pow_right₀ hlog hexp)
    have h3 : (R : ℝ) ≤ 10 * (WTParams.Rdown ⟨d, γ, η, φin, τ, φ, 4 * Cs, ν, δ, D, 1, L⟩ (D - (p + 1)) : ℝ) := by
      exact_mod_cast hRm
    have h4 := ten_mul_pow_le hlog ((40 * d) ^ (2 * D + 1))
    nlinarith
  have hord : ((2 * G.order : ℕ) : ℝ) ≤ (1 + Real.log L) ^ (4 * (40 * d) ^ (2 * D + 2) + 1) := by
    have h1 := N_quartic_le_log_pow ⟨d, γ, η, φin, τ, φ, 4 * Cs, ν, δ, D, 1, L⟩ (by show 1 ≤ d; omega) hlog (p + 1)
    have h2 : (G.order : ℝ) ≤ (WTParams.N ⟨d, γ, η, φin, τ, φ, 4 * Cs, ν, δ, D, 1, L⟩ (p + 1) : ℝ) ^ 4 := by
      exact_mod_cast hnm
    have h3 := two_mul_pow_le hlog (4 * (40 * d) ^ (2 * D + 2))
    have h5 : (G.order : ℝ) ≤ Real.log L ^ (4 * (40 * d) ^ (2 * D + 2)) := h2.trans h1
    push_cast
    nlinarith
  exact hR L hLR₀ G hpl hirr hbal hn hR1 hRc hord D' C S hh hg hS hO base roots Adm hAdm

/-- **C1c bridge (proved here)**: with no survivors the marked admissibility is main's (one-atom gardens and the
`m = 0` case go to main's LOW route unchanged). -/
theorem admissible_of_MK_zero {w d : ℕ} {G : Garden w} (D : SplicedKernelData G d) (C : CountingChoices G d)
    (S : SurvivorData G) (hm : S.m = 0) (L γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (κ : GardenDart G → (Fin d → ℤ)) (h : splicedCountingAdmissibleMK G D C S L γ η base roots κ) :
    splicedCountingAdmissible G D C L γ η base roots κ := by
  have hE : ∀ i : Fin S.m, False := fun i => by have := i.2; omega
  have hj : S.joints = ∅ := by
    ext x; simp only [SurvivorData.joints, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.notMem_empty,
      iff_false, not_exists]
    exact fun i => (hE i).elim
  have hF : forbiddenMK C.subpro S = C.subpro.forbidden := by
    ext x; simp only [forbiddenMK, Set.mem_union, Set.mem_iUnion, Finset.mem_coe]
    exact ⟨fun h => h.elim id fun ⟨i, _⟩ => (hE i).elim, Or.inl⟩
  obtain ⟨hz, hs, ⟨rk, hrk, K, hK, hC⟩, h3, h4, h5, h6, -, h8, h9, h10⟩ := h
  refine ⟨hz, ⟨hs.selectedSG, hs.zeroTame, ?_, hs.hingeSG, hs.hingeJoint, ?_⟩,
    ⟨rk, hrk, K, by rw [← hF]; exact hK, hC⟩, h3, h4, h5, h6, h8, fun v hv => h9 v ⟨hv, fun i => (hE i).elim⟩, h10⟩
  · intro P hP hout hdis
    rcases hs.contained P hP hout (fun i => (hE i).elim) (by rw [hj, Finset.union_empty]; exact hdis) with
      ⟨S', a, b, h1, h2, h3', h4', -⟩ | ⟨Q, h1, h2, h3', h4', -⟩
    · rw [hj, Finset.union_empty] at h3'; exact Or.inl ⟨S', a, b, h1, h2, h3', h4'⟩
    · rw [hj, Finset.union_empty] at h3'; exact Or.inr ⟨Q, h1, h2, h3', h4'⟩
  · intro P hP hout hmeet
    exact hs.crossing P hP hout (fun i => (hE i).elim) (by rw [hj]; exact Finset.disjoint_empty_right _) hmeet

end C1

end WaveTurbulence.Flower.FinalMKDefs
