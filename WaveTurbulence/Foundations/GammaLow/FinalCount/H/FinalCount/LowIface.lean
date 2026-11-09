/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowIface
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmEnd3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmGate
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmHmemShape
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmRegMol
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL27
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GV14
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.LowIface`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY (LOW, session 20): the interface of the LOW half.**

The LOW half (`FinalCountLowAt`, some atom of degree `< 3` or a loop) is split into three exact targets, stated here as `Prop`s:
* `LowClassBound d γ η` (owner LOW-CHAIN): `reg_class_bound'` with `SubHyp` replaced by G3-LOWDEG's `SubHypL` (no `deg3`) and the
  Step-1 inputs `HmemAt`/`HendAt` replaced by their molecule-level geometric sources (`LowClassHyps`: exactly the hypotheses of
  `hmemAt_of_shape` and `hendAt_of_inputs`, which the REG garden supplies).  The run is G3-LOWDEG's (`HRunLC`: Step 1 with `D1`
  steps, the `D3` phase, Steps 2-4), the index `R` is a run variable.
* `LowMoleculeBound d γ η`: the class split (`low_molecule_bound_of` below, proved from `LowClassBound`).
* `LowGardenBound d γ η` (owner LOW-GARDEN): the garden-level bound for `¬ RegGeom` gardens (loop start `M.unloop`, base shift,
  `Sum.inl`, `LowClassHyps` for every class).  `finalCount_low_half_of_garden` (LowGlue) closes the gate from it. 

Low-range change (L6-HLOW, GAMMA row): `LowGardenBoundAll` ranges over `0 < γ ≤ 1/2` (main: `1/2 < γ < 1`).-/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc)
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
  WaveTurbulence.VineCount

section ports
universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

end ports

section stmts
variable {V : Type} [DecidableEq V] [Infinite V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- **`HostConnF` for the LOW run.**  After the Step-1 removals along pairwise atom-disjoint collected objects `ps` and a further
collected object `p` that is not first-stage, the joints of `p` are joined outside the removed darts, PROVIDED each joint keeps a
bond.  A joint that keeps no bond (in particular a joint of degree `2` whose two darts lie in `p`) becomes an isolated atom, which
G3-LOWDEG's `HStepD1` deletes with the piece (GL4 `vineStG`), so that removal creates no component either.  For `REG` molecules this
is implied by `HostConnF` (`hostConnFL_of`). -/
def HostConnFL {V : Type} [DecidableEq V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {d : ℕ} (M₀ : Molecule V D₀)
    (C : CollData M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)) (Fst : Set (Src.Object Src.γL M₀))
    (L γ η : ℝ) (w : Mom d) (A0 : Set (D₀ → (Fin d → ℤ))) : Prop :=
  ∀ κ ∈ A0, ∀ (ps : List (Src.Object Src.γL M₀ × Quad D₀)) (p : Src.Object Src.γL M₀ × Quad D₀), (∀ q ∈ ps, PieceData C Un L γ η w κ q) →
    PieceData C Un L γ η w κ p → p.1 ∉ Fst → (p :: ps).Pairwise (fun p q => Disjoint p.1.atoms q.1.atoms) →
    (∃ z, M₀.atom z = p.1.upper ∧ z ∉ KillS ps ∪ PieceKill p.1 p.2 ∧ M₀.mate z ∉ KillS ps ∪ PieceKill p.1 p.2) →
    (∃ z, M₀.atom z = p.1.lower ∧ z ∉ KillS ps ∪ PieceKill p.1 p.2 ∧ M₀.mate z ∉ KillS ps ∪ PieceKill p.1 p.2) →
    ConnAvoid M₀ (KillS ps ∪ PieceKill p.1 p.2) p.1.upper p.1.lower

theorem hostConnFL_of {V : Type} [DecidableEq V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {d : ℕ} {M₀ : Molecule V D₀}
    {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)} {L γ η : ℝ} {w : Mom d}
    {A0 : Set (D₀ → (Fin d → ℤ))} (h : HostConnF M₀ C Un Fst L γ η w A0) : HostConnFL M₀ C Un Fst L γ η w A0 :=
  fun κ hκ ps p hps hp hpF hpw _ _ => h κ hκ ps p hps hp hpF hpw

structure LowClassHyps (M₀ : Molecule V D₀) (Rn : ℕ) (P : Finset V → ℝ) (A0 : Set (D₀ → (Fin d → ℤ))) (C : CollData M₀)
    (Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)) (Fst : Set (Src.Object Src.γL M₀)) (crit Tm : V → Prop) (L γ η : ℝ) (m : ℕ) : Prop where
  subHypL : SubHypL Rn M₀
  isMol : M₀.IsMolecule
  hP : LadderHered M₀ P
  hP0 : ∀ S, 0 ≤ P S
  pinned : PinnedM0 (fun k => k ∈ A0) L (0 : Mom d) M₀
  obl : ∀ κ ∈ A0, SubproOblG C L γ η (0 : Mom d) κ
  trip : TripleDesig C
  unsel : ∀ κ ∈ A0, C.UnselOK L γ η (0 : Mom d) κ (Un κ)
  degen : ∀ κ ∈ A0, DegenSGT M₀ L γ η (0 : Mom d) κ Tm
  h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 →
    ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L (0 : Mom d) κ x = 0
  tameEq : ∀ k0 ∈ A0, ∀ v ∈ M₀.atoms, Tm v → ∀ x y, M₀.atom x = v → M₀.atom y = v → k0 x = k0 y
  mate : ∀ k0 ∈ A0, ∀ x, k0 (M₀.mate x) = k0 x
  fix : ∀ v ∈ M₀.atoms, Tm v → M₀.deg v < 4 → ∃ k, ∀ k0 ∈ A0, ∀ x, M₀.atom x = v → k0 x = k
  critSG : ∀ κ ∈ A0, ∀ a, crit a → SGat M₀ L γ η (0 : Mom d) κ a
  card : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ (1 + Real.log L) ^ m
  srcGaps : ∀ k ∈ A0, SourceLadderGaps M₀ L (0 : Mom d) P k
  dec : ∀ k ∈ A0, ∃ c0, M₀.IsDecoration L (0 : Mom d) c0 k ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0
  /-- Step-1 geometry (`hmemAt_of_shape`): collected objects have the same designation or are atom-disjoint -/
  disj : ∀ κ ∈ A0, ∀ U U' : Src.Object Src.γL M₀, Collected C (Un κ) L γ η (0 : Mom d) κ U →
    Collected C (Un κ) L γ η (0 : Mom d) κ U' → SameDes U U' ∨ Disjoint U.atoms U'.atoms
  /-- first-stage objects are collected for every decoration -/
  fst : ∀ κ ∈ A0, ∀ U ∈ Fst, Collected C (Un κ) L γ η (0 : Mom d) κ U
  /-- collected objects are SG -/
  sgC : ∀ κ ∈ A0, ∀ U, Collected C (Un κ) L γ η (0 : Mom d) κ U → U.HasGapKind L γ η (0 : Mom d) κ .SG
  /-- the designated pairs at the joints of a collected object -/
  desC : ∀ κ ∈ A0, ∀ U, Collected C (Un κ) L γ η (0 : Mom d) κ U → HingeData C U
  /-- shape: three atoms, or a vine -/
  shape : ∀ κ ∈ A0, ∀ U, Collected C (Un κ) L γ η (0 : Mom d) κ U → U.atoms.card = 3 ∨ ObjVine M₀ U
  /-- host connectivity of three-atom collected objects -/
  hostConn : HostConn M₀ C Un L γ η (0 : Mom d) A0
  /-- interior atoms of collected objects are not critical -/
  critInt : ∀ κ ∈ A0, ∀ U, Collected C (Un κ) L γ η (0 : Mom d) κ U → ∀ a ∈ U.atoms, a ≠ U.upper → a ≠ U.lower → ¬ crit a
  /-- Step-1 end bound (`hendAt_of_inputs`): the cnblock bound on the first-stage removals -/
  cnBound : CnBound M₀ C Un Fst L γ η (0 : Mom d) A0 Rn
  /-- the joints of a later collected object stay connected when both keep a bond -/
  hostConnFL : HostConnFL M₀ C Un Fst L γ η (0 : Mom d) A0

def LowClassBound (d : ℕ) (γ η : ℝ) : Prop :=
  ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
    ∀ {V : Type} [DecidableEq V] [Infinite V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {M₀ : Molecule V D₀} {Rn : ℕ}
      {P : Finset V → ℝ} {A0 : Set (D₀ → (Fin d → ℤ))} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)}
      {Fst : Set (Src.Object Src.γL M₀)} {crit Tm : V → Prop},
      LowClassHyps (d := d) M₀ Rn P A0 C Un Fst crit Tm L γ η m →
      M₀.countA L γ δ C1 (0 : Mom d) (fun k => k ∈ A0) P ≤
        ENNReal.ofReal (L ^ (-4 * η ^ 6 * ((M₀.rho : ℝ) + ((M₀.atoms.filter crit).card : ℝ))) *
          L ^ (((Rn : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40 - 1 / 20) - (η ^ 5 - 4 * η ^ 6) / 4))

/-- **The molecule-level LOW bound** (the statement of `reg_molecule_bound` with `SubHypL` and `LowClassHyps`). -/
def LowMoleculeBound (d : ℕ) (γ η : ℝ) : Prop :=
  ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m c : ℕ, ∀ C1 ≥ 4 * Cstar, ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
    ∀ {V : Type} [DecidableEq V] [Infinite V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {M₀ : Molecule V D₀} {Rn : ℕ}
      {P : Finset V → ℝ} {Adm : (D₀ → (Fin d → ℤ)) → Prop} {C : CollData M₀}
      {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)} {crit : V → Prop} (kFix : Finset (Mom d)),
      SubHypL Rn M₀ → kFix.card ≤ 2 * Rn → (Rn : ℝ) ≤ (1 + Real.log L) ^ c →
      (∀ κ, Adm κ → ∀ x, κ (M₀.mate x) = κ x) →
      (∀ lab ∈ labelSet M₀ kFix, (∃ κ, Adm κ ∧ InClass M₀ L (0 : Mom d) kFix lab.1 lab.2 κ) →
        LowClassHyps (d := d) M₀ Rn P {κ | Adm κ ∧ InClass M₀ L (0 : Mom d) kFix lab.1 lab.2 κ} C Un Fst
          crit (fun v => v ∈ lab.1) L γ η m) →
      M₀.countA L γ δ C1 (0 : Mom d) Adm P ≤
        ENNReal.ofReal (L ^ (-4 * η ^ 6 * ((M₀.rho : ℝ) + ((M₀.atoms.filter crit).card : ℝ))) *
          L ^ (((Rn : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40)))

/-- **LOW-GARDEN target: the garden-level LOW bound** (the statement of `reg_garden_bound` for `¬ RegGeom` gardens, with all premises
of `FinalCountAtWith`). -/
def LowGardenBound (d : ℕ) (γ η : ℝ) : Prop :=
  ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m c : ℕ, ∀ C1 ≥ 4 * Cstar, ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
    ∀ {R : ℕ} (G : Garden (2 * R)), G.IsPlain → G.Irreducible → IsBalancedSig G.sig → 1 ≤ G.order →
      1 ≤ R → (R : ℝ) ≤ (1 + Real.log L) ^ c → ((2 * G.order : ℕ) : ℝ) ≤ (1 + Real.log L) ^ m →
    ∀ (D : SplicedKernelData G d) (C : Src.CountingChoices Src.γL G d), D.hinges = C.subpro.hinges → Src.CountingGeometry G C →
      ¬ RegGeom G →
    ∀ (base : Mom d) (roots : Fin (2 * R) → (Fin d → ℤ)) (Adm : (GardenDart G → (Fin d → ℤ)) → Prop),
      (∀ κ, Adm κ → Src.splicedCountingAdmissible G D C L γ η base roots κ) →
      G.molecule.countA L γ δ C1 base Adm C.ladderScale ≤
        ENNReal.ofReal (L ^ (-4 * η ^ 6 * (G.molecule.rho + C.numCriticalSG)) *
          L ^ (((R : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40)))

/-- The smallness form consumed by the parameter prefix: for `d ≥ 3` and `1/2 < γ < 1` there is `η₀ > 0` such that the LOW garden
bound holds for every `η ∈ (0, η₀]`. -/
def LowGardenBoundAll : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, 0 < γ → γ ≤ 1 / 2 → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → LowGardenBound d γ η

end stmts

theorem low_molecule_bound_of {d : ℕ} {γ η : ℝ} (hη : 0 < η) (hη40 : η ≤ 1 / 40) (hcl : LowClassBound d γ η) :
    LowMoleculeBound d γ η := by
  obtain ⟨Cs, hCs, hreg⟩ := hcl
  have hεpos : 0 < (η ^ 5 - 4 * η ^ 6) / 4 := by
    have h5 : 0 < η ^ 5 := by positivity
    have : 4 * η ^ 6 < η ^ 5 := by
      have : η ^ 6 = η * η ^ 5 := by ring
      rw [this]; nlinarith
    linarith
  refine ⟨Cs, hCs, fun m c C1 hC1 δ hδ => ?_⟩
  obtain ⟨R₁, hR₁, h1⟩ := hreg m (C1 / 4) (by linarith) δ hδ
  obtain ⟨L₁, hL₁, h2⟩ := absorb_Rpow 36 (by norm_num) c ((η ^ 5 - 4 * η ^ 6) / 4) hεpos
  refine ⟨max R₁ L₁, le_trans hR₁ (le_max_left _ _), fun L hL V _ _ D₀ _ _ M₀ Rn P Adm C Un Fst crit kFix hS hk hRc hAdm hclass => ?_⟩
  have hLa : R₁ ≤ L := le_trans (le_max_left _ _) hL
  have hLb : L₁ ≤ L := le_trans (le_max_right _ _) hL
  have hL1 : 1 ≤ L := le_trans hR₁ hLa
  have hL0 : 0 < L := by linarith
  have hRn : 1 ≤ Rn := hS.one_le
  set S := labelSet M₀ kFix with hSdef
  have hcl : ∀ lab ∈ S, M₀.countA L γ δ (C1 / 4) (0 : Mom d) (fun κ => Adm κ ∧ InClass M₀ L (0 : Mom d) kFix lab.1 lab.2 κ) P ≤
      ENNReal.ofReal (L ^ (-4 * η ^ 6 * ((M₀.rho : ℝ) + ((M₀.atoms.filter crit).card : ℝ))) *
        L ^ (((Rn : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40 - 1 / 20) - (η ^ 5 - 4 * η ^ 6) / 4)) :=
    fun lab hlab => by
      by_cases hne : ∃ κ, Adm κ ∧ InClass M₀ L (0 : Mom d) kFix lab.1 lab.2 κ
      · exact h1 L hLa (hclass lab hlab hne)
      · push Not at hne
        have h0 := countA_union_le M₀ L γ δ (C1 / 4) (0 : Mom d) (∅ : Finset Bool)
          (Adm := fun κ => Adm κ ∧ InClass M₀ L (0 : Mom d) kFix lab.1 lab.2 κ) (fun _ _ => True)
          (fun κ hκ => absurd hκ.2 (hne κ hκ.1)) P
        simp only [Finset.sum_empty] at h0
        exact h0.trans bot_le
  have hB : 0 ≤ L ^ (-4 * η ^ 6 * ((M₀.rho : ℝ) + ((M₀.atoms.filter crit).card : ℝ))) *
        L ^ (((Rn : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40 - 1 / 20) - (η ^ 5 - 4 * η ^ 6) / 4) := by positivity
  have hcover : ∀ κ, Adm κ → ∃ lab ∈ S, Adm κ ∧ InClass M₀ L (0 : Mom d) kFix lab.1 lab.2 κ := by
    intro κ hκ
    obtain ⟨lab, hl, hc⟩ := exists_classLabelL hS L (0 : Mom d) kFix κ (hAdm κ hκ) hL0.ne'
    exact ⟨lab, hl, hκ, hc⟩
  have key := countA_le_sum_classes M₀ L γ δ C1 (0 : Mom d) S (fun lab κ => Adm κ ∧ InClass M₀ L (0 : Mom d) kFix lab.1 lab.2 κ)
    P hcover hB hcl
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  have hχ : M₀.circuitRank = (M₀.atoms.card : ℤ) - Rn + 1 := by
    unfold Molecule.circuitRank
    rw [numComponents_initL hS]
    have := hS.count
    omega
  have hSc : (S.card : ℝ) ≤ (2 : ℝ) ^ M₀.atoms.card * (2 * (Rn : ℝ) + 1) ^ (2 * Rn) := by
    have := labelSet_card_leL hS kFix hk
    exact_mod_cast this
  have hfac : (S.card : ℝ) * (4 : ℝ) ^ (-M₀.circuitRank) ≤ (36 * (Rn : ℝ) ^ 2) ^ Rn := by
    rw [hχ]
    refine le_trans (mul_le_mul_of_nonneg_right hSc (by positivity)) ?_
    have := class_factor_le M₀.atoms.card Rn hRn
    convert this using 2
  have habs := h2 L hLb Rn hRn hRc
  set E1 : ℝ := -4 * η ^ 6 * ((M₀.rho : ℝ) + ((M₀.atoms.filter crit).card : ℝ))
  set E2 : ℝ := ((Rn : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40 - 1 / 20) - (η ^ 5 - 4 * η ^ 6) / 4
  have hE : (((Rn : ℝ) - 1) / 20 + (η ^ 5 - 4 * η ^ 6) / 4) + E2 = ((Rn : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40) := by
    simp only [E2]; ring
  calc (S.card : ℝ) * 4 ^ (-M₀.circuitRank) * (L ^ E1 * L ^ E2)
      ≤ L ^ (((Rn : ℝ) - 1) / 20 + (η ^ 5 - 4 * η ^ 6) / 4) * (L ^ E1 * L ^ E2) := by
        gcongr
        exact hfac.trans habs
    _ = L ^ E1 * L ^ ((((Rn : ℝ) - 1) / 20 + (η ^ 5 - 4 * η ^ 6) / 4) + E2) := by
        rw [Real.rpow_add hL0 (((Rn : ℝ) - 1) / 20 + (η ^ 5 - 4 * η ^ 6) / 4) E2]; ring
    _ = L ^ E1 * L ^ (((Rn : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40)) := by rw [hE]

end WaveTurbulence.GammaLow.FinalCount.H
