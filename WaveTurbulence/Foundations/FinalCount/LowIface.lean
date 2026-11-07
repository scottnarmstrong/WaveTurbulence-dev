/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmRegMol
public import WaveTurbulence.Foundations.FinalCount.AsmHmemShape
public import WaveTurbulence.Foundations.FinalCount.AsmEnd3
public import WaveTurbulence.Foundations.FinalCount.GL28
public import WaveTurbulence.Foundations.FinalCount.AsmGate
/-! **FINALCOUNT-ASSEMBLY (LOW, session 20): the interface of the LOW half.**

The LOW half (`FinalCountLowAt`, some atom of degree `< 3` or a loop) is split into three exact targets, stated here as `Prop`s:
* `LowClassBound d γ η` (owner LOW-CHAIN): `reg_class_bound'` with `SubHyp` replaced by G3-LOWDEG's `SubHypL` (no `deg3`) and the
  Step-1 inputs `HmemAt`/`HendAt` replaced by their molecule-level geometric sources (`LowClassHyps`: exactly the hypotheses of
  `hmemAt_of_shape` and `hendAt_of_inputs`, which the REG garden supplies).  The run is G3-LOWDEG's (`HRunLC`: Step 1 with `D1`
  steps, the `D3` phase, Steps 2-4), the index `R` is a run variable.
* `LowMoleculeBound d γ η`: the class split (`low_molecule_bound_of` below, proved from `LowClassBound`).
* `LowGardenBound d γ η` (owner LOW-GARDEN): the garden-level bound for `¬ RegGeom` gardens (loop start `M.unloop`, base shift,
  `Sum.inl`, `LowClassHyps` for every class).  `finalCount_low_half_of_garden` (LowGlue) closes the gate from it. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc)
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
  WaveTurbulence.VineCount

section ports
universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- `card_lowdeg_le` for `SubHypL`: at most `2R` atoms have degree `< 4`. -/
theorem card_lowdeg_leL {R : ℕ} {M₀ : Molecule V D₀} (hS : SubHypL R M₀) :
    (M₀.atoms.filter fun a => M₀.deg a < 4).card ≤ 2 * R := by
  have h1 := sum_deg_eq M₀
  have h2 := card_darts_eq_two_bonds M₀
  have h3 := hS.count
  have hle : ∀ a ∈ M₀.atoms, M₀.deg a ≤ 4 := fun a ha => deg_le_four (M := M₀) (hS.bounds a ha)
  have key : ∑ a ∈ M₀.atoms, (4 - M₀.deg a) = 2 * R := by
    have : ∑ a ∈ M₀.atoms, (4 - M₀.deg a) + ∑ a ∈ M₀.atoms, M₀.deg a = ∑ a ∈ M₀.atoms, 4 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a ha => Nat.sub_add_cancel (hle a ha)
    simp only [Finset.sum_const, smul_eq_mul] at this
    omega
  calc (M₀.atoms.filter fun a => M₀.deg a < 4).card = ∑ a ∈ M₀.atoms.filter (fun a => M₀.deg a < 4), 1 := by simp
    _ ≤ ∑ a ∈ M₀.atoms.filter (fun a => M₀.deg a < 4), (4 - M₀.deg a) := by
        refine Finset.sum_le_sum fun a ha => ?_
        have := (Finset.mem_filter.1 ha).2
        omega
    _ ≤ ∑ a ∈ M₀.atoms, (4 - M₀.deg a) := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = 2 * R := key

theorem labelSet_card_leL {R : ℕ} {M : Molecule V D₀} (hS : SubHypL R M) (kFix : Finset (Mom d)) (hk : kFix.card ≤ 2 * R) :
    (labelSet M kFix).card ≤ 2 ^ M.atoms.card * (2 * R + 1) ^ (2 * R) := by
  unfold labelSet
  rw [Finset.card_product, Finset.card_powerset, Fintype.card_piFinset]
  refine Nat.mul_le_mul_left _ ?_
  have h1 : (insert none (kFix.image some) : Finset (Option (Mom d))).card ≤ 2 * R + 1 :=
    (Finset.card_insert_le _ _).trans (by have := Finset.card_image_le (s := kFix) (f := (some : Mom d → Option (Mom d))); omega)
  calc ∏ _i : lowAtoms M, (insert none (kFix.image some) : Finset (Option (Mom d))).card
      ≤ ∏ _i : lowAtoms M, (2 * R + 1) := Finset.prod_le_prod' fun _ _ => h1
    _ = (2 * R + 1) ^ Fintype.card (lowAtoms M) := by simp
    _ ≤ (2 * R + 1) ^ (2 * R) := by
        apply Nat.pow_le_pow_right (by omega)
        rw [Fintype.card_coe]
        exact card_lowdeg_leL hS

/-- `exists_classLabel` for `SubHypL` (only `deg ≥ 1` is used: every atom carries a dart). -/
theorem exists_classLabelL {R : ℕ} {M : Molecule V D₀} (hS : SubHypL R M) (L : ℝ) (w : Mom d) (kFix : Finset (Mom d))
    (κ : D₀ → (Fin d → ℤ)) (hmate : ∀ x, κ (M.mate x) = κ x) (hL : L ≠ 0) :
    ∃ lab ∈ labelSet M kFix, InClass M L w kFix lab.1 lab.2 κ := by
  let Z : Finset V := M.atoms.filter fun v => M.IsTame L w kFix κ v
  have hdart : ∀ v ∈ M.atoms, ∃ x, M.atom x = v := by
    intro v hv
    have h3 := hS.deg_pos v hv
    have : 0 < (M.dartsAt v).card := by unfold Molecule.deg at h3; omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp this
    exact ⟨x, (Mole.mem_dartsAt M v x).mp hx⟩
  refine ⟨(Z, fun v => if v.1 ∈ Z then some (Molecule.kvec L w κ (Classical.choose (hdart v.1 (Finset.mem_filter.1 v.2).1))) else none),
    ?_, ?_, ?_⟩
  · unfold labelSet
    refine Finset.mem_product.2 ⟨Finset.mem_powerset.2 (Finset.filter_subset _ _), ?_⟩
    rw [Fintype.mem_piFinset]
    intro v
    by_cases hv : v.1 ∈ Z
    · have hlow := (Finset.mem_filter.1 v.2).2
      have hT := (Finset.mem_filter.1 hv).2
      have hx := Classical.choose_spec (hdart v.1 (Finset.mem_filter.1 v.2).1)
      simp only [hv, if_true]
      exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨_, hT.2 hlow _ hx, rfl⟩)
    · simp [hv]
  · intro v hv
    simp [Z, hv]
  · intro v hv x hx
    simp only [hv, if_true]
    have hT := (Finset.mem_filter.1 hv).2
    have hx' := Classical.choose_spec (hdart v.1 (Finset.mem_filter.1 v.2).1)
    rw [hT.1 _ _ hx' hx]

theorem numComponents_initL {Rn : ℕ} {M₀ : Molecule V D₀} (hS : SubHypL Rn M₀) : M₀.numComponents = 1 := by
  refine Mole.numComponents_eq_one M₀ ?_ hS.conn
  by_contra hne
  have h0 : M₀.atoms = ∅ := Finset.not_nonempty_iff_eq_empty.1 hne
  have := hS.count
  rw [h0] at this
  have h1 := hS.one_le
  simp at this
  omega

end ports

section stmts
variable {V : Type} [DecidableEq V] [Infinite V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- **`HostConnF` for the LOW run.**  After the Step-1 removals along pairwise atom-disjoint collected objects `ps` and a further
collected object `p` that is not first-stage, the joints of `p` are joined outside the removed darts, PROVIDED each joint keeps a
bond.  A joint that keeps no bond (in particular a joint of degree `2` whose two darts lie in `p`) becomes an isolated atom, which
G3-LOWDEG's `HStepD1` deletes with the piece (GL4 `vineStG`), so that removal creates no component either.  For `REG` molecules this
is implied by `HostConnF` (`hostConnFL_of`). -/
def HostConnFL {V : Type} [DecidableEq V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {d : ℕ} (M₀ : Molecule V D₀)
    (C : CollData M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)) (Fst : Set (Object M₀))
    (L γ η : ℝ) (w : Mom d) (A0 : Set (D₀ → (Fin d → ℤ))) : Prop :=
  ∀ κ ∈ A0, ∀ (ps : List (Object M₀ × Quad D₀)) (p : Object M₀ × Quad D₀), (∀ q ∈ ps, PieceData C Un L γ η w κ q) →
    PieceData C Un L γ η w κ p → p.1 ∉ Fst → (p :: ps).Pairwise (fun p q => Disjoint p.1.atoms q.1.atoms) →
    (∃ z, M₀.atom z = p.1.upper ∧ z ∉ KillS ps ∪ PieceKill p.1 p.2 ∧ M₀.mate z ∉ KillS ps ∪ PieceKill p.1 p.2) →
    (∃ z, M₀.atom z = p.1.lower ∧ z ∉ KillS ps ∪ PieceKill p.1 p.2 ∧ M₀.mate z ∉ KillS ps ∪ PieceKill p.1 p.2) →
    ConnAvoid M₀ (KillS ps ∪ PieceKill p.1 p.2) p.1.upper p.1.lower

theorem hostConnFL_of {V : Type} [DecidableEq V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {d : ℕ} {M₀ : Molecule V D₀}
    {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)} {Fst : Set (Object M₀)} {L γ η : ℝ} {w : Mom d}
    {A0 : Set (D₀ → (Fin d → ℤ))} (h : HostConnF M₀ C Un Fst L γ η w A0) : HostConnFL M₀ C Un Fst L γ η w A0 :=
  fun κ hκ ps p hps hp hpF hpw _ _ => h κ hκ ps p hps hp hpF hpw

/-- **The premises of the LOW class bound for one class `A0`** (interface of LOW-CHAIN and LOW-GARDEN).  The fields up to `dec` are
those of `RegClassHyps` with `SubHyp` replaced by `SubHypL`; the Step-1 fields are the molecule-level geometric inputs from which the
REG chain derives `HmemAt` (`hmemAt_of_shape`) and `HendAt` (`hendAt_of_inputs`), so that the LOW run's Step-1 coverage and
end bound are LOW-CHAIN work and the garden supplies only geometry (as `regClassHyps_garden` does). -/
structure LowClassHyps (M₀ : Molecule V D₀) (Rn : ℕ) (P : Finset V → ℝ) (A0 : Set (D₀ → (Fin d → ℤ))) (C : CollData M₀)
    (Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)) (Fst : Set (Object M₀)) (crit Tm : V → Prop) (L γ η : ℝ) (m : ℕ) : Prop where
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
  disj : ∀ κ ∈ A0, ∀ U U' : Object M₀, Collected C (Un κ) L γ η (0 : Mom d) κ U →
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

/-- **LOW-CHAIN target: the LOW class bound** (the statement of `reg_class_bound'` with `LowClassHyps`). -/
def LowClassBound (d : ℕ) (γ η : ℝ) : Prop :=
  ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
    ∀ {V : Type} [DecidableEq V] [Infinite V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {M₀ : Molecule V D₀} {Rn : ℕ}
      {P : Finset V → ℝ} {A0 : Set (D₀ → (Fin d → ℤ))} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)}
      {Fst : Set (Object M₀)} {crit Tm : V → Prop},
      LowClassHyps (d := d) M₀ Rn P A0 C Un Fst crit Tm L γ η m →
      M₀.countA L γ δ C1 (0 : Mom d) (fun k => k ∈ A0) P ≤
        ENNReal.ofReal (L ^ (-4 * η ^ 6 * ((M₀.rho : ℝ) + ((M₀.atoms.filter crit).card : ℝ))) *
          L ^ (((Rn : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40 - 1 / 20) - (η ^ 5 - 4 * η ^ 6) / 4))

/-- **The molecule-level LOW bound** (the statement of `reg_molecule_bound` with `SubHypL` and `LowClassHyps`). -/
def LowMoleculeBound (d : ℕ) (γ η : ℝ) : Prop :=
  ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m c : ℕ, ∀ C1 ≥ 4 * Cstar, ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
    ∀ {V : Type} [DecidableEq V] [Infinite V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {M₀ : Molecule V D₀} {Rn : ℕ}
      {P : Finset V → ℝ} {Adm : (D₀ → (Fin d → ℤ)) → Prop} {C : CollData M₀}
      {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)} {Fst : Set (Object M₀)} {crit : V → Prop} (kFix : Finset (Mom d)),
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
    ∀ (D : SplicedKernelData G d) (C : CountingChoices G d), D.hinges = C.subpro.hinges → CountingGeometry G C →
      ¬ RegGeom G →
    ∀ (base : Mom d) (roots : Fin (2 * R) → (Fin d → ℤ)) (Adm : (GardenDart G → (Fin d → ℤ)) → Prop),
      (∀ κ, Adm κ → splicedCountingAdmissible G D C L γ η base roots κ) →
      G.molecule.countA L γ δ C1 base Adm C.ladderScale ≤
        ENNReal.ofReal (L ^ (-4 * η ^ 6 * (G.molecule.rho + C.numCriticalSG)) *
          L ^ (((R : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40)))

/-- The smallness form consumed by the parameter prefix: for `d ≥ 3` and `1/2 < γ < 1` there is `η₀ > 0` such that the LOW garden
bound holds for every `η ∈ (0, η₀]`. -/
def LowGardenBoundAll : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, 1 / 2 < γ → γ < 1 → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → LowGardenBound d γ η

end stmts

/-- **The class split of the LOW case** (`reg_molecule_bound` with `SubHypL`; mechanical port). -/
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

end WaveTurbulence.FinalCountAsm
