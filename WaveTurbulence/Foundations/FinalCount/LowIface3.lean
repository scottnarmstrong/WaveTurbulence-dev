/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowIface2
public import WaveTurbulence.Foundations.FinalCount.GL26
/-! **LOW interface, treatment A (ruling R79): `LowIface3`.**

The original-class loop-provenance interface over `LowLoopData`-style molecules.  `M` is the ORIGINAL garden molecule with
`R` its physical index (`SubHypLoop R M`), `N = M.unloop`, `B = loopAtoms M` the atoms carrying a loop, `k = M.loopBonds.card`.
Classes are cut on `M` (the ORIGINAL tame set `Tm`, pulled to `N`), so `DegenSGT N ... Tm` is the GL26 form and no free
`SmoothAt` survivor is admitted without provenance: the loop atoms are in `Tm`, and a `Tm` atom has a fixed label iff its
EFFECTIVE degree (`deg_N + 2` on `B`, i.e. the degree in `M`) is `< 4`.  `CnBound` is stated at the ORIGINAL `R` with its equality
clause.  The weight `g^k`, `g = L^{-(d-γ)} C₁⁻¹ δ^{1/2}`, is carried by the class bound (`LowLoopClassBound`), whose run index
is the effective one `r = (R + k) - k = R`.  The loop-free `LowClassBound` is its `k = 0` specialization (`low_loop_k0`). -/
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

section stmts3
variable {V : Type} [DecidableEq V] [Infinite V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The atoms of `M` carrying a loop. -/
noncomputable def loopAtoms (M : Molecule V D₀) : Finset V :=
  M.atoms.filter fun v => ∃ z, M.atom z = v ∧ M.atom (M.mate z) = v

/-- The effective degree: the degree in `M.unloop`, plus `2` at a loop atom. -/
noncomputable def effDeg (M : Molecule V D₀) (v : V) : ℕ := M.unloop.deg v + if v ∈ loopAtoms M then 2 else 0

/-- The loop gain `g = L^{-(d-γ)} C₁⁻¹ δ^{1/2}` of one loop (`countA_unloop_le`, GL17). -/
noncomputable def loopGain (d : ℕ) (γ L δ C1 : ℝ) : ℝ := L ^ (-((d : ℝ) - γ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ))

/-- **The premises of the LOW class bound, original-class form (treatment A, R79).**  `N = M.unloop`; the labels `A0` are labels of the
darts of `N`; `Tm` is the ORIGINAL tame predicate; `R` is the ORIGINAL index (so `SubHypL (R + k) N`). -/
structure LowLoopClassHyps (M : Molecule V D₀) (R : ℕ) (P : Finset V → ℝ) (A0 : Set (NonLoop M → Fin d → ℤ))
    (C : CollData M.unloop) (Un : (NonLoop M → Fin d → ℤ) → Set (Object M.unloop)) (Fst : Set (Object M.unloop))
    (crit Tm : V → Prop) (L γ η : ℝ) (m : ℕ) : Prop where
  /-- the original molecule: index `R`, loops allowed, connected -/
  subHypLoop : SubHypLoop R M
  /-- the unlooped molecule has index `R + k` (`SubHypLoop.unloop`) -/
  subHypL : SubHypL (R + M.loopBonds.card) M.unloop
  /-- one loop per loop atom: `|B| = k` -/
  card_loopAtoms : (loopAtoms M).card = M.loopBonds.card
  isMol : M.unloop.IsMolecule
  hP : LadderHered M.unloop P
  hP0 : ∀ S, 0 ≤ P S
  pinned : PinnedM0 (fun k => k ∈ A0) L (0 : Mom d) M.unloop
  obl : ∀ κ ∈ A0, SubproOblG C L γ η (0 : Mom d) κ
  trip : TripleDesig C
  unsel : ∀ κ ∈ A0, C.UnselOK L γ η (0 : Mom d) κ (Un κ)
  /-- the ORIGINAL tame set, pulled to `N` (GL26 `DegenSGT.unloop` form): no `SmoothAt` alternative -/
  degen : ∀ κ ∈ A0, DegenSGT M.unloop L γ η (0 : Mom d) κ Tm
  h0 : ∀ κ ∈ A0, ∀ a ∈ M.unloop.atoms, M.unloop.deg a = 4 →
    ∑ x ∈ M.unloop.dartsAt a, M.unloop.dartSign x • Molecule.kvec L (0 : Mom d) κ x = 0
  /-- all `N`-darts at a `Tm` atom carry one label -/
  tameEq : ∀ k0 ∈ A0, ∀ v ∈ M.atoms, Tm v → ∀ x y, M.unloop.atom x = v → M.unloop.atom y = v → k0 x = k0 y
  mate : ∀ k0 ∈ A0, ∀ x, k0 (M.unloop.mate x) = k0 x
  /-- EFFECTIVE fixedness: the label of a `Tm` atom of effective degree `< 4` is fixed over the class -/
  fixEff : ∀ v ∈ M.atoms, Tm v → effDeg M v < 4 → ∃ k, ∀ k0 ∈ A0, ∀ x, M.unloop.atom x = v → k0 x = k
  /-- the loop atoms are in the original tame set -/
  loopTame : ∀ v ∈ loopAtoms M, Tm v
  /-- B-persistence input: no SG object of `N` contains a loop atom of `M` -/
  noLoopSG : ∀ κ ∈ A0, ∀ U : Object M.unloop, U.HasGapKind L γ η (0 : Mom d) κ .SG → ∀ v ∈ U.atoms, v ∉ loopAtoms M
  critSG : ∀ κ ∈ A0, ∀ a, crit a → SGat M.unloop L γ η (0 : Mom d) κ a
  card : ((2 * M.unloop.atoms.card : ℕ) : ℝ) ≤ (1 + Real.log L) ^ m
  kle : ((M.loopBonds.card : ℕ) : ℝ) ≤ (1 + Real.log L) ^ m
  srcGaps : ∀ k ∈ A0, SourceLadderGaps M.unloop L (0 : Mom d) P k
  dec : ∀ k ∈ A0, ∃ c0, M.unloop.IsDecoration L (0 : Mom d) c0 k ∧ ∀ x ∈ M.unloop.atoms, M.unloop.deg x = 4 → c0 x = 0
  disj : ∀ κ ∈ A0, ∀ U U' : Object M.unloop, Collected C (Un κ) L γ η (0 : Mom d) κ U →
    Collected C (Un κ) L γ η (0 : Mom d) κ U' → SameDes U U' ∨ Disjoint U.atoms U'.atoms
  fst : ∀ κ ∈ A0, ∀ U ∈ Fst, Collected C (Un κ) L γ η (0 : Mom d) κ U
  sgC : ∀ κ ∈ A0, ∀ U, Collected C (Un κ) L γ η (0 : Mom d) κ U → U.HasGapKind L γ η (0 : Mom d) κ .SG
  desC : ∀ κ ∈ A0, ∀ U, Collected C (Un κ) L γ η (0 : Mom d) κ U → HingeData C U
  shape : ∀ κ ∈ A0, ∀ U, Collected C (Un κ) L γ η (0 : Mom d) κ U → U.atoms.card = 3 ∨ ObjVine M.unloop U
  hostConn : HostConn M.unloop C Un L γ η (0 : Mom d) A0
  critInt : ∀ κ ∈ A0, ∀ U, Collected C (Un κ) L γ η (0 : Mom d) κ U → ∀ a ∈ U.atoms, a ≠ U.upper → a ≠ U.lower → ¬ crit a
  /-- `CnBound` at the ORIGINAL `R`, equality clause included (NOT the weaker index `R + k`) -/
  cnBound : CnBound M.unloop C Un Fst L γ η (0 : Mom d) A0 R
  hostConnFL : HostConnFL M.unloop C Un Fst L γ η (0 : Mom d) A0

/-- **LOW-CHAIN target (treatment A): the weighted class bound.**  The loop gain `g^k` weights the count on `N`; the bound has the
ORIGINAL `R` (the run's effective index `r = (R + k) - k`). -/
def LowLoopClassBound (d : ℕ) (γ η : ℝ) : Prop :=
  ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
    ∀ {V : Type} [DecidableEq V] [Infinite V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {M : Molecule V D₀} {R : ℕ}
      {P : Finset V → ℝ} {A0 : Set (NonLoop M → Fin d → ℤ)} {C : CollData M.unloop}
      {Un : (NonLoop M → Fin d → ℤ) → Set (Object M.unloop)} {Fst : Set (Object M.unloop)} {crit Tm : V → Prop},
      LowLoopClassHyps (d := d) M R P A0 C Un Fst crit Tm L γ η m →
      ENNReal.ofReal (loopGain d γ L δ C1 ^ M.loopBonds.card) *
        M.unloop.countA L γ δ C1 (0 : Mom d) (fun k => k ∈ A0) P ≤
        ENNReal.ofReal (L ^ (-4 * η ^ 6 * ((M.unloop.rho : ℝ) + ((M.unloop.atoms.filter crit).card : ℝ))) *
          L ^ (((R : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40 - 1 / 20) - (η ^ 5 - 4 * η ^ 6) / 4))

/-- The `k = 0` (loop-free) part of `LowLoopClassBound`. -/
def LowLoopClassBoundK0 (d : ℕ) (γ η : ℝ) : Prop :=
  ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
    ∀ {V : Type} [DecidableEq V] [Infinite V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {M : Molecule V D₀} {R : ℕ}
      {P : Finset V → ℝ} {A0 : Set (NonLoop M → Fin d → ℤ)} {C : CollData M.unloop}
      {Un : (NonLoop M → Fin d → ℤ) → Set (Object M.unloop)} {Fst : Set (Object M.unloop)} {crit Tm : V → Prop},
      M.loopBonds.card = 0 →
      LowLoopClassHyps (d := d) M R P A0 C Un Fst crit Tm L γ η m →
      M.unloop.countA L γ δ C1 (0 : Mom d) (fun k => k ∈ A0) P ≤
        ENNReal.ofReal (L ^ (-4 * η ^ 6 * ((M.unloop.rho : ℝ) + ((M.unloop.atoms.filter crit).card : ℝ))) *
          L ^ (((R : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40 - 1 / 20) - (η ^ 5 - 4 * η ^ 6) / 4))

theorem LowLoopClassBound.toK0 {d : ℕ} {γ η : ℝ} (h : LowLoopClassBound d γ η) : LowLoopClassBoundK0 d γ η := by
  obtain ⟨Cs, hCs, h⟩ := h
  refine ⟨Cs, hCs, fun m C1 hC1 δ hδ => ?_⟩
  obtain ⟨R₀, hR₀, h'⟩ := h m C1 hC1 δ hδ
  refine ⟨R₀, hR₀, fun L hL V _ _ D₀ _ _ M R P A0 C Un Fst crit Tm hk hh => ?_⟩
  have := h' L hL hh
  rw [hk] at this
  simpa using this

theorem loopAtoms_eq_empty {M : Molecule V D₀} (hk : M.loopBonds.card = 0) : loopAtoms M = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun v hv => ?_
  obtain ⟨-, z, hz1, hz2⟩ := Finset.mem_filter.1 hv
  have hy : ∃ y, M.out y = true ∧ M.atom y = M.atom (M.mate y) := by
    by_cases ho : M.out z = true
    · exact ⟨z, ho, hz1.trans hz2.symm⟩
    · refine ⟨M.mate z, ?_, ?_⟩
      · have := M.out_mate z
        have ho' : M.out z = false := by simpa using ho
        simpa [ho'] using this
      · rw [M.mate_mate]; exact (hz1.trans hz2.symm).symm
  obtain ⟨y, hy1, hy2⟩ := hy
  have : 0 < M.loopBonds.card := Finset.card_pos.2 ⟨y, Finset.mem_filter.2 ⟨by simp [Molecule.bonds, hy1], hy2⟩⟩
  omega

/-- **`low_loop_k0` (bridge, hypotheses):** with no loop, `LowLoopClassHyps` is exactly `LowClassHyps` on `N = M.unloop`. -/
theorem LowLoopClassHyps.toLowClassHyps {M : Molecule V D₀} {R : ℕ} {P : Finset V → ℝ} {A0 : Set (NonLoop M → Fin d → ℤ)}
    {C : CollData M.unloop} {Un : (NonLoop M → Fin d → ℤ) → Set (Object M.unloop)} {Fst : Set (Object M.unloop)}
    {crit Tm : V → Prop} {L γ η : ℝ} {m : ℕ} (h : LowLoopClassHyps (d := d) M R P A0 C Un Fst crit Tm L γ η m)
    (hk : M.loopBonds.card = 0) : LowClassHyps (d := d) M.unloop R P A0 C Un Fst crit Tm L γ η m := by
  have hB := loopAtoms_eq_empty hk
  have hnd : ∀ v, effDeg M v = M.unloop.deg v := fun v => by simp [effDeg, hB]
  have hS : SubHypL R M.unloop := by simpa [hk] using h.subHypL
  have hcn : CnBound M.unloop C Un Fst L γ η (0 : Mom d) A0 R := h.cnBound
  have hat : M.unloop.atoms = M.atoms := rfl
  exact
    { subHypL := hS, isMol := h.isMol, hP := h.hP, hP0 := h.hP0, pinned := h.pinned, obl := h.obl, trip := h.trip,
      unsel := h.unsel, degen := h.degen, h0 := h.h0, tameEq := h.tameEq, mate := h.mate
      fix := fun v hv hT hlt => h.fixEff v (hat ▸ hv) hT (by rw [hnd]; exact hlt)
      critSG := h.critSG, card := h.card, srcGaps := h.srcGaps, dec := h.dec, disj := h.disj, fst := h.fst, sgC := h.sgC,
      desC := h.desC, shape := h.shape, hostConn := h.hostConn, critInt := h.critInt, cnBound := hcn,
      hostConnFL := h.hostConnFL }

/-- **`low_loop_k0` (bridge, bounds):** the loop-free `LowClassBound` gives the `k = 0` part of `LowLoopClassBound`. -/
theorem low_loop_k0 {d : ℕ} {γ η : ℝ} (h : LowClassBound d γ η) : LowLoopClassBoundK0 d γ η := by
  obtain ⟨Cs, hCs, h⟩ := h
  refine ⟨Cs, hCs, fun m C1 hC1 δ hδ => ?_⟩
  obtain ⟨R₀, hR₀, h'⟩ := h m C1 hC1 δ hδ
  exact ⟨R₀, hR₀, fun L hL V _ _ D₀ _ _ M R P A0 C Un Fst crit Tm hk hh => h' L hL (hh.toLowClassHyps hk)⟩

end stmts3

end WaveTurbulence.FinalCountAsm
