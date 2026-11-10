/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.SlotObl

/-! # B3s-HELPER8: the slot obligation by kinds

`MkSlotsI.GenSlotObligationAt` (SlotObl rev 5, sha256 32790a0f…) is proved slot kind by slot kind. This file fixes
the interface:

* **`SlotConcl`**: the conclusion asked for ONE slot `sl` and ONE centre `x` (the body of `GenSlotObligationAt`,
  verbatim); **`SlotFam1`** (one family at one moment weight `θ`) and `slotConcl_of_fam1` (`θ = η` off `SelAdj`,
  `θ = 1/4` on `SelAdj`, rev 4); `SlotFam1C`, `slotConcl_of_fam1C` (HasSum only on the `TopCut` box, rev 5);
* **`SlotPred`**, **`GenSlotOnAt Q Kg P`**: `GenSlotObligationAt` restricted to the slots satisfying `Q` (the extra
  premise `Q a J pat t s kSel σ sl`, right after `sl = iota s'`);
* `genSlotObligationAt_iff_on`: `GenSlotObligationAt Kg P ↔ GenSlotOnAt (fun … => True) Kg P` (definitional);
* `slotConcl_mono`, **`genSlotOnAt_or`**: two kinds covering `Q` combine with the constant `max K₁ K₂` (on records
  with `1 ≤ C₁`, `0 < δ`, `2 ≤ L`, the prefix guards);
* `genSlotOnAt_mono` (large-constant monotonicity, for `prefix_and`), `prefix_guard` (a prefix statement may use the
  guards);
* the four kinds `IsCapSlot`, `IsCplSlot`, `IsRootChainSlot`, `IsInnerChainSlot` and their cover. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Represents
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineEstS3
  WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.VineAlign
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.Stage1WNoVine
open WaveTurbulence.Flower.Stage1MKGate
open WaveTurbulence.Flower.MkSlots (anchProfiles capNodeW recLG IsCapPair capTreeOf stA fixCore)
open WaveTurbulence.Flower.MkSlotsI

namespace WaveTurbulence.Flower.MkSlotsO

/-- **The conclusion for one slot `sl` and one centre `x`** (the body of `MkSlotsI.GenSlotObligationAt`). -/
def SlotConcl (P : WTParams) (C : ℝ) (Kg : ℕ → ℝ → ℝ) {R p : ℕ} (a : PrescribedPrimeGarden (2 * R))
    (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ) (σ kSel : Fin (2 * R) → Option ℕ)
    (Rs : Fin (2 * R) → ℝ) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (Rf : Fin (2 * R) → Option ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (b : ℝ)
    (sl : ReplacementSlot a.prime.skeleton) (x : Fin P.d → ℤ) : Prop :=
  ∃ (Λ : Type) (_ : Countable Λ) (wt : Λ → ℝ) (m : Λ → Fin 2 → ℤ) (c : Λ → Fin P.d → ℤ)
    (amp : Λ → Mom P.d → ℂ),
    (∀ l, 0 ≤ wt l) ∧ Summable wt ∧ (∀ l k, ‖amp l k‖ ≤ 1) ∧ (∀ l, SNorm (30 * P.d) 0 (amp l) ≤ 1) ∧
    (∀ q, sl = .inl q → ∀ l k, amp l k ≠ 0 → ‖k - latPt P.d (c l)‖ ≤ 1) ∧
    (∀ ts ∈ genBoxAt p a J pat t s sl, TopCut a J pat t s sl ts → ∀ n : Fin P.d → ℤ,
      (∀ q, sl = .inl q → IsCapPair a.prime.skeleton a.prime.prime.1 J q →
        n = roots (capTreeOf a.prime.skeleton a.prime.prime.1 J q)) →
      (∀ β : GBranch a.prime.skeleton.tree, sl = .inr β → β.1.2 = [] → n = roots β.1.1) →
      (∀ β : GBranch a.prime.skeleton.tree, sl = .inr β → β.1.2 ≠ [] →
        ‖latticePoint P.L n - latPt P.d x‖ ≤ 1) →
      HasSum (fun l => (wt l : ℂ) * amp l (latticePoint P.L n) * fsPhase (m l) ts)
        (genSlotKer P.L P.γ P.δ p a J pat t s σ kSel Rs h roots Rf dag sl ts (latticePoint P.L n))) ∧
    (¬ SelAdj a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel sl →
      ∑' l, maxBracketPow P.η (half (m l)) * ENNReal.ofReal (wt l) ≤
        ENNReal.ofReal (Kg P.d P.η * genSlotMass P C b a J pat t s kSel Rs sl)) ∧
    (SelAdj a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel sl →
      ∑' l, maxBracketPow (1 / 4) (half (m l)) * ENNReal.ofReal (wt l) ≤
        ENNReal.ofReal (Kg P.d P.η * P.L ^ (47 * (P.d : ℝ) + 2) * genSlotMass P C b a J pat t s kSel Rs sl))

/-- **One slot family at one moment weight `θ`** with `θ`-moment mass `≤ μ`: the structural part of `SlotConcl`
(SlotFam-compatible amplitudes, localization on leaf pairs, the HasSum at the consumed lattice momenta on the box). -/
def SlotFam1 (P : WTParams) {R p : ℕ} (a : PrescribedPrimeGarden (2 * R))
    (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ) (σ kSel : Fin (2 * R) → Option ℕ)
    (Rs : Fin (2 * R) → ℝ) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (Rf : Fin (2 * R) → Option ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d))
    (sl : ReplacementSlot a.prime.skeleton) (x : Fin P.d → ℤ) (θ : ℝ) (μ : ℝ≥0∞) : Prop :=
  ∃ (Λ : Type) (_ : Countable Λ) (wt : Λ → ℝ) (m : Λ → Fin 2 → ℤ) (c : Λ → Fin P.d → ℤ)
    (amp : Λ → Mom P.d → ℂ),
    (∀ l, 0 ≤ wt l) ∧ Summable wt ∧ (∀ l k, ‖amp l k‖ ≤ 1) ∧ (∀ l, SNorm (30 * P.d) 0 (amp l) ≤ 1) ∧
    (∀ q, sl = .inl q → ∀ l k, amp l k ≠ 0 → ‖k - latPt P.d (c l)‖ ≤ 1) ∧
    (∀ ts ∈ genBoxAt p a J pat t s sl, ∀ n : Fin P.d → ℤ,
      (∀ q, sl = .inl q → IsCapPair a.prime.skeleton a.prime.prime.1 J q →
        n = roots (capTreeOf a.prime.skeleton a.prime.prime.1 J q)) →
      (∀ β : GBranch a.prime.skeleton.tree, sl = .inr β → β.1.2 = [] → n = roots β.1.1) →
      (∀ β : GBranch a.prime.skeleton.tree, sl = .inr β → β.1.2 ≠ [] →
        ‖latticePoint P.L n - latPt P.d x‖ ≤ 1) →
      HasSum (fun l => (wt l : ℂ) * amp l (latticePoint P.L n) * fsPhase (m l) ts)
        (genSlotKer P.L P.γ P.δ p a J pat t s σ kSel Rs h roots Rf dag sl ts (latticePoint P.L n))) ∧
    ∑' l, maxBracketPow θ (half (m l)) * ENNReal.ofReal (wt l) ≤ μ

/-- **One slot family on the cut box** (`TopCut`, SlotObl rev 5): `SlotFam1` with the HasSum asked only at the
times where every pinned native top sits below its clock. -/
def SlotFam1C (P : WTParams) {R p : ℕ} (a : PrescribedPrimeGarden (2 * R))
    (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ) (σ kSel : Fin (2 * R) → Option ℕ)
    (Rs : Fin (2 * R) → ℝ) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (Rf : Fin (2 * R) → Option ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d))
    (sl : ReplacementSlot a.prime.skeleton) (x : Fin P.d → ℤ) (θ : ℝ) (μ : ℝ≥0∞) : Prop :=
  ∃ (Λ : Type) (_ : Countable Λ) (wt : Λ → ℝ) (m : Λ → Fin 2 → ℤ) (c : Λ → Fin P.d → ℤ)
    (amp : Λ → Mom P.d → ℂ),
    (∀ l, 0 ≤ wt l) ∧ Summable wt ∧ (∀ l k, ‖amp l k‖ ≤ 1) ∧ (∀ l, SNorm (30 * P.d) 0 (amp l) ≤ 1) ∧
    (∀ q, sl = .inl q → ∀ l k, amp l k ≠ 0 → ‖k - latPt P.d (c l)‖ ≤ 1) ∧
    (∀ ts ∈ genBoxAt p a J pat t s sl, TopCut a J pat t s sl ts → ∀ n : Fin P.d → ℤ,
      (∀ q, sl = .inl q → IsCapPair a.prime.skeleton a.prime.prime.1 J q →
        n = roots (capTreeOf a.prime.skeleton a.prime.prime.1 J q)) →
      (∀ β : GBranch a.prime.skeleton.tree, sl = .inr β → β.1.2 = [] → n = roots β.1.1) →
      (∀ β : GBranch a.prime.skeleton.tree, sl = .inr β → β.1.2 ≠ [] →
        ‖latticePoint P.L n - latPt P.d x‖ ≤ 1) →
      HasSum (fun l => (wt l : ℂ) * amp l (latticePoint P.L n) * fsPhase (m l) ts)
        (genSlotKer P.L P.γ P.δ p a J pat t s σ kSel Rs h roots Rf dag sl ts (latticePoint P.L n))) ∧
    ∑' l, maxBracketPow θ (half (m l)) * ENNReal.ofReal (wt l) ≤ μ

/-- A family on the whole box is a family on the cut box. -/
theorem SlotFam1.toC {P : WTParams} {R p : ℕ} {a : PrescribedPrimeGarden (2 * R)}
    {J : Finset (Fin (2 * R))} {pat : Fin (2 * R) → FixPat} {t s : ℝ} {σ kSel : Fin (2 * R) → Option ℕ}
    {Rs : Fin (2 * R) → ℝ} {h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ} {roots : Fin (2 * R) → (Fin P.d → ℤ)}
    {Rf : Fin (2 * R) → Option ℝ} {dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)}
    {sl : ReplacementSlot a.prime.skeleton} {x : Fin P.d → ℤ} {θ : ℝ} {μ : ℝ≥0∞}
    (H : SlotFam1 P (p := p) a J pat t s σ kSel Rs h roots Rf dag sl x θ μ) :
    SlotFam1C P (p := p) a J pat t s σ kSel Rs h roots Rf dag sl x θ μ := by
  obtain ⟨Λ, hΛ, wt, m, c, amp, h1, h2, h3, h4, h5, h6, h7⟩ := H
  exact ⟨Λ, hΛ, wt, m, c, amp, h1, h2, h3, h4, h5, fun ts hts _ => h6 ts hts, h7⟩

/-- **The conclusion from one cut-box family at the slot's weight** (rev 5). -/
theorem slotConcl_of_fam1C (P : WTParams) (C : ℝ) (Kg : ℕ → ℝ → ℝ) {R p : ℕ} (a : PrescribedPrimeGarden (2 * R))
    (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ) (σ kSel : Fin (2 * R) → Option ℕ)
    (Rs : Fin (2 * R) → ℝ) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (Rf : Fin (2 * R) → Option ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (b : ℝ)
    (sl : ReplacementSlot a.prime.skeleton) (x : Fin P.d → ℤ)
    (hη : ¬ SelAdj a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel sl →
      SlotFam1C P (p := p) a J pat t s σ kSel Rs h roots Rf dag sl x P.η
        (ENNReal.ofReal (Kg P.d P.η * genSlotMass P C b a J pat t s kSel Rs sl)))
    (hq : SelAdj a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel sl →
      SlotFam1C P (p := p) a J pat t s σ kSel Rs h roots Rf dag sl x (1 / 4)
        (ENNReal.ofReal (Kg P.d P.η * P.L ^ (47 * (P.d : ℝ) + 2) * genSlotMass P C b a J pat t s kSel Rs sl))) :
    SlotConcl P C Kg (p := p) a J pat t s σ kSel Rs h roots Rf dag b sl x := by
  by_cases hs : SelAdj a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel sl
  · obtain ⟨Λ, hΛ, wt, m, c, amp, h1, h2, h3, h4, h5, h6, h7⟩ := hq hs
    exact ⟨Λ, hΛ, wt, m, c, amp, h1, h2, h3, h4, h5, h6, fun hn => (hn hs).elim, fun _ => h7⟩
  · obtain ⟨Λ, hΛ, wt, m, c, amp, h1, h2, h3, h4, h5, h6, h7⟩ := hη hs
    exact ⟨Λ, hΛ, wt, m, c, amp, h1, h2, h3, h4, h5, h6, fun _ => h7, fun h' => (hs h').elim⟩

/-- **The conclusion from one family at the slot's weight**: `θ = η` off `SelAdj`, `θ = 1/4` with the loss
`L^{47d+2}` on `SelAdj` (SlotObl rev 4). -/
theorem slotConcl_of_fam1 (P : WTParams) (C : ℝ) (Kg : ℕ → ℝ → ℝ) {R p : ℕ} (a : PrescribedPrimeGarden (2 * R))
    (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ) (σ kSel : Fin (2 * R) → Option ℕ)
    (Rs : Fin (2 * R) → ℝ) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (Rf : Fin (2 * R) → Option ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (b : ℝ)
    (sl : ReplacementSlot a.prime.skeleton) (x : Fin P.d → ℤ)
    (hη : ¬ SelAdj a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel sl →
      SlotFam1 P (p := p) a J pat t s σ kSel Rs h roots Rf dag sl x P.η
        (ENNReal.ofReal (Kg P.d P.η * genSlotMass P C b a J pat t s kSel Rs sl)))
    (hq : SelAdj a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel sl →
      SlotFam1 P (p := p) a J pat t s σ kSel Rs h roots Rf dag sl x (1 / 4)
        (ENNReal.ofReal (Kg P.d P.η * P.L ^ (47 * (P.d : ℝ) + 2) * genSlotMass P C b a J pat t s kSel Rs sl))) :
    SlotConcl P C Kg (p := p) a J pat t s σ kSel Rs h roots Rf dag b sl x :=
  slotConcl_of_fam1C P C Kg a J pat t s σ kSel Rs h roots Rf dag b sl x (fun hs => (hη hs).toC)
    (fun hs => (hq hs).toC)

/-- A predicate on the slots of a prescribed point (with its cap trees, pattern, times, selection and filters). -/
abbrev SlotPred : Type :=
  ∀ {R : ℕ} (_a : PrescribedPrimeGarden (2 * R)) (_J : Finset (Fin (2 * R))) (_pat : Fin (2 * R) → FixPat)
    (_t _s : ℝ) (_kSel _σ : Fin (2 * R) → Option ℕ), ReplacementSlot _a.prime.skeleton → Prop

/-- **The slot obligation on the slots satisfying `Q`.** -/
def GenSlotOnAt (Q : SlotPred) (Kg : ℕ → ℝ → ℝ) (P : WTParams) : Prop :=
  ∀ C : ℝ, P.C₁ ≤ C →
  ∀ {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat)
    (t s : ℝ),
    p < P.D → IsCanonGC (p + 1) a.layered → a.prime.data.size ≤ P.N (p + 1) ^ 4 → J.card = R →
    CapGeo a.layered J p → CapPatValid a.layered J pat p → a.layered.garden.Irreducible →
    t ∈ Ioo (p : ℝ) (p + 1) → s ∈ Ioo (p : ℝ) t →
  ∀ (kSel : Fin (2 * R) → Option ℕ), (∀ j, (kSel j).isSome → pat j = FixPat.plain) →
  ∀ (σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ), (∀ j, P.L ≤ Rs j) →
  ∀ (mkF : Stage1Mk.MarkFn (2 * R)), FineMarking J pat t s kSel σ mkF →
    (¬ StemDep σ kSel ∨ CleanPt J a) →
  ∀ (roots : Fin (2 * R) → (Fin P.d → ℤ)) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ), 1 ≤ b →
    (∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b) →
  ∀ (Rf : Fin (2 * R) → Option ℝ), (∀ j r, Rf j = some r → P.L / 2 ≤ r) →
    (((∃ i, σ i ≠ none) ∨ ∃ i, kSel i ≠ none) → ∀ j, j ∉ J → ∃ r, Rf j = some r ∧
      (∀ j' x, ‖x‖ ≥ r → h p j j' x = 0 ∧ h p j' j x = 0) ∧ r ^ 10 ≤ ‖latticePoint P.L (roots j)‖) →
  ∀ (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)),
  ∀ (s' : ReplacementSlot (stA mkF a).G) (sl : ReplacementSlot a.prime.skeleton),
    sl = (MkSlotsT.shapeRep mkF a).iota a.prime.prime.1 ((stA mkF a).plain a.prime.prime.1) s' →
    Q a J pat t s kSel σ sl →
  ∀ x : Fin P.d → ℤ, SlotConcl P C Kg (p := p) a J pat t s σ kSel Rs h roots Rf dag b sl x

/-- The full obligation is the obligation on all slots. -/
theorem genSlotObligationAt_iff_on (Kg : ℕ → ℝ → ℝ) (P : WTParams) :
    GenSlotObligationAt Kg P ↔ GenSlotOnAt (fun _ _ _ _ _ _ _ _ => True) Kg P := by
  constructor
  · intro H C hC R p a J pat t s hp hcan hsz hJ hgeo hpat hirr ht hs kSel hkSel σ Rs hRs mkF hfine hclean roots h b
      hb hh Rf hRf hRf' dag s' sl hsl _ x
    exact H C hC a J pat t s hp hcan hsz hJ hgeo hpat hirr ht hs kSel hkSel σ Rs hRs mkF hfine hclean roots h b hb hh
      Rf hRf hRf' dag s' sl hsl x
  · intro H C hC R p a J pat t s hp hcan hsz hJ hgeo hpat hirr ht hs kSel hkSel σ Rs hRs mkF hfine hclean roots h b
      hb hh Rf hRf hRf' dag s' sl hsl x
    exact H C hC a J pat t s hp hcan hsz hJ hgeo hpat hirr ht hs kSel hkSel σ Rs hRs mkF hfine hclean roots h b hb hh
      Rf hRf hRf' dag s' sl hsl trivial x

/-- The slot mass is nonnegative (`C ≥ 0`, `δ ≥ 0`, `L > 0`, `b ≥ 1`, `Rs > 0`). -/
theorem genSlotMass_nonneg (P : WTParams) {C b : ℝ} (hC : 0 ≤ C) (hb : 1 ≤ b) (hL : 0 < P.L) {R : ℕ}
    (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ)
    (kSel : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (hRs : ∀ j, 0 < Rs j)
    (sl : ReplacementSlot a.prime.skeleton) : 0 ≤ genSlotMass P C b a J pat t s kSel Rs sl := by
  have hcF : 0 ≤ frontierConst P.d := le_trans zero_le_one (one_le_frontierConst P.d)
  have hleaf : 0 ≤ genLeaf a J b sl := by
    have hsl : ∀ sl', 0 ≤ slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
        (fun _ => b.toNNReal) sl' := fun sl' => by
      unfold slotLeaf
      cases sl' <;> exact Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    cases sl with
    | inl q =>
      simp only [genLeaf]
      refine mul_nonneg ?_ (hsl _)
      split_ifs
      · exact inv_nonneg.2 (by linarith)
      · exact zero_le_one
    | inr β => simp only [genLeaf]; exact hsl _
  unfold genSlotMass
  refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (mul_nonneg hC (Real.sqrt_nonneg _)) _)
    (Real.rpow_nonneg hL.le _)) (mul_nonneg (pow_nonneg hcF _) hleaf)) (Real.rpow_nonneg hL.le _))
    (Finset.prod_nonneg fun v _ => Real.rpow_nonneg (hRs _).le _)

/-- A conclusion with a smaller constant gives the conclusion with a larger one. -/
theorem slotConcl_mono (P : WTParams) {C : ℝ} {Kg Kg' : ℕ → ℝ → ℝ} (hK : Kg P.d P.η ≤ Kg' P.d P.η) {R p : ℕ}
    {a : PrescribedPrimeGarden (2 * R)} {J : Finset (Fin (2 * R))} {pat : Fin (2 * R) → FixPat} {t s : ℝ}
    {σ kSel : Fin (2 * R) → Option ℕ} {Rs : Fin (2 * R) → ℝ} {h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ}
    {roots : Fin (2 * R) → (Fin P.d → ℤ)} {Rf : Fin (2 * R) → Option ℝ} {dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)}
    {b : ℝ} {sl : ReplacementSlot a.prime.skeleton} {x : Fin P.d → ℤ}
    (hm : 0 ≤ genSlotMass P C b a J pat t s kSel Rs sl) (hL : 0 < P.L)
    (H : SlotConcl P C Kg (p := p) a J pat t s σ kSel Rs h roots Rf dag b sl x) :
    SlotConcl P C Kg' (p := p) a J pat t s σ kSel Rs h roots Rf dag b sl x := by
  obtain ⟨Λ, hΛ, wt, m, c, amp, h1, h2, h3, h4, h5, h6, h7, h8⟩ := H
  refine ⟨Λ, hΛ, wt, m, c, amp, h1, h2, h3, h4, h5, h6, fun hs => (h7 hs).trans ?_, fun hs => (h8 hs).trans ?_⟩
  · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hK hm)
  · exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hL.le _)) hm)

/-- **Two kinds covering `Q`** combine with the constant `max K₁ K₂` (prefix guards `1 ≤ C₁`, `2 ≤ L`). -/
theorem genSlotOnAt_or {Q Q₁ Q₂ : SlotPred} {K₁ K₂ : ℕ → ℝ → ℝ} {P : WTParams} (hC₁ : 1 ≤ P.C₁) (hL : 2 ≤ P.L)
    (hcov : ∀ {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat)
      (t s : ℝ) (kSel σ : Fin (2 * R) → Option ℕ) (sl : ReplacementSlot a.prime.skeleton),
      Q a J pat t s kSel σ sl → Q₁ a J pat t s kSel σ sl ∨ Q₂ a J pat t s kSel σ sl)
    (h₁ : GenSlotOnAt Q₁ K₁ P) (h₂ : GenSlotOnAt Q₂ K₂ P) :
    GenSlotOnAt Q (fun d η => max (K₁ d η) (K₂ d η)) P := by
  intro C hC R p a J pat t s hp hcan hsz hJ hgeo hpat hirr ht hs kSel hkSel σ Rs hRs mkF hfine hclean roots h b
    hb hh Rf hRf hRf' dag s' sl hsl hQ x
  have hL0 : 0 < P.L := by linarith
  have hm : 0 ≤ genSlotMass P C b a J pat t s kSel Rs sl :=
    genSlotMass_nonneg P (by linarith) hb hL0 a J pat t s kSel Rs (fun j => lt_of_lt_of_le hL0 (hRs j)) sl
  rcases hcov a J pat t s kSel σ sl hQ with hq | hq
  · exact slotConcl_mono P (le_max_left _ _) hm hL0
      (h₁ C hC a J pat t s hp hcan hsz hJ hgeo hpat hirr ht hs kSel hkSel σ Rs hRs mkF hfine hclean roots h b hb hh
        Rf hRf hRf' dag s' sl hsl hq x)
  · exact slotConcl_mono P (le_max_right _ _) hm hL0
      (h₂ C hC a J pat t s hp hcan hsz hJ hgeo hpat hirr ht hs kSel hkSel σ Rs hRs mkF hfine hclean roots h b hb hh
        Rf hRf hRf' dag s' sl hsl hq x)

/-- Large-constant monotonicity of the restricted obligation (for `prefix_and`). -/
theorem genSlotOnAt_mono (Q : SlotPred) (Kg : ℕ → ℝ → ℝ) : LargeConstantMonotone (GenSlotOnAt Q Kg) := by
  intro P c₁ c₂ _ _ _ _ h₁ _ h C hC R p a J pat t s hp hcan hsz
  exact h C (h₁.trans hC) (R := R) (p := p) a J pat t s hp hcan (by rw [← vineEstHalfMK_N P c₁ c₂ (p + 1)]; exact hsz)

/-- A prefix statement may use the prefix guards `1 ≤ C₁`, `0 < δ`, `2 ≤ L`. -/
theorem prefix_guard {A B : WTParams → Prop} (hA : WTPrefix A)
    (hAB : ∀ P : WTParams, 1 ≤ P.C₁ → 0 < P.δ → 2 ≤ P.L → A P → B P) : WTPrefix B := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H⟩ := hA d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin hφin τs hτs φ hW => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H2⟩ := H η hη φin hφin τs hτs φ hW
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, H3⟩ := H2 ν hν
  refine ⟨δ₀, hδ₀, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H4⟩ := H3 δ hδ D hD hτD
  exact ⟨C₂, hC₂, L₀, hL₀, fun L hL => hAB _ hC₁ hδ.1 (hL₀.trans hL) (H4 L hL)⟩

/-- **Combining two kinds on the prefix.** -/
theorem prefix_genSlotOnAt_or {Q Q₁ Q₂ : SlotPred} {K₁ K₂ : ℕ → ℝ → ℝ}
    (hcov : ∀ {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat)
      (t s : ℝ) (kSel σ : Fin (2 * R) → Option ℕ) (sl : ReplacementSlot a.prime.skeleton),
      Q a J pat t s kSel σ sl → Q₁ a J pat t s kSel σ sl ∨ Q₂ a J pat t s kSel σ sl)
    (h₁ : WTPrefix (GenSlotOnAt Q₁ K₁)) (h₂ : WTPrefix (GenSlotOnAt Q₂ K₂)) :
    WTPrefix (GenSlotOnAt Q (fun d η => max (K₁ d η) (K₂ d η))) :=
  prefix_guard (prefix_and h₁ h₂ (genSlotOnAt_mono Q₁ K₁) (genSlotOnAt_mono Q₂ K₂))
    fun _ hC₁ _ hL H => genSlotOnAt_or hC₁ hL hcov H.1 H.2

/-! ## The four kinds -/

/-- A cap pair. -/
def IsCapSlot : SlotPred := fun a J _ _ _ _ _ sl =>
  ∃ q, sl = .inl q ∧ IsCapPair a.prime.skeleton a.prime.prime.1 J q

/-- A leaf pair that is not a cap pair. -/
def IsCplSlot : SlotPred := fun a J _ _ _ _ _ sl =>
  ∃ q, sl = .inl q ∧ ¬ IsCapPair a.prime.skeleton a.prime.prime.1 J q

end WaveTurbulence.Flower.MkSlotsO
