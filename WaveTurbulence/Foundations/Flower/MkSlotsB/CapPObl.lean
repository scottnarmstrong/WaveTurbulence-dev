/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.CapPNT
public import WaveTurbulence.Foundations.Flower.MkSlotsB.ROne
public import WaveTurbulence.Foundations.Flower.MkSlots.CapObl
public import WaveTurbulence.Foundations.Flower.ProtPin.ProtGate

/-! # B3s-HELPER3 (B5(i)): **`capSlotObligationPat : CapSlotObligationPat`**

The pattern twin of B3s's `CapSlotObligation`: for every pattern `pat` (`CapPatValid`), the relaxed (R187) cap slot
kernel `capSlotKerPat … pat` (pins `fixCap … pat`) at the cap momentum is a `SlotFam`-compatible superposition with the
B3 slot mass times `L^{31d+6}`, proved from D3's `ProtDefs.ProtBoundGate` (`ProtPin.protBoundGate`).

**The box** (F-H3-2, B3s interface): the superposition holds on `capPatBox` = the slot box intersected with
`{ts | v ≤ ts j}` for every native TOP (root branch of the native couple, in tree `j`) pinned at `v`. For the root-pinned
cap objects (`dRoot` → `rootTerm` at a garden root, pin `t`; `dParent` with `|X.lonePath| = 2` → `penTerm`, pin `s`) this
is D3's R176 restriction (`ts j0 ≥ t`, resp. `≥ s`, the latter consumed only on `ts j0 > s` under R187's `lb`); for all
other cap slots no native top is pinned and `capPatBox` is the slot box.

* `capPatBox`, `CapSlotObligationPatAt`, `CapSlotObligationPat`;
* `capSlotKerPat_triv` (trivial couple: the pattern kernel is B3s's `capSlotKer`), `capSlotPat_triv_obl`;
* `capSlotPat_nontriv_obl` (both configurations: `pinsRoot = false` from `capSlotPat_sup`, `pinsRoot = true` one
  constant mode from `capSlotPat_const`);
* `capSlotObligationPatAt_of`, **`capSlotObligationPat`**. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open Set
open WaveTurbulence TTree WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  WaveTurbulence.Links WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtGeo WaveTurbulence.Flower.ProtWhole
  WaveTurbulence.Flower.MkDefs WaveTurbulence.LGSpine WaveTurbulence.Flower.Stage1W
  WaveTurbulence.Flower.Stage1WNoVine WaveTurbulence.VineEstS3.FS WaveTurbulence.VineA
  WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineAlign WaveTurbulence.Represents
  WaveTurbulence.Flower.MkSlots

namespace WaveTurbulence.Flower.MkSlotsB

/-- **The pattern cap-slot box**: the slot box of the cap pair `q`, with the upper clock `ts j` of every native top (a
root branch of the native couple, in tree `j`; the branches are `NativeClockBranch D (.inl q)`) pinned at `v` at least
`v`. -/
def capPatBox {w : ℕ} (p : ℕ) (a : PrescribedPrimeGarden w) (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ)
    (q : SourcePair a.prime.skeleton) : Set (Fin 2 → ℝ) :=
  slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode) a.prime.prime.1 (.inl q) ∩
    {ts | ∀ (b : GBranch (decodedCouple (a.prime.data.couple q)).tree) (v : ℝ), b.1.2 = [] →
      fixNative a.prime.data a.prime.prime.1 (fixCap (recLG a) J pat t s) (.inl q) b = some v → v ≤ ts b.1.1}

theorem capPatBox_subset {w : ℕ} (p : ℕ) (a : PrescribedPrimeGarden w) (J : Finset (Fin w)) (pat : Fin w → FixPat)
    (t s : ℝ) (q : SourcePair a.prime.skeleton) :
    capPatBox p a J pat t s q ⊆
      slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode) a.prime.prime.1 (.inl q) :=
  inter_subset_left

/-- **The pattern cap-slot obligation at one parameter record** (constant `Kc d η`): `MkSlots.CapSlotObligationAt`
with a pattern `pat` (`CapPatValid`), the relaxed pattern kernel `capSlotKerPat … pat` and the box `capPatBox`. -/
def CapSlotObligationPatAt (Kc : ℕ → ℝ → ℝ) (P : WTParams) : Prop :=
  ∀ C : ℝ, P.C₁ ≤ C →
  ∀ {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ),
    p < P.D → IsCanonGC (p + 1) a.layered → a.prime.data.size ≤ P.N (p + 1) ^ 4 →
    CapGeo a.layered J p → CapPatValid a.layered J pat p → a.layered.garden.Irreducible →
    t ∈ Ioo (p : ℝ) (p + 1) → s ∈ Ioo (p : ℝ) t →
  ∀ (roots : Fin (2 * R) → (Fin P.d → ℤ)) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ), 1 ≤ b →
    (∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b) →
  ∀ (Rf : Fin (2 * R) → Option ℝ), (∀ j r, Rf j = some r → P.L / 2 ≤ r) →
  ∀ (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)),
  ∀ q : SourcePair a.prime.skeleton, IsCapPair a.prime.skeleton a.prime.prime.1 J q →
  ∃ (Λ : Type) (_ : Countable Λ) (wt : Λ → ℝ) (m : Λ → Fin 2 → ℤ) (c : Λ → Fin P.d → ℤ)
    (amp : Λ → Mom P.d → ℂ),
    (∀ l, 0 ≤ wt l) ∧ Summable wt ∧ (∀ l k, ‖amp l k‖ ≤ 1) ∧ (∀ l, SNorm (30 * P.d) 0 (amp l) ≤ 1) ∧
    (∀ l k, amp l k ≠ 0 → ‖k - RepAnalytic.latPt P.d (c l)‖ ≤ 1) ∧
    (∀ ts ∈ capPatBox p a J pat t s q,
      HasSum (fun l => (wt l : ℂ) * amp l (latticePoint P.L (roots (capTreeOf a.prime.skeleton a.prime.prime.1 J q))) *
          fsPhase (m l) ts)
        (capSlotKerPat P.L P.γ P.δ p a J pat t s h roots Rf dag (.inl q) ts
          (latticePoint P.L (roots (capTreeOf a.prime.skeleton a.prime.prime.1 J q))))) ∧
    ∑' l, maxBracketPow P.η (half (m l)) * ENNReal.ofReal (wt l) ≤
      ENNReal.ofReal (Kc P.d P.η * (C * Real.sqrt P.δ) ^ slotSize a.prime.data (.inl q) *
        P.L ^ (-(P.η ^ 8) * (slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
          (.inl q) : ℝ)) *
        (frontierConst P.d ^ slotNr a.prime.data a.prime.prime.1 (.inl q) *
          (b⁻¹ * slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
            (fun _ => b.toNNReal) (.inl q))) *
        P.L ^ (31 * (P.d : ℝ) + 6))

/-- **`CapSlotObligationPat`** (B5(i)): a constant `Kc d η ≥ 1` with `CapSlotObligationPatAt Kc` on the prefix. -/
def CapSlotObligationPat : Prop :=
  ∃ Kc : ℕ → ℝ → ℝ, (∀ d η, 1 ≤ Kc d η) ∧ WTPrefix (CapSlotObligationPatAt Kc)

/-! ### A trivial cap couple -/

/-- On a trivial cap couple (no branches) the pattern kernel is B3s's `capSlotKer` (neither sees times or pins). -/
theorem capSlotKerPat_triv {w d : ℕ} (L γ δ : ℝ) (p : ℕ) (a : PrescribedPrimeGarden w) (J : Finset (Fin w))
    (pat : Fin w → FixPat) (t s : ℝ) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (roots : Fin w → (Fin d → ℤ))
    (Rf : Fin w → Option ℝ) (dag : Option (Fin w → Fin 3 → Mom d)) (q : SourcePair a.prime.skeleton)
    (ht : (a.prime.data.couple q).trees.1 = .leaf ∧ (a.prime.data.couple q).trees.2 = .leaf) (ts : Fin 2 → ℝ)
    (k : Mom d) :
    capSlotKerPat L γ δ p a J pat t s h roots Rf dag (.inl q) ts k =
      capSlotKer L γ δ p a J t s h roots Rf dag (.inl q) ts k := by
  have hT := triv_trees a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) q ht
  have := isEmpty_branch_of_leaves hT
  unfold capSlotKerPat capSlotKer
  dsimp only [slotFnGWFRL, slotFnNWF]
  refine (kernelNodeWR_one_eq L γ δ
    (nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) q) _ _ _
    (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 k (fun _ => 0) 0 _
    (fun τ _ => ?_)).trans ?_
  · simp only [kDomainR, kDomain, Set.mem_ofPred_eq, IsEmpty.forall_iff]
  · exact (kernelNodeWF_noBranch _ _ _ _ hT _ _ _ _ _ _ _ _).trans
      (kernelNodeWF_noBranch _ _ _ _ hT _ _ _ _ _ _ _ _).symm

section Slot

variable {P : WTParams} (hL : 2 ≤ P.L) (hd : 3 ≤ P.d) (hη : 0 < P.η)
  (C : ℝ) {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat)
  (t s : ℝ) (hGeo : CapGeo (recLG a) J p)
  (roots : Fin (2 * R) → (Fin P.d → ℤ)) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ) (hb1 : 1 ≤ b)
  (Rf : Fin (2 * R) → Option ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (q : SourcePair a.prime.skeleton)

include hL hd hη hGeo hb1 in
/-- **A trivial cap slot under a pattern** (B3s's `capSlot_triv_obl` on the smaller box). -/
theorem capSlotPat_triv_obl (hq : IsCapPair a.prime.skeleton a.prime.prime.1 J q)
    (ht : (a.prime.data.couple q).trees.1 = .leaf ∧ (a.prime.data.couple q).trees.2 = .leaf) :
    ∃ (Λ : Type) (_ : Countable Λ) (wt : Λ → ℝ) (m : Λ → Fin 2 → ℤ) (c : Λ → Fin P.d → ℤ)
      (amp : Λ → Mom P.d → ℂ),
      (∀ l, 0 ≤ wt l) ∧ Summable wt ∧ (∀ l k, ‖amp l k‖ ≤ 1) ∧ (∀ l, SNorm (30 * P.d) 0 (amp l) ≤ 1) ∧
      (∀ l k, amp l k ≠ 0 → ‖k - RepAnalytic.latPt P.d (c l)‖ ≤ 1) ∧
      (∀ ts ∈ capPatBox p a J pat t s q,
        HasSum (fun l => (wt l : ℂ) * amp l (latticePoint P.L (roots (capTreeOf a.prime.skeleton a.prime.prime.1 J q))) *
            fsPhase (m l) ts)
          (capSlotKerPat P.L P.γ P.δ p a J pat t s h roots Rf dag (.inl q) ts
            (latticePoint P.L (roots (capTreeOf a.prime.skeleton a.prime.prime.1 J q))))) ∧
      ∑' l, maxBracketPow P.η (half (m l)) * ENNReal.ofReal (wt l) ≤
        ENNReal.ofReal (capKc P.d P.η * (C * Real.sqrt P.δ) ^ Represents.slotSize a.prime.data (.inl q) *
          P.L ^ (-(P.η ^ 8) * (Represents.slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a)
            (sourceLayer_isLayering a) (.inl q) : ℝ)) *
          (frontierConst P.d ^ Stage1WNoVine.slotNr a.prime.data a.prime.prime.1 (.inl q) *
            (b⁻¹ * Represents.slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
              (fun _ => b.toNNReal) (.inl q))) *
          P.L ^ (31 * (P.d : ℝ) + 6)) := by
  obtain ⟨Λ, hΛ, wt, m, c, amp, hw0, hws, hamp1, hampS, hampc, hsum, hmass⟩ :=
    capSlot_triv_obl hL hd hη C a J t s hGeo roots h b hb1 Rf dag q hq ht
  refine ⟨Λ, hΛ, wt, m, c, amp, hw0, hws, hamp1, hampS, hampc, fun ts hts => ?_, hmass⟩
  rw [capSlotKerPat_triv]
  · exact hsum ts (capPatBox_subset p a J pat t s q hts)
  · exact ht

end Slot

/-! ### A nontrivial cap slot -/

section Slot

variable {P : WTParams} (hD3 : ProtBoundAt P) (hd : 3 ≤ P.d) (hη : 0 < P.η)
  (hηγ : P.η ^ 8 ≤ P.gamma1 - Real.sqrt P.η) (hL : 2 ≤ P.L) (hC1 : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ)
  (C : ℝ) (hC : P.C₁ ≤ C) {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R)))
  (pat : Fin (2 * R) → FixPat) (t s : ℝ)
  (hp : p < P.D) (hcan : IsCanonGC (p + 1) (recLG a)) (hsz : a.prime.data.size ≤ P.N (p + 1) ^ 4)
  (hGeo : CapGeo (recLG a) J p) (hpat : CapPatValid (recLG a) J pat p)
  (hps : (p : ℝ) < s) (hst : s < t) (htp : t < p + 1)
  (roots : Fin (2 * R) → (Fin P.d → ℤ)) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ) (hb1 : 1 ≤ b)
  (hb : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b)
  (Rf : Fin (2 * R) → Option ℝ) (hRf1 : ∀ j r, Rf j = some r → 1 ≤ r)
  (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (q : SourcePair a.prime.skeleton)

include hGeo in
/-- On the pattern box, the chain clock of a root-pinning configuration is above the root pin. -/
theorem capPatBox_rootPin (K : CapSide a.prime.data a.prime.prime.1 J q)
    (hroot : (CapP.cfgPat K (sourceLayer a) (sourceLayer_isLayering a) pat).pinsRoot K.X = true)
    (hst : s ≤ t) (ts : Fin 2 → ℝ) (hts : ts ∈ capPatBox p a J pat t s q) :
    rootPinVal (CapP.cfgPat K (sourceLayer a) (sourceLayer_isLayering a) pat) s t ≤ ts K.j0 := by
  set Dq := K.Dq (sourceLayer a) (sourceLayer_isLayering a)
  set r1 := CapP.rootT1 K (sourceLayer a) (sourceLayer_isLayering a)
  have hfix := CapP.capFixPat K (sourceLayer a) (sourceLayer_isLayering a) hGeo pat t s 0 r1
  rw [(pinsRoot_fix hroot s t 0 hst).1 r1 rfl] at hfix
  exact hts.2 (Dq.βc r1) _ rfl hfix

include hD3 hd hη hηγ hL hC1 hδ hC hp hcan hsz hGeo hpat hps hst htp hb1 hb hRf1 in
/-- **A nontrivial cap slot under a pattern.** -/
theorem capSlotPat_nontriv_obl (K : CapSide a.prime.data a.prime.prime.1 J q) :
    ∃ (Λ : Type) (_ : Countable Λ) (wt : Λ → ℝ) (m : Λ → Fin 2 → ℤ) (c : Λ → Fin P.d → ℤ)
      (amp : Λ → Mom P.d → ℂ),
      (∀ l, 0 ≤ wt l) ∧ Summable wt ∧ (∀ l k, ‖amp l k‖ ≤ 1) ∧ (∀ l, SNorm (30 * P.d) 0 (amp l) ≤ 1) ∧
      (∀ l k, amp l k ≠ 0 → ‖k - RepAnalytic.latPt P.d (c l)‖ ≤ 1) ∧
      (∀ ts ∈ capPatBox p a J pat t s q,
        HasSum (fun l => (wt l : ℂ) * amp l (latticePoint P.L (roots (capTreeOf a.prime.skeleton a.prime.prime.1 J q))) *
            fsPhase (m l) ts)
          (capSlotKerPat P.L P.γ P.δ p a J pat t s h roots Rf dag (.inl q) ts
            (latticePoint P.L (roots (capTreeOf a.prime.skeleton a.prime.prime.1 J q))))) ∧
      ∑' l, maxBracketPow P.η (half (m l)) * ENNReal.ofReal (wt l) ≤
        ENNReal.ofReal (capKc P.d P.η * (C * Real.sqrt P.δ) ^ Represents.slotSize a.prime.data (.inl q) *
          P.L ^ (-(P.η ^ 8) * (Represents.slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a)
            (sourceLayer_isLayering a) (.inl q) : ℝ)) *
          (frontierConst P.d ^ Stage1WNoVine.slotNr a.prime.data a.prime.prime.1 (.inl q) *
            (b⁻¹ * Represents.slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
              (fun _ => b.toNNReal) (.inl q))) *
          P.L ^ (31 * (P.d : ℝ) + 6)) := by
  have hL1 : 1 ≤ P.L := by linarith
  set k₀ := latticePoint P.L (roots (capTreeOf a.prime.skeleton a.prime.prime.1 J q)) with hk₀
  have hk₀' : k₀ = latticePoint P.L (roots K.cleaf.1.1) := by rw [hk₀, K.capTree]
  have hcF0 : 0 ≤ frontierConst P.d := le_trans zero_le_one (one_le_frontierConst P.d)
  have hLSb : 0 ≤ b⁻¹ * Represents.slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
      (fun _ => b.toNNReal) (.inl q) := by
    refine mul_nonneg (inv_nonneg.2 (by linarith)) ?_
    unfold Represents.slotLeaf leafSizeProduct
    exact Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hn : 1 ≤ K.X.size / 2 := by have := K.two_le_size; omega
  have hsize : Represents.slotSize a.prime.data (.inl q) = 2 * (K.X.size / 2) := by
    rw [K.slotSize_eq]
    obtain ⟨r, hr⟩ := chain_size_even K.X
    omega
  have hK0 : 0 ≤ capKcen P.d := le_trans zero_le_one (one_le_capKcen P.d)
  cases hr : (CapP.cfgPat K (sourceLayer a) (sourceLayer_isLayering a) pat).pinsRoot K.X with
  | false =>
    obtain ⟨wt, u, hw0, hws, hu, hsum, hmass⟩ := CapP.capSlotPat_sup K (sourceLayer a) (sourceLayer_isLayering a)
      hGeo hD3 (capCsup_spec P.d hη.le) hη.le (by omega) hL1 hcan hp hsz hpat hr hps hst htp h b hb1 hb Rf hRf1 dag
      roots
    obtain ⟨c, amp, hw0', hws', hamp1, hampS, hampc, hsum', hmass'⟩ :=
      (Classical.choose_spec (cap_centre P.d)).2 P.η (capPatBox p a J pat t s q)
        (fun ts => capSlotKerPat P.L P.γ P.δ p a J pat t s h roots Rf dag (.inl q) ts k₀) k₀ wt
        (fun m => capMode K.j0 m) u hw0 hws hu
        (fun ts hts => by rw [hk₀']; exact hsum ts (capPatBox_subset p a J pat t s q hts))
    refine ⟨Fin 2 → ℤ, inferInstance, fun l => capKcen P.d * wt l, fun l => capMode K.j0 l, c, amp, hw0', hws',
      hamp1, hampS, hampc, hsum', ?_⟩
    have hCs := capCsup_ne_top P.d P.η
    set Cs := (capCsup P.d P.η).toReal
    have hCs0 : 0 ≤ Cs := ENNReal.toReal_nonneg
    rw [hsize]
    calc ∑' l, maxBracketPow P.η (half (capMode K.j0 l)) * ENNReal.ofReal (capKcen P.d * wt l)
        = ENNReal.ofReal (capKcen P.d) * ∑' l, maxBracketPow P.η (half (capMode K.j0 l)) * ENNReal.ofReal (wt l) :=
          hmass'
      _ ≤ ENNReal.ofReal (capKcen P.d) * (ENNReal.ofReal Cs * (2 * (ENNReal.ofReal (frontierConst P.d ^
            (K.frontS (sourceLayer a) (sourceLayer_isLayering a) p).card) *
            ENNReal.ofReal (P.L ^ (31 * (P.d : ℝ) + 6)) *
            regBound P (K.X.size / 2) (Represents.slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a)
              (sourceLayer_isLayering a) (.inl q)) *
            ENNReal.ofReal (b⁻¹ * Represents.slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a)
              (sourceLayer_isLayering a) (fun _ => b.toNNReal) (.inl q))))) := by
          refine mul_le_mul' le_rfl (hmass.trans (le_of_eq ?_))
          rw [ENNReal.ofReal_toReal hCs, Finset.prod_const, ENNReal.ofReal_pow hcF0]
      _ ≤ _ := capMass_le P C hC hC1 hδ hL1 hηγ (capKcen P.d) Cs (capKc P.d P.η) hK0 hCs0
            (mul_le_mul_of_nonneg_left (le_max_right _ _) hK0) _ _
            (K.frontS_card_le (sourceLayer a) (sourceLayer_isLayering a)) _ _ hn _ hLSb
  | true =>
    obtain ⟨V, hV, hconst⟩ := CapP.capSlotPat_const K (sourceLayer a) (sourceLayer_isLayering a) hGeo hD3 hη.le
      (by omega) hL1 hcan hp hsz hpat hr hps hst htp h b hb1 hb Rf hRf1 dag roots
    have hval : ∀ ts ∈ capPatBox p a J pat t s q,
        capSlotKerPat P.L P.γ P.δ p a J pat t s h roots Rf dag (.inl q) ts k₀ = V := fun ts hts => by
      rw [hk₀']
      exact hconst ts (capPatBox_rootPin a J pat t s hGeo q K hr hst.le ts hts)
    set u : ℂ := if V = 0 then 0 else V / (‖V‖ : ℂ) with hu
    have hu1 : ‖u‖ ≤ 1 := by
      rw [hu]
      split_ifs with hV0
      · simp
      · rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hV0)]
    have hwu : (‖V‖ : ℂ) * u = V := by
      rw [hu]
      split_ifs with hV0
      · rw [hV0]; simp
      · have : (‖V‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hV0)
        field_simp
    obtain ⟨c, amp, hw0', hws', hamp1, hampS, hampc, hsum', hmass'⟩ :=
      (Classical.choose_spec (cap_centre P.d)).2 P.η (capPatBox p a J pat t s q)
        (fun ts => capSlotKerPat P.L P.γ P.δ p a J pat t s h roots Rf dag (.inl q) ts k₀) k₀
        (fun _ : Unit => ‖V‖) (fun _ => 0) (fun _ => u) (fun _ => norm_nonneg _) Summable.of_finite
        (fun _ => hu1) (fun ts hts => by
          have hs := hasSum_single (f := fun l : Unit => ((‖V‖ : ℝ) : ℂ) * u * fsPhase 0 ts) ()
            (fun b' hb' => absurd (Subsingleton.elim b' ()) hb')
          have hv : ((‖V‖ : ℝ) : ℂ) * u * fsPhase 0 ts =
              capSlotKerPat P.L P.γ P.δ p a J pat t s h roots Rf dag (.inl q) ts k₀ := by
            rw [fsPhase_zero', mul_one, hwu, hval ts hts]
          rw [← hv]
          exact hs)
    refine ⟨Unit, inferInstance, fun _ => capKcen P.d * ‖V‖, fun _ => 0, c, amp, hw0', hws', hamp1, hampS, hampc,
      hsum', ?_⟩
    refine le_trans (le_of_eq hmass') ?_
    rw [tsum_eq_single () (fun b' hb' => absurd (Subsingleton.elim b' ()) hb'), maxBracketPow_zero, one_mul, hsize,
      ofReal_norm]
    have h12 : ENNReal.ofReal (1 / 2) * 2 = 1 := by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
      exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
    calc ENNReal.ofReal (capKcen P.d) * ‖V‖ₑ
        ≤ ENNReal.ofReal (capKcen P.d) * (ENNReal.ofReal (1 / 2) * (2 * (ENNReal.ofReal (frontierConst P.d ^
            (K.frontS (sourceLayer a) (sourceLayer_isLayering a) p).card) *
            ENNReal.ofReal (P.L ^ (31 * (P.d : ℝ) + 6)) *
            regBound P (K.X.size / 2) (Represents.slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a)
              (sourceLayer_isLayering a) (.inl q)) *
            ENNReal.ofReal (b⁻¹ * Represents.slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a)
              (sourceLayer_isLayering a) (fun _ => b.toNNReal) (.inl q))))) := by
          refine mul_le_mul' le_rfl (hV.trans (le_of_eq ?_))
          rw [← mul_assoc, h12, one_mul, Finset.prod_const, ENNReal.ofReal_pow hcF0]
      _ ≤ _ := capMass_le P C hC hC1 hδ hL1 hηγ (capKcen P.d) (1 / 2) (capKc P.d P.η) hK0 (by norm_num)
            (by
              rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, mul_one]
              exact le_mul_of_one_le_right hK0 (le_max_left _ _)) _ _
            (K.frontS_card_le (sourceLayer a) (sourceLayer_isLayering a)) _ _ hn _ hLSb

end Slot

/-! ### One parameter record and the prefix -/

/-- **The pattern cap-slot obligation at one parameter record**, from D3's `ProtBoundAt`. -/
theorem capSlotObligationPatAt_of {P : WTParams} (hD3 : ProtBoundAt P) (hd : 3 ≤ P.d) (hη : 0 < P.η)
    (hηγ : P.η ^ 8 ≤ P.gamma1 - Real.sqrt P.η) (hL : 2 ≤ P.L) (hC1 : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) :
    CapSlotObligationPatAt capKc P := by
  intro C hC R p a J pat t s hp hcan hsz hGeo hpat _ ht hs roots h b hb1 hb Rf hRf dag q hq
  have hrec : recLG a = a.layered := sourceLayer_reconstructs a
  rw [← hrec] at hcan hGeo hpat
  have hcap : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = .leaf := hGeo.cap_leaf
  have hRf1 : ∀ j r, Rf j = some r → 1 ≤ r := fun j r hr => by have := hRf j r hr; linarith
  rcases capSlot_cases a.prime.data a.prime.prime.1 J hcap q hq with htriv | ⟨X, hX, hne, hQ, h2, h1⟩ |
      ⟨X, hX, hne, hQ, h1, h2⟩
  · exact capSlotPat_triv_obl hL hd hη C a J pat t s hGeo roots h b hb1 Rf dag q hq htriv
  · exact capSlotPat_nontriv_obl hD3 hd hη hηγ hL hC1 hδ C hC a J pat t s hp hcan hsz hGeo hpat hs.1 hs.2 ht.2
      roots h b hb1 hb Rf hRf1 dag q (capSideLeft a.prime.data a.prime.prime.1 J q X hX hne hQ h2 h1)
  · exact capSlotPat_nontriv_obl hD3 hd hη hηγ hL hC1 hδ C hC a J pat t s hp hcan hsz hGeo hpat hs.1 hs.2 ht.2
      roots h b hb1 hb Rf hRf1 dag q (capSideRight a.prime.data a.prime.prime.1 J hcap q X hX hne hQ h1 h2)

/-- **`CapSlotObligationPat`** (B5(i)): proved from D3's `ProtPin.protBoundGate`. -/
theorem capSlotObligationPat : CapSlotObligationPat := by
  refine ⟨capKc, fun d η => one_le_capKc d η, ?_⟩
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H⟩ := ProtPin.protBoundGate d hd γ hγ
  set g1 : ℝ := min (2 * γ) (min 1 (2 * ((d : ℝ) - 1) * (1 - γ))) with hg1def
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hg1 : 0 < g1 := by
    refine lt_min (by linarith [hγ.1]) (lt_min one_pos ?_)
    have : 0 < 1 - γ := by linarith [hγ.2]
    have : 0 < (d : ℝ) - 1 := by linarith
    positivity
  have hg1' : g1 ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  refine ⟨min η₀ ((g1 / 2) ^ 2), lt_min hη₀ (by positivity), fun η hη φin hφin τs hτs φ hW => ?_⟩
  have hη1 : η ∈ Ioc 0 η₀ := ⟨hη.1, hη.2.trans (min_le_left _ _)⟩
  have hη2 : η ≤ (g1 / 2) ^ 2 := hη.2.trans (min_le_right _ _)
  obtain ⟨C₁, hC₁, ν₀, hν₀, H2⟩ := H η hη1 φin hφin τs hτs φ hW
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, H3⟩ := H2 ν hν
  refine ⟨δ₀, hδ₀, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H4⟩ := H3 δ hδ D hD hτD
  refine ⟨C₂, hC₂, L₀, hL₀, fun L hL => ?_⟩
  exact capSlotObligationPatAt_of (H4 L hL) hd hη.1 (sqrt_add_pow8_le hg1 hg1' hη.1 hη2) (le_trans hL₀ hL) hC₁
    hδ.1.le

end WaveTurbulence.Flower.MkSlotsB
