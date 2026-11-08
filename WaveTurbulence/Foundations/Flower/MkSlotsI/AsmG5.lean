/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.ClassForm
public import WaveTurbulence.Foundations.Flower.MkSlotsI.Count
public import WaveTurbulence.Foundations.Flower.MkSlotsI.RepSel
public import WaveTurbulence.Foundations.Flower.MkSlotsE.Engine
public import WaveTurbulence.Foundations.Flower.MkSlotsB.EngDR
public import WaveTurbulence.Foundations.Flower.MkSlotsG.Bridge
public import WaveTurbulence.Foundations.Flower.MkSlotsS.SelClk
public import WaveTurbulence.Foundations.Flower.MkSlots.IntAsm1

/-! # B3s-HELPER7 AsmG (1): small facts for the general assembly `classRepGen_at`

* `representsIntMK_absorbG`: a loss `L^ℓ` of the mass of `RepresentsIntMK` moves into `L^{cP·d·nProt}` from any
  `cP₀` (`cP₀·d·nProt + ℓ ≤ cP·d·nProt`; α's `representsIntMK_absorbJ` is `cP₀ = 0`);
* `outerValMμD_inter_pinSet`: the outer form against `fixMeasure fix` does not see `Dom ∩ pinSet fix` vs `Dom`
  (β's `integral_fixMeasure_inter_pinSet`); used to run the engine on `domOf π tt ∩ pinSet π.fix`;
* `tsum_famX_le`: the moment mass of the centre-indexed family `famX fam₀ famC X` at a slot, from the masses of `fam₀`
  off the centred slots and of the chain pieces on them;
* `selAdj_iota_of_adjS`, `adjS_of_selAdj_iota`: a slot of `G_sb` has a (non-routed) residual selected clock iff its
  skeleton slot has a clock whose core is a selected vertex (`SelAdj`); hence `prod_selAdj_le`;
* `isCapPair_iota_iff`, `genLeaf_iota`: the cap pairs of the skeleton among the outer slots are those of `G_sb`;
* `pieceGenAt_filt_le`, `pieceGenAt_ind_mem`, `selRAt_not_unitClock`, `selRAt_card_le`: the piece facts at a marked
  set `Mk = classMk mkF a` (transported from `MkSlotsG`, δ). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Represents
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineEstS3
  WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.VineAlign
open WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.Stage1MKGate
open WaveTurbulence.RedSplice (stSt unitBlocks)
open WaveTurbulence.Flower.MkSlots (IsCapPair outerValMμD fixMeasure coreAt fixAt sibIndAt flwAt recLG)

namespace WaveTurbulence.Flower.MkSlotsI

variable {w : ℕ}

/-! ## Mass bookkeeping -/

/-- **A loss carried by the mass of `RepresentsIntMK` moves into the protected factor** from any `cP₀`. -/
theorem representsIntMK_absorbG {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R) {n : ℕ} {cP₀ cP ℓ : ℝ}
    (hL : 1 ≤ P.L) (hℓ : cP₀ * P.d * (π.nProt : ℝ) + ℓ ≤ cP * P.d * (π.nProt : ℝ)) {tt : Fin (2 * R) → ℝ}
    {base : Mom P.d} {roots : Fin (2 * R) → (Fin P.d → ℤ)} {s : ℝ} {val : ℂ}
    (h : π.RepresentsIntMK n cP₀ tt base roots (P.L ^ ℓ * s) val) :
    π.RepresentsIntMK n cP tt base roots s val := by
  obtain ⟨Ξ, hΞ, μ, w, ctr, edge, hinge, freq, h1, h2, h3, h4, h5⟩ := h
  refine ⟨Ξ, hΞ, μ, w, ctr, edge, hinge, freq, h1, h2, h3, ?_, h5⟩
  have hL0 : 0 < P.L := lt_of_lt_of_le one_pos hL
  set K := (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
      P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ)) with hKdef
  have hint0 : 0 ≤ ∫ ξ, ‖w ξ‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
  have hexp : P.L ^ (cP₀ * P.d * (π.nProt : ℝ)) * P.L ^ ℓ ≤ P.L ^ (cP * P.d * (π.nProt : ℝ)) := by
    rw [← Real.rpow_add hL0]
    exact Real.rpow_le_rpow_of_exponent_le hL hℓ
  have hpos : 0 < P.L ^ (cP₀ * P.d * (π.nProt : ℝ)) * P.L ^ ℓ :=
    mul_pos (Real.rpow_pos_of_pos hL0 _) (Real.rpow_pos_of_pos hL0 _)
  have h4' : ∫ ξ, ‖w ξ‖ ∂μ ≤ (K * s) * (P.L ^ (cP₀ * P.d * (π.nProt : ℝ)) * P.L ^ ℓ) := by
    have e : K * P.L ^ (cP₀ * P.d * (π.nProt : ℝ)) * (P.L ^ ℓ * s) =
        (K * s) * (P.L ^ (cP₀ * P.d * (π.nProt : ℝ)) * P.L ^ ℓ) := by ring
    rw [← e]; exact h4
  have hKs : 0 ≤ K * s := by
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_neg_of_pos hneg hpos
    linarith
  calc _ ≤ (K * s) * (P.L ^ (cP₀ * P.d * (π.nProt : ℝ)) * P.L ^ ℓ) := h4'
    _ ≤ (K * s) * P.L ^ (cP * P.d * (π.nProt : ℝ)) := mul_le_mul_of_nonneg_left hexp hKs
    _ = K * P.L ^ (cP * P.d * (π.nProt : ℝ)) * s := by ring

/-! ## The domain on the pinned slice -/

/-- **The outer form against `fixMeasure fix` only sees the pinned slice** (β's `integral_fixMeasure_inter_pinSet`). -/
theorem outerValMμD_inter_pinSet {d : ℕ} (G : Garden w) (L γ δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (tt : Fin w → ℝ) (Dom : Set (GBranch G.tree → ℝ)) (hinges : Finset (GBranch G.tree))
    (Zw : GenDecoration G d roots 0 → ℂ) (hS : G.IsPlain) (fix : GBranch G.tree → Option ℝ)
    (amp : ReplacementSlot G → Mom d → ℂ) (frq : ReplacementSlot G → Fin 2 → ℤ) {J : Type} [Fintype J]
    [DecidableEq J] (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J) (hclk : J → Fin 3 → ClkSrc G)
    (hmom : J → Fin 4 → GNode G.tree) (HkM : J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ) :
    outerValMμD G L γ δ base roots tt (Dom ∩ MkSlotsB.pinSet fix) hinges Zw hS (fixMeasure fix) amp frq route hclk
        hmom HkM =
      outerValMμD G L γ δ base roots tt Dom hinges Zw hS (fixMeasure fix) amp frq route hclk hmom HkM := by
  unfold outerValMμD
  congr 1
  refine tsum_congr fun z => ?_
  rw [MkSlotsB.integral_fixMeasure_inter_pinSet]

/-! ## The moment masses of the centre-indexed family -/

/-- **The moment mass of `famX` at a slot**: from the mass of `fam₀` off the centred slots and the mass of the chain
piece at the centre `X c` on the centred slot `.inr c`. -/
theorem tsum_famX_le {G : Garden w} {d : ℕ} (fam₀ : SlotFam G d) (famC : CentredSlot G → (Fin d → ℤ) → ChainPiece d)
    (X : CentredSlot G → (Fin d → ℤ)) (s : ReplacementSlot G) (θ : ℝ) (μ : ℝ≥0∞)
    (h0 : ¬ IsCentred s → ∑' l, maxBracketPow θ (half (fam₀.m s l)) * ENNReal.ofReal (fam₀.w s l) ≤ μ)
    (hC : ∀ c : CentredSlot G, s = Sum.inr c.1 →
      ∑' l, maxBracketPow θ (half ((famC c (X c)).m l)) * ENNReal.ofReal ((famC c (X c)).w l) ≤ μ) :
    ∑' l, maxBracketPow θ (half ((famX fam₀ famC X).m s l)) * ENNReal.ofReal ((famX fam₀ famC X).w s l) ≤ μ := by
  have hsplit := ENNReal.summable.tsum_sum (f := fun l : fam₀.Λ s ⊕ (pieceAtX famC X s).Λ =>
    maxBracketPow θ (half ((famX fam₀ famC X).m s l)) * ENNReal.ofReal ((famX fam₀ famC X).w s l))
    ENNReal.summable
  refine le_trans (le_of_eq hsplit) ?_
  by_cases hc : IsCentred s
  · -- the `fam₀` modes carry weight `0`; the piece is the chain piece at `X c`
    have h0' : ∀ l : fam₀.Λ s, maxBracketPow θ (half ((famX fam₀ famC X).m s (Sum.inl l))) *
        ENNReal.ofReal ((famX fam₀ famC X).w s (Sum.inl l)) = 0 := fun l => by
      simp only [famX, Sum.elim_inl, hc, ite_true, ENNReal.ofReal_zero, mul_zero]
    simp only [h0', tsum_zero, zero_add]
    rcases s with q | c
    · exact absurd hc (by simp [IsCentred])
    · have hc' : c.1.2 ≠ [] := hc
      have e : pieceAtX famC X (Sum.inr c) = famC ⟨c, hc'⟩ (X ⟨c, hc'⟩) := by
        simp only [pieceAtX, ne_eq, hc', not_false_eq_true, ↓reduceDIte]
      have key := hC ⟨c, hc'⟩ rfl
      simp only [famX, Sum.elim_inr]
      rw [e]
      exact key
  · -- no piece; the `fam₀` modes
    have hE : ∀ l : (pieceAtX famC X s).Λ, False := by
      rcases s with q | c
      · exact fun l => (l : Empty).elim
      · have hc' : ¬ c.1.2 ≠ [] := hc
        have e : pieceAtX famC X (Sum.inr c) = ChainPiece.empty d := by
          simp only [pieceAtX, hc', ↓reduceDIte]
        intro l
        have l' : (ChainPiece.empty d).Λ := e ▸ l
        exact (l' : Empty).elim
    have h1 : ∀ l : (pieceAtX famC X s).Λ, maxBracketPow θ (half ((famX fam₀ famC X).m s (Sum.inr l))) *
        ENNReal.ofReal ((famX fam₀ famC X).w s (Sum.inr l)) = 0 := fun l => (hE l).elim
    simp only [h1, tsum_zero, add_zero]
    refine le_trans (le_of_eq ?_) (h0 hc)
    refine tsum_congr fun l => ?_
    simp only [famX, Sum.elim_inl, hc, ite_false]

/-! ## Records -/

theorem R_withC₁ (P : WTParams) (c : ℝ) (q : ℕ) : (MkSlots.withC₁ P c).R q = P.R q := by
  simpa using LGSpine.R_largeConstants P (c * P.C₁) P.C₂ q

theorem N_withC₁ (P : WTParams) (c : ℝ) (q : ℕ) : (MkSlots.withC₁ P c).N q = P.N q :=
  N_bumpC1 P (c * P.C₁) q

theorem mkCarries_withC₁ (P : WTParams) (c : ℝ) {p n : ℕ} {LG : LayeredGarden w}
    (h : MkCarries (MkSlots.withC₁ P c) p n LG) : MkCarries P p n LG := by
  unfold MkCarries at h ⊢
  rw [N_withC₁, N_withC₁] at h
  exact h

/-! ## Pinned points -/

theorem extendFix_mem_pinSet {G : Garden w} (fix : GBranch G.tree → Option ℝ)
    (τ : {b : GBranch G.tree // fix b = none} → ℝ) : G.extendFix fix τ ∈ MkSlotsB.pinSet fix := by
  intro b v h
  unfold Garden.extendFix
  split
  · rename_i v' hv'
    rw [h] at hv'
    exact (Option.some.inj hv').symm
  · rename_i hv'
    rw [h] at hv'
    exact absurd hv' (by simp)

/-! ## Selection-adjacent slots -/

/-- Selected vertices transported along an equality of layered gardens. -/
theorem exists_selSetCap_congr {LG₁ LG₂ : LayeredGarden w} (h : LG₁ = LG₂) (J : Finset (Fin w))
    (kSel : Fin w → Option ℕ) {x : Fin w × List (Fin 3)}
    (hx : ∃ v ∈ selSetCap LG₁ J kSel, v.1 = x) : ∃ v ∈ selSetCap LG₂ J kSel, v.1 = x := by
  subst h
  exact hx

/-- **A slot of `G_sb` with a non-routed residual selected clock is `SelAdj` on the skeleton.** -/
theorem selAdj_iota_of_adjS (J : Finset (Fin w)) (kSel : Fin w → Option ℕ) (a : PrescribedPrimeGarden w)
    (Mk : Set (Stage1.CLVine a.prime.skeleton)) (sl : ReplacementSlot (stSt a.prime.skeleton a.totalSigma Mk).G)
    (h : MkSlotsS.AdjS ((VineB.stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma Mk).route
      a.prime.prime.1 ((stSt a.prime.skeleton a.totalSigma Mk).plain a.prime.prime.1)) (selRAt J kSel a Mk) sl) :
    SelAdj a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel (iotaAt a Mk sl) := by
  obtain ⟨i, v, hv, hr⟩ := h
  have harg := (VineB.stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma Mk).route_inl
    a.prime.prime.1 _ hr
  refine ⟨i, (VineB.stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma Mk).br v, harg, ?_⟩
  have hmem : coreAt a Mk v ∈ selSetCap a.layered J kSel := (Finset.mem_filter.1 hv).2
  exact exists_selSetCap_congr (sourceLayer_reconstructs a).symm J kSel ⟨coreAt a Mk v, hmem, rfl⟩

/-- **Conversely, a `SelAdj` outer slot has a non-routed residual selected clock** (a unit lower joint carries no
selection, δ's `coreBranch_unit_not_sel`). -/
theorem adjS_of_selAdj_iota {J : Finset (Fin w)} (pat : Fin w → FixPat) (t s : ℝ) (kSel : Fin w → Option ℕ)
    (mkF : Stage1Mk.MarkFn w) (hsub : ∀ {LG : LayeredGarden w} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B)
    (a : PrescribedPrimeGarden w) (Mk : Set (Stage1.CLVine a.prime.skeleton)) (hMk : Mk = classMk mkF a)
    (sl : ReplacementSlot (stSt a.prime.skeleton a.totalSigma Mk).G)
    (h : SelAdj a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel (iotaAt a Mk sl)) :
    MkSlotsS.AdjS ((VineB.stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma Mk).route
      a.prime.prime.1 ((stSt a.prime.skeleton a.totalSigma Mk).plain a.prime.prime.1)) (selRAt J kSel a Mk) sl := by
  subst hMk
  set Φ := VineB.stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (classMk mkF a)
  set hSb := (stSt a.prime.skeleton a.totalSigma (classMk mkF a)).plain a.prime.prime.1
  obtain ⟨i, β, harg, v, hv, hvβ⟩ := h
  have hβsel : a.prime.data.decodedCoreBranch a.prime.prime.1 a.prime.decodes β ∈ selSetCap a.layered J kSel := by
    obtain ⟨v', hv', he⟩ := exists_selSetCap_congr (sourceLayer_reconstructs a) J kSel ⟨v, hv, hvβ⟩
    have hveq : v' = a.prime.data.decodedCoreBranch a.prime.prime.1 a.prime.decodes β := Subtype.ext he
    rw [← hveq]
    exact hv'
  rcases Φ.route_natural a.prime.prime.1 hSb sl i with hr | ⟨j, hr⟩
  · have h2 := Φ.route_inl a.prime.prime.1 hSb hr
    rw [harg] at h2
    rcases hsrc : argSrc hSb sl i with k | c
    · rw [hsrc] at h2
      exact absurd h2 (by simp [VineB.SpliceShape.srcMap])
    · rw [hsrc] at h2
      have hβ : β = Φ.br c := Sum.inr_injective h2
      refine ⟨i, c, ?_, by rw [hr, hsrc]⟩
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      rw [hβ] at hβsel
      exact hβsel
  · have h2 := Φ.route_inr a.prime.prime.1 hSb hr
    rw [harg] at h2
    have hβ : β = (VineB.unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (classMk mkF a) j).lower :=
      Sum.inr_injective h2
    rw [hβ] at hβsel
    exact absurd hβsel (MkSlotsS.coreBranch_unit_not_sel pat t s kSel mkF hsub a (List.get_mem _ _)
      (VineB.lower_mem _))

/-- **The selection-adjacent losses**: `∏_{s'} (SelAdj (ι s') ? c : 1) ≤ c^{4 |selR|}`. -/
theorem prod_selAdj_le {J : Finset (Fin w)} (pat : Fin w → FixPat) (t s : ℝ) (kSel : Fin w → Option ℕ)
    (mkF : Stage1Mk.MarkFn w) (hsub : ∀ {LG : LayeredGarden w} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B)
    (a : PrescribedPrimeGarden w) (Mk : Set (Stage1.CLVine a.prime.skeleton)) (hMk : Mk = classMk mkF a)
    {c : ℝ} (hc : 1 ≤ c) :
    ∏ sl : ReplacementSlot (stSt a.prime.skeleton a.totalSigma Mk).G,
      (if SelAdj a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel (iotaAt a Mk sl)
        then c else 1) ≤ c ^ (4 * (selRAt J kSel a Mk).card) := by
  have e : ∀ sl : ReplacementSlot (stSt a.prime.skeleton a.totalSigma Mk).G,
      (if SelAdj a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel (iotaAt a Mk sl)
        then c else 1) =
      (if MkSlotsS.AdjS ((VineB.stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma Mk).route
        a.prime.prime.1 ((stSt a.prime.skeleton a.totalSigma Mk).plain a.prime.prime.1)) (selRAt J kSel a Mk) sl
        then c else 1) := by
    intro sl
    by_cases h : SelAdj a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel
      (iotaAt a Mk sl)
    · rw [if_pos h, if_pos (adjS_of_selAdj_iota pat t s kSel mkF hsub a Mk hMk sl h)]
    · rw [if_neg h, if_neg (fun h' => h (selAdj_iota_of_adjS J kSel a Mk sl h'))]
  rw [Finset.prod_congr rfl fun sl _ => e sl]
  exact prod_adjS_le ((stSt a.prime.skeleton a.totalSigma Mk).plain a.prime.prime.1) _ _
    (fun sl i => (VineB.stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma Mk).route_natural
      a.prime.prime.1 _ sl i) hc

/-! ## Cap pairs among the outer slots -/

theorem leaf_tree_eq {S Gsb : Garden w} {Ju : Type} [Fintype Ju] [DecidableEq Ju] {blk : Ju → RedSplice.CLBlock S}
    (Φ : VineB.SpliceShape blk Gsb) (ℓ : GLeaf Gsb.tree) : (Φ.leaf ℓ).1.1 = ℓ.1.1 := by
  have h := congrArg (fun x : GNode S.tree => x.1.1) (Φ.leaf_node ℓ)
  exact h.trans (Φ.tree_eq ℓ.toNode)

/-- **The skeleton pair of an outer leaf pair is a cap pair iff the leaf pair is.** -/
theorem isCapPair_iota_iff {S Gsb : Garden w} {Ju : Type} [Fintype Ju] [DecidableEq Ju]
    {blk : Ju → RedSplice.CLBlock S} (Φ : VineB.SpliceShape blk Gsb) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (J : Finset (Fin w)) (q : SourcePair Gsb) :
    IsCapPair S hS J (pairOfLeaf S hS (Φ.leaf (q.firstLeaf hSb))) ↔ IsCapPair Gsb hSb J q := by
  unfold IsCapPair
  rw [Φ.iota_first hS hSb q, Φ.iota_second hS hSb q, leaf_tree_eq, leaf_tree_eq]

/-- **The leaf factor of an outer slot**: `b⁻¹` on the cap slots of `G_sb`, times B3's `slotLeaf`. -/
theorem genLeaf_iota {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R))) (b : ℝ)
    (Mk : Set (Stage1.CLVine a.prime.skeleton)) (sl : ReplacementSlot (stSt a.prime.skeleton a.totalSigma Mk).G) :
    genLeaf a J b (iotaAt a Mk sl) =
      (if MkSlots.IntMember.IsCapSlot ((stSt a.prime.skeleton a.totalSigma Mk).plain a.prime.prime.1) J sl
        then b⁻¹ else 1) *
      slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) (fun _ => b.toNNReal)
        (iotaAt a Mk sl) := by
  rcases sl with q | c
  · show (if IsCapPair a.prime.skeleton a.prime.prime.1 J _ then b⁻¹ else 1) * _ = _
    congr 1
    refine if_congr ?_ rfl rfl
    rw [isCapPair_iota_iff]
    constructor
    · intro h; exact ⟨q, rfl, h⟩
    · rintro ⟨q', hq', h⟩
      cases hq'
      exact h
  · rw [if_neg (by rintro ⟨q, hq, -⟩; cases hq), one_mul]
    rfl

/-! ## The piece facts at a marked set equal to the class marking -/

section PieceFacts

variable (P : WTParams) {R : ℕ} (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ)
  (kSel σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (mkF : Stage1Mk.MarkFn (2 * R))
  (a : PrescribedPrimeGarden (2 * R)) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d))

/-- `hfilt` of the engine for the general piece at `Mk = classMk mkF a` (`MkSlotsG.filtGen_ok`). -/
theorem pieceGenAt_filt_le (hsub : ∀ {LG : LayeredGarden (2 * R)} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B)
    (hL : 1 ≤ P.L) (hRs : ∀ j, P.L ≤ Rs j) (Mk : Set (Stage1.CLVine a.prime.skeleton)) (hMk : Mk = classMk mkF a) :
    ∀ c q, (pieceGenAt P J pat t s kSel σ Rs a Mk dag).filt c = some q → ∀ u, ‖q.2 u‖ ≤ 1 := by
  subst hMk
  intro c q hq
  exact (MkSlotsG.filtGen_ok P J pat t s kSel σ Rs mkF a dag hsub hL hRs MkSlotsG.cθGen le_rfl c q hq).2.2.1

/-- `hind` of the engine for the general piece at `Mk = classMk mkF a` (`MkSlotsG.indGen_mem`). -/
theorem pieceGenAt_ind_mem (Mk : Set (Stage1.CLVine a.prime.skeleton)) (hMk : Mk = classMk mkF a) :
    ∀ k, 0 ≤ (pieceGenAt P J pat t s kSel σ Rs a Mk dag).ind k ∧
      (pieceGenAt P J pat t s kSel σ Rs a Mk dag).ind k ≤ 1 := by
  subst hMk
  intro k
  exact MkSlotsG.indGen_mem J P.L σ kSel mkF a dag k

/-- `hselclk` of the engine: no unit clock is a residual selected atom (δ's `selROf_not_unitClock` at a stem-clean
point; no selected atom without selections). -/
theorem selRAt_not_unitClock (hsub : ∀ {LG : LayeredGarden (2 * R)} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B)
    (hstem : ¬ StemDep σ kSel ∨ CleanPt J a) (Mk : Set (Stage1.CLVine a.prime.skeleton)) (hMk : Mk = classMk mkF a) :
    ∀ v ∈ selRAt J kSel a Mk, ∀ j i,
      (VineB.stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma Mk).hclk
        (VineB.unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma Mk) j i ≠ Sum.inr v := by
  subst hMk
  rcases hstem with hnd | hcl
  · intro v hv
    exfalso
    have hk := MkSlotsS.selROf_kSel (mkF := mkF) hv
    apply hnd
    right
    exact ⟨v.1.1, fun h0 => by rw [h0] at hk; exact absurd hk (by simp)⟩
  · exact MkSlotsS.selROf_not_unitClock pat t s kSel mkF hsub hcl

/-- At most `nProt` residual selected atoms. -/
theorem selRAt_card_le (Mk : Set (Stage1.CLVine a.prime.skeleton)) (hMk : Mk = classMk mkF a) :
    (selRAt J kSel a Mk).card ≤ (pieceGenAt P J pat t s kSel σ Rs a Mk dag).nProt := by
  subst hMk
  exact MkSlotsS.selROf_card_le pat t s

end PieceFacts

/-! ## Algebra of the selected mass -/

/-- `selMassMK = b^N · ∏_{kSel j} Rs_j⁻¹ · ∏_{kSel j, j ∉ U} Rs_j^{-1/18}`. -/
theorem selMassMK_eq {R : ℕ} (N : ℕ) (b : ℝ) (Rs : Fin (2 * R) → ℝ) (kSel : Fin (2 * R) → Option ℕ)
    (U : Finset (Fin (2 * R))) :
    selMassMK N b Rs kSel U = b ^ N * ((∏ j, if (kSel j).isSome then (Rs j)⁻¹ else 1) *
      ∏ j, if (kSel j).isSome ∧ j ∉ U then Rs j ^ (-(1 / 18 : ℝ)) else 1) := by
  unfold selMassMK
  rw [← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hk : (kSel j).isSome
  · by_cases hU : j ∈ U
    · simp [hk, hU]
    · simp [hk, hU]
  · simp [hk]

/-- The per-unit top-filter radii: at most two. -/
theorem length_radTGen_le (L : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ) (j : Fin w) :
    (radTGen L σ kSel Rs j).length ≤ 2 := by
  unfold radTGen
  rw [List.length_append]
  have h1 : ((σ j).elim [] (fun i => [2 ^ i * L])).length ≤ 1 := by cases σ j <;> simp
  have h2 : (if (kSel j).isSome then [Rs j] else []).length ≤ 1 := by split_ifs <;> simp
  omega

end WaveTurbulence.Flower.MkSlotsI
