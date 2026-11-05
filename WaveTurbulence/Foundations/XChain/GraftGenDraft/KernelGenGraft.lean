/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.GraftKernelComponents
public import WaveTurbulence.Foundations.XChain.GraftFreeTimes
public import WaveTurbulence.Foundations.XChain.FlowerDraft.GateProbes

/-!
# `kernelKgen_graft`: the general kernel of a graft

Let `𝒢 = graft(top, P, low)` be INDUCT's marked layered graft (`markedLayeredGardenGraft`, `GraftAPI`): a top forest
in layer `p`, an irreducible-or-not partition `P` of its leaves, and plain lower gardens `low B` in layers `< p`
(no lone leaves, no flower parents). Let the data of B1.12's general kernel `kernelKgen` live on the top forest:
* the designated times `fix` vanish on the lower branches, agree with `fixT` on the top branches, and every
  designated value is `≥ p`;
* the removed phases `off` are top branches, those of `offT`;
* the weight is `k ↦ wtop(k|_top)` with `|wtop| ≤ 1`;
* the upper times are `up ≡ t` with `p ≤ t ≤ p + 1`.

**Statement** (`kernelKgen_graft`).
`kernelKgen 𝒢 fix off wt (fun _ => t) k₀ n n'`
` = (c^{n(top)} ∏_{𝔫 ∈ 𝒩(top)} i ζ_𝔫) ∑'_{κ ∈ ForestDecoration top n} topGenFactor(κ) ∏_B kernelK(low B, p, s, k₀, κ|_B, n')`.
Here `topGenFactor(κ) = ε_top(κ) · wtop(k₀ + κ/L) · ∫ 1_{topDomFix} ∏_{𝔫 ∉ offT} e^{πiζ_𝔫δL^{2γ}Ω_𝔫 t_𝔫}`, the integral over
the free top times, and `κ|_B` are the labels of the top leaves of block `B`.

This extends wt-cumul's `kernelK_graft` (GraftAPI; WORKLOG §GRAFT API: "`kernelKgen` off-phase/general weight/further
designated-node variants remain consumer extensions").

**Proof.**
- ε and the inputs factor as in `kernelK_graft` (`markedGardenGraft_epsDec`, `markedLayeredGardenGraft_inputs`).
- The phases with `off` factor branchwise (`prod_graft_branches` and the top/lower sign and `Ω` identities).
- The time domain `kDomainFix` splits: a lower branch lies below `p`, so its order constraint with a top parent holds
  automatically, whether that parent is free (time `> p`) or designated (value `≥ p`).
- The free times split measure-preservingly (`graftFixTimeSplit`, as `graftFreeTimeSplit`). The lower integrals are the lower `kernelK`
  integrals.
- The decoration sum regroups (`tsum_sigma_independent_prod`); it is summable since the summand is bounded by the
  input product (`summable_kernelGenFactor`).

The INDUCT modules used are byte-identical copies (`MANIFEST.md`).
-/

@[expose] public section

namespace WaveTurbulence.GraftGen

open Finset MeasureTheory Induct
open scoped Classical

variable {d w : ℕ}

/-! ## Designated times -/

theorem extendFix_of_some (G : Garden w) {fix : GBranch G.tree → Option ℝ}
    (τ : {b : GBranch G.tree // fix b = none} → ℝ) {b : GBranch G.tree} {v : ℝ} (h : fix b = some v) :
    G.extendFix fix τ b = v := by
  unfold Garden.extendFix
  split
  · next v' h' => rw [h] at h'; exact (Option.some.inj h').symm
  · next h' => rw [h] at h'; exact absurd h' (by simp)

theorem extendFix_of_none (G : Garden w) {fix : GBranch G.tree → Option ℝ}
    (τ : {b : GBranch G.tree // fix b = none} → ℝ) {b : GBranch G.tree} (h : fix b = none) :
    G.extendFix fix τ b = τ ⟨b, h⟩ := by
  unfold Garden.extendFix
  split
  · next v' h' => rw [h] at h'; exact absurd h' (by simp)
  · rfl

/-- Branch times of a forest from its free times. -/
def extendFixF (top : Fin w → TTree) (fix : GBranch top → Option ℝ)
    (τ : {b : GBranch top // fix b = none} → ℝ) : GBranch top → ℝ :=
  fun b => match h : fix b with
    | some v => v
    | none => τ ⟨b, h⟩

theorem extendFixF_of_some (top : Fin w → TTree) {fix : GBranch top → Option ℝ}
    (τ : {b : GBranch top // fix b = none} → ℝ) {b : GBranch top} {v : ℝ} (h : fix b = some v) :
    extendFixF top fix τ b = v := by
  unfold extendFixF
  split
  · next v' h' => rw [h] at h'; exact (Option.some.inj h').symm
  · next h' => rw [h] at h'; exact absurd h' (by simp)

theorem extendFixF_of_none (top : Fin w → TTree) {fix : GBranch top → Option ℝ}
    (τ : {b : GBranch top // fix b = none} → ℝ) {b : GBranch top} (h : fix b = none) :
    extendFixF top fix τ b = τ ⟨b, h⟩ := by
  unfold extendFixF
  split
  · next v' h' => rw [h] at h'; exact absurd h' (by simp)
  · rfl

/-! ## The top forest -/

/-- The top time domain with designated nodes (as `kDomainFix`, all nodes in layer `p`, `up ≡ t`). -/
def topDomFix (top : Fin w → TTree) (p t : ℝ) (fix : GBranch top → Option ℝ) : Set (GBranch top → ℝ) :=
  {τ | ∀ b, (fix b = none → p < τ b ∧ τ b < p + 1 ∧ 0 < τ b ∧ τ b < t) ∧
    ∀ b' : GBranch top, b'.IsChildOf b → (fix b' = none ∨ fix b = none) → τ b' < τ b}

variable (L γ δ : ℝ)

/-- The top phase product with the phases of `off` removed. -/
noncomputable def forestPhaseProdOff (sig : Fin w → ℤˣ) (top : Fin w → TTree) (off : Finset (GBranch top))
    (k : GNode top → Mom d) (τ : GBranch top → ℝ) : ℂ :=
  ∏ b : GBranch top, if b ∈ off then 1 else
    Complex.exp ((Real.pi * ((nodeSign sig b.toNode.1 : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
      resFactor (k (b.child 0)) (k (b.child 1)) (k (b.child 2)) (k b.toNode) * τ b : ℝ) * Complex.I)

/-- The top time integral with designated nodes and removed phases. -/
noncomputable def topFixIntegral (sig : Fin w → ℤˣ) (top : Fin w → TTree) (fix : GBranch top → Option ℝ)
    (off : Finset (GBranch top)) (k : GNode top → Mom d) (p t : ℝ) : ℂ :=
  ∫ τ : {b : GBranch top // fix b = none} → ℝ,
    (topDomFix top p t fix).indicator (forestPhaseProdOff L γ δ sig top off k) (extendFixF top fix τ)

/-- **The top factor** `ε_top(κ) · wtop(k₀ + κ/L) · ∫ 1_{topDomFix} ∏_{𝔫 ∉ off} e^{…}`. -/
noncomputable def topGenFactor (sig : Fin w → ℤˣ) (top : Fin w → TTree) (fix : GBranch top → Option ℝ)
    (off : Finset (GBranch top)) (wtop : (GNode top → Mom d) → ℝ) (kt : GNode top → (Fin d → ℤ)) (k₀ : Mom d)
    (p t : ℝ) : ℂ :=
  (((∏ b : GBranch top, epsCoef (kt (b.child 0)) (kt (b.child 1)) (kt (b.child 2))) : ℝ) : ℂ) *
    (wtop (fun a => k₀ + latticePoint L (kt a)) : ℂ) *
      topFixIntegral L γ δ sig top fix off (fun a => k₀ + latticePoint L (kt a)) p t

/-! ## The summand of `kernelKgen` -/

/-- The time integral of `kernelKgen` at one decoration. -/
noncomputable def genIntegral (LG : LayeredGarden w) (fix : GBranch LG.garden.tree → Option ℝ)
    (off : Finset (GBranch LG.garden.tree)) (up : GBranch LG.garden.tree → ℝ) (k : GNode LG.garden.tree → Mom d) :
    ℂ :=
  ∫ τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ,
    (kDomainFix LG up fix).indicator (phaseProdOff L γ δ LG.garden off k) (LG.garden.extendFix fix τ)

/-- **The summand of `kernelKgen`.** -/
noncomputable def kernelGenFactor (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w)
    (fix : GBranch LG.garden.tree → Option ℝ) (off : Finset (GBranch LG.garden.tree))
    (wt : (GNode LG.garden.tree → Mom d) → ℝ) (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom d)
    {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ} (κ : GenDecoration LG.garden d n nfl) : ℂ :=
  (epsDec LG.garden κ.1 : ℂ) * (wt (cosetDecoration LG.garden L k₀ κ.1) : ℂ) *
    genIntegral L γ δ LG fix off up (cosetDecoration LG.garden L k₀ κ.1) *
      ∏ ℓ ∈ inputLeaves LG.garden, (F (LG.layer ℓ.toNode) (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)

theorem kernelKgen_eq_tsum (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w)
    (fix : GBranch LG.garden.tree → Option ℝ) (off : Finset (GBranch LG.garden.tree))
    (wt : (GNode LG.garden.tree → Mom d) → ℝ) (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom d)
    (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) :
    kernelKgen L γ δ F LG fix off wt up k₀ n nfl =
      (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
        ∑' κ : GenDecoration LG.garden d n nfl, kernelGenFactor L γ δ F LG fix off wt up k₀ κ := rfl

/-! ## Summability -/

theorem norm_phaseProdOff_le (G : Garden w) (off : Finset (GBranch G.tree)) (k : GNode G.tree → Mom d)
    (τ : GBranch G.tree → ℝ) : ‖phaseProdOff L γ δ G off k τ‖ ≤ 1 := by
  unfold phaseProdOff
  rw [norm_prod]
  refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun b _ => ?_
  split_ifs
  · simp
  · exact le_of_eq (Complex.norm_exp_ofReal_mul_I _)

theorem norm_genIntegral_le (LG : LayeredGarden w) (fix : GBranch LG.garden.tree → Option ℝ)
    (off : Finset (GBranch LG.garden.tree)) (up : GBranch LG.garden.tree → ℝ) (k : GNode LG.garden.tree → Mom d) :
    ‖genIntegral L γ δ LG fix off up k‖ ≤
      (volume : Measure ({b : GBranch LG.garden.tree // fix b = none} → ℝ)).real
        (Set.pi Set.univ fun b => Set.Icc (LG.layer b.1.toNode : ℝ) (LG.layer b.1.toNode + 1)) := by
  set Box : Set ({b : GBranch LG.garden.tree // fix b = none} → ℝ) :=
    Set.pi Set.univ fun b => Set.Icc (LG.layer b.1.toNode : ℝ) (LG.layer b.1.toNode + 1)
  have hBm : MeasurableSet Box := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hBc : IsCompact Box := isCompact_univ_pi fun _ => isCompact_Icc
  unfold genIntegral
  rw [← integral_indicator_one hBm]
  refine norm_integral_le_of_norm_le ((integrable_indicator_iff hBm).2
    (integrableOn_const hBc.measure_lt_top.ne)) (Filter.Eventually.of_forall fun τ => ?_)
  by_cases hD : LG.garden.extendFix fix τ ∈ kDomainFix LG up fix
  · have hτ : τ ∈ Box := fun b _ => by
      have h := (hD b.1).1 b.2
      rw [extendFix_of_none LG.garden τ b.2] at h
      exact ⟨h.1.le, h.2.1.le⟩
    rw [Set.indicator_of_mem hD, Set.indicator_of_mem hτ]
    exact norm_phaseProdOff_le L γ δ _ _ _ _
  · rw [Set.indicator_of_notMem hD, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

/-- **The summand of `kernelKgen` is summable** without lone leaves, for bounded weights and summable inputs.
The decoration is determined by its input-leaf values: this is the argument of the snapshot's
`summable_kernelK_summand` (`WaveB1-Lemmas.lean`), with the bound `‖genIntegral‖ ≤ |box|`. -/
theorem summable_kernelGenFactor (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w)
    (fix : GBranch LG.garden.tree → Option ℝ) (off : Finset (GBranch LG.garden.tree))
    (wt : (GNode LG.garden.tree → Mom d) → ℝ) (hwt : ∀ k, |wt k| ≤ 1) (up : GBranch LG.garden.tree → ℝ)
    (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hn : ∀ ℓ, LG.garden.mark ℓ ≠ some MarkTag.lower)
    (hF : ∀ q, Summable fun m : Fin d → ℤ => |F q (k₀ + latticePoint L m)|) :
    Summable (kernelGenFactor L γ δ F LG fix off wt up k₀ (n := nroot) (nfl := nfl)) := by
  let ι := {ℓ : GLeaf LG.garden.tree // ℓ ∈ inputLeaves LG.garden}
  let Φ : GenDecoration LG.garden d nroot nfl → (ι → (Fin d → ℤ)) := fun κ ℓ => κ.1 ℓ.1.toNode
  -- the decoration is determined by its input-leaf values
  have hΦ : Function.Injective Φ := by
    intro κ κ' hκ
    let δ' : GNode LG.garden.tree → (Fin d → ℤ) := fun a => κ.1 a - κ'.1 a
    have hδb : ∀ b : GBranch LG.garden.tree,
        δ' b.toNode = δ' (b.child 0) - δ' (b.child 1) + δ' (b.child 2) := by
      intro b
      simp only [δ', κ.2.1.1 b, κ'.2.1.1 b]
      abel
    have hin : ∀ ℓ ∈ inputLeaves LG.garden, δ' ℓ.toNode = 0 := fun ℓ hℓ => by
      have := congrFun hκ ⟨ℓ, hℓ⟩
      simp only [Φ] at this
      simp [δ', this]
    have hleaf : ∀ ℓ : GLeaf LG.garden.tree, ¬ LG.garden.IsLone ℓ → δ' ℓ.toNode = 0 := by
      intro ℓ hnl
      by_cases hm : LG.garden.mark ℓ = none
      · by_cases hs : LG.garden.sign ℓ.toNode = 1
        · exact hin ℓ (by simp [inputLeaves, hs, hm])
        · have hne : LG.garden.pair ℓ ≠ ℓ := fun h => ((LG.garden.pair_eq_iff ℓ).1 h) hm
          have hs' : LG.garden.sign ℓ.toNode = -1 := by
            rcases Int.units_eq_one_or (LG.garden.sign ℓ.toNode) with h | h
            · exact absurd h hs
            · exact h
          have hpm : LG.garden.mark (LG.garden.pair ℓ) = none := by
            by_contra h
            have := (LG.garden.pair_eq_iff (LG.garden.pair ℓ)).2 h
            rw [LG.garden.pair_pair] at this
            exact hne this.symm
          have hps : LG.garden.sign (LG.garden.pair ℓ).toNode = 1 := by
            have := LG.garden.pair_sign ℓ hne
            change nodeSign LG.garden.sig (LG.garden.pair ℓ).1 = -nodeSign LG.garden.sig ℓ.1 at this
            change nodeSign LG.garden.sig (LG.garden.pair ℓ).1 = 1
            rw [this]
            change -LG.garden.sign ℓ.toNode = 1
            rw [hs']
            rfl
          have h0 := hin (LG.garden.pair ℓ) (by simp [inputLeaves, hps, hpm])
          simp only [δ'] at h0 ⊢
          rw [κ.2.1.2 ℓ, κ'.2.1.2 ℓ]
          exact h0
      · have hfl : LG.garden.IsFlower ℓ := by
          rcases hmk : LG.garden.mark ℓ with _ | tag
          · exact absurd hmk hm
          · cases tag
            · exact absurd hmk hnl
            · exact hmk
        simp [δ', κ.2.2.2 ℓ hfl, κ'.2.2.2 ℓ hfl]
    have hlone' : ∀ ℓ ℓ' : GLeaf LG.garden.tree, LG.garden.IsLone ℓ → LG.garden.IsLone ℓ' →
        ℓ.1.1 = ℓ'.1.1 → ℓ = ℓ' := fun ℓ _ h _ _ => absurd h (hn ℓ)
    have hroot : ∀ j, δ' (GNode.root LG.garden.tree j) = 0 := fun j => by
      simp [δ', κ.2.2.1 j, κ'.2.2.1 j]
    apply Subtype.ext
    funext a
    exact sub_eq_zero.1 (eq_zero_of_roots_leaves_zero δ' hδb LG.garden.IsLone hlone' hroot hleaf a)
  -- the dominating summable family
  let f : ι → (Fin d → ℤ) → ℝ := fun ℓ m => |F (LG.layer ℓ.1.toNode) (k₀ + latticePoint L m)|
  have hf : Summable fun z : ι → (Fin d → ℤ) => ∏ ℓ, f ℓ (z ℓ) :=
    summable_pi_prod f (fun _ _ => abs_nonneg _) fun ℓ => hF _
  set C := (volume : Measure ({b : GBranch LG.garden.tree // fix b = none} → ℝ)).real
    (Set.pi Set.univ fun b => Set.Icc (LG.layer b.1.toNode : ℝ) (LG.layer b.1.toNode + 1))
  refine Summable.of_norm_bounded ((hf.comp_injective hΦ).mul_left C) fun κ => ?_
  unfold kernelGenFactor
  rw [norm_mul, norm_mul, norm_mul, norm_prod]
  simp only [Complex.norm_real, Real.norm_eq_abs, Function.comp_apply]
  have hprod : ∏ ℓ ∈ inputLeaves LG.garden,
      |F (LG.layer ℓ.toNode) (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode)| = ∏ ℓ : ι, f ℓ (Φ κ ℓ) := by
    rw [← Finset.prod_coe_sort]
    rfl
  rw [hprod]
  have hC : 0 ≤ C := measureReal_nonneg
  have hP : 0 ≤ ∏ ℓ : ι, f ℓ (Φ κ ℓ) := Finset.prod_nonneg fun _ _ => abs_nonneg _
  calc |epsDec LG.garden κ.1| * |wt (cosetDecoration LG.garden L k₀ κ.1)| *
        ‖genIntegral L γ δ LG fix off up (cosetDecoration LG.garden L k₀ κ.1)‖ * ∏ ℓ : ι, f ℓ (Φ κ ℓ)
      ≤ 1 * 1 * C * ∏ ℓ : ι, f ℓ (Φ κ ℓ) := by
        gcongr
        · exact abs_epsDec_le_one LG.garden κ.1
        · exact hwt _
        · exact norm_genIntegral_le L γ δ LG fix off up _
    _ = C * ∏ ℓ : ι, f ℓ (Φ κ ℓ) := by ring

/-! ## The graft: domain and phases -/

section Graft

variable {sig : Fin w → ℤˣ} {top : Fin w → TTree} {P : Finpartition (univ : Finset (GLeaf top))}
  {low : (B : P.parts) → LayeredGarden B.1.card} {p : ℕ}
  {hsig : ∀ B k, (low B).garden.sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1}
  {hbound : ∀ B a, (low B).layer a ≤ p}

theorem graft_layer_top (b : GBranch top) :
    (markedLayeredGardenGraft sig top P low p hsig hbound).layer
      (gardenBranchEquiv top P (fun B => (low B).garden) (.inl b)).toNode = p :=
  (congrArg (graftLayer top P low p) (gardenBranch_toNode_top top P (fun B => (low B).garden) b)).trans
    (graftLayer_top top P low p b)

theorem graft_layer_lower (B : P.parts) (b : GBranch (low B).garden.tree) :
    (markedLayeredGardenGraft sig top P low p hsig hbound).layer
      (gardenBranchEquiv top P (fun B => (low B).garden) (.inr ⟨B, b⟩)).toNode = (low B).layer b.toNode :=
  (congrArg (graftLayer top P low p) (gardenBranch_toNode_lower top P (fun B => (low B).garden) B b)).trans
    (graftLayer_lower top P low p B b.toNode)

/-- **The domain splits.** The top part is in `topDomFix`, each lower part in the lower `kDomain`. The constraint
between a lower root and its top parent holds automatically, since lower times are `< p` and top times are `≥ p`. -/
theorem kDomainFix_graft_iff (hbranch : ∀ B (b : GBranch (low B).garden.tree), (low B).layer b.toNode < p)
    (hn : ∀ B ℓ, (low B).garden.mark ℓ ≠ some MarkTag.lower)
    (fix : GBranch (markedLayeredGardenGraft sig top P low p hsig hbound).garden.tree → Option ℝ)
    (hfixL : ∀ z, fix (gardenBranchEquiv top P (fun B => (low B).garden) (.inr z)) = none)
    (t s : ℝ) (hpt : (p : ℝ) ≤ t)
    (x : GBranch (markedLayeredGardenGraft sig top P low p hsig hbound).garden.tree → ℝ)
    (hx : ∀ b, fix (gardenBranchEquiv top P (fun B => (low B).garden) (.inl b)) ≠ none →
      (p : ℝ) ≤ x (gardenBranchEquiv top P (fun B => (low B).garden) (.inl b))) :
    x ∈ kDomainFix (markedLayeredGardenGraft sig top P low p hsig hbound) (fun _ => t) fix ↔
      (fun b => x (gardenBranchEquiv top P (fun B => (low B).garden) (.inl b))) ∈
          topDomFix top p t (fun b => fix (gardenBranchEquiv top P (fun B => (low B).garden) (.inl b))) ∧
        ∀ B, (fun b => x (gardenBranchEquiv top P (fun B => (low B).garden) (.inr ⟨B, b⟩))) ∈
          kDomain (low B) (fun _ => p) s := by
  set e := gardenBranchEquiv top P (fun B => (low B).garden)
  have hlt : ∀ b, (markedLayeredGardenGraft sig top P low p hsig hbound).layer (e (.inl b)).toNode = p :=
    fun b => graft_layer_top b
  have hll : ∀ B (b : GBranch (low B).garden.tree),
      (markedLayeredGardenGraft sig top P low p hsig hbound).layer (e (.inr ⟨B, b⟩)).toNode =
        (low B).layer b.toNode := fun B b => graft_layer_lower B b
  have hlowp : ∀ B (b : GBranch (low B).garden.tree), ((low B).layer b.toNode : ℝ) + 1 ≤ p := fun B b => by
    exact_mod_cast Nat.succ_le_iff.mpr (hbranch B b)
  constructor
  · intro h
    refine ⟨fun b => ⟨fun hb => ?_, fun b' hb' hor => ?_⟩, fun B => ?_⟩
    · have h1 := (h (e (.inl b))).1 hb
      have hT : (((markedLayeredGardenGraft sig top P low p hsig hbound).layer (e (.inl b)).toNode : ℕ) : ℝ) =
          (p : ℝ) := by exact_mod_cast hlt b
      exact ⟨hT.symm.trans_lt h1.1, h1.2.1.trans_eq (congrArg (· + 1) hT), h1.2.2.1, h1.2.2.2⟩
    · exact (h (e (.inl b))).2 (e (.inl b')) ((graft_top_branch_edge_iff top P (fun B => (low B).garden) b' b).mpr hb') hor
    · refine (kDomain_iff_bounds_order (low B) p s (hn B) _).mpr ⟨fun b => ?_, fun a b hab => ?_⟩
      · have h1 := (h (e (.inr ⟨B, b⟩))).1 (hfixL _)
        have hT : (((markedLayeredGardenGraft sig top P low p hsig hbound).layer (e (.inr ⟨B, b⟩)).toNode : ℕ) :
            ℝ) = ((low B).layer b.toNode : ℝ) := by exact_mod_cast hll B b
        have h2 : x (e (.inr ⟨B, b⟩)) < ((low B).layer b.toNode : ℝ) + 1 := h1.2.1.trans_eq (congrArg (· + 1) hT)
        exact ⟨hT.symm.trans_lt h1.1, h2, h1.2.2.1, h2.trans_le (hlowp B b)⟩
      · exact (h (e (.inr ⟨B, b⟩))).2 (e (.inr ⟨B, a⟩)) (graft_lower_branch_edge top P (fun B => (low B).garden) B a b hab)
          (Or.inl (hfixL _))
  · rintro ⟨ht, hl⟩ b
    have hlo := fun B => (kDomain_iff_bounds_order (low B) p s (hn B) _).mp (hl B)
    obtain ⟨z, rfl⟩ := e.surjective b
    rcases z with b | ⟨B, b⟩
    · refine ⟨fun hb => ?_, fun b' hb' hor => ?_⟩
      · have hT : (((markedLayeredGardenGraft sig top P low p hsig hbound).layer (e (.inl b)).toNode : ℕ) : ℝ) =
            (p : ℝ) := by exact_mod_cast hlt b
        have h1 := (ht b).1 hb
        exact ⟨hT.trans_lt h1.1, h1.2.1.trans_eq (congrArg (· + 1) hT.symm), h1.2.2.1, h1.2.2.2⟩
      · obtain ⟨z', rfl⟩ := e.surjective b'
        rcases z' with a | ⟨B, a⟩
        · exact (ht b).2 a ((graft_top_branch_edge_iff top P (fun B => (low B).garden) a b).mp hb') hor
        · have hlow := ((hlo B).1 a).2.2.2
          have htop : (p : ℝ) ≤ x (e (.inl b)) := by
            by_cases hf : fix (e (.inl b)) = none
            · exact ((ht b).1 hf).1.le
            · exact hx b hf
          exact hlow.trans_le htop
    · refine ⟨fun _ => ?_, fun b' hb' _ => ?_⟩
      · have hT : (((markedLayeredGardenGraft sig top P low p hsig hbound).layer (e (.inr ⟨B, b⟩)).toNode : ℕ) :
            ℝ) = ((low B).layer b.toNode : ℝ) := by exact_mod_cast hll B b
        have h1 := (hlo B).1 b
        exact ⟨hT.trans_lt h1.1, h1.2.1.trans_eq (congrArg (· + 1) hT.symm), h1.2.2.1, h1.2.2.2.trans_le hpt⟩
      · obtain ⟨c, rfl, hc⟩ := graft_child_of_lower top P (fun B => (low B).garden) B b b' hb'
        exact (hlo B).2 c b hc

/-- **The phases split**, with `off` on the top. -/
theorem phaseProdOff_graft (off : Finset (GBranch (markedLayeredGardenGraft sig top P low p hsig hbound).garden.tree))
    (offT : Finset (GBranch top))
    (hoffT : ∀ b, gardenBranchEquiv top P (fun B => (low B).garden) (.inl b) ∈ off ↔ b ∈ offT)
    (hoffL : ∀ z, gardenBranchEquiv top P (fun B => (low B).garden) (.inr z) ∉ off)
    (k : GNode (markedLayeredGardenGraft sig top P low p hsig hbound).garden.tree → Mom d)
    (x : GBranch (markedLayeredGardenGraft sig top P low p hsig hbound).garden.tree → ℝ) :
    phaseProdOff L γ δ (markedLayeredGardenGraft sig top P low p hsig hbound).garden off k x =
      forestPhaseProdOff L γ δ sig top offT
          (fun a => k (topNodeEmbedding top P (fun B => (low B).garden) a))
          (fun b => x (gardenBranchEquiv top P (fun B => (low B).garden) (.inl b))) *
        ∏ B, phaseProd L γ δ (low B).garden
          (fun a => k (lowerNodeEmbedding top P (fun B => (low B).garden) B a))
          (fun b => x (gardenBranchEquiv top P (fun B => (low B).garden) (.inr ⟨B, b⟩))) := by
  unfold phaseProdOff forestPhaseProdOff phaseProd
  refine (prod_graft_branches top P (fun B => (low B).garden) _).trans ?_
  congr 1
  · refine Finset.prod_congr rfl fun b _ => ?_
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd ((hoffT b).mp h1) h2
    · exact absurd ((hoffT b).mpr h2) h1
    · exact congrArg₂ (fun (ζ : ℤˣ) (ω : ℝ) => Complex.exp ((Real.pi * (ζ : ℤ) * δ * L ^ (2 * γ) * ω *
        x (gardenBranchEquiv top P (fun B => (low B).garden) (.inl b)) : ℝ) * Complex.I))
        (gardenBranchEquiv_top_sign sig top P (fun B => (low B).garden) b)
        (markedGardenGraft_omega_top sig top P (fun B => (low B).garden) hsig k b)
  · refine Finset.prod_congr rfl fun B _ => Finset.prod_congr rfl fun b _ => ?_
    split_ifs with h1
    · exact absurd h1 (hoffL _)
    · exact congrArg₂ (fun (ζ : ℤˣ) (ω : ℝ) => Complex.exp ((Real.pi * (ζ : ℤ) * δ * L ^ (2 * γ) * ω *
        x (gardenBranchEquiv top P (fun B => (low B).garden) (.inr ⟨B, b⟩)) : ℝ) * Complex.I))
        (gardenBranchEquiv_lower_sign sig top P (fun B => (low B).garden) hsig B b)
        (markedGardenGraft_omega_lower sig top P (fun B => (low B).garden) hsig k B b)

end Graft

/-! ## The integral -/

section Integral

/-- The free-time split of `graftFreeTimeSplit` (GraftAPI) for the predicate `fix b = none`, restated so that
the subtypes carry the `Fintype` instances of `kernelKgen` (`Option.decidableEqNone`). -/
noncomputable def graftFixTimeSplit (top : Fin w → TTree) (P : Finpartition (univ : Finset (GLeaf top)))
    (low : (B : P.parts) → Garden B.1.card) (fix : GBranch (graftForest top (blockGraftTrees top P low)) → Option ℝ) :
    ({b : GBranch (graftForest top (blockGraftTrees top P low)) // fix b = none} → ℝ) ≃ᵐ
      ({b : GBranch top // fix (gardenBranchEquiv top P low (.inl b)) = none} → ℝ) ×
      ({z : Σ B : P.parts, GBranch (low B).tree // fix (gardenBranchEquiv top P low (.inr z)) = none} → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (graftFreeBranchEquiv top P low (fun b => fix b = none))).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ))

theorem measurePreserving_graftFixTimeSplit (top : Fin w → TTree) (P : Finpartition (univ : Finset (GLeaf top)))
    (low : (B : P.parts) → Garden B.1.card) (fix : GBranch (graftForest top (blockGraftTrees top P low)) → Option ℝ) :
    MeasurePreserving (graftFixTimeSplit top P low fix) volume
      ((volume : Measure ({b : GBranch top // fix (gardenBranchEquiv top P low (.inl b)) = none} → ℝ)).prod
        (volume : Measure ({z : Σ B : P.parts, GBranch (low B).tree //
          fix (gardenBranchEquiv top P low (.inr z)) = none} → ℝ))) := by
  have h₁ := (measurePreserving_piCongrLeft
    (fun _ : {b : GBranch (graftForest top (blockGraftTrees top P low)) // fix b = none} =>
      (volume : Measure ℝ)) (graftFreeBranchEquiv top P low (fun b => fix b = none))).symm
  have h₂ := measurePreserving_sumPiEquivProdPi
    (fun _ : {b : GBranch top // fix (gardenBranchEquiv top P low (.inl b)) = none} ⊕
      {z : Σ B : P.parts, GBranch (low B).tree // fix (gardenBranchEquiv top P low (.inr z)) = none} =>
        (volume : Measure ℝ))
  exact h₂.comp h₁

variable {sig : Fin w → ℤˣ} {top : Fin w → TTree} {P : Finpartition (univ : Finset (GLeaf top))}
  {low : (B : P.parts) → LayeredGarden B.1.card} {p : ℕ}
  {hsig : ∀ B k, (low B).garden.sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1}
  {hbound : ∀ B a, (low B).layer a ≤ p}

/-- **The integral factors**: the top integral with designated nodes times the lower phase integrals. -/
theorem genIntegral_graft (hbranch : ∀ B (b : GBranch (low B).garden.tree), (low B).layer b.toNode < p)
    (hn : ∀ B ℓ, (low B).garden.mark ℓ ≠ some MarkTag.lower)
    (hf : ∀ B b, ¬ (low B).garden.IsFlowerParent b)
    (fix : GBranch (markedLayeredGardenGraft sig top P low p hsig hbound).garden.tree → Option ℝ)
    (hfixL : ∀ z, fix (gardenBranchEquiv top P (fun B => (low B).garden) (.inr z)) = none)
    (hfixv : ∀ b v, fix (gardenBranchEquiv top P (fun B => (low B).garden) (.inl b)) = some v → (p : ℝ) ≤ v)
    (off : Finset (GBranch (markedLayeredGardenGraft sig top P low p hsig hbound).garden.tree))
    (offT : Finset (GBranch top))
    (hoffT : ∀ b, gardenBranchEquiv top P (fun B => (low B).garden) (.inl b) ∈ off ↔ b ∈ offT)
    (hoffL : ∀ z, gardenBranchEquiv top P (fun B => (low B).garden) (.inr z) ∉ off)
    (t s : ℝ) (hpt : (p : ℝ) ≤ t)
    (k : GNode (markedLayeredGardenGraft sig top P low p hsig hbound).garden.tree → Mom d) :
    genIntegral L γ δ (markedLayeredGardenGraft sig top P low p hsig hbound) fix off (fun _ => t) k =
      topFixIntegral L γ δ sig top (fun b => fix (gardenBranchEquiv top P (fun B => (low B).garden) (.inl b)))
          offT (fun a => k (topNodeEmbedding top P (fun B => (low B).garden) a)) p t *
        ∏ B, phaseIntegral L γ δ (low B).garden (kDomain (low B) (fun _ => p) s) s
          (fun a => k (lowerNodeEmbedding top P (fun B => (low B).garden) B a)) := by
  set e := gardenBranchEquiv top P (fun B => (low B).garden)
  set fixT : GBranch top → Option ℝ := fun b => fix (e (.inl b)) with hfixTdef
  set ktop := fun a => k (topNodeEmbedding top P (fun B => (low B).garden) a)
  set klow := fun B a => k (lowerNodeEmbedding top P (fun B => (low B).garden) B a)
  set Top : ({b : GBranch top // fix (e (.inl b)) = none} → ℝ) → ℂ := fun u =>
    (topDomFix top p t fixT).indicator (forestPhaseProdOff L γ δ sig top offT ktop) (extendFixF top fixT u)
  set Low : ({z : Σ B : P.parts, GBranch (low B).garden.tree // fix (e (.inr z)) = none} → ℝ) → ℂ := fun v =>
    ∏ B, (kDomain (low B) (fun _ => p) s).indicator (phaseProd L γ δ (low B).garden (klow B))
      (fun b => v ⟨⟨B, b⟩, hfixL _⟩)
  -- pointwise
  have hpt' : ∀ τ : {b : GBranch (markedLayeredGardenGraft sig top P low p hsig hbound).garden.tree // fix b = none} → ℝ,
      (kDomainFix (markedLayeredGardenGraft sig top P low p hsig hbound) (fun _ => t) fix).indicator (phaseProdOff L γ δ (markedLayeredGardenGraft sig top P low p hsig hbound).garden off k) ((markedLayeredGardenGraft sig top P low p hsig hbound).garden.extendFix fix τ) =
        Top (graftFixTimeSplit top P (fun B => (low B).garden) fix τ).1 * Low (graftFixTimeSplit top P (fun B => (low B).garden) fix τ).2 := by
    intro τ
    set x := (markedLayeredGardenGraft sig top P low p hsig hbound).garden.extendFix fix τ with hxdef
    have hxt : (fun b => x (e (.inl b))) = extendFixF top fixT (graftFixTimeSplit top P (fun B => (low B).garden) fix τ).1 := by
      funext b
      rw [hxdef]
      rcases h : fix (e (.inl b)) with _ | v
      · rw [extendFix_of_none (markedLayeredGardenGraft sig top P low p hsig hbound).garden τ h]
        have h' : fixT b = none := h
        rw [extendFixF_of_none top _ h']
        rfl
      · rw [extendFix_of_some (markedLayeredGardenGraft sig top P low p hsig hbound).garden τ h]
        have h' : fixT b = some v := h
        rw [extendFixF_of_some top _ h']
    have hxl : ∀ B, (fun b => x (e (.inr ⟨B, b⟩))) =
        fun b => (graftFixTimeSplit top P (fun B => (low B).garden) fix τ).2 ⟨⟨B, b⟩, hfixL _⟩ := fun B => by
      funext b
      rw [hxdef, extendFix_of_none (markedLayeredGardenGraft sig top P low p hsig hbound).garden τ (hfixL _)]
      rfl
    have hx : ∀ b, fix (e (.inl b)) ≠ none → (p : ℝ) ≤ x (e (.inl b)) := by
      intro b hb
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hb
      rw [hxdef, extendFix_of_some (markedLayeredGardenGraft sig top P low p hsig hbound).garden τ hv]
      exact hfixv b v hv
    have hd := kDomainFix_graft_iff hbranch hn fix hfixL t s hpt x hx
    have hp := phaseProdOff_graft L γ δ off offT hoffT hoffL k x
    unfold Set.indicator
    rw [hp]
    have hc : (if x ∈ kDomainFix (markedLayeredGardenGraft sig top P low p hsig hbound) (fun _ => t) fix then
          forestPhaseProdOff L γ δ sig top offT ktop (fun b => x (e (.inl b))) *
            ∏ B, phaseProd L γ δ (low B).garden (klow B) (fun b => x (e (.inr ⟨B, b⟩))) else 0) =
        (if (fun b => x (e (.inl b))) ∈ topDomFix top p t fixT ∧
            ∀ B, (fun b => x (e (.inr ⟨B, b⟩))) ∈ kDomain (low B) (fun _ => p) s then
          forestPhaseProdOff L γ δ sig top offT ktop (fun b => x (e (.inl b))) *
            ∏ B, phaseProd L γ δ (low B).garden (klow B) (fun b => x (e (.inr ⟨B, b⟩))) else 0) := by
      by_cases hh : x ∈ kDomainFix (markedLayeredGardenGraft sig top P low p hsig hbound) (fun _ => t) fix
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hh), ite_eq_left_of_eq_true _ _ (eq_true (hd.mp hh))]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hh),
          ite_eq_right_of_eq_false _ _ (eq_false (fun h => hh (hd.mpr h)))]
    rw [hc, ite_and_forall_mul_prod]
    simp only [Top, Low, Set.indicator]
    rw [← hxt]
    congr 1
    refine Finset.prod_congr rfl fun B _ => ?_
    rw [← hxl B]
  have hmp := measurePreserving_graftFixTimeSplit top P (fun B => (low B).garden) fix
  -- the lower integral
  have hlow : ∫ v, Low v = ∏ B, phaseIntegral L γ δ (low B).garden (kDomain (low B) (fun _ => p) s) s (klow B) := by
    let eqv : {z : Σ B : P.parts, GBranch (low B).garden.tree // fix (e (.inr z)) = none} ≃
        (Σ B : P.parts, GBranch (low B).garden.tree) := Equiv.subtypeUnivEquiv hfixL
    have hmpl := measurePreserving_piCongrLeft (fun _ : Σ B : P.parts, GBranch (low B).garden.tree =>
      (volume : Measure ℝ)) eqv
    let G : ((Σ B : P.parts, GBranch (low B).garden.tree) → ℝ) → ℂ := fun y =>
      ∏ B, (kDomain (low B) (fun _ => p) s).indicator (phaseProd L γ δ (low B).garden (klow B))
        (fun b => y ⟨B, b⟩)
    have hLG : ∀ v, Low v = G (MeasurableEquiv.piCongrLeft (fun _ => ℝ) eqv v) := fun v => by
      simp only [Low, G]
      refine Finset.prod_congr rfl fun B _ => ?_
      congr 1
    calc ∫ v, Low v = ∫ v, G (MeasurableEquiv.piCongrLeft (fun _ => ℝ) eqv v) :=
          integral_congr_ae (Filter.Eventually.of_forall hLG)
      _ = ∫ y, G y := hmpl.integral_comp' G
      _ = ∏ B, ∫ τ, (kDomain (low B) (fun _ => p) s).indicator (phaseProd L γ δ (low B).garden (klow B)) τ :=
          integral_lowerTime_prod top P (fun B => (low B).garden)
            (fun B => (kDomain (low B) (fun _ => p) s).indicator (phaseProd L γ δ (low B).garden (klow B)))
      _ = _ := Finset.prod_congr rfl fun B _ =>
          (phaseIntegral_of_no_flowerParent L γ δ (low B).garden (hf B) _ s (klow B)).symm
  unfold genIntegral
  refine (integral_congr_ae (Filter.Eventually.of_forall hpt')).trans ?_
  refine (hmp.integral_comp' (fun z => Top z.1 * Low z.2)).trans ?_
  rw [integral_prod_mul Top Low, hlow]
  rfl

end Integral

/-! ## The kernel -/

section Kernel

variable {sig : Fin w → ℤˣ} {top : Fin w → TTree} {P : Finpartition (univ : Finset (GLeaf top))}
  {low : (B : P.parts) → LayeredGarden B.1.card} {p : ℕ}
  {hsig : ∀ B k, (low B).garden.sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1}
  {hbound : ∀ B a, (low B).layer a ≤ p}

/-- **One decoration**: the summand of `kernelKgen` on the graft is the top factor times the lower summands. -/
theorem kernelGenFactor_graft (F : ℕ → Mom d → ℝ)
    (hbranch : ∀ B (b : GBranch (low B).garden.tree), (low B).layer b.toNode < p)
    (hn : ∀ B ℓ, (low B).garden.mark ℓ ≠ some MarkTag.lower)
    (hf : ∀ B b, ¬ (low B).garden.IsFlowerParent b)
    (fix : GBranch (markedLayeredGardenGraft sig top P low p hsig hbound).garden.tree → Option ℝ)
    (fixT : GBranch top → Option ℝ)
    (hfixT : ∀ b, fix (gardenBranchEquiv top P (fun B => (low B).garden) (.inl b)) = fixT b)
    (hfixL : ∀ z, fix (gardenBranchEquiv top P (fun B => (low B).garden) (.inr z)) = none)
    (hfixv : ∀ b v, fixT b = some v → (p : ℝ) ≤ v)
    (off : Finset (GBranch (markedLayeredGardenGraft sig top P low p hsig hbound).garden.tree))
    (offT : Finset (GBranch top))
    (hoffT : ∀ b, gardenBranchEquiv top P (fun B => (low B).garden) (.inl b) ∈ off ↔ b ∈ offT)
    (hoffL : ∀ z, gardenBranchEquiv top P (fun B => (low B).garden) (.inr z) ∉ off)
    (wtop : (GNode top → Mom d) → ℝ) (t s : ℝ) (hpt : (p : ℝ) ≤ t) (k₀ : Mom d)
    (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (κ : GenDecoration (markedGardenGraft sig top P (fun B => (low B).garden) hsig) d n nfl) :
    kernelGenFactor L γ δ F (markedLayeredGardenGraft sig top P low p hsig hbound) fix off
        (fun k => wtop (fun a => k (topNodeEmbedding top P (fun B => (low B).garden) a))) (fun _ => t) k₀ κ =
      topGenFactor L γ δ sig top fixT offT wtop
          (splitGenDecoration sig top P (fun B => (low B).garden) hsig n nfl κ).1.1 k₀ p t *
        ∏ B, kernelDecorationFactor L γ δ F (low B) (fun _ => p) s k₀
          ((splitGenDecoration sig top P (fun B => (low B).garden) hsig n nfl κ).2 B) := by
  have hfix' : (fun b => fix (gardenBranchEquiv top P (fun B => (low B).garden) (.inl b))) = fixT := funext hfixT
  have hfixv' : ∀ b v, fix (gardenBranchEquiv top P (fun B => (low B).garden) (.inl b)) = some v → (p : ℝ) ≤ v :=
    fun b v h => hfixv b v ((hfixT b).symm.trans h)
  have hI := genIntegral_graft L γ δ hbranch hn hf fix hfixL hfixv' off offT hoffT hoffL t s hpt
    (cosetDecoration (markedLayeredGardenGraft sig top P low p hsig hbound).garden L k₀ κ.1)
  rw [hfix'] at hI
  have he : (epsDec (markedLayeredGardenGraft sig top P low p hsig hbound).garden κ.1 : ℂ) =
      ((∏ b : GBranch top, epsCoef (κ.1 (topNodeEmbedding top P (fun B => (low B).garden) (b.child 0)))
        (κ.1 (topNodeEmbedding top P (fun B => (low B).garden) (b.child 1))) (κ.1 (topNodeEmbedding top P (fun B => (low B).garden) (b.child 2))) : ℝ) : ℂ) *
        ∏ B, (epsDec (low B).garden (fun a => κ.1 (lowerNodeEmbedding top P (fun B => (low B).garden) B a)) : ℂ) := by
    have hh := congrArg (fun r : ℝ => (r : ℂ)) (markedGardenGraft_epsDec sig top P (fun B => (low B).garden) hsig κ.1)
    have hlow : ((∏ B : P.parts, epsDec (low B).garden
        (fun a => κ.1 (lowerNodeEmbedding top P (fun B => (low B).garden) B a)) : ℝ) : ℂ) =
        ∏ B : P.parts, ((epsDec (low B).garden
          (fun a => κ.1 (lowerNodeEmbedding top P (fun B => (low B).garden) B a)) : ℝ) : ℂ) :=
      Complex.ofReal_prod _ _
    exact hh.trans ((Complex.ofReal_mul _ _).trans (congrArg _ hlow))
  have hi := markedLayeredGardenGraft_inputs sig top P low p hsig hbound F (cosetDecoration (markedLayeredGardenGraft sig top P low p hsig hbound).garden L k₀ κ.1)
  have hs1 : ((splitGenDecoration sig top P (fun B => (low B).garden) hsig n nfl κ).1.1 :
      GNode top → (Fin d → ℤ)) = fun a => κ.1 (topNodeEmbedding top P (fun B => (low B).garden) a) := rfl
  have hs2 : ∀ B, (((splitGenDecoration sig top P (fun B => (low B).garden) hsig n nfl κ).2 B).1 :
      GNode (low B).garden.tree → (Fin d → ℤ)) =
        fun a => κ.1 (lowerNodeEmbedding top P (fun B => (low B).garden) B a) := fun B => rfl
  unfold kernelGenFactor topGenFactor kernelDecorationFactor
  rw [he, hI, hi]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [hs1, hs2]
  unfold cosetDecoration
  ring

/-- **`kernelKgen_graft`**: the general kernel of a graft, with designated nodes, removed phases and weight on the
top forest. -/
theorem kernelKgen_graft (F : ℕ → Mom d → ℝ)
    (hbranch : ∀ B (b : GBranch (low B).garden.tree), (low B).layer b.toNode < p)
    (hn : ∀ B ℓ, (low B).garden.mark ℓ ≠ some MarkTag.lower)
    (hf : ∀ B b, ¬ (low B).garden.IsFlowerParent b)
    (fix : GBranch (markedLayeredGardenGraft sig top P low p hsig hbound).garden.tree → Option ℝ)
    (fixT : GBranch top → Option ℝ)
    (hfixT : ∀ b, fix (gardenBranchEquiv top P (fun B => (low B).garden) (.inl b)) = fixT b)
    (hfixL : ∀ z, fix (gardenBranchEquiv top P (fun B => (low B).garden) (.inr z)) = none)
    (hfixv : ∀ b v, fixT b = some v → (p : ℝ) ≤ v)
    (off : Finset (GBranch (markedLayeredGardenGraft sig top P low p hsig hbound).garden.tree))
    (offT : Finset (GBranch top))
    (hoffT : ∀ b, gardenBranchEquiv top P (fun B => (low B).garden) (.inl b) ∈ off ↔ b ∈ offT)
    (hoffL : ∀ z, gardenBranchEquiv top P (fun B => (low B).garden) (.inr z) ∉ off)
    (wtop : (GNode top → Mom d) → ℝ) (hwtop : ∀ k, |wtop k| ≤ 1)
    (t s : ℝ) (hpt : (p : ℝ) ≤ t) (k₀ : Mom d) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hF : ∀ q, Summable fun m : Fin d → ℤ => |F q (k₀ + latticePoint L m)|) :
    kernelKgen L γ δ F (markedLayeredGardenGraft sig top P low p hsig hbound) fix off
        (fun k => wtop (fun a => k (topNodeEmbedding top P (fun B => (low B).garden) a))) (fun _ => t) k₀ n nfl =
      ((coupling d L γ δ : ℂ) ^ (∑ j, (top j).order) *
        ∏ b : GBranch top, Complex.I * (((nodeSign sig b.toNode.1 : ℤˣ) : ℤ) : ℂ)) *
      ∑' kt : ForestDecoration top d n,
        topGenFactor L γ δ sig top fixT offT wtop kt.1 k₀ p t *
          ∏ B : P.parts, kernelK L γ δ F (low B) (fun _ => p) s k₀
            (fun k => kt.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode) nfl := by
  set wt := fun k : GNode (markedLayeredGardenGraft sig top P low p hsig hbound).garden.tree → Mom d => wtop (fun a => k (topNodeEmbedding top P (fun B => (low B).garden) a))
  set E := fun kt : ForestDecoration top d n => topGenFactor L γ δ sig top fixT offT wtop kt.1 k₀ p t
  set g := fun (kt : ForestDecoration top d n) (B : P.parts)
    (kl : GenDecoration (low B).garden d (fun k => kt.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode) nfl) =>
      kernelDecorationFactor L γ δ F (low B) (fun _ => p) s k₀ kl
  have hfac : ∀ x : BoundaryDecorationData top P (fun B => (low B).garden) d n nfl,
      kernelGenFactor L γ δ F (markedLayeredGardenGraft sig top P low p hsig hbound) fix off wt (fun _ => t) k₀ (assembleGenDecoration sig top P (fun B => (low B).garden) hsig n nfl x) =
        E x.1 * ∏ B, g x.1 B (x.2 B) := by
    intro x
    rw [kernelGenFactor_graft L γ δ F hbranch hn hf fix fixT hfixT hfixL hfixv off offT hoffT hoffL wtop t s hpt
      k₀ n nfl, split_assembleGenDecoration]
  have hsum := summable_kernelGenFactor L γ δ F (markedLayeredGardenGraft sig top P low p hsig hbound) fix off wt (fun k => hwtop _) (fun _ => t) k₀ n nfl
    (markedLayeredGardenGraft_no_lone sig top P low p hsig hbound hn) hF
  have hs : Summable (fun x : BoundaryDecorationData top P (fun B => (low B).garden) d n nfl => E x.1 * ∏ B, g x.1 B (x.2 B)) :=
    ((summable_assembleGenDecoration_iff sig top P (fun B => (low B).garden) hsig n nfl _).mpr hsum).congr hfac
  have h0 : (∑' κ : GenDecoration (markedLayeredGardenGraft sig top P low p hsig hbound).garden d n nfl,
      kernelGenFactor L γ δ F (markedLayeredGardenGraft sig top P low p hsig hbound) fix off wt (fun _ => t) k₀ κ) =
      ∑' x, kernelGenFactor L γ δ F (markedLayeredGardenGraft sig top P low p hsig hbound) fix off wt (fun _ => t) k₀
        ((graftGenDecorationEquiv sig top P (fun B => (low B).garden) hsig n nfl).symm x) :=
    ((graftGenDecorationEquiv sig top P (fun B => (low B).garden) hsig n nfl).symm.tsum_eq _).symm
  rw [kernelKgen_eq_tsum, h0]
  have h1 : (∑' x, kernelGenFactor L γ δ F (markedLayeredGardenGraft sig top P low p hsig hbound) fix off wt (fun _ => t) k₀
      ((graftGenDecorationEquiv sig top P (fun B => (low B).garden) hsig n nfl).symm x)) =
      ∑' x : BoundaryDecorationData top P (fun B => (low B).garden) d n nfl, E x.1 * ∏ B, g x.1 B (x.2 B) := tsum_congr hfac
  have hpre : (coupling d L γ δ : ℂ) ^ (markedLayeredGardenGraft sig top P low p hsig hbound).garden.order *
      (markedLayeredGardenGraft sig top P low p hsig hbound).garden.zeta =
      ((coupling d L γ δ : ℂ) ^ (∑ j, (top j).order) *
        ∏ b : GBranch top, Complex.I * (((nodeSign sig b.toNode.1 : ℤˣ) : ℤ) : ℂ)) *
      ∏ B : P.parts, (coupling d L γ δ : ℂ) ^ (low B).garden.order * (low B).garden.zeta :=
    markedGardenGraft_prefactor (coupling d L γ δ : ℂ) sig top P (fun B => (low B).garden) hsig
  rw [h1, tsum_sigma_independent_prod E g hs, hpre, prefactor_mul_tsum_prod]
  congr 1

end Kernel

end WaveTurbulence.GraftGen
