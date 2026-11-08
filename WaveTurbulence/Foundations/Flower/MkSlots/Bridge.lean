/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Hyp
public import WaveTurbulence.Foundations.FlowerTop.Port.FlowerP1Stub
public import WaveTurbulence.Foundations.FlowerTop.Port.S2ST.AnchorFamilyB

/-! # B3s MK-SLOTS: the frozen class integrand as a pinned weighted leaf kernel

The class value of B4's hypothesis sums the frozen `kernelKgenSel` with intrinsic pins `fixCap`, removed phases
`offCap` and the weight `markedWt = selOK · markedWeight`. Here it is rewritten as a PINNED weighted leaf kernel:
main's `FlowerP1.kernelLeavesFixTerm` (time domain `kDomainFix`, leaf profiles) with the anchored pair-type profiles
`S2ST.typeProfilesAnchB J LG h` (profile `1` on pairs meeting a cap tree), times a decoration weight (the rest of the
marked weight and the removed-phase factor `offFactor`, a unimodular decoration function, because every removed phase
is at a pinned branch).

* `kernelLeavesFixSelW`: the pinned weighted leaf kernel (the pinned analogue of `Stage1W.kernelLeavesSelW`).
* `leafProdCap_eq`: `leafProdCap = ∏_{input leaves} typeProfilesAnchB`.
* `phaseProdOff_extendFix` (copied by source from D6b's `ProtWhole/CapRed.lean`, see `COPIED-SHA256SUMS`).
* **`kernelKgenSel_eq_fixW`**: the bridge for any weight `rest · leafProdCap`.
* `markedWt_eq`, `offCap_pinned`: the instance at B4's `markedWt` and `offCap`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.Stage1MKGate

namespace WaveTurbulence.Flower.MkSlots

variable {w d : ℕ}

/-- **The pinned weighted leaf kernel**: main's `kernelLeavesFixSel` with a decoration weight. -/
def kernelLeavesFixSelW (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (fix : GBranch LG.garden.tree → Option ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) (sel : GenDecoration LG.garden d nroot nfl → Prop)
    (wt : GenDecoration LG.garden d nroot nfl → ℂ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
    ∑' κ : GenDecoration LG.garden d nroot nfl,
      if sel κ then wt κ * FlowerP1.kernelLeavesFixTerm L γ δ LG H up fix k₀ κ else 0

/-- The anchored leaf-profile product is `leafProdCap`. -/
theorem leafProdCap_eq (LG : LayeredGarden w) (J : Finset (Fin w)) (h : ℕ → Fin w → Fin w → Mom d → ℝ)
    (k : GNode LG.garden.tree → Mom d) :
    leafProdCap LG J h k = ∏ ℓ ∈ inputLeaves LG.garden, S2ST.typeProfilesAnchB J LG h ℓ.1 (k ℓ.toNode) := by
  unfold leafProdCap
  refine Finset.prod_congr rfl fun ℓ _ => ?_
  rw [S2ST.typeProfilesAnchB_leaf]
  split_ifs <;> simp [typeProfiles_leaf]

theorem extendFix_some' (G : Garden w) (fix : GBranch G.tree → Option ℝ)
    (τ : {b : GBranch G.tree // fix b = none} → ℝ) {b : GBranch G.tree} {v : ℝ} (h : fix b = some v) :
    G.extendFix fix τ b = v := by
  unfold Garden.extendFix
  split
  · next v' h' => rw [h] at h'; exact (Option.some.inj h').symm
  · next h' => rw [h] at h'; exact absurd h' (by simp)

-- [copied] D6b `ProtWhole/CapRed.lean` (see COPIED-SHA256SUMS): `offFactor`, `norm_offFactor`, `prod_off_aux`,
-- `phaseProdOff_extendFix` (with the local `extendFix_some'`).
/-- The removed-phase factor: the inverse phases of the `off` branches at their pinned times. -/
def offFactor (L γ δ : ℝ) (G : Garden w) (off : Finset (GBranch G.tree)) (fix : GBranch G.tree → Option ℝ)
    (K : GNode G.tree → Mom d) : ℂ :=
  ∏ b ∈ off, Complex.exp (-(((Real.pi * ((G.sign b.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) * omegaNode G K b *
    (fix b).getD 0 : ℝ) : ℂ) * Complex.I))

theorem norm_offFactor (L γ δ : ℝ) (G : Garden w) (off : Finset (GBranch G.tree)) (fix : GBranch G.tree → Option ℝ)
    (K : GNode G.tree → Mom d) : ‖offFactor L γ δ G off fix K‖ = 1 := by
  unfold offFactor
  rw [norm_prod]
  refine Finset.prod_eq_one fun b _ => ?_
  rw [← neg_mul, ← Complex.ofReal_neg]
  exact Complex.norm_exp_ofReal_mul_I _

theorem prod_off_aux {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Finset ι) (E N : ι → ℂ)
    (h : ∀ i ∈ s, E i * N i = 1) : ∏ i, (if i ∈ s then 1 else E i) = (∏ i, E i) * ∏ i ∈ s, N i := by
  have hpt : ∀ i, (if i ∈ s then (1 : ℂ) else E i) = E i * (if i ∈ s then N i else 1) := fun i => by
    split_ifs with hi
    · exact (h i hi).symm
    · ring
  rw [Finset.prod_congr rfl (fun i _ => hpt i), Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter]

/-- **Removed phases at pinned branches** are a decoration factor. -/
theorem phaseProdOff_extendFix (L γ δ : ℝ) (G : Garden w) (off : Finset (GBranch G.tree))
    (fix : GBranch G.tree → Option ℝ) (hoff : ∀ b ∈ off, (fix b).isSome) (K : GNode G.tree → Mom d)
    (τ : {b : GBranch G.tree // fix b = none} → ℝ) :
    phaseProdOff L γ δ G off K (G.extendFix fix τ) =
      phaseProd L γ δ G K (G.extendFix fix τ) * offFactor L γ δ G off fix K := by
  unfold phaseProdOff phaseProd offFactor
  refine prod_off_aux off _ _ fun b hb => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hoff b hb)
  rw [extendFix_some' G fix τ hv, hv, Option.getD_some, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
-- [end copied]

/-- **The bridge.** With every removed phase at a pinned branch, the frozen `kernelKgenSel` with weight
`rest · leafProdCap` is the pinned weighted leaf kernel with the anchored profiles and the weight
`rest · offFactor`. -/
theorem kernelKgenSel_eq_fixW (L γ δ : ℝ) (LG : LayeredGarden w) (J : Finset (Fin w))
    (fix : GBranch LG.garden.tree → Option ℝ) (off : Finset (GBranch LG.garden.tree))
    (hoff : ∀ b ∈ off, (fix b).isSome) (h : ℕ → Fin w → Fin w → Mom d → ℝ)
    (rest : (GNode LG.garden.tree → Mom d) → ℝ) (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (sel : GenDecoration LG.garden d nroot 0 → Prop) :
    kernelKgenSel L γ δ LG fix off (fun k => rest k * leafProdCap LG J h k) up k₀ nroot sel =
      kernelLeavesFixSelW L γ δ LG (S2ST.typeProfilesAnchB J LG h) up fix k₀ nroot 0 sel
        (fun κ => (rest (cosetDecoration LG.garden L k₀ κ.1) : ℂ) *
          offFactor L γ δ LG.garden off fix (cosetDecoration LG.garden L k₀ κ.1)) := by
  unfold kernelKgenSel kernelLeavesFixSelW
  congr 1
  refine tsum_congr fun κ => ?_
  split_ifs with hs
  · unfold FlowerP1.kernelLeavesFixTerm
    have hint : ∀ K : GNode LG.garden.tree → Mom d,
        (∫ τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ,
          (kDomainFix LG up fix).indicator (phaseProdOff L γ δ LG.garden off K) (LG.garden.extendFix fix τ)) =
        (∫ τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ,
          (kDomainFix LG up fix).indicator (phaseProd L γ δ LG.garden K) (LG.garden.extendFix fix τ)) *
          offFactor L γ δ LG.garden off fix K := by
      intro K
      rw [← integral_mul_const]
      refine integral_congr_ae (ae_of_all _ fun τ => ?_)
      simp only [Set.indicator]
      split_ifs
      · exact phaseProdOff_extendFix L γ δ LG.garden off fix hoff K τ
      · simp
    rw [hint]
    beta_reduce
    rw [leafProdCap_eq LG J h]
    push_cast
    ring
  · rfl

/-- B4's marked weight is `rest · leafProdCap` (all other factors in `rest`). -/
theorem markedWt_eq (P : WTParams) {R : ℕ} (J : Finset (Fin (2 * R))) (p : ℕ) (kSel : Fin (2 * R) → Option ℕ)
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (Rf : Fin (2 * R) → Option ℝ) (σ : Fin (2 * R) → Option ℕ)
    (Rs : Fin (2 * R) → ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (LG : LayeredGarden (2 * R)) :
    markedWt P J p kSel h Rf σ Rs dag LG = fun k =>
      (selOK LG J kSel * (Typed.frontierW LG p Rf k * stemFilterCap LG J P.L σ k *
        selWeightCap LG J (selCap LG J kSel) Rs k * dag.elim 1 (fun c => sibWeightCap LG J c k))) *
        leafProdCap LG J h k := by
  funext k
  unfold markedWt markedWeight
  ring

/-- The dagger's removed phases are at the capped flower parents, which `fixCap` pins (for every pattern). -/
theorem offCap_pinned (LG : LayeredGarden w) (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (dag : Bool) :
    ∀ b ∈ offCap LG J dag, (fixCap LG J pat t s b).isSome := by
  intro b hb
  unfold offCap at hb
  split_ifs at hb
  · have hc : IsCapFlowerParent LG J b := (Finset.mem_filter.1 hb).2
    simp [fixCap, hc]
  · simp at hb

end WaveTurbulence.Flower.MkSlots
