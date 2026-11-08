/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Top.StarStatements
public import WaveTurbulence.Foundations.Flower.Stage1W.Inputs
public import WaveTurbulence.Foundations.Canon.Basic
public import WaveTurbulence.Foundations.Spine.DecoratedRootWeights
public import WaveTurbulence.Foundations.WaveB.Lemmas
public import WaveTurbulence.Foundations.Molecule.GardenNodeCounts

/-! # INC-TOP: per-arm top weights are star weights on an antichain

The per-arm top weight of a standalone regular object (STAGE1W's `rowTopWeightR p g LG qr`, one weight `g i` per
root/arm, real or complex) is the star weight (`starWeight`, C2-B-TOP) on the **top set**

  `topSet p LG qr = {a | layer a < p ∧ rowParentLayer LG qr a = p}`

with the star weight `y ↦ g a.1.1 (y 0)` (it reads only the node's own momentum).  Each `GPresented (32d) (g i) c`
gives `StarPresented (30d) (·) c` (`starPresented_of_gPresented`: the pushforward of the presentation along
`ξ ↦ (ξ, 0, 0, 0)`; total frequency `ξ`).  The top set is an antichain (layers are non-increasing downwards, and a
top node's parent has layer `p > layer`), so it has at most as many nodes as leaves: `≤ 2·order + w`
(`card_topSet_le`).  This is supplement Lemma 4.1's count `h` of inserted factors (`h ≤ #leaves`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Finset
open scoped ENNReal Classical
namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.LGSpine

/-- The top set of a standalone layered regular object (root `i` reads parent layer `qr i`). -/
def topSet {w : ℕ} (p : ℕ) (LG : LayeredGarden w) (qr : Fin w → ℕ) : Finset (GNode LG.garden.tree) :=
  Finset.univ.filter fun a => LG.layer a < p ∧ Stage1W.rowParentLayer LG qr a = p

/-- The star weight of the per-arm top weight: `g` of the node's arm at the node's own momentum. -/
def topStar {w d : ℕ} {T : Fin w → TTree} (g : Fin w → Mom d → ℂ) : GNode T → Star d → ℂ :=
  fun a y => g a.1.1 (y 0)

theorem starNode_zero {w : ℕ} {T : Fin w → TTree} (a : GNode T) : starNode a 0 = a := by
  unfold starNode
  split_ifs <;> rfl

theorem starMomenta_zero {w d : ℕ} {T : Fin w → TTree} (κ : GNode T → Mom d) (a : GNode T) :
    starMomenta κ a 0 = κ a := by
  unfold starMomenta
  simp [starNode_zero]

/-- **Top weight = star weight on the top set.** -/
theorem rowTopWeightR_eq_starWeight {w d : ℕ} (p : ℕ) (g : Fin w → Mom d → ℂ) (LG : LayeredGarden w)
    (qr : Fin w → ℕ) (k : GNode LG.garden.tree → Mom d) :
    Stage1W.rowTopWeightR p g LG qr k = starWeight (topSet p LG qr) (topStar g) k := by
  unfold Stage1W.rowTopWeightR starWeight topSet
  rw [Finset.prod_filter]
  refine Finset.prod_congr rfl fun a _ => ?_
  unfold Stage1W.topPsi topStar
  split_ifs <;> simp [starMomenta_zero]

/-- The pushforward of a `GPresented` presentation along `ξ ↦ (ξ, 0, 0, 0)`. -/
def starLift {d : ℕ} {α : Type} [MeasurableSpace α] (M : Cut2A.SpatialMeasure (Mom d) α) :
    Cut2A.SpatialMeasure (Star d) α where
  μ := M.μ
  sigmaFinite := M.sigmaFinite
  frequency := fun a => WithLp.toLp 2 (fun s : Fin 4 => if s = 0 then M.frequency a else 0)
  frequency_measurable :=
    (PiLp.continuous_toLp 2 _).measurable.comp
      (measurable_pi_iff.mpr fun s => by
        by_cases hs : s = 0
        · simpa only [hs, ite_true] using M.frequency_measurable
        · simpa only [hs, ite_false] using measurable_const)
  amplitude := M.amplitude
  amplitude_integrable := M.amplitude_integrable

theorem starLift_frequency_apply {d : ℕ} {α : Type} [MeasurableSpace α] (M : Cut2A.SpatialMeasure (Mom d) α)
    (a : α) (s : Fin 4) :
    (starLift M).frequency a s = if s = 0 then M.frequency a else 0 := rfl

theorem inner_starLift {d : ℕ} {α : Type} [MeasurableSpace α] (M : Cut2A.SpatialMeasure (Mom d) α) (a : α)
    (y : Star d) : inner ℝ ((starLift M).frequency a) y = inner ℝ (M.frequency a) (y 0) := by
  rw [PiLp.inner_apply, Fin.sum_univ_four]
  simp [starLift_frequency_apply]

theorem starRootFrequency_starLift {d : ℕ} {α : Type} [MeasurableSpace α]
    (M : Cut2A.SpatialMeasure (Mom d) α) (a : α) :
    starRootFrequency ((starLift M).frequency a) = M.frequency a := by
  unfold starRootFrequency
  rw [Fin.sum_univ_four]
  simp [starLift_frequency_apply]

/-- **`GPresented (J')` gives `StarPresented (J)` for `J ≤ J'`**, at the same constant, for the star weight reading
the node's own momentum. -/
theorem starPresented_of_gPresented {d J J' : ℕ} (hJ : J ≤ J') {g : Mom d → ℂ} {c : ℝ}
    (h : Stage1W.GPresented J' g c) : StarPresented J (fun y : Star d => g (y 0)) c := by
  obtain ⟨α, hα, M, hM, hv⟩ := h
  refine ⟨α, hα, starLift M, ?_, fun y => ?_⟩
  · refine le_trans ?_ hM
    unfold starMoment Stage1W.momentMassMom
    refine lintegral_mono fun a => ?_
    rw [starRootFrequency_starLift]
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    exact pow_le_pow_right₀ (by linarith [norm_nonneg (M.frequency a)]) hJ
  · change (starLift M).value y = g (y 0)
    rw [← hv]
    unfold Cut2A.SpatialMeasure.value
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    change M.amplitude a * _ = M.amplitude a * _
    rw [inner_starLift]

/-- Every per-arm weight presentation gives the star presentation of `topStar`. -/
theorem topStar_presented {w d : ℕ} {T : Fin w → TTree} (g : Fin w → Mom d → ℂ) {c : ℝ}
    (hg : ∀ i, Stage1W.GPresented (32 * d) (g i) c) (a : GNode T) :
    StarPresented (30 * d) (topStar g a) c :=
  starPresented_of_gPresented (by omega) (hg a.1.1)

/-- The top set is an antichain. -/
theorem eq_of_mem_topSet_of_isDesc {w : ℕ} {p : ℕ} {LG : LayeredGarden w} {qr : Fin w → ℕ}
    {a b : GNode LG.garden.tree} (ha : a ∈ topSet p LG qr) (hb : b ∈ topSet p LG qr) (h : a.IsDesc b) :
    a = b := by
  by_contra hne
  have hpath := Canon.path_ne_nil_of_isDesc_of_ne h hne
  have hle := LG.layer_le_of_isDesc (Canon.isDesc_par_of_isDesc_of_ne h hne)
  have ha1 := (Finset.mem_filter.1 ha).2.1
  have hb2 := (Finset.mem_filter.1 hb).2.2
  have hpar : Stage1W.rowParentLayer LG qr b = LG.layer (Canon.par b) := by
    simp only [Stage1W.rowParentLayer, hpath, ↓reduceIte, LayeredGarden.parentLayer]
    rfl
  omega

/-- **Antichain count**: the top set has at most as many nodes as leaves. -/
theorem card_topSet_le_leaves {w : ℕ} (p : ℕ) (LG : LayeredGarden w) (qr : Fin w → ℕ) :
    (topSet p LG qr).card ≤ Fintype.card (GLeaf LG.garden.tree) := by
  let f : GNode LG.garden.tree → GLeaf LG.garden.tree := fun a => (leavesBelow_nonempty a).choose
  have hf (a : GNode LG.garden.tree) : a.IsDesc (f a).toNode :=
    (Finset.mem_filter.1 (leavesBelow_nonempty a).choose_spec).2
  have hinj : Set.InjOn f (topSet p LG qr : Set (GNode LG.garden.tree)) := by
    intro a ha b hb hab
    have hb' : b.IsDesc (f a).toNode := hab ▸ hf b
    rcases Canon.isDesc_total (hf a) hb' with h | h
    · exact eq_of_mem_topSet_of_isDesc ha hb h
    · exact (eq_of_mem_topSet_of_isDesc hb ha h).symm
  rw [← Finset.card_image_of_injOn hinj]
  exact Finset.card_le_univ _

/-- The top set has at most `2·order + w` nodes. -/
theorem card_topSet_le {w : ℕ} (p : ℕ) (LG : LayeredGarden w) (qr : Fin w → ℕ) :
    (topSet p LG qr).card ≤ 2 * LG.garden.order + w := by
  have h := card_topSet_le_leaves p LG qr
  rw [Mole.card_gleaf] at h
  exact h

/-- The cost of the top weights: `∏_{a ∈ topSet} cψ ≤ cψ ^ (2·order + w)` for `cψ ≥ 1`. -/
theorem prod_topSet_cost_le {w : ℕ} (p : ℕ) (LG : LayeredGarden w) (qr : Fin w → ℕ) {c : ℝ} (hc : 1 ≤ c)
    {N : ℕ} (hN : 2 * LG.garden.order + w ≤ N) :
    (∏ _a ∈ topSet p LG qr, ENNReal.ofReal c) ≤ ENNReal.ofReal (c ^ N) := by
  rw [Finset.prod_const, ENNReal.ofReal_pow (zero_le_one.trans hc)]
  exact pow_le_pow_right₀ (ENNReal.one_le_ofReal.mpr hc) ((card_topSet_le p LG qr).trans hN)

end WaveTurbulence.Flower.IncTop
