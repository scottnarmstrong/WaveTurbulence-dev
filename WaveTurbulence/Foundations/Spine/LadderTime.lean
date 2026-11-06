/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceLocalLadder
public import WaveTurbulence.Foundations.Spine.TimeDrop
/-! # Time-ordering drop for the local ladder kernel (S3b LADDER-DECAY) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open WaveTurbulence WaveTurbulence.LGSpine MeasureTheory Set Finset

variable {w d : ℕ} (G : Garden w)

/-- The product of unit time boxes. -/
def timeBox (layer : GBranch G.tree → ℕ) (S : Finset (GBranch G.tree)) : Set (S → ℝ) :=
  Set.pi univ (fun v : S => Icc (layer v.1 : ℝ) (layer v.1 + 1))

lemma clocks_subset_box (layer : GBranch G.tree → ℕ) (S : Finset (GBranch G.tree))
    (outside : GBranch G.tree → ℝ) :
    localLadderClocks G layer S outside ⊆ timeBox G layer S := fun _ ht v _ => ht.1 v

lemma isCompact_timeBox (layer : GBranch G.tree → ℕ) (S : Finset (GBranch G.tree)) :
    IsCompact (timeBox G layer S) :=
  isCompact_univ_pi (fun _ => isCompact_Icc)

lemma clocks_measurable (layer : GBranch G.tree → ℕ) (S : Finset (GBranch G.tree))
    (outside : GBranch G.tree → ℝ) : MeasurableSet (localLadderClocks G layer S outside) := by
  have hdef : localLadderClocks G layer S outside =
      {t : S → ℝ | ∀ v : S, t v ∈ Icc (layer v.1 : ℝ) (layer v.1 + 1)} ∩
      {t : S → ℝ | ∀ v u : GBranch G.tree, v.IsChildOf u → v ∈ S ∨ u ∈ S →
        (if hv : v ∈ S then t ⟨v, hv⟩ else outside v) < (if hu : u ∈ S then t ⟨u, hu⟩ else outside u)} := rfl
  rw [hdef]
  refine MeasurableSet.inter ?_ ?_
  · have : {t : S → ℝ | ∀ v : S, t v ∈ Icc (layer v.1 : ℝ) (layer v.1 + 1)} =
        ⋂ v : S, (fun t : S → ℝ => t v) ⁻¹' Icc (layer v.1 : ℝ) (layer v.1 + 1) := by
      ext t; simp
    rw [this]
    exact MeasurableSet.iInter (fun v => measurable_pi_apply v measurableSet_Icc)
  · have : {t : S → ℝ | ∀ v u : GBranch G.tree, v.IsChildOf u → v ∈ S ∨ u ∈ S →
        (if hv : v ∈ S then t ⟨v, hv⟩ else outside v) < (if hu : u ∈ S then t ⟨u, hu⟩ else outside u)} =
        ⋂ v : GBranch G.tree, ⋂ u : GBranch G.tree, ⋂ (_ : v.IsChildOf u ∧ (v ∈ S ∨ u ∈ S)),
          {t : S → ℝ | (if hv : v ∈ S then t ⟨v, hv⟩ else outside v) <
            (if hu : u ∈ S then t ⟨u, hu⟩ else outside u)} := by
      ext t; simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro h v u hvu; exact h v u hvu.1 hvu.2
      · intro h v u hvu hS; exact h v u ⟨hvu, hS⟩
    rw [this]
    refine MeasurableSet.iInter (fun v => MeasurableSet.iInter (fun u => MeasurableSet.iInter (fun _ => ?_)))
    have hm : ∀ x : GBranch G.tree, Measurable (fun t : S → ℝ =>
        (if hx : x ∈ S then t ⟨x, hx⟩ else outside x)) := by
      intro x
      by_cases hx : x ∈ S
      · simp only [hx, dite_true]; exact measurable_pi_apply _
      · simp only [hx, dite_false]; exact measurable_const
    exact measurableSet_lt (hm v) (hm u)


variable {G}

/-- The weight of a decoration in the local ladder kernel (epsilon, gap indicator, amplitudes). -/
noncomputable def ladderWeight (D : SplicedKernelData G d) (S : Finset (GBranch G.tree))
    (L γ η : ℝ) (base : Mom d) (z : GNode G.tree → (Fin d → ℤ)) : ℂ :=
  ((∏ v ∈ S, epsCoef (z (v.child 0)) (z (v.child 1)) (z (v.child 2))) : ℂ) *
    (localLadderGapIndicator G D S L γ η base z : ℂ) *
    (∏ x ∈ G.molecule.bonds.filter (G.molecule.InGroup S),
      D.edgeAmplitude x (base + latticePoint L (bondIndex G z x)))

/-- The time phase of a decoration. -/
noncomputable def ladderPhase (D : SplicedKernelData G d) (S : Finset (GBranch G.tree))
    (L γ δ : ℝ) (base : Mom d) (z : GNode G.tree → (Fin d → ℤ)) (t : S → ℝ) : ℂ :=
  ∏ v : S, Complex.exp ((Real.pi *
      (((((G.sign v.1.toNode : ℤˣ) : ℤ) : ℝ) * δ * L ^ (2 * γ) *
        omegaNode G (cosetDecoration G L base z) v.1 + D.frequency v.1) * t v) : ℝ) * Complex.I)

lemma kernel_eq (D : SplicedKernelData G d) (S : Finset (GBranch G.tree))
    (outside : GBranch G.tree → ℝ) (L γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (boundary : GardenDart G → (Fin d → ℤ)) :
    sourceLocalLadderKernel G D S outside L γ η δ base roots boundary =
      (coupling d L γ δ : ℂ) ^ (S.card - 1) *
        ∑' z : localLadderDecorations G S roots boundary,
          ladderWeight D S L γ η base z.1.1 *
            ∫ t : S → ℝ, (localLadderClocks G D.layer S outside).indicator
              (ladderPhase D S L γ δ base z.1.1) t := rfl

lemma continuous_ladderPhase (D : SplicedKernelData G d) (S : Finset (GBranch G.tree))
    (L γ δ : ℝ) (base : Mom d) (z : GNode G.tree → (Fin d → ℤ)) :
    Continuous (ladderPhase D S L γ δ base z) := by
  unfold ladderPhase
  refine continuous_finsetProd _ (fun v _ => ?_)
  fun_prop

lemma norm_ladderPhase (D : SplicedKernelData G d) (S : Finset (GBranch G.tree))
    (L γ δ : ℝ) (base : Mom d) (z : GNode G.tree → (Fin d → ℤ)) (t : S → ℝ) :
    ‖ladderPhase D S L γ δ base z t‖ = 1 := by
  unfold ladderPhase
  rw [norm_prod]
  refine Finset.prod_eq_one (fun v _ => ?_)
  exact Complex.norm_exp_ofReal_mul_I _

lemma integrable_clocks_phase (D : SplicedKernelData G d) (S : Finset (GBranch G.tree))
    (outside : GBranch G.tree → ℝ) (L γ δ : ℝ) (base : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) :
    Integrable ((localLadderClocks G D.layer S outside).indicator
      (ladderPhase D S L γ δ base z)) := by
  have h1 : IntegrableOn (ladderPhase D S L γ δ base z) (timeBox G D.layer S) :=
    (continuous_ladderPhase D S L γ δ base z).continuousOn.integrableOn_compact
      (isCompact_timeBox G D.layer S)
  have h2 : IntegrableOn (ladderPhase D S L γ δ base z) (localLadderClocks G D.layer S outside) :=
    h1.mono_set (clocks_subset_box G D.layer S outside)
  exact (integrable_indicator_iff (clocks_measurable G D.layer S outside)).mpr h2


/-- **Dropping the time ordering.** The kernel is bounded by the coupling power times the integral,
over the product of unit boxes, of the modulus of the (finite) lattice sum at fixed times. -/
theorem kernel_norm_le (D : SplicedKernelData G d) (S : Finset (GBranch G.tree))
    (outside : GBranch G.tree → ℝ) (L γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (boundary : GardenDart G → (Fin d → ℤ))
    (T : Finset ↥(localLadderDecorations G S roots boundary))
    (hT : ∀ z, z ∉ T → ladderWeight D S L γ η base z.1.1 = 0) :
    ‖sourceLocalLadderKernel G D S outside L γ η δ base roots boundary‖ ≤
      ‖(coupling d L γ δ : ℂ)‖ ^ (S.card - 1) *
        ∫ t in timeBox G D.layer S,
          ‖∑ z ∈ T, ladderWeight D S L γ η base z.1.1 * ladderPhase D S L γ δ base z.1.1 t‖ := by
  rw [kernel_eq, tsum_eq_sum (s := T) (fun z hz => by rw [hT z hz, zero_mul]), norm_mul, norm_pow]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine norm_sum_integral_indicator_le volume T _ (fun z t => ladderPhase D S L γ δ base z.1.1 t)
    _ _ (clocks_measurable G D.layer S outside) (clocks_subset_box G D.layer S outside)
    (fun z _ => integrable_clocks_phase D S outside L γ δ base z.1.1) ?_
  have hc : Continuous (fun t : S → ℝ =>
      ∑ z ∈ T, ladderWeight D S L γ η base z.1.1 * ladderPhase D S L γ δ base z.1.1 t) :=
    continuous_finsetSum _ (fun z _ => continuous_const.mul (continuous_ladderPhase D S L γ δ base z.1.1))
  exact hc.norm.continuousOn.integrableOn_compact (isCompact_timeBox G D.layer S)

end WaveTurbulence.LadderDecay
