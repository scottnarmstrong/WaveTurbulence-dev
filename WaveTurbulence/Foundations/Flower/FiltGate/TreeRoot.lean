/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltGate.TreeExt
public import WaveTurbulence.Foundations.Flower.FiltGate.Statements
public import WaveTurbulence.Foundations.Flower.FiltGate.Quarter
public import WaveTurbulence.Foundations.Flower.FiltProd.TreeDecay
public import WaveTurbulence.Foundations.Incoh.ConstantAbsorption

/-! # D5b-3 FILT-GATE: filtered root-modulated raw trees at both gate weights

- `exists_parameterTreeCausalExtension_gate_decayFilt`: the family bound for `(θ, c) ∈ {(η, 0), (1/4, 4d)}`: D5b-2's
  `exists_parameterTreeCausalExtensionFilt_decay` at `θ = η` and its `X^{1/4}` bound
  `exists_parameterTreeCausalExtensionFilt_quarter_bound` (o82 Lemma 16.1 for trees: T1091, loss `L^{2d}`) at `θ = 1/4`,
  whose cutoff constant (chosen after `χ`) is absorbed into `L^{ηg}`.
- Twins of INC-TOP `Top/TreeRootRate` (copied by source, sha256 in COPIED-SHA256SUMS):
  `exists_rootRawTreeKernel_restriction_boundFilt`, `exists_rootRawTreeKernel_rateFilt`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.FiltGate
open WaveTurbulence.Incoh WaveTurbulence.Flower.IncTop WaveTurbulence.Flower.FiltSrc
  WaveTurbulence.Flower.FiltProd WaveTurbulence.Flower.FiltLink

/-- The rate algebra of the tree `θ = 1/4` bound: `C · X L^{-(γ₁-2η)g} L^{2d}` with `C ≤ L^{ηg}` is at most the
`X^η` rate times `L^{4d}`. -/
theorem tree_quarter_rate_le {d g : ℕ} (hd : 1 ≤ d) {L η γ₁ C X X' : ℝ} (hL : 1 ≤ L) (hη : 0 ≤ η)
    (hX : 0 ≤ X) (hXX : X ≤ X') (hC : 0 ≤ C) (hCL : C ≤ L ^ (η * g)) :
    ENNReal.ofReal C * ENNReal.ofReal (X * L ^ (-(γ₁ - 2 * η) * g) * L ^ ((d : ℝ) * 2)) ≤
      ENNReal.ofReal (X' * L ^ (-(γ₁ - 100 * (d : ℝ) * η) * g) * L ^ (4 * (d : ℝ))) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL
  rw [← ENNReal.ofReal_mul hC]
  apply ENNReal.ofReal_le_ofReal
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hgR : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  have h1 : C * L ^ (-(γ₁ - 2 * η) * g) ≤ L ^ (-(γ₁ - 100 * (d : ℝ) * η) * g) := by
    calc C * L ^ (-(γ₁ - 2 * η) * g) ≤ L ^ (η * g) * L ^ (-(γ₁ - 2 * η) * g) :=
          mul_le_mul_of_nonneg_right hCL (Real.rpow_nonneg hL0 _)
      _ = L ^ (η * g + -(γ₁ - 2 * η) * g) := (Real.rpow_add hLp _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL (by
          nlinarith [mul_nonneg hη hgR, mul_nonneg (mul_nonneg hη hgR) (sub_nonneg.mpr hdR)])
  have h2 : L ^ ((d : ℝ) * 2) ≤ L ^ (4 * (d : ℝ)) := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  calc C * (X * L ^ (-(γ₁ - 2 * η) * g) * L ^ ((d : ℝ) * 2))
      = X * (C * L ^ (-(γ₁ - 2 * η) * g)) * L ^ ((d : ℝ) * 2) := by ring
    _ ≤ X' * L ^ (-(γ₁ - 100 * (d : ℝ) * η) * g) * L ^ (4 * (d : ℝ)) :=
      mul_le_mul (mul_le_mul hXX h1 (mul_nonneg hC (Real.rpow_nonneg hL0 _)) (hX.trans hXX)) h2
        (Real.rpow_nonneg hL0 _) (mul_nonneg (hX.trans hXX) (Real.rpow_nonneg hL0 _))

/-- **The filtered tree family bound at both gate weights** (o82 Prop 15.1 at `θ = η`, Lemma 16.1 at `θ = 1/4`). -/
theorem exists_parameterTreeCausalExtension_gate_decayFilt (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ m : ℕ, m ≤ 2 →
      ∀ η : ℝ, 0 < η → η ≤ 1 / 100 →
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ θ c : ℝ, GateWeight d η θ c → ∀ n g : ℕ, 1 ≤ g → ∀ V : Type,
        ∀ Q : V → Fin n → LayerLink d,
        (∀ k i, |((Q k i).leftLayer : ℝ) - (Q k i).rightLayer| + 1 ≤ D) →
        (∀ k, incoherenceCount (Q k) = g) →
        ∀ (K : ℝ), 0 ≤ K → ∀ φ : V → Fin n → ℝ → ℂ, (∀ v i, PresentedMult L K (φ v i)) →
        ∀ T : (∀ k, TreeClockFibers m (Q k)), ∀ R : RootCoordinates n,
        ∀ J : Finset (Fin n), J.card ≤ 2 →
        (∀ k, R.rootVertex 0 = (T k).selection.coordinates.rootVertex 0) →
        (∀ k, R.rootVertex 1 = (T k).selection.coordinates.rootVertex (Fin.last (m + 1))) →
        (∀ k, (T k).selection.coordinates.rootLinks = J) →
        (∀ k v, v ∈ R.rootBox (Q k) → ∀ j, χ (v j) = 1) →
        (∀ k v, v ∈ (T k).selection.coordinates.rootBox (Q k) → ∀ j, χ (v j) = 1) →
        Fourier.mixedFourierNorm00 θ
          (RootCoordinates.parameterTreeCausalExtensionFilt R χ L γ δ Q φ (fun k => (T k).timeDomain)) ≤
          ENNReal.ofReal ((K * C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * g) * L ^ c) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_parameterTreeCausalExtensionFilt_decay d hd
  obtain ⟨C₂, hC₂, h₂⟩ := exists_parameterTreeCausalExtensionFilt_quarter_bound d hd
  refine ⟨max C₁ C₂, hC₁.trans_le (le_max_left _ _), ?_⟩
  intro m hm η hη hη₁ χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₁, hL₁, h₁⟩ := h₁ m hm η hη hη₁ χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨C, hC, h₂⟩ := h₂ m hm χ hχ hcχ
  obtain ⟨L₂, hL₂, h₂⟩ := h₂ γ hγ η hη hηγ δ hδ hδ₁ D hD
  obtain ⟨Lₐ, hLₐ, ha⟩ := exists_constant_absorption_threshold C hη
  refine ⟨max Lₐ (max L₁ L₂), hLₐ.trans (le_max_left _ _), ?_⟩
  intro L hL θ c hθc n g hg V Q hspan hcount K hK φ hφ T R J hJ hfirst hlast hJe hχroot hχsel
  have hLa : Lₐ ≤ L := (le_max_left _ _).trans hL
  have hL₁L : L₁ ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hL₂L : L₂ ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hLone : 1 ≤ L := hLₐ.trans hLa
  have hL0 : 0 ≤ L := zero_le_one.trans hLone
  rcases hθc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine (h₁ L hL₁L n g hg V Q hspan hcount K hK φ hφ T R J hJ hfirst hlast hJe hχroot hχsel).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rw [Real.rpow_zero, mul_one]
    exact mul_le_mul_of_nonneg_right (kpow_mono hK hC₁.le (le_max_left _ _) hδ.le n) (Real.rpow_nonneg hL0 _)
  · have hgR : (1 : ℝ) ≤ g := by exact_mod_cast hg
    have hCL : C ≤ L ^ (η * g) := (ha L hLa).trans
      (Real.rpow_le_rpow_of_exponent_le hLone (by nlinarith only [hgR, hη.le]))
    exact (h₂ L hL₂L n g V Q hspan hcount K hK φ hφ T R J hJ hfirst hlast hJe hχroot hχsel).trans
      (tree_quarter_rate_le (by omega) hLone hη.le
        (pow_nonneg (mul_nonneg (mul_nonneg hK hC₂.le) hδ.le) n)
        (kpow_mono hK hC₂.le (le_max_right _ _) hδ.le n) hC.le hCL)

/-- Filtered root-modulated tree restriction estimate, at both gate weights. -/
theorem exists_rootRawTreeKernel_restriction_boundFilt (d : ℕ) (hd : 3 ≤ d) :
    ∃ Cₗ : ℝ, 0 < Cₗ ∧ ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ l : ℕ, l ≤ 2 →
      ∀ η : ℝ, 0 < η → η ≤ 1 / 100 →
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ θ c : ℝ, GateWeight d η θ c → ∀ n m w J K M : ℕ,
        ∀ P : MomentumTreeData n m w, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        1 ≤ incoherenceCount Q → ∀ R : RootCoordinates n, ∀ T : TreeClockFibers l Q,
        R.rootVertex 0 = T.selection.coordinates.rootVertex 0 →
        R.rootVertex 1 = T.selection.coordinates.rootVertex (Fin.last (l + 1)) →
        (∀ v ∈ R.rootBox Q, ∀ j, χ (v j) = 1) →
        (∀ v ∈ T.selection.coordinates.rootBox Q, ∀ j, χ (v j) = 1) →
        ∀ (Kφ : ℝ), 0 ≤ Kφ → ∀ φ : Fin n → ℝ → ℂ, (∀ i, PresentedMult L Kφ (φ i)) →
        ∀ f : Fin m → Mom d → ℂ, ∀ B : ℝ, d + 1 + J ≤ K → 2 * d ≤ M → 0 ≤ B →
        (∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) →
        ∀ E : Set (Fin 2 → ℝ), (∀ t ∈ E, t 1 ≤ t 0) →
        (∀ t ∈ E, ∀ j, χ (t j) = 1) → ∀ ζ : Circle, ∀ A : Set (Mom d),
        ∀ {α : Type} [MeasurableSpace α] (G : RootMeasure d n α), G.momentMass J < ⊤ →
        Fourier.mixedRestrictionNorm θ J 0 E A
          (fun t k => (MomentumTreeData.weightedSourceTreeKernelFilt (P := P)) (G.at k) ζ R L γ δ Q φ T.timeDomain
            f t k) ≤
          ENNReal.ofReal (rootJetConstant J) * (treeCellConstant d m J K M n Cₗ B * G.momentMass J) *
          ENNReal.ofReal ((Kφ * C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q) * L ^ c) := by
  obtain ⟨Cₗ, hCₗ, hloc⟩ := exists_uniform_couple_link_cell_localization d (by omega)
  obtain ⟨C₀, hC₀, hb⟩ := exists_parameterTreeCausalExtension_gate_decayFilt d hd
  obtain ⟨Cᵣ, _, hr⟩ := exists_rootDensityFilt_L1_bound d hd
  refine ⟨Cₗ, hCₗ, C₀, hC₀, ?_⟩
  intro l hl η hη hη₁ χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨hc⟩ := Fourier.exists_cutoffControl hχ hcχ
  obtain ⟨L₁, hL₁, hb⟩ := hb l hl η hη hη₁ χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₂, _, hr⟩ := hr γ hγ η hη hηγ δ hδ D hD
  refine ⟨max L₁ L₂, hL₁.trans (le_max_left _ _), ?_⟩
  intro L hL θ c hθc n m w J K M P Q hspan hg R T hfirst hlast hχroot hχsel Kφ hKφ φ hφ f B hK hM hB hf E
    hforward hχext ζ A α _ G hfin
  have hLa := (le_max_left L₁ L₂).trans hL
  have hLr := (le_max_right L₁ L₂).trans hL
  have hLone : 1 ≤ L := hL₁.trans hLa
  have hLp : 0 < L := zero_lt_one.trans_le hLone
  have hφB : ∀ i u, ‖φ i u‖ ≤ Kφ := fun i u => FiltProd.PresentedMult.norm_le (hφ i) hLp.le hKφ u
  choose S hScard hcover using (fun c => hloc n (m + 1) w P.withRootInput P.withRootInput_all_leaves c)
  let Nr := ENNReal.ofReal ((Kφ * Cᵣ * δ) ^ n *
    L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q))
  have hroot (z : (Fin n × Fin 2) → Fin d → ℤ) (ξ : LocalizedCellIndex n (m + 1) → Fin d → ℝ) (a : α) :
      eLpNorm (RootCoordinates.linkDensityFilt R L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P.withRootInput))
        (spatialFrequencyLinks Q (G.base.frequency a)) z ξ) φ T.timeDomain) 1 ≤ Nr := by
    have hQ' : incoherenceCount ((MomentumTreeData.spectralLinksSpatial (P := P.withRootInput))
        (spatialFrequencyLinks Q (G.base.frequency a)) z ξ) = incoherenceCount Q := by
      rw [(MomentumTreeData.incoherenceCount_spectralLinksSpatial (P := P.withRootInput)),
        incoherenceCount_spatialFrequencyLinks]
    have h := hr L hLr n ((MomentumTreeData.spectralLinksSpatial (P := P.withRootInput))
      (spatialFrequencyLinks Q (G.base.frequency a)) z ξ) hspan Kφ hKφ φ hφ T.timeDomain
      T.measurableSet_timeDomain T.timeDomain_subset_linkBoxes R
    rw [hQ'] at h
    exact h
  have hagree (t : E) (k : A) :
      (MomentumTreeData.fourierRootPartitionSourceTreeExtensionFilt (P := P)) (G.at k) ζ R χ L γ δ Q φ T.timeDomain
          f S t k =
        (MomentumTreeData.weightedSourceTreeKernelFilt (P := P)) (G.at k) ζ R L γ δ Q φ T.timeDomain f t k :=
    (MomentumTreeData.fourierRootPartitionSourceTreeExtension_agrees_on_cutoffFilt (P := P)) (G.at k) ζ R hχ hc
      L γ δ Q φ hφB T.timeDomain T.measurableSet_timeDomain T.timeDomain_subset_linkBoxes hχroot f S hcover hScard
      hLone (by omega) hM hf ENNReal.ofReal_lt_top hroot t (hχext t t.property) (hforward t t.property) k
  apply (Fourier.mixedRestrictionNorm_le_extension
    (fun t k => (MomentumTreeData.fourierRootPartitionSourceTreeExtensionFilt (P := P)) (G.at k) ζ R χ L γ δ Q φ
      T.timeDomain f S t k) hagree).trans
  have hext := rootTreeExtensionFilt_le_of_roots P hχ hc R hLp γ δ Q φ T.timeDomain T.measurableSet_timeDomain
    T.timeDomain_subset_linkBoxes f hK hM hB hf S hScard ζ G hfin θ (N := Nr) ENNReal.ofReal_lt_top hroot
  refine hext.trans (mul_le_mul' le_rfl ?_)
  let U := SourceCellIndex S × (LocalizedCellIndex n (m + 1) → Fin d → ℝ)
  let Q' := fun u : U × α =>
    (MomentumTreeData.spectralLinksSpatial (P := P.withRootInput)) (spatialFrequencyLinks Q (G.base.frequency u.2))
      u.1.1.2.val u.1.2
  let T' := fun u : U × α => (MomentumTreeData.spectralTreeClockFibersSpatial (P := P.withRootInput))
    (spatialFrequencyLinks Q (G.base.frequency u.2))
      ((TreeClockFibers.spatialFrequency (T := T)) (G.base.frequency u.2)) u.1.1.2.val u.1.2
  have hJ := T.selection.card_links_le_two (by omega : l + 2 ≤ 4)
  exact hb L hLa θ c hθc n (incoherenceCount Q) hg (U × α) Q' (fun _ => hspan) (fun _ => rfl) Kφ hKφ
    (fun _ => φ) (fun _ => hφ) T' R T.selection.coordinates.rootLinks hJ (fun _ => hfirst) (fun _ => hlast)
    (fun _ => rfl) (fun _ => hχroot) (fun _ => hχsel)

/-- Root-modulated filtered raw tree, printed rate (`30d, 0`), at both gate weights. -/
theorem exists_rootRawTreeKernel_rateFilt (d : ℕ) (hd : 3 ≤ d) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ l : ℕ, l ≤ 2 → ∀ η : ℝ, 0 < η → η ≤ 1 / 100 →
      (100 * (d : ℝ)) ^ 2 * η ≤ 1 →
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ θ c : ℝ, GateWeight d η θ c → ∀ n m w : ℕ, m + 1 ≤ 3 * n →
        ∀ P : MomentumTreeData n m w, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        1 ≤ incoherenceCount Q → ∀ R : RootCoordinates n, ∀ T : TreeClockFibers l Q,
        R.rootVertex 0 = T.selection.coordinates.rootVertex 0 →
        R.rootVertex 1 = T.selection.coordinates.rootVertex (Fin.last (l + 1)) →
        (∀ v ∈ R.rootBox Q, ∀ j, χ (v j) = 1) →
        (∀ v ∈ T.selection.coordinates.rootBox Q, ∀ j, χ (v j) = 1) →
        ∀ (Kφ : ℝ), 0 < Kφ → ∀ φ : Fin n → ℝ → ℂ, (∀ i, PresentedMult L Kφ (φ i)) →
        ∀ f : Fin m → Mom d → ℂ,
        (∀ a, Fourier.spatialNorm (40 * d) (40 * d) (f a) ≤ ENNReal.ofReal B) →
        ∀ E : Set (Fin 2 → ℝ), (∀ t ∈ E, t 1 ≤ t 0) →
        (∀ t ∈ E, ∀ j, χ (t j) = 1) → ∀ ζ : Circle, ∀ A : Set (Mom d),
        ∀ {α : Type} [MeasurableSpace α] (G : RootMeasure d n α),
        Fourier.mixedRestrictionNorm θ (30 * d) 0 E A
          (fun t k => (MomentumTreeData.weightedSourceTreeKernelFilt (P := P)) (G.at k) ζ R L γ δ Q φ T.timeDomain
            f t k) ≤
            ENNReal.ofReal (rootJetConstant (30 * d)) * G.momentMass (30 * d) *
            ENNReal.ofReal ((Kφ * C₁ * δ) ^ n *
              L ^ (-(incoherenceExponent d γ - Real.sqrt η) * incoherenceCount Q) * L ^ c) := by
  obtain ⟨Cₗ, hCₗ, C₀, hC₀, hb⟩ := exists_rootRawTreeKernel_restriction_boundFilt d hd
  let C₁ := treeSourceExponentialCoefficientSpatial d (30 * d) (40 * d) (40 * d) B Cₗ * C₀
  have hcoef := treeSourceExponentialCoefficient_posSpatial d (30 * d) (40 * d) (40 * d) B Cₗ
  have hC₁ : 0 < C₁ := mul_pos hcoef hC₀
  refine ⟨C₁, hC₁, ?_⟩
  intro l hl η hη hη₁ hsmall χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb l hl η hη hη₁ χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL θ c hθc n m w hm P Q hspan hg R T hfirst hlast hχroot hχsel Kφ hKφ φ hφ f hf E hforward hχext ζ A
    α _ G
  have hn := one_le_linkCount_of_incoherent Q hg
  have hLone := hL₀.trans hL
  have hLp := zero_lt_one.trans_le hLone
  have hL0 := hLp.le
  have hrate : 0 < (Kφ * C₁ * δ) ^ n *
      L ^ (-(incoherenceExponent d γ - Real.sqrt η) * incoherenceCount Q) * L ^ c :=
    mul_pos (mul_pos (pow_pos (mul_pos (mul_pos hKφ hC₁) hδ) _) (Real.rpow_pos_of_pos hLp _))
      (Real.rpow_pos_of_pos hLp _)
  by_cases hfin : G.momentMass (30 * d) = ⊤
  · exact le_top_of_momentMass_top G _ hfin (rootJetConstant_pos _) hrate _
  have hraw := hb L hL θ c hθc n m w (30 * d) (40 * d) (40 * d) P Q hspan hg R T hfirst hlast
    hχroot hχsel Kφ hKφ.le φ hφ f B (by omega) (by omega) hB hf E hforward hχext ζ A G (lt_top_iff_ne_top.mpr hfin)
  apply hraw.trans
  have habs : treeCellConstant d m (30 * d) (40 * d) (40 * d) n Cₗ B * ENNReal.ofReal ((Kφ * C₀ * δ) ^ n *
      L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q) * L ^ c) ≤
      ENNReal.ofReal ((Kφ * C₁ * δ) ^ n *
        L ^ (-(incoherenceExponent d γ - Real.sqrt η) * incoherenceCount Q) * L ^ c) := by
    have h1 := tree_source_ennreal_coefficient_leSpatial (d := d) (J := 30 * d) (K := 40 * d) (M := 40 * d) hn hm
      (B := B) hCₗ.le (mul_nonneg hKφ.le hC₀.le) hδ.le
      (mul_nonneg (Real.rpow_nonneg hL0 (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q))
        (Real.rpow_nonneg hL0 c))
    rw [mul_assoc ((Kφ * C₀ * δ) ^ n)]
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [mul_assoc ((Kφ * C₁ * δ) ^ n),
      show treeSourceExponentialCoefficientSpatial d (30 * d) (40 * d) (40 * d) B Cₗ * (Kφ * C₀) * δ =
        Kφ * C₁ * δ by ring]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (incoherence_rpow_le_sqrt_loss hLone hη.le hsmall) (Real.rpow_nonneg hL0 c)) ?_
    exact pow_nonneg (mul_nonneg (mul_nonneg hKφ.le hC₁.le) hδ.le) n
  calc
    _ = ENNReal.ofReal (rootJetConstant (30 * d)) * G.momentMass (30 * d) *
        (treeCellConstant d m (30 * d) (40 * d) (40 * d) n Cₗ B * ENNReal.ofReal ((Kφ * C₀ * δ) ^ n *
          L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q) * L ^ c)) := by ring
    _ ≤ _ := mul_le_mul' le_rfl habs

end WaveTurbulence.Flower.FiltGate
