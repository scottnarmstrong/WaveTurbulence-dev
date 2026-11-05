/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LeafCellModulationMass

/-! # Absolute coefficient mass for the global ordinary-cell singular representation -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh WithLp ApproxNT Finset

/-- The actual finite half-link cover followed by its actual ordinary-cell cover. -/
abbrev LeafSingularCellFiber {d n m : ℕ}
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (c : Fin m → Fin d → ℤ) := Σ z : S c, halfCellOrdinaryCells z.val

/-- All original leaf centers and the two literal geometric cell covers. -/
abbrev LeafSingularCellIndex {d n m : ℕ}
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ)) :=
  Σ c : Fin m → Fin d → ℤ, LeafSingularCellFiber S c

/-- A uniformly finite fiber preserves absolute summability. -/
theorem summable_sigma_finite_fiber_of_card_le {A : Type*} {B : A → Type*}
    [∀ a, Fintype (B a)] {f : A → ℝ} (hf : ∀ a, 0 ≤ f a) (hs : Summable f)
    {C : ℝ} (hc : ∀ a, (Fintype.card (B a):ℝ) ≤ C) :
    Summable (fun x : Σ a, B a => f x.1) := by
  classical
  apply (summable_sigma_of_nonneg (fun x => hf x.1)).mpr
  refine ⟨fun _ => (hasSum_fintype _).summable,?_⟩
  simp only [tsum_fintype,sum_const,card_univ,nsmul_eq_mul]
  exact Summable.of_nonneg_of_le (fun a => mul_nonneg (Nat.cast_nonneg _) (hf a))
    (fun a => mul_le_mul_of_nonneg_right (hc a) (hf a)) (hs.mul_left C)

/-- The double cover has a geometric cardinality, uniformly in all leaf centers. -/
theorem card_leafSingularCellFiber_le {d n m : ℕ}
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {C : ℝ} (hS : ∀ c, ((S c).card:ℝ) ≤ C^n) (c : Fin m → Fin d → ℤ) :
    (Fintype.card (LeafSingularCellFiber S c):ℝ) ≤
      C^n*((2*max 1 (Real.sqrt d)+5)^(2*d))^n := by
  classical
  rw [Fintype.card_sigma,Nat.cast_sum]
  calc
    _ ≤ ∑ _z : S c, ((2*max 1 (Real.sqrt d)+5)^(2*d))^n := by
      apply sum_le_sum
      intro z _
      simpa only [Fintype.card_coe] using card_halfCellOrdinaryCells_le z.val
    _ = ((S c).card:ℝ)*((2*max 1 (Real.sqrt d)+5)^(2*d))^n := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (hS c) (by positivity)

/-- The literal joint leaf/half-cell Fourier coefficient. The ordinary
cell index chooses its support cell but does not alter this coefficient. -/
def leafSingularCellCoefficient {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ} (F : Mom d → ℂ)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
      Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (i : LeafSingularCellIndex S)
    (uv : (Fin (2*Q.links.length+1) → Fin d → ℝ) ×
      ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d))) : ℂ :=
  leafSpectrumCoefficient F i.1 uv.1 * fourierW
    (halfCellAmplitude i.2.1.val (leafModulations hQ hG uv.1).1 (leafModulations hQ hG uv.1).2)
    uv.2.1 uv.2.2

/-- The literal joint coefficient is strongly measurable before any integration. -/
theorem stronglyMeasurable_leafSingularCellCoefficient {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d K M : ℕ}
    {F : Mom d → ℂ} {B : ℝ} (hK : d+1 ≤ K) (hB : 0 ≤ B)
    (hF : Fourier.spatialNorm K M F ≤ ENNReal.ofReal B)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
      Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ)) (i : LeafSingularCellIndex S) :
    StronglyMeasurable (leafSingularCellCoefficient hQ hG F S i) := by
  have hcoef : StronglyMeasurable (fun α : Fin (2*Q.links.length+1) → Fin d → ℝ =>
      leafSpectrumCoefficient F i.1 α) :=
    (stronglyMeasurable_leafSpectrumCoefficient hK hB hF).comp_measurable
      (g := fun α : Fin (2*Q.links.length+1) → Fin d → ℝ => (i.1,α))
      (measurable_const.prodMk measurable_id)
  have hβ : Measurable (fun α : Fin (2*Q.links.length+1) → Fin d → ℝ =>
      (leafModulations hQ hG α).1) := (continuous_leafModulations hQ hG d).fst.measurable
  have hγ : Measurable (fun α : Fin (2*Q.links.length+1) → Fin d → ℝ =>
      (leafModulations hQ hG α).2) := (continuous_leafModulations hQ hG d).snd.measurable
  exact stronglyMeasurable_halfCellFourierMixture i.2.1.val _ _ hβ hγ _ hcoef

/-- Every actual cell coefficient has ordinary joint L1 integrability. -/
theorem integrable_leafSingularCellCoefficient {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d K M : ℕ} (hn : 0 < Q.links.length)
    {F : Mom d → ℂ} {B : ℝ} (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hF : Fourier.spatialNorm K M F ≤ ENNReal.ofReal B)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
      Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ)) (i : LeafSingularCellIndex S) :
    Integrable (leafSingularCellCoefficient hQ hG F S i) :=
  integrable_leafCell_halfCellFourier hQ hG hn hK hM hB hF i.1 i.2.1.val

/-- Absolute masses are summable over ALL original centers and cover
indices; this supplies the generic countable singular Fubini hypothesis. -/
theorem summable_integral_norm_leafSingularCellCoefficient {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d K M : ℕ} (hn : 0 < Q.links.length)
    {F : Mom d → ℂ} {B C : ℝ} (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hF : Fourier.spatialNorm K M F ≤ ENNReal.ofReal B)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
      Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (hS : ∀ c, ((S c).card:ℝ) ≤ C^Q.links.length) :
    Summable (fun i : LeafSingularCellIndex S => ∫ uv, ‖leafSingularCellCoefficient hQ hG F S i uv‖) := by
  classical
  let Kcell := (1+2*Real.pi)*halfLinkFirstMomentConstant d^(2*Q.links.length)
  let mass := fun c : Fin (2*Q.links.length+1) → Fin d → ℤ =>
    ∫ α : Fin (2*Q.links.length+1) → Fin d → ℝ, ‖leafSpectrumCoefficient F c α‖*
      (1+((∑ j, ‖(leafModulations hQ hG α).1 j‖)+(∑ j, ‖(leafModulations hQ hG α).2 j‖)))
  have hKcell : 0 ≤ Kcell := by
    have := (halfLinkFirstMomentConstant_pos d).le
    dsimp only [Kcell]
    positivity
  have hm (c : Fin (2*Q.links.length+1) → Fin d → ℤ) : 0 ≤ mass c := by
    apply integral_nonneg
    intro α
    positivity
  have hs : Summable mass := summable_leafCell_modulation_integral hQ hG hK hM hB hF
  have hsf : Summable (fun i : LeafSingularCellIndex S => Kcell*mass i.1) :=
    summable_sigma_finite_fiber_of_card_le (fun c => mul_nonneg hKcell (hm c)) (hs.mul_left Kcell)
      (card_leafSingularCellFiber_le S hS)
  apply Summable.of_nonneg_of_le (fun i => integral_nonneg (fun _ => norm_nonneg _)) _ hsf
  intro i
  have hcoef : StronglyMeasurable (fun α : Fin (2*Q.links.length+1) → Fin d → ℝ =>
      leafSpectrumCoefficient F i.1 α) :=
    (stronglyMeasurable_leafSpectrumCoefficient (by omega) hB hF).comp_measurable
      (g := fun α : Fin (2*Q.links.length+1) → Fin d → ℝ => (i.1,α))
      (measurable_const.prodMk measurable_id)
  have hβ : Measurable (fun α : Fin (2*Q.links.length+1) → Fin d → ℝ =>
      (leafModulations hQ hG α).1) := (continuous_leafModulations hQ hG d).fst.measurable
  have hγ : Measurable (fun α : Fin (2*Q.links.length+1) → Fin d → ℝ =>
      (leafModulations hQ hG α).2) := (continuous_leafModulations hQ hG d).snd.measurable
  exact (halfCellFourierMixture_integrable_mass volume hn i.2.1.val _ _ hβ hγ _ hcoef
    (integrable_leafCell_modulation_weight hQ hG hK hM hB hF i.1)).2

end WaveTurbulence.RegAsymp
