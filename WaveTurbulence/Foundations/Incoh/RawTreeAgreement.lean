/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.MovingTreePointwise
public import WaveTurbulence.Foundations.Incoh.FiniteSelectionIntegral
public import WaveTurbulence.Foundations.Incoh.RawSourceCellIntegral

/-!
# Exact raw source agreement of the moving-cell tree extension

The finite cover need only cover each actual root momentum separately.
Pointwise Fubini and the actual causal source identity identify the full
moving-cell spectral extension with the raw unlocalized source operator.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff ENNReal

namespace WaveTurbulence.Incoh

/-- The literal raw source tree kernel with its original external causal root constraints. -/
@[expose] def MomentumTreeData.sourceTreeKernel {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (f : Fin m → Mom d → ℂ) (t : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  P.sourceIntegral ζ L γ δ Q (I ∩ R.causalRootCut t) f k

/-- Exact raw tree source agreement. The physical root envelope is only a conditional Fubini
premise and is supplied by the independently proved analytic core in the final source bound. -/
theorem MomentumTreeData.movingCellSourceTreeExtension_agrees_raw {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (R : RootCoordinates n)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : Fourier.CutoffControl χ)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (hI : MeasurableSet I) (hbox : I ⊆ univ.pi (fun i => linkBox (Q i)))
    (hχroot : ∀ a ∈ R.rootBox Q, ∀ j, χ (a j) = 1)
    (f : Fin m → Mom d → ℂ)
    (S : Mom d → (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (hcover : ∀ k c x, P.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin n × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S k c)
    {C : ℝ} (hS : ∀ k c, ((S k c).card : ℝ) ≤ C ^ n) {B : ℝ}
    (hL : 1 ≤ L) (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    {N : ℝ≥0∞} (hN : N < ⊤)
    (hb : ∀ z : (Fin n × Fin 2) → Fin d → ℤ, ∀ ξ : LocalizedCellIndex n m → Fin d → ℝ,
      eLpNorm (R.linkDensity L γ δ (P.spectralLinks Q z ξ) I) 1 ≤ N)
    (t : Fin 2 → ℝ) (ht : t ∈ R.rootBox Q) (hord : t 1 ≤ t 0) (k : Mom d) :
    P.movingCellSourceTreeExtension ζ R χ L γ δ Q I f S t k =
      P.sourceTreeKernel ζ R L γ δ Q I f t k := by
  classical
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hs := P.integrable_movingTreeSlice_of_uniformRootL1 ζ R hχ hc L γ δ Q I hI hbox
    f S hS hLp hK hM hB h hN hb t k
  let F := fun c z ξ => P.sourceSpectralAmplitude ζ f c z k ξ *
    P.unrestrictedTreeKernel R χ L γ δ Q I t ((c, z), ξ)
  change Integrable (fun u => P.movingCellAmplitude ζ f S k u *
    P.unrestrictedTreeKernel R χ L γ δ Q I t u) (Measure.count.prod volume) at hs
  have hF : Integrable (fun u : UnrestrictedCellIndex d n m × (LocalizedCellIndex n m → Fin d → ℝ) =>
      if u.1.2 ∈ S k u.1.1 then F u.1.1 u.1.2 u.2 else 0) (Measure.count.prod volume) := by
    convert hs using 1
    funext u
    unfold movingCellAmplitude
    split_ifs <;> simp only [F, zero_mul]
  have he := integral_count_product_finite_selection volume (S k) F hF
  have hcell : P.movingCellSourceTreeExtension ζ R χ L γ δ Q I f S t k =
      ∑' u : SourceCellIndex (S k), ∫ ξ, F u.1 u.2.val ξ := by
    unfold movingCellSourceTreeExtension unrestrictedCellMeasure movingCellAmplitude
    simp only [ite_mul, zero_mul]
    exact he
  rw [hcell]
  unfold sourceTreeKernel
  rw [P.sourceIntegral_eq_tsum_localizedSourceIntegral_of_cover_at ζ L γ δ Q (I ∩ R.causalRootCut t)
    (Set.inter_subset_left.trans hbox) f (S k) k (hcover k) (hS k) hL hK hM hB h]
  apply tsum_congr
  intro u
  rw [P.localizedSourceIntegral_eq_linkKernelMixture ζ L γ δ Q (I ∩ R.causalRootCut t)
    (Set.inter_subset_left.trans hbox) f u.1 u.2.val hLp hK hB h k]
  apply integral_congr_ae
  apply ae_of_all
  intro ξ
  dsimp only [F]
  congr 1
  exact P.unrestrictedTreeKernel_agrees R L γ δ Q I hI hbox hχroot hLp t ht hord ((u.1, u.2.val), ξ)

end WaveTurbulence.Incoh
