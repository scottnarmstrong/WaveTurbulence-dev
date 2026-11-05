/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeBoundedSourceAgreement
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreePhaseRootIndependent

/-! # The literal KTstar is the actual moving-root leaf Fourier mixture -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh IncohInst Links

/-- The actual original time and squared-Wick coefficient, independent of the root momentum. -/
def treeOriginalArrayCoefficient {d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden 1)
    {X : RegChain} (hX : X.DecodesTree LG.garden) (t s : ℝ)
    (g : (Fin (X.treeLinks (LG.garden.sig 0)).length → Fin d → ℤ) ×
      (Fin (X.treeLinks (LG.garden.sig 0)).length → Fin d → ℤ)) : ℂ :=
  treeOriginalLatticeCoefficient L γ δ LG hX t s 0
    (fun p => if p.2=0 then g.1 p.1 else g.2 p.1)

/-- The original array coefficient obeys the unit bound for every pair of endpoints. -/
theorem treeOriginalArrayCoefficient_norm_le {d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden 1)
    {X : RegChain} (hX : X.DecodesTree LG.garden) (h0 : ∀ a, LG.layer a = 0)
    (t s : ℝ)
    (g : (Fin (X.treeLinks (LG.garden.sig 0)).length → Fin d → ℤ) ×
      (Fin (X.treeLinks (LG.garden.sig 0)).length → Fin d → ℤ)) :
    ‖treeOriginalArrayCoefficient L γ δ LG hX t s g‖ ≤ 1 :=
  treeOriginalLatticeCoefficient_norm_le L γ δ LG hX h0 t s 0 _

/-- The original kernel, with its exact source coupling and garden sign, equals the
actual moving-root leaf Fourier mixture. All global exchanges and root input removal
are proved from the original finite spatial norms, including for order zero. -/
theorem KTstar_eq_tree_leaf_spectral_mixture {d K M : ℕ} (L γ δ : ℝ)
    (LG : LayeredGarden 1) {X : RegChain} (hX : X.DecodesTree LG.garden)
    (hwf : X.wf = true) (h0 : ∀ a, LG.layer a = 0)
    {B : ℝ} (hB : 0 ≤ B) (hL : 1 ≤ L) (hK : d+2 ≤ K) (hM : 2*d ≤ M)
    (F : Mom d → ℝ)
    (hf : ∀ a, Fourier.spatialNorm K M (treeInputFunctions LG (fun _ => F) a) ≤ ENNReal.ofReal B)
    (S : (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, (treeCarrier hX).withRootInput.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p => x p.1 p.2) ≠ 0 → z ∈ S c)
    {C : ℝ} (hS : ∀ c, ((S c).card:ℝ) ≤ C^(X.treeLinks (LG.garden.sig 0)).length)
    {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1) (k : Mom d) :
    KTstar L γ δ (fun _ => F) LG t s k =
      (coupling d L γ δ:ℂ)^LG.garden.order*LG.garden.zeta*
        ∫ u, rootAmplitudeSum (treeRootLeafAmplitude (treeInputFunctions LG (fun _ => F)) S) k u *
          treeBoundedScalar hX L (treeOriginalArrayCoefficient L γ δ LG hX t s) S u
            ∂treeLeafCellMeasure S := by
  rw [tree_bounded_mixture_eq_source hX hL
    (treeOriginalArrayCoefficient L γ δ LG hX t s) zero_le_one
      (treeOriginalArrayCoefficient_norm_le L γ δ LG hX h0 t s)
        (treeInputFunctions LG (fun _ => F)) hK hM hB hf S hcover hS,
    KTstar_eq_original_lattice_source L γ δ LG hX F t s k]
  apply congrArg (fun v : ℂ => (coupling d L γ δ:ℂ)^LG.garden.order*LG.garden.zeta*v)
  let E := (linkLatticeArrayEquiv (Fin (X.treeLinks (LG.garden.sig 0)).length) (Fin d → ℤ)).trans
    (Equiv.arrowProdEquivProdArrow (Fin (X.treeLinks (LG.garden.sig 0)).length)
      (fun _ => Fin d → ℤ) (fun _ => Fin d → ℤ))
  rw [← E.symm.tsum_eq]
  apply tsum_congr
  intro g
  rw [treeOriginalLatticeCoefficient_root_independent L γ δ LG hX hwf h0 hs hst ht _ k 0]
  have hx : (fun j i => latticePoint L (E.symm g (j,i))) =
      (fun j i => if i=0 then latticePoint L (g.1 j) else latticePoint L (g.2 j)) := by
    funext j i
    fin_cases i <;> rfl
  rw [hx]
  rfl

end WaveTurbulence.RegAsymp
