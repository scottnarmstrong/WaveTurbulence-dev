/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.BinaryMomentumConvergence
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceAddressFactors

/-! # Exact binary source root operation with an independent scalar factor -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links Reg ApproxNT

/-- A mini-tree's original binary root operation contributes exactly
factor2, retaining its literal delta/PV choice. Finite child norms justify
scalar extraction at a PV root, including a vanishing scalar. -/
theorem addressAppStep_binary_source {d w K M : ℕ} (hd : 2 ≤ d)
    (hK : 0 < K) (hM : 2*d < M) {B : ℝ} (hB : 0 ≤ B)
    {f g : Mom d → ℝ}
    (hf : Fourier.spatialNorm K M (fun x => (f x:ℂ)) ≤ ENNReal.ofReal B)
    (hg : Fourier.spatialNorm K M (fun x => (g x:ℂ)) ≤ ENNReal.ofReal B)
    (m : MiniTreeCode) (Z : Finset (Fin w × TTree.Path)) (a : Fin w × TTree.Path)
    (k : Mom d) (c : ℂ) (θ : Fin w × TTree.Path → Mom d × Mom d) :
    addressAppStep Z a (fun θ => c*
      (f (childVals k (θ a) m.red.1)*g (childVals k (θ a) m.green.1):ℝ)) θ =
    (2:ℂ)*c*((if a∈Z then pvResonantIntegral (binaryMomentumFunction m.c f g) k
      else resIntegral (binaryMomentumFunction m.c f g) k):ℝ) := by
  classical
  simp only [addressAppStep,Function.update_self]
  have he : (fun x y => c*(f (childVals k (x,y) m.red.1)*
      g (childVals k (x,y) m.green.1):ℝ)) =
      (fun x y => c*(binaryMomentumFunction m.c f g (k+x) (k+x-y) (k-y):ℂ)) := by
    funext x y
    rw [binaryMomentumFunction_eq_miniTree]
    rfl
  rw [he]
  split_ifs
  · rw [pvOp_const_mul_binaryMomentum_of_spatialNorm hd hK hM hB hf hg,
      pvOp_binaryMomentum_of_spatialNorm hd hK hM hB hf hg]
    ring
  · rw [deltaInner_const_mul,deltaInner_source_momentum]
    ring

end WaveTurbulence.RegAsymp
