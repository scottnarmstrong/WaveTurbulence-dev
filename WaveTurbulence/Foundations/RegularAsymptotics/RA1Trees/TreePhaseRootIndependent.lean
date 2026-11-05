/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreePhysicalCellExpansion
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreePhysicalEnergy

/-! # The literal original regular-tree phase is independent of root momentum -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh IncohInst Links ClassJR MainCoef WithLp

/-- The original coefficient family and source conservation remove the root momentum
from the actual tree phase, while retaining the original physical NT parameter2delta. -/
theorem tree_phaseIntegral_root_independent {d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden 1)
    {X : RegChain} (hX : X.DecodesTree LG.garden) (hwf : X.wf = true)
    (h0 : ∀ a, LG.layer a = 0) {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1)
    (p : (Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ)
    (k k' : Mom d) :
    phaseIntegral L γ δ LG.garden (kDomain LG (fun _ => t) s) s
      (cosetDecoration LG.garden L k (treeDecOfParams hX (0:Fin d → ℤ)
        (fun j => (p (j,0),p (j,1)))).val) =
    phaseIntegral L γ δ LG.garden (kDomain LG (fun _ => t) s) s
      (cosetDecoration LG.garden L k' (treeDecOfParams hX (0:Fin d → ℤ)
        (fun j => (p (j,0),p (j,1)))).val) := by
  obtain ⟨C,-,hphase⟩ := actual_tree_profile_expansion (η := 1) (by norm_num)
    (by norm_num) (le_refl ClassJR.A1) X hwf (LG.garden.sig 0)
  have he (v : Mom d) := hphase d L γ δ LG rfl h0 hX
    (cosetDecoration LG.garden L v (treeDecOfParams hX (0:Fin d → ℤ)
      (fun j => (p (j,0),p (j,1)))).val)
    (by
      rw [← tree_decOfParams_eq_coset hX L v]
      exact (treeDecOfParams hX v _).property.1) t s hs hst ht s
  rw [he k,he k']
  simp_rw [tree_alphaOmega_chosen]

/-- The squared-Wick factor also carries no root-momentum dependence. -/
theorem treeOriginalLatticeCoefficient_root_independent {d : ℕ} (L γ δ : ℝ)
    (LG : LayeredGarden 1) {X : RegChain} (hX : X.DecodesTree LG.garden)
    (hwf : X.wf = true) (h0 : ∀ a, LG.layer a = 0)
    {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1)
    (p : (Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ)
    (k k' : Mom d) :
    treeOriginalLatticeCoefficient L γ δ LG hX t s k p =
      treeOriginalLatticeCoefficient L γ δ LG hX t s k' p := by
  unfold treeOriginalLatticeCoefficient
  rw [tree_phaseIntegral_root_independent L γ δ LG hX hwf h0 hs hst ht p k k']

end WaveTurbulence.RegAsymp
