/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.CoupleMomentumData
public import WaveTurbulence.Foundations.Incoh.RootInputCoordinates

/-! # Actual source leaf signs supply the root-mask structural premise -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links Incoh

/-- The source sigma signs recover the actual root from all input leaves.
This datum contains only finite integer rows, with no analytic conclusion. -/
def coupleRootInputCoordinates {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) :
    RootInputCoordinates (coupleMomentumData hQ hG) where
  sigma a := incohSigma G (plusLeafEquiv hQ hG a).val
  abs_sigma_le a := by
    have h := incohSigma_mem (G := G) (plusLeafEquiv hQ hG a).val
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h <;> rw [h] <;> norm_num
  root_row := by
    funext c
    have h := root_eq_sigma_sum hG (coordinateDecoration hQ c).property.1
    have he : (∑ ℓ ∈ plusLeaves G,
        incohSigma G ℓ • (coordinateDecoration hQ c).val ℓ.toNode) =
        ∑ a, incohSigma G (plusLeafEquiv hQ hG a).val •
          (coordinateDecoration hQ c).val (plusLeafEquiv hQ hG a).val.toNode := by
      calc
        _ = ∑ ℓ : PlusLeaf G, incohSigma G ℓ.val •
            (coordinateDecoration hQ c).val ℓ.val.toNode :=
          Finset.sum_subtype _ (fun ℓ => mem_plusLeaves ℓ) _
        _ = _ := ((plusLeafEquiv hQ hG).sum_comp _).symm
    rw [he] at h
    have hroot := congrFun (sourceNodeRow_root hQ 0) c
    change (coordinateDecoration hQ c).val (GNode.root G.tree 0) = momentumUnitRow none c at hroot
    simp only [Finset.sum_apply, Pi.smul_apply]
    change (∑ a, incohSigma G (plusLeafEquiv hQ hG a).val •
      (coordinateDecoration hQ c).val (plusLeafEquiv hQ hG a).val.toNode) = _
    exact h.symm.trans hroot

end WaveTurbulence.RegAsymp
