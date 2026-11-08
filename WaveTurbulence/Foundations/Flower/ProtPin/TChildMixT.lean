/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TChildMix

/-! # D3 PROT-PIN (P7): tree pieces whose lone leaf lies below their parent layer

`tc_tree_mixed`: a tree piece (root parent layer `q`, lone leaf in layer `q' ≤ q`) with star weights and filters on
`timeBoxGt q q'`: FILT-GATE if incoherent (root layer `≤ q`), FILT-COH's tree clause (`TcFC`) if coherent
(`IsCoherentTreeAt p q q'`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs

/-- **A tree piece on the box of its parent and lone layers.** -/
theorem tc_tree_mixed {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (K : AlphaConsts P C₁a C₂a C₁b C₂b) (hFC : TcFC P)
    {p : ℕ} (hp : p < P.D) {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4) {θ c' : ℝ} (hθc : PieceLoss P θ c')
    (Y : RegChain) (LGt : LayeredGarden 1) (hwf : Y.wf = true) (hsz : Y.size = 2 * n)
    (hdec : Y.DecodesTree LGt.garden) (hle : ∀ a, LGt.layer a ≤ p) {q q' : ℕ} (hqq : q' ≤ q) (hqp : q ≤ p)
    (hroot : LGt.layer (GNode.root LGt.garden.tree 0) ≤ q)
    (hlone : ∀ a : GNode LGt.garden.tree, a.1.2 = Y.lonePath → LGt.layer a = q')
    (hcoh : LGt.incoherency (Y.treeLinks (LGt.garden.sig 0)) = 0 → IsCoherentTreeAt p q q' Y LGt)
    (S : Finset (GNode LGt.garden.tree)) (ω : GNode LGt.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LGt.garden.tree → ℝ) (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (F : Finset (GBranch LGt.garden.tree)) (M : GBranch LGt.garden.tree → ℝ) (hM : ∀ b ∈ F, P.L ≤ M b)
    (Fu : Finset (GBranch LGt.garden.tree)) (Mu : GBranch LGt.garden.tree → ℝ) (hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
    (Ht : LeafProfiles 1 P.d) (Bt : (Fin 1 × TTree.Path) → NNReal) (hHt : LeafwiseControlled LGt Ht Bt)
    (k' : Mom P.d) :
    rn θ (timeBoxGt (q : ℝ) q') (fun x => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGt Ht (fun _ => x 0) (x 1) k'
        (fun _ => 0) 0 (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
          filtWeight Fu (fun _ => false) Mu κ)) ≤
      (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ c') *
        regBound P n (LGt.incoherency (Y.treeLinks (LGt.garden.sig 0))) * ENNReal.ofReal (leafSizeProduct LGt Bt) := by
  have hθ := hθc.theta K.hη0 K.hη
  have h0 := rn_le_XNormRestr θ (30 * P.d) 0 (timeBoxGt (q : ℝ) q') (K := Set.univ)
    (fun ts k => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGt Ht (fun _ => ts 0) (ts 1) k (fun _ => 0) 0
      (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
        filtWeight Fu (fun _ => false) Mu κ)) (Set.mem_univ k')
  simp only [pow_zero, ENNReal.ofReal_one, one_mul] at h0
  refine h0.trans ?_
  by_cases hg : LGt.incoherency (Y.treeLinks (LGt.garden.sig 0)) = 0
  · obtain ⟨C₁c, C₂c, hG, hc0, hcle⟩ := hFC
    have h1 := (hG p hp n (by rw [N_with]; exact hn) θ hθ.1 hθ.2).2 Y LGt q q' hqq hqp hsz (hcoh hg) S ω cω hpres
      F (fun _ => false) M hM Fu Mu hMu Ht Bt hHt
    refine (le_of_eq_of_le (by norm_cast) h1).trans ?_
    rw [hg]
    exact star_rhs_le0 hc0 hcle K.hδ K.hL hθc.nonneg n 0 _ _
  · refine ((K.hI p hp n (by rw [N_with]; exact hn) θ c' hθc).2 Y hwf hsz LGt hdec hle q q' hqq hqp
      hroot hlone (by omega) S ω cω hpres F (fun _ => false) M hM Fu Mu hMu Ht Bt hHt).trans ?_
    exact star_rhs_le K.ha0 K.ha K.hδ K.hL le_rfl n _ _ _

end WaveTurbulence.Flower.ProtPin
