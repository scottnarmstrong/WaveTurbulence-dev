/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.PieceGate

/-! # D3 PROT-PIN: the gates on the pieces of a cut, with star weights and filters

The star- and filter-weighted versions of `tree_piece_rn` / `couple_piece_rn`: a cut piece carrying the gate-form
multiplier `starWeight S ω · filtWeight F 0 M · filtWeight Fu 0 Mu` is bounded, one output at a time, by FILT-GATE
(incoherent) or the flat coherent gate (coherent pieces are flat, `hflat`), with the star cost `∏_{a ∈ S} cω a`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs

/-- **A tree piece with star weights and filters.** -/
theorem tree_piece_star {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (K : AlphaConsts P C₁a C₂a C₁b C₂b)
    {p : ℕ} (hp : p < P.D) {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4) {θ c' : ℝ} (hθc : PieceLoss P θ c')
    (Y : RegChain) (LGt : LayeredGarden 1) (hwf : Y.wf = true) (hsz : Y.size = 2 * n)
    (hdec : Y.DecodesTree LGt.garden) (hle : ∀ a, LGt.layer a ≤ p)
    (hlone : ∀ a : GNode LGt.garden.tree, a.1.2 = Y.lonePath → LGt.layer a = p)
    (hflat : LGt.incoherency (Y.treeLinks (LGt.garden.sig 0)) = 0 → ∀ a, LGt.layer a = p)
    (S : Finset (GNode LGt.garden.tree)) (ω : GNode LGt.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LGt.garden.tree → ℝ) (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (F : Finset (GBranch LGt.garden.tree)) (M : GBranch LGt.garden.tree → ℝ) (hM : ∀ b ∈ F, P.L ≤ M b)
    (Fu : Finset (GBranch LGt.garden.tree)) (Mu : GBranch LGt.garden.tree → ℝ) (hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
    (Ht : LeafProfiles 1 P.d) (Bt : (Fin 1 × TTree.Path) → NNReal) (hHt : LeafwiseControlled LGt Ht Bt)
    (k' : Mom P.d) :
    rn θ (timeBoxGt p p) (fun x => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGt Ht (fun _ => x 0) (x 1) k'
        (fun _ => 0) 0 (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
          filtWeight Fu (fun _ => false) Mu κ)) ≤
      (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ c') *
        regBound P n (LGt.incoherency (Y.treeLinks (LGt.garden.sig 0))) * ENNReal.ofReal (leafSizeProduct LGt Bt) := by
  have hθ := hθc.theta K.hη0 K.hη
  have h0 := rn_le_XNormRestr θ (30 * P.d) 0 (timeBoxGt (p : ℝ) p) (K := Set.univ)
    (fun ts k => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGt Ht (fun _ => ts 0) (ts 1) k (fun _ => 0) 0
      (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
        filtWeight Fu (fun _ => false) Mu κ)) (Set.mem_univ k')
  simp only [pow_zero, ENNReal.ofReal_one, one_mul] at h0
  refine h0.trans ?_
  by_cases hg : LGt.incoherency (Y.treeLinks (LGt.garden.sig 0)) = 0
  · have hlay : ∀ a : GNode LGt.garden.tree, LGt.layer a = if a.1.2 = Y.lonePath then p else p := fun a => by
      rw [hflat hg a, ite_self]
    refine ((K.hC p hp n (by rw [N_with]; exact hn) θ hθ.1 hθ.2).2 p p Y le_rfl hwf hsz LGt hdec hlay
      S ω cω hpres F (fun _ => false) M hM Fu Mu hMu Ht Bt hHt).trans ?_
    rw [hg]
    exact star_rhs_le0 K.hb0 K.hb K.hδ K.hL hθc.nonneg n 0 _ _
  · refine ((K.hI p hp n (by rw [N_with]; exact hn) θ c' hθc).2 Y hwf hsz LGt hdec hle p p le_rfl le_rfl
      (hle _) hlone (by omega) S ω cω hpres F (fun _ => false) M hM Fu Mu hMu Ht Bt hHt).trans ?_
    exact star_rhs_le K.ha0 K.ha K.hδ K.hL le_rfl n _ _ _

/-- **A couple piece with star weights and filters**, with its output weight. -/
theorem couple_piece_star {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (K : AlphaConsts P C₁a C₂a C₁b C₂b)
    {p : ℕ} (hp : p < P.D) {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4) {θ c' : ℝ} (hθc : PieceLoss P θ c')
    (Q : RegCpl) (LGc : LayeredGarden 2) (hwf : Q.wf = true) (hsz : Q.size = 2 * n)
    (hdec : Q.Decodes LGc.garden) (hle : ∀ a, LGc.layer a ≤ p)
    (hflat : LGc.incoherency Q.links = 0 → ∀ a, LGc.layer a = p)
    (S : Finset (GNode LGc.garden.tree)) (ω : GNode LGc.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LGc.garden.tree → ℝ) (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (F : Finset (GBranch LGc.garden.tree)) (M : GBranch LGc.garden.tree → ℝ) (hM : ∀ b ∈ F, P.L ≤ M b)
    (Fu : Finset (GBranch LGc.garden.tree)) (Mu : GBranch LGc.garden.tree → ℝ) (hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
    (Hc : LeafProfiles 2 P.d) (Bc : (Fin 2 × TTree.Path) → NNReal) (hHc : LeafwiseControlled LGc Hc Bc)
    (k' : Mom P.d) :
    ENNReal.ofReal (jbr k' ^ (30 * P.d)) *
        rn θ (timeBox p p) (fun x => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGc Hc
          (fun b => if b.1.1 = 0 then x 0 else x 1) 0 k' (fun _ => 0) 0
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ)) ≤
      (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ c') * regBound P n (LGc.incoherency Q.links) *
        ENNReal.ofReal (leafSizeProduct LGc Bc) := by
  have hθ := hθc.theta K.hη0 K.hη
  refine (rn_le_XNormRestr θ (30 * P.d) (30 * P.d) (timeBox (p : ℝ) p) (K := Set.univ)
    (fun ts k => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGc Hc (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 k
      (fun _ => 0) 0 (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
        filtWeight Fu (fun _ => false) Mu κ)) (Set.mem_univ k')).trans ?_
  by_cases hg : LGc.incoherency Q.links = 0
  · refine ((K.hC p hp n (by rw [N_with]; exact hn) θ hθ.1 hθ.2).1 p Q hwf hsz LGc hdec (hflat hg)
      S ω cω hpres F (fun _ => false) M hM Fu Mu hMu Hc Bc hHc).trans ?_
    rw [hg]
    exact star_rhs_le0 K.hb0 K.hb K.hδ K.hL hθc.nonneg n 0 _ _
  · refine ((K.hI p hp n (by rw [N_with]; exact hn) θ c' hθc).1 Q hwf hsz LGc hdec hle p p le_rfl le_rfl
      (hle _) (hle _) (by omega) S ω cω hpres F (fun _ => false) M hM Fu Mu hMu Hc Bc hHc).trans ?_
    exact star_rhs_le K.ha0 K.ha K.hδ K.hL le_rfl n _ _ _

end WaveTurbulence.Flower.ProtPin
