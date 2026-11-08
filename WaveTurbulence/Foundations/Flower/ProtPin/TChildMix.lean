/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TChildConj
public import WaveTurbulence.Foundations.Flower.ProtPin.TChildAmbS
public import WaveTurbulence.Foundations.Flower.ProtPin.PieceStar
public import WaveTurbulence.Foundations.Flower.ProtPin.Pointwise

/-! # D3 PROT-PIN (P7): couple pieces whose two parents lie in different layers

`TcFC P`: FILT-COH's multi-layer coherent gate at a constant `C₁c ≤ C₁` (the prefix fact of `CfgUF`).
`tc_couple_mixed`: a couple piece with star weights and filters on the box `[q₀, q₀+1] × [q₁, q₁+1]` of its parent
layers: FILT-GATE if incoherent (root layers `≤ q₀, q₁`), `TcFC` through `tc_coh_any` (either orientation) if coherent.
`tc_couple_pt`: the pointwise form (continuity). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs

/-- FILT-COH's multi-layer coherent gate with a constant `C₁c ≤ C₁`. -/
def TcFC (P : WTParams) : Prop :=
  ∃ C₁c C₂c : ℝ, FiltCoherentBoundAt { P with C₁ := C₁c, C₂ := C₂c } ∧ 0 ≤ C₁c ∧ C₁c ≤ P.C₁

/-- **A couple piece on the box of its two parent layers.** -/
theorem tc_couple_mixed {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (K : AlphaConsts P C₁a C₂a C₁b C₂b) (hFC : TcFC P)
    {p : ℕ} (hp : p < P.D) {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4) {θ c' : ℝ} (hθc : PieceLoss P θ c')
    (Q : RegCpl) (LGc : LayeredGarden 2) (hwf : Q.wf = true) (hsz : Q.size = 2 * n)
    (hdec : Q.Decodes LGc.garden) (hle : ∀ a, LGc.layer a ≤ p) {q₀ q₁ : ℕ} (hq₀ : q₀ ≤ p) (hq₁ : q₁ ≤ p)
    (hr₀ : LGc.layer (GNode.root LGc.garden.tree 0) ≤ q₀) (hr₁ : LGc.layer (GNode.root LGc.garden.tree 1) ≤ q₁)
    (hcoh : LGc.incoherency Q.links = 0 → IsCoherentCoupleAt p q₀ q₁ Q LGc)
    (S : Finset (GNode LGc.garden.tree)) (ω : GNode LGc.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LGc.garden.tree → ℝ) (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (F : Finset (GBranch LGc.garden.tree)) (M : GBranch LGc.garden.tree → ℝ) (hM : ∀ b ∈ F, P.L ≤ M b)
    (Fu : Finset (GBranch LGc.garden.tree)) (Mu : GBranch LGc.garden.tree → ℝ) (hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
    (Hc : LeafProfiles 2 P.d) (Bc : (Fin 2 × TTree.Path) → NNReal) (hHc : LeafwiseControlled LGc Hc Bc)
    (k' : Mom P.d) :
    ENNReal.ofReal (jbr k' ^ (30 * P.d)) *
        rn θ (timeBox (q₀ : ℝ) q₁) (fun x => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGc Hc
          (fun b => if b.1.1 = 0 then x 0 else x 1) 0 k' (fun _ => 0) 0
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ)) ≤
      (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ c') * regBound P n (LGc.incoherency Q.links) *
        ENNReal.ofReal (leafSizeProduct LGc Bc) := by
  have hθ := hθc.theta K.hη0 K.hη
  refine (rn_le_XNormRestr θ (30 * P.d) (30 * P.d) (timeBox (q₀ : ℝ) q₁) (K := Set.univ)
    (fun ts k => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGc Hc (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 k
      (fun _ => 0) 0 (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
        filtWeight Fu (fun _ => false) Mu κ)) (Set.mem_univ k')).trans ?_
  by_cases hg : LGc.incoherency Q.links = 0
  · obtain ⟨C₁c, C₂c, hG, hc0, hcle⟩ := hFC
    have h1 := tc_coh_any (P := { P with C₁ := C₁c, C₂ := C₂c }) hG hp (by rw [N_with]; exact hn) hθ.1 hθ.2 Q LGc
      hq₀ hq₁ hsz (hcoh hg) S ω cω hpres F (fun _ => false) M hM Fu Mu hMu Hc Bc hHc
    refine (le_of_eq_of_le (by norm_cast) h1).trans ?_
    rw [hg]
    exact star_rhs_le0 hc0 hcle K.hδ K.hL hθc.nonneg n 0 _ _
  · refine ((K.hI p hp n (by rw [N_with]; exact hn) θ c' hθc).1 Q hwf hsz LGc hdec hle q₀ q₁ hq₀ hq₁
      hr₀ hr₁ (by omega) S ω cω hpres F (fun _ => false) M hM Fu Mu hMu Hc Bc hHc).trans ?_
    exact star_rhs_le K.ha0 K.ha K.hδ K.hL le_rfl n _ _ _

/-- **The pointwise form.** -/
theorem tc_couple_pt {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (K : AlphaConsts P C₁a C₂a C₁b C₂b) (hFC : TcFC P)
    {p : ℕ} (hp : p < P.D) {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4) {θ c' : ℝ} (hθc : PieceLoss P θ c')
    (Q : RegCpl) (LGc : LayeredGarden 2) (hwf : Q.wf = true) (hsz : Q.size = 2 * n)
    (hdec : Q.Decodes LGc.garden) (hle : ∀ a, LGc.layer a ≤ p) {q₀ q₁ : ℕ} (hq₀ : q₀ ≤ p) (hq₁ : q₁ ≤ p)
    (hr₀ : LGc.layer (GNode.root LGc.garden.tree 0) ≤ q₀) (hr₁ : LGc.layer (GNode.root LGc.garden.tree 1) ≤ q₁)
    (hcoh : LGc.incoherency Q.links = 0 → IsCoherentCoupleAt p q₀ q₁ Q LGc)
    (S : Finset (GNode LGc.garden.tree)) (ω : GNode LGc.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LGc.garden.tree → ℝ) (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (F : Finset (GBranch LGc.garden.tree)) (M : GBranch LGc.garden.tree → ℝ) (hM : ∀ b ∈ F, P.L ≤ M b)
    (Fu : Finset (GBranch LGc.garden.tree)) (Mu : GBranch LGc.garden.tree → ℝ) (hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
    (Hc : LeafProfiles 2 P.d) (Bc : (Fin 2 × TTree.Path) → NNReal) (hHc : LeafwiseControlled LGc Hc Bc)
    (k' : Mom P.d)
    (hcont : Continuous fun x : Fin 2 → ℝ => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGc Hc
      (fun b => if b.1.1 = 0 then x 0 else x 1) 0 k' (fun _ => 0) 0
      (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
        filtWeight Fu (fun _ => false) Mu κ))
    {x : Fin 2 → ℝ} (hx : x ∈ timeBox (q₀ : ℝ) q₁) :
    ENNReal.ofReal (jbr k' ^ (30 * P.d)) *
        ‖Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGc Hc (fun b => if b.1.1 = 0 then x 0 else x 1) 0 k'
          (fun _ => 0) 0 (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ)‖ₑ ≤
      (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ c') * regBound P n (LGc.incoherency Q.links) *
        ENNReal.ofReal (leafSizeProduct LGc Bc) := by
  have hθ := hθc.theta K.hη0 K.hη
  refine (mul_le_mul' le_rfl (enorm_le_rn hθ.1
    (fun y hy => VineEstS3.timeBox_subset_closure_interior _ _ hy) hcont hx)).trans ?_
  exact tc_couple_mixed K hFC hp hn hθc Q LGc hwf hsz hdec hle hq₀ hq₁ hr₀ hr₁ hcoh S ω cω hpres F M hM Fu Mu
    hMu Hc Bc hHc k'

end WaveTurbulence.Flower.ProtPin
