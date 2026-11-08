/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.None
public import WaveTurbulence.Foundations.Flower.ProtPin.Restr

/-! # D3 PROT-PIN: the gates on the pieces of a cut, one output at a time

A regular paired tree (a cut piece: prefix or interior) in layers `≤ p` with lone leaf in layer `p`, and a regular
couple in layers `≤ p`, are bounded at every output `k'` in the scalar restricted norm `rn θ`, on `timeBoxGt p p`
resp. `timeBox p p`, by FILT-GATE (incoherent) or the flat coherent gate `CohFlatAt` (coherent pieces are flat in
layer `p`, the hypothesis `hflat`, supplied by `CutFlat.lean` from the canonical ambient); couples with the output
weight `⟨k'⟩^{30d}`. The loss is `L^{c'}`, `c' = 0` at `θ = η` and `c' = 4d` at `θ = 1/4`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs

/-- The per-piece loss exponent of the gates. -/
def PieceLoss (P : WTParams) (θ c' : ℝ) : Prop := (θ = P.η ∧ c' = 0) ∨ (θ = 1 / 4 ∧ c' = 4 * P.d)

theorem PieceLoss.nonneg {P : WTParams} {θ c' : ℝ} (h : PieceLoss P θ c') : 0 ≤ c' := by
  rcases h with ⟨-, h⟩ | ⟨-, h⟩ <;> subst h <;> positivity

theorem PieceLoss.theta {P : WTParams} {θ c' : ℝ} (hη0 : 0 ≤ P.η) (hη : P.η ≤ 1 / 4) (h : PieceLoss P θ c') :
    0 ≤ θ ∧ θ ≤ 1 / 4 := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ <;> subst h
  · exact ⟨hη0, hη⟩
  · norm_num

/-- **A tree piece.** -/
theorem tree_piece_rn {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (K : AlphaConsts P C₁a C₂a C₁b C₂b)
    {p : ℕ} (hp : p < P.D) {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4) {θ c' : ℝ} (hθc : PieceLoss P θ c')
    (Y : RegChain) (LGt : LayeredGarden 1) (hwf : Y.wf = true) (hsz : Y.size = 2 * n)
    (hdec : Y.DecodesTree LGt.garden) (hle : ∀ a, LGt.layer a ≤ p)
    (hlone : ∀ a : GNode LGt.garden.tree, a.1.2 = Y.lonePath → LGt.layer a = p)
    (hflat : LGt.incoherency (Y.treeLinks (LGt.garden.sig 0)) = 0 → ∀ a, LGt.layer a = p)
    (Ht : LeafProfiles 1 P.d) (Bt : (Fin 1 × TTree.Path) → NNReal) (hHt : LeafwiseControlled LGt Ht Bt)
    (k' : Mom P.d) :
    rn θ (timeBoxGt p p) (fun x => treeLeaves P.L P.γ P.δ LGt Ht (x 0) (x 1) k') ≤
      ENNReal.ofReal (P.L ^ c') * regBound P n (LGt.incoherency (Y.treeLinks (LGt.garden.sig 0))) *
        ENNReal.ofReal (leafSizeProduct LGt Bt) := by
  have hθ := hθc.theta K.hη0 K.hη
  have h0 := rn_le_XNormRestr θ (30 * P.d) 0 (timeBoxGt (p : ℝ) p) (K := Set.univ)
    (fun ts k => treeLeaves P.L P.γ P.δ LGt Ht (ts 0) (ts 1) k) (Set.mem_univ k')
  simp only [pow_zero, ENNReal.ofReal_one, one_mul] at h0
  refine h0.trans ?_
  have hk : ∀ (ts : Fin 2 → ℝ) (k : Mom P.d), Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGt Ht (fun _ => ts 0)
      (ts 1) k (fun _ => 0) 0 (fun κ => Flower.IncTop.starWeight ∅ (fun _ _ => 0) κ *
        filtWeight ∅ (fun _ => false) (fun _ => 0) κ * filtWeight ∅ (fun _ => false) (fun _ => 0) κ) =
      treeLeaves P.L P.γ P.δ LGt Ht (ts 0) (ts 1) k := fun ts k =>
    kernelLeavesW_one _ _ _ _ _ _ _ _ _ _ _ (gateMult_eq_one _ _ _ _)
  by_cases hg : LGt.incoherency (Y.treeLinks (LGt.garden.sig 0)) = 0
  · have hlay : ∀ a : GNode LGt.garden.tree, LGt.layer a = if a.1.2 = Y.lonePath then p else p := fun a => by
      rw [hflat hg a, ite_self]
    have hb := (K.hC p hp n (by rw [N_with]; exact hn) θ hθ.1 hθ.2).2 p p Y le_rfl hwf hsz LGt hdec hlay
      ∅ (fun _ _ => 0) (fun _ => 0) (by simp) ∅ (fun _ => false) (fun _ => 0) (by simp) ∅ (fun _ => 0) (by simp)
      Ht Bt hHt
    refine le_trans (le_of_eq (XNormRestr_congr fun ts _ k _ => (hk ts k).symm)) (hb.trans ?_)
    rw [Finset.prod_empty, one_mul, hg]
    calc regBound { P with C₁ := C₁b, C₂ := C₂b } n 0 * ENNReal.ofReal (leafSizeProduct LGt Bt)
        = ENNReal.ofReal (P.L ^ (0 : ℝ)) * regBound { P with C₁ := C₁b, C₂ := C₂b } n 0 *
            ENNReal.ofReal (leafSizeProduct LGt Bt) := by simp
      _ ≤ _ := none_rhs_le K.hb0 K.hb K.hδ K.hL hθc.nonneg n 0 _
  · have hb := (K.hI p hp n (by rw [N_with]; exact hn) θ c' hθc).2 Y hwf hsz LGt hdec hle p p le_rfl le_rfl
      (hle _) hlone (by omega) ∅ (fun _ _ => 0) (fun _ => 0) (by simp) ∅ (fun _ => false) (fun _ => 0) (by simp)
      ∅ (fun _ => 0) (by simp) Ht Bt hHt
    refine le_trans (le_of_eq (XNormRestr_congr fun ts _ k _ => (hk ts k).symm)) (hb.trans ?_)
    rw [Finset.prod_empty, one_mul]
    exact none_rhs_le K.ha0 K.ha K.hδ K.hL le_rfl n _ _

/-- **A couple piece**, with its output weight. -/
theorem couple_piece_rn {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (K : AlphaConsts P C₁a C₂a C₁b C₂b)
    {p : ℕ} (hp : p < P.D) {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4) {θ c' : ℝ} (hθc : PieceLoss P θ c')
    (Q : RegCpl) (LGc : LayeredGarden 2) (hwf : Q.wf = true) (hsz : Q.size = 2 * n)
    (hdec : Q.Decodes LGc.garden) (hle : ∀ a, LGc.layer a ≤ p)
    (hflat : LGc.incoherency Q.links = 0 → ∀ a, LGc.layer a = p)
    (Hc : LeafProfiles 2 P.d) (Bc : (Fin 2 × TTree.Path) → NNReal) (hHc : LeafwiseControlled LGc Hc Bc)
    (k' : Mom P.d) :
    ENNReal.ofReal (jbr k' ^ (30 * P.d)) *
        rn θ (timeBox p p) (fun x => coupleLeaves P.L P.γ P.δ LGc Hc (x 0) (x 1) k') ≤
      ENNReal.ofReal (P.L ^ c') * regBound P n (LGc.incoherency Q.links) *
        ENNReal.ofReal (leafSizeProduct LGc Bc) := by
  have hθ := hθc.theta K.hη0 K.hη
  refine (rn_le_XNormRestr θ (30 * P.d) (30 * P.d) (timeBox (p : ℝ) p) (K := Set.univ)
    (fun ts k => coupleLeaves P.L P.γ P.δ LGc Hc (ts 0) (ts 1) k) (Set.mem_univ k')).trans ?_
  have hk : ∀ (ts : Fin 2 → ℝ) (k : Mom P.d), Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGc Hc
      (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 k (fun _ => 0) 0
      (fun κ => Flower.IncTop.starWeight ∅ (fun _ _ => 0) κ *
        filtWeight ∅ (fun _ => false) (fun _ => 0) κ * filtWeight ∅ (fun _ => false) (fun _ => 0) κ) =
      coupleLeaves P.L P.γ P.δ LGc Hc (ts 0) (ts 1) k := fun ts k =>
    kernelLeavesW_one _ _ _ _ _ _ _ _ _ _ _ (gateMult_eq_one _ _ _ _)
  by_cases hg : LGc.incoherency Q.links = 0
  · have hb := (K.hC p hp n (by rw [N_with]; exact hn) θ hθ.1 hθ.2).1 p Q hwf hsz LGc hdec (hflat hg)
      ∅ (fun _ _ => 0) (fun _ => 0) (by simp) ∅ (fun _ => false) (fun _ => 0) (by simp) ∅ (fun _ => 0) (by simp)
      Hc Bc hHc
    refine le_trans (le_of_eq (XNormRestr_congr fun ts _ k _ => (hk ts k).symm)) (hb.trans ?_)
    rw [Finset.prod_empty, one_mul, hg]
    calc regBound { P with C₁ := C₁b, C₂ := C₂b } n 0 * ENNReal.ofReal (leafSizeProduct LGc Bc)
        = ENNReal.ofReal (P.L ^ (0 : ℝ)) * regBound { P with C₁ := C₁b, C₂ := C₂b } n 0 *
            ENNReal.ofReal (leafSizeProduct LGc Bc) := by simp
      _ ≤ _ := none_rhs_le K.hb0 K.hb K.hδ K.hL hθc.nonneg n 0 _
  · have hb := (K.hI p hp n (by rw [N_with]; exact hn) θ c' hθc).1 Q hwf hsz LGc hdec hle p p le_rfl le_rfl
      (hle _) (hle _) (by omega) ∅ (fun _ _ => 0) (fun _ => 0) (by simp) ∅ (fun _ => false) (fun _ => 0) (by simp)
      ∅ (fun _ => 0) (by simp) Hc Bc hHc
    refine le_trans (le_of_eq (XNormRestr_congr fun ts _ k _ => (hk ts k).symm)) (hb.trans ?_)
    rw [Finset.prod_empty, one_mul]
    exact none_rhs_le K.ha0 K.ha K.hδ K.hL le_rfl n _ _

end WaveTurbulence.Flower.ProtPin
