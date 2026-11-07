/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.GateRowsH

/-! # The `q ≤ q'` orientation of a coherent couple row, layer family with leaf cost (Step 3 port, R45)

Copy-and-edit of `ConjCoh.couple_row_le_conj`/`_both`: the leaf cost of the conjugate couple equals that of the couple
(`layerCost_conj`, from the pairing of input leaves `PL234.Conj.inputs_eq`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
open WaveTurbulence WaveTurbulence.VineEstS3 WaveTurbulence.LGSpine WaveTurbulence.PL234 WaveTurbulence.ConjCoh
open scoped ENNReal

theorem layerCost_conj {w : ℕ} {LG LH : LayeredGarden w} {e : Fin w ≃ Fin w} (h : IsConjugateBy LG LH e)
    (Bh : ℕ → ℝ) : layerCost Bh LH = layerCost Bh LG := by
  have := Conj.inputs_eq h (d := 1) (fun r _ => Bh r) (fun _ => 0) (fun _ => rfl)
  unfold layerCost
  exact_mod_cast this

/-- **Row bound for a regular couple in the `q ≤ q'` orientation** (layer family, leaf cost). -/
theorem couple_row_leaf_le_conj {P : WTParams} (hgate : CoherentGateH P) (hinc : IncoherentGateH P)
    (hd : 1 ≤ P.d) (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2)
    (hC : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    {p : ℕ} (hp : p < P.D) {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ} (hB : ProfileBound P h Bh p)
    {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4)
    {Q : RegCpl} {LG : LayeredGarden 2} {q q' : ℕ} (hqp : q ≤ p) (hq'p : q' ≤ p) (hqq : q ≤ q')
    (hwf : Q.wf = true) (hsize : Q.size = 2 * n) (hdec : Q.Decodes LG.garden) (hlay : ∀ a, LG.layer a ≤ p)
    (hr0 : LG.layer (GNode.root LG.garden.tree 0) ≤ q) (hr1 : LG.layer (GNode.root LG.garden.tree 1) ≤ q')
    (hcoh : LG.incoherency Q.links = 0 → IsCoherentCoupleAt p q q' Q LG) :
    XNormRestr (6 * P.η ^ 6) (30 * P.d) (30 * P.d) (timeBox q q') Set.univ
      (fun ts k => KQstar P.L P.γ P.δ h LG (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (rowB P n (LG.incoherency Q.links) * layerCost Bh LG) := by
  by_cases hg : LG.incoherency Q.links = 0
  · have hh := conjLayered_isConjugateBy LG (Equiv.swap (0 : Fin 2) 1)
    have hr0' : (conjLayered LG (Equiv.swap (0 : Fin 2) 1)).layer
        (GNode.root (conjLayered LG (Equiv.swap (0 : Fin 2) 1)).garden.tree 0) ≤ q' := by
      have hn := PL234.Conj.node_root hh 1
      simp only [Equiv.swap_apply_right] at hn
      rw [← hn, PL234.Conj.layer_node hh]; exact hr1
    have hr1' : (conjLayered LG (Equiv.swap (0 : Fin 2) 1)).layer
        (GNode.root (conjLayered LG (Equiv.swap (0 : Fin 2) 1)).garden.tree 1) ≤ q := by
      have hn := PL234.Conj.node_root hh 0
      simp only [Equiv.swap_apply_left] at hn
      rw [← hn, PL234.Conj.layer_node hh]; exact hr0
    have hlay' : ∀ a, (conjLayered LG (Equiv.swap (0 : Fin 2) 1)).layer a ≤ p := by
      intro a
      obtain ⟨a0, rfl⟩ := (PL234.Conj.nodeEquiv hh).surjective a
      rw [PL234.Conj.layer_node hh]; exact hlay a0
    have key := couple_row_leaf_le (q := q') (q' := q) hgate hinc hd hη6 hη2 hC hδ hL hw hp hB hn hq'p hqp
      ((wf_conjCpl Q).trans hwf) ((size_conjCpl Q).trans hsize) (decodes_conj hh hdec) hlay' hr0' hr1'
      (fun h0 => by
        rw [incoherency_conj hh hdec] at h0
        exact ⟨hqq, isCoherentCoupleAt_conj hh (hcoh h0)⟩)
    rw [incoherency_conj hh hdec, layerCost_conj hh] at key
    rw [XNormRestr_KQstar_conj hh]
    exact key
  · exact couple_row_leaf_le hgate hinc hd hη6 hη2 hC hδ hL hw hp hB hn hqp hq'p hwf hsize hdec hlay hr0 hr1
      (fun h0 => absurd h0 hg)

/-- **Row bound for a regular couple, both orientations** (layer family, leaf cost). -/
theorem couple_row_leaf_le_both {P : WTParams} (hgate : CoherentGateH P) (hinc : IncoherentGateH P)
    (hd : 1 ≤ P.d) (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2)
    (hC : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    {p : ℕ} (hp : p < P.D) {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ} (hB : ProfileBound P h Bh p)
    {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4)
    {Q : RegCpl} {LG : LayeredGarden 2} {q q' : ℕ} (hqp : q ≤ p) (hq'p : q' ≤ p)
    (hwf : Q.wf = true) (hsize : Q.size = 2 * n) (hdec : Q.Decodes LG.garden) (hlay : ∀ a, LG.layer a ≤ p)
    (hr0 : LG.layer (GNode.root LG.garden.tree 0) ≤ q) (hr1 : LG.layer (GNode.root LG.garden.tree 1) ≤ q')
    (hcoh : LG.incoherency Q.links = 0 → IsCoherentCoupleAt p q q' Q LG) :
    XNormRestr (6 * P.η ^ 6) (30 * P.d) (30 * P.d) (timeBox q q') Set.univ
      (fun ts k => KQstar P.L P.γ P.δ h LG (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (rowB P n (LG.incoherency Q.links) * layerCost Bh LG) := by
  rcases le_total q' q with hqq | hqq
  · exact couple_row_leaf_le hgate hinc hd hη6 hη2 hC hδ hL hw hp hB hn hqp hq'p hwf hsize hdec hlay hr0 hr1
      (fun h0 => ⟨hqq, hcoh h0⟩)
  · exact couple_row_leaf_le_conj hgate hinc hd hη6 hη2 hC hδ hL hw hp hB hn hqp hq'p hqq hwf hsize hdec hlay
      hr0 hr1 hcoh

end WaveTurbulence.VineEstS5C
