/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.GateRows
public import WaveTurbulence.Foundations.VineEst.ConjCoherent
public import WaveTurbulence.Foundations.VineEst.NormSwapConj

/-!
# The `q < q'` orientation of a coherent couple row (CONJ-COH; ruling R20(5))

`couple_row_le` (V5 `GateRows`) bounds the starred kernel of a regular couple of incoherency index `0` only for
`q' ≤ q`, the orientation of the 0814 gate.  For `q ≤ q'` the conjugate couple (`conjCpl Q`, `LGbar`) is coherent at
`(p, q', q)` (`isCoherentCoupleAt_conj`) and `K*_{LG}(t, s) = conj K*_{LGbar}(s, t)` (`KQstar_conj`), so by the
swap-and-conjugate invariance of `XNormRestr` (`XNormRestr_swapConj`) the bound for `(q, q')` follows from the bound
for `(q', q)` applied to the conjugate.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct

namespace WaveTurbulence.ConjCoh

open WaveTurbulence WaveTurbulence.VineEstS3 WaveTurbulence.LGSpine WaveTurbulence.PL234

theorem timeBox_permT (q q' : ℝ) :
    permT (Equiv.swap (0 : Fin 2) 1) ⁻¹' timeBox q q' = timeBox q' q := by
  ext ts
  simp [timeBox, permT, and_comm]

theorem swap_invol : ∀ i : Fin 2, (Equiv.swap (0 : Fin 2) 1) ((Equiv.swap (0 : Fin 2) 1) i) = i := fun i => by
  simp

/-- The restriction norm of the starred kernel of `LG` over `ℬ(q, q')` is that of the conjugate garden over
`ℬ(q', q)`. -/
theorem XNormRestr_KQstar_conj {LG LGbar : LayeredGarden 2} (h : IsConjugateCouple LG LGbar)
    (θ : ℝ) (Λ₁ Λ₂ : ℕ) (q q' : ℝ) (L γ δ : ℝ) {d : ℕ} (F : ℕ → Mom d → ℝ) :
    XNormRestr θ Λ₁ Λ₂ (timeBox q q') Set.univ (fun ts k => KQstar L γ δ F LG (ts 0) (ts 1) k) =
      XNormRestr θ Λ₁ Λ₂ (timeBox q' q) Set.univ (fun ts k => KQstar L γ δ F LGbar (ts 0) (ts 1) k) := by
  have hf : (fun (ts : Fin 2 → ℝ) (k : Mom d) => KQstar L γ δ F LG (ts 0) (ts 1) k) =
      swapConj (Equiv.swap (0 : Fin 2) 1) (fun ts k => KQstar L γ δ F LGbar (ts 0) (ts 1) k) := by
    funext ts k
    have := KQstar_conj L γ δ F h (ts 1) (ts 0) k
    simp only [swapConj, permT]
    simp [this]
  rw [hf, XNormRestr_swapConj swap_invol, timeBox_permT]


/-- **Row bound for a regular couple in the `q ≤ q'` orientation.**  Same conclusion as `couple_row_le`, with
`IsCoherentCoupleAt p q q' Q LG` for `q ≤ q'` (the case the 0814 gate does not state). -/
theorem couple_row_le_conj {P : WTParams} (hgate : CoherentGateAt P) (hinc : IncoherentGateAt P)
    (hd : 1 ≤ P.d) (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2)
    (hC : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    {p : ℕ} (hp : p < P.D) {R : ℕ → Mom P.d → ℝ} (hR : ∀ r ≤ p, InputRemainder P (R r) r)
    {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4)
    {Q : RegCpl} {LG : LayeredGarden 2} {q q' : ℕ} (hqp : q ≤ p) (hq'p : q' ≤ p) (hqq : q ≤ q')
    (hwf : Q.wf = true) (hsize : Q.size = 2 * n) (hdec : Q.Decodes LG.garden) (hlay : ∀ a, LG.layer a ≤ p)
    (hr0 : LG.layer (GNode.root LG.garden.tree 0) ≤ q) (hr1 : LG.layer (GNode.root LG.garden.tree 1) ≤ q')
    (hcoh : LG.incoherency Q.links = 0 → IsCoherentCoupleAt p q q' Q LG) :
    XNormRestr (6 * P.η ^ 6) (30 * P.d) (30 * P.d) (timeBox q q') Set.univ
      (fun ts k => KQstar P.L P.γ P.δ (inputsF P R) LG (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (rowB P n (LG.incoherency Q.links)) := by
  by_cases hg : LG.incoherency Q.links = 0
  · have h := conjLayered_isConjugateBy LG (Equiv.swap (0 : Fin 2) 1)
    have hr0' : (conjLayered LG (Equiv.swap (0 : Fin 2) 1)).layer
        (GNode.root (conjLayered LG (Equiv.swap (0 : Fin 2) 1)).garden.tree 0) ≤ q' := by
      have hn := PL234.Conj.node_root h 1
      simp only [Equiv.swap_apply_right] at hn
      rw [← hn, PL234.Conj.layer_node h]; exact hr1
    have hr1' : (conjLayered LG (Equiv.swap (0 : Fin 2) 1)).layer
        (GNode.root (conjLayered LG (Equiv.swap (0 : Fin 2) 1)).garden.tree 1) ≤ q := by
      have hn := PL234.Conj.node_root h 0
      simp only [Equiv.swap_apply_left] at hn
      rw [← hn, PL234.Conj.layer_node h]; exact hr0
    have hlay' : ∀ a, (conjLayered LG (Equiv.swap (0 : Fin 2) 1)).layer a ≤ p := by
      intro a
      obtain ⟨a0, rfl⟩ := (PL234.Conj.nodeEquiv h).surjective a
      rw [PL234.Conj.layer_node h]; exact hlay a0
    have key := couple_row_le (q := q') (q' := q) hgate hinc hd hη6 hη2 hC hδ hL hw hp hR hn hq'p hqp
      ((wf_conjCpl Q).trans hwf) ((size_conjCpl Q).trans hsize) (decodes_conj h hdec) hlay' hr0' hr1'
      (fun h0 => by
        rw [incoherency_conj h hdec] at h0
        exact ⟨hqq, isCoherentCoupleAt_conj h (hcoh h0)⟩)
    rw [incoherency_conj h hdec] at key
    rw [XNormRestr_KQstar_conj h]
    exact key
  · exact couple_row_le hgate hinc hd hη6 hη2 hC hδ hL hw hp hR hn hqp hq'p hwf hsize hdec hlay hr0 hr1
      (fun h0 => absurd h0 hg)

/-- **Row bound for a regular couple, both orientations.**  For a coherent couple the orientation of
`(q, q')` is arbitrary. -/
theorem couple_row_le_both {P : WTParams} (hgate : CoherentGateAt P) (hinc : IncoherentGateAt P)
    (hd : 1 ≤ P.d) (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2)
    (hC : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    {p : ℕ} (hp : p < P.D) {R : ℕ → Mom P.d → ℝ} (hR : ∀ r ≤ p, InputRemainder P (R r) r)
    {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4)
    {Q : RegCpl} {LG : LayeredGarden 2} {q q' : ℕ} (hqp : q ≤ p) (hq'p : q' ≤ p)
    (hwf : Q.wf = true) (hsize : Q.size = 2 * n) (hdec : Q.Decodes LG.garden) (hlay : ∀ a, LG.layer a ≤ p)
    (hr0 : LG.layer (GNode.root LG.garden.tree 0) ≤ q) (hr1 : LG.layer (GNode.root LG.garden.tree 1) ≤ q')
    (hcoh : LG.incoherency Q.links = 0 → IsCoherentCoupleAt p q q' Q LG) :
    XNormRestr (6 * P.η ^ 6) (30 * P.d) (30 * P.d) (timeBox q q') Set.univ
      (fun ts k => KQstar P.L P.γ P.δ (inputsF P R) LG (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (rowB P n (LG.incoherency Q.links)) := by
  rcases le_total q' q with hqq | hqq
  · exact couple_row_le hgate hinc hd hη6 hη2 hC hδ hL hw hp hR hn hqp hq'p hwf hsize hdec hlay hr0 hr1
      (fun h0 => ⟨hqq, hcoh h0⟩)
  · exact couple_row_le_conj hgate hinc hd hη6 hη2 hC hδ hL hw hp hR hn hqp hq'p hqq hwf hsize hdec hlay
      hr0 hr1 hcoh

end WaveTurbulence.ConjCoh
