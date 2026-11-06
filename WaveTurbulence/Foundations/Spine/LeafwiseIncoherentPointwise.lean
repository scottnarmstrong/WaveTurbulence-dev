/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafwisePointwise
/-! Pointwise incoherent decay with the product of actual individual leaf costs. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set
open scoped ENNReal

theorem enorm_leafwise_incoherent_le (P : WTParams) (hsource : LeafwiseIncoherentDecayAt P)
    (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη : 0 ≤ P.η)
    {p n q q' : ℕ} (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4)
    (Q : RegCpl) (hwf : Q.wf = true) (hsize : Q.size = 2 * n)
    (LG : LayeredGarden 2) (hQ : Q.Decodes LG.garden) (hlayer : ∀ a, LG.layer a ≤ p)
    (hq : q ≤ p) (hq' : q' ≤ p)
    (hroot : LG.layer (GNode.root LG.garden.tree 0) ≤ q)
    (hroot' : LG.layer (GNode.root LG.garden.tree 1) ≤ q')
    (hi : 1 ≤ LG.incoherency Q.links)
    (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal)
    (hH : LeafwiseControlled LG H B) (t s : ℝ)
    (ht : t ∈ Icc (q : ℝ) (q + 1)) (hs : s ∈ Icc (q' : ℝ) (q' + 1)) (k : Mom P.d) :
    ‖coupleLeaves P.L P.γ P.δ LG H t s k‖ₑ ≤
      regBound P n (LG.incoherency Q.links) * ENNReal.ofReal (leafSizeProduct LG B) := by
  have hX := (hsource p hp n hn).1 Q hwf hsize LG hQ hlayer q q' hq hq' hroot hroot' hi H B hH
  have hK := continuous_coupleLeaves_time P.L P.γ P.δ H LG hQ.1.1 k (hH.summable_coset hd hL k)
  have htime : ![t, s] ∈ closure (interior (timeBox (q : ℝ) q')) := by
    rw [closure_interior_timeBox]
    exact ⟨ht, hs⟩
  have h := (enorm_le_XNormRestr_of_continuous hη (30 * P.d) (30 * P.d)
    (timeBox q q') Set.univ
    (fun ts k => coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k)
    ![t, s] k htime (mem_univ _) hK).trans hX
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using h

end WaveTurbulence.LGSpine
