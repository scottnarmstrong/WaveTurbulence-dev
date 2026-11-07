/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepConj1
public import WaveTurbulence.Foundations.Stage1.Represents.RepConj2
public import WaveTurbulence.Foundations.VineEst.ConjCoherent
public import WaveTurbulence.Foundations.Spine.LeafwiseAt
public import WaveTurbulence.Foundations.Spine.LeafwiseSpineInputs
import Mathlib.Tactic

/-!
# S2 REPRESENTS: the coherent couple gate for `q < q'` (finding F-CONJ, TARGET L899 "by symmetry")

`LeafwiseCoherentApproximationAt` states the couple gate for `q' ≤ q`.  For `q < q'` the conjugate couple
(`conjCpl Q`, conjugate garden, conjugate profile) is coherent at `(p, q', q)`, the leafwise kernel of the
conjugate garden is the conjugate kernel with the times exchanged (`coupleLeaves_conj`), and `XNormRestr`,
`XNorm00Restr` are invariant under swap-and-conjugate.  The approximation of the `q < q'` kernel is therefore
the swap-conjugate of the conjugate couple's approximation.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct

namespace WaveTurbulence.Represents

open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.ConjCoh WaveTurbulence.PL234 Set
open scoped ENNReal ComplexConjugate

theorem timeBox_permT' (q q' : ℝ) :
    permT (Equiv.swap (0 : Fin 2) 1) ⁻¹' timeBox q q' = timeBox q' q := by
  ext ts
  simp [timeBox, permT, and_comm]

theorem swap_invol' : ∀ i : Fin 2, (Equiv.swap (0 : Fin 2) 1) ((Equiv.swap (0 : Fin 2) 1) i) = i :=
  fun i => by simp

/-- The coherent couple gate for `q < q'`, with an approximation `f` in place of `LeafApp.coherentCouple`
(the swap-conjugate of the conjugate couple's approximation). -/
def CoupleCohSwap (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 →
    ∀ (Q : RegCpl) (LG : LayeredGarden 2) (q q' : ℕ), q < q' → q' ≤ p → Q.size = 2 * n →
      IsCoherentCoupleAt p q q' Q LG →
      ∀ (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal), LeafwiseControlled LG H B →
      ∃ f : (Fin 2 → ℝ) → Mom P.d → ℂ,
      XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox (q : ℝ) q') Set.univ
        (fun ts k => coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k - f ts k) ≤
        regBound P n 1 * ENNReal.ofReal (leafSizeProduct LG B) ∧
      LeafwiseSeparated P n (30 * P.d) (timeBox (q : ℝ) q') f (leafSizeProduct LG B)

theorem coupleCohSwap_of_gate (P : WTParams) (hcoh : LeafwiseCoherentApproximationAt P) :
    CoupleCohSwap P := by
  intro p hp n hn Q LG q q' hqq hq'p hsz hQc H B hctrl
  set LGb : LayeredGarden 2 := conjLayered LG (Equiv.swap (0 : Fin 2) 1) with hLGb
  have h : IsConjugateCouple LG LGb := conjLayered_isConjugateCouple LG
  have hQb : IsCoherentCoupleAt p q' q (conjCpl Q) LGb := isCoherentCoupleAt_conj h hQc
  have hctrlb := leafwiseControlled_conj h hctrl
  obtain ⟨hXe, -, hsep⟩ := (hcoh p hp n hn).1 (conjCpl Q) LGb q' q hqq.le hq'p
    (by rw [size_conjCpl]; exact hsz) hQb (transferProf h H) (transferProf h B) hctrlb
  rw [leafSizeProduct_conj h] at hXe hsep
  obtain ⟨m, J, M, hm, hrep, hJ, hM⟩ := hsep
  set app : (Fin 2 → ℝ) → Mom P.d → ℂ := fun ts k =>
    LeafApp.coherentCouple P.δ LGb (transferProf h H) (conjCpl Q) q' q (ts 0) (ts 1) k with happ
  refine ⟨fun ts k => conj (app (permT (Equiv.swap (0 : Fin 2) 1) ts) k), ?_, ?_⟩
  · have hf : (fun (ts : Fin 2 → ℝ) (k : Mom P.d) => coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
        conj (app (permT (Equiv.swap (0 : Fin 2) 1) ts) k)) =
        swapConj (Equiv.swap (0 : Fin 2) 1) (fun ts k =>
          coupleLeaves P.L P.γ P.δ LGb (transferProf h H) (ts 0) (ts 1) k - app ts k) := by
      funext ts k
      have := coupleLeaves_conj h P.L P.γ P.δ H (ts 0) (ts 1) k
      simp only [swapConj, permT, map_sub, ← happ]
      have e0 : (Equiv.swap (0 : Fin 2) 1) 0 = 1 := by simp
      have e1 : (Equiv.swap (0 : Fin 2) 1) 1 = 0 := by simp
      simp only [e0, e1] at this ⊢
      rw [this, Complex.conj_conj]
    rw [hf, XNormRestr_swapConj swap_invol', timeBox_permT']
    exact hXe
  · refine ⟨m, fun i ts => conj (J i (permT (Equiv.swap (0 : Fin 2) 1) ts)), M, hm, ?_, ?_, hM⟩
    · intro ts hts k
      have hts' : permT (Equiv.swap (0 : Fin 2) 1) ts ∈ timeBox (q' : ℝ) q := by
        have := timeBox_permT' (q' : ℝ) q
        rw [← this] at hts
        exact hts
      have this : app (permT (Equiv.swap (0 : Fin 2) 1) ts) k =
          ∑ i, (P.δ : ℂ) ^ n * J i (permT (Equiv.swap (0 : Fin 2) 1) ts) * (M i k : ℂ) := hrep _ hts' k
      show conj (app (permT (Equiv.swap (0 : Fin 2) 1) ts) k) = _
      rw [this, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [map_mul, Complex.conj_ofReal]
    · intro i
      have h1 : (fun (ts : Fin 2 → ℝ) (_ : Unit) => conj (J i (permT (Equiv.swap (0 : Fin 2) 1) ts))) =
          swapConjV (Equiv.swap (0 : Fin 2) 1) (fun ts (_ : Unit) => J i ts) := rfl
      rw [h1, XNorm00Restr_swapConjV swap_invol', timeBox_permT']
      exact hJ i

end WaveTurbulence.Represents
