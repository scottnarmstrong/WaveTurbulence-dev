/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.TreeStep

/-!
# Prop 6.1, `q > q'`, trees: the bottom tree factor on a target box

* `mem_closure_interior_timeBoxGt_top`: the top edge `{r+1} × [q'', q''+1]` of `timeBoxGt r q''` (`q'' ≤ r`) lies in
  the closure of its interior; for `q'' = r` the corner `(r+1, r+1)` is a limit of points of the box;
* **`tree_bottom_bounds`**: from the single-layer estimates of a tree with lone layer `q'' ≤ r`, the trace at
  `t = r + 1` (`restr_trace_transport`) bounds the error and the leading term as functions of `s` on any target box
  mapped into the unit box by `ts ↦ ts + (b₀, -q'')`.
-/

@[expose] public section
open WaveTurbulence.Induct

open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

theorem mem_closure_interior_timeBoxGt_top {r q'' : ℕ} (hq : q'' ≤ r) {x : ℝ}
    (hx : x ∈ Icc (q'' : ℝ) (q'' + 1)) :
    (![(r : ℝ) + 1, x] : Fin 2 → ℝ) ∈ closure (interior (timeBoxGt (r : ℝ) q'')) := by
  have hg : Continuous fun y : ℝ => (![(r : ℝ) + 1, y] : Fin 2 → ℝ) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact continuous_const
    · exact continuous_id
  have hcl : IsClosed ((fun y : ℝ => (![(r : ℝ) + 1, y] : Fin 2 → ℝ)) ⁻¹'
      closure (interior (timeBoxGt (r : ℝ) q''))) := isClosed_closure.preimage hg
  have hqr : (q'' : ℝ) ≤ r := by exact_mod_cast hq
  have hsub : Ico (q'' : ℝ) (q'' + 1) ⊆ (fun y : ℝ => (![(r : ℝ) + 1, y] : Fin 2 → ℝ)) ⁻¹'
      closure (interior (timeBoxGt (r : ℝ) q'')) := by
    intro y hy
    apply mem_closure_interior_timeBoxGt
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [Matrix.cons_val_zero]
      constructor <;> linarith
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      exact ⟨hy.1, hy.2.le⟩
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      linarith [hy.2]
  have h := hcl.closure_subset_iff.mpr hsub
  rw [closure_Ico (ne_of_lt (lt_add_one _))] at h
  exact h hx

theorem trace_line_tree_bot {r q'' : ℕ} (hq : q'' ≤ r) (u : Fin 2 → ℝ)
    (hu : u ∈ (Layered.unitBox : Set (Fin 2 → ℝ))) :
    Function.update u 0 1 + ![(r : ℝ), q''] ∈ closure (interior (timeBoxGt (r : ℝ) q'')) := by
  have h1 := hu 1
  have e : Function.update u 0 1 + ![(r : ℝ), q''] = ![(r : ℝ) + 1, u 1 + q''] := by
    funext i
    fin_cases i
    · simp [Function.update]
      try ring
    · simp [Function.update]
  rw [e]
  apply mem_closure_interior_timeBoxGt_top hq
  constructor <;> linarith [h1.1, h1.2]

section TreeBottom

variable (P : WTParams) {r q'' n : ℕ} (X : RegChain) (LG : LayeredGarden 1) (H : LeafProfiles 1 P.d)

end TreeBottom

end WaveTurbulence.PL234
