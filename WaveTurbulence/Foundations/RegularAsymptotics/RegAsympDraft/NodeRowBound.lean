/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.NodeValueBound

/-! # Linear-in-order bounds on the actual integer coordinate rows -/

public section
namespace WaveTurbulence.RegAsymp
open Links

/-- Testing on a basis decoration bounds every actual node-row entry.
The bound is linear in the source order, even before well-formedness. -/
theorem norm_sourceNodeRow_le {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G)
    (a : GNode G.tree) (c : LinkCoord Q) :
    ‖sourceNodeRow hQ a c‖ ≤ 1+(Q.size:ℝ) := by
  let t : Fin Q.links.length → ℤ × ℤ := fun j =>
    (Incoh.momentumUnitRow c (some (j,0)),Incoh.momentumUnitRow c (some (j,1)))
  have hunit (z : LinkCoord Q) : ‖Incoh.momentumUnitRow c z‖ ≤ (1:ℝ) := by
    unfold Incoh.momentumUnitRow
    split <;> norm_num
  have ht (j : Fin Q.links.length) : ‖(t j).1‖ ≤ (1:ℝ) ∧ ‖(t j).2‖ ≤ (1:ℝ) :=
    ⟨hunit _,hunit _⟩
  have hpar (z : Fin 2 × TTree.Path) :
      ‖(paramFun Q t z).1‖ ≤ (1:ℝ) ∧ ‖(paramFun Q t z).2‖ ≤ (1:ℝ) := by
    unfold paramFun
    split
    · exact ht _
    · simp
  have hh := norm_cplVal_le (paramFun Q t) 1 zero_le_one hpar Q (0,[]) (1,[])
    (Incoh.momentumUnitRow c none) a.val
  change ‖cplVal (paramFun Q t) Q (0,[]) (1,[]) (Incoh.momentumUnitRow c none) a.val‖ ≤ _
  exact hh.trans (by simpa only [mul_one] using add_le_add (hunit none) (le_refl (Q.size:ℝ)))

end WaveTurbulence.RegAsymp
