/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBTripleFrame
public import WaveTurbulence.Foundations.FinalCount.AppBLocalLabelDetermination
public import WaveTurbulence.Foundations.FinalCount.AppBDeletionCounting
import Mathlib.Tactic

/-! # TB-2N: the three internal labels determine the external label -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Set Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def appbFirstThreeEmbedding (n : ℕ) (hn : 3 ≤ n) : Fin 3 ↪ Fin n where
  toFun j := ⟨j.val,lt_of_lt_of_le j.isLt hn⟩
  inj' := by intro i j he; exact Fin.ext (congrArg (fun z : Fin n => z.val) he)

def appbTB2Frame {M : Molecule V D} (r : AppbRealization M AppbPatternKind.tb2.pattern) :
    AppbTripleFrame r (r.vertex 1) where
  index := appbFirstThreeEmbedding _ (by decide)
  incidence := by
    intro j
    rw [r.edge_incidence _ 1 (by decide)]
    fin_cases j <;> decide
  other := by
    intro i hi
    rw [r.edge_incidence i 1 (by decide)]
    fin_cases i
    · exact False.elim (hi 0 rfl)
    · exact False.elim (hi 1 rfl)
    · exact False.elim (hi 2 rfl)
    · decide

/-- TB-2N's external label is reconstructed from the internal triple and
actual momentum at the degree-four atom. -/
theorem appb_tb2_projection_injective {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.tb2.pattern)
    {d : ℕ} (p : AppbCountParameters M d) {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) :
    Set.InjOn ((appbTB2Frame r).project (K := Fin d → ℤ)) (r.localChoices p hL γ δ w Adm : Set _) := by
  intro q hq q' hq' he
  obtain ⟨κ,hκ,rfl⟩ := (r.mem_localChoices p hL γ δ w Adm q).mp hq
  obtain ⟨κ',hκ',rfl⟩ := (r.mem_localChoices p hL γ δ w Adm q').mp hq'
  have h0 := congrFun he (0 : Fin 3)
  have h1 := congrFun he (1 : Fin 3)
  have h2 := congrFun he (2 : Fin 3)
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · apply r.local_label_eq_of_others hL.ne'
      (mem_image_of_mem _ (show 2 ∈ AppbPatternKind.tb2.pattern.removed by decide)) ⟨3,by decide⟩
      (by rw [r.edge_incidence _ 2 (by decide)]; decide) w p.momentum κ κ' hκ.1 hκ'.1
    intro j hj
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact False.elim (hj rfl)

end WaveTurbulence.Mole
