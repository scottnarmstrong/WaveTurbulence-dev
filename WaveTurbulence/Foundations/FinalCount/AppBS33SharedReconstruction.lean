/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBS33SharedCut
public import WaveTurbulence.Foundations.FinalCount.AppBLocalLabelDetermination
import Mathlib.Tactic

/-! # Reconstruction from a triple in the common-neighbour split figures -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def appbS33SharedFrame {M : Molecule V D} (k : AppbPatternKind) (hk : k ∈ appbS33SharedKinds)
    (r : AppbRealization M k.pattern) : AppbTripleFrame r (r.vertex 1) :=
  appbFiveFirst r (appb_s33_kind_length k (appb_s33_shared_mem k hk)) _
    (appb_s33_first_incidence k (appb_s33_shared_mem k hk) r)

theorem appb_s33_shared_projection_injective {M : Molecule V D} (k : AppbPatternKind) (hk : k ∈ appbS33SharedKinds)
    (r : AppbRealization M k.pattern)
    (hside : ∀ a ∈ k.pattern.vertices,r.vertex a ∈ Degen.residualComponent M r.removedAtoms (r.vertex 3) ↔ a = 3)
    {d : ℕ} (p : AppbCountParameters M d) {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) :
    Set.InjOn ((appbS33SharedFrame k hk r).project (K := Fin d → ℤ)) (r.localChoices p hL γ δ w Adm : Set _) := by
  intro q hq q' hq' he
  obtain ⟨κ,hκ,rfl⟩ := (r.mem_localChoices p hL γ δ w Adm q).mp hq
  obtain ⟨κ',hκ',rfl⟩ := (r.mem_localChoices p hL γ δ w Adm q').mp hq'
  have h0 := congrFun he (0 : Fin 3)
  have h1 := congrFun he (1 : Fin 3)
  have h2 := congrFun he (2 : Fin 3)
  have h3 := (appbS33SharedCutPair k hk r hside).second_label_eq hL.ne' w p.momentum κ κ' hκ.1 hκ'.1 h1
  have ht : ∀ k ∈ appbS33SharedKinds,2 ∈ k.pattern.removed := by decide
  have hv := mem_image_of_mem r.vertex (ht k hk)
  funext i
  obtain ⟨j,rfl⟩ := (finCongr (appb_s33_kind_length k (appb_s33_shared_mem k hk)).symm).surjective i
  fin_cases j
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · apply r.local_label_eq_of_others hL.ne' hv
      (appbFiveEmbedding (appb_s33_kind_length k (appb_s33_shared_mem k hk)) 4)
      (by
        have hh := (appb_s33_second_incidence k (appb_s33_shared_mem k hk) r 4)
        exact hh) w p.momentum κ κ' hκ.1 hκ'.1
    intro i hi
    obtain ⟨j,rfl⟩ := (finCongr (appb_s33_kind_length k (appb_s33_shared_mem k hk)).symm).surjective i
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact False.elim (hi rfl)

end WaveTurbulence.Mole
