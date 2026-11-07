/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBTripleFixedThird
import Mathlib.Tactic

/-! # Counting entire reconstructible local tuples with one fixed triple label -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_triple_fixed_tuples_good_bound (d : ℕ) (hd : 2 ≤ d) (δ γ : ℝ)
    (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (M : Molecule V D) (P : AppbPattern) (r : AppbRealization M P),
    ∀ v ∈ r.removedAtoms, ∀ t : AppbTripleFrame r v,
    ∀ (p : AppbCountParameters M d) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
      (z : Fin d → ℤ) (Q : Finset (Fin P.edges.length → (Fin d → ℤ))),
      Q ⊆ r.localChoices p hLp γ δ w Adm → (∀ q ∈ Q,q (t.index 2) = z) →
      Set.InjOn (t.project (K := Fin d → ℤ)) (r.localChoices p hLp γ δ w Adm : Set _) →
      (appbIncidenceSign M v (r.edge (t.index 0)).val ≠ appbIncidenceSign M v (r.edge (t.index 1)).val →
        ∀ κ,κ ∈ p.decorations L γ δ w Adm →
        L^(-γ+2*min γ (1-γ)/3) ≤ ‖Molecule.kvec L w κ (r.edge (t.index 0)).val-
          Molecule.kvec L w κ (r.edge (t.index 1)).val‖) →
      (Q.card : ℝ) ≤ L^((d : ℝ)-γ-31*min γ (1-γ)/48) := by
  classical
  obtain ⟨L₀,hL₀⟩ := appb_triple_fixed_third_good_bound (V := V) (D := D) d hd δ γ hδ hγ
  refine ⟨L₀,?_⟩
  intro L hL hLp M P r v hv t p w Adm z Q hQ hz hi hgap
  have hinj : Set.InjOn (fun q : Fin P.edges.length → (Fin d → ℤ) => (q (t.index 0),q (t.index 1))) (Q : Set _) := by
    intro q hq q' hq' he
    apply hi (hQ hq) (hQ hq')
    funext j
    fin_cases j
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he
    · exact (hz q hq).trans (hz q' hq').symm
  have hb := hL₀ L hL hLp M P r v hv t p w Adm z Q hQ hz hgap
  rw [Finset.card_image_of_injOn hinj] at hb
  exact hb

end WaveTurbulence.Mole
