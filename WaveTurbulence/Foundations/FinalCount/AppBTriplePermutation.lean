/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBTripleOrdering
import Mathlib.Tactic

/-! # Exact permutation into the signed triple profile -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole

/-- The reordering is a genuine permutation, so no local labels or
multiplicity factors are discarded by choosing the two equal signs. -/
theorem appb_three_sign_permutation (σ : Fin 3 → ℤˣ)
    (hplus : ¬∀ i,σ i = 1) (hminus : ¬∀ i,σ i = -1) :
    ∃ π : Equiv.Perm (Fin 3),σ (π 0) = σ (π 2) ∧ σ (π 0) ≠ σ (π 1) := by
  obtain ⟨i,j,k,hij,hik,hjk,hs,ho⟩ := appb_three_sign_order σ hplus hminus
  let f : Fin 3 → Fin 3 := ![i,j,k]
  have hf : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [f]
  let π : Equiv.Perm (Fin 3) := Equiv.ofBijective f ⟨hf,Finite.surjective_of_injective hf⟩
  exact ⟨π,hs,ho⟩

/-- Ordered triple encoding is injective for every permutation. -/
theorem appb_triple_permutation_encoding_injective {K : Type*} (π : Equiv.Perm (Fin 3)) :
    Function.Injective (fun q : Fin 3 → K => (q (π 0),q (π 1),q (π 2))) := by
  intro q q' he
  funext j
  obtain ⟨i,rfl⟩ := π.surjective j
  fin_cases i
  · exact congrArg Prod.fst he
  · exact congrArg (fun p => p.2.1) he
  · exact congrArg (fun p => p.2.2) he

end WaveTurbulence.Mole
