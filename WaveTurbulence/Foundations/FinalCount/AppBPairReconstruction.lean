/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBPairDetermination
public import WaveTurbulence.Foundations.FinalCount.AppBDeletionCounting
import Mathlib.Tactic

/-! # Reconstructing short degree-two chains from two retained local labels -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset Set
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

/-- A finite incidence reconstruction certificate for 2R-3F. Every extra
bond is paired at a deleted degree-two atom with one of the two central
bonds. All certificate premises concern the input graph only. -/
theorem pair_projection_injOn_localChoices {v : V} (central : AppbLocalPair r v)
    {n : ℕ} (leaves : Fin n → Σ a : V,AppbLocalPair r a)
    (hremoved : ∀ j,(leaves j).1 ∈ r.removedAtoms)
    (hfirst : ∀ j,(leaves j).2.first = central.first ∨ (leaves j).2.first = central.second)
    (hcover : ∀ i : Fin P.edges.length,
      i = central.first ∨ i = central.second ∨ ∃ j : Fin n,i = (leaves j).2.second)
    {d : ℕ} (p : AppbCountParameters M d) {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) :
    Set.InjOn (central.project (K := Fin d → ℤ)) (r.localChoices p hL γ δ w Adm : Set _) := by
  intro q hq q' hq' he
  obtain ⟨κ,hκ,rfl⟩ := (r.mem_localChoices p hL γ δ w Adm q).mp hq
  obtain ⟨κ',hκ',rfl⟩ := (r.mem_localChoices p hL γ δ w Adm q').mp hq'
  have h0 := congrArg Prod.fst he
  have h1 := congrArg Prod.snd he
  simp only [AppbLocalPair.project] at h0 h1
  funext i
  rcases hcover i with hi | hi | ⟨j,hi⟩
  · simpa only [hi] using h0
  · simpa only [hi] using h1
  · rw [hi]
    apply (leaves j).2.second_label_eq hL.ne' (hremoved j) w p.momentum κ κ' hκ.1 hκ'.1
    rcases hfirst j with hj | hj
    · simpa only [hj] using h0
    · simpa only [hj] using h1

end AppbRealization
end WaveTurbulence.Mole
