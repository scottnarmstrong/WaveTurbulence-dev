/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103BetaBridge
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103BetaReindex
import Mathlib.Tactic

/-! # No source beta operation is created by removing all old bridges -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
universe u v
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The source B pruning stage preserves absence of permitted beta splits.
The proof performs actual bond deletions by a strictly decreasing bond count. -/
theorem admitsBetaSplit_before_bridgeCore (M : Molecule V D) (hM : M.IsMolecule) :
    AdmitsBetaSplit (bridgeCore M) → AdmitsBetaSplit M := by
  classical
  have aux : ∀ n : ℕ, ∀ {E : Type v} [Fintype E] [DecidableEq E] (N : Molecule V E),
      N.bonds.card = n → N.IsMolecule → AdmitsBetaSplit (bridgeCore N) → AdmitsBetaSplit N := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro E _ _ N hn hN hbeta
      by_cases hno : ∀ e, ¬ IsBridge N e
      · let f := (bridgeCoreEquivOfNoBridges N hno).symm
        exact admitsBetaSplit_of_dart_equiv N (bridgeCore N) f rfl
          (fun _ => rfl) (fun _ => Subtype.ext rfl) (fun _ => rfl) hbeta
      · push Not at hno
        obtain ⟨e,he⟩ := hno
        have hlt : (eraseBond N e).bonds.card < n := by
          have hh := card_bonds_eraseBond_add_one N e
          omega
        let f := (bridgeCoreEraseEquiv N e he).symm
        have hbeta' : AdmitsBetaSplit (bridgeCore (eraseBond N e)) :=
          admitsBetaSplit_of_dart_equiv (bridgeCore (eraseBond N e)) (bridgeCore N) f rfl
            (fun _ => rfl) (fun _ => Subtype.ext rfl) (fun _ => rfl) hbeta
        have hnext := ih _ hlt (eraseBond N e) rfl (eraseBond_isMolecule N hN e) hbeta'
        exact admitsBetaSplit_before_eraseBond N hN e he hnext
  exact aux _ M rfl hM

end WaveTurbulence.MoleProp
