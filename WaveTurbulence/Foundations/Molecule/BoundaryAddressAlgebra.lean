/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistExcludedSubtree

/-! # Address algebra for the retained splice boundary subtrees -/

public section
namespace WaveTurbulence.Twist
open TTree

/-- Extend an actual forest address by a relative subtree address. -/
@[expose] def appendAddress {w : ℕ} (a : Fin w × Path) (p : Path) : Fin w × Path := (a.1,a.2 ++ p)

/-- A prefix entering a subtree is comparable with its root prefix. -/
theorem prefix_append_comparable {a b p : Path} (h : a <+: b ++ p) : a <+: b ∨ b <+: a :=
  List.prefix_or_prefix_of_prefix h (List.prefix_append b p)

/-- Addresses below a subtree incomparable with both exchange sites are fixed. -/
theorem exchangeAddress_append_fixed {w : ℕ} (h₀ h₁ z : Fin w × Path) (keep : Fin 3) (p : Path)
    (h₀z : h₀.1 = z.1 → ¬ h₀.2 <+: z.2 ∧ ¬ z.2 <+: h₀.2)
    (h₁z : h₁.1 = z.1 → ¬ h₁.2 <+: z.2 ∧ ¬ z.2 <+: h₁.2) :
    exchangeAddress h₀ h₁ keep (appendAddress z p) = appendAddress z p := by
  have hn : ¬ (z.1 = h₀.1 ∧ h₀.2 <+: z.2 ++ p) := by
    rintro ⟨hi,hp⟩
    rcases prefix_append_comparable hp with h | h
    · exact (h₀z hi.symm).1 h
    · exact (h₀z hi.symm).2 h
  have he : appendAddress z p ≠ h₁ := by
    intro he
    have hi := congrArg Prod.fst he
    have hp : z.2 <+: h₁.2 := ⟨p,congrArg Prod.snd he⟩
    exact (h₁z hi.symm).2 hp
  exact ite_eq_right hn |>.trans (ite_eq_right he)

/-- Extending a lower child address moves its whole ordered subtree without changing its tail. -/
theorem exchangeAddress_lower_child {w : ℕ} (h₀ h₁ : Fin w × Path) (keep i : Fin 3) (p : Path) :
    exchangeAddress h₀ h₁ keep (appendAddress (h₀.1,h₀.2 ++ [i]) p) =
      appendAddress (h₁.1,h₁.2 ++ [freeSwap keep i]) p := by
  simp [exchangeAddress,appendAddress,List.append_assoc,switchPath]

end WaveTurbulence.Twist
