/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.UnitTwistInvolution

/-! # The uniform twist address map on ordinary parent-child edges

TARGET twistexplain (a): all ordinary PC edges retain their endpoints;
only the lower PC edge is exchanged with its retained LP edge.
-/

public section
namespace WaveTurbulence.Twist
open TTree

/-- A prefix ending at a child is a prefix of its parent or is that whole child address. -/
theorem prefix_child_cases {a p : Path} {i : Fin 3} (h : a <+: p ++ [i]) : a <+: p ∨ a = p ++ [i] := by
  by_cases hl : a.length ≤ p.length
  · exact Or.inl (List.prefix_of_prefix_length_le h (List.prefix_append p [i]) hl)
  · apply Or.inr
    apply h.eq_of_length
    have hh := h.length_le
    simp only [List.length_append,List.length_singleton] at hh ⊢
    omega

/-- A child slot changes only at the lower root. -/
@[expose] def exchangeChildSlot {w : ℕ} (h₀ : Fin w × Path) (keep : Fin 3)
    (p : Fin w × Path) (i : Fin 3) : Fin 3 := if p = h₀ then freeSwap keep i else i

/-- Transport an ordinary parent-child edge through the concrete address map. -/
theorem exchangeAddress_child {w : ℕ} (h₀ h₁ p : Fin w × Path) (keep i : Fin 3)
    (hp : p ≠ h₁) (hc₀ : (p.1,p.2 ++ [i]) ≠ h₀) (hc₁ : (p.1,p.2 ++ [i]) ≠ h₁) :
    exchangeAddress h₀ h₁ keep (p.1,p.2 ++ [i]) =
      ((exchangeAddress h₀ h₁ keep p).1,
        (exchangeAddress h₀ h₁ keep p).2 ++ [exchangeChildSlot h₀ keep p i]) := by
  by_cases hi : p.1 = h₀.1
  · by_cases hpre : h₀.2 <+: p.2
    · obtain ⟨q,hq⟩ := hpre
      have hpval : p = (h₀.1,h₀.2 ++ q) := Prod.ext hi hq.symm
      rw [hpval]
      cases q with
      | nil => simp [exchangeAddress,exchangeChildSlot,switchPath]
      | cons j q =>
        have hn : (h₀.1,h₀.2 ++ j::q) ≠ h₀ := by
          intro he
          have hh := congrArg (fun a : Fin w × Path => a.2.length) he
          simp only [List.length_append,List.length_cons] at hh
          omega
        simp [exchangeAddress,exchangeChildSlot,hn,List.append_assoc,switchPath]
    · have hcpre : ¬ h₀.2 <+: p.2 ++ [i] := by
        intro h
        rcases prefix_child_cases h with h | h
        · exact hpre h
        · exact hc₀ (Prod.ext hi h.symm)
      have hp₀ : p ≠ h₀ := by
        intro he
        apply hpre
        rw [he]
      have hc₁' : (h₀.1,p.2 ++ [i]) ≠ h₁ := by simpa only [hi] using hc₁
      simp [exchangeAddress,hi,hpre,hcpre,hp,hc₁',exchangeChildSlot,hp₀]
  · have hp₀ : p ≠ h₀ := fun he => hi (congrArg Prod.fst he)
    simp [exchangeAddress,hi,hp,hc₁,exchangeChildSlot,hp₀]

end WaveTurbulence.Twist
