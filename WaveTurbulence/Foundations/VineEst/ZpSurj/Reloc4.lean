/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Reloc3

/-! # ZP-SURJ: the relocation map and the pairs of a relocated code -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ZpSurj
open TTree WaveTurbulence.Reg WaveTurbulence.Links

variable {w w' : ℕ}

/-- The two-root relocation map. -/
@[expose] noncomputable def relocMap (a₁ b₁ : Fin w × Path) (a₂ b₂ : Fin w' × Path) (z : Fin w × Path) :
    Fin w' × Path := by
  classical
  exact if Under a₁ z then shiftTo a₁ a₂ z else shiftTo b₁ b₂ z

theorem under_b_not_a {a₁ b₁ : Fin w × Path} (hab : Indep a₁ b₁) {x : Fin w × Path} (hx : Under b₁ x) :
    ¬ Under a₁ x := fun hxa => by
  rcases under_total hxa hx with h | h
  · exact hab.1 h
  · exact hab.2 h

theorem relocMap_P {a₁ b₁ : Fin w × Path} (x : Fin w × Path) (q : Path) (hx : Under a₁ x ∨ Under b₁ x) :
    Under a₁ (addrExt x q) ∨ Under b₁ (addrExt x q) :=
  hx.imp (fun h => under_trans h (under_ext x q)) (fun h => under_trans h (under_ext x q))

theorem relocMap_ext {a₁ b₁ : Fin w × Path} (hab : Indep a₁ b₁) (a₂ b₂ : Fin w' × Path) (x : Fin w × Path)
    (q : Path) (hx : Under a₁ x ∨ Under b₁ x) :
    relocMap a₁ b₁ a₂ b₂ (addrExt x q) = addrExt (relocMap a₁ b₁ a₂ b₂ x) q := by
  classical
  rcases hx with hx | hx
  · have h2 : Under a₁ (addrExt x q) := under_trans hx (under_ext x q)
    simp only [relocMap, if_pos hx, if_pos h2]
    exact shiftTo_addrExt a₂ hx q
  · have h1 : ¬ Under a₁ x := under_b_not_a hab hx
    have h2 : ¬ Under a₁ (addrExt x q) := under_b_not_a hab (under_trans hx (under_ext x q))
    simp only [relocMap, if_neg h1, if_neg h2]
    exact shiftTo_addrExt b₂ hx q

theorem relocMap_a {a₁ b₁ : Fin w × Path} (a₂ b₂ : Fin w' × Path) (r : Path) :
    relocMap a₁ b₁ a₂ b₂ (addrExt a₁ r) = addrExt a₂ r := by
  classical
  simp only [relocMap, if_pos (under_ext a₁ r)]
  exact shiftTo_addrExt_self a₁ a₂ r

theorem relocMap_b {a₁ b₁ : Fin w × Path} (hab : Indep a₁ b₁) (a₂ b₂ : Fin w' × Path) (r : Path) :
    relocMap a₁ b₁ a₂ b₂ (addrExt b₁ r) = addrExt b₂ r := by
  classical
  simp only [relocMap, if_neg (under_b_not_a hab (under_ext b₁ r))]
  exact shiftTo_addrExt_self b₁ b₂ r

theorem pairsAt_reloc {a₁ b₁ : Fin w × Path} (hab : Indep a₁ b₁) (a₂ b₂ : Fin w' × Path) (Q : RegCpl) :
    Q.pairsAt a₂ b₂ = (Q.pairsAt a₁ b₁).map
      (fun l => (relocMap a₁ b₁ a₂ b₂ l.1, relocMap a₁ b₁ a₂ b₂ l.2)) := by
  have e1 : relocMap a₁ b₁ a₂ b₂ a₁ = a₂ := by
    have := relocMap_a (a₁ := a₁) (b₁ := b₁) a₂ b₂ []
    simpa [addrExt_nil] using this
  have e2 : relocMap a₁ b₁ a₂ b₂ b₁ = b₂ := by
    have := relocMap_b hab a₂ b₂ []
    simpa [addrExt_nil] using this
  have := cpl_pairs_map (fun z => Under a₁ z ∨ Under b₁ z) (relocMap a₁ b₁ a₂ b₂)
    (fun x q hx => relocMap_P x q hx) (fun x q hx => relocMap_ext hab a₂ b₂ x q hx) Q a₁ b₁
    (Or.inl (under_refl _)) (Or.inr (under_refl _))
  rwa [e1, e2] at this

end WaveTurbulence.ZpSurj
