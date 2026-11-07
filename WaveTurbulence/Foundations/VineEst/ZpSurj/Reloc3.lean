/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Reloc2

/-! # ZP-SURJ: relocation of a layer pattern from roots `(a₁, b₁)` to roots `(a₂, b₂)` -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ZpSurj
open TTree WaveTurbulence.Reg WaveTurbulence.Links

variable {w w' : ℕ}

/-- Rebase an address below `a₁` to the corresponding address below `a₂`. -/
@[expose] def shiftTo (a₁ : Fin w × Path) (a₂ : Fin w' × Path) (z : Fin w × Path) : Fin w' × Path :=
  (a₂.1, a₂.2 ++ z.2.drop a₁.2.length)

theorem shiftTo_addrExt {a₁ : Fin w × Path} (a₂ : Fin w' × Path) {x : Fin w × Path} (hx : Under a₁ x) (q : Path) :
    shiftTo a₁ a₂ (addrExt x q) = addrExt (shiftTo a₁ a₂ x) q := by
  obtain ⟨h1, r, hr⟩ := hx
  simp only [shiftTo, addrExt, ← hr, List.drop_left, List.append_assoc, Prod.mk.injEq, true_and]

theorem shiftTo_self (a₁ : Fin w × Path) (a₂ : Fin w' × Path) : shiftTo a₁ a₂ a₁ = a₂ := by
  simp [shiftTo]

theorem shiftTo_addrExt_self (a₁ : Fin w × Path) (a₂ : Fin w' × Path) (r : Path) :
    shiftTo a₁ a₂ (addrExt a₁ r) = addrExt a₂ r := by
  simp [shiftTo, addrExt]

/-- One-root relocation: the layers below `a₂` are those below `a₁`. -/
theorem treePatternN_reloc {H1 : LayeredGarden w} {H2 : LayeredGarden w'} (pa : ℕ) (X : RegChain) (ζ : ℤˣ)
    (a₁ : Fin w × Path) (a₂ : Fin w' × Path)
    (hlay : ∀ r, layerAt H2 (addrExt a₂ r) = layerAt H1 (addrExt a₁ r)) :
    TreePatternN H2 pa X ζ a₂ ↔ TreePatternN H1 pa X ζ a₁ := by
  have := treePatternN_map (fun z => Under a₁ z) (shiftTo a₁ a₂)
    (fun x q hx => under_trans hx (under_ext x q)) (fun x q hx => shiftTo_addrExt a₂ hx q)
    (H1 := H1) (H2 := H2) (fun z hz => by
      obtain ⟨r, rfl⟩ := under_of_addrExt hz
      rw [shiftTo_addrExt_self]; exact hlay r) pa X ζ a₁ (under_refl _)
  rwa [shiftTo_self] at this

/-- Two-root relocation. -/
theorem layerPatternN_reloc {H1 : LayeredGarden w} {H2 : LayeredGarden w'} (pa pb : ℕ) (Q : RegCpl)
    (a₁ b₁ : Fin w × Path) (hab : Indep a₁ b₁) (a₂ b₂ : Fin w' × Path)
    (hlayA : ∀ r, layerAt H2 (addrExt a₂ r) = layerAt H1 (addrExt a₁ r))
    (hlayB : ∀ r, layerAt H2 (addrExt b₂ r) = layerAt H1 (addrExt b₁ r)) :
    LayerPatternN H2 pa pb Q a₂ b₂ ↔ LayerPatternN H1 pa pb Q a₁ b₁ := by
  classical
  let ρ : Fin w × Path → Fin w' × Path := fun z => if Under a₁ z then shiftTo a₁ a₂ z else shiftTo b₁ b₂ z
  have hbA : ∀ x, Under b₁ x → ¬ Under a₁ x := fun x hx hxa => by
    rcases under_total hxa hx with h | h
    · exact hab.1 h
    · exact hab.2 h
  have hP : ∀ x q, (Under a₁ x ∨ Under b₁ x) → (Under a₁ (addrExt x q) ∨ Under b₁ (addrExt x q)) := fun x q hx =>
    hx.imp (fun h => under_trans h (under_ext x q)) (fun h => under_trans h (under_ext x q))
  have hρ : ∀ x q, (Under a₁ x ∨ Under b₁ x) → ρ (addrExt x q) = addrExt (ρ x) q := by
    intro x q hx
    rcases hx with hx | hx
    · have h2 : Under a₁ (addrExt x q) := under_trans hx (under_ext x q)
      simp only [ρ, if_pos hx, if_pos h2]
      exact shiftTo_addrExt a₂ hx q
    · have h1 : ¬ Under a₁ x := hbA x hx
      have h2 : ¬ Under a₁ (addrExt x q) := hbA _ (under_trans hx (under_ext x q))
      simp only [ρ, if_neg h1, if_neg h2]
      exact shiftTo_addrExt b₂ hx q
  have e1 : ρ a₁ = a₂ := by simp [ρ, under_refl, shiftTo_self]
  have e2 : ρ b₁ = b₂ := by
    simp only [ρ, if_neg (fun h => hab.1 h), shiftTo_self]
  have := layerPatternN_map (fun z => Under a₁ z ∨ Under b₁ z) ρ hP hρ (H1 := H1) (H2 := H2) (fun z hz => by
      rcases hz with hz | hz
      · obtain ⟨r, rfl⟩ := under_of_addrExt hz
        simp only [ρ, if_pos hz]
        rw [shiftTo_addrExt_self]; exact hlayA r
      · obtain ⟨r, rfl⟩ := under_of_addrExt hz
        simp only [ρ, if_neg (hbA _ hz)]
        rw [shiftTo_addrExt_self]; exact hlayB r) pa pb Q a₁ b₁ (Or.inl (under_refl _)) (Or.inr (under_refl _))
  rwa [e1, e2] at this

end WaveTurbulence.ZpSurj
