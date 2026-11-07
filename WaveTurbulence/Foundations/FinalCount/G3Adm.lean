/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3HErase
/-! **FINALCOUNT-G3: admissible decorations of a state** (excessprop1 (1), glue to FINALCOUNT-G2).

`AdmS Adm0 s` is the class of decorations of the dart type of the state `s` that are inherited from an admissible
decoration of `M_sub` (the class `Adm0` of the piece being counted): `k' = k0 ∘ s.down`.  The G2 hypotheses
`hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1)` of the removal operations hold by construction. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} {d : ℕ}

/-- The decorations of `s` inherited from the admissible class `Adm0` of `M_sub`. -/
def AdmS (Adm0 : (D₀ → (Fin d → ℤ)) → Prop) (s : St.{u} V D₀) : (s.D → (Fin d → ℤ)) → Prop :=
  fun k' => ∃ k0, Adm0 k0 ∧ k' = k0 ∘ s.down

theorem AdmS.of_mem {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} {s : St.{u} V D₀} {k0 : D₀ → (Fin d → ℤ)} (h : Adm0 k0) :
    AdmS Adm0 s (k0 ∘ s.down) := ⟨k0, h, rfl⟩

theorem AdmS.cutSt_eq (Adm0 : (D₀ → (Fin d → ℤ)) → Prop) (s : St.{u} V D₀) (v v₂ : V) (x₁ x₂ : s.D) (c₁ c₂ : Cls) :
    AdmS Adm0 (s.cutSt v v₂ x₁ x₂ c₁ c₂) = AdmS Adm0 s := rfl

theorem AdmS.withCls_eq (Adm0 : (D₀ → (Fin d → ℤ)) → Prop) (s : St.{u} V D₀) (c : V → Cls) :
    AdmS Adm0 (s.withCls c) = AdmS Adm0 s := rfl

theorem AdmS.cutSt {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} {s : St.{u} V D₀} (v v₂ : V) (x₁ x₂ : s.D) (c₁ c₂ : Cls)
    {κ : s.D → (Fin d → ℤ)} (h : AdmS Adm0 s κ) : AdmS Adm0 (s.cutSt v v₂ x₁ x₂ c₁ c₂) κ := h

theorem AdmS.delSt {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} {s : St.{u} V D₀} (P : V → Prop) [DecidablePred P]
    (hP : PClosed s.M P) {κ : s.D → (Fin d → ℤ)} (h : AdmS Adm0 s κ) :
    AdmS Adm0 (s.delSt P hP) (fun x => κ x.1) := by
  obtain ⟨k0, hk, rfl⟩ := h
  exact ⟨k0, hk, rfl⟩

theorem AdmS.eraseSt {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} {s : St.{u} V D₀} (v : V)
    {κ : s.D → (Fin d → ℤ)} (h : AdmS Adm0 s κ) :
    AdmS Adm0 (s.eraseSt v) (fun x => κ x.1.1) := by
  obtain ⟨k0, hk, rfl⟩ := h
  exact ⟨k0, hk, rfl⟩

end WaveTurbulence.FinalCountG3
