/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Range
public import WaveTurbulence.Foundations.FinalCount.G3HInv
/-! **FINALCOUNT-G3: the dart-set invariant `DPInv`.**  Every atom `j` carrying a cut record `(p, _)` has, as set of
`M_sub`-darts, either exactly the recorded pair `{p.1, p.2}` (the half that kept the two cut darts) or a set disjoint from it
(the half that received the other darts).  This is the model fact behind "a hinge is cut along its designated bonds":
a joint half holds both designated darts or neither. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}

/-- The `M_sub`-darts at the atom `j` of the state `s`. -/
def DSet (s : St.{u} V D₀) (j : V) : Set D₀ := {z | ∃ x : s.D, s.M.atom x = j ∧ s.down x = z}

/-- `S` is the recorded pair or disjoint from it. -/
def DPOk (S : Set D₀) (p : D₀ × D₀) : Prop := S = {p.1, p.2} ∨ Disjoint S {p.1, p.2}

/-- The dart-set invariant. -/
structure DPInv (h : HSt V D₀) : Prop where
  ok : ∀ j ∈ h.s.M.atoms, ∀ p vis, h.crec j = some (p, vis) → DPOk (DSet h.s j) p

theorem DPInv.init (M₀ : Molecule V D₀) : DPInv (HSt.init M₀) where
  ok := fun j _ p vis h => by simp [HSt.init] at h

theorem DPInv.cut_gen {h : HSt V D₀} (hI : DPInv h) (hinj : Function.Injective h.s.down) {v v₂ : V} {x₁ x₂ : h.s.D}
    (hc : h.s.M.IsCutData v v₂ x₁ x₂) (c₁ c₂ : Cls) (nh : List (D₀ × D₀)) {na : V → V}
    (r₁ r₂ : Option ((D₀ × D₀) × List (D₀ × D₀)))
    (s1 : ∀ p vis, r₁ = some (p, vis) → p = h.s.pr x₁ x₂)
    (s2 : ∀ p vis, r₂ = some (p, vis) → p = h.s.pr x₁ x₂) :
    DPInv ⟨h.s.cutSt v v₂ x₁ x₂ c₁ c₂, nh, Function.update (Function.update h.crec v r₁) v₂ r₂, na⟩ where
  ok := by
    intro j hj p vis hp
    simp only at hj hp ⊢
    have hv : v ∈ h.s.M.atoms := hc.1
    have hv₂ : v₂ ∉ h.s.M.atoms := hc.2.1
    have hne : v₂ ≠ v := fun e => hv₂ (e ▸ hv)
    have hat : ∀ x : h.s.D, (h.s.cutSt v v₂ x₁ x₂ c₁ c₂).M.atom x =
        if h.s.M.atom x = v ∧ x ≠ x₁ ∧ x ≠ x₂ then v₂ else h.s.M.atom x := fun x => rfl
    by_cases e2 : j = v₂
    · subst e2
      rw [Function.update_self] at hp
      have hpp := s2 p vis hp
      subst hpp
      right
      rw [Set.disjoint_left]
      rintro z ⟨x, hx, rfl⟩ hz
      rw [hat x] at hx
      split_ifs at hx with hcond
      · simp only [St.pr, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with hz | hz
        · exact hcond.2.1 (hinj hz)
        · exact hcond.2.2 (hinj hz)
      · exact hv₂ (hx ▸ h.s.M.atom_mem x)
    · rw [Function.update_of_ne e2] at hp
      by_cases e1 : j = v
      · subst e1
        rw [Function.update_self] at hp
        have hpp := s1 p vis hp
        subst hpp
        left
        ext z
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, St.pr]
        constructor
        · rintro ⟨x, hx, rfl⟩
          rw [hat x] at hx
          split_ifs at hx with hcond
          · exact absurd hx hne
          · by_cases hx1 : x = x₁
            · exact Or.inl (by rw [hx1]; rfl)
            · have hx2 : x = x₂ := by
                by_contra hx2
                exact hcond ⟨hx, hx1, hx2⟩
              exact Or.inr (by rw [hx2]; rfl)
        · rintro (rfl | rfl)
          · refine ⟨x₁, ?_, rfl⟩
            rw [hat]; simp [hc.2.2.1]
          · refine ⟨x₂, ?_, rfl⟩
            rw [hat]; simp [hc.2.2.2.1]
      · rw [Function.update_of_ne e1] at hp
        have hjm : j ∈ h.s.M.atoms := (Finset.mem_insert.1 hj).resolve_left e2
        have := hI.ok j hjm p vis hp
        have hds : DSet (h.s.cutSt v v₂ x₁ x₂ c₁ c₂) j = DSet h.s j := by
          ext z
          constructor
          · rintro ⟨x, hx, rfl⟩
            refine ⟨x, ?_, rfl⟩
            rw [hat x] at hx
            split_ifs at hx with hcond
            · exact absurd hx.symm e2
            · exact hx
          · rintro ⟨x, hx, rfl⟩
            refine ⟨x, ?_, rfl⟩
            rw [hat x]
            split_ifs with hcond
            · exact absurd (hcond.1.symm.trans hx).symm e1
            · exact hx
        rw [hds]; exact this

theorem DPInv.delSt {h : HSt V D₀} (hI : DPInv h) (P : V → Prop) [DecidablePred P] (hP : PClosed h.s.M P) :
    DPInv ⟨h.s.delSt P hP, h.hist, h.crec, h.anc⟩ where
  ok := by
    intro j hj p vis hp
    have hj' := Finset.mem_filter.1 hj
    have := hI.ok j hj'.1 p vis hp
    have hds : DSet (h.s.delSt P hP) j = DSet h.s j := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩; exact ⟨x.1, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, by rw [hx]; exact hj'.2⟩, hx, rfl⟩
    rw [hds]; exact this

end WaveTurbulence.FinalCountG3
