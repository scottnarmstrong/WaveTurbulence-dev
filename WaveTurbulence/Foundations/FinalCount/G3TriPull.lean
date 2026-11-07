/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Bal
public import WaveTurbulence.Foundations.FinalCount.G3HInv
/-! **FINALCOUNT-G3: triangles pull back along a cut.**  A triangle of `M.cut v v₂ x₁ x₂` is a triangle of `M` with
the same darts (when `M` has no self-loop), so `NoSGTriangle` is preserved by the cuts of Steps 3 and 4. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem piV_cut_atom {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) {v v₂ : V} {x₁ x₂ : D}
    (hcd : M.IsCutData v v₂ x₁ x₂) (y : D) : piV v v₂ ((M.cut v v₂ x₁ x₂).atom y) = M.atom y := by
  rw [cut_atom]
  unfold piV
  split_ifs with h1 h2 h2
  · exact h1.1.symm
  · exact absurd rfl h2
  · exact absurd h2 (fun e => hcd.2.1 (e ▸ M.atom_mem y))
  · rfl

theorem TriData.pull {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D} {v v₂ : V} {x₁ x₂ : D}
    (hcd : M.IsCutData v v₂ x₁ x₂) (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x))
    (T' : TriData (M.cut v v₂ x₁ x₂)) :
    ∃ T : TriData M, (∀ j, T.a j = T'.a j) ∧ ∀ j, T.b j = T'.b j := by
  have hkey := piV_cut_atom M hcd
  have hcons : ∀ k : Fin 3, piV v v₂ (T'.t k) ≠ piV v v₂ (T'.t (k + 1)) := by
    intro k hk
    have h1 : M.atom (T'.b k) = piV v v₂ (T'.t k) := by rw [← hkey, T'.atom_b]
    have h2 : M.atom (M.mate (T'.b k)) = piV v v₂ (T'.t (k + 1)) := by
      have : (M.cut v v₂ x₁ x₂).mate (T'.b k) = T'.a (k + 1) := T'.mate_b k
      have e : M.mate (T'.b k) = T'.a (k + 1) := this
      rw [e, ← hkey, T'.atom_a]
    exact hnl (T'.b k) (by rw [h1, h2]; exact hk)
  refine ⟨⟨fun j => piV v v₂ (T'.t j), T'.f, T'.a, T'.b, ?_, ?_, ?_, T'.f_inj, ?_, ?_, T'.out_a, T'.out_b, T'.mate_b⟩,
    fun _ => rfl, fun _ => rfl⟩
  · intro j
    exact piV_mem M hcd (T'.t_mem j)
  · intro i j hij
    by_contra hne
    have : j = i + 1 ∨ i = j + 1 := (by decide : ∀ i j : Fin 3, i ≠ j → j = i + 1 ∨ i = j + 1) i j hne
    rcases this with h | h
    · exact hcons i (by rw [← h]; exact hij)
    · exact hcons j (by rw [← h]; exact hij.symm)
  · intro j h
    exact T'.f_fresh j (Finset.mem_insert_of_mem h)
  · intro j; rw [← hkey, T'.atom_a]
  · intro j; rw [← hkey, T'.atom_b]

theorem NoSGTriangle.cutSt {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {s : St.{u} V D₀}
    (h : NoSGTriangle L γ η w κ s) (hnl : ∀ x, s.M.atom x ≠ s.M.atom (s.M.mate x)) {v v₂ : V} {x₁ x₂ : s.D}
    (hcd : s.M.IsCutData v v₂ x₁ x₂) (c₁ c₂ : Cls) : NoSGTriangle L γ η w κ (s.cutSt v v₂ x₁ x₂ c₁ c₂) := by
  intro T' hT
  obtain ⟨T, ha, hb⟩ := TriData.pull hcd hnl T'
  apply h T
  rw [ha, hb, ha, hb]
  exact hT

theorem Step3.noSGTri {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {s s' : St.{u} V D₀}
    (hs : Step3 L γ η w κ s s') (h : NoSGTriangle L γ η w κ s) (hnl : ∀ x, s.M.atom x ≠ s.M.atom (s.M.mate x)) :
    NoSGTriangle L γ η w κ s' := by
  cases hs with
  | cut v v₂ x₁ x₂ hcd R kp hR hkp hε hsg hsim h3 => exact h.cutSt hnl hcd _ _

theorem Step4.noSGTri {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {s s' : St.{u} V D₀}
    (hs : Step4 s s') (h : NoSGTriangle L γ η w κ s) (hnl : ∀ x, s.M.atom x ≠ s.M.atom (s.M.mate x)) :
    NoSGTriangle L γ η w κ s' := by
  cases hs with
  | cut v v₂ x₁ x₂ hcd hε hβ h3 => exact h.cutSt hnl hcd _ _

end WaveTurbulence.FinalCountG3
