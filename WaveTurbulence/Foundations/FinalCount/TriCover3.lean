/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.TriCover2
/-! Triangles, part 6 (FINALCOUNT-G2): `𝔈(M) ≤ N · 𝔈(kept)` from a bound `N` on the number of triangle label
triples (DH23 L1793, `𝔉`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Set
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

namespace TriData
variable {M : Molecule V D} (T : TriData M)

/-- The set of triangle label triples of the decorations of one parameter triple. -/
def tripleSet (L γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (c : V → Mom d) (β : V → ℝ)
    (k0 : D → Mom d) : Set (Fin 3 → (Fin d → ℤ)) :=
  T.triZ '' decSet M L γ δ w Adm c β k0

/-- **The exact-triple cover.** -/
theorem countE_le_tri (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (L γ δ : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (Adm' : (PDart T.m3 T.TP → (Fin d → ℤ)) → Prop)
    (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1)) (N : ℕ)
    (hN : ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      (T.tripleSet L γ δ w Adm c β k0).encard ≤ N) :
    M.countE L γ δ w Adm ≤ (N : ℕ∞) * T.kept.countE L γ δ w Adm' := by
  refine countE_le_mul_of_cover_proj M T.kept L γ δ w Adm Adm' (fun κ x => κ x.1) N ?_
  intro c β k0 hP
  have hfin : (T.tripleSet L γ δ w Adm c β k0).Finite :=
    Set.finite_of_encard_le_coe (hN c β k0 hP)
  refine ⟨Fin 3 → (Fin d → ℤ), hfin.toFinset, fun i => {κ | T.triZ κ = i},
    fun i => T.keptParams L w c β k0 i, ?_, ?_, ?_, ?_⟩
  · have := hN c β k0 hP
    rw [hfin.encard_eq_coe_toFinset_card] at this
    exact_mod_cast this
  · intro i _
    exact T.keptParams_ok hM L w c β k0 hP i
  · intro κ hκ
    refine Set.mem_iUnion₂.mpr ⟨T.triZ κ, ?_, rfl⟩
    rw [Set.Finite.mem_toFinset]
    exact ⟨κ, hκ, rfl⟩
  · intro i _
    refine ⟨?_, ?_⟩
    · intro κ hκ κ' hκ' h
      exact T.kappa_eq_of_triZ κ κ' hκ.2.1.1 hκ'.2.1.1 (hκ.1.trans hκ'.1.symm) h
    · rintro _ ⟨κ, ⟨hz, hκ⟩, rfl⟩
      have := T.rho_mem L γ δ w Adm Adm' hAdm' c β k0 κ hκ
      rw [hz] at this
      exact this

end TriData
end WaveTurbulence.FinalCount
