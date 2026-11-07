/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineGapTransport
/-! Conserving dart labels pull back through actual molecule isomorphisms. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Stage1 Mole
variable {V W D E : Type*} [DecidableEq V] [DecidableEq W]
  [Fintype D] [Fintype E]
  {M : Molecule V D} {N : Molecule W E} {d : ℕ}

theorem molIso_decoration_pull (F : MolIso M N) (L : ℝ) (base : Mom d)
    (c : W → Mom d) (κ : E → (Fin d → ℤ)) (hκ : N.IsDecoration L base c κ) :
    M.IsDecoration L base (c ∘ F.e) (κ ∘ F.d) := by
  constructor
  · intro x
    change κ (F.d (M.mate x)) = κ (F.d x)
    rw [← F.mate_comm]
    exact hκ.1 _
  · intro v hv
    refine Eq.trans ?_ (hκ.2 (F.e v) ((F.atoms_iff v).mpr hv))
    apply Finset.sum_bij (fun x _ => F.d x)
    · intro x hx
      exact (mem_dartsAt N _ _).mpr ((F.atom_comm x).trans (congrArg F.e ((mem_dartsAt M _ _).mp hx)))
    · intro x _ y _ h
      exact F.d.injective h
    · intro y hy
      obtain ⟨x, rfl⟩ := F.d.surjective y
      refine ⟨x, ?_, rfl⟩
      exact (mem_dartsAt M _ _).mpr (F.e.injective ((F.atom_comm x).symm.trans ((mem_dartsAt N _ _).mp hy)))
    · intro x _
      simp only [Molecule.dartSign, F.out_comm, Molecule.kvec, Function.comp_apply]

end WaveTurbulence.VineA
