/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.FrozenB1

/-! # Exact integer and coset coordinate shifts for source decoration fibers -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed

/-- Uniform translation preserves the actual source branching and pairing rules. -/
theorem isDecoration_add {w : ℕ} (G : Garden w) {E : Type*} [AddCommGroup E]
    (κ : GNode G.tree → E) (hκ : IsDecoration G κ) (v : E) :
    IsDecoration G (fun a => κ a + v) := by
  constructor
  · intro b
    change κ b.toNode+v = (κ (b.child 0)+v)-(κ (b.child 1)+v)+(κ (b.child 2)+v)
    rw [hκ.1 b]
    abel
  · intro ℓ
    exact congrArg (fun z => z+v) (hκ.2 ℓ)

theorem latticePoint_add {d : ℕ} (L : ℝ) (a b : Fin d → ℤ) :
    latticePoint L (a+b) = latticePoint L a+latticePoint L b := by
  ext j
  simp only [latticePoint,PiLp.add_apply,Pi.add_apply,Int.cast_add,add_div]

theorem epsCoef_add {d : ℕ} (a b c v : Fin d → ℤ) :
    epsCoef (a+v) (b+v) (c+v) = epsCoef a b c := by
  simp only [epsCoef,ne_eq,add_left_inj]

theorem epsDec_add {w d : ℕ} (G : Garden w) (κ : GNode G.tree → (Fin d → ℤ))
    (v : Fin d → ℤ) : epsDec G (fun a => κ a+v) = epsDec G κ := by
  unfold epsDec
  exact Finset.prod_congr rfl (fun _ _ => epsCoef_add _ _ _ v)

theorem cosetDecoration_add {w d : ℕ} (G : Garden w) (L : ℝ) (k : Mom d)
    (κ : GNode G.tree → (Fin d → ℤ)) (v : Fin d → ℤ) :
    cosetDecoration G L k (fun a => κ a+v) = cosetDecoration G L (k+latticePoint L v) κ := by
  funext a
  simp only [cosetDecoration,latticePoint_add]
  abel

end WaveTurbulence.RegRed
