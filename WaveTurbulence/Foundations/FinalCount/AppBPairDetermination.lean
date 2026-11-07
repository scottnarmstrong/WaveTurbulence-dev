/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBPairIncidence
public import WaveTurbulence.Foundations.FinalCount.AppBPhysicalPair
import Mathlib.Tactic

/-! # Conservation determines the second label of a degree-two pair -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbLocalPair
variable {M : Molecule V D} {P : AppbPattern} {r : AppbRealization M P} {v : V}
    (p : AppbLocalPair r v)

/-- Fixed momentum and one actual integer label determine the other one.
This is the reconstruction step in the extended 2R-3F removal. -/
theorem second_label_eq {d : ℕ} {L : ℝ} (hL : L ≠ 0) (hv : v ∈ r.removedAtoms)
    (w : Mom d) (c : V → Mom d) (κ κ' : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hκ' : M.IsDecoration L w c κ')
    (hfirst : r.localLabels κ p.first = r.localLabels κ' p.first) :
    r.localLabels κ p.second = r.localLabels κ' p.second := by
  have hm := p.momentum hv L w c κ hκ
  have hm' := p.momentum hv L w c κ' hκ'
  have he : Molecule.kvec L w (r.localLabels κ) p.first =
      Molecule.kvec L w (r.localLabels κ') p.first := by
    exact congrArg (fun z => w+latticePoint L z) hfirst
  rw [he] at hm
  have hs := add_left_cancel (hm.trans hm'.symm)
  have hvec : Molecule.kvec L w (r.localLabels κ) p.second =
      Molecule.kvec L w (r.localLabels κ') p.second := by
    rcases Int.units_eq_one_or (appbIncidenceSign M v (r.edge p.second).val) with h | h
    · simpa only [h,Units.val_one,one_smul] using hs
    · simpa only [h,Units.val_neg,Units.val_one,neg_smul,one_smul,neg_inj] using hs
  exact appb_latticePoint_injective hL (add_left_cancel hvec)

end AppbLocalPair
end WaveTurbulence.Mole
