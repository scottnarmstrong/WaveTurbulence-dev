/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBIncidenceSigns
public import WaveTurbulence.Foundations.FinalCount.AppBPhysicalPair
import Mathlib.Tactic

/-! # A final local label is fixed by actual conservation at a deleted atom -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

/-- If all other outgoing labels agree, a single incidence at a deleted
atom is determined by its prescribed source momentum. -/
theorem local_label_eq_of_others {d : ℕ} {L : ℝ} (hL : L ≠ 0) {v : V}
    (hv : v ∈ r.removedAtoms) (j : Fin P.edges.length)
    (hinc : appbIncidence M v (r.edge j).val = 1)
    (w : Mom d) (c : V → Mom d) (κ κ' : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hκ' : M.IsDecoration L w c κ')
    (hother : ∀ i,i ≠ j → r.localLabels κ i = r.localLabels κ' i) :
    r.localLabels κ j = r.localLabels κ' j := by
  let F := fun (k : D → (Fin d → ℤ)) (i : Fin P.edges.length) =>
    (if M.atom (r.edge i).val = v then Molecule.kvec L w (r.localLabels k) i else 0)-
      (if M.atom (M.mate (r.edge i).val) = v then Molecule.kvec L w (r.localLabels k) i else 0)
  have hm : (∑ i,F κ i) = c v := r.local_momentum L w c κ hκ hv
  have hm' : (∑ i,F κ' i) = c v := r.local_momentum L w c κ' hκ' hv
  have hd : (∑ i,(F κ i-F κ' i)) = 0 := by rw [sum_sub_distrib,hm,hm',sub_self]
  have hs : (∑ i,(F κ i-F κ' i)) = F κ j-F κ' j := by
    apply sum_eq_single j
    · intro i hi hij
      have he : Molecule.kvec L w (r.localLabels κ) i = Molecule.kvec L w (r.localLabels κ') i :=
        congrArg (fun z => w+latticePoint L z) (hother i hij)
      simp only [F,he,sub_self]
    · intro hj
      exact False.elim (hj (mem_univ _))
  rw [hs] at hd
  have he := sub_eq_zero.mp hd
  dsimp only [F] at he
  rw [appb_incidence_sign_eq M v _ hinc,appb_incidence_sign_eq M v _ hinc] at he
  have hvec : Molecule.kvec L w (r.localLabels κ) j = Molecule.kvec L w (r.localLabels κ') j := by
    rcases Int.units_eq_one_or (appbIncidenceSign M v (r.edge j).val) with hs | hs
    · simpa only [hs,Units.val_one,one_smul] using he
    · simpa only [hs,Units.val_neg,Units.val_one,neg_smul,one_smul,neg_inj] using he
  exact appb_latticePoint_injective hL (add_left_cancel hvec)

end AppbRealization
end WaveTurbulence.Mole
