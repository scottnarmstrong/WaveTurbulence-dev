/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.MoleculeCuts
public import WaveTurbulence.Foundations.Molecule.MoleculeDecorations
import Mathlib.Tactic

/-!
# Conservation and quadratic energies under actual half-edge cuts

TARGET `defcut` and `defcounta2`, L2117–L2137. The inherited dart labels
are unchanged. The kept vertex has conservation vector minus the cut gap;
the other vertex receives the complementary conservation vector.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    (M : Molecule V D) {v v2 : V} {x1 x2 : D}

omit [Fintype D] in
theorem cut_dartSign (x : D) : (M.cut v v2 x1 x2).dartSign x = M.dartSign x := rfl

/-- Summing over the two actual cut atoms recovers the original atom sum. -/
theorem sum_cut_darts {E : Type*} [AddCommMonoid E] (f : D → E)
    (hd : M.IsCutData v v2 x1 x2) :
    (∑ x ∈ (M.cut v v2 x1 x2).dartsAt v, f x)+
      (∑ x ∈ (M.cut v v2 x1 x2).dartsAt v2, f x) = ∑ x ∈ M.dartsAt v, f x := by
  have hsub : {x1,x2} ⊆ M.dartsAt v := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (mem_dartsAt M v _).mpr hd.2.2.1
    · exact (mem_dartsAt M v _).mpr hd.2.2.2.1
  rw [cut_dartsAt_old M hd,cut_dartsAt_new M hd]
  simpa only [add_comm] using Finset.sum_sdiff hsub (f := f)

/-- TARGET `defcut`: the kept incoming/outgoing darts carry conservation
vector minus the actual cut gap. -/
theorem cut_conservation_old {d : ℕ} (hd : M.IsCutData v v2 x1 x2)
    (L : ℝ) (w : Mom d) (kappa : D → (Fin d → ℤ)) :
    (∑ x ∈ (M.cut v v2 x1 x2).dartsAt v,
      (M.cut v v2 x1 x2).dartSign x • Molecule.kvec L w kappa x) =
      -Molecule.gapAt L w kappa x1 x2 := by
  rw [cut_dartsAt_old M hd,Finset.sum_pair (cut_darts_ne M hd)]
  simp only [Molecule.cut,Molecule.dartSign,hd.2.2.2.2.2.1,hd.2.2.2.2.2.2,
    Bool.false_eq_true,ite_false,ite_true,neg_one_smul,one_smul,Molecule.gapAt]
  abel

/-- The other actual cut atom carries the complementary conservation vector. -/
theorem cut_conservation_new {d : ℕ} (hd : M.IsCutData v v2 x1 x2)
    (L : ℝ) (w : Mom d) (c : V → Mom d) (kappa : D → (Fin d → ℤ))
    (hk : M.IsDecoration L w c kappa) :
    (∑ x ∈ (M.cut v v2 x1 x2).dartsAt v2,
      (M.cut v v2 x1 x2).dartSign x • Molecule.kvec L w kappa x) =
      c v+Molecule.gapAt L w kappa x1 x2 := by
  have he := sum_cut_darts M (fun x => M.dartSign x • Molecule.kvec L w kappa x) hd
  have hkept := cut_conservation_old M hd L w kappa
  simp only [cut_dartSign] at hkept ⊢
  rw [hkept,hk.2 v hd.1] at he
  calc
    _ = Molecule.gapAt L w kappa x1 x2+
        (-Molecule.gapAt L w kappa x1 x2+∑ x ∈ (M.cut v v2 x1 x2).dartsAt v2,
          M.dartSign x • Molecule.kvec L w kappa x) := by abel
    _ = Molecule.gapAt L w kappa x1 x2+c v := congrArg
      (fun z => Molecule.gapAt L w kappa x1 x2+z) he
    _ = _ := add_comm _ _

/-- The kept cut atom has the exact signed difference of squared bond norms. -/
theorem cut_Gamma_old {d : ℕ} (hd : M.IsCutData v v2 x1 x2)
    (L : ℝ) (w : Mom d) (kappa : D → (Fin d → ℤ)) :
    (M.cut v v2 x1 x2).Gamma L w kappa v =
      -‖Molecule.kvec L w kappa x1‖^2+‖Molecule.kvec L w kappa x2‖^2 := by
  unfold Molecule.Gamma
  rw [cut_dartsAt_old M hd,Finset.sum_pair (cut_darts_ne M hd)]
  simp only [Molecule.cut,Molecule.dartSign,hd.2.2.2.2.2.1,hd.2.2.2.2.2.2,
    Bool.false_eq_true,ite_false,ite_true,neg_one_mul,one_mul]

/-- The quadratic energies of the two actual cut vertices add to the old energy. -/
theorem cut_Gamma_add {d : ℕ} (hd : M.IsCutData v v2 x1 x2)
    (L : ℝ) (w : Mom d) (kappa : D → (Fin d → ℤ)) :
    (M.cut v v2 x1 x2).Gamma L w kappa v+(M.cut v v2 x1 x2).Gamma L w kappa v2 =
      M.Gamma L w kappa v := by
  exact sum_cut_darts M (fun x => M.dartSign x * ‖Molecule.kvec L w kappa x‖^2) hd

end WaveTurbulence.Mole
