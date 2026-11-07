/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBDeletionCounting
import Mathlib.Tactic

/-! # Box bound for the local labels of a deletion pattern

The local tuple set of `deletion_countE_exists_post` lies in a coordinate box, with no source
equation used: it costs `⌈2L+1⌉^d` per removed bond.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset Set
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

theorem localChoices_card_le_box {d : ℕ} (p : AppbCountParameters M d) {L : ℝ}
    (hL : 0 < L) (γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) :
    (r.localChoices p hL γ δ w Adm).card ≤ ⌈2*L+1⌉₊^(d*P.edges.length) := by
  classical
  let C (x : D) (j : Fin d) : Finset ℤ := Counting.integerInterval
    (L*((p.center x) j-w j)-L) (L*((p.center x) j-w j)+L)
  let S (i : Fin P.edges.length) : Set (Fin d → ℤ) :=
    Set.pi Set.univ (fun j => (C (r.edge i).val j : Set ℤ))
  have hsub : ((r.localChoices p hL γ δ w Adm : Finset _) : Set (Fin P.edges.length → (Fin d → ℤ))) ⊆
      Set.pi Set.univ S := by
    intro q hq i _hi j _hj
    obtain ⟨κ,hκ,rfl⟩ := (r.mem_localChoices p hL γ δ w Adm q).mp hq
    have hk := hκ.2.1
    apply (Counting.mem_integerInterval _ _ _).mpr
    have he := (PiLp.norm_apply_le (p := (2:ENNReal))
      (Molecule.kvec L w κ (r.edge i).val-p.center (r.edge i).val) j).trans (hk.2 (r.edge i).val)
    have hcoord : |w j+(κ (r.edge i).val j:ℝ)/L-(p.center (r.edge i).val) j| ≤ 1 := by
      simpa only [Molecule.kvec,latticePoint,PiLp.sub_apply,PiLp.add_apply,Real.norm_eq_abs] using he
    have hlo : (p.center (r.edge i).val) j-w j-1 ≤ (κ (r.edge i).val j:ℝ)/L := by
      linarith only [(abs_le.mp hcoord).1]
    have hhi : (κ (r.edge i).val j:ℝ)/L ≤ (p.center (r.edge i).val) j-w j+1 := by
      linarith only [(abs_le.mp hcoord).2]
    have hl := (le_div_iff₀ hL).mp hlo
    have hu := (div_le_iff₀ hL).mp hhi
    have e : r.localLabels κ i j = κ (r.edge i).val j := rfl
    rw [e]
    constructor <;> nlinarith only [hl,hu]
  have hcoord : ∀ a : ℝ, (Counting.integerInterval (a-L) (a+L)).card ≤ ⌈2*L+1⌉₊ := by
    intro a
    have hreal := (Counting.card_integerInterval_le a hL.le).trans (Nat.le_ceil (2*L+1))
    exact_mod_cast hreal
  have henc : ((r.localChoices p hL γ δ w Adm : Finset _) : Set (Fin P.edges.length → (Fin d → ℤ))).encard ≤
      ((⌈2*L+1⌉₊ ^(d*P.edges.length) : ℕ) : ℕ∞) := by
    calc _ ≤ (Set.pi Set.univ S).encard := Set.encard_mono hsub
      _ = ∏ i : Fin P.edges.length, ∏ j : Fin d, (C (r.edge i).val j : Set ℤ).encard := by
        simp only [S,Set.encard_pi_eq_prod_encard]
      _ ≤ ∏ _i : Fin P.edges.length, ∏ _j : Fin d, (⌈2*L+1⌉₊ : ℕ∞) := by
        apply Finset.prod_le_prod
        intro i _
        apply Finset.prod_le_prod
        intro j _
        rw [Set.encard_coe_eq_coe_finsetCard]
        exact_mod_cast hcoord _
      _ = _ := by
        simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← pow_mul]
        push_cast
        rw [mul_comm]
  rw [Set.encard_coe_eq_coe_finsetCard] at henc
  exact_mod_cast henc

end AppbRealization
end WaveTurbulence.Mole
