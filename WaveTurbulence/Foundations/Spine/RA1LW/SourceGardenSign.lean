/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.PhysicalGlobalProfile

/-! # Original garden sign and the literal recursive leading prefactor -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open Links TTree

/-- Original branching-node multiplication is the per-tree sign product. -/
theorem garden_zeta_eq_zetaOfTrees {w : ℕ} (G : Garden w) :
    G.zeta = zetaOfTrees G.sig G.tree := by
  classical
  let E : GBranch G.tree ≃ (Σ j : Fin w, {p : Path // p ∈ (G.tree j).branching}) :=
    { toFun := fun b => ⟨b.val.1,⟨b.val.2,b.property⟩⟩
      invFun := fun b => ⟨(b.1,b.2.val),b.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold Garden.zeta zetaOfTrees
  calc
    _ = ∏ b : (Σ j : Fin w, {p : Path // p ∈ (G.tree j).branching}),
        Complex.I * (((pathSign (G.sig b.1) b.2.val:ℤˣ):ℤ):ℂ) :=
      Fintype.prod_equiv E _ _ (fun _ => rfl)
    _ = _ := by
      rw [Fintype.prod_sigma]
      apply Finset.prod_congr rfl
      intro j _
      exact Finset.prod_coe_sort (G.tree j).branching
        (fun p => Complex.I * (((pathSign (G.sig j) p:ℤˣ):ℤ):ℂ))

/-- A decoded couple has the exact tree sign appearing in B2 app. -/
theorem decoded_couple_zeta {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) :
    G.zeta = zetaOfTrees ![1,-1] ![Q.trees.1,Q.trees.2] := by
  have ht : G.tree = ![Q.trees.1,Q.trees.2] := by
    funext j
    fin_cases j
    · exact hQ.2.1
    · exact hQ.2.2.1
  rw [garden_zeta_eq_zetaOfTrees,hQ.1.2,ht]

/-- The physical leading scale, including the original singular factor2
per link, is precisely the recursive app normalization. -/
theorem physical_leading_app_prefactor (n : ℕ) (δ : ℝ) :
    (((δ/8)^n:ℝ):ℂ)*(2:ℂ)^n = (2:ℂ)⁻¹^(2*n)*(δ:ℂ)^n := by
  simp only [Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_ofNat,pow_mul]
  rw [← mul_pow,← mul_pow]
  congr 1
  norm_num
  ring

end WaveTurbulence.RA1Leafwise
