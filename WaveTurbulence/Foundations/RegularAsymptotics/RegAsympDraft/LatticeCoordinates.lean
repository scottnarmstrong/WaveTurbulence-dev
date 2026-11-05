/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.Links.Incoh1

/-! # The actual integer-decoration sum in link coordinates

DH23 (newsum1), DH21 (substitution). The flower condition is removed
only for a plain couple. The finite-dimensional change of variables is
an equivalence of the ACTUAL GenDecoration carrier, not a replacement sum.
-/

@[expose] public section
namespace WaveTurbulence.RegAsymp
open Links

/-- On plain couples, the extra flower-label condition is void. -/
def genDecorationEquivDecR {G : Garden 2} (hG : IsCouple G) (d : ℕ) :
    GenDecoration G d (fun _ => 0) 0 ≃ DecR G (Fin d → ℤ) 0 where
  toFun κ := ⟨κ.1,κ.2.1,κ.2.2.1⟩
  invFun κ := ⟨κ.1,κ.2.1,κ.2.2,fun ℓ hf => by
    have hn := hG.1 ℓ
    unfold Garden.IsFlower at hf
    rw [hn] at hf
    cases hf⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The source integer-decoration coordinates, one independent pair per link. -/
def integerLinkEquiv {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G) (d : ℕ) :
    GenDecoration G d (fun _ => 0) 0 ≃ (Fin Q.links.length → (Fin d → ℤ) × (Fin d → ℤ)) :=
  (genDecorationEquivDecR hG d).trans (decEquiv hQ hG 0)

/-- Exact reindexing is valid without an extra summability premise. -/
theorem tsum_integerLinkEquiv {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G)
    (d : ℕ) (f : GenDecoration G d (fun _ => 0) 0 → ℂ) :
    (∑' κ, f κ) = ∑' θ, f ((integerLinkEquiv hQ hG d).symm θ) :=
  ((integerLinkEquiv hQ hG d).symm.tsum_eq f).symm

/-- The constructed old decoration has exactly the prescribed link coordinates. -/
theorem integerLinkEquiv_symm_params {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G)
    (hG : IsCouple G) (d : ℕ) (θ : Fin Q.links.length → (Fin d → ℤ) × (Fin d → ℤ)) :
    decParams hQ (genDecorationEquivDecR hG d ((integerLinkEquiv hQ hG d).symm θ)) = θ :=
  (integerLinkEquiv hQ hG d).apply_symm_apply θ

/-- F62: each link contributes the SQUARE of its single-node Wick factor. -/
theorem epsDec_integerLinkEquiv_symm {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G)
    (hG : IsCouple G) (d : ℕ) (θ : Fin Q.links.length → (Fin d → ℤ) × (Fin d → ℤ)) :
    epsDec G ((integerLinkEquiv hQ hG d).symm θ).val =
      ∏ j, epsXY (θ j).1 (θ j).2 ^ 2 := by
  have hp := integerLinkEquiv_symm_params hQ hG d θ
  rw [epsDec_eq_prod_links hQ hG ((integerLinkEquiv hQ hG d).symm θ).property.1]
  apply Finset.prod_congr rfl
  intro j _
  have hj := congrFun hp j
  have hx := congrArg Prod.fst hj
  have hy := congrArg Prod.snd hj
  change xv (extend ((integerLinkEquiv hQ hG d).symm θ).val) (chosenNode Q j) = (θ j).1 at hx
  change yv (extend ((integerLinkEquiv hQ hG d).symm θ).val) (chosenNode Q j) = (θ j).2 at hy
  rw [hx,hy]

end WaveTurbulence.RegAsymp
