/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceMomentumBridge

/-! # Exact finite link-cell decomposition of the actual localized leaves -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links Incoh

/-- The literal product of localized source inputs in the actual coordinates. -/
@[expose] def coupleLeafCellProduct {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ} (F : Mom d → ℂ)
    (c : Fin (2*Q.links.length+1) → Fin d → ℤ) (k : Mom d)
    (x : Fin Q.links.length → Fin 2 → Mom d) : ℂ :=
  ∏ a, leafCell F (c a) ((coupleMomentumData hQ hG).inputMomentum k x a)

/-- Factoring off the source inputs exposes precisely the localization weight. -/
theorem coupleLeafCellProduct_factor {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ} (F : Mom d → ℂ)
    (c : Fin (2*Q.links.length+1) → Fin d → ℤ) (k : Mom d)
    (x : Fin Q.links.length → Fin 2 → Mom d) :
    coupleLeafCellProduct hQ hG F c k x =
      (∏ a, F ((coupleMomentumData hQ hG).inputMomentum k x a)) *
        (coupleMomentumData hQ hG).inputCellWeight c k x := by
  simp only [coupleLeafCellProduct,leafCell,MomentumTreeData.inputCellWeight,leafCellProfile,
    Finset.prod_mul_distrib]

/-- An exact finite decomposition with a geometric number of link cells;
the same finite index set works for every input and every root momentum. -/
theorem actual_couple_finite_cell_decomposition (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (G : Garden 2) (Q : RegCpl) (hQ : Q.Decodes G) (hG : IsCouple G),
      ∀ c : Fin (2*Q.links.length+1) → Fin d → ℤ,
      ∃ S : Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ),
        (S.card : ℝ) ≤ C ^ Q.links.length ∧
        ∀ F : Mom d → ℂ, ∀ k : Mom d, ∀ x : Fin Q.links.length → Fin 2 → Mom d,
          coupleLeafCellProduct hQ hG F c k x =
            ∑ z ∈ S, coupleLeafCellProduct hQ hG F c k x *
              halfCellArrayWeight z (fun p => x p.1 p.2) := by
  classical
  obtain ⟨C,hC,h⟩ := actual_couple_uniform_cell_cover d hd
  refine ⟨C,hC,?_⟩
  intro G Q hQ hG c
  obtain ⟨S,hS,hs⟩ := h G Q hQ hG c
  refine ⟨S,hS,?_⟩
  intro F k x
  let A := coupleLeafCellProduct hQ hG F c k x
  have hz (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ) (hz : z ∉ S) :
      A * halfCellArrayWeight z (fun p => x p.1 p.2) = 0 := by
    by_cases hA : A = 0
    · rw [hA,zero_mul]
    have hw : (coupleMomentumData hQ hG).inputCellWeight c k x ≠ 0 := by
      intro he
      apply hA
      dsimp only [A]
      rw [coupleLeafCellProduct_factor,he,mul_zero]
    have he : halfCellArrayWeight z (fun p => x p.1 p.2) = 0 := by
      by_contra hn
      exact hz (hs k x hw z hn)
    rw [he,mul_zero]
  have hsum := (hasSum_halfCellArrayWeight (fun p : Fin Q.links.length × Fin 2 => x p.1 p.2)).mul_left A
  have hfin : HasSum (fun z : (Fin Q.links.length × Fin 2) → Fin d → ℤ => A * halfCellArrayWeight z (fun p => x p.1 p.2))
      (∑ z ∈ S, A * halfCellArrayWeight z (fun p => x p.1 p.2)) :=
    hasSum_sum_of_ne_finset_zero hz
  exact (by simpa only [mul_one] using hsum.unique hfin)

end WaveTurbulence.RegAsymp
