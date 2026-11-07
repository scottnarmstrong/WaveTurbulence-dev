/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.TriSib2
/-! Triangles, sibling part 3 (G2-SIBLING): **`triangle_excess_sibling`**, DH23 Prop 9.4 Step 2 (L1793--L1796 with
the L1801 modification) when the `κ = 50` hit of the second `α`-atom is the first cut of the same triangle. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace TriData
variable {M : Molecule V D} (T : TriData M)

/-- **DH23 Prop 9.4, Step 2 (removing a triangle), with a sibling `κ₁ = 50` hit.**  As `triangle_excess`, except that
when `κ₁ = 50` the second ball is either a fixed ball (`hball1`, an older cut) or centred at `± ` the gap of the first
cut of the same triangle (`hsib1`).  The conclusion is identical. -/
theorem triangle_excess_sibling {d : ℕ} {L γ η δ C₁ : ℝ} (H : TriReal d L γ η δ C₁) (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4)
    (c : ℕ) (hn : (M.atoms.card : ℝ) ≤ Real.log L ^ c) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart T.m3 T.TP → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1))
    (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ T.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ T.m2.maximalLadders, ∀ S ∈ T.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hP3 : ∀ S' ∈ T.m3.maximalLadders, ∀ S ∈ T.m2.maximalLadders, S' ⊆ S → P S' = P S)
    (hnz : ∀ κ, Adm κ → ∀ j, Molecule.gapAt L w κ (T.a j) (T.b j) ≠ 0)
    (R₀ R₁ : ℝ) (κ₀ κ₁ : ℕ) (hκ₀ : κ₀ = 0 ∨ κ₀ = 50) (hκ₁ : κ₁ = 0 ∨ κ₁ = 50)
    (hR₀l : L⁻¹ ≤ R₀) (hR₀u : R₀ ≤ L ^ (-γ + η)) (hR₁l : L⁻¹ ≤ R₁) (hR₁u : R₁ ≤ L ^ (-γ + η))
    (hgap0 : ∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' (T.a 0) (T.b 0)‖ ≤ 2 * R₀)
    (hball0 : κ₀ = 50 → ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      ∃ r₀ : Mom d, ∀ κ' ∈ decSet M L γ δ w Adm c β k0,
        ‖Molecule.gapAt L w κ' (T.a 0) (T.b 0) - r₀‖ ≤ L ^ (-50 * η) * R₀)
    (hgap1 : ∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' (T.a 1) (T.b 1)‖ ≤ 2 * R₁)
    (hb1 : κ₁ = 50 → (∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      ∃ r₀ : Mom d, ∀ κ' ∈ decSet M L γ δ w Adm c β k0,
        ‖Molecule.gapAt L w κ' (T.a 1) (T.b 1) - r₀‖ ≤ L ^ (-50 * η) * R₁) ∨
      T.SiblingReading L w Adm (L ^ (-50 * η) * R₁)) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (T.kept.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal (triConst d c η δ *
        excessRHS L γ η (T.alphaLabels R₀ R₁ κ₀ κ₁) ((T.kept.numComponents : ℤ) - M.numComponents)
          (3 - ((T.alphaLabels R₀ R₁ κ₀ κ₁).length : ℤ)))) := by
  by_cases hα0 : T.IsA0 <;> by_cases hα1 : T.IsA1
  · have hl : T.alphaLabels R₀ R₁ κ₀ κ₁ = [(R₀, κ₀), (R₁, κ₁)] := by simp [alphaLabels, hα0, hα1]
    have hΔ : ((T.kept.numComponents : ℤ) - M.numComponents) = 0 := by rw [T.deltaF_eq]; simp [hα0, hα1]
    rw [hl, hΔ]
    by_cases h50 : κ₁ = 50
    · rcases hb1 h50 with hf | hs
      · simpa using T.tri_aa H hM c w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 R₀ R₁ κ₀ κ₁ hκ₀ hκ₁ hR₀l hR₀u hR₁l hR₁u
          hgap0 hball0 hgap1 (fun _ => hf) hα0 hα1
      · simpa using T.tri_aa_sib H hM c w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 R₀ R₁ κ₀ κ₁ hκ₀ h50 hR₀l hR₀u hR₁l hR₁u
          hgap0 hball0 hs hα0 hα1
    · simpa using T.tri_aa H hM c w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 R₀ R₁ κ₀ κ₁ hκ₀ hκ₁ hR₀l hR₀u hR₁l hR₁u
        hgap0 hball0 hgap1 (fun h => absurd h h50) hα0 hα1
  · have hl : T.alphaLabels R₀ R₁ κ₀ κ₁ = [(R₀, κ₀)] := by simp [alphaLabels, hα0, hα1]
    have hΔ : ((T.kept.numComponents : ℤ) - M.numComponents) = 1 := by rw [T.deltaF_eq]; simp [hα0, hα1]
    rw [hl, hΔ]
    simpa using T.tri_ab H hM c hn w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 hnz R₀ κ₀ hκ₀ hR₀l hR₀u hgap0 hball0 hα0 hα1
  · have hl : T.alphaLabels R₀ R₁ κ₀ κ₁ = [(R₁, κ₁)] := by simp [alphaLabels, hα0, hα1]
    have hΔ : ((T.kept.numComponents : ℤ) - M.numComponents) = 1 := by rw [T.deltaF_eq]; simp [hα0, hα1]
    rw [hl, hΔ]
    have hball1 : κ₁ = 50 → ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
        ∃ r₀ : Mom d, ∀ κ' ∈ decSet M L γ δ w Adm c β k0,
          ‖Molecule.gapAt L w κ' (T.a 1) (T.b 1) - r₀‖ ≤ L ^ (-50 * η) * R₁ := by
      intro h50
      rcases hb1 h50 with hf | hs
      · exact hf
      · exact fun c β k0 _ => T.ball1_of_sib_beta (by linarith [(Real.one_le_exp (by norm_num)).trans H.hL])
          H.hδ0 w Adm (T.hbeta0 hα0) hs c β k0
    simpa using T.tri_ba H hM c hn w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 hnz R₁ κ₁ hκ₁ hR₁l hR₁u hgap1 hball1 hα0 hα1
  · have hl : T.alphaLabels R₀ R₁ κ₀ κ₁ = [] := by simp [alphaLabels, hα0, hα1]
    have hΔ : ((T.kept.numComponents : ℤ) - M.numComponents) = 2 := by rw [T.deltaF_eq]; simp [hα0, hα1]
    rw [hl, hΔ]
    simpa using T.tri_bb H hM c hn w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 hnz hα0 hα1

end TriData
end WaveTurbulence.FinalCount
