/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Cancel.MCBridge
public import WaveTurbulence.Foundations.ClassJR.MCTExp

/-! # Pointwise extraction of a tree time coefficient from its regularized limit

Tree expansions are required only on the forward triangle. The extraction theorem
needs the actual Gaussian limit at that point, so a full-square regularized-limit
invariant is unnecessary. The source tree limit itself is a separate obligation.
-/

public section
namespace WaveTurbulence.RegAsymp
open ClassJR Cancel Filter
open scoped Topology

/-- Conditional coefficient extraction for a forward-triangle expansion. This helper
consumes an actual regularized-limit proof; it does not assert that source limit. -/
theorem tree_component_mint_eq_of_tendsto {V : Type} [DecidableEq V]
    {θ a b Agev N : ℝ} (hθ : 0 ≤ θ) {ζ : V → ℤ}
    (hζ : ∀ v, ζ v = 1 ∨ ζ v = -1) {Z S : Finset V} (hZ : Z ⊆ S)
    {F : (V → ℝ) → ℝ → ℝ → ℂ}
    {G : Finset V → (V → ℝ) → ℝ → ℝ → ℂ}
    (hG : ∀ Z' ⊆ S, MCRep θ a b Agev N (↑(S \ Z')) (G Z'))
    (hF : ∀ α t s, 0 ≤ s → s < t → t ≤ 1 →
      F α t s = ∑ Z' ∈ S.powerset, (∏ z ∈ Z', PhiZ ζ z (α z))*G Z' α t s)
    {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1) {J : ℂ}
    (hlim : Tendsto (fun ε => RI ε ζ Z S F t s) (𝓝[>] (0:ℝ)) (𝓝 J)) (α₀ : V → ℝ) :
    mint (S \ Z) (fun α => G Z α t s) α₀ = J := by
  have ht' : t ∈ Set.Icc (0:ℝ) 1 := ⟨hs.trans hst.le,ht⟩
  have hs' : s ∈ Set.Icc (0:ℝ) 1 := ⟨hs,hst.le.trans ht⟩
  rw [mint_eq_of_dependsOn (mcRep_dependsOn (hG Z hZ) ht' hs') α₀ 0]
  have h := tendsto_mint_wgt_of_expansion hZ hζ (F := fun α => F α t s)
    (G := fun Z' α => G Z' α t s) (α₀ := 0)
    (fun Z' hZ' => mcRep_dependsOn (hG Z' hZ') ht' hs')
    (fun Z' hZ' => mcRep_mInt hθ (hG Z' hZ') ht' hs' 0)
    (fun α => hF α t s hs hst ht)
  exact tendsto_nhds_unique h hlim

end WaveTurbulence.RegAsymp
