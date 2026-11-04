/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCConst

/-!
# DH21 Proposition 5.1 with the DH23 weights

**Statement (code form, `RegCpl.maincoef`).** Let `0 ≤ θ < 1`, `0 < a`, `0 ≤ b` with `a + b < 1` and
`a + b ≤ θ`, and `A ≥ A1`. For every well-formed couple code `Q`, `B̃_Q = RegCpl.Btilde Q` has the
expansion (maincoef3) in the chosen nodes `𝒩^ch = chosenSet Q.links`:
`B̃_Q(t, s, α) = Σ_{Z ⊆ 𝒩^ch} ∏_{𝔫 ∈ Z} Φ(ζ_𝔫 α_𝔫) B̃_{Q,Z}(t, s, α[𝒩^ch ∖ Z])` on `[0,1]²`, where
`Φ(ζx) = χ_∞(x)/(ζπix)` (`PhiZ`, `phiR_sign`) and each `B̃_{Q,Z}` is
`∫ 𝒞(λ, α[𝒩^ch ∖ Z]) e^{πi(λ₁t + λ₂s)} dλ` (`MCRep`) with
* (maincoef2) `∫ ⟨max(λ₁,λ₂)⟩^θ |∂^ρ_α 𝒞| ≤ C₀^{2n+1} A^{|ρ|} (2|ρ|)!`,
* (maincoef2.5) `∫ ⟨max(λ₁,λ₂)⟩^a ⟨α_𝔫⟩^b |𝒞| ≤ C₀^{2n+1}` for each `𝔫 ∈ 𝒩^ch ∖ Z`,
where `n = Q.size` is the order of the couple and `C₀ = C0 θ a b`.

**DH23 weights (`RegCpl.maincoef_DH23`).** `θ = 1 - η/8`, `a = η/4`, `b = 1 - η/2` (DH23 L955–L969) for
`0 < η ≤ 2`.

**Garden form (`maincoef_of_structure`).** For carriers `G` with a predicate `IsReg` and a decoding
relation `Dec`, under the structure theorem in exactly the form of REG-STRUCT's
`existsUnique_regCpl_decodes` (`∀ G, IsReg G → ∃! Q, Q.wf = true ∧ Dec Q G`; with `Garden 2`,
`IsRegularCouple` and `RegCpl.Decodes` this is the named obligation), every regular `G` has a unique
well-formed code, and its `B̃` has the expansion.

**The sign of F61.** By construction the factor in front of `B̃_{Q,Z}` is DH21 (maincoef1)'s
`∏_{𝔫 ∈ Z} χ_∞(α_𝔫)/(ζ_𝔫 πi α_𝔫)`; the `-1` of Lemma 5.8's `T₀ = -I_μ` (`iker_comp_decompP`) is inside
`B̃_{Q,Z}`.
-/

public section

namespace WaveTurbulence.ClassJR

/-- **DH21's `B̃_Q(t, s, α[𝒩^ch])`** for a couple code: the `+` tree at `(0, [])`, the `-` tree at
`(1, [])`. -/
@[expose] noncomputable def RegCpl.Btilde (Q : RegCpl) : (Addr → ℝ) → ℝ → ℝ → ℂ :=
  Q.Bt (0, []) (1, [])

theorem disjoint_up_roots : Disjoint (Up ((0 : Fin 2), ([] : Path))) (Up ((1 : Fin 2), ([] : Path))) := by
  rw [Set.disjoint_left]
  rintro v ⟨h0, -⟩ ⟨h1, -⟩
  rw [h0] at h1
  exact absurd h1 (by decide)

/-- **DH21 Proposition 5.1 (maincoef)**, code form, with the DH23 weights `⟨max(λ₁,λ₂)⟩^θ` in
(maincoef2) and `⟨max(λ₁,λ₂)⟩^a ⟨α_𝔫⟩^b` in (maincoef2.5). -/
theorem RegCpl.maincoef {θ a b A : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (ha : 0 < a) (hb : 0 ≤ b)
    (hab1 : a + b < 1) (hab : a + b ≤ θ) (hA : A1 ≤ A) (Q : RegCpl) (hQ : Q.wf = true) :
    MCExp θ a b A (C0 θ a b ^ (2 * Q.size + 1)) nodeSgn (chosenSet Q.links) Q.Btilde :=
  (RegCpl.mcexp hθ0 hθ1 ha hb hab1 hab hA Q _ _ disjoint_up_roots).mono
    (RegCpl.NB_le Q hQ).2 (A1_nonneg.trans hA)

/-- **DH21 Proposition 5.1 with the weights of DH23** (L955–L969): `θ = 1 - η/8`, `a = η/4`,
`b = 1 - η/2`. -/
theorem RegCpl.maincoef_DH23 {η A : ℝ} (hη : 0 < η) (hη2 : η ≤ 2) (hA : A1 ≤ A) (Q : RegCpl)
    (hQ : Q.wf = true) :
    MCExp (1 - η / 8) (η / 4) (1 - η / 2) A
      (C0 (1 - η / 8) (η / 4) (1 - η / 2) ^ (2 * Q.size + 1)) nodeSgn (chosenSet Q.links)
      Q.Btilde :=
  RegCpl.maincoef (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) hA Q hQ

/-- **DH21 Proposition 5.1 for regular couples**, through the structure theorem (DH21 Props 4.7–4.8,
TARGET Prop 4.4). The hypothesis `hstruct` is the named obligation `existsUnique_regCpl_decodes` of
REG-STRUCT (`∃! Q : RegCpl, Q.wf = true ∧ Q.Decodes G` for `G : Garden 2` with
`IsRegularCouple G`), stated over the carrier type, the regularity predicate and the decoding
relation. -/
theorem maincoef_of_structure {Carrier : Type*} (IsReg : Carrier → Prop)
    (Dec : RegCpl → Carrier → Prop)
    (hstruct : ∀ G : Carrier, IsReg G → ∃! Q : RegCpl, Q.wf = true ∧ Dec Q G)
    {θ a b A : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (ha : 0 < a) (hb : 0 ≤ b) (hab1 : a + b < 1)
    (hab : a + b ≤ θ) (hA : A1 ≤ A) (G : Carrier) (hG : IsReg G) :
    ∃! Q : RegCpl, (Q.wf = true ∧ Dec Q G) ∧
      MCExp θ a b A (C0 θ a b ^ (2 * Q.size + 1)) nodeSgn (chosenSet Q.links) Q.Btilde := by
  obtain ⟨Q, hQ, huniq⟩ := hstruct G hG
  exact ⟨Q, ⟨hQ, RegCpl.maincoef hθ0 hθ1 ha hb hab1 hab hA Q hQ.1⟩,
    fun Q' hQ' => huniq Q' hQ'.1⟩

end WaveTurbulence.ClassJR
