/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCTMain
public import WaveTurbulence.Foundations.ClassJR.MCProp51

/-!
# DH21 Proposition 5.1 for regular trees (DH21 Proposition 6.10)

DH21 Proposition 6.10 (L1698–L1710; DH23 L1175: "the results for regular trees `𝒯` are proved
similarly using the fact that a regular tree forms a regular couple with the trivial tree"):
`Ã_𝒯(t, s, α[𝒩^ch])` "has form (maincoef1) that satisfies (maincoef2)–(maincoef2.5), for `t > s`",
with the weights `(⟨λ₁⟩ + ⟨λ₂⟩)` in place of the product weights of DH21. With the DH23 weights
`⟨max(λ₁, λ₂)⟩` of `RegCpl.maincoef_DH23` the statement is the same as for couples, with the identity
for `0 ≤ s < t ≤ 1` (`MCExpT`).

Route: directly from the chain integral with the continuation `1{t' > s}` (`RegChain.At`), rebased at
`s` (`chainT_rebase`), which is DH21's "analyzing the regular chain similar to Section 5.2, … for
`t > s`". The couple `(𝒯, •)` of DH21 is not needed for the time coefficient: it organizes the
decorations and the pairing (DH21 Prop 6.10, first paragraph), which enter through the tree links
`X.linksAt ζ x`.

* `RegChain.maincoefT`: general exponents, constant `C_T^{2n(𝒯)+1}`;
* `RegChain.maincoefT_DH23`: the DH23 weights `θ = 1 - η/8`, `a = η/4`, `b = 1 - η/2`, the couples of
  the pairs expanded with `θ' = 1 - η/16`, `a' = 5η/16`, and the difference exponent `δ = η/16`.
-/

public section

namespace WaveTurbulence.ClassJR

/-- **DH21 Proposition 5.1 for a regular tree code** (DH21 Proposition 6.10): for a well-formed tree
code `X` of root sign `ζ` rooted at `x`, `Ã_𝒯 = X.At ζ x` has the expansion (maincoef3) for `t > s` in
the chosen nodes `𝒩^ch` of the tree links, with the constant `C_T^{2n(𝒯)+1}`. -/
theorem RegChain.maincoefT {θ a b A θ' a' δ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (ha : 0 < a)
    (hb : 0 ≤ b) (hab1 : a + b < 1) (hab : a + b ≤ θ) (hA : A1 ≤ A) (hθ'1 : θ' < 1) (ha' : 0 < a')
    (hab1' : a' + b < 1) (hab' : a' + b ≤ θ') (hδ : 0 < δ) (hδθ : δ + θ ≤ θ') (hδa : δ + a ≤ a')
    (hδb : δ + b ≤ 1) (X : RegChain) (hX : X.wf = true) (ζ : ℤˣ) (x : Addr) :
    MCExpT θ a b A (CT θ a b θ' a' δ ^ (2 * X.size + 1)) nodeSgn (chosenSet (X.linksAt ζ x))
      (X.At ζ x) :=
  (RegChain.mcexpT hθ0 hθ1 ha hb hab1 hab hA hθ'1 ha' hab1' hab' hδ hδθ hδa hδb X ζ x).mono
    (RegChain.NtreeX_le_CT X hX) (A1_nonneg.trans hA)

/-- The constant `C_T` with the DH23 weights. -/
@[expose] noncomputable def CTη (η : ℝ) : ℝ :=
  CT (1 - η / 8) (η / 4) (1 - η / 2) (1 - η / 16) (5 * η / 16) (η / 16)

/-- **DH21 Proposition 5.1 for regular trees with the weights of DH23** (L955–L969 for couples, L1175
for trees): `θ = 1 - η/8`, `a = η/4`, `b = 1 - η/2`, for `t > s`. -/
theorem RegChain.maincoefT_DH23 {η A : ℝ} (hη : 0 < η) (hη2 : η ≤ 2) (hA : A1 ≤ A) (X : RegChain)
    (hX : X.wf = true) (ζ : ℤˣ) (x : Addr) :
    MCExpT (1 - η / 8) (η / 4) (1 - η / 2) A (CTη η ^ (2 * X.size + 1)) nodeSgn
      (chosenSet (X.linksAt ζ x)) (X.At ζ x) :=
  RegChain.maincoefT (θ' := 1 - η / 16) (a' := 5 * η / 16) (δ := η / 16) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hA (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) X hX ζ x

end WaveTurbulence.ClassJR
