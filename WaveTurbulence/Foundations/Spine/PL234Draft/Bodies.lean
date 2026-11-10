/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SpineInputs

/-!
# The parameter prefix with a larger constant `C₁`

The spine gates `CoherentApproximationGate` and `CoherentTaylorGate` and the B2.1 anchor
`RegularAsymptoticsGate` are `WTPrefix` statements, so each chooses its own `C₁` after the data. TARGET's
`C₁` is "an arbitrary large constant" (L608): products of the single-layer bounds of B2.1 have more
factors of `C₁` than one. `wtPrefix_transfer` proves a `WTPrefix` statement from another one, with
`C₁` replaced by `g C₁` and `η₀` shrunk to at most `ηmax`.

`B21Body` is the body of `RegularAsymptoticsGate` (`regularAsymptotics_gate_eq`: `rfl`).
-/

@[expose] public section
open WaveTurbulence.Induct

open Set

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine

/-- The body of the B2.1 anchor `RegularAsymptoticsGate` (text of the B2 anchor). -/
def B21Body (P : WTParams) : Prop :=
    ∀ p : ℕ, p < P.D → ∀ r : ℕ, r ≤ p → ∀ R : Mom P.d → ℝ, InputRemainder P R r →
    ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 →
      let F : Mom P.d → ℝ := fun k => P.φ (P.δ * r) k + R k
      -- (1) regular couples
      (∀ Q : RegCpl, Q.wf = true → Q.size = 2 * n → ∀ LG : LayeredGarden 2, Q.Decodes LG.garden →
        (∀ a, LG.layer a = r) →
        XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox r r) Set.univ
          (fun ts k => KQstar P.L P.γ P.δ (fun _ => F) LG (ts 0) (ts 1) k -
            Q.app P.δ r F (ts 0) (ts 1) k) ≤ regBound P n 1) ∧
      -- (2) regular trees
      (∀ X : RegChain, X.wf = true → X.size = 2 * n → ∀ LG : LayeredGarden 1,
        X.DecodesTree LG.garden → ∀ q' : ℕ, q' ≤ r →
        (∀ a : GNode LG.garden.tree, LG.layer a = if a.1.2 = X.lonePath then q' else r) →
        XNormRestr P.η (30 * P.d) 0 (timeBoxGt r q') Set.univ
          (fun ts k => KTstar P.L P.γ P.δ (fun _ => F) LG (ts 0) (ts 1) k -
            X.app P.δ r F (LG.garden.sig 0) (ts 0) (ts 1) k) ≤ regBound P n 1) ∧
      -- (3) the factors
      (∀ Q : RegCpl, Q.wf = true → Q.dominant = true → Q.size = 2 * n →
        XNorm00Restr (V := Unit) (1 - P.η) (timeBox r r) Set.univ
            (fun ts _ => (Q.JB r (ts 0) (ts 1) : ℂ)) ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n) ∧
          ∀ Z ∈ specialSets Q.links,
            SNormR (30 * P.d) (30 * P.d) (Q.Mstar F Z (0, []) (1, [])) ≤
              ENNReal.ofReal (P.C₁ * P.C₁ ^ n)) ∧
      (∀ X : RegChain, X.wf = true → X.dominant = true → X.size = 2 * n → ∀ ζ : ℤˣ,
        ∀ q' : ℕ, q' ≤ r →
        XNorm00Restr (V := Unit) (1 - P.η) (timeBoxGt r q') Set.univ
            (fun ts _ => (X.JBtree r (ts 0) (ts 1) : ℂ)) ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n) ∧
          ∀ Z ∈ specialSets (X.treeLinks ζ),
            SNormR (30 * P.d) 0 (X.Nstar F Z ζ (0, [])) ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n)) ∧
      -- (4) the WKE identity (corrected regref1-5)
      (r = p → (∀ k, R k = 0) → ∀ t ∈ Icc (p : ℝ) (p + 1), ∀ k : Mom P.d,
        ∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.dominant = true ∧ Q.size = 2 * n),
            Q.app P.δ p F t t k =
          (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p n t k : ℂ))

/-- The standing facts on the parameters available inside `WTPrefix` (with the shrunk `η₀`). -/
structure Standing (P : WTParams) (ηmax : ℝ) : Prop where
  d_ge : 3 ≤ P.d
  γ_mem : P.γ ∈ Ioo (0 : ℝ) 1
  η_pos : 0 < P.η
  η_le : P.η ≤ ηmax
  φin_nonneg : ∀ k, 0 ≤ P.φin k
  τstar_pos : 0 < P.τstar
  wke : IsWKESolution P.φin P.τstar P.φ
  C₁_ge : 1 ≤ P.C₁
  ν_pos : 0 < P.ν
  δ_pos : 0 < P.δ
  D_ge : 1 ≤ P.D
  τstar_eq : P.τstar = P.D * P.δ
  C₂_ge : 1 ≤ P.C₂
  L_ge : 2 ≤ P.L

end WaveTurbulence.PL234
