/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.InputRemainder
public import WaveTurbulence.Frozen.Defs.KQstar
public import WaveTurbulence.Frozen.Defs.KTstar
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.RegBound
public import WaveTurbulence.Frozen.Defs.RegChainApp
public import WaveTurbulence.Frozen.Defs.RegChainDecodesTree
public import WaveTurbulence.Frozen.Defs.RegChainJBtree
public import WaveTurbulence.Frozen.Defs.RegChainLonePath
public import WaveTurbulence.Frozen.Defs.RegChainTreeLinks
public import WaveTurbulence.Frozen.Defs.RegCplApp
public import WaveTurbulence.Frozen.Defs.RegCplDecodes
public import WaveTurbulence.Frozen.Defs.RegCplDominantRegChainDominant
public import WaveTurbulence.Frozen.Defs.RegCplJBRegChainJBchain
public import WaveTurbulence.Frozen.Defs.RegCplLinks
public import WaveTurbulence.Frozen.Defs.RegCplMstarRegChainNstar
public import WaveTurbulence.Frozen.Defs.RegCplRegChain
public import WaveTurbulence.Frozen.Defs.RegCplSizeRegChainSize
public import WaveTurbulence.Frozen.Defs.RegCplWfRegChainWf
public import WaveTurbulence.Frozen.Defs.SNormR
public import WaveTurbulence.Frozen.Defs.SpecialSets
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreeNodes
public import WaveTurbulence.Frozen.Defs.TTreePath
public import WaveTurbulence.Frozen.Defs.TimeBox
public import WaveTurbulence.Frozen.Defs.TimeBoxGt
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTParamsN
public import WaveTurbulence.Frozen.Defs.WTPrefix
public import WaveTurbulence.Frozen.Defs.WkeTaylorTerm
public import WaveTurbulence.Frozen.Defs.XNorm00Restr
public import WaveTurbulence.Frozen.Defs.XNormRestr
public import WaveTurbulence.Provider.RegularAsymptotics

/-!
# regularAsymptotics

Wave B tier B2 (WaveB2-Statements.lean), source: L1145–L1232; WAVE-B v2 §4.11; T (regref1-3); DH21 Lemma 7.3. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

-- FROZEN_ANCHOR_PREFIX_BEGIN
/-- **B2.1 `regularAsymptotics`** (T Props `regref1`–`regref3`, L1145–L1232; F11; WAVE-B v2 §4.11).
Under (Π), for `0 ≤ p < 𝔇`, `0 ≤ r ≤ p`, a remainder `R_r` with `‖R_r‖_{𝔖^{40d,40d}} ≤ L^{-θ_r}`, inputs
`F_r = φ(δr) + R_r` and every `n ≤ N_{p+1}^4`:
1. for every well-formed couple code `𝒬` of order `2n` and every layered couple decoded by it with all
   nodes in layer `r`: `‖K*_𝒬 - (K*_𝒬)_app‖_{𝔛^{η,30d,30d}([r,r+1]²)} ≤ C₁(C₁δ)^n L^{-(γ₁-√η)}`
   (for non-dominant `𝒬`, `(K*_𝒬)_app = 0`: this is the bound on `K*_𝒬` itself);
2. for every well-formed tree code `𝒯` of order `2n` and every layered paired tree decoded by it with all
   nodes except the lone leaf in layer `r` and the lone leaf in layer `q' ≤ r`: the same bound for
   `K*_𝒯 - (K*_𝒯)_app` in `𝔛^{η,30d,0}(([r,r+1]×[q',q'+1]) ∩ {t > s})`;
3. for dominant codes and special `Z`: `‖𝒥ℬ*‖_{𝔛^{1-η}(ℬ)} ≤ C₁C₁^n` and `‖ℳ*‖_{𝔖^{30d,30d}} ≤ C₁C₁^n`
   (trees: `𝔛^{1-η}(ℬ_𝒯)`, `𝔖^{30d,0}`); both are real valued by definition;
4. (regref1-5 corrected, F11) if `r = p` and `R_p = 0`: for `t ∈ [p, p+1]`, `k ∈ ℝ^d`,
   `∑_{𝒬 dominant, n(𝒬) = 2n} (K*_𝒬)_app(t,t,k) = 𝒰^{(p)}_n(t,k)` (a finite sum, probe
   `finite_dominant_codes`).
Deviations: (D1) `(K*)_app` is defined by the explicit recursions (route R4; `RegCpl.app`); the source's
"`𝒥ℬ*` depends only on `𝒬`" is then a definition, its agreement with DH21's construction DH21 Props 7.5,
7.7; (D2) `ℬ` for trees as stated (F11); (D3) item 4 with `app`, not `K*` (F11); (D4) regular objects are
quantified as pairs (code, carrier) with `Decodes` (structure data = the unique code,
`existsUnique_regCpl_decodes`); (D5) inputs with finite `𝔖^{40d,40d}` norm instead of `C^∞` (O3); (D6) the
order range `n ≤ N_{p+1}^4` (F33, route R14; the main proof risk); (D7) the special-subset weight of
`(K*)_app` is `∏_{𝔫∈Z} (−ζ_𝔫 π i)^{-1}`, not T (regref1-3)'s `(ζ_𝔫 π i)^{-1}` (F61, confirmed: DH21 Lemma 7.3
sign error; trace `/home/scott/wt-scratch/wke/F61-sign-trace.md`; B2-CL-11). Item 4 is unaffected, since `|Z|`
is constant on each equivalence class. -/
theorem regularAsymptotics : WTPrefix fun P =>
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
          (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p n t k : ℂ)) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact WaveTurbulence.Provider.regularAsymptotics
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end WaveTurbulence
-- FROZEN_ANCHOR_SUFFIX_END
