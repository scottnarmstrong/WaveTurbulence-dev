# JR-OPS audit (Task 16a): class J/R operators, DH21 Def 5.2 and Lemmas 5.3–5.8

Auditor: `wt-orch` (Opus), refute-first. Date: 2026-11-03.

## Subject and sources

**Subject.** Landed `8ecbe39` ("Land w/jr-ops"), `WaveTurbulence/Foundations/ClassJR/**`. Design log:
`/home/scott/wt-scratch/wke/JR-OPS-design.md`.

**DH21 (`Inventiones-Final_Version.tex`).** With the shared theorem counter:
- Prop 5.1 `maincoef` (L936–L944);
- Def 5.2 `defclassjr` (L955–L964);
- Lemmas 5.3 `regchainlem1` (L966), 5.4 `regchainlem2` (L1001), 5.5 `regchainlem3` (L1027), 5.6 `regchainlem4`
  (L1040), 5.7 `regchainlem5` (L1062), 5.8 `regchainlem6` (L1069–L1081);
- the consumers: Lemmas 7.1–7.3 (L1715–L1745), Prop 7.4 `maincancel` (L1748), Props 7.8–7.10 (L1838–L1895).

**DH23.** `Revision_Submit.tex` L955–L969: the weights `1−η/8` and `1−η/2`.

## Verdicts

| Item | Verdict |
|---|---|
| Def 5.2 (class J, class R, norms) | **PASS**, with deviations D1, D3, D4 below; all are strengthenings or harmless |
| Lemma 5.3 `ClassJ.comp`, `ClassJP.comp` | **PASS** |
| Lemma 5.4 `ClassJ.comp_R`, `ClassR.comp_J` (and the `P` forms) | **PASS** |
| Lemma 5.5 `ClassR.comp_R` (and the `P` form) | **PASS** |
| Lemma 5.6 `ClassJP.iker_comp_iker` | **PASS** |
| Lemma 5.7 `ClassRP.iker_comp_iker` | **PASS** |
| Lemma 5.8 `iker_comp_decompP` / `iker_comp_decomp` | **PASS**. D5 (the averager `½·1_{[-1,1]}`) does **not** require a redo. One watch item (W1). |

## Def 5.2 against the Lean definitions

**`ClassJ θ A N T`.** On the triangle (`KEqOn`), `T α` is a finite sum of basic kernels
`∫ m(α,γ) J_{ℓ(α);γ₁,γ₂} dγ`, where:
- `ℓ` is a bundle with coefficients in `{−1,0,1}` (`IsBundle`);
- the norms `c_i` satisfy `Σ c_i ≤ N`.

This matches (typeJ0) and DH21's "linear combination, norm = inf Σ|a_ℓ|", with the coefficients absorbed into the
symbols.

**`ClassR`.**
- The kernel is `χ_∞(ℓ₁+εα₁+γ₃)/(ℓ₁+εα₁+γ₃) · e^{πi(ℓ₂+εα₁)(t−s)} e^{πi(γ₁t+γ₂s)}` (`rker`, with
  `chiInvR = Fourier.chiInfinity x / x`).
- The symbol does not depend on the special variable `α₁ = α none`, and `ε = ±1`.
- This matches (typeR0).

**Weights.**
- `wJ = (1+Σ|α_j|+|γ₁|)^θ`: no `γ₂`, as in (typeJ2).
- `wR = (1+Σ|α_j|+|γ₁|+|γ₃|)^θ`: no `γ₂`, as in (typeR2).

**`μ[E]`.** The parametric `ClassJP`/`ClassRP` have bounds uniform in `p` ("for all `μ[E]`") and joint measurability
in `(p, α, γ)`. This is required by Prop 5.1, which integrates over `μ = λ_a+λ_b` (my Infra-review-3 Q1).

**Variable bookkeeping matches "the variables in different operators are different".**
- Compositions act on `ι₁ ⊕ ι₂`, `ι₁ ⊕ Option ι₂`, and so on.
- 5.6 and 5.7 add a fresh special variable `α none`. In 5.7 the inner operator's special variable becomes an ordinary
  variable, and the output has special index 1 only.

**Headline statements.** Each composition lemma has the form
`ClassX θ A N₁ T₁ → ClassY θ A N₂ T₂ → ClassJ θ A (C·N₁·N₂) (kcomp …)`, with the **same** `A`, explicit `C`, and
`A ≥ A0`. Lemmas 5.6–5.8 decompose `kcomp (kcomp (iker (εα₁)) T) (iker (μ₁−εα₁))` into a class J part plus a class R
part, each parametric in `(p, μ₁)`. This is exactly DH21's content, with norms `≤ C‖·‖`.

## The six reported deviations

**D1. The Gevrey bound `N·A^k·(2k)!`, with the α-derivative measured in ℓ¹.**
- `dnorm k` is the operator norm of the `k`-th Fréchet derivative on `ℓ¹(ι)`. This dominates `|∂^ρ m|` for every
  `|ρ| = k`, so the Lean norm bound implies DH21's per-ρ bound (with constant `N A^k`).
- The factor `A^k` is necessary. DH21's literal normalization `(2|ρ|)!` does not close under Leibniz: the sum
  `Σ_{ρ₁≤ρ} (ρ choose ρ₁)(2|ρ₁|)!(2|ρ−ρ₁|)! ≤ (|ρ|+1)(2|ρ|)!` loses a factor growing with `|ρ|`.
- Lean keeps `A` fixed across every composition; only `N` grows.
- **Effect downstream.** Prop 5.1 then carries `C^n A^{|ρ|}(2|ρ|)!` instead of DH23 (maincoef2)'s `C^n(2|ρ|)!`. Its
  only consumer is DH23 Prop 6.4 (propertypsi2), which is landed in APPROXNT as
  `WordDerivL1 Ψ₁ (k ↦ C₀^n (4k)!)`.
  - Since `A^k(2k)! ≤ K_A (4k)!` with `K_A = sup_k A^k(2k)!/(4k)! < ∞`, the loss is absorbed into `C₀^n` for
    `n ≥ 1`.
  - Pointwise word derivatives are bounded by `dnorm`. **Harmless.**

**D2. The ranges `θ ≤ 1` (Lemma 5.3) and `θ < 1` (Lemmas 5.4–5.8), with constants `C(θ)`.**
- Both DH21's `θ = 1/4` and DH23's `θ = 1 − η/8` (η > 0) lie in `[0,1)`.
- The θ-dependent constants (`Ir (2−θ)` and others) depend on `η` under DH23. That is allowed, since DH23's `C`
  depends on `(d, γ, η)`.
- Proving the lemmas for **every** `θ < 1` also confirms DH23's remark (L969ff) that "a careful inspection" of DH21
  §5 gives the `1−η/8` weight. **PASS.**

**D3. The qualitative `SymReg` in Def 5.2.**
- Symbols must be smooth in `α`, jointly measurable, and satisfy `∫ sup_α ‖D^k m‖ dγ < ∞`. DH21 leaves this
  implicit.
- Every constructor in the package (`ofGen`, `ofGenE`, `ofAny`, the pieces, compositions, reindexing) produces it, and
  no lemma *assumes* class membership of an external object. So it is an internal invariant. **Harmless.**
- Watch item W3 below.

**D4. The `ofAny` smoothing constant `CM0`.**
- DH21 removes Dirac masses in `γ` with (extraid) ("we can always convolve by a decaying analytic function"). That
  silently costs a constant.
- Lean makes it explicit as `CM0 = ∫(1+|σ|)|M₀| · ∫|M₀|`. For example, Lemma 5.8's `𝒥_{α[ ],μ₁}` has norm `CM0`
  instead of 1.
- The constant is absorbed by the `C` of each lemma and by `C^m` in 5.9–5.10. **Harmless.**

**D5. Lemma 5.8 is proved with the averager `ρ = ½·1_{[−1,1]}` instead of DH21's "compactly supported Gevrey 2
`M`".**

- **Where ρ enters.** Only inside term III: replacing `χ_∞(εα₁)/(εα₁)` by its average
  `∫ρ(g) χ_∞(εα₁+g)/(εα₁+g) dg`.
  - The averaged part becomes the class R symbol `m(γ₃) = ρ(γ₃)/(πi)` (`rhoc`).
  - The difference becomes the class J error, whose α₁-symbol is `chiInvR(εα₁) − chiInvR(εα₁+g)`.
- **Def 5.2 imposes no regularity in γ.** (typeR2) differentiates only in `α`, and `rhoc` does not depend on `α`.
  - The error symbol's α-derivatives fall on `chiInvR`, which is Gevrey-2 (`chiInvR_gevrey`).
  - So DH21's Gevrey choice of `M` is unnecessary, and the indicator gives the same class J and class R
    memberships.
- **The prefactor is Wave B's `chiInfinity`.** The output is
  `phiR (ε·α₁) · T₀ + T_J + T_R`, where `phiR x = chiInvR x / (πi)` and `chiInvR = Fourier.chiInfinity x / x`.
  - `phiR_sign` gives `phiR(εx) = χ_∞(x)/(επix)`, using `chi0_even`.
  - `Fourier.chi0 = smoothTransition(2−2|x|)` is pointwise equal to Wave B's `chi0` (snapshot-5
    `WaveB1-Bridges.chi0_eq_fourier_chi0`).
  - So the χ_∞ that Lemma 5.10, and hence Prop 5.1's (maincoef1), will inherit is already `chiInfinity`.
- **Must the (maincoef1) χ_∞ be `chiInfinity` for the consumers? Yes, and it already is.**
  - **TARGET `regref` route (RA1 / J5).** The Z-factors of (maincoef1), evaluated at `α = δL^{2γ}⟨x,y⟩`, become the
    profile `Ψ = ∏_{j∈J} χ_∞(Ω_j)/Ω_j · Ψ₁` of DH23 Prop 6.4 (propertypsi1). The landed APPROXNT builds that profile
    with `Fourier.chiInfinity` (`resProfile`). For `dh23_prop_6_4` to apply without being re-proved, Prop 5.1 must
    produce literally `Fourier.chiInfinity`.
    - The Wave B statements (`regref1-3`, `𝒥ℬ*` by explicit recursion, `ℳ*` with `pvResonantIntegral`) contain
      no χ_∞ themselves. They are cutoff-free limits.
  - **J4 (Prop 7.4) and J6 (Lemma 7.3 → Props 7.5–7.10).** These need of χ_∞ only:
    - evenness (Lemma 7.3's "by symmetry, `[G]∫ χ_∞(α)/α · K** = 0`");
    - (additionvanish), the translation identity, which holds for any bounded cutoff equal to 1 near ∞;
    - Gevrey regularity (Prop 5.1 Case 2's translated factors, absorbed into class J).

    `chiInfinity` has all three properties.
- **Conclusion: Lemma 5.8 need not be redone.** The averager `ρ` is invisible outside the class R and class J pieces
  of term III. Those pieces are consumed only through their class memberships and norms, and through the exact
  kernel identity (`KEqOn`). Nothing downstream sees `ρ`.

**D6. Explicit constants** (`A0`, `CJJ`, `CJR θ`, `CRR θ`, `C56J θ`, `C57J θ`, `C58J θ`, `CM0`, …). These strengthen
DH21's unspecified `C`. **PASS.**

## Watch items for J2 and J3, and for J4 and J6 (not defects of the landed lemmas)

**W1. The explicit `T₀` in Lemma 5.8 is hidden.**
- `iker_comp_decompP` states `∃ T₀ TJ TR, ClassJP … T₀ ∧ …`. The proof actually has
  `T₀ μ _ t s = −jker 0 0 μ t s = −I_μ` on the triangle (`exists_piece_58_0`).
- DH21 Lemma 7.3 (dominant chains, used through Props 7.5–7.10, packet J6) computes `∫ K̃ dα[W]` using the
  **explicit** operator `I_{μ_j}` at `j ∈ Z`. A class J operator with no variables is not enough for that
  computation.
- **Recommendation:** expose `∀ μ t s, t,s ∈ [0,1] → T₀ μ isEmptyElim t s = −jker 0 0 μ t s` in
  `iker_comp_decompP`/`iker_comp_decomp`. This is a one-line addition: `hk0` already proves it. Carry the explicit
  `j ∈ Z` factor through Lemma 5.10 (J2).

**W2. A candidate sign error in DH21 Lemma 7.3, to be resolved before B2.1 freezes.**

**The two versions disagree.**
- Directly from the definitions, the kernel of `X = I_{εα}I_{μ−εα}` is `e^{πiμs}(e^{επiα(t−s)} − 1)/(επiα)`.
- Its `χ_∞` part therefore contains `−χ_∞(α)/(επiα) · I_μ`. This is:
  - DH21 Lemma 5.8's own proof term `II = −χ_∞(εα₁)/(επiα₁) J_{0;0,μ₁}`, with `J_{0;0,μ} = I_μ`;
  - and Lean's **machine-checked** `T₀ = −jker 0 0 μ`, inside the `KEqOn` identity of `iker_comp_decompP`.
- This coefficient of `Φ(εα)` cannot be moved into the class J/R parts. `Φ(εα)·I_μ` is not integrable in `α`. A class
  R kernel always carries the phase `e^{πi(ℓ₂+εα₁)(t−s)}`, which depends on `α₁`.
- DH21 Lemma 7.3 (L1737) instead writes `+χ_∞(α_j)/(ε_jπiα_j) I_{μ_j}`, and in its proof `I*` keeps `+I_{μ_j}`
  for `j ∈ Z`.

**The consequence.**
- DH21 sets `ε_j^+ = ζ_{𝔫_a^+}` (L930), with no extra sign.
- Hence (regchaincalref) should read `∫K̃ = (−1)^{|Z|} ∫ e^{πi(μ₁t₁+⋯)+πiλ₀t_m}`.
- DH21 Prop 7.5 and TARGET (regref1-3) state that `𝒥ℬ*_Q` "does not depend on Z". That then holds only up to
  `(−1)^{|Z|}`, unless the sign convention `α_𝔫 = ±δL^{2γ}Ω_𝔫` inside `ℳ*_{(Q,Z)}` compensates it. A minus sign there
  would flip each `Z` factor.

**Why it matters.**
- The final WKE identification is probably unaffected: Z = ∅ terms are unchanged, and Prop 7.8 cancels the Z ≠ ∅
  classes with a sign that is uniform within each class.
- But **B2.1 item (1)** bounds `K*_Q − Q.app` **per couple**, and the Z ≠ ∅ terms of `Q.app` (B2 `RegCpl.app`, weight
  `∏_{Z} (ζπi)⁻¹`) are not small individually. A sign error there would make that frozen statement false.

**Recommendation.**
- Log this as a FINDINGS candidate now.
- Before freezing B2.1, have the B2 drafter (or J3) trace the sign of each `Z` factor:
  - from (newsum1) (L1674: `χ_∞(2δL²⟨x,y⟩_β)/…`), through the p.v. limit, into `ℳ*`;
  - against the Lean-proved `−I_μ`.
- A second per-node sign source must be tracked together with the first: with `k₂ = k₁+k₃−k`,
  `Ω = |k₁|²−|k₂|²+|k₃|²−|k|² = −2⟨k₁−k, k₃−k⟩`. Whether the two signs cancel is exactly what needs checking.

**W3. Prop 5.1's induction must carry regularity.** Its Lean statement must carry the `SymReg`-type regularity of
`𝒞`: smooth in `α`, jointly measurable in `(λ, α)`, and the domination clause. Otherwise the induction hypothesis
cannot be fed back through `ofGen`/`ofAny` into class J or class R.

**W4. The λ₂ weight must come from J3.**
- DH23 (maincoef2) weights `⟨max(λ₁,λ₂)⟩^{1−η/8}`, but the class J weight omits `γ₂`, as in DH21.
- So the λ₂ weight has to come from the structure in J3 (DH21's proof pairs the two trees). Do not expect it from a
  single class J operator.

## Build and axioms (my own compile)

- I compiled the 58-module closure of `Lemma53–58`, `ParamComp`, `ParamJR2` and `JRChain` from this worktree's
  sources (main `017cff0` merged), one `lake env lean` at a time: 0 errors, 0 `sorry`.
- `scratch/Task16a-jr-axioms.lean` (`df862a08d74a…`) gives `[propext, Classical.choice, Quot.sound]` for:
  - `ClassJ.comp`, `ClassJ.comp_R`, `ClassR.comp_J`, `ClassR.comp_R`, and their `ClassJP`/`ClassRP` forms;
  - `ClassJP.iker_comp_iker`, `ClassRP.iker_comp_iker`, `iker_comp_decompP`, `iker_comp_decomp`;
  - `ClassJRP.iker_comp_iker`, `ClassJRP.comp`, `phiR_sign`.
- `Lemma58.lean`: `5513e9879804…`.
