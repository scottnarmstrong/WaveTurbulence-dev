# Audit — Wave A draft of Theorem 1.1 (`scratch/Draft.lean`)

Auditor: `wt-orch` (Opus), refute-first. Date: 2026-11-03.

- Audited file: `scratch/Draft.lean`, sha256 `9e53e660…aa82` (123 lines).
- Source: `paper/source/WKE-Longer_times_Final_arXiv.tex`, sha256 `493eef6b…727cb`. Cited lines refer to this file
  unless prefixed (GIT20 = `src-1711.05587/Kin8.tex`, DH21 = `src-2104.11204/Inventiones-Final_Version.tex`,
  DH19 = `src-1912.09518/Derivation-of-WKE-11.tex`).
- Toolchain: Lean v4.35.0, Mathlib v4.35.0. The draft elaborates with only the expected `sorry` warning.

**Verdict: NOT APPROVED. One REQUIRED fix (R1).** As drafted, `main` is **false**: the hypotheses make each `g n`
only a.e.-measurable, and then the conjunct `MeasurableSet (solvableEvent …)` can fail (counterexample below; the
hypothesis gap is checked in Lean by probe P6). With R1 applied, I found no other WRONG item. All other declarations
and binders are FAITHFUL or disclosed readings that I accept.

## 1. Verdict table

### Declarations

| Decl | Verdict | TeX | Reason |
|---|---|---|---|
| `Mom` | FAITHFUL | L310 | `EuclideanSpace ℝ (Fin d)`. The inner product is `∑ kʲℓʲ`. |
| `latticePoint` | FAITHFUL | L286 | `n/L ∈ (L⁻¹ℤ)^d = ℤ_L^d`. |
| `collisionOp` | DEVIATION (disclosed reading; accepted) | L300–L307, (C.5) L2503 | See §1a. The signs of the four terms, the factor `(2‖ℓ₁‖)⁻¹` and the hyperplane measure are all correct. Probe P1 shows that `volume` on `↥(ℝ ∙ ℓ₁)ᗮ` is `measureSpaceOfInnerProductSpace` (orthonormal parallelepipeds have volume 1), i.e. (d−1)-dimensional Lebesgue measure. It is **not** `Measure.Subtype.measureSpace` (a comap, which would be 0 and make 𝒦 ≡ 0). |
| `IsWKESolution` | FAITHFUL (equivalent reformulation) | L299–L301, L598–L601, L2526–L2528 | See §1b. It admits no spurious solutions. |
| `partialDeriv`, `normLaplacian` | FAITHFUL | L285 | `Δ = (2π)⁻¹ ∑ ∂²ⱼ`. `deriv` along `Function.update` is the true partial derivative for the smooth `u t`. |
| `torusFourierCoeff` | FAITHFUL | L286–L288 | It has the `L^{-d/2}` prefactor, the phase `e^{-2πi k·x}` with `k = n/L`, and integrates over the box `[0,L]^d` with Lebesgue measure. |
| `IsSmoothNLSSolution` | FAITHFUL (disclosed: data imposed through coefficients) | L278–L281, L292–L293, L316 | The equation `I·∂ₜu − Δu + α‖u‖²u = 0` matches `(i∂_t−Δ)u+α\|u\|²u=0`. `u` is C^∞ (`(⊤:ℕ∞)`, smooth, not analytic) on `[0,T]×ℝ^d` and L-periodic. A continuous periodic `u(0)` is determined by its coefficients, and the series (DAT) defines a smooth `u_in` iff its coefficients decay rapidly. So "∃ smooth solution with `û(0)=c`" ⟺ the source event. Sign check: the linear flow is `û ∝ e^{2πi\|k\|²t}`, which is exactly undone by (reducedcoef) L543. |
| `stdComplexGaussian` | FAITHFUL | L294; DH21 L297; DH19 L140 | Circular complex Gaussian with Re and Im iid `N(0,1/2)` (`gaussianReal` takes the variance), so `𝔼g=0` and `𝔼\|g\|²=1`. The circular (not real) reading is forced by the gauge invariance used at L568. |
| `initialCoeff` | FAITHFUL | L292–L293 | `√φin(k)·g_k`. The `sqrt` argument is ≥ 0 under `hφin`. |
| `solvableEvent` | FAITHFUL | L316, L818 | F = "(NLS) has a smooth solution on [0,T]". |

### Binders and conclusion of `main`

| Item | Verdict | TeX | Reason |
|---|---|---|---|
| `d`, `3 ≤ d` | FAITHFUL | L314 | |
| `γ ∈ Ioo 0 1` | FAITHFUL (D2) | L314 | |
| `∃ θ > 0` before `φin` | FAITHFUL | L318, L612 | θ = η²⁰ depends only on (d,γ). |
| `φin : 𝓢(Mom d, ℝ)`, `0 ≤ φin` | FAITHFUL | L294, L314 | |
| `∀ τstar > 0, ∀ φ, IsWKESolution φin τstar φ →` | FAITHFUL (equivalent) | L314–L315, L598 | See §1b. A solution on the closed interval `[0,τ★]` exists iff `τ★ < τmax`, and it is unique. |
| `∃ L₀, ∀ L ≥ L₀` (real L) | FAITHFUL | L316 | "Sufficiently large L". L₀ may depend on φin, τ★ and φ, as in the source (C₂ at L610). Choosing L₀ before (Ω,P,g) is harmless because only the law of g matters (once R1 is applied). |
| `∀ (Ω : Type) [MeasurableSpace Ω] P [IsProbabilityMeasure P]` | FAITHFUL | — | Universe 0. Optionally make it universe-polymorphic (O3). |
| `g`, `iIndepFun g P`, `P.map (g n) = stdComplexGaussian` | **WRONG** → R1 | L294 | The source's "i.i.d. random variables" are measurable. The Lean hypotheses force only `AEMeasurable (g n) P`: `map` of a non-a.e.-measurable function is a Dirac mass, which ≠ a Gaussian, and `iIndepFun` imposes no measurability. P6 exhibits non-measurable `g` satisfying both hypotheses, and §2 R1 turns this into a counterexample to `main`. |
| `α = L^(-γ)`, `T = τstar * (L^(2γ)/2)` | FAITHFUL | L297, L314, L316 | |
| `MeasurableSet F` (added conjunct) | DEVIATION (added; implicit in source) | L316, L818 | The source uses `P(F)` and `E(1_F …)`, which presuppose measurability. **False without R1** (§2). True with R1, but it is a Lean-only proof obligation (Q1). |
| `1 − exp(−(log L)^{40d}) ≤ P.real F` | FAITHFUL | L316; supported by L691 + L612 | `P(F) ≥ P(F_𝔇) ≥ 1−e^{−N_𝔇}` with `N_𝔇 = ⌊(log L)^{40d}⌋^{40d} ≥ (log L)^{40d}` for large L. The proof text at L818 writes the weaker `(log L)^{20d}` (Q3). |
| `∀ U, (∀ ω ∈ F, U ω solves) →` | FAITHFUL (given uniqueness) | L316–L318 | §1c. |
| `∀ t ∈ Icc 0 T, ∀ n` | FAITHFUL | L317 | `sup_{t∈[0,T]} sup_{k∈ℤ_L^d}`. |
| `∫ ω, F.indicator (‖û(U ω t, n)‖²) ∂P` | FAITHFUL | L318, **L576**, L818 | L576 defines "taken assuming an event F" as "with an additional factor 1_F", and the proof (L818) uses `E(1_{F_p}…)`. A conditional-expectation reading differs by at most `C L^d e^{−(log L)^{40d}} ≪ L^{−θ}`, so nothing hinges on the choice. |
| `φ (t/(L^(2γ)/2)) (latticePoint L n)` | FAITHFUL | L317 | `φ(t/T_kin, k)`. The time argument lies in `[0, τ★]`, where φ is constrained. |
| `≤ L^(-θ)` | FAITHFUL | L317 | |

### 1a. `collisionOp` (item 2 of the brief)

- **Change of variables.** Integrating out `δ(k₁−k₂+k₃−k)` and substituting `k₁=k+ℓ₁`, `k₃=k+ℓ₃`, `k₂=k+ℓ₁+ℓ₃` has
  Jacobian 1. It gives `Ω = −2⟨ℓ₁,ℓ₃⟩` (L2503). Lean term i corresponds to (COL) term i, with matching signs:
  `+φ₁(k₁)φ₂(k₂)φ₃(k₃)`, `−φ₁(k)φ₂(k₂)φ₃(k₃)`, `+φ₁(k₁)φ₂(k)φ₃(k₃)`, `−φ₁(k₁)φ₂(k₂)φ₃(k)` (L300–L302).
- **Delta.** Write `ℓ₃ = s·ℓ̂₁ + w` with `w ∈ ℓ₁^⊥`, so `dℓ₃ = ds dw`. Then `δ(2|ℓ₁|s) = (2|ℓ₁|)⁻¹δ(s)`, and δ is even, so
  the sign in `δ(−2⟨ℓ₁,ℓ₃⟩)` does not matter. This agrees with:
  - GIT20 L646–L655: `δ(G) = dσ/|∇G|` with `|∇_{ℓ₃}(2⟨ℓ₁,ℓ₃⟩)| = 2|ℓ₁|`;
  - GIT20 L981: the mollifier `ψ_ε(2(x−p)·(y−p))` with `∫ψ = 1`;
  - DH21 L1630: `μΨ(μΩ) → (∫Ψ)·δ(⟨x,y⟩)`.

  The iterated form `∫dℓ₁ (2|ℓ₁|)⁻¹ ∫_{ℓ₁^⊥}` equals the coarea form on `{⟨ℓ₁,ℓ₃⟩=0} ⊂ ℝ^{2d}`.
- **Edge case `ℓ₁ = 0`.** `(2·0)⁻¹ = 0` and `(ℝ∙0)ᗮ = ⊤`, so the integrand is 0 on a null set. Harmless.
- **Integrability.** For Schwartz inputs and d ≥ 2 all four terms are integrable: `|ℓ₁|⁻¹` is locally integrable, and
  `w ⊥ ℓ₁` gives `|ℓ₁+w| ≥ |ℓ₁|`. So the Bochner integrals take their true values and are not junk 0.
- **Normalization sanity check (independent).** I did a second-order Wick computation from
  `∂ₜa = iαL^{−d}∑e^{2πiΩt}a₁ā₂a₃`. It uses two pairings `k₁↔k₃` and `|∫₀ᵗe^{2πiΩs}ds|² ≈ t·δ(Ω)`, and gives
  `∂ₜ𝔼|a_k|² ≈ 2α²·𝒦(n,n,n)`. So `T_kin = 1/(2α²)` (L297) is consistent with (COL) having no prefactor.

### 1b. `IsWKESolution` versus Prop `wkelwp` (item 3)

The topology of `C([0,τ★]; 𝓢)` is the topology of `C([0,τ★]; Z_{s,m})` for all `s, m`: the norms `Z_{s,m}` (L2515)
generate the Schwartz topology.

**The pointwise ODE implies the mild form.** `τ ↦ 𝒦(φ(τ))(k)` is continuous, because `𝒦 : Z_s³ → L^∞` is bounded
(GIT20 L975–L981). So FTC gives Duhamel in each `k`, and hence in `Z_s`.

**Uniqueness.** The trilinear estimate (L2516) plus Gronwall gives uniqueness in `C([0,τ★]; Z_s)`. So there are no
spurious solutions.

**Existence.** For `τ★ < τmax` the source solution lies in `C([0,τmax); Z_{s,m})` for all s, m (L2526–L2528). It
therefore satisfies the pointwise ODE on `[0,τ★]`.

**No solution for `τ★ ≥ τmax`.** When `τmax < ∞`, a solution on the closed interval `[0,τ★]` would keep
`‖⟨k⟩^sφ‖_{L²}` bounded up to τmax, contradicting the blow-up criterion (L599).

**Conclusion.** "∀ τ★>0, ∀ φ solving on [0,τ★]" ⟺ "τ★ ∈ (0,τmax), φ the solution".

### 1c. Selection device and measurability (item 6)

**The integrand is canonical.** For `ω ∈ F`, smooth periodic solutions on `[0,T]` are unique (L² energy estimate on
the difference). So `1_F(ω)·|û(U ω t, n)|²` does not depend on the choice of `U`, and a non-measurable selection
cannot occur.

**It is measurable once R1 is applied.** The integrand equals `Φ_{t,n}(g(ω))·1_S(g(ω))`, where:
- `S ⊆ ℂ^{ℤ^d}` is the solvable set;
- `Φ_{t,n}(c) = |û_c(t,n)|²`, with `û_c` the Fourier coefficient of the solution with data `c`;
- `g` is the joint map `ω ↦ (g_n(ω))_n`.

`S` is Borel: it is `h^∞ ∩ {lifespan_{H^s} > T}`, the second set is open in the separable space `h^s`, and `h^s` is
a Borel subset of the product σ-algebra. `Φ` is continuous on `S` in the `h^s` topology. So the integrand is
measurable and the Bochner integral is not junk.

**Integrability.** Mass conservation gives `|û(t,n)|² ≤ ∑_m φin(m/L)|g_m|²`, and its mean is finite.

## 2. REQUIRED fixes

### R1 — add measurability of the Gaussians (fixes a falsity)

Exact change in `main`:

```lean
        (g : (Fin d → ℤ) → Ω → ℂ),
        (∀ n, Measurable (g n)) → iIndepFun g P → (∀ n, P.map (g n) = stdComplexGaussian) →
```

**Counterexample to the current draft.** Let θ, L₀ be arbitrary. Take `φin(k) = e^{−|k|²}`, which is Schwartz and
positive. Take any `τ★ > 0` small enough that the WKE has a solution φ on `[0,τ★]` (Prop `wkelwp`), and let
`L = max(L₀, 1)`.

The probability space:
- Let `Ω' = ℂ^{ℤ^d} × Bool`, with the σ-algebra pulled back along `Prod.fst`. Every measurable set then has the form
  `A × Bool`.
- Let `P` be the push-forward of `P₀ = infinitePi stdComplexGaussian` under `ω ↦ (ω, false)`.

The Gaussians:
- Set `g_n(ω,b) = ω_n`, except `g_n(0,true) = φin(n/L)^{−1/2}`.
- `g` differs from the canonical family only on `{0} × Bool`, a P-null set. So `iIndepFun g P` holds
  (`iIndepFun.congr'`), and `P.map (g n) = stdComplexGaussian` holds (`Measure.map_congr`).
- Probe P6 checks all of this in Lean, using the value 1 instead of `φin^{−1/2}`; the proof is identical.

Why F is not measurable:
- `(0,false) ∈ F`: the data are 0 and `u ≡ 0` solves (probe P3′).
- `(0,true) ∉ F`: all coefficients equal 1. That is not square-summable, contradicting Bessel's inequality for a
  continuous `u(0)` on `[0,L]^d`.
- A measurable F would have the form `A × Bool`, and then `(0,false) ∈ F ⇒ (0,true) ∈ F`. So `F` is not measurable.

The first conjunct therefore fails for every `L ≥ L₀`, and `main` as drafted is false.

R1 is the faithful repair, because random variables are measurable. A weaker alternative, replacing the conjunct by
`NullMeasurableSet F P`, also kills this counterexample, but it leaves the hypotheses unfaithfully weak. I recommend
R1 and keeping `MeasurableSet F` (see Q1).

## 3. OPTIONAL suggestions

- **O1.** Write the law hypothesis as `HasLaw (g n) stdComplexGaussian P` (Mathlib idiom), together with R1's
  `Measurable`.
- **O2.** Name the repeated quantities, e.g. `kineticTime L γ := L ^ (2*γ) / 2` and the final time
  `τstar * kineticTime L γ`. `solvableEvent L (L^(-γ)) (τstar * …) φin g` currently appears four times.
- **O3.** Make Ω universe-polymorphic (`Ω : Type u`). This is a free strengthening.
- **O4.** Add early characterization lemmas as statement tests; these are not definition changes:
  - (a) `collisionOp` equals the GIT20 mollified limit
    `lim_{ε→0} ∫∫ ψ_ε(2⟨ℓ₁,ℓ₃⟩)(…) dℓ₁dℓ₃` for Schwartz inputs;
  - (b) `torusFourierCoeff L (x ↦ L^{−d/2}e^{2πi m·x/L}) n = 𝟙_{n=m}`;
  - (c) `stdComplexGaussian` has mean 0, `∫‖z‖² = 1`, and is invariant under `z ↦ e^{iθ}z`.
- **O5.** Prove a non-dependent formula for the inner hyperplane integral, e.g. via the orthogonal projection and a
  unit slab. This eases measurability and continuity in ℓ₁, which the dependent subtype `↥(ℝ ∙ ℓ₁)ᗮ` makes awkward.

## 4. Open questions for the author

- **Q1.** `MeasurableSet F`, and a.e.-measurability of the integrand, are proof obligations the source never
  discharges. They need Borel-ness of the solvable set and of the solution map, via H^s local well-posedness and
  lower semicontinuity of the lifespan. Keep them in the statement (recommended; true after R1), or weaken to
  `NullMeasurableSet`?
- **Q2.** Confirm the reading "expectation taken assuming F" = `E(1_F ·)`. L576 defines the phrase this way, and
  L818 uses it.
- **Q3.** The proof of Theorem 1.1 (L818) states `P(F) ≥ 1 − e^{−(log L)^{20d}}`, but the theorem states 40d
  (L316). The draft follows L316, which Prop `propansatz`(1) (L691) supports through
  `N_𝔇 = ⌊(log L)^{40d}⌋^{40d}`. Is that acceptable?
- **Q4.** Confirm the closed-interval reading "smooth solution on [0,T]" (L316, L818).

## 5. Non-vacuity probes (`scratch/Probes.lean`, untracked, sha256 `8413ce41…7905`)

The file contains the draft's definitions verbatim (lines 1–99) plus the probes below. It elaborates with **no
errors, no warnings and no `sorry`**:

```
nice -n 5 lake env lean scratch/Probes.lean
```

| Probe | Statement | Status |
|---|---|---|
| P1a | `inferInstance : MeasureSpace ↥(ℝ ∙ ℓ)ᗮ` is `measureSpaceOfInnerProductSpace` (by `rfl`) | compiled |
| P1b | every orthonormal basis of `ℓ^⊥` has `volume (parallelepiped b) = 1` | compiled |
| P1c | `collisionOp` unfolds (`rfl`) with `∂(@volume _ measureSpaceOfInnerProductSpace)` | compiled |
| P2 | `IsProbabilityMeasure stdComplexGaussian` | compiled |
| P3 | `IsSmoothNLSSolution L α T 0 0` (u = 0, zero data) | compiled |
| P3′ | `solvableEvent L α T φin 0 = univ` | compiled |
| P4 | `IsWKESolution 0 τstar 0` (φ ≡ 0, zero data) | compiled |
| P5 | hypotheses satisfiable: `Ω = ℂ^{ℤ^d}`, `P = infinitePi stdComplexGaussian`, `g n = eval n` (measurable, `iIndepFun`, law) | compiled |
| P6 | ∃ (Ω,P,g) with `iIndepFun g P`, `∀ n, P.map (g n) = stdComplexGaussian`, and `∀ n, ¬ Measurable (g n)` | compiled |

Taken together, P4 and P5 show that the hypotheses of `main` (after R1) can be satisfied, with φin = 0 and any
τ★. In that case `F = univ` by P3′.
