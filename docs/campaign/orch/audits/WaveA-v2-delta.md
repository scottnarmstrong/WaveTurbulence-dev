# Delta audit — Wave A draft v2 (`scratch/Draft-v2.lean`)

Auditor: `wt-orch` (Opus), refute-first. Date: 2026-11-03.

**Scope.** Only the declarations that changed or are new relative to the Task 1 audit (`49d5f8b`):

- `kineticTime`;
- the new binders of `main` (R1, O2, O3);
- `weightedL2Norm`;
- `wkelwp`.

All other declarations are byte-identical to v1, which I checked with `diff`, so their Task 1 verdicts carry over.

**Inputs.**

- Audited file: `scratch/Draft-v2.lean`, sha256 `3bb96094…b18f` (148 lines).
- Source: the same TeX file as Task 1 (sha256 `493eef6b…727cb`). GIT20 is `src-1711.05587/Kin8.tex`.
- Toolchain: Lean v4.35.0, Mathlib v4.35.0. The file elaborates with exactly two warnings, both `sorry`, in `main`
  and `wkelwp`.

**Verdict: APPROVED for the delta.** There are no REQUIRED fixes. R1 is applied correctly, so the Task 1 refutation
no longer applies. I tried to refute `wkelwp` on six fronts and every attempt failed:

- the quantifier order;
- the iff in the existence clause;
- uniqueness;
- the blow-up clause;
- the dimension assumption;
- sign and junk values.

I have three cosmetic optional suggestions and one planning question (Q5), which concerns proof risk rather than
the statement.

## 1. Verdict table

| Item | Verdict | TeX | Reason |
|---|---|---|---|
| `kineticTime α = 1/(2α²)` | FAITHFUL | L297 | Transcribed exactly. At `α = 0` it returns 0 (Lean's 1/0), but that case is never reached: `α = L^{-γ} > 0` for `L > 0`. |
| `main`: `∀ α T : ℝ, α = L^(-γ) → T = τstar * kineticTime α →` | FAITHFUL (equivalent to v1) | L297, L314, L316 | Binders that only fix a value by an equation are the same as substitution. For `L > 0`, `kineticTime (L^{-γ}) = L^{2γ}/2` (probe P7), so `T` and `t / kineticTime α` agree with v1. L₀ is the prover's choice, so `L > 0` can be assumed. |
| `main`: `(∀ n, Measurable (g n)) →` (R1) | FAITHFUL | L294 | "Random variables" are measurable. The R1 change is applied exactly as proposed, before `iIndepFun`. |
| `main`: `Ω : Type u` (O3) | FAITHFUL | — | A universe-polymorphic strengthening. Everything depends only on the law of `g`. |
| `weightedL2Norm s f = √∫((1+‖k‖²)^{s/2} f k)²` | FAITHFUL | L599 (blowuptest), L2515 (`Z_s`); GIT20 L549 | The TARGET uses ⟨k⟩ without defining it (no definition found). GIT20 L549 fixes `⟨x⟩ = (1+\|x\|²)^{1/2}` for `L²_s`, the space the TARGET cites for `Z_s`. Mathlib's `Sobolev` uses the same weight. Any other common choice, such as `1+\|k\|`, is equivalent up to √2 and does not change "= ∞". No junk on Schwartz inputs: probe P8 shows the integrand is integrable for every real `s`, and the square root is taken of a nonnegative number. |
| `wkelwp`: `∃ τmax : ℝ≥0∞, 0 < τmax` first | FAITHFUL | L598 | "There exists a maximal time τmax > 0 (may be ∞)". |
| `wkelwp`: `∀ τ★ > 0, (ofReal τ★ < τmax ↔ ∃ φ, IsWKESolution φin τ★ φ)` | FAITHFUL | L598, L2526–L2528 | §1a. This clause pins τmax down uniquely, as `sup{τ★ : a solution exists}`. |
| `wkelwp`: uniqueness on `[0, τ★]` | FAITHFUL | L598 ("unique solution … in Schwartz class") | It holds for every τ★ > 0 and is vacuous when τ★ ≥ τmax. Proof: Gronwall in `Z_s` via the trilinear estimate (L2516), as in Task 1 §1b. |
| `wkelwp`: blow-up clause | FAITHFUL | L599–L601 | §1b. |
| `wkelwp`: `3 ≤ d` | FAITHFUL | L277 (standing assumption "in dimension d≥3"); GIT20 Remark 2.6 = L592–L594 | The source proposition holds under the paper's standing assumption. GIT20 claims it for every d ≥ 2, so the hypothesis weakens nothing that matters. See Q5 for the proof-burden side. |
| `wkelwp`: no sign assumption on `φin` | FAITHFUL | L598 ("any Schwartz initial data"); GIT20 Thm `main2` L564 | GIT20's `L²_s` local well-posedness, part (i), has no sign hypothesis; positivity is only part (ii). Appendix C only uses `\|𝒦_j(f,g,h)\| ≤ 𝒦_j(\|f\|,\|g\|,\|h\|)`, because each 𝒦_j is a positive trilinear operator (L2502). So signed data is covered. |
| `wkelwp`: junk values | FAITHFUL (harmless junk only) | — | `weightedL2Norm` has no junk on Schwartz inputs (P8). `ENNReal.ofReal` of a negative τ₀ is 0, which is harmless. For τ★ ≤ 0 inside the blow-up clause, `IsWKESolution` degenerates (P10), but the prover chooses τ₀ and can always take `0 ≤ τ₀ < τmax`. |

### 1a. The existence clause is exactly maximality

**τ★ < τmax gives a solution.** The source solution lies in `C([0,τmax); Z_{s,m})` for all s, m (L2526–L2528).
That makes it continuous into 𝓢 on `[0,τ★]`. Because 𝒦 maps `Z_s³` boundedly into `L^∞` (GIT20 L976), the Duhamel
form gives the pointwise ODE, so the restriction satisfies `IsWKESolution` (Task 1 §1b).

**A solution gives τ★ < τmax.** Suppose a Schwartz solution exists on the closed interval `[0,τ★]` with τ★ ≥ τmax and
τmax < ∞. Then `‖⟨k⟩^sφ‖_{L²}` stays bounded on `[0,τmax)`. That contradicts the blow-up criterion, or equivalently the
extension argument at L2528 ("otherwise we can extend the solution in `Z_{s,0}`").

The two conditions are the same notion of solution: continuity into 𝓢 is equivalent to continuity into every
`Z_{s,m}`, which is how τmax is defined in the source.

### 1b. The blow-up formulation

`∀ M, ∃ τ₀, ofReal τ₀ < τmax ∧ ∀ τ★ ∈ (τ₀, τmax), ∀ φ solving on [0,τ★], M < ‖⟨k⟩^s φ(τ★)‖_{L²}` is exactly
`lim_{τ→τmax⁻} ‖⟨k⟩^sΦ(τ)‖ = ∞`, where Φ is the maximal solution:

- By uniqueness, `φ(τ★) = Φ(τ★)`.
- By the existence clause, a solution exists for every τ★ ∈ (τ₀, τmax), so the inner `∀ φ` is not vacuous.
- The limit is a full limit, not a limsup. The source proof supports this: the local existence time depends only on
  the `Z_s` norm (GIT20 Thm `main2`(i): `T ≳ R^{-2}`). A bounded subsequence near a finite τmax would therefore
  extend the solution past τmax.

The quantifier `∀ s > d/2 − 1` matches L599 and the threshold `s > (d−2)/2` of GIT20 Remark 2.6.

## 2. REQUIRED fixes

None.

## 3. OPTIONAL suggestions

- **O6 (cosmetic).** Rename the section header "Proposition 3.1" to **Proposition 3.2**: in Section 3 the shared
  `thm` counter assigns 3.1 to Definition `defcm` (L570). In the `wkelwp` docstring, the statement occupies
  **L598–L601**; L602–L606 are its proof pointer and the "fix τmax" paragraph.
- **O7 (hygiene, optional).** In the blow-up clause, write `∃ τ₀ : ℝ, 0 ≤ τ₀ ∧ ENNReal.ofReal τ₀ < τmax ∧ …`, or
  `∀ τstar > max τ₀ 0`. This removes the degenerate regime τ★ ≤ 0, where `Icc 0 τ★` is empty or a single point and
  `IsWKESolution` collapses to `φ 0 = φin` (P10). It is not needed for correctness, since the prover picks τ₀.
- **O8 (cosmetic).** In the `weightedL2Norm` docstring, also cite the TARGET's own definition
  `‖φ‖_{Z_s} = ‖⟨k⟩^sφ‖_{L²}` (L2515). `weightedL2Norm s` is exactly `‖·‖_{Z_s}`.

## 4. Open questions for the author

- **Q5 (planning, not statement).** Under D1, `wkelwp` needs GIT20's `L²_s` trilinear estimate in **every** d ≥ 3.
  GIT20 proves it only for d = 3. Remark 2.6 (GIT20 L592–L594) asserts the d-dimensional version with `s > (d−2)/2`
  but gives no proof, and the TARGET relies on exactly that remark (L2516: "Lemmas 4.1–4.3 of [GIT20] (also Remark 2.6
  of [GIT20])"). So for d ≥ 4 the Lean proof has no written source. Accept this as new mathematics for the WKE
  packet, or ask whether a written d-dimensional proof exists elsewhere?
- Q1–Q4 from Task 1 remain open.

## 5. Probes (`scratch/ProbesV2.lean`, untracked, sha256 `1df9a3a4…b146`)

The file contains the v2 definitions verbatim (lines 1–104 and 126–131, without `main` and `wkelwp`) plus the probes
below. It elaborates with **no errors, no warnings and no `sorry`**:

```
nice -n 5 lake env lean scratch/ProbesV2.lean
```

| Probe | Statement | Status |
|---|---|---|
| P7 | `0 < L → kineticTime (L ^ (-γ)) = L ^ (2 * γ) / 2` | compiled |
| P8 | `Integrable (fun k => ((1 + ‖k‖^2)^(s/2) * f k)^2)` for every `f : 𝓢(Mom d, ℝ)` and every real `s` | compiled |
| P8′ | `0 ≤ weightedL2Norm s f` | compiled |
| P9 | for `φin = 0`, `τmax = ⊤` satisfies `0 < τmax`, the existence iff, and the (vacuous) blow-up clause | compiled |
| P10 | `τstar < 0 → φ 0 = φin → IsWKESolution φin τstar φ` (degenerate regime, see O7) | compiled |
