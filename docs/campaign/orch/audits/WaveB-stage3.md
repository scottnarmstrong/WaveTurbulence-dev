# Audit: Wave B stage 3 (tier-B1 statements)

Auditor: independent refute-first statement auditor (Opus). Date: 2026-11-03.
Scope: the 12 tier-B1 statements of the snapshot (plus the optional `cumulantExpansion`) and the way they use the
stage-1/2 definitions. The definitions themselves are audited elsewhere; stage-1 (`docs/campaign/orch/audits/
WaveB-stage1.md`, R1) is cited where it changes a statement's truth value.

## Inputs

| file | sha256 (prefix) |
|---|---|
| `/home/scott/wt-scratch/waveb-snap-1/WaveB1-Statements.lean` | `7a7d2e1e…` (`sha256sum -c SHA256SUMS`: all OK) |
| `WaveB1-Sumint.lean` | `6797ba89…` |
| `WaveB1-System.lean` | `ffb5fb69…` (note: the live `waveb/` copy has since changed; I audited the snapshot) |
| `WaveB1-Core.lean` | `aff86f25…` |
| `WaveB1-Statements-probes.lean`, `DESIGN.md` | per SHA256SUMS |
| TARGET `WKE-Longer_times_Final_arXiv.tex` | `493eef6b…727cb` (line numbers below are this file, "T Lnnn") |
| DH23 `references/src-2301.07063/Revision_Submit.tex` | Lemma A.2 L2048–L2096, Lemma A.3 L2097–L2112 |

**Elaboration.** From `/home/scott/WaveTurbulence-worktrees/orch`, one `lean` at a time, `nice -n 5`, I compiled the
snapshot as modules `WaveBDraft.{Core, System, Statements, Sumint}` into my session scratch root
(`/tmp/claude-1004/-home-scott/749ee92b-8f50-4496-8faa-864f2fd27c53/scratchpad/aud/`). All four compile; the only
warnings are the expected `declaration uses sorry` (6–9 s each, ≈3.9 GB). Two audit files were elaborated against
them (Appendix A):
- `Stage3Probe.lean` (sha256 `aa509dd2…`): `ContDiff ℝ ⊤` = `ContDiff ℝ ω`; a refutation of `nlsAkBridge` item (4)
  (`nlsAkBridge_refuted : False`, whose only extra axiom is the draft's own `sorryAx`; the helper lemmas are
  sorry-free, axioms `[propext, Classical.choice, Quot.sound]`).
- `Stage3Fixes.lean` (sha256 `2d330bc7…`): every replacement statement proposed in §3 elaborates.

## 0. Overall verdict

**NOT APPROVED.** 9 REQUIRED fixes: R1–R7 apply now; R8 blocks freezing B1.12; R9 blocks freezing the optional
`cumulantExpansion`.

Four statements are false or unprovable as drafted:
- **`layergarden`**: it concludes that a function is real-analytic. In this Mathlib `ContDiff ℝ ⊤` is C^ω (R1, R2).
- **`nlsAkBridge`**: item (4) is false. Lean derives `False` from it (R3).
- **`atomCountLemma`**: item (1) is false at `k = 0`, `ε = (+,−)`, γ > 1/2 (R4). The literal TARGET bound has the
  same defect (new finding).
- **`canonicalCharacterization`**: item (2) is false because of stage-1 R1, and the uniqueness of construction data
  is missing for couples and flower gardens (R7).

Three more are not faithful as drafted:
- **`propansatz`**: it demands analytic R_p (R1).
- **`countLemma`**: it claims uniformity in δ that the source proof does not give (R5).
- **`sumint`**: a zero factor in ∏Λ ≤ A^M switches the hypothesis off (R6).

What holds once these are fixed:
- the parameter prefix and its composition;
- the shared `truncSum`;
- the time-parameter treatment;
- `fixedpoint`, `wkeTaylor`, `quadExpSum2`, `quadExpSum3`;
- the chain `main ⇐ propansatz ⇐ {layergarden, fixedpoint, wkeTaylor}`.

## 1. Verdict table

| # | statement | TeX | verdict | REQUIRED |
|---|---|---|---|---|
| B1.1 | `propansatz` | L689–L707 (+L951, F7/F27) | **WRONG as drafted, fixable.** It demands analytic `R p` (`ContDiff ℝ ⊤` = C^ω), which is not in TARGET and not intended. Everything else is FAITHFUL with deviations D1–D7 accepted. It suffices for `main` (§2). | R1 |
| B1.2 | `layergarden` | L761–L779 | **WRONG (false).** (2)(b) concludes that the couple remainder is real-analytic, which is false for compactly supported φin (§4.2). Even C^∞ is not implied by the hypotheses. Otherwise FAITHFUL with D1–D5. | R1, R2 |
| B1.3 | `fixedpoint` | L780–L794 | **FAITHFUL** (D1–D4 accepted). Only its hypothesis `AnsatzAt` inherits R1, which makes it weaker, not wrong. | (R1 via `AnsatzAt`) |
| B1.4 | `nlsAkBridge` | L540–L566, L817–L819 | **WRONG (false, Lean-refuted)**: item (4) asks measurability for all t ∈ ℝ. Items (1)–(3) are FAITHFUL; I re-derived the phase conventions against the frozen normalized Laplacian (§4.4). | R3 |
| B1.5 | `wkeTaylor` | L749–L758 (F10) | **FAITHFUL** (deviations: conjunct (0), time parameter). | — |
| B1.6 | `sumint` | L1595–L1640 | **DEVIATION**: D1–D7 acceptable. One junk hazard: `∏ Λ_v ≤ A^M` with some `Λ_v = 0`. | R6 |
| B1.7 | `countLemma` | L2459–L2466; DH23 A.2 | **DEVIATION, not acceptable as drafted.** L₀ comes before δ (uniform in δ ∈ (0,1]); DH23's own bound needs L ≥ L₀(δ). | R5 |
| B1.8 | `atomCountLemma` | L2467–L2478; DH23 A.3 | **WRONG (false)** at `nk = 0`, `ε = −1`, γ > 1/2. | R4 |
| B1.9 | `quadExpSum2` | L970–L977 | **FAITHFUL** | — |
| B1.10 | `quadExpSum3` | L1554–L1593 | **FAITHFUL** | — |
| B1.11 | `canonicalCharacterization` | L657–L668, L888–L897, L2259–L2263 | **WRONG.** (2) is false (stage-1 R1 counterexample), and (3)/(4) lack uniqueness. Items (1), (3), (4) existence parts: FAITHFUL. | R7 |
| B1.12 | `layergardenFlower` | L2273–L2305 | **DEVIATION, not sufficient for its consumer.** It lacks the M₁/M₂ cutoffs and the Dirac (∂_t, ∂_s) variants that `fixedpoint`'s proof needs (L2312, L2320–L2338). Its core estimate is FAITHFUL. | R8 (+R1 via `RemainderBound`) |
| opt | `cumulantExpansion` | L727–L730, L798–L804 | **WRONG (false)**: the N-range drops gardens with large attached gardens. | R9 (if frozen) |

## 2. Composability (the questions of the brief)

**Parameter prefix (Π), F5.** `WTPrefix` is ∀d∀γ ∃η₀∀η ∀φin∀τ★∀φ ∃C₁ ∃ν₀∀ν ∃δ₀∀δ ∀𝔇 (τ★ = 𝔇δ) ∃C₂ ∃L₀∀L. This is
exactly C₀ → η → 𝔆 → C₁ → ν → δ (𝔇) → C₂ → L, and stage 1 approved it.

The variants place their extra parameter consistently:
- `WTPrefixA` (`sumint`) puts A right after η, so C₁ may depend on A and η₀ may not. That is right: A only enters
  through the factor (∏Λ)^d ≤ A^{dM}, which is absorbed into (C₁δ^{−1/2})^M (T L1625).
- `WTPrefixP` (B1.12) puts P after ν and before δ (§5, Q7).

Every B1 statement is monotone in C₁, C₂ and the thresholds, so the conjunction lemma of Q3 holds.

**`main` ⇐ `propansatz` + `nlsAkBridge`.** Choose:
- η := η₀(d, γ) and θ := η^{20};
- ν := ν₀, then δ ≤ δ₀ and 𝔇 = τ★/δ;
- then C₂ and L₀.

Then:
- F_𝔇 is measurable and symmetric, with P(F_𝔇) ≥ 1 − e^{−N_𝔇} ≥ 1 − e^{−(log L)^{40d}}.
- On F_𝔇 ∩ {data rapidly decreasing} (full measure), `nlsAkBridge` (2) gives a smooth solution. With (3) and the
  ∀U device, U ω t = u_ω t and |û(t,n)| = |a_n(t/(δT_kin))| on [0, T].
- (4) (after R3) gives measurability of the integrand.
- For s ∈ [p−1, p], item (2′) of `AnsatzAt p` gives |E[1_{F_p}|a_n(s)|²] − φ(δs, n/L)| ≤ 2L^{−θ_p}. This is ≤ ½L^{−θ}
  for large L, since θ_p = η^{20}(1+2^{−p}) > θ.
- The events F_p and the solvable event differ by probability ≤ Σ e^{−4N_q}. On that difference, |û(t,n)|² is
  bounded by the mass Σ_m φin(m/L)|g_m|², and Cauchy–Schwarz closes the estimate.

So `propansatz` (after R1) and `nlsAkBridge` (after R3) suffice for `main`. The proof also needs three unfrozen glue
lemmas: mass conservation for smooth NLS solutions, the almost-sure rapid decay of initialCoeff, and the Gaussian
moments of the mass. List them as obligations (O8).

**Inductive step: `propansatz` at p+1 ⇐ `fixedpoint` + `layergarden` + `wkeTaylor` + T.cmattr (unfrozen) + glue.**
I checked conjunct by conjunct:
- **(1).** Take F′ from `fixedpoint`. Then P ≥ 1 − e^{−N_p} − e^{−4N_{p+1}} ≥ 1 − e^{−N_{p+1}}, and F′ is symmetric
  in the same initial-data sense (Q5), which is consistent.
- **(1), the solution.** The contraction in (4) (Lipschitz ½, ball complete because Z requires continuity) gives
  b★. The Duhamel identity for `Lop` (glue) gives a solution on [p, p+1]. It glues with the old a at t = p, since
  `IsAkSolution` uses `HasDerivWithinAt` on `Icc`, so both one-sided derivatives equal 𝒞₊(a(p)). Uniqueness holds
  in the ⟨n⟩^{d+1}-class.
- **(1), measurability.** Picard iterates are measurable in ω.
- **(1), integrability.** On F_{p+1}, |a| is bounded by e^{3N} + e^{−10N}.
- **(2) and (2′).** These come from the couple expansion at time t ∈ (p, p+1], `layergarden` (2)(b) at t, and
  `wkeTaylor` (1) at t.
  - (4θ_{p+1}+θ_p)/5 > θ_{p+1} supplies the slack for the constant 2.
  - The R=1 lattice sum `truncSum (p+1) N t ![1,-1] ![n,n]` must be bridged to `truncSumC … (n/L)` by a glue
    lemma (shift κ ↦ κ + n). Add it as an obligation (O6).
- **(3) and (4).** `layergarden` (1) at t = p+1 gives ‖truncSum‖ ≤ (∏⟨n⟩)^{−4Λ}L^{−(m−1)/4}δ^{2νN}, which is
  ≤ (∏⟨n⟩)^{−Λ}L^{−(m−1)/6}δ^{νN} because jbrProd ≥ 1, L ≥ 1 and δ ≤ 1 (the prover takes δ₀ ≤ 1). Orders
  N_{p+1} < N ≤ N_{p+1}^4 go into Ẽ_{p+1} via δ^{2νN} ≤ e^{−N_{p+1}}. Orders > N_{p+1}^4 go via (ansatz5) at p, as
  in T L807–L809.
- **Shared sums (G-3).** `AnsatzAt (p+1)` (3)/(4) and `layergarden` use the same `truncSum P (inputsF P R) (p+1) N`.
  The time is p+1 in one and t in the other; the inputs F_q (q ≤ p, the only layers present), the time domain and
  the truncation are identical. The truncation is void in both ranges (orders ≤ N_{p+1}^4 ≤ N_p), so stage-1 R1 does
  not affect B1.1/B1.2/B1.12. It does affect B1.11(2) and `cumulantExpansion`.

**Time parameter (F7/F27).** It is carried consistently:
- B1.1 (2′): t ∈ [p−1, p];
- B1.2: t ∈ (p, p+1];
- B1.3 and B1.5: t ∈ [p, p+1];
- B1.12: p ≤ s < t ≤ p+1;
- `cumulantExpansion`: t ∈ [p, p+1].

This is exactly what `main` (L821) and T L2309 consume.

**Hypotheses.** None is conclusion-shaped or stronger than what the source uses:
- `RemainderBound` (after R1) is (ansatz2) for q ≤ p, which is what L949–L951 use (F36).
- `AnsatzAt q` for q ≤ p is the induction hypothesis.
- `sumint`'s `M ≤ N_1^4` (G-4) and `nlsAkBridge`'s rapid-decay hypothesis restrict data that every consumer
  satisfies.

## 3. REQUIRED fixes (exact Lean changes; all replacements elaborate, `Stage3Fixes.lean`)

### R1. `ContDiff ℝ ⊤` is real-analyticity
In Mathlib v4.35 `ContDiff 𝕜 (n : WithTop ℕ∞)`; `⊤ = ω`, and `ContDiff ℝ ⊤ f → AnalyticOnNhd ℝ f univ`. My probes
`remainderBound_analytic`, `ansatzAt_R_analytic` and `layergarden_conclusion_analytic` check this. The draft probe
`remainderBound_zero` cannot catch it, because constants are analytic. Wave A writes `(⊤ : ℕ∞)` for exactly this
reason (`IsSmoothNLSSolution`).

The three occurrences are `RemainderBound` (Statements L75), `layergarden` (2)(b) (L103) and `AnsatzAt` (2) (System
L456).

- **Option B (preferred, source-faithful: TARGET only has R_p ∈ 𝔖^{Λ_p,Λ_p}).** Delete the smoothness conjunct.
  `SNormR Λ Λ (R q) ≤ ofReal _` already forces `ContDiff ℝ Λ (R q)`; this is proved in `contDiff_of_remainderBoundB`.
  ```lean
  def RemainderBound (P : WTParams) (R : ℕ → Mom P.d → ℝ) (p : ℕ) : Prop :=
    ∀ q ≤ p, SNormR (P.Lambda q) (P.Lambda q) (R q) ≤ ENNReal.ofReal (P.L ^ (-P.theta q))
  -- AnsatzAt (2): replace `(ContDiff ℝ ⊤ (R p) ∧ SNormR …` by `(SNormR …`
  ```
  WAVE-B B2.1/B2.2 ("every C^∞ real R_r") should then take C^{40d} inputs. That is enough for the 30d-derivative
  norms they use.
- **Option A (minimal ripple).** Use `ContDiff ℝ (⊤ : ℕ∞) (R q)` in `RemainderBound` and `AnsatzAt` (2). Then
  `propansatz` must produce C^∞ remainders R_{p+1}. `layergarden` does not supply that (R2), so the prover needs an
  extra mollification lemma: mollify R_{p+1} at scale e^{−2N_{p+1}} and put the lattice error into E_{p+1}.

In both options, update D1 of `propansatz` ("smooth" → "C^{Λ_p}" or "C^∞").

### R2. `layergarden` (2)(b): delete the smoothness conjunct
`ContDiff ℝ ⊤ (coupleRemainder …)` is false:
- Take φin a nonnegative compactly supported bump, R ≡ 0 (`remainderBound_zero`), p = 0 and N = 2.
- Every leaf vector of an order-2 couple decoration is an argument of some input F_0 = φin.
- So `truncSumC` and 𝒰₁ = δ(t−p)𝒦(φin) vanish for |k| > C.
- If the remainder were analytic, it would vanish identically. It does not: it is the nonzero O(L^{−θ})
  lattice-versus-continuum discrepancy, including the ε = −1 degenerate terms that 𝒦 lacks.

With `(⊤ : ℕ∞)` the conjunct is still not implied: `RemainderBound` controls only Λ_q derivatives of R_q, and the
lattice sums over κ of higher derivatives need not converge. TARGET (L776) claims only the 𝔖^{4Λ_{p+1}} bound, and
that bound already gives C^{4Λ_{p+1}}.
```lean
      SNorm (4 * P.Lambda (p + 1)) (4 * P.Lambda (p + 1)) (coupleRemainder P R p N t) ≤
        ENNReal.ofReal (P.L ^ (-(4 * P.theta (p + 1) + P.theta p) / 5) * P.δ ^ (2 * P.ν * N))
```
(`layergarden'` in `Stage3Fixes.lean`.)

### R3. `nlsAkBridge` item (4): restrict to t ∈ [0, T]
`IsSmoothNLSSolution` constrains `u t` only for t ∈ [0, T], so `U ω t` for t ∉ [0, T] is arbitrary. Lean derives
`False` from the draft (`nlsAkBridge_refuted`, Appendix A) with:
- d = 1, L = 1, γ = 0, δ = 1, 𝔇 = 1, so T = 1/2;
- Ω = Bool with the trivial σ-algebra ⊥;
- data c ≡ 0;
- U = 0 on [0, 1/2], and the constant 1 at t = 5 for ω = true only.

The integrand at t = 5, n = 0 is then `if ω then 1 else 0`, which is not ⊥-measurable. `main` only needs
t ∈ Icc 0 T. Change:
```lean
        ∀ t ∈ Icc 0 T, ∀ n, Measurable fun ω =>
```

### R4. `atomCountLemma` (1): exclude k = 0 for ε = (+,−)
The draft is false:
- **The set.** For nk = 0, β = 0, a₁ = a₂ = 0, ε = −1, the set S₂(−1) contains every (n, n) with ‖n/L‖ ≤ 1.
- **Its size.** That is ≳ L^d/d^{d/2} points.
- **The claimed bound.** For γ ∈ (1/2, 1) and δ = 1 it is C·L^{d+1−2γ} = o(L^d).

DH23 Lemma A.3(1) (L2100) assumes |k₁−k₂| ∼ R ∈ [L^{−1}, 1], i.e. k ≠ 0, and then gives
L^{d−1} + δ^{−1}min(R^{−1}L^{d−2γ}, L^d) ≤ 2δ^{−1}min(L^d, L^{d+1−2γ}).

**New finding (for FINDINGS):** TARGET (atomcountbd) T L2472 states the first bound without k ≠ 0. It is false at
k = 0, ε = (+,−), γ > 1/2. Consumers (degenerate atoms, cf. F21) must exclude or handle k = 0.
```lean
      (∀ ε : ℤˣ, (S₂ ε).Finite) ∧
      (∀ ε : ℤˣ, (ε = -1 → nk ≠ 0) →
        ((S₂ ε).ncard : ℝ) ≤ C * δ⁻¹ * min (L ^ d) (L ^ ((d : ℝ) + 1 - 2 * γ))) ∧
```
(Item (2) already forces k ≠ 0; items (3) and (2) are otherwise unchanged; `atomCountLemma'`.)

### R5. `countLemma`: C before δ, L₀ after δ
The draft puts `∃ C L₀, ∀ L ≥ L₀, ∀ δ ∈ (0,1]`, i.e. it claims uniformity over δ. DH23's proof does not give that:
- DH23 (countc1-1), second case, is δ^{−2}L^{2(d−γ)}min(…, L^{−10η}).
- Turning it into "≲ δ^{−1}L^{2(d−γ)}𝔛^{−1}" needs δ^{−1}L^{−10η} ≤ (log L)^{−2}, i.e. L ≥ L₀(δ).
- Rescaling δ into γ′ (tolerance L^{−2γ′}) does not help: γ′ can approach ½ from above, where the L^{−10η} saving
  (η ≪ γ′ − ½) is unavailable.

Consumers fix δ before L, so this costs nothing. C stays uniform in δ, as "≲₁" requires:
```lean
theorem countLemma :
    ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η ∈ Ioc 0 η₀,
    ∀ c₀ : ℝ, 1 ≤ c₀ → ∃ C : ℝ, ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ α β : ℝ, …  -- rest unchanged
```
(Item (2) is uniform in δ by subdivision; the reorder is harmless there.)

### R6. `sumint`: require Λ_v ≥ 1
`Admissible` has `(∏ v, (D.Λ v : ℝ)) ≤ A ^ M`. One `Λ v₀ = 0`, i.e. ℓ_{v₀} = ℓ_{prev v₀}, makes the product 0. Every
other Λ_v is then unconstrained, up to M + 4 nonzero σ's each.

The proof's counting factor (∏ max(t_v,1))^d (T L1621) can then be ≈ (M+4)^{d(M−1)}. With M up to N₁^4 = (log L)^{C},
that factor is not absorbable into (C₁δ^{−1/2})^M L^{η^7}. TARGET's Λ are ≥ 1 ("at most Λ terms", with
∏Λ ≤ C₀^M as a genuine count). Add to `SumintDatum.Admissible` (or as a hypothesis of `sumint`):
```lean
  (∀ v, 1 ≤ D.Λ v) ∧
```

### R7. `canonicalCharacterization`: fix (2) and add uniqueness for 𝒞 and ℋ
**(2) is false.** Its conclusion uses `Relation.EqvGen LG.AttachLinked`. That relation is generated on all nodes, so
two attached gardens in one top tree merge through their common root. Stage-1's E1 garden ∈ 𝒢₂ is a sorry-free
counterexample: `[0,0]` and `[2]` lie in different blocks but are `EqvGen`-related. The fix uses the relation on
𝒰 (stage-1 R1).

**Uniqueness is missing.** (3) and (4) state existence of a decomposition only. Without uniqueness, B1.11 cannot
certify that `IsTrunc` inside `truncSumC` (B1.2 (2)(b)) and `truncSumHζ` (B1.12) is Def `defgtr` / ℋ^tr (L2288).
WAVE-B §4.14 asks for it: "Same for `IsCanonC` … and `IsCanonH`". Replace (2) by one clause covering all three
classes:
```lean
-- Core (stage-1 R1):  def AttachLinkedOn (p) (u u') := u ∈ LG.attachNodes p ∧ u' ∈ LG.attachNodes p ∧ LG.AttachLinked u u'
-- Statements: factor the body of `TopDecomp` as `TopDecompWith flowers p sub S U Bp` (so TopDecomp = ∃ U Bp, …)
    ((IsCanonGC (p + 1) LG ∨ IsCanonH (p + 1) LG) →
      ∀ (flowers : Bool) (U : Finset (GNode LG.garden.tree)) (Bp : Finpartition U),
        LG.TopDecompWith flowers p (LG.CanonInd p) LG.roots U Bp →
        U = LG.attachNodes p ∧
          ∀ B ∈ Bp.parts, ∀ u ∈ B, ∀ u' ∈ U,
            (u' ∈ B ↔ Relation.EqvGen (LG.AttachLinkedOn p) u u'))
```
(`canonicalUniqueness` in `Stage3Fixes.lean`.)

Why the clause is right:
- `IsCanonGC` covers 𝒢 and 𝒞 uniformly at any width.
- For flower gardens with `flowers = false` the hypothesis is unsatisfiable, so the clause is vacuous there.
- Why it is true:
  - Blocks are irreducible and completely paired, so the 𝒰-restricted relation never leaves a block and connects
    each block.
  - 𝒰 nodes have layer < p, and their parent is a top node in layer p (or a root, read as p); nodes inside an
    attached garden have parent layer ≤ p−1.

### R8. B1.12 `layergardenFlower`: not sufficient for its consumer
The core per-order estimate (flowerest2) is transcribed faithfully:
- the sign ζ·ζ_j on flowers;
- (k,k′)-decorations;
- L^{d−γ} (F25);
- truncation by layer-p branching nodes (L2290);
- the (Y-1)–(Y-2) and (W-1)–(W-3) restrictions.

But `fixedpoint`'s proof, which is G-1's reason for the gate, also uses:
- (a) the M₁/M₂ smooth-cutoff gains (L2283–L2285, used at L2320ff);
- (b) the ∂_t a^tr and ∂_t ℒ₀ moments, with an extra δ(t_𝔯 − t) at the root (L2312);
- (c) the ∂_{t,s} kernels in (sobolev2), with δ(t_𝔫 − s) at the parent or a non-flower child of 𝔣^pr (L2330–L2338).

`kernelK` can fix times only at flower parents, so (b) and (c) are not even expressible. A frozen B1.12 without
these does not spare the VH re-run that G-1 is about.

**Required decision:**
- either do not freeze B1.12 in this batch (packet X1 first);
- or generalize the carrier now: a set of designated branching nodes with prescribed times (root ↦ t, flower parent
  ↦ s, one parent or child of 𝔣^pr ↦ s), plus a cutoff-function parameter. Then state B1.12 for that class.

Either way, `RemainderBound` inherits R1.

### R9. `cumulantExpansion` (optional anchor): the N-range is wrong
`∑ N ∈ range (2m·N_{p+1} + 1)` keeps only gardens of order ≤ 2m·N_{p+1}. Gardens in 𝒢^tr_{p+1} carry attached
gardens of order up to N_p each, as Q9's reading overlooks.

Example:
- m = 2, four trivial top trees, and one block replaced by G′ ∈ 𝒢_p with 4N_{p+1} < n(G′) ≤ N_p.
- Its K_G(p+1) = K_{G′}(p) is genuinely part of 𝕂_p(a^tr(p+1)) (T (proofmain-1), L799–L801).
- It is of size up to δ^{νn}, which is ≫ e^{−N_p}.

So the identity with error e^{−N_p} is false. If the anchor is frozen:
- sum to `Nmax := 2*m*P.N (p+1) + m*(2*P.N (p+1)+1)*P.N p`, which bounds the order of every truncated garden of
  width 2m; or drop the order filter altogether;
- apply stage-1 R1, since attached orders now matter;
- add the m = 1 couple case with `truncSumC`, as WAVE-B §4.16 has ("1 ≤ m … couples: truncSumC").

`C₀ = 10` gives L^{10dRN} ≥ TARGET's L^{20RN} for d ≥ 2, which is fine.

## 4. Per-statement notes (what I checked and accept)

### 4.1 `propansatz` (B1.1)
Everything below is FAITHFUL, R1 aside:
- **(1).** Measurable, symmetric event; nested `Fev p ⊆ Fev (p−1)`; P ≥ 1−e^{−N_p}; a classed solution on [0,p] with
  data `initialCoeff`, unique in the class; measurability of ω ↦ a ω t n; integrability of all finite products on
  Fev p. These last two are true: products are bounded on F_p for p ≥ 1, and are Gaussian moments at p = 0.
- **(2).** The moment form of (ansatz1) is correct: first moments vanish on symmetric events, D2. E = E[1_F ·] (D6
  ruling).
- **(3), (4).** These use `truncSum p N p`, whose truncation is void for N ≤ N_p, consistent with `truncSum_untruncated`.
  Supports and bounds are as in (ansatz3)–(ansatz5). At p = 0, 𝒢₀ = ∅ gives `truncSum = 0`.
- **(2′).** Its bound 2L^{−θ_p} is provable from the step at t (slack (4θ_{p+1}+θ_p)/5 > θ_{p+1}), and it is what
  `main` needs.

The existential witnesses are pinned: P(Fev p) > 0, and E, Ẽ are tiny and bounded. A single `a` serves all p,
because each `AnsatzAt p` reads `a` only on [0, p].

### 4.2 `layergarden` (B1.2)
Checked against the source:
- the quantifiers: p < 𝔇; R with (ansatz2) for q ≤ p; t ∈ (p, p+1]; N ≤ N_{p+1}^4; 2 ≤ m ≤ 10R_{p+1}; balanced ζ;
- the bounds (estgarden) and (estcouple2);
- `coupleRemainder` = 𝒦^tr_{p+1,N}(t,k) − [N even]𝒰^{(p)}_{N/2}(t,k), with 𝒰 built from φ(δp).

(2)(a) is trivially true: n₀ ≠ n₁ admits no decoration. That matches T L770.

The quantifier order is right: R comes after L, and the bound is uniform over all R obeying the bounds. That is
legitimate, because the proof uses R only through (ansatz2) (F36). R2 is needed as explained.

### 4.3 `fixedpoint` (B1.3)
All items match the source and the stated deviations:
- **(1), (2).** Bounds for t ∈ [p,p+1]. `∀ b` in (2) is harmless, since ℒ₀ ignores b.
- **(3).** "Maps Z into Z, bijective, ‖b‖ ≤ e^{3N}‖(1−ℒ₁)b‖" is equivalent to (fixedest3). Invertibility on bounded
  arrays implies invertibility on the continuous subspace, because b = c + ℒ₁b.
- **(4).** Existence of c in the ball plus Lipschitz ½ on solutions is (fixedest4). Uniqueness of c follows by taking
  b = b′, so Φ is well defined. ½ is provable: e^{3N}(2e^{−6N} + L^{30d}e^{−20N}) ≪ ½.
- **`Lop`.** `slotCountB = j`; `Ntr ≤ slotOrder` only for j = 0; the conjugate in the middle slot (F9).
- **Data.** 𝒥 and a^tr are built from `a ω p`; Z uses Λ = (5/4)Λ_{p+1}; F′ ⊆ Fev p is measurable and symmetric with
  μ(Fev p ∖ F′) ≤ e^{−4N_{p+1}}.
- **𝒥₀.** The order-0 tree term is a_n(p): the integral over `Empty → ℝ` is a point mass.

### 4.4 `nlsAkBridge` (B1.4)
I re-derived (reducedcoef) with the frozen Δ = (2π)^{−1}∑∂² and the frozen L^{−d/2} normalization:
- Δe^{2πik·x} = −2π|k|²e^{2πik·x};
- with s = δT_kin t = δL^{2γ}t/2, the linear phase is e^{πiδL^{2γ}|k|²t};
- M = ⨍|u|² = L^{−d}∑|c|², and v = e^{−2iαMs}u gives the Wick term;
- the resulting nonlinearity is exactly `aNonlin … 1`, with (δ/2L^{d−γ})·i and phase e^{πiδL^{2γ}Ωt}.

So the drafter's flagged conventions are correct. Items (1)–(3) are FAITHFUL; (2) needs the rapid-decay hypothesis
(D2), and on F_𝔇 that holds almost surely. (4): R3.

### 4.5 `wkeTaylor` (B1.5)
𝒰₀ = φ(pδ) and 𝒰_{n+1} = δ∑_{n₁+n₂+n₃=n}∫_p^t 𝒦; item (1) holds for all t ∈ [p,p+1]; the 𝔖^{4Λ_{p+1}} bound is
C₂(C₁δ)^N with C₁ fixed before δ and 𝔇.

The base can indeed be independent of Λ. A majorant argument gives X(z) = x₀exp(3C₀(Λ)∫Y²), which has the same
radius of convergence; the Λ-dependence goes into C₂. Conjunct (0) closes the junk-integral hazard for
`wkeTaylorTerm`, which B1.2 (2)(b) consumes.

### 4.6 `sumint` (B1.6)
I checked the following against (sumintI1) (T L1601–L1611) and found them right:
- the phase: e^{πi·}, not e(·); the (t_j−s_j)⟨x_j,y_j⟩ terms; the j=0 term with ζ₀ = x₀; ζ_j = a x_j + b y_j + c r;
  the parameters λ, μ, σ;
- the Nor block: τ₁−τ₃, τ₂−τ₃ with Λ_i, and τ₃−t with ξ_i;
- the bad-case factors: (b) |r|^{#}, (c) |t₁−s₁|^{1−3η} inside the integral, (a) and (d) in `Admissible`;
- the domain 𝒟: unit intervals, all < t, t₀¹ > max(t′,t″), and the order constraints;
- (ii) as affine identities with `prev`; (iii); the weight norms (propertyKj) with γ₁;
- M₀ (A read as Nor), M₁, |Bad|;
- ℬ, K, the restriction norm 𝔛^{2η^8,0,0}(ℬ) with sup over (e,f,g,h);
- the RHS (FourierboundI).

There is no junk:
- `maxPar ≥ 1`, since TVar is nonempty for I ≥ 1;
- the x-sum is genuinely summable, because T₁ is unimodular and the ⟨k⟩^{−30d} decay comes from SNorm < ⊤;
- the τ-integral has a bounded integrand on a bounded domain;
- the extension norm is ⊤ when no extension exists.

Two readings to disclose (see O3 and question 3): `prev = none` means ℓ_v itself is a signed sum (otherwise (ii)
would be impossible for the lex-first index), and D7. R6 is required.

### 4.7–4.10 Counting and exponential sums
`countLemma`:
- the |r| ∼ P encoding with c₀ and the three ξ, ζ choices are FAITHFUL;
- 𝔛 is positive for L ≥ e;
- finiteness is stated (against junk `ncard`);
- R5 is required.

`atomCountLemma`:
- (2) and (3) are FAITHFUL; (2)'s L^{d−1} term is absorbed because γ+η ≤ 1;
- (3) includes the degenerate k₁ = k or k₃ = k solutions (2L^d ≤ L^{2d−2γ});
- R4 is required.

`quadExpSum2` and `quadExpSum3`:
- FAITHFUL; T₀ = 𝔇δ = τ★ ("≲₂");
- the lattice sums are finite and continuous in s (resp. (t,s)), so the Bochner integrals are not junk;
- `quadExpSum2`'s ∀η > 0 is the standard ε-loss form; `quadExpSum3`'s region is the same as L ≤ max(|t|,|s|) ≤ T₀L^{2γ}.

### 4.11 `canonicalCharacterization` (B1.11)
`CanonInd`/`TopDecomp` transcribe Def `defcanon` faithfully:
- U = the replaced top leaves; the top region is in layer p;
- top leaves outside U are paired inside the top region;
- blocks have size ≥ 4 and are in 𝒢_p (layers ≤ p−1 by recursion);
- `IrreducibleAt S` is equivalent to the "no proper A whose top leaves are a union of B_i" condition, given that
  the blocks are irreducible;
- balance is automatic.

The couple clause without irreducibility is right: a single tree has an odd number of leaves. The flower clause is
right too: flowers cannot lie below 𝒰, because `CompletelyPaired` fails there, so the stem is top-region in layer p.

(1) and the existence parts of (3)/(4) are plausible and correctly stated: they are `canonequiv` and its ℋ version
(L2262). R7 is required.

### 4.12 `layergardenFlower` (B1.12)
Optional (O1):
- **The extra factor.** The kind ≠ 0 conjunct demands e^{−100N_{p+1}} on top of δ^{2νN} per order. TARGET claims
  that factor only for the sum over N > N_{p+1} (L2305). Per order it is likely true, since the true bounds are
  ~(C₁√δ)^n, but it is stronger than stated. Using the same per-order bound for all kinds is enough for the
  consumer: (Y)/(W) force N ≥ 2P(N_{p+1}+1), and ∑δ^{2νN} ≤ e^{−100N_{p+1}}.
- **The time range.** The endpoints s = p and t = p+1 are harmless: the flower parents' layer constraint makes the
  kernel 0 at s = p.

## 5. DESIGN questions

- **Q3 (prefix composition): ACCEPT.** Leave the conjunction lemma to the provers. Every B1 statement is monotone in
  C₁, C₂ and the thresholds, including `wkeTaylor` (C₂(C₁δ)^N with C₁δ ≥ 0) and `sumint`.
- **Q5 (symmetric events as initial-data preimages): ACCEPT.** It is the literal T L567. An initial-data preimage is
  also a g-preimage of an invariant set, so the existential in `propansatz` is not weaker than WAVE-B's. The form is
  stable under the step: F′ is a function of û_in on F_p. It also suffices for the gauge argument, since the law of
  û_in is invariant and the solution is a function of û_in.
- **Q7 (P after ν, before δ): ACCEPT.** TARGET makes P and ν both depend on C₁ alone, so either linearization is
  implied by the source. P after ν lets P₀ depend on ν; WAVE-B's P-before-ν lets ν₀ depend on P. `fixedpoint`'s
  proof composes with the draft's order: given ν, pick P := P₀(ν), then δ₀(P). "∀ Pm ≥ P₀" is exactly "P large".
- **Q8 (`truncSumHζ`): ACCEPT.** Move it into System and delete `truncSumH`, so that one shared definition is used
  (G-3) (O4).
- **Q9 (`cumulantExpansion`): REJECT the N-range** (R9). C₀ = 10 is fine.

## 6. OPTIONAL suggestions

- **O1.** B1.12: use the kind-independent per-order bound (§4.12).
- **O2.** `countLemma`, Pr = 1: also assume ‖r‖ ≤ c₀. In every use, r is a difference of vectors in unit balls. The
  unbounded-|r| case is probably true (slab counts only shrink), but it is outside DH23's dyadic setting.
- **O3.** `sumint` docstring:
  - disclose the `prev = none` reading;
  - say that D7 excludes constant lattice offsets in h₁, h₂ and requires coefficient sum 1 (see question 3);
  - fix the stale docstring of `AttachLinked` ("two attachment nodes").
- **O4.** Move `truncSumHζ` (and `FlowerRestr`, `topCountBelow`) into System with the other shared sums; delete
  `truncSumH`.
- **O5.** `summable_kernelK_summand` assumes summability of F q for all q. With `inputsF P R` and R constrained only
  for q ≤ p, that is unsatisfiable in general. Restrict the hypothesis to the layers present (q ≤ the max layer), as
  the kernels only read those.
- **O6.** Add the glue obligations that the assembly needs:
  - `truncSum (p+1) N t ![1,-1] ![n,n] = truncSumC (p+1) N t (n/L)` (decoration shift);
  - the Duhamel identity for `Lop`/`aTr`;
  - mass conservation for classed a-system solutions.
- **O7.** B1.12: write s ∈ (p, t), t ∈ (p, p+1], as in the source (cosmetic).
- **O8.** In `propansatz`'s docstring, list what `main` needs beyond the frozen anchors:
  - mass conservation for smooth NLS (T L819);
  - almost-sure rapid decay of initialCoeff (PROB.smoothData);
  - Gaussian moments of the mass.
- **O9.** Add a negative probe for R1, so that any `ContDiff ℝ ⊤` regression is caught: for example, assert
  `¬ AnalyticOnNhd` for a bump in the probe file, or state `RemainderBound` for a compactly supported nonzero R.

## 7. Questions for the author

1. **R1:** should the remainders be in C^{Λ_q} (Option B; B2.1/B2.2 then take C^{40d} inputs) or in C^∞ (Option A;
   one extra mollification lemma in `propansatz`)? My recommendation is B.
2. **R8:** freeze B1.12 now as a partial gate, or wait for X1 and generalize `kernelK` to designated fixed-time nodes
   plus cutoffs? My recommendation is to wait. Freezing a gate that `fixedpoint` cannot use does not reduce the
   critical path.
3. **`sumint` D7:** in every consumer, are h₁ and h₂ integer combinations of (e,f,g,h) with coefficient sum 1 and no
   constant lattice offset? If any consumer needs an offset, add `c₁ c₂ : S.VIdx → (Fin d → ℤ)` to the datum.
4. **New finding for FINDINGS:** TARGET (atomcountbd) T L2472 needs k ≠ 0 for ε = (+,−) when γ > 1/2. Should it be
   recorded as a candidate erratum, consistent with DH23 A.3(1)'s |k₁−k₂| ∼ R ≥ L^{−1}?
5. **`cumulantExpansion`:** freeze (with R9 and the m = 1 couple case) or leave to T.cmattr?

## Appendix A. Probe sources (session scratch; not in any repository)

Snapshot modules compiled as `WaveBDraft.{Core, System, Statements, Sumint}` from `waveb-snap-1`. Command per module:
`cd /home/scott/WaveTurbulence-worktrees/orch && nice -n 5 lake env bash -c "LEAN_PATH=\$LEAN_PATH:<S>/build lean -R
<S>/src -o <S>/build/WaveBDraft/<M>.olean -i <S>/build/WaveBDraft/<M>.ilean <S>/src/WaveBDraft/<M>.lean"`.
Here `<S>` is `/tmp/claude-1004/-home-scott/749ee92b-8f50-4496-8faa-864f2fd27c53/scratchpad/aud`.

`Stage3Probe.lean` (imports `WaveBDraft.Statements`, `WaveBDraft.Sumint`; `open scoped ContDiff`), key parts:
```lean
example (f : ℝ → ℝ) : ContDiff ℝ ⊤ f ↔ ContDiff ℝ ω f := Iff.rfl

theorem remainderBound_analytic (P : WTParams) (R : ℕ → Mom P.d → ℝ) (p : ℕ)
    (h : RemainderBound P R p) : AnalyticOnNhd ℝ (R 0) Set.univ :=
  (h 0 (Nat.zero_le p)).1.analyticOnNhd

noncomputable def U : Bool → ℝ → (Fin 1 → ℝ) → ℂ := fun b t _ => if b = true ∧ t = 5 then 1 else 0

theorem U_sol (b : Bool) : IsSmoothNLSSolution (1 : ℝ) 1 (1 / 2) (fun _ => 0) (U b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (contDiffOn_const (c := (0 : ℂ))).congr ?_
    rintro ⟨t, x⟩ ⟨ht, -⟩
    simp [U_eq_zero b ht]
  · intro t ht x j; simp [U_eq_zero b ht]
  · intro n; rw [U_eq_zero b ⟨le_rfl, by norm_num⟩]; simp [torusFourierCoeff]
  · intro t ht x
    have h1 : derivWithin (fun s => U b s x) (Icc 0 (1 / 2)) t = 0 := by
      rw [derivWithin_congr (f := fun _ => (0 : ℂ)) (fun s hs => by simp [U_eq_zero b hs])
        (by simp [U_eq_zero b ht])]
      simp
    rw [h1, U_eq_zero b ht]
    simp [normLaplacian, partialDeriv]

theorem nlsAkBridge_refuted : False := by
  have h := (nlsAkBridge (d := 1) le_rfl (1 : ℝ) 0 1 one_pos one_pos 1 1 (1 / 2)
    (by simp) (by simp [kineticTime])).2.2.2
  let _ : MeasurableSpace Bool := ⊥
  have hm := (h Bool c0 measurable_const).2 U (fun b _ => U_sol b) 5 0
  -- solvable set = univ; integrand at t = 5, n = 0 is `if b then 1 else 0` (coeff_one);
  -- `MeasurableSpace.measurableSet_bot_iff` on its preimage of {1} = {true}: contradiction.
  …
```
`#print axioms`:
- `U_sol`, `coeff_one`, `remainderBound_analytic`: `[propext, Classical.choice, Quot.sound]`;
- `nlsAkBridge_refuted`: the same plus `sorryAx`, which is the draft `nlsAkBridge` body itself. The draft statement
  implies `False`.

`Stage3Fixes.lean` contains `RemainderBoundA/B`, `contDiff_of_remainderBoundB` (proved), `layergarden'`, `item4`,
`atomCountLemma'`, `countPrefix`, `AttachLinkedOn`, `TopDecompWith`, `canonicalUniqueness`, `sumint'` and `Nmax`.
All of them elaborate.
