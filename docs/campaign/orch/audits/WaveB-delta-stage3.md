# Delta audit: Wave B stage 3 after fixes (snapshot 2)

Auditor: independent refute-first statement auditor (Opus). Date: 2026-11-03.
Scope: closure of the stage-3 REQUIRED items R1–R9 (`docs/campaign/orch/audits/WaveB-stage3.md`, sha256
`5fb36dde…`), new defects in the 11 freeze-set statements, the effect of delta-1's D1, composability, and joint
elaboration. Read-only on every draft and repository file; this file is my only output.

## Inputs

`/home/scott/wt-scratch/waveb-snap-2/`, `sha256sum -c SHA256SUMS`: all 8 OK.

| file | sha256 |
|---|---|
| `WaveB1-Core.lean` | `9e6c6b4d…3088e3f0` |
| `WaveB1-Core-probes.lean` | `58f7ac3f…976ced40` |
| `WaveB1-System.lean` | `70a762bd…b55be2c8` |
| `WaveB1-System-probes.lean` | `331a31f2…5063a86a` |
| `WaveB1-Statements.lean` | `4a6fe805…c68accd5` |
| `WaveB1-Statements-probes.lean` | `8128437a…07e0b519` |
| `WaveB1-Sumint.lean` | `8863d8fa…b9a06363` |
| `DESIGN.md` (changelog CL-1 … CL-11) | `d40536f5…0f31a117` |

TARGET `WKE-Longer_times_Final_arXiv.tex` sha256 `493eef6b7dec448b…` ("T Lnnn" below). I diffed every file against
`waveb-snap-1`. Frozen Wave A and the landed `Foundations/NLS/AkSystem` were read in the `w/orch` worktree
(`62e374a`).

**Elaboration.** From `/home/scott/WaveTurbulence-worktrees/orch`, one `lean` at a time (`nice -n 5 lake env …
lean -R <S>/src -o …`), I compiled the seven snapshot files as modules `WaveBDraft.{Core, System, Statements, Sumint,
CoreProbes, SystemProbes, StatementsProbes}`. `<S>` is my session scratch
`/tmp/claude-1004/-home-scott/749ee92b-8f50-4496-8faa-864f2fd27c53/scratchpad/aud3`.

| module | time | result |
|---|---|---|
| Core | 52 s | 0 errors |
| System | 62 s | 0 errors |
| Statements | 114 s | 0 errors |
| Sumint | 166 s | 0 errors |
| CoreProbes | 155 s | 0 errors |
| SystemProbes | 87 s | 0 errors |
| StatementsProbes | 78 s | 0 errors |

Each module peaks at ≈3.9 GB. Load average was ≈55, hence the slow times.

The only warnings are 12 `declaration uses sorry`. They are exactly the anchors:
- Statements L72, L106, L132, L182, L222, L249, L285, L351, L366, L469 (the 10 freeze anchors);
- Statements L517 (the deferred `layergardenFlower`);
- Sumint L260 (`sumint`).

The orch `.lake` oleans of every imported Frozen/Foundations module are newer than their sources, so I rebuilt no
library.

## 0. Verdict

**NOT APPROVED — one new REQUIRED item (N1), with a one-line fix.**

- **R1–R7 are closed exactly**: each edited declaration is, token for token, the replacement Lean of
  WaveB-stage3.md §3. R5 also folds in the optional O2, a pure weakening.
- **R8 and R9 dispositions are correct.** B1.12 is outside the freeze set and `cumulantExpansion` is gone. No
  freeze-set statement reaches any B1.12-only object (checked in Lean, §5).
- **D1** (`truncSumHζ` empty for kind ≠ 0) affects **no** freeze-set statement. It matters only if `truncSumHζ`,
  `FlowerRestr` or `topCountBelow` are landed as sealed definitions (§3).
- **N1 (new, REQUIRED): `nlsAkBridge` item (2) is false at 𝔇 = 0.** Lean derives `False` from the draft
  (`nlsAkBridge_D0_refuted`, sorry-free apart from the draft anchor itself). The defect was already in snapshot 1;
  the stage-3 audit missed it. Fix: add `(hD : 1 ≤ D)`. Every consumer has it (`WTPrefix` gives `1 ≤ D`).
- I found no other defect. With N1 applied, the freeze set is approvable as is: the change is a single added
  hypothesis, checkable by `diff`.

## 1. R1–R9

| # | required change (stage 3) | snapshot 2 | verdict | evidence |
|---|---|---|---|---|
| R1 | Option B: `RemainderBound` and `AnsatzAt` (2) lose the `ContDiff ℝ ⊤` conjunct; D1 of `propansatz` updated | `RemainderBound` (Statements L87–L88) is `∀ q ≤ p, SNormR (P.Lambda q) (P.Lambda q) (R q) ≤ ENNReal.ofReal (P.L ^ (-P.theta q))`, verbatim. `AnsatzAt` (2) (System L517) begins `(SNormR (P.Lambda p) (P.Lambda p) (R p) ≤ …`. The `propansatz` D1 now says "real `C^{Λ_p}`". | **CLOSED exactly** | `grep`: `ContDiff ℝ ⊤` occurs only in docstrings in all seven files. `remainderBound_iff` (`Iff.rfl`) pins the definiens. `contDiff_of_remainderBound` and `contDiff_of_SNormR_lt_top` use standard axioms. *Pending author:* C^{Λ_q}, not C^∞ (question 1). |
| R2 | `layergarden` (2)(b): delete the smoothness conjunct | L116–L117 is exactly `SNorm (4 * P.Lambda (p + 1)) (4 * P.Lambda (p + 1)) (coupleRemainder P R p N t) ≤ ENNReal.ofReal (P.L ^ (-(4 * P.theta (p + 1) + P.theta p) / 5) * P.δ ^ (2 * P.ν * N))` | **CLOSED exactly** | The `SNorm` guard still forces C^{4Λ_{p+1}}, which holds: every input F_q is C^{Λ_q} with Λ_q ≥ Λ_p = 40d·Λ_{p+1}, the phase integrals are smooth in k, and the derivative series converge by the ⟨k⟩^{−Λ_q} decay. So the guard is not a junk-⊤ trap. |
| R3 | `nlsAkBridge` (4): `∀ t ∈ Icc 0 T, ∀ n, Measurable fun ω =>` | L209, verbatim | **CLOSED exactly** | The stage-3 refutation used t = 5 ∉ [0, 1/2] and no longer applies. With t ∈ [0,T], item (4) is true: the solvable set is a Borel set of data (lifetime > T, lower semicontinuous in H^{s₀}; Lusin–Souslin into the product space), and on it the integrand is a continuous function of the data. **But item (2) is false at 𝔇 = 0: N1.** |
| R4 | `atomCountLemma` (1): finiteness split off; the bound for ε = −1 needs `nk ≠ 0` | L297–L299, verbatim | **CLOSED exactly** | ε = −1, k ≠ 0 gives a slab count ≲ L^{d−1}(1 + L²·δ^{−1}L^{−2γ}) ≤ 2δ^{−1}L^{d+1−2γ}, uniform in δ. ε = +1 at k = 0 is a shell count ≤ the same bound. Items (2) and (3) are unchanged. |
| R5 | `countLemma`: `∃ C, ∀ δ ∈ Ioc 0 1, ∃ L₀, ∀ L ≥ L₀` | L251, verbatim. Also O2: for P = 1, `‖r‖ ≤ c₀` | **CLOSED exactly** (O2 accepted) | O2 adds a hypothesis, so it only weakens the statement. It is the literal "|r| ∼₀ P" at P = 1 (T L2460). Cosmetic, pre-existing: the binder `∀ η ∈ Ioc 0 η₀` is unused in the body (O1 below). |
| R6 | `SumintDatum.Admissible`: `(∀ v, 1 ≤ D.Λ v) ∧` | Sumint L152, verbatim, before `∏ Λ ≤ A^M`. The D8 docstring was added. | **CLOSED exactly** | Consumers lose nothing: they take Λ_v := max(#terms, 1), and TARGET's "at most Λ terms" already allows Λ ≥ 1. |
| R7 | (2) replaced by uniqueness for `IsCanonGC ∨ IsCanonH`, with classes of `EqvGen (AttachLinkedOn p)`; `TopDecomp` factored through `TopDecompWith` | L471–L476 are verbatim the stage-3 `canonicalUniqueness`. `TopDecompWith` (L412–L419) is byte-identical to the old body of `TopDecomp`, and `TopDecomp := ∃ U Bp, TopDecompWith …`. `AttachLinkedOn` (Core L620) is verbatim stage-1 R1. | **CLOSED exactly**, and I checked it is **true** (§2.11) | (1), (3), (4) keep their meaning (`diff`). The probes `e1_trunc`, `e1_canon2`, `figLG0_canonInd1` elaborate. |
| R8 | B1.12 not frozen (wait for X1), or generalized | Deferred. A section header and docstring say "DEFERRED, not for freezing". O1 (one kind-independent per-order bound) and O7 (`t ∈ Ioc p (p+1)`, `s ∈ Ioo p t`) were applied to the draft. | **Disposition correct** | §5: none of the 11 freeze statements reaches `layergardenFlower`, `WTPrefixP`, `truncSumHζ`, `FlowerRestr`, `topCountBelow` or `KGflower`. Under D1, the deferred draft's kind ≠ 0 content is vacuous (0 ≤ RHS); X1 must fix D1 first. *Pending author* (question 2). |
| R9 | `cumulantExpansion`: fix the N-range or do not freeze | Removed from all files. DESIGN CL-9 records the corrected range `Nmax = 2m·N_{p+1} + m(2N_{p+1}+1)·N_p`, the `AttachLinkedOn` attached orders and the missing m = 1 couple case for whoever states T.cmattr. | **Disposition correct** | `grep`: no occurrence in any `.lean` file. In Lean, `cumulantExpansion` is absent from the environment (§5). Nothing referenced it: it was a leaf. *Pending author* (question 3). |

## 2. The freeze set after the fixes (refute-first pass)

Unchanged from snapshot 1 apart from the edits above: the prefixes `WTPrefix` and `WTPrefixA` (F5 order
C₀ → η → 𝔆 → C₁ → ν → δ(𝔇) → C₂ → L), `IsGaussianData`, and the time parameters (F7/F27). The time parameters are:

- `layergarden`: t ∈ (p, p+1];
- `fixedpoint` and `wkeTaylor`: t ∈ [p, p+1];
- `AnsatzAt` (2′): t ∈ [p−1, p];
- `nlsAkBridge`: t ∈ [0, T].

I re-checked each statement for wrong quantifier order, conclusion-shaped hypotheses, junk values and D1.

### 2.1 N1 (new, REQUIRED): `nlsAkBridge` (2) is false at 𝔇 = 0

**Why it fails.** `nlsAkBridge` quantifies every `D : ℕ`, including 0, and then T = 0·δ·T_kin = 0.

- **The a-system side is trivial.** `IsAkSolution L γ δ 0 c a` only asks for `a 0 = c`, a bound at t = 0, and
  `HasDerivWithinAt … (Icc 0 0) 0`. That last condition holds for *any* derivative, since a derivative within a
  singleton is arbitrary (`hasDerivWithinAt_singleton_self`).
- **The NLS side is not.** `IsSmoothNLSSolution L α 0 c u` (frozen) imposes the equation at t = 0 with
  `derivWithin … (Icc 0 0) 0`, and Mathlib sets that to 0 (`derivWithin_zero_of_not_accPt`). So it forces the
  stationary equation −Δu₀ + α|u₀|²u₀ = 0.
- **Why no solution exists.** Pairing with ū₀ and integrating gives (2π)^{−1}‖∇u₀‖² + α‖u₀‖⁴₄ = 0, so u₀ = 0.
  Item (2) therefore fails for every rapidly decreasing c ≠ 0.

**Lean witness.** `nlsAkBridge_D0_refuted : False` (`Delta3Probe.lean`, §5) uses:

- d = 1, L = 1, γ = 0, δ = 1, 𝔇 = 0 (so α = 1 and T = 0);
- c = δ_{n,0} and a ≡ c.

The proof is that `eq_of_torusFourierCoeff_eq` gives u(0) ≡ 1, after which the equation at x = 0 reads
0 − 0 + 1 = 0.

Items (1), (3) and (4) are true at 𝔇 = 0. Item (2) is true for 𝔇 ≥ 1: there T > 0, the classed a-solution is an
H^{s} solution for d/2 < s < d/2 + 1, and persistence of regularity applies.

**Exact Lean change** (`WaveB1-Statements.lean`, `nlsAkBridge` signature):

```lean
theorem nlsAkBridge {d : ℕ} (hd : 1 ≤ d) (L γ δ : ℝ) (hL : 0 < L) (hδ : 0 < δ) (D : ℕ)
    (hD : 1 ≤ D) (α T : ℝ) (hα : α = L ^ (-γ)) (hT : T = D * δ * kineticTime α) :
```

The body is unchanged. Add a deviation to the docstring: "(D3) `1 ≤ 𝔇`: at `𝔇 = 0` the `a`-system on `[0,0]` is
void while a smooth solution on `[0,0]` must be stationary". The replacement elaborates, and the draft implies it
(`NlsAkBridgeFixed`, `nlsAkBridge_implies_fixed` in `Delta3Fix.lean`).

Consumers are unaffected: `main` instantiates 𝔇 from `WTPrefix`, which carries `1 ≤ D` (§4). The alternative
`(hT0 : 0 < T)` also works, but `1 ≤ D` matches the prefix.

### 2.2 The other ten statements and `canonicalCharacterization`

- **`propansatz` (B1.1).** The only change is in `AnsatzAt`:
  - (2) is now the bare (ansatz2) bound, which is weaker and source-faithful.
  - (1) uses the landed `IsAkSolution L γ δ p c a`. Its argument order is right: 𝔇-slot = p, data = û_in.
    `IsAkBounded` carries the same ⟨n/L⟩^{d+1} weight as the removed `IsASolution`.
  - At p = 0 the `[0,0]` triviality is harmless and correct: the solution and the uniqueness clause only constrain
    t = 0. There is no D = 0 issue, because `WTPrefix` has `1 ≤ D`.
- **`layergarden` (B1.2).** R2 as above.
  - The hypothesis `RemainderBound` is exactly `AnsatzAt q` (2)'s first conjunct (same expression), so the inductive
    step feeds it without glue.
  - Not conclusion-shaped: R ≡ 0 satisfies it (`remainderBound_zero`).
- **`fixedpoint` (B1.3), `wkeTaylor` (B1.5), `quadExpSum2` (B1.9), `quadExpSum3` (B1.10).** Unchanged (`diff`).
  - Only `fixedpoint`'s hypothesis `AnsatzAt` changed, and it got weaker, so the statement got stronger. It is still
    true, because its proof uses (ansatz2) only through the norm bound.
  - CL-4 adds sorry-free finiteness and summability lemmas for the B1.9/B1.10 lattice sums, so those `tsum`s are
    not junk.
- **`sumint` (B1.6).** R6 only. `Admissible` remains satisfiable, and the conclusion is unchanged.
- **`countLemma` (B1.7).**
  - R5: the prefix is d, γ → η → c₀ → C → δ → L₀ → L.
  - The P = 1 upper bound (O2) is a hypothesis on data that every use satisfies.
- **`atomCountLemma` (B1.8).**
  - R4: the excluded case (ε = −1, k = 0) is exactly the false one.
  - The constants `∃ C L₀` come before δ. That is fine, because the bounds are uniform in δ ∈ (0,1] (computed in the
    table above).
- **`canonicalCharacterization` (B1.11).** (2) is true. In fact it holds for every layered garden; the
  `IsCanonGC ∨ IsCanonH` hypothesis is not used. Proof sketch:
  - **Layers below a block.** By induction, `CanonInd (p'+1) S` puts every node below S in layer ≤ p′. A node is
    either in the top region outside U′ (layer p′) or below a block of `CanonInd p'`.
  - **U ⊆ 𝒰.** Take u ∈ U in a block B with `CanonInd p B`. Then 𝔏_u ≤ p − 1. Its parent, if any, lies in the top
    region and outside U, because `TopRegion S U u` forbids strict ancestors in U. So the parent is in layer p and
    u ∈ 𝒰.
  - **𝒰 ⊆ U.** Take a ∈ 𝒰 ∖ U. It cannot lie in the top region, where it would have layer p. So it has a strict
    ancestor in U, and then its parent has layer ≤ p − 1. Contradiction.
  - **Blocks are classes (→).** Within B, leaves below B are completely paired. If the `AttachLinkedOn`-class of u
    in B were a proper subset, it would have completely paired leaves, contradicting `IrreducibleAt B`.
  - **Classes stay in their block (←).** A link from v ∈ B lands below some v″ ∈ B, by complete pairing. Two
    elements of U above a common leaf are comparable, hence equal.

  For `flowers = false` and a flower garden of width ≥ 1, the hypothesis is unsatisfiable: a flower cannot lie below
  a block, since `CompletelyPaired` forbids it, and it is not paired. That matches the docstring. Items (1), (3) and
  (4) are unchanged.
- **D1** affects none of the above (§3, §5).

## 3. D1 and the freeze surface

`truncSumHζ` (with `FlowerRestr` and `topCountBelow`) is used only by the deferred `layergardenFlower` and the probe
`finite_truncSumHζ_support`. The Lean dependency closure (§5) confirms that no freeze-set statement reaches it.
D1 therefore does **not** block this freeze.

D1 does matter for what is *landed* with the freeze. If System is landed as one file of sealed definitions, then:

- either apply delta-1's exact fix (`kind = 0 → ∀ j, topOrder ≤ N_{p+1}` in place of `IsTrunc`);
- or keep `topCountBelow`, `FlowerRestr` and `truncSumHζ` (and, from Statements, `WTPrefixP` and
  `layergardenFlower`) out of the landed or sealed set until X1.

I recommend the second, so that X1 settles the flower carrier once (D1 + R8).

The draft definitions on the freeze surface are listed in §5 (`freezeSurface`). Those are the definitions that have
to be sealed together with the 11 anchors.

## 4. Composability (re-checked against the fixed drafts)

### `main` ⇐ `propansatz` + `nlsAkBridge` (with N1) + glue

**Parameters.** θ := η^{20}, with η := η₀(d,γ) from `WTPrefix`; θ is chosen before φin, as `main` requires. Then:

- ν := ν₀;
- 𝔇 := ⌈τ★/δ₀⌉ ≥ 1 and δ := τ★/𝔇 ≤ δ₀;
- `main`'s L₀ := max(L₀, L₁), where L₁ (depending on everything chosen) makes the error terms below small.

Then `T = τ★·T_kin = 𝔇·δ·T_kin` is literally `nlsAkBridge`'s `hT`, and `hD : 1 ≤ 𝔇` holds.

**The three conclusions of `main`.**

- **Measurability.** It is (4) with c := `initialCoeff L φin g` (measurable).
- **Probability.** On `Fev 𝔇` ∩ {rapid decay} (a.s.; glue G2), `AnsatzAt 𝔇` (1) gives an `IsAkSolution` on [0,𝔇].
  (2) then gives a smooth solution, so P(solvable) ≥ 1 − e^{−N_𝔇} ≥ 1 − e^{−(log L)^{40d}}.
- **The estimate.** Take t ∈ [0,T], s := t/(δT_kin), and p ≥ 1 with s ∈ [p−1, p].
  - On `Fev p` ∩ solvable, (1) applied to `U ω` gives an `IsAkSolution` on [0,𝔇]. Its restriction to [0,p] (glue G1:
    `HasDerivWithinAt.mono` and the bound on the subinterval) equals `a ω` by `AnsatzAt p` (1) uniqueness. So
    |û(t,n)| = |a_n(s)|.
  - (2′) gives |∫_{Fev p}|a_n(s)|² − φ(δs, n/L)| ≤ 2L^{−θ_p}, with δs = t/T_kin.
  - The symmetric difference of `Fev p` and the solvable set is a.s. inside `Fev 𝔇`ᶜ. On it, |û|² and |a_n(s)|² are
    bounded by the mass Σφin(m/L)|g_m|² (glue G3: mass conservation for NLS and for classed a-solutions).
    Cauchy–Schwarz with Gaussian moments (G4) bounds that part by C L^d e^{−N_𝔇/2}.
  - Finally, 2L^{−θ_p} + C L^d e^{−N_𝔇/2} ≤ L^{−θ}, since θ_p − θ ≥ η^{20}2^{−𝔇} and L₀ may depend on 𝔇.

The changes since snapshot 1 only weaken what `main` consumes (no smoothness of R; measurability only on [0,T]),
so the chain stands. The glue G1–G4 is unfrozen (O8 in the `propansatz` docstring; G1 is new, trivial).

### Inductive step: `AnsatzAt (p+1)` ⇐ `layergarden` + `fixedpoint` + `wkeTaylor` (+ T.cmattr, glue)

As in stage 3 §2, which I re-traced. The fixes make every regularity requirement on both sides the same finite
smoothness:

- `layergarden`'s `RemainderBound` hypothesis is literally the first conjunct of `AnsatzAt q` (2) for q ≤ p.
- `AnsatzAt (p+1)` (2) needs ‖R_{p+1}‖_{𝔖^{Λ_{p+1},Λ_{p+1}}} ≤ L^{−θ_{p+1}}. Here R_{p+1} := Re Σ_{N ≤ N_{p+1}}
  `coupleRemainder` at t = p+1, plus the Taylor tail (or the tail goes into E_{p+1}).
- That bound follows from `layergarden` (2)(b), via the 𝔖^{4Λ} bound, monotonicity of `SNorm` in (Λ₁, Λ₂) and
  `SNormR (Re f) ≤ SNorm f` (glue), together with `wkeTaylor` (1)–(2). The slack is
  (4θ_{p+1}+θ_p)/5 > θ_{p+1}, and Σ_N δ^{2νN} ≤ 2.
- No smooth (C^∞) remainder is produced or consumed anywhere. Option B is therefore internally consistent.

Downstream note: WAVE-B B2.1/B2.2 still say "every C^∞ real R_r". When they are drafted they must take the 𝔖^{40d}
bound (C^{40d}) instead, or they will not accept the R_q that `propansatz` produces (O3).

## 5. Elaboration and probes

Both probe files are in `<S>/src/WaveBDraft/` (session scratch, not in any repository), compiled as modules
against the snapshot.

**`Delta3Probe.lean`** (164 lines, sha256 `c9dcb9bf…03c82e01`; 0 errors, 81 s).
- `no_smooth_solution_T0`: no `u` satisfies `IsSmoothNLSSolution 1 1 0 c1 u` for `c1 = δ_{n,0}`. The proof uses
  `eq_of_torusFourierCoeff_eq` and `torusFourierCoeff_torusChar` to get u(0) ≡ 1, then
  `derivWithin_zero_of_not_accPt` on `Icc 0 0 = {0}`, and the equation at x = 0 gives 1 = 0.
- `akSolution_T0`: `IsAkSolution 1 0 1 0 c1 (fun _ => c1)`, via `hasDerivWithinAt_singleton_self`.
- `nlsAkBridge_D0_refuted : False`: `nlsAkBridge.{0}` at d = 1, L = 1, γ = 0, δ = 1, 𝔇 = 0, α = 1, T = 0, item
  `.2.1`.
- `#print axioms`:
  - `no_smooth_solution_T0`, `akSolution_T0`: `[propext, Classical.choice, Quot.sound]`;
  - `nlsAkBridge_D0_refuted`: the same plus `sorryAx`, which is the draft `nlsAkBridge` anchor itself. **The draft
    statement implies `False`.**
- `wtDeps`/`run_cmd`: the transitive `WaveTurbulence.*` dependency closure of each freeze statement. It follows
  types, and the values of non-theorems; it does not follow the anchors' `sorry` proofs. Output:
  - `cumulantExpansion present: false`.
  - B1.12-only objects reached (`truncSumHζ`, `FlowerRestr`, `topCountBelow`, `WTPrefixP`, `KGflower`,
    `layergardenFlower`): **none**, for each of `propansatz` (163 deps), `layergarden` (164), `fixedpoint` (181),
    `nlsAkBridge` (21), `wkeTaylor` (32), `sumint` (97), `countLemma` (5), `atomCountLemma` (5), `quadExpSum2` (9),
    `quadExpSum3` (9) and `canonicalCharacterization` (77).
  - **Freeze surface.** 202 draft constants, excluding auxiliary `_proof_`/`match_`/`inst` names and the anchors
    themselves. These are the definitions to seal with the anchors:

    `AnsatzAt`, the forest carriers (`GNode`, `GLeaf`, `GBranch` and their API, `TTree.*`, `forestSet`),
    `Garden.*` (including `IsFlowerGarden`, `IsFlowerParent`, `IsLoneParent`, `FreeBranch`, `extendTime`),
    `MarkTag`, `GenDecoration`, `IsDecoration`, `IsBranchConsistent`, `IsBalancedSig`, `IsCanonC/G/GC/H`,
    `IsCouple`, `IsGaussianData`, `IsSymmetricEvent`, `IsUnitCoeff`, `KG`, `KQ`, `KQstar`, `LayeredGarden.*`
    (`AttachLinked`, `AttachLinkedOn`, `BelowSet`, `CanonCriterion`, `CanonInd`, `IrreducibleAt`, `IsTrunc`,
    `OnStem`, `TopDecomp`, `TopDecompWith`, `TopRegion`, `attachNodes`, `attachedOrder`, `leavesBelowSet`,
    `parentLayer`, `roots`, `topOrder`), `Lop`, `Slot`, `slotCountB`, `slotOrder`, `NearLattice`,
    `RemainderBound`, `SNorm`, `SNormR`, `SumintDatum.*`, `SumintShape.*`, `TreeDecoration`, `WTParams.*`,
    `WTPrefix`, `WTPrefixA`, `XNorm00`, `XNorm00Restr`, `ZNorm`, `ZNormOn`, `ZSpace`, `aTr`, `chi0`, `chi0Vec`,
    `cosetDecoration`, `coupleRemainder`, `coupling`, `eZ`, `epsDec`, `inputLeaves`, `inputsF`, `iterPartial`,
    `jbr`, `jbrProd`, `kDomain`, `kernelK`, `maxBracketPow`, `nodeSign`, `omegaNode`, `partialMom`,
    `phaseIntegral`, `phaseProd`, `resFactor`, `single`, `timeFT`, `treeSign`, `treeTerm`, `treeTermN`,
    `treeTimeDomain`, `truncSum`, `truncSumC`, `wkeTaylorTerm`, `zpowSign`.

    The surface does **not** include `truncSumHζ`, `FlowerRestr`, `topCountBelow`, `KGflower`, `KTstar`,
    `XNorm` or `XNormRestr`.

**`Delta3Fix.lean`** (58 lines, sha256 `cdf34d2c…92c3c426`; 0 errors; only unused-binder linter warnings).
- `NlsAkBridgeFixed : Prop` is the N1 replacement statement (the draft plus `(hD : 1 ≤ D)`).
- `nlsAkBridge_implies_fixed : NlsAkBridgeFixed` (from the draft), so the fix is a pure weakening.

## 6. REQUIRED items (open)

1. **N1** — `nlsAkBridge`: add `(hD : 1 ≤ D)` after `(D : ℕ)` (§2.1), and docstring deviation D3.

No other REQUIRED item.

**Landing condition (not a statement change).** Do not seal `truncSumHζ`, `FlowerRestr`, `topCountBelow`,
`WTPrefixP` or `layergardenFlower` with this batch (D1, R8). If System is landed whole, apply delta-1's D1 fix to
`truncSumHζ` first.

## 7. OPTIONAL

- **O1.** `countLemma`: the binder `∀ η ∈ Ioc 0 η₀` is unused in the body. It is harmless (C may depend on η) but
  vacuous; drop it or say so in the docstring. Pre-existing.
- **O2.** `canonicalCharacterization` docstring: "(and ℋ^tr, T L2288)". Given D1, `IsTrunc` is ℋ^tr only for the
  𝒳 kind; the 𝒴/𝒲 reading is X1's. Add "kind 0" or drop the parenthesis.
- **O3.** WAVE-B §4.11–§4.12 (B2.1/B2.2): replace "every C^∞ real R_r" by "every real R_r with
  ‖R_r‖_{𝔖^{40d,40d}} ≤ L^{−θ_r}" (Option B).
- **O4.** DESIGN §6 B1.4 still says "the classed `IsASolution`", and Q8 still places `truncSumHζ` in the statements
  file (delta-1 O1). Refresh it when recording N1.
- **O5.** Add `IsAkSolution.mono` (restriction from [0,𝔇] to [0,p]) to the unfrozen glue list (G1, §4). `main`
  uses it.

## 8. Questions for the author

1. **R1 (pending):** confirm Option B: the remainders R_q are C^{Λ_q} (finite smoothness, forced by the 𝔖 bound),
   not C^∞. Note that in this Mathlib `ContDiff ℝ ⊤` is C^ω and C^∞ is `(⊤ : ℕ∞)`. If confirmed, B2.1/B2.2 take
   𝔖^{40d} inputs (O3). If you want C^∞ (Option A), `propansatz` needs an extra mollification lemma, and
   `RemainderBound`/`AnsatzAt` get `ContDiff ℝ (⊤ : ℕ∞)`.
2. **R8 (pending):** confirm that B1.12 `layergardenFlower` stays out of this freeze and waits for packet X1. X1
   would generalize the kernel to designated fixed-time nodes and cutoffs, and fix D1.
3. **R9 (pending):** confirm that `cumulantExpansion` stays the unfrozen target T.cmattr. Whoever states it uses
   DESIGN CL-9's range and adds the m = 1 couple case.
4. **N1:** approve the added hypothesis `1 ≤ 𝔇` in `nlsAkBridge`. It is forced: the statement is false at 𝔇 = 0.
5. **Still open from stage 3 (question 3), `sumint` D7:** are the shifts h₁, h₂ in every consumer integer
   combinations of (e,f,g,h) with coefficient sum 1 and no constant lattice offset? The draft's docstring now
   discloses this reading. If a consumer needs an offset, the datum gets `c₁ c₂ : S.VIdx → (Fin d → ℤ)` before
   freezing.
6. **FINDINGS:** record the two candidate errata.
   - T (atomcountbd) L2472 needs k ≠ 0 for ε = (+,−), γ > 1/2 (R4).
   - T L2288 is empty for 𝒴/𝒲 if read literally (delta-1 D1).
