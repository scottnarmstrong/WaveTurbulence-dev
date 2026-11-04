# Statement audit: X3 FIXEDPT (`fixedpoint_of_gates`, wt-gauss-hc)

Auditor: `wt-orch`, refute-first. Date: 2026-11-04 (Task 29b). Findings only; nothing was edited.

**Scope.**
- `/home/scott/wt-scratch/fixedpt` (`X3-HANDOFF.md`): `fixedpoint_of_gates`, and whether its gate types are
  snapshot 7's exactly.
- The two named obligations O-X2-EXP and O-X3-CPL. Are they faithful to what TARGET's proof asserts (T L2279–L2338:
  `flowerest1`, `fp.part1`), and no stronger than the source can give?

## Verdict

**PASS.**
- **Exact type.** `fixedpoint_of_gates : LayergardenFlowerGate → OX2Exp.{u} → Gates.LayergardenGate →
  Gates.WkeTaylorGate → OX3Cpl.{u} → Gates.FixedpointGate.{u}`, checked on the elaborated type.
- **The gates are snapshot 7's.** The four gate types equal snapshot 7's B1.12, B1.2, B1.5 and B1.3 in one environment.
  The 216 snapshot constants reachable from the gates and the obligations are identical to my snapshot-7 build,
  including the F68 `PatValid` and `flowerSum`.
- **Axioms:** [propext, Classical.choice, Quot.sound].
- **The obligations are faithful.** Both assume only TARGET's inductive hypothesis. They state its intermediate
  moment expansions, with errors that the source's own treatment makes far smaller than required.
- **Findings:** X-1 (stale labels), X-2 (recommendation for the pending "hM gap" ruling: do not change B1.3), X-3
  (watch items for discharging the obligations).

## 1. Inputs

**The trees.**
- `fixedpt`: local git `98964f6` (04:13). Pinned at 05:33: 75 files, list digest `1893d86e56a1…`.
- `flower`: local git `e91a8d7` (04:25, F68). It holds the gate copies and both obligations. Pinned at 05:41: 41
  files, list digest `a0f4ea153335…`.
- Both were re-verified unchanged at the end.

**Key files** (sha256 prefixes):
- `X3-HANDOFF.md` `e097e6117fff…`, `X3-Part2.lean` `06250358e5c3…`, `X3-Part2Op.lean` `634e88dfbca9…`;
- `X2-Est.lean` `e9ff71917ee3…`, `X2-Couple.lean` `8817437a7480…`, `X2-Kernel.lean` `c7dc1e85e96d…`,
  `X2-Gates.lean` `a9ef73127308…`;
- `Flower-Gate.lean` `a7c15279f10b…`, byte-identical to snapshot 7's `WaveB1-Flower.lean`.

**The snapshot copies.** `duhamel/src/WaveBDraft/{Core,System,Statements,Lemmas,CoreProbes}.lean` are byte-identical
to snapshot 7.

**Build consistency.** The handoff was written before F68, but the build is after it.
- Flower's `Gate` was rebuilt at 04:20:32, and the X3 oleans at 04:21–04:24.
- In `X3Part2`'s import closure there are 73 local modules: 36 X3, 18 flower and 19 duhamel. Every olean is newer
  than all of its transitive imports, and every source equals its committed file.
- The gauss-hc base build has not changed since 01:27. Its toolchain and packages are dev's.

## 2. The gate types against snapshot 7

**The type and axioms.** `fixedpoint_of_gates` has literally the arrow above, with level parameters `[u]`. Its axioms
are standard.

**One environment.** I ran a probe in X3's own environment, read-only.
- It unfolds the gate abbreviations: `Gates.*Gate/*Body`, `LayergardenFlowerGate`, `B112Body`.
- It elaborates snapshot 7's statement texts in the same file:
  - B1.2, B1.3, B1.5 with the opens of `WaveB1-Statements.lean`;
  - B1.12 with those of `WaveB1-Flower.lean`, including its `open Classical in`.
- **All four are syntactically equal** after zeta and beta reduction and erasing proofs. In raw form, B1.12 differs
  only by the beta-redex `(i : Fin d) → (fun _ => ℝ) i` in an instance argument.

**Closure.** The snapshot constants reachable from the four gates and the two obligations number 216: `WaveBDraft`,
`FlowerDraft.Gate` and Wave A frozen definitions. They are **identical** to my snapshot-7 build, including
`LayeredGarden.PatValid` and `flowerSum`.

**B1.12 under F68.** X3 consumes B1.12 only at the `plain` and `dRoot` patterns, which F68 does not change. The
conditional result is against snapshot 7.

## 3. The obligations against TARGET

| | O-X2-EXP (`X2-Est.lean`, prefix `(Π_P)`) | O-X3-CPL (`X2-Couple.lean`, prefix `(Π)`) |
|---|---|---|
| hypotheses | probability data; `∀ q ≤ p, AnsatzAt` | the same |
| object | `𝒦` = `randFlowerKernel` from `a(p)`, any kind; pattern `plain`/`dRoot`; optional `†`; cutoffs with B1.12's side condition; `t ∈ (p,p+1)`, `s ∈ (p,t)` | `X` ∈ {`a^tr`, `ℒ₀`, `∂_t a^tr`, `∂_t ℒ₀`} from `a(p)`, `t ∈ (p,p+1)` |
| conclusion | `\|𝒦\|^{2Pm}` integrable on `F_p`, and `\|𝔼_p\|𝒦\|^{2Pm} − ∑_{N ≤ N_{p+1}^4} flowerSum_N\| ≤ x2Bound · e^{−101N_{p+1}}` | `\|X\|²` integrable, and `\|𝔼_p\|X\|² − ∑_{N ≤ N_{p+1}^4} coupleSum_N\| ≤ ⟨k⟩^{−4Λ_{p+1}} e^{−101N_{p+1}}` |
| TARGET | (flowerexp2) L2288; `𝓔⁽¹⁾`, `𝓔⁽²⁾` "treated as in the proof of Prop propansatz" and `n(𝒢) ≤ N_{p+1}^4` (L2290); used by Part 2 (1), (6), (8) (L2323–L2331) | Part 1 L2308–L2312 ((trterm1) "by repeating the arguments of propansatz"; `ℒ₀` with `e^{−100N}`; `∂_t` with the arguments of `flowerest1`); used by the Sobolev step L2313–L2316 |

`x2Bound` is B1.12's right-hand side without `δ^{2νN}`.

**1. Hypotheses.**
- Both obligations assume only `∀ q ≤ p, AnsatzAt`. That is TARGET's inductive hypothesis, (1)–(4) at `q ≤ p`
  (L708–L709). There is no extra premise.
- Their prefixes are TARGET's. For O-X2-EXP, "`P` large depending on `C₁`, `δ` small depending on `P`" (L2279) is
  `(Π_P)`, as in B1.12.

**2. Objects.**
- `a^tr` and `ℒ₀` are the frozen `aTr` and `Lop … 0`. `Lop` is evaluated at `b = 0`, and `ℒ₀` does not depend on `b`.
- The `∂_t` variants are the Duhamel integrands: TARGET's extra `δ(t_𝔯 − t)` factor (L2312).
- `randFlowerKernel` is X2's sum, over the kind's flower trees with sign `ζ`, of the (jtflower) kernel (T
  (operatorxker), L2270–L2273).
- **Its identity with the frozen operator is proved, not assumed.** The frozen `Lop` equals the parametrix `Xker/Yker/
  Wker` (O-FK, flower). `Xker_eq_rand`, `Yker_eq_rand` and `Wker_eq_rand` (`X3-Part2Op`) equate those with
  `randFlowerKernel`.

**3. Conclusions.**
- The obligations state TARGET's intermediate expansions: "moment = garden or couple sum + small error". TARGET
  displays only the resulting bounds, (flowerest2) and (trterm1).
- Lean derives those bounds from B1.12 and B1.2 (`flowerest1_of_gates`, `cplMoments_of_gates`).
- The split is finer than TARGET's statements, but it is exactly what TARGET's proof asserts at L2288–L2290 and
  L2310.

**4. Error size.** TARGET leaves `𝓔⁽¹⁾` and `𝓔⁽²⁾` to the proof of Prop `propansatz`.
- `𝓔⁽¹⁾` contains `E_p` or `Ẽ_p`, which are `≤ e^{−N_p}` with `N_p = R_p^{40d} = N_{p+1}^{(40d)²}` (T (parameters2);
  `WTParams.N`, `.R`).
- `𝓔⁽²⁾` collects orders `n > N_{p+1}^4`, which carry `δ^{νn}`-type factors.
- Both are far below `e^{−101N_{p+1}}` once `L` is large, since `N_{p+1} ≥ log L`. **The obligations are not stronger
  than the source.**
- The decay `⟨k − ζk'⟩^{−4Λ_{p+1}Pm}` (resp. `⟨k⟩^{−4Λ_{p+1}}`) is available from the inputs, because
  `Λ_p = 40d·Λ_{p+1}`.

**5. Moment orders.**
- `|𝒦|^{2Pm}` involves at most `2Pm(2N_{p+1}+1)` factors of `a(p)`, and `|X|²` at most `2(2N_{p+1}+1)`.
- `AnsatzAt` (3) controls cumulants up to `2R_p = 2N_{p+1}^{40d}` factors.
- `Pm` is fixed before `L`. The needed orders are inside the hypothesis.

**6. Restrictions.**
- O-X2-EXP covers only the `plain` and `dRoot` patterns; O-X3-CPL takes `t` in the open interval.
- Both restrictions make the obligations weaker than what TARGET's own route uses. They match X3's operator bound
  `sup_t ∫|𝒦(t,s)| ds` in place of `sup_{t,s}|𝒦|`, which needs `∂_t` only (X3-DESIGN; handoff finding 2).
- Restricting to `plain`/`dRoot` also keeps O-X2-EXP clear of the `dChild` question that F68 settled.

## 4. Findings

**X-1 (doc).** Labels are stale.
- `X3-HANDOFF.md` says B1.12 is the "snapshot-6 text" and B1.3 the "snapshot-5" gate.
- The docstring of `fixedpoint_of_gates` says "B1.12 (snapshot 6)" and "B1.3 (snapshot 5)".
- The built result is against snapshot 7 (§2). Relabel.

**X-2 (pending ruling; my recommendation).** The open "hM gap", raised by wt-gauss-hc with wt-cumul:
- **The gap.** INDUCT's cmattr identity needs all-order ℓ¹ moments of `a(p)` on `F_p`. That is
  `AnsatzPrefixData.l1_moments`, an INDUCT-internal invariant. `AnsatzAt` does not state it: its class bound's
  constant depends on ω.
- **Option A** adds these moments to B1.3. That would put a premise into a frozen source statement that TARGET's Prop
  `fixedpoint` does not have, and would change B1.3. **Do not take it.**
- **Option B (recommended):** derive the finite-order moments the obligations need from `AnsatzAt`:
  - **Pairs:** clause (2).
  - **Balanced cumulants:** clauses (3)–(4) bound every balanced cumulant of order `≤ 2R_p`, with
    `∏⟨n_j⟩^{−Λ_p}` decay.
  - **Unbalanced cumulants** vanish by gauge symmetry: the event is symmetric, the solution map is equivariant and
    the Gaussian law is gauge invariant.
  - So `𝔼_p|a_n(p)|^{2m} ≤ C_m ⟨n⟩^{−c}` for `m ≤ R_p`.
  - Minkowski and monotone convergence over momenta then give integrability and the exchange of `𝔼` with the
    momentum sums, for every order up to `2Pm(2N_{p+1}+1) ≪ 2R_p`.
- This is my assessment, not a Lean proof. On it, neither obligation needs to be weakened and B1.3 need not be
  strengthened.

**X-3 (watch items for discharging the obligations; not statement defects).**
- **(a) The cutoff gains on the errors.** O-X2-EXP's error must carry `x2Bound`'s `M₁` and `M₂` cutoff factors
  uniformly in `(j₁, j₂)`.
  - `M₂` is unbounded, so the smallness of `e^{−N_p}` alone does not give this.
  - The per-tree time-integration gain must be taken before the pairing, as TARGET's proof of `flowerest1` does at
    L2299 (its item (6): "integrating in `t_j` before manipulating everything else").
  - TARGET asserts the cutoff variants of (flowerest2) (L2283–L2285), so this is within the source. It is the place
    where a discharge could stall.
- **(b) Constant choices.** The obligations use one constant pattern and one constant `†` across the `2Pm` trees.
  B1.12's per-tree generality (D11) is not needed.

**Recorded earlier.** The `Pm ≥ 100(d+1)²` choice (handoff finding 1) was accepted by the orchestrator. It lies inside
`(Π_P)`, where `Pm` is chosen after `ν`.
