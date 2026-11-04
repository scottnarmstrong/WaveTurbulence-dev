# FLOWER redraft review (Task 13): B1.12, `kernelKgen` bridges, the `^ζ` erratum, the 𝒴/𝒲 sign

Auditor: `wt-orch` (Opus), refute-first. Date: 2026-11-03. Subject: wt-gauss-hc's packet X1 in
`/home/scott/wt-scratch/flower/`:
- `FLOWER-DESIGN.md` (284 lines);
- `Flower-Gate.lean` (frozen candidate);
- `Flower-Gate-probes.lean`, `Flower-Trees.lean`, `Flower-Ops.lean`, `Flower-Ident.lean`, `Flower-Kernel.lean`,
  `Flower-Obligations.lean`.

**Sources.**
- TARGET L2257–L2338: Def `defflower`, (jtflower), (kqflower), (operatorx), (operatorxker), the 𝒴/𝒲 classes,
  Prop `flowerest1` with its proof, and the proof of `fixedpoint`.
- DH23 `Revision_Submit.tex` L503–L508: Prop `mainprop2`, (parametrix), (kernelexp).
- DH21 `Inventiones-Final_Version.tex` L2651–L2700: Def 11.1, Prop 11.2 (`L^nexpansion`) and its proof, Cor 11.3.

**Build check.** On my own snapshot-5 roots, one `lake env lean` at a time, I rebuilt `Flower-Gate.lean` (sha
`52f11d66becc…`), `Flower-Gate-probes.lean` (`be3708569c18…`), `Flower-Trees`, `Flower-Ops` and `Flower-Ident`.
- **0 errors.** The only `sorry` is the B1.12 anchor.
- **Axioms** `[propext, Classical.choice, Quot.sound]` for `kernelKgen_flowerParents`, `kernelKgen_noFix`,
  `coupleSum_tr`, `one_sub_L1op_Xop` and `Xop_one_sub_L1op`. Only `layergardenFlower` adds `sorryAx`.
- **The identities as stated:** `Xop b − L1op (Xop b) = b − Yop b` and `Xop (b − L1op b) = b − Wop b`, for
  `b` in the class `Good` (continuous in t, with a summable majorant uniform in t), which contains `ZSpace` for Λ > d.

**O-FK.** At review time the packet reports O-FK (`fOp_kernel_rep`) proved in `OFK-*.lean` (1395 lines, local
commits up to `baef7c5` plus uncommitted edits in progress). I did not review or build it here; it is not needed for
B1.12.

## Verdict

- **The `^ζ` erratum: CONFIRMED.**
- **The 𝒴/𝒲 sign claim: CONFIRMED** (derivation in §2).
- **The `kernelKgen` bridges: correct and conservative.**
- **B1.12 redraft: faithful to `flowerest1` and sufficient for the proof of `fixedpoint`.** It is
  **freeze-ready after two small edits** (F1, F2). There is no REQUIRED mathematical change.

Recommendations on the author's decisions (FLOWER-DESIGN §6):
1. **Freeze B1.12 in the concrete form: YES**, after F1–F2.
2. **D2 exponents: keep `δ^{2νN}` for flowers and `δ^{νN}` for couples** (as drafted). Do not switch couples to `2ν`.
3. **Approve both readings:** `^ζ` as an erratum, the 𝒴/𝒲 sign as a precision.

## 1. The `^ζ` erratum (TARGET (operatorx), L2268)

**TARGET prints:** `(𝒳b)_k(t) = Σ_ζ Σ_{k'} ∫_p^t 𝒳^ζ_{kk'}(t,s) b_{k'}(s) ds`, with no exponent on `b`.

**Evidence the exponent belongs there:**
- DH23 Prop `mainprop2` (L503), defining the kernel of any ℝ-linear operator, has `b_{k'}(s)^ζ`.
- DH21's proof of Prop 11.2 (L2680–L2686) says that "the linear (or conjugate linear) part of `ℒⁿ` corresponds to
  the flower of `𝒯` having the same (or opposite) sign as the root".
- TARGET's own ℒ₁ (eqnbk1.5) is ℝ-linear, not ℂ-linear: in the middle slot of `𝒞₊` the input `b` enters as `b̄`.

**Conclusion.** Without `^ζ`, the `ζ = −` kernels would act on `b` instead of `b̄`, making 𝒳 ℂ-linear, so
`(1−ℒ₁)𝒳 = 1+𝒴` could not hold. The adopted reading `b^ζ` (`kernelOp`) is the only one consistent with DH21/DH23
and with `ℒ₁`.

**Confirmed: record as a FINDINGS erratum.** It affects only the operator identities (packets X2/I2), not the norm
bounds in B1.12.

## 2. The sign of 𝒴, 𝒲 (TARGET L2273: "the same expression")

Write `𝒳 = 1 + X₊` with `X₊ = Σ_{1≤n(F)≤N} 𝒥_F`.
- **ℒ₁ is root attachment.** `ℒ₁ b = Σ_{i,T₁,T₂ (n ≤ N)} 𝒥_{node i 𝔣 T₁ T₂}[b]`, and `ℒ₁ 𝒥_F[b] = Σ 𝒥_{node i F T₁ T₂}[b]`
  (DH21 Prop 11.2's proof: "attaching two sub-trees to a single node").
- So `ℒ₁𝒳 = Σ_G 𝒥_G` over all `G = node i F T₁ T₂` with `n(F), n(T₁), n(T₂) ≤ N`, F possibly trivial.
- **Split by n(G).**
  - Those with `1 ≤ n(G) ≤ N` are exactly `X₊`: each such G has all root children of order ≤ N, and the root
    decomposition is unique.
  - Those with `n(G) > N` are exactly the (Y) class (Y-1, Y-2).
- **Hence `(1−ℒ₁)𝒳 = 1 + X₊ − X₊ − Y₊ = 1 − Y₊`**, i.e. `𝒴 := (1−ℒ₁)𝒳 − 1 = −Σ_{(Y)} 𝒥̃`.
- **The same argument for 𝒲.** `𝒳ℒ₁` is flower-end attachment; the unique bottom decomposition gives (W-2) and
  (W-3). So `𝒲 = −Σ_{(W)} 𝒥̃`.

**Confirmed.** TARGET's "same expression" holds up to an overall minus sign. DH23 (kernelexp) is consistent: it
defines `𝒴 := (1−ℒ)𝒳 = 1 + Σ 𝒴_m`, with the sign absorbed into `𝒴_m`.
- The sign is irrelevant for the Neumann series and the norm bounds `‖𝒴‖, ‖𝒲‖ ≤ 1/2` (TARGET L2335).
- It matters for exact identities. The Lean statements `𝒳b − ℒ₁𝒳b = b − Yop b` and `𝒳(b−ℒ₁b) = b − Wop b` are the
  right ones.
- **Recommend recording it as a precision, not an erratum.**

**Related (already ledgered).**
- F39, the identity term, is settled by DH23 (kernelexp): `𝒳 = 1 + Σ_{m=1}^N 𝒳_m`.
- F25: the prefactor `L^{d−1}` in (jtflower)/(kqflower) is DH21's γ = 1 normalization (DH21 (defkerLn) uses `δL²`);
  `L^{d−γ}` matches TARGET's own (defkg) and the phases' `L^{2γ}`.

## 3. The `kernelKgen` bridges (`Flower-Gate-probes.lean`)

| Bridge | Verdict | Notes |
|---|---|---|
| `kernelKgen_flowerParents`: with only the flower parents designated (time `s`), no removed phase and weight 1, `kernelKgen = kernelK` with up `t` and flower time `s` | CORRECT | Hypotheses: a flower garden; flower parents in layer `p`; `p < s < p+1`; `0 < s < t`. Inside `flowerSum` all are supplied by `IsCanonH` (stems in layer `p`) and the range `p < s < t ≤ p+1`. Uses `flowerParent_unique` (one flower per tree, from `IsFlowerGarden`). |
| `kernelKgen_noFix`: for plain gardens, nothing designated, `kernelKgen = kernelK` | CORRECT | — |
| `coupleSum_tr`: `coupleSum … .tr false = truncSumC (p+1)` | CORRECT | The filters coincide (`IsTrunc` = `TreeKindOK .tr` plus the attached-order bound). |

So the plain `flowerSum` of kind X is the old `truncSumHζ` with corrected kinds. The generalization is conservative:
it adds data (designated nodes, removed phases, weights) without changing the base objects.

## 4. B1.12 `layergardenFlower`: statement review

### 4.1 Faithfulness to `flowerest1` (TARGET L2279–L2305)

| Element | TARGET | Redraft | Verdict |
|---|---|---|---|
| Moment order | `P` large depending on `C₁`, `δ` small depending on `P` | `WTPrefixP`: `∃ P₀ ∀ Pm ≥ P₀` after `ν`, before `δ` | ✓ (P may also depend on ν; harmless) |
| Garden class | width `2P`, `ℋ^tr_{p+1}`: initial trees `≤ N_{p+1}` (top count, L2290), attached gardens `≤ N_p` | `IsCanonH (p+1)`, attached `≤ N_p`, `FlowerKindOK` | ✓ |
| Flower signs, decorations | `𝔼|𝒳^ζ|^{2P}`: P copies and P conjugates; `(k,k')`-decorations | flower sign `ζ·ζ_j`; roots `n`, flowers `n'` | ✓ |
| Per-order bound | `⟨k−ζk'⟩^{−4Λ_{p+1}P} L^{(100d)³P} δ^{2νn}` (L2305) | identical, `N ≤ N_{p+1}^4` (L2290) | ✓ |
| `M₁` cutoff | `max_{ℓ≠𝔣} |k_ℓ| ∼₀ M₁` (≲₀ if `M₁ = L`); factor `M₁^{−80dP}` | `dyadicCut` on the initial tree's non-flower leaves (`IsTopLeaf`), same `j₁` for all trees | ✓ (D7 makes the smooth cutoff explicit; support `M/4 < |x| < M`, or `< L`) |
| `M₂` cutoff | `|k| ≥ M₁^{10}`, "further" restrict `max_{𝔫∈𝒮} |Ω_𝔫| ∼₀ M₂`, 𝒮 = stem minus `𝔣^pr`; factor `M₂^{−P/9}` | `cutWeight2` over `OnStem ∧ ¬IsFlowerParent`; hypothesis `cut2 → ∃ cut1, (2^{j₁}L)^{10} ≤ |k|` | ✓ |
| 𝒴, 𝒲 | the same, with `e^{−100N_{p+1}}`; classes (Y-1)–(Y-2), (W-1)–(W-3) in top counts (L2290) | kinds `Y`, `W` replace the top bound (F46/D1); the consumer sums `N ≥ 2P(N_{p+1}+1)` | ✓ (W-3: top order minus `topCountBelow(𝔣^pr)`, which counts `𝔣^pr` itself, as TARGET's "replace `𝔣^pr` by a flower") |
| Prefactor | `L^{d−1}` (typo) | `L^{d−γ}` | ✓ (F25) |

### 4.2 Sufficiency for `fixedpoint` (TARGET L2306–L2338)

| Use | Needed | Supplied by |
|---|---|---|
| Part 1 (trterm1), `a^tr` | `𝔼|a^tr|² ≤ L²⟨k⟩^{−4Λ}` | B1.2 (`truncSumC`; bridge `coupleSum_tr`) |
| Part 1, `ℒ₀` | the same with `e^{−100N_{p+1}}` | (2), kind `ℒ₀`. `δ^{νN}` summed over `N ≥ 2(N_{p+1}+1)` gives `e^{−100N_{p+1}}` for `δ` small depending on `ν`; the `L^{100d}` loss is absorbed |
| Part 1, `∂_t a^tr`, `∂_t ℒ₀` | `δ(t_𝔯 − t)` bounds with an `L^{100d}` loss | (2), `dt` (the roots fixed at `t`) |
| Part 2 (2)–(3) | `(k,k')` fixed, `M₁` cutoff, with or without `M₂` (the latter when `|k| ≤ M₁^{10}`) | (1), `cut1`, optional `cut2` |
| Part 2 (5) | `𝒥^†`: sibling labels fixed, phase at `𝔣^pr` removed | (1), `dagger` (`sibWeight` plus `off`). Labels may differ per tree, which is more general |
| Part 2 (7) | plain kernel with the `M₂^{−P/9}` gain | (1), plain patterns: the `M₂` factor is kept, with or without `dagger` |
| Part 2 (8) | `∂_{t,s}` of `𝒥^†`: `δ(t_𝔯 − t)` or `δ(t_𝔫 − s)` at the parent or a non-flower child of `𝔣^pr`; extra loss `L^{(100d)³P}`, `M₂` gain possibly lost | (1), patterns `dRoot`/`dParent`/`dChild i` with `c = 2` and no `M₂` factor. The `M₁` factor is kept, which the consumer needs to sum over `M₁` |

The boundary-term reading (D8) is right:
- `∂_s 𝒥^†` puts `t_{𝔣^pr} = s` on the boundaries `t_{parent} = s` and `t_{child} = s`. The constraint between the
  two designated nodes is exactly that boundary, so it must be dropped. With `kDomain`'s strict inequalities every
  such kernel would be 0.
- There is no phase-derivative term, since `†` removed the phase at `𝔣^pr`.
- `∂_t` hits only the root's constraint `t_𝔯 < t`.
- For `𝔣^pr = 𝔯`, `PatValid` excludes `dRoot` (the kernel is t-independent, so `∂_t = 0`) and `dParent` (no
  parent). These are TARGET's "trivial adjustments".

**D10 is genuinely needed.** TARGET's "the same proof … using (taylorbound) and (estcouple2)" (L2312) bounds `ℒ₀`'s
couples, but these form a class disjoint from B1.2's `𝒞^tr` (tree orders `> N_{p+1}`). (estcouple2) controls only the
remainder of the **full** sum, so B1.2 does not imply the `ℒ₀` bound.

### 4.3 Points to fix before freezing (no mathematical change)

- **F1 (range).** (1) allows `t = p+1` (`Ioc`). TARGET defines the flower kernels for `p+1 > t > s > p`, and the
  consumer uses only `L^{2P}_{t,s}` norms (a.e.) and continuity. Either restrict to `t ∈ Ioo p (p+1)`, which
  matches TARGET and `coupleSum`'s range and removes a boundary case from the proof (recommended), or add it to the
  deviations as D11. As drafted it is an undisclosed extension: the docstring says `t ≤ p+1`, but D1–D10 omit it.
- **F2 (bookkeeping).** List in the docstring's deviations that (1) quantifies over **per-tree** `†` labels and
  **per-tree** patterns, which is more general than the consumer's uniform choice. This is harmless (the proof is
  per tree), but a frozen statement should say so. Also record in `FLOWER-DESIGN.md` that the `M₁` factor is kept
  for derivative patterns.

## 5. Recommendations on FLOWER-DESIGN §6

1. **Freeze B1.12 in the concrete form: YES, after F1–F2.** The abstract alternative (arbitrary weights with bounded
   𝔖-norms) would need its own characterization of which weights arise, and would move the burden to the consumer.
   The concrete form is exactly what L2306–L2338 consume (§4.2). Its base cases reduce to the frozen
   `kernelK`/`truncSumC` by proved bridges (§3).
2. **D2: keep `δ^{νN}` for couples.**
   - It suffices: the consumer needs only `Σ_{N≥2(N_{p+1}+1)} δ^{νN} ≤ e^{−100N_{p+1}}`, and `δ` is chosen after `ν`.
   - It is strictly weaker. The restricted `ℒ₀` class includes regular-couple contributions of size `≲ C₂(C₁δ)^{N/2}`
     that are not subtracted (unlike (estcouple2)'s remainder). `δ^{2νN}` would then additionally require `ν < 1/4`.
   - The flower clause's `δ^{2νN}` is TARGET's literal L2305 and should stay.
3. **Approve both readings:** `^ζ` (§1) as a FINDINGS erratum (TARGET L2268), and the 𝒴/𝒲 sign (§2) as a precision.
   Neither enters B1.12. Both matter for the operator identities, which are proved for the Lean operators, and for
   the bridge obligation O-FK.

**Other notes.**
- O-FK, the kernel representation of `𝒥_F`, is not needed for B1.12. The packet now reports it proved; that work
  was still being edited at review time and should be reviewed when it is committed.
- The design memo's "Lean `ℒ₁` is ℝ-linear (middle slot conjugated)" agrees with my Task 11 review of
  `treeTerm_node` (F9 sign convention).
