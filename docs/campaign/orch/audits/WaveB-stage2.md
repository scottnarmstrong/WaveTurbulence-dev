# Audit: Wave B stage 2 (system definitions, `WaveB1-System.lean`)

Auditor: `wt-orch` (Opus), refute-first. Date: 2026-11-03. Task 4b, stage 2.

## Inputs

**Snapshot.** The frozen snapshot `/home/scott/wt-scratch/waveb-snap-1/`; `sha256sum -c SHA256SUMS` passes. The files I
audited:

| File | Lines | sha256 |
|---|---|---|
| `WaveB1-System.lean` | 507 | `ffb5fb69…673991aa7` |
| `WaveB1-System-probes.lean` | 190 | `4902e26b…37e34976` |
| `DESIGN.md` (§5 and the definitional questions Q5, Q6) | — | `625952e2…442f6b` |

**Source.** `paper/source/WKE-Longer_times_Final_arXiv.tex`, sha256 `493eef6b…727cb`.

**Build.** As in `WaveB-stage1.md` (modules `WaveBDraft.*`, no `lake build`). System imports only `WaveBDraft.Core`,
`Frozen/Defs/{CollisionOp, InitialCoeff}` and the landed `Foundations/Cumulant/Basic`; every path resolves.
- `WaveB1-System.lean` elaborates with exactly two `sorry`s: the draft obligations `summable_kernelK_summand` (L488)
  and `truncSum_untruncated` (L500).
- `WaveB1-System-probes.lean` elaborates sorry-free. `#print axioms` on `KG_trivialCouple`, `KG_trivialCouple_off`,
  `finite_truncSum_support`, `isCanonGC_iff_G`, `isCanonGC_iff_C`, `chi0_of_abs_le_half` and `chi0_neg` gives
  `[propext, Classical.choice, Quot.sound]`.

**Stage 1 carries over.** Stage 1's R1 (`attachedOrder`) also governs every `truncSum*` defined here. The numbering
below continues from stage 1.

## Verdict

**NOT APPROVED. Three REQUIRED fixes.**

- **R4 (`AnsatzAt`): `ContDiff ℝ ⊤` means analytic.** In Mathlib v4.35, `ContDiff ℝ ⊤` is `ContDiff ℝ ω`, i.e.
  real-analytic. Item (2) therefore demands an analytic R_p, which TARGET neither asserts nor controls. The B1.1
  anchor (∃ R …) becomes stronger than `propansatz`; with TARGET's R_p it is not even plausibly true.
- **R2 (the obligation `summable_kernelK_summand`) is false as stated.** I instantiated it on a garden with three
  lone leaves in one tree. The result derives `False`, sorry-free apart from the obligation's own `sorry`.
- **R3 (`maxBracketPow`) is wrong for θ < 0.** It computes max_i ⟨λ_i⟩^θ, whereas (normX) has (max_i ⟨λ_i⟩)^θ.
  TARGET does use negative θ (𝔛^{−η,0,0}, 𝔛^{−η⁸,0,0} at L1083, L1697, L2360).

**Everything else** is FAITHFUL or a disclosed reading that I accept. This covers:
- the classed a-system solution;
- symmetric events (Q5);
- the one kernel and its five instances, including the time-domain reading and F25;
- `IsCanonGC` and the shared sums (modulo stage-1 R1);
- the tree terms (F9), a^tr and ℒ_j;
- the 𝔖 and Z norms;
- χ₀ (Q6);
- the WKE Taylor terms;
- the rest of `AnsatzAt`.

The second obligation, `truncSum_untruncated`, is true (§1, last row).

## 1. Verdict table

| Decl | Verdict | TeX | Reason |
|---|---|---|---|
| `jbr`, `zpowSign`, `coupling` | FAITHFUL | L617 (z^±), (akeqn2) | ⟨k⟩ = (1+\|k\|²)^{1/2}; z⁺ = z, z⁻ = z̄; δ/(2L^{d−γ}) with rpow. |
| `IsASolution` | FAITHFUL (classed reading C1 / Q16, accepted) | (akeqn)–(akeqn2) L545–L564 | The landed `IsAkSolution` plus `∃ C, ⟨n/L⟩^{d+1}\|a_n(t)\| ≤ C` on [0,T]. This closes Infra-review-1 N1: with weight d+1 > d, the `aNonlin` triple sum is absolutely summable (two free indices, each summable against ⟨·⟩^{−(d+1)}). The weighted ℓ^∞ class is a convolution algebra, so the nonlinearity is locally Lipschitz and uniqueness in the class follows from Grönwall. |
| `IsSymmetricEvent` | FAITHFUL (reading Q5, accepted) | L567–L569 | F = (û_in)⁻¹(A), with A measurable, gauge-invariant (c ↦ e^{iθ}c) and translation-invariant (c_n ↦ e^{−2πi⟨n/L, x₀⟩}c_n, for all x₀ ∈ ℝ^d). These are the Fourier coefficients of u(· − x₀); since x₀ ranges over a group, the sign convention does not matter. See §4. |
| `GBranch.IsChildOf`, `IsParentOf`, `IsFlowerParent`, `IsLoneParent`, `FreeBranch`, `extendTime` | FAITHFUL | (kqflower), (timepairtree) | Flower parents are distinct, one per tree, and get time s, which integrates the δ(t_{𝔣^pr} − s) factors. Lone-leaf parents get the constraint > s. |
| `phaseProd`, `phaseIntegral` | FAITHFUL; no junk | (defkg0) | ∏ e^{πiζ_𝔫 δL^{2γ}Ω_𝔫 t_𝔫} over the product Lebesgue measure on the free nodes. The domain is open and contained in ∏(𝔏, 𝔏+1); the integrand is continuous with modulus 1. So the Bochner integral is a genuine integral, with modulus ≤ 1 (used in R2's fix). |
| `kDomain` | FAITHFUL (reading: t_𝔫 < up(𝔫) for every branching node; accepted) | (timegarden) L674, (timecouple), (timepairtree) | Read literally, (timegarden) leaves "t_𝔫 < t" unenforced at a root whose children are all leaves. This only matters for 𝒦^tr_{p+1} at t ∈ (p, p+1) with a layer-p root; for K_𝒢 at t ≥ p with layers ≤ p−1, the layer bound gives t_𝔫 < 𝔏+1 ≤ t anyway. The reading is the Duhamel time ordering TARGET intends, and (timetree) with a tree of order 1 confirms it. The extra conjunct `0 < τ` is implied by 𝔏 ≥ 0. |
| `inputLeaves` | FAITHFUL | (defkg0) "sign +", (timepairtree)(ii), (kqflower) | + and unmarked, which excludes the lone leaf and the flowers, as required. |
| `kernelK` | FAITHFUL on TARGET's objects (but see R2 and O7) | Def `defkg`, (kqflower) | Prefactor (δ/2L^{d−γ})^n, ζ(𝒢), ε_ℐ, the phase integral, and ∏^{(+)} F_{𝔏_ℓ}(k_ℓ), summed over `GenDecoration` with vectors k₀ + κ/L. The `tsum` is genuine for the four TARGET carriers (plain gardens, couples, paired trees, flower gardens) with summable inputs (R2's corrected obligation). |
| `KG` | FAITHFUL | (defkg0) L671–L674 | up ≡ t, k₀ = 0, root labels n. s and n′ are unused (no marks). Probes: `KG_trivialCouple` = F₀(n/L) (the source value for (•,•) in layer 0), and `KG_trivialCouple_off` = 0 off the diagonal. |
| `KQstar`, `KQ` | FAITHFUL | (timecouple) L678–L680 | up = t on 𝒯⁺ (tree 0) and s on 𝒯⁻; coset k-decorations with real k; K_𝒬 = K*_𝒬(t,t,·). |
| `KTstar` | FAITHFUL | (timepairtree) L681–L684 | up ≡ t, lone parent > s, input product without the lone leaf, coset k-decorations. k_{ℓ_lo} = k is automatic (stage-1 O4). Defined for all (t,s); TARGET's range (t > q, s < q′+1, t > s) is imposed by the consumers. |
| `KGflower` | FAITHFUL (F25 prefactor L^{d−γ}; accepted per F25) | (kqflower) L2266–L2268 | (k,k′)-decorations (all roots n, all flowers n′), flower parents at s, input product over unmarked + leaves. The literal TeX has L^{d−1}. See author question A1 on trivial flower trees (F39). |
| `IsCanonGC` | FAITHFUL | (ansatz3) with G-3 | Probes `isCanonGC_iff_G` (w ≥ 4) and `isCanonGC_iff_C` (w = 2). False for w ∈ {1, 3}. |
| `inputsF` | FAITHFUL | (ansatz3) L703 | F_q = φ(δq) + R_q. |
| `truncSum`, `truncSumC`, `truncSumH` | FAITHFUL modulo stage-1 R1 | (expgarden) L762, (ansatz3)–(ansatz5), (flowerexp2) L2283–L2288, Def `defgtr` | `IsTrunc (q−1) (N_q) (N_{q−1})` is 𝒢^tr_q with (i) top orders ≤ N_q and (ii) attached orders ≤ N_{q−1}. The finite supports are probed (`finite_truncSum*_support`), so the `finsum`s are genuine. `truncSumH` is superseded by the statements' `truncSumHζ` (Q8; O3). |
| `single`, `IsBranchConsistent`, `TreeDecoration`, `treeSign` | FAITHFUL | Def `defdec` (trees) | — |
| `treeTimeDomain` | FAITHFUL (same reading as `kDomain`) | (timetree) L714 | p < t_𝔫 < t for all branching nodes, children earlier. |
| `treeTerm` | FAITHFUL (F9) | (defjt) L710–L714 | Prefactor, ζ(𝒯), ε, phase with the landed `resonance` in the order (k₁,k₂,k₃,k), and the leaf factor a_{k_ℓ}(p)^{ζ_ℓ} (F9). The `tsum` is genuine for summable data, which a(p) in the class provides (O2). |
| `treeTermN`, `aTr` | FAITHFUL | (defjn), (defbk) | The `finsum` over trees of order N is finite (`finite_order_le`). a^tr = Σ_{n ≤ N_{p+1}} 𝒥_n. |
| `Slot`, `slotCountB`, `slotOrder`, `Lop` | FAITHFUL | (eqnbk1.5) L717–L725 | Ordered triples from {b, 𝒥₀,…,𝒥_{Ntr}}³ with exactly j entries b; for j = 0, n₁+n₂+n₃ ≥ N_{p+1}. The integrand is 𝒞₊(u, v̄, w) through the landed `aNonlin … 1`, with the middle conjugate explicit (F9). b is extended by `IccExtend`, and only [p, t] enters. |
| `partialMom`, `iterPartial`, `SNorm`, `SNormR` | FAITHFUL (reading: classical C^{Λ₁}; O5) | (normX2) L585 | max_{\|ρ\| ≤ Λ₁} sup_k ⟨k⟩^{Λ₂}\|∂^ρF\|, with ⊤ unless F ∈ C^{Λ₁}. For C^{Λ₁} functions the coordinate partials commute, so the `foldr` order is irrelevant. |
| `timeFT` | FAITHFUL | L579 | e^{−2πi⟨λ,t⟩}. |
| `maxBracketPow` | **WRONG for θ < 0 (R3)** | (normX) | — |
| `XNorm`, `XNorm00` | FAITHFUL via R3, except the integrability guard (O1) | (normX), L589 | max over ρ outside ∫dλ; L^∞ in k as a sup (continuous under the C^{Λ₁} guard, so it equals the ess sup); any type V for the vector variables of 𝔛^{θ,0,0}. |
| `XNormRestr`, `XNorm00Restr` | FAITHFUL (modulo O1) | (locnorm) L588–L590 | Infimum over all G agreeing on 𝓑 × K, ⊤ if there is none. |
| `ZNormOn`, `ZNorm`, `ZSpace` | FAITHFUL (ZSpace adds continuity in t, Q16, accepted) | (defznorm) L594, L787 | Λ is real, as Z^{(5/4)Λ_{p+1}} needs. |
| `chi0`, `chi0Vec` | FAITHFUL (reading Q6, accepted) | L617–L623 | See §4. Probes: =1 on \|x\| ≤ ½, =0 on \|x\| ≥ 1, values in [0,1], even. |
| `wkeTaylorTerm` | FAITHFUL | (wketaylor2) L753–L755 | 𝒰₀ = φ(pδ); 𝒰_{n+1} = δ Σ_{n₁+n₂+n₃=n} ∫_p^t 𝒦(𝒰_{n₁},𝒰_{n₂},𝒰_{n₃}) dt′, over ordered triples, with the frozen `collisionOp`. Interval-integral junk is closed by B1.5's conjunct (0) (stage 3). |
| `AnsatzAt` | **WRONG in item (2) (R4)**; otherwise FAITHFUL | Prop `propansatz` L690–L708 | See the item checks below. |
| `summable_kernelK_summand` (obligation) | **FALSE as stated (R2)** | — | — |
| `truncSum_untruncated` (obligation) | TRUE (proof sketch) | (ansatz3) L704 ("order at most N_p … all nodes in layer at most p−1") | (i) The top orders are ≤ the order N ≤ N_q. (ii) The attachment nodes are pairwise incomparable (a node strictly below another has parent layer < p), so every class order is ≤ Σ_{𝒰} orderBelow ≤ N ≤ N_q ≤ N_{q−1}. Here N_{q−1} = N_q^{(40d)²} ≥ N_q in ℕ, and the clamped R gives N_{q−1} = N_q for q > 𝔇. This holds with or without R1. |

**`AnsatzAt` items checked against (ansatz1)–(ansatz5):**
- **(1)** Agrees with TARGET:
  - `Fev p` is measurable and symmetric;
  - Fev p ⊆ Fev (p−1) for p ≥ 1 (TARGET's F_p ⊃ F_{p+1}, read under ∀ p);
  - μ(Fev p) ≥ 1 − e^{−N_p};
  - on Fev p a classed solution with data û_in exists on [0,p] and is unique in the class.

  The two additions are both provable and close junk hazards:
  - global measurability of ω ↦ a_n(t) (C1);
  - integrability of all finite products on Fev p (mass conservation bounds |a_n(t)|² by Σ φin(m/L)|g_m|², which
    has all moments).

  "𝔼, 𝕂 taken assuming F_p" is μ.restrict, i.e. E[1_F ·] (L576), as in the landed `cumulant`.
- **(2)** The (ansatz1)/(ansatz2) content is right:
  - 𝔼_p(a_n ā_{n′}) = 1_{n=n′}(φ(δp, n/L) + R_p(n/L) + E_p(n));
  - ‖R_p‖_𝔖 ≤ L^{−θ_p};
  - |E_p| ≤ ⟨n/L⟩^{−Λ_p}e^{−N_p};
  - R and E real.

  Only the extra conjunct `ContDiff ℝ ⊤ (R p)` is wrong (R4).
- **(2′)** Not in TARGET's statement: it is the WAVE-B time-parameter addition (F7/F27). Consistent; not re-derived
  here (A3).
- **(3)** 𝕂_p(a^{ζ_j}_{n_j}(p)) = Σ_{N ≤ N_p} truncSum p N p + Ẽ_p for 2 ≤ m ≤ R_p and Σζ = 0. Ẽ_p = 0 off
  Σζ_j n_j = 0, with the (ansatz4) bound. This is TARGET's 𝒢_p sum through `truncSum_untruncated`. Stage-1 R1 does
  not affect it, since all orders are ≤ N_p.
- **(4)** The (ansatz5) bound for N ≤ N_p.

## 2. REQUIRED fixes

### R4. `AnsatzAt` (2) asks `R p` to be analytic

**The defect.** `ContDiff ℝ ⊤ (R p)` elaborates with `⊤ : WithTop ℕ∞`, which is `ω`.
- Probe `contDiff_top_is_omega` (`Iff.rfl`) shows the two are definitionally the same.
- `ansatz_R_analytic` derives `AnalyticOnNhd ℝ (R p) univ` from the conjunct.
- `infty_ne_omega` confirms that ∞ and ω differ.

**Why it matters.**
- TARGET gives R_p only through (ansatz1)–(ansatz2): a real function with finite 𝔖^{Λ_p,Λ_p} norm. Its R_{p+1} is
  built from couple sums of the inputs φ(δq) + R_q, and φ(0) = φin is merely Schwartz (for instance compactly
  supported).
- Such R_p are not analytic in general. So B1.1 (∃ R with `AnsatzAt`) is strictly stronger than `propansatz` and
  cannot be discharged by TARGET's construction.
- Wave A's convention for "smooth" is `(⊤ : ℕ∞)`, i.e. ∞ (WaveA-main-draft §1, `IsSmoothNLSSolution`).

**Exact Lean change** (`WaveB1-System.lean`, `AnsatzAt`, item (2)). Preferred: drop the conjunct, because
`SNormR (Λ_p) (Λ_p) (R p) ≤ ofReal (L^{−θ_p}) < ⊤` already forces R_p ∈ C^{Λ_p}, which is all TARGET controls:

```lean
  -- (2) two-point function at time p
  (SNormR (P.Lambda p) (P.Lambda p) (R p) ≤ ENNReal.ofReal (P.L ^ (-P.theta p)) ∧
    (∀ n, |E p n| ≤ …) ∧ …)
```

Alternative, only if a consumer needs C^∞ and the author accepts the extra proof burden (TARGET tracks only
Λ_p derivatives): `ContDiff ℝ ∞ (R p)` with `open scoped ContDiff`, or equivalently `ContDiff ℝ (⊤ : ℕ∞) (R p)`.

**Cross-stage note for the stage-3 auditor.** The same `ContDiff ℝ ⊤` occurs at `WaveB1-Statements.lean`:
- L75: the hypothesis of `RemainderBound`. It must match whatever B1.1 provides.
- L103: the *conclusion* that `coupleRemainder P R p N t` is analytic. A defined function with Schwartz inputs is
  not analytic in general, so that conjunct is likely false.

### R2. The obligation `summable_kernelK_summand` is false

**The defect.** The obligation quantifies over **all** layered gardens. Its argument ("a decoration is determined by
its input-leaf values") fails when one tree carries two or more `lower`-marked (lone) leaves. Their values are then
free, subject only to the root constraint, yet they carry no input factor.

**Counterexample** (`scratch/WaveB-stage2-summable.lean`, sorry-free).
- **The garden.** `lone3`: one tree of order 1 (sign +) with all three leaves marked `lower`, every layer 0.
- **The parameters.** d = 1, L = 1, γ = 0, δ = 0, F ≡ 0, up ≡ 2, s = 0, k₀ = 0, root label 0. The obligation's
  hypothesis `hF` then holds (`summable_kernelK_summand_hyp`).
- **The phase integral.** With δ = 0 it equals 1 for every decoration (`lone3_phaseIntegral`, computed as
  vol((0,1)) = 1).
- **The input product.** It is empty, hence 1 (`lone3_inputLeaves`).
- **An infinite family.** The decorations κ_m with children (m+1, 2(m+1), m+1) have ε = 1 (`lone3Dec_eps`) and are
  pairwise distinct (`lone3Dec_injective`).
- **Conclusion.** The summand has norm 1 infinitely often: `summable_kernelK_summand_false`.
- **The draft lemma derives False.** `draft_obligation_inconsistent : False` applies the draft lemma to these data.
  Its axioms are `[propext, sorryAx, Classical.choice, Quot.sound]`; the only `sorry` is the obligation itself.

**Exact Lean change.** Add the hypothesis "at most one lone leaf per tree", which every TARGET carrier satisfies
(plain gardens and couples 0, paired trees 1, flower gardens 0):

```lean
theorem summable_kernelK_summand {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ))
    (nfl : Fin d → ℤ)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hF : ∀ q, Summable fun n : Fin d → ℤ => |F q (k₀ + latticePoint L n)|) :
    Summable fun κ : GenDecoration LG.garden d nroot nfl => ‖…‖ := by
  sorry
```

This exact statement elaborates (`summable_kernelK_summand'` in `scratch/WaveB-stage2-norms.lean`).

**Why the corrected statement is true.**
- Leaf values are determined as follows:
  - each pair has exactly one + leaf, which is an input leaf;
  - flowers are fixed at n′;
  - a tree's single lone leaf is determined by the tree's root value, since
    k_𝔯 = Σ_ℓ ±k_ℓ and the lone leaf enters that sum with a unit coefficient.
- So κ ↦ (κ_ℓ)_{ℓ ∈ inputLeaves} is injective.
- Each summand has norm at most ∏_{ℓ ∈ inputLeaves} |F(k_ℓ)|, because |ε| ≤ 1 and |phaseIntegral| ≤ 1.
- The sum of these bounds is at most ∏_{ℓ ∈ inputLeaves} Σ_n |F_{𝔏_ℓ}(k₀ + n/L)| < ∞.

Also update `kernelK`'s docstring, which currently claims convergence for every garden.

### R3. `maxBracketPow` is wrong for θ < 0

**The defect.** `maxBracketPow θ λ = ⨆ i, ofReal(⟨λ_i⟩^θ)` is max_i ⟨λ_i⟩^θ. (normX) has (max_i ⟨λ_i⟩)^θ.
- For θ ≥ 0 the two agree.
- For θ < 0 the draft takes the *minimum* bracket, so its weight, and its norm, is too large.
- TARGET uses θ < 0 with several time variables: (incohproof26) L1083 𝔛^{−η,0,0}, L1697 𝔛^{−η⁸,0,0}, (estichi) L2360
  𝔛^{−η,0,0}.

**Probes** (`scratch/WaveB-stage2-norms.lean`, sorry-free): at λ = (0,3), θ = −1:
- the draft weight is ≥ 1 (`maxBracketPow_neg_ge_one`);
- TARGET's weight 10^{−1/2} is < 1 (`target_weight_lt_one`).

**Exact Lean change.** The `⊔ 1` makes r = 0 give weight 1 instead of the junk 0. ⟨λ⟩ ≥ 1, so for r ≥ 1 this is
exactly (max_i ⟨λ_i⟩)^θ. The definition elaborates (`maxBracketPow'` in the probe file).

```lean
/-- `(max_i ⟨λ_i⟩)^θ` (T (normX)); `1` for `r = 0`. -/
noncomputable def maxBracketPow {r : ℕ} (θ : ℝ) (lam : Fin r → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (((⨆ i, Real.sqrt (1 + lam i ^ 2)) ⊔ 1) ^ θ)
```

No B1 statement is affected: the only consumer, B1.6 `sumint`, uses θ = 2η⁸ > 0. The fix is still REQUIRED, because
the frozen definition must mean (normX) on its whole carrier θ ∈ ℝ, and the provers' internal lemmas need θ < 0.

## 3. OPTIONAL suggestions

- **O1. The integrability guard of `XNorm` and `XNorm00`.**
  - **What it does.** It returns ⊤ unless every t ↦ F(t,·) is integrable. TARGET's norm is finite whenever F̂ is a
    weighted-integrable function, e.g. F(t) = sinc(t) with F̂ = 1_{[−½,½]}.
  - **Why it is harmless for B1.** The restricted norms over a bounded 𝓑, the only B1 use (B1.6, 𝓑 ⊆ ∏[q,q+1]), agree
    with TARGET's up to an absolute factor. Replace G by χG, with χ ∈ C_c^∞ equal to 1 on 𝓑; then
    ‖χG‖ ≤ (∫⟨ν⟩^{|θ|}|χ̂(ν)| dν)·‖G‖ by Peetre's inequality. That factor is absorbed by the existential C₁ of
    `WTPrefixA`.
  - **A side benefit.** The guard makes λ ↦ ⨆_v |F̂(λ,v)| lower semicontinuous, hence measurable, so the `lintegral`
    has no inner-integral junk.
  - **Recommendation.** Disclose this reading in the docstrings. If any later statement uses an *unrestricted* 𝔛 norm
    or a fixed explicit constant, switch to the Fourier-representative form (inf over integrable H with
    F(t,k) = ∫ H(λ,k) e^{2πi⟨λ,t⟩} dλ).
- **O2. A summability obligation for `treeTerm`.** The `tsum` over `TreeDecoration` is genuine for summable b; for
  non-summable b TARGET's 𝒥_𝒯 is undefined, so the junk value is harmless. A statement in the style of R2 records
  this for the provers of B1.3:

  ```lean
  theorem summable_treeTerm_summand (hb : Summable fun n => ‖b n‖) : Summable fun κ : TreeDecoration T d n => ‖…‖
  ```
- **O3. Remove `truncSumH`, or define it as a specialization of `truncSumHζ`.** Two flower sums in the frozen surface
  invite drift (Q8).
- **O4. Add one non-trivial kernel probe.**
  - Show that `kDomain figLG (fun _ => 3) 0` is nonempty. This checks the time domain of a genuine canonical garden.
    It is nonempty because same-layer children can be ordered inside (𝔏, 𝔏+1), and a lower-layer child is
    automatically earlier.
  - Or compute `KG` for `miniCouple00` at δ = 0: the phase integral is the volume of the domain.
  - At present only the trivial couple, with no branching nodes, exercises `kernelK`.
- **O5. Disclose the classical-derivative reading of `SNorm`.** ⊤ unless F ∈ C^{Λ₁}. A function with bounded but
  discontinuous top partials has a finite source norm but ⊤ here. All consumers supply smooth or C^{Λ₁} functions.
- **O6. 𝔖 on ℤ_L^d.** (locnorm)'s "the same applies to 𝔖 (so it can be defined for functions on ℤ_L^d)" has no
  counterpart in the draft. No B1 statement needs it; add `SNormRestr` only if a consumer appears.
- **O7. Junk on gardens with several lone leaves in one tree.** On these non-TARGET gardens `kernelK` returns the
  `tsum` junk value 0 (R2's counterexample). This is harmless, but say it in the docstring.

## 4. DESIGN questions (definitional; my answers)

- **Q5 (symmetric events as initial-data preimages): ACCEPT.**
  - L568: "any event F can be interpreted as a subset of initial data u_in … symmetry if the corresponding subset is
    … invariant". The draft is the literal reading.
  - The g-preimage reading (WAVE-B v2 §2.3.4) admits events that depend on g_n where φin(n/L) = 0. That would make the
    existential event of B1.1 easier to supply than TARGET's.
  - With the initial-data reading, B1.1's existential is exactly as strong as the source. All F_p in TARGET are
    defined through the solution, which depends only on û_in, so it costs the proof nothing.
- **Q6 (χ₀ Gevrey bound): ACCEPT the reading "Gevrey 2 with a constant", |χ₀^{(m)}| ≤ C^{m+1}(2m)!.**
  - **The literal bound fails at m = 1.** χ₀ drops by 1 on [½,1], so sup|χ₀′| ≥ 2. Equality would force χ₀′ ≡ −2 on
    [½,1], contradicting χ₀′(½) = 0 (χ₀ is smooth and ≡ 1 on [−½,½]). So sup|χ₀′| > 2 = (2·1)!.
  - **The chosen formula meets the reading.** χ₀ = smoothTransition(2 − 2|x|) is Gevrey 2:
    - e^{−1/x} is Gevrey 2;
    - smoothTransition = f(x)/(f(x)+f(1−x)) has a denominator ≥ c > 0 on [0,1], and Gevrey classes are closed under
      such division;
    - the kink of |x| at 0 lies where χ₀ ≡ 1.
  - **Equivalent forms.** C^{m+1}(2m)! and C^{m+1}(m!)² are equivalent, since (m!)² ≤ (2m)! ≤ 4^m(m!)².
  - The candidate erratum (T L622) should go to FINDINGS, as DESIGN proposes. Any statement of the bound (packet N1)
    must carry the constant.
- **Other stage-2 readings in DESIGN §5, all accepted:**
  - the time-domain reading;
  - the F25 prefactor;
  - the F9 leaf and middle-slot conjugates;
  - the classed solution (Q16);
  - `IccExtend` in ℒ_j;
  - the ⊤ conventions (modulo R3 and O1);
  - backward nesting of the F_p.

## 5. Author questions

- **A1 (F39 and trivial flower trees).** `IsCanonH` admits flower gardens with trivial flower trees (flower = root),
  faithfully to Def `defflower`.
  - On such a tree, `KGflower` contributes 1_{n = n′}, with no δ(t_{𝔣^pr} − s) factor; TARGET's (kqflower) is
    undefined there, since the flower has no parent.
  - The 𝒳 moment expansion (flowerexp2) only produces trees of order ≥ 1 (F39: 𝒳's kernel has no identity term).
  - The statements' `truncSumHζ` kind 0 imposes no such restriction. For the stage-3 auditor and the author: should
    kind 0 require every root to be branching (`1 ≤ topOrder p j` for all j)? Or should the parametrix fix of F39
    (1 + 𝒳) be reflected some other way?
- **A2 (the class weight).** Q16 fixes the weight ⟨n/L⟩^{d+1}. Any weight > d gives absolute convergence and
  uniqueness. Confirm that d+1 is the frozen choice, so that B1.4 (`nlsAkBridge`) and B1.1 use the same class.
- **A3 ((2′), F7/F27).** This item is not in TARGET's Prop `propansatz`. Please confirm the constant 2L^{−θ_p} and the
  use of F_p (not F_{p−1}) for t ∈ [p−1, p] against the F27 derivation. I did not re-derive it.

## 6. Non-vacuity probes

**Snapshot probes** (`WaveB1-System-probes.lean`, sorry-free):
- `KG_trivialCouple` (K = F₀(n/L)) and `KG_trivialCouple_off` (= 0);
- the finite supports of the three shared sums;
- `IsCanonGC` against `IsCanonG` and `IsCanonC`;
- five χ₀ properties.

**My probes** (untracked, they import `WaveBDraft.SystemProbes`, standard axioms unless noted):
- `scratch/WaveB-stage2-summable.lean` (160 lines, sha256 `4ff2eaf9…922ad3b`): R2.
  - `lone3_phaseIntegral`, `lone3Dec_eps`, `lone3Dec_injective`, `summable_kernelK_summand_false`,
    `summable_kernelK_summand_hyp`.
  - `draft_obligation_inconsistent : False`, through the draft's sorry'd lemma.
- `scratch/WaveB-stage2-norms.lean` (71 lines, sha256 `b2ea639e…0eae42`):
  - R3: `maxBracketPow_neg_ge_one`, `target_weight_lt_one`, and the proposed `maxBracketPow'`;
  - R4: `contDiff_top_is_omega`, `ansatz_R_analytic`, `infty_ne_omega`;
  - the corrected obligation `summable_kernelK_summand'`, statement only (`sorry`).
