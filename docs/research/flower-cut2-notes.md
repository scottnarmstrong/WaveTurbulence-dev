# CX-CUT2 — product stem cutoffs

2026-11-06. Research route, not a completed Lean proof.

## 0. Verdict and scope

**PROVABLE-VIA a weighted, multiple-stub version of design C, followed by mixed BV integration in one marked clock per original tree.** Keep the proposed v3 statement. There is no reason to weaken its exponent for this route. This is substantially more work than adding a `cut2` argument to the present Stage-1 gate.

The important new observation is that localized resonance cutoffs have a **uniform spatial Fourier-measure norm**, even when the root momentum is arbitrarily large. Use spatial modulation uniformity in the regular-object and sumint proofs, not R58's temporal modulation tolerance. The latter is the wrong Fourier operation for this purpose.

For the high-frequency gain, mark exactly one non-flower-parent stem node in each original tree. Excision makes its time an *outer integration variable*, not a permanently fixed time. Integration by parts in these outer variables produces ordinary cap/floor faces. Excision of the additional pinned neighbors makes every face another multiple-stub garden. There are O(Pm) pins, not O(N). The frequency gain can be stronger than the requested one; the expense is a larger, but still fixed, polynomial in L per original tree.

This verdict is a proof architecture with source-level arguments for its analytic extensions. The multiple-stub construction, its image/carrier theorem, its weighted decay/summation adapter, and the BV identity are implementation obligations. They are not theorems currently available in Lean. In particular this report does **not** certify the flower provider, the main theorem, or completion of FC3/design C. Those already-required packages remain dependencies. The elementary Lean probe below certifies only the free-clock classification and numerical implications.

The brief's alternative `STOP` would not be justified: no counterexample was found, and the apparent upper-cutoff obstruction has a concrete repair. A claim that a missing current API proves impossibility would be incorrect.

## 1. Inputs, permission, and review

Only this directory was written. No source, frozen declaration, repository configuration, or dependency artifact was edited. The user already specified the permission envelope: research notes/probes here; read-only main; narrow transient Lean allowed. No commit, push, or external message was made.

The immutable manifest is `probe/manifest.json`; file contents are stored by SHA256 in `probe/frozen-v1/`. The main revision at pinning is recorded there. Pinning followed initial reconnaissance, before the findings below were consolidated; the manifest includes the whole XChain and frozen-definition surface to avoid uncertainty about transitive definitions. It is broader than the portions actually audited.

Principal sources (all citations below refer to these frozen contents):

* T = `/home/scott/wave-turbulence/paper/source/WKE-Longer_times_Final_arXiv.tex`: flowerest1 L2279–2305; fixedpoint Part 2 L2318–2333; regular estimates L950–1095; sumint L1596–1720; vine cancellation L1840–1924; reduction L1944–1976.
* DH21 = `/home/scott/wave-turbulence/references/src-2104.11204/Inventiones-Final_Version.tex`: `maincoef` L935–943, time-denominator lemma L2431–2444, Corollary `extragaincor` L2699–2705, dyadic construction L2731/L2735.
* DH23 = `/home/scott/wave-turbulence/references/src-2301.07063/Revision_Submit.tex`: L961–969/L1163–1168 and flower/endgame L1992–2024.
* Required predecessor NOTES, FlowerCut.lean, design-C NOTES/referee REPORT, and R47/R58/R61/R62 were read. R61's referee corrections are part of the design assumed here, including root excision for Y/W and splitting adjacent fixed nodes.
* Main: `LayeredGardenFixPat`, `KDomainFix`, `LayeredGardenCutWeight2`, `FlowerSum`, `KernelKgen`; `LayergardenFlowerV2`; X2Kernel, FlowerTop, X2Est, V2Chain/FixedpointS and the X3 Part-2 chain.
* LG-spine `Stage1Interface`, `Stage1Gate`, `SourceSplicedKernel`, `TypeFamily`.

Method: focused tier-2 research audit, refute first, with independent adversarial review in `probe/independent-review.md`. The reviewer used the repository's designated GPT-6.1-Sol/low configuration (D5); this supersedes the audit skill's unavailable older model. The reviewer first rejected a premature positive conclusion, then checked the spatial-Fourier repair, pointwise vine cancellation, and weighted regular estimates. Its chronological report deliberately retains the earlier objections and their later resolutions. The numerical local-cost budget below is my conservative working ledger, not an independently formalized bound.

## 2. Exact splitting and which clock is free — question (a)

Write P = Pm, w = 2P, M = 2^j L, a = δ L^{2γ}. Order the eligible stem nodes in a tree from root to flower, omitting f^pr. Put

    A_b = χ₀(|Ω_b|/M),   B_b = χ₀(2|Ω_b|/M).

For j≥1 the exact identity is

    ∏ A_b − ∏ B_b
      = Σ_b (A_b−B_b) (∏_{c<b} B_c) (∏_{c>b} A_c).                  (2.1)

Thus select a marked b in each of the 2P trees. This is an equality of signed/complex kernels; no monotonicity of an oscillatory sum is invoked. On each resulting support,

    M/4 < |Ω_b| < M,

and every remaining eligible stem resonance is <M. The factors left at other nodes are smooth *upper* cutoffs, at scale M or M/2. An empty eligible stem gives zero for j≥1, so there is no need to choose a mark there. There are at most N^{2P} choices of marks; N≤N_{p+1}^4 is polylogarithmic in L with parameters fixed, so this is an L^εP cost for sufficiently large L.

For the plain pattern the definition is literally

    fixPat plain t s b = if IsFlowerParent b then some s else none.

Consequently every selected b has a free original clock. `plain_mark_free` in the probe proves this directly from the frozen definition. The original design-C stub f^pr is excluded by construction. For Y/W, a selected root may be moved into the *outer* root-time integral by the carrier repair; that clock remains integrated. One must not mistake an intermediate external parameter for a permanently pinned s-clock.

For nonplain patterns v3 requests **no M₂ gain**. In particular it would be wrong to apply the preceding free-clock argument to a selected dRoot/dParent node. Such patterns still require the upper-weight bound in §3.

Do not run Stage 1 to its existing scalar output and then try to recover the selected resonance: regular contraction and vine splicing have discarded that information. Also do not replace a time integral by its absolute oscillatory denominator and then call an unmodified garden theorem on the remaining integrand. The domains and phases at its faces have changed.

The valid order is:

1. exact marked splitting (2.1), including cut1 and dagger weights;
2. garden-level excision at f^pr and at the marked nodes, retaining marked times as outer variables and retaining the marked local labels;
3. a uniform weighted multiple-stub bound for the interior kernels **and their cap/floor faces**;
4. integration by parts/BV in the outer marked clocks; then sum the special labels and centers using the decay adapter.

Equivalently, one may form the face identities before the reductions and then estimate each face by Stage 1/2. Fubini at finite truncations is an identity; passing to infinite decoration sums requires the summable bounds. This is not an assertion that integration by parts commutes with the unchanged Stage-1 API.

## 3. The other stem cutoffs — question (b)

### 3.1 A local Fourier-algebra lemma

Let x consist of the O(d) incident momentum coordinates at one node, localized to a fixed unit box. For a smooth compactly supported cutoff φ on that box, a fixed smooth Schwartz χ, and a quadratic Q with bounded coefficients, define

    H(x) = φ(x) χ((b + v·x + Q(x))/M),     M≥1.

Then

    || Fourier(H) ||₁ ≤ C(d,φ,χ,Q),                                   (3.1)

uniformly in **both** b and v. In particular the constant does not depend on |k|/M or the centers of the localized momenta.

Proof: expand χ in its scalar Fourier variable u. The integrand is

    χ̂(u) exp(iub/M) exp(iu v·x/M) φ(x) exp(iuQ(x)/M).

The second spatial exponential translates Fourier frequency and preserves its L¹ norm. A compact-support Sobolev estimate, with a fixed number of derivatives exceeding half the dimension, bounds the remaining Fourier norm by C(1+|u|/M)^s. Integrate this against |χ̂(u)|. Schwartz decay and M≥1 give (3.1). Choice of π versus 2π only rescales u and C.

For a resonance, expand its quadratic polynomial about the incident momentum centers. Its Hessian is bounded independently of those centers; the arbitrarily large part is exactly the harmless linear v. χ₀(|Ω|/M)=χ₀(Ω/M) because χ₀ is even. Products of O(N) local factors cost C^{O(N)} by the Fourier-algebra inequality. Under an affine conservation map, use the pushforward of the finite Fourier measure: total variation cannot increase. This avoids a Jacobian claim for a rank-deficient map, and avoids losses from large coefficients in a leaf-to-node map.

This defeats the derivative-based objection |∂_k χ(Ω/M)|≈|k|/M. That derivative can indeed be large; it does not imply a large Fourier L¹ norm.

### 3.2 Regular objects: preserve the incoherency gain

This point can be checked directly in T, without importing an unproved uniform time-shift theorem.

In T's proof of `proplayer1`, L987–1035 (`incohproof2` through `incohproof12`), paired branch variables satisfy

    Ω_n = 2 x_n·y_n,   ζ_n' Ω_n' = −ζ_n Ω_n.

The external root k appears only in the profile product W. T L995 explicitly places external k derivatives on W. After localization, T L1017 requires the remaining estimate **uniformly in all choices of spatial (ξ_n,ξ'_n)**. Each upper cutoff contributes at most two factors on the same paired (x_n,y_n). Apply (3.1) there; it only adds spatial modulations ξ_n,ξ'_n. The estimates `incohproof13`–`incohproof15`, including the unequal-layer time rectangles producing g, remain the same. Thus the full L^{−(γ₁−√η)g} gain survives, at C per linked pair. The g=0 norm bound uses the same inequalities without an incoherency gain. The regular-tree case has the usual missing external-root decay, as in the source's final tree step.

We do not need to claim that arbitrary cutoff-modified coherent approximants obey the original kinetic identities. Under the high-root assumption, a stem regular tree is not one of the coherent T_(u2), Q_(u23,u0) replacements used in an SG twist: the flower travels through the preserved child u11. Those replaced objects are off stem and have no cut2 factors. The weighted stem regular factors only need their norm bound.

An alternative coefficient route is to multiply the DH21/DH23 generalized α coefficient by χ(α/(aM)). For aM≥1, its Gevrey derivative class is stable. T L623 assumes Gevrey-2 cutoffs. This alternative is unnecessary for the weighted incoherency argument just given; it should not replace the explicit spatial-modulation proof.

### 3.3 Vines and Stage 2

An SG vine may have its *top* on the stem even though its interior coherent replacements are off stem. Its top Ω can depend on an internally summed momentum. Therefore it is incorrect simply to call this cutoff an external scalar.

T's `replaceterm1` and subsequent cancellation, L1883–1924, are identities before the internal momentum sum is estimated. The leading coherent terms cancel pointwise after the (Q,T) sum, and the remaining terms have the stated small gap/time-difference/remainder factors. A common twist-invariant cutoff stays outside that cancellation. In the mean-value comparison of the unweighted approximants at x_* and y_*, do **not** differentiate the common cutoff. Then insert it through (3.1) into sumint. T L1625 explicitly proves uniformity in spatial modulation parameters. For a vine bound with an outer momentum supremum inside a time-Fourier norm, localize and Fourier-expand in the **external as well as internal** momentum variables. The resulting measure is independent of the exterior momentum argument, and exterior spatial modulations have modulus one. This makes Minkowski legitimate in the actual norm order. A family of separate Fourier measures depending on the exterior argument, with only uniformly bounded variation, would not by itself justify interchanging that supremum and the time-frequency integral.

After splicing, weights internal to a collapsed vine are part of its bounded hinge amplitude; weights on surviving atoms are handled by the same local Fourier-measure insertion. The coarse ladder proof again uses uniform spatial modulations. The absolute counting branch retains weights bounded by 1. Fourier expansion is used on the analytic branch; the original bounded weight is used on the counting branch. Both estimates concern the same weighted expression. Inserting arbitrary oscillatory leaf profiles *before* coherent cancellation would be a different, unjustified procedure.

R47 still controls the actual pair-type leaf families and cut1's polynomial extraction. It does not on its own authorize a decoration-dependent Ω weight. R58 supplies temporal modulations e^{πiλt}; Fourier expansion of χ(Ω/M) instead shifts the Ω clock. These operations must not be conflated. The spatial argument above is the needed additional interface.

## 4. Marked excision, faces, and the multiple-stub adapter — questions (a),(c)

### 4.1 Exact identities

For a selected branch b, fix the local momenta at b and its three children. Cut off its child subtrees, replacing the children by anchored leaves, and keep b as a pendant stub at clock τ_b. Keep all original coupling and epsilon factors; the phase of b is now an outer factor

    exp(iπ ζ_b a Ω_b τ_b).

The children become separate capped trees. Its free parent retains the floor τ_parent>τ_b. Cut edges between two designated nodes as in referee fix X2. The same construction is made at the original flower parent and at any additional node pinned by a face. It is reversible by gluing the recorded slots. Canonicity is tested with the anchored pairs: a proper subtree containing a stub cannot be a collapsed regular couple, and its anchors prevent an unnoticed regular-object contraction through the cut. The stub can occur as the lone-leaf position of a regular tree, with its clock retained as an endpoint.

For fixed outer labels, after removing the selected phases let the remaining coefficient be A(τ_1,…,τ_r), r=2P. Its τ dependence is entirely in time domains (caps and floors). No remaining phase is differentiated in forming a domain derivative. An ordinary derivative in τ_i consists of at most four faces: its free parent and its at most three branching children. A neighbor in a lower layer contributes no interior face at a layer-p τ_i. An already fixed neighbor contributes a support endpoint, not another free-coordinate integral.

Every such face pins one additional branch at τ_i. Apply the same excision to that branch. Adjacent fixed-fixed edges are removed and the face's one-sided trace is retained. This is a face integral of the original measure, not the zero measure of an equality set inside the old full-dimensional integral.

There is one selected mark per **original tree**. Hence mixed first derivatives in distinct τ_i do not identify free clocks from different marked trees; leaf pairing imposes momentum equalities, not time equalities. At most r additional branches are pinned in a mixed face term. No repeated differentiation up the stem is needed.

### 4.2 What has to be generalized from design C

The needed statement is an anchored-garden estimate uniform in a vector of designated times, with:

* O(P) pendant stubs and arbitrary per-tree caps;
* bounded cut2 upper factors as treated in §3;
* the cut1 family/bond weights from FC3 and the existing dagger restrictions;
* sums over the O(P) special momentum labels with the decay described below;
* all lower-dimensional cap/floor traces obtained by pinning at most one neighbor of each marked node.

It must bound these kernels before the high-frequency integration, so it contains **no M₂ decay hypothesis or conclusion**. Using it is therefore not a disguised assumption of cut2.

Its reduction follows the same construction as design C, now with vector stub times. A pendant stub lies in no block or ladder. Its phase is a bounded outer coefficient. The parent floor is imposed by subtracting the capped term, schematically

    B_floor(τ) = B − B_parent≤τ.

Products of these identities produce at most 2^{#stubs} terms, with arbitrary caps. Fixed external-time traces of a Fourier-L¹ representation are bounded by integrating the same Fourier absolute value; several traces do not multiply the Fourier mass. In particular the V5 lower-child clock must be the correct R58 clock before taking the trace. The coarse/ladder estimates must be stated with these caps and pendant stubs; a plain-garden theorem with all times integrated is not a substitute.

For the carrier, record the original-tree indices, cut slots, stem order, and topOrders. Reconstruct the flower by gluing. Use the SG stem-preserving correspondence, and the unaltered subtrees at recorded anchor slots, to transport this data. This is the multiple-mark version of design C's carrier proof. Do not estimate individual fixed garden shapes absolutely; class sums are still required. Twists involving an excised atom no longer occur in the anchored components. The loss from those atoms is paid per cut, not per remaining order.

### 4.3 Summing the fixed labels without an L^{cN} loss

The phrase “fix Ω at L^{10d} cost” is only valid *after* localization; it is false as a global cardinality claim. At a node with its incident momenta in fixed unit balls, at most (CL)^{3d} choices of its three child labels determine its resonance, independent of the centers. At O(P) nodes this is L^{O(d)P}. O(N)-sized boxes instead give an additional (N+1)^{O(d)P}, also affordable.

One must not fix a separate global leaf-center assignment before the coherent family cancellation. Use family-compatible localization, or perform the cancellation first and localize its common expression. For cut labels that remain outside a component estimate, use the following flux version of the leaf-decay adapter.

For a cut subtree with root label κ, subtract the signed flower label if it contains the flower. The resulting flux is a signed sum of its genuine nonflower input leaves. Momentum conservation reconstructs all dependent cut labels from a choice of independent fluxes and the fixed k,k'. Each original tree has only O(1) cuts (flower parent, mark, one face neighbor, and possible root). Consequently each genuine leaf appears in only O(1) of these flux forms, independent of P and N. Allocate an even polynomial decay power >d to each independent flux and sum its lattice label:

    Σ_{z∈Z^d} <z/L−c>^{−(2d+2)} ≤ C_d L^d     (L≥1),

uniformly in c. The affine momentum constraints only reduce the number of free sums. The extra polynomial weights are extracted by the same exact polynomial/family mechanism as R47 and FC2, not by a pointwise inequality inside a complex sum. At most a fixed number of extra weights per original tree are needed; the corresponding degree/mark counts are (N+1)^{O(d)P} times C^N.

There is room in the leaf regularity/decay budget. For p<D, Λ_p=40dΛ_{p+1} and Λ_{p+1}≥40d. Even a reserve of 200d in addition to 8Λ_{p+1} is smaller than Λ_p for d≥3. This covers the original 40d-per-tree M₁ extraction, finitely many cut-flux weights, and their fixed derivative orders. Dagger restrictions only fix some of these labels and do not increase their number. This summation argument is a necessary lemma of the adapter; it must not be replaced by counting every original leaf at L^d cost.

### 4.4 Mixed integration by parts, with every boundary included

Integrate each selected clock on the fixed interval [s,t], extending A by zero where the original domain is empty. This packages the max-of-children lower endpoint without differentiating a chosen maximum. Let ||A||_{BV_mix} denote the sum, over subsets I of the r coordinates, of the total variations of the mixed first derivative in I and the endpoint traces in the remaining coordinates. For smooth coefficients this is precisely the sum of the usual iterated integration-by-parts face integrals; the BV version follows by approximation or directly from the time-domain faces.

For nonzero ω_i=πζ_i aΩ_i,

    |∫_[s,t]^r exp(iΣ_i ω_iτ_i) A(τ) dτ|
      ≤ (∏_i |ω_i|^{-1}) ||A||_{BV_mix}.                            (4.1)

The scalar identity is

    ∫_s^t e^{iωτ} A(τ)dτ
      = [e^{iωτ}A(τ)/(iω)]_s^t − (1/(iω))∫_s^t e^{iωτ} dA(τ).

Both endpoint terms are present. A fixed flower-parent clock supplies an endpoint at s when adjacent. All choices of interior face or endpoint give at most 6^r terms, and each has at most one extra pin per original marked tree. This is why a mixed BV norm, not only a bound on the full mixed derivative, is the right formulation.

The face estimates of §4.2/4.3 yield the same garden order decay with a polynomial per-pin loss. On annular support (4.1) supplies

    (4/(πaM))^{2P}.                                                (4.2)

This strong decay is allowed because the marks lie in distinct original trees. It would be false to claim a full inverse power for arbitrarily many marks on a single chain: opposite neighboring resonances can leave only one large denominator. We do not use such a claim.

If a formal implementation chooses the DH21 denominator route instead, it must retain enough marked frequency data. DH21's recurrence q_v=α_v+Σ_child d_c q_c implies a large α_v forces one of at most four nearby q's large, and each q can witness at most two marked vertices. That gives at least r/2 large denominators on the unreduced forest. After contractions the congestion must be proved anew. This route is plausible, but the excision/BV route avoids that additional combinatorial audit.

## 5. Exponent ledger and small j₂

The following is a deliberately generous implementation budget. It is not a claim that every listed source estimate already has a Lean wrapper with these constants.

Let r=2P. In a face term there are at most four designated branch roles per original tree: original flower parent, selected mark, its face neighbor, and possible excised root. Coincidences decrease this count. Thus at most 8P designated branches suffice. Splitting a fixed-fixed edge does not create a new branch. At most 3 anchored child slots per designated branch and at most a constant number of resulting capped components occur. The width remains O(P), so R≤10R_{p+1} follows by increasing L₀(P); no widening of LG's width range is needed.

A safe local allowance per designated branch is L^{1000d}. For comparison, three lattice delta extensions of derivative order 40d cost at most L^{120d}; their local label sum costs L^{3d}; additional incident-label/frequency choices, cap/trace bookkeeping and lost normalization can be covered by the remaining allowance. The constants depending only on d and the fixed prefix parameters are absorbed by L₀. This uses exactly the local, pendant-stub construction above; it is **not** an allowance for an arbitrary fixed interior atom of a ladder. No estimate with L^{cN} belongs in this ledger.

With all other flower/anchor losses and the polynomial mark/flux costs reserved, use

    B(d) = 10000 d²

as a working bound on the total L exponent per P before the artificial j=0 gains. This is much larger than 8·1000d for d≥3 and leaves room for the original design-C costs. The exact optimized constant is irrelevant, but the proof packages must document their local costs and remain within this reserve. If an implementation produces a loss depending on N in the exponent of L, it has not followed this route.

Exponential costs C^N (local Fourier algebra, ordinary class decomposition, product splitting, input-family extraction) are absorbed by a reserved part of the underlying δ-per-order gain: choose δ small after ν and P, retaining δ^{2νN} in the final statement. Polynomial (N+1)^{C(d)P} costs are ≤L^{εP} for sufficiently large L with prefix parameters fixed. The original frozen statement at its exact exponent cannot itself be used as a black box and then charged these costs; use the underlying estimates with their unused slack.

The phase normalization in (4.2) is essential. It is (δL^{2γ}M)^{-2P}, not merely M^{-2P}. If some designated nodes were excluded from the order used in an interior estimate, restore their coupling factors and record the finite residual δ^{-C P} explicitly. It is legitimate to absorb this in L^P because δ and P are chosen **before** L₀ in `WTPrefixP`. For example δ^{-CP}≤L^P once L≥δ^{-C}. The same applies to constants depending on D. No constant may depend on the dyadic j₂, root k, or total order N.

For j₂≥1, after this adjustment the high-frequency estimate has the schematic size

    <k−ζk'>^{-4Λ_{p+1}P} δ^{2νN} M₁^{-80dP}
        · L^{B(d)P+P} M₂^{-2P}.

Since M₂≥L≥1, weakening M₂^{-2P} to M₂^{-P/9} is immediate. The unselected upper weights cost C^N, not a power of M₂.

For j₂=0, there is **no large resonance** and no integration-by-parts gain. Use only the weighted multiple-stub estimate. Supply the required L^{-P/9} by leaving that amount unused in the L budget. If j₁=0 as well, reserve another 80dP for its artificial M₁ gain. Numerically,

    10000d² + 80d + 2 < (100d)³,       d≥3.                         (5.1)

The probe checks (5.1). It leaves much more than P/9 plus the fixed-parameter absorption margin. Empty eligible stems at j₂=0 have product 1, exactly as required; no false lower-support assertion is used.

## 6. The actual consumer — question (d)

The main path is:

    B112Body / layergardenFlower
      → V2Chain.FixedpointS.flowerest1S_of_gates
      → X2Body (fixed-coordinate 2Pm moment)
      → X3Part2Prob.termB / probSum
      → X3Part2Num.termB_le, card_testB_le_real, powB_le, probSum_le
      → part2S_of_X2
      → fixedpointS_of_parts.

`FlowerTop` and `X2Kernel` transport the tree weights into the garden expansion. `X3DyadicReduction` uses their partition/support; `X3DaggerExpansion` removes the fixed flower-parent phase by fixing siblings; `X3KerInv` uses invariance of the remaining stem resonances and their upper bound to reduce the unbounded root range to `testB`. Thus the cutoff's **upper support** is as important as its tail gain. Dropping other-node upper factors would break this reduction.

The current Lean numerics differ from the paper's displayed Sobolev constants. In `X3Part2Num.par2`:

    q=2P, J=ceil(M₂^{1/50}), h=M₂^{-1/50},
    v(j₂)=(1−ρ)ρ^{j₂}, ρ=2^{-1/100}.

The representative set costs M₂^{D₀}, D₀=d(d+1), by `card_testB_le_real`. The dagger label count costs M₁ powers, not M₂ powers. Summation in k' uses the surviving Japanese-bracket decay.

If the fixed-coordinate moment gain is M₂^{-cP}, the two M₂ exponents, including the threshold v^{-q} and representative count, are

    value:       D₀ + q/50 + q/100 − cP = D₀ +(3/50−c)P,
    derivative:  D₀ −(q−1)/50 + q/100 = D₀ +(2−2P)/100.              (6.1)

The existing proof compresses the value term to the derivative exponent by requiring

    cP ≥ (4P−1)/50.

Hence **c=2/25 suffices with exactly the existing J,h,ρ and P≥100(d+1)²**. The exponent 1/9 is not sharp and is not necessary. Only the scalar `hJq` comparison (X3Part2Num L440–454) and the bound definitions need the numerical replacement; the remainder of the exponent argument is unchanged. The probe proves that comparison and the resulting summability inequality.

More generally, any fixed c>0 proportional to P suffices after retuning. Take J≈M^{c/8}, h=M^{-c/8}, and ρ=2^{-c/16}. Then the two exponents before D₀ are

    −5cP/8,        −cP/8+c/8.

Take P sufficiently large depending on d and c. In particular P≥1+8(D₀+1)/c makes the derivative exponent ≤−1. A gain M^{-c} with c independent of P is different: it need not beat D₀ or the costs of the supremum. A logarithmic gain does not pay for polynomially many representatives in this proof. This is a statement about this union-bound method, not a theorem that every possible method must use a power.

No weakening is recommended: §4 supplies a route to the full v3 gain. If a later implementation deliberately uses the weaker consumer contract, the exact RHS replacement is

```lean
(cut2.elim 1 fun j₂ =>
  if ∀ j, pat j = .plain then
    ((2 : ℝ) ^ j₂ * P.L) ^ (-(2 * Pm / 25 : ℝ))
  else 1)
```

Every other binder, hypothesis, factor, pattern clause, dagger clause, and the couple clause remains verbatim from v3. This is an optional successor contract, **not** permission to edit frozen v3. `weakerCut2Factor` in the probe type-checks the replacement independently. There is no proposed Lean change for the recommended full-exponent route.

## 7. Twist check — question (e)

On cut1 support, a nonflower top-subtree momentum has size O(N_top M₁), whereas a stem momentum is the signed flower/root momentum plus such an error. Since N_top is polylogarithmic and M₁≥L, |k|≥M₁^{10} makes stem and offstem momenta separated by at least |k|/2 for large enough L. An SG pair has separation ≤L^{-γ+η}≤1. Exactly one of u21,u22 cannot therefore lie on the stem. If the flower lies below u1, it travels through u11. This is the geometric content of T (7).

Use the actual decoration correspondence of `twistexplain(d)`: the momenta at u2 and u23 are exchanged. It preserves each signed stem resonance and the stem order; absolute Ω and every product factor, including the ordered marked term (2.1), are preserved. Comparing diagrams with the same *coordinate names* held fixed gives a spurious counterexample because it omits that exchange. The independent review explicitly tried and rejected that counterexample.

For a vine-top weight, invariance alone would not allow taking it outside the entire internal sum. The additional pointwise cancellation and spatial Fourier argument in §3.3 are necessary. No invariance is claimed for arbitrary large-gap twists; the source's decomposition only needs cancellation in the SG subclass. After excision, transport the recorded original-tree/mark data and restrict to the corresponding admissible class; do not erase that data and invoke unrestricted twists without the carrier proof.

## 8. Work packages and precise closeout conditions

Estimates are implementation sizes, not promises or already-proved line counts.

| Packet | Content | Estimated new Lean |
|---|---|---:|
| C2-A | Local quadratic Fourier-measure lemma; affine pullbacks/products; sumint/coarse spatial-modulation wrapper | 1–2k |
| C2-B | Weighted regular norms via incohproof2–15; weighted V5 common-factor transport; Stage-1 weighted representation | 2–4k |
| C2-C | Multiple-stub excision, gluing/carrier theorem, vector-time cap/floor/trace adapters; extend R61 construction | 3–5k beyond shared design C |
| C2-D | Exact mixed face/BV formula with one mark per original tree; all endpoint terms; retained phase labels | 1–2k |
| C2-E | Flux-decay extraction, local label sum, mark sum, prefix/slack ledger and v3 assembly | 2–3k |

Total roughly 9–16k incremental lines, with substantial overlap with FC3 and R61 work; uncertainty at least a factor of two. This is not the earlier optimistic 3–6k estimate. C2-A/B can start without freezing a new source-facing theorem. Do not add the final flower estimate or its multiple-stub specialization as an assumed gate and call the result closed.

Closeout requires: exact weighted identities; preserved incoherency powers; pointwise common-factor cancellation; twist-compatible marked carrier; all face terms represented; per-pin rather than per-order L loss; explicit flux summability; preserved cut1/decay and δ exponents; unchanged full v3 statement; no unproved axiom in the final provider. In particular the numerical budget must be rechecked against the implemented multi-stub construction. This report establishes a route and does not waive any of those checks.

## 9. Findings ledger / refutation outcomes

| Item | Finding | Disposition |
|---|---|---|
| F1 | The selected plain node might be the fixed f^pr stub | Refuted by definition; Lean local check |
| F2 | R58 temporal modulations directly implement χ(Ω/M) | False implication; use spatial Fourier lemma |
| F3 | Large |k|/M derivatives prevent uniform Fourier control | Refuted by (3.1), independently checked |
| F4 | Upper cutoffs destroy the incoherency gain | Refuted by exact spatial-modulation proof L987–1042 |
| F5 | Twist-invariant multiplier is automatically an external V5 coefficient | False; pointwise cancellation plus Fourier insertion repairs it |
| F6 | One naive integration by parts leaves an ordinary unchanged garden | False; face/multiple-stub adapter required |
| F7 | j₂=0 has a large-Ω mechanism | False; explicit L slack required |
| F8 | Full P/9 is required by the current consumer | Refuted; 2P/25 suffices with its current parameters |
| F9 | Missing multiple-stub API proves mathematical impossibility | Refuted; concrete extension, no counterexample |

Source exposition issue: T L2299 “integrating … before manipulating everything else” omits the face and carrier arguments, and “otherwise these cutoffs play no role” omits their weighted Fourier insertion. DH21 Cor 11.3 is evidence for a route, not a ready-made layered 2P-mark theorem. No new source falsity is claimed.

## 10. Validation

Read-only source/consumer inspection and independent refutation are complete at the scope stated above. `probe/Cut2Checks.lean` checks only local arithmetic and the exact frozen `fixPat` classification. Its compile command and result are recorded in `probe/Cut2Checks.log` and the final validation addendum below. No full project or dependency build was requested. No existing frozen `sorry` was used to prove the local checks.

### Final validation and limitation addendum

Command (from `/home/scott/WaveTurbulence-dev`):

```sh
nice -n 5 lake env lean /home/scott/wt-scratch/research-cut2/probe/Cut2Checks.lean
```

Exit 0; no Lean warnings or errors. All four printed declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`. The other arithmetic declarations also compiled. No `sorry`, custom axiom, or heartbeat override occurs in the probe. The toolchain was the existing `wt-throttled` override; elapsed time included a substantial shared compile-gate wait. An initial relative-path file creation failed before writing anything; an accidentally queued duplicate invocation was terminated while waiting at the wrapper. Only one actual Lean probe completed. No dependency compilation was invoked.

Final independent review supports the route as an architecture but does **not** certify its final numerical constant. It identifies one especially substantive remaining lemma: after fixing cut labels, the reconstructed fiber must be closed under the admissible augmented LF twists and contain complete coherent families. Injective/reversible gluing alone does not prove this. The adapter must verify canonicity across the glued layer-p boundaries, record original-tree membership and marked stem order, preserve the original topOrder/kind predicates, and show fixed anchor labels survive every allowed operation. An unrestricted garden estimate cannot bound a complex subset sum merely by inclusion. This is not currently proved here or in the cited design-C report.

Accordingly **do not mark cut2 or the flower theorem closed from this report**. `PROVABLE-VIA` in STATUS denotes the concrete research architecture, with this fiber theorem and the per-pin loss ledger explicitly pending. The analytic upper-cutoff problem and consumer arithmetic are resolved at the stated source-check level; the whole requested estimate has not received a complete mathematical or Lean proof in this task. No impossibility verdict is established either. This distinction is essential when answering the author.
