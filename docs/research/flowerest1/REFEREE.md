# Referee report — SUPPLEMENT-v1 (`flowerest1`, proved parts)

Referee: independent, refute-first (wt-orch request, 2026-11-07). Read-only on all other files.

## 0. Pins

- Supplement: `<scratch>/flower-open/SUPPLEMENT-v1.md`, sha256 `ddd81fe1238e7c51379a69981b4d10aa68690ced46d0fc1b115200fc0c3774d7` (verified at first read; 808 lines). A pinned copy was taken at first read.
- T: sha256 `493eef6b…727cb` (verified). D21: `50d0e236…fe402` (verified). D23: `c7e47dfa…5475` (verified).
- Line numbers below are "S<line>" for the supplement, "T/D21/D23<line>" for the sources.

(Complete. Summary table in §5; OPEN-item assessment and missing items in §4.)

## 1. Conventions of §1 (not lemmas, but they change the target)

- **Normalization d−γ (S32).** Correct. T671 and T712 use δ/(2L^{d−γ}). The printed d−1 in T2264–2265 is inconsistent with 𝓛₁ (T725, built from the T712 trees) and with the expansion (T2287 "follow the arguments in Section secduhamel"). Accept as an erratum.
- **Order-zero convention (S34).** Necessary: for the trivial flower tree, T2264's δ(t_{f^pr}−s) has no f^pr. Reading (1.1) as a bound on the regular kernel 𝔛_reg = 𝔛 − I on p<s<t<p+1 is the only meaningful pointwise reading. It is consistent with 𝔜 = (1−𝓛₁)𝔛 − 1 (T2273), whose "−1" removes I. This is a **statement-level reinterpretation**: wt-orch should record it as such, not as a proved step. No negative-sign order-zero term exists: for a trivial tree ζ_f = ζ_r = +.
- **Quantifier order (S15).** "P first, δ second, L last" is consistent with T2279 ("P large depending on C₁", "δ small depending on P") and with T606–610 (ν depends on C₁, δ on ν, C₂ on δ). Fine.

## 2. Per-lemma verdicts with reasons

### Lemma 2.1 — Capped encoding: **PASS** (one wording fix)
- (1) A cap c_j is a trivial tree; its root is a leaf. Pairing c_j with f_j needs opposite signs, and the cap's sign is chosen that way. Signature balance: in each tree the leaf signs sum to the root sign (ternary rule (ζ,−ζ,ζ), T630). The non-flower leaves are paired, so Σ_j ζ_{f_j} = Σ_j ζ_{r_j} = 0. Hence the caps are balanced. No branching node is added, so order, resonances and signs are unchanged.
- (2) Each component has even width: a completely paired component has root-sign sum 0 by the same leaf-sign identity. Canonicity: the recursive construction T660/T2261 restricted to a component is checked correctly. The key fact is that an irreducible lower replacement cannot straddle two components. This also gives the T637 ⇔ T660 irreducibility equivalence. The alternative check through `canonequiv` (T889(ii)) is also right: the only newly completely paired pairs (n,n′) have n′ = c_j, and L_{c_j} = p ≥ the required min.
- (3)(4) Bijection and labels: correct.
- **Wording fix (non-substantive):** (2) says "at most 2P components". The proof gives 4P/2 = 2P. OK as stated.
- Remark used later and verified here: by `block_clcn`(1a)(iii) (T1349), a (CL) realization 𝒢[𝔅] is completely paired inside itself. In the capped garden this means **no (CL) or (CN) realization ever contains a flower**: f_j's partner c_j is a separate root. So the stem can meet a (CL) realization only through u₁ → {u₁₁, u₂₁, u₂₂}.

### Lemma 2.2 — Decoration-sum and moment identities: **PASS**
- (2.1): the caps add no branching node, no time variable and no ε factor. Exactly one leaf of each flower–cap pair has sign +, and it receives input 1, so ∏^{(+)} matches T2265's "l ≠ f". ζ(Ĝ) = ζ(G) and the normalization is unchanged.
- Moment statement: deterministic multipliers depend only on decorations, which are summed outside E_p. The inversion formula T573 (valid under 𝔉_p by T576) is applied exactly as at T2288. The ansatz T693/T698 supplies F_q pairs and 𝒢_p gardens of order ≤ N_p, matching ℋ^tr. Block sizes: 2P(2N_{p+1}) ≪ 2R_p, so (ansatz3) is always within range. The error terms keep their multipliers.
- The caveat at S86 is correct: (2.1) is not an ordinary 𝒦_𝒢, because the input 1 is not Schwartz and there are pins. `layergarden` does not apply to it directly.
- Interchange of E_p with infinite decoration sums is used exactly as T itself uses it. No new issue.

### Lemma 3.1 — Fourier-measure algebra: **PASS** (one wording fix)
- Pushforward/convolution argument correct. The moment bound (3.5) is correct, using 1+2π|Σv_i| ≤ Σu_i for h ≥ 1 and (Σu_i)^s ≤ h^{s−1}Σu_i^s.
- **Wording fix:** "increases its Fourier L¹ norm by at most B₀(χ)^h" should read "multiplies … by at most B₀(χ)^h".

### Lemma 3.2 — Shell expansion and commutators: **PASS** (notation fix)
- Telescoping plus the fundamental theorem of calculus is correct. The translations ub_ir are unimodular phases. TV ≤ R_*^{-1}Σ_i‖b_i‖B₁B₀^{h−1} after the factor |r| is removed, where the amplitude depends on r̂ = r/|r|, u and r. In every application (S320, the LF twist, x_*−y_* = ±r, T1897) r is the vine **output** gap, so this dependence is allowed by Lemma 4.2. The |r| is exactly sumint alternative (b) (T1611, T1657).
- **Notation fix:** "fixed vectors b_i, fixed r ∈ ℝ^d, b_i r" is ill-typed. b_i must be scalars (in use, b_i ∈ {0,±1}) or d×d matrices with operator norm ‖b_i‖. State which.

### Lemma 4.1 — Frontier-weighted `proplayer1`: **PASS AFTER FIX** (proof-level fix for the tree half; the statement stands)
Checked against T981–1092:
- T986/T993: every leaf satisfies k_l − k = z_l, an integer combination of (x_n, y_n). Conservation gives every vertex k_v = k + z_v. Ω and ε are translation invariant (T647, T990). So an inserted χ((k+z_v)/R_v) is affine in (k,x,y) with k-coefficient I/R_v, and Lemma 3.1 applies with ‖A^{(k)}‖/R_v ≤ 1.
- T995 ("derivatives fall on F") becomes: derivatives fall on F or on the χ's. The χ part costs ≤ h^{s}B_sB₀^{h−1} with s ≤ 32d (30d for the norm plus 2d for the Sobolev step T997–1000). The ⟨k⟩^{30d} weight still comes from max⟨k_l⟩ (T995).
- **Couple half:** the norm order (sup_k inside the λ-integral) is handled exactly by T999 (incohproof4): Sobolev in k, then Fubini. Correct.
- **Tree half — the proof's sentence is wrong as written.** S189 says "Thus the Sobolev step gives the norm (1.2)" for both objects. But T1060 states explicitly that for 𝒦*_𝒯 "the manipulation in (incohproof4) is not possible", because there is no k-decay (no input at the lone leaf). T then uses a different argument (T1062–1092). It reduces to 𝒦̃(t,s,k) with parameters (a,b,ξ,ξ′) "allowed to depend on k" (T1065). It gets bounds uniform in k: L¹/L^∞ of 𝒮, 𝒮_j for the negative endpoint (T1077–1083), and the e^{iΓ(t−s)} replacement with timeintlem2 for the positive endpoint (T1084–1091). Then it interpolates.
- **Fix:** for 𝒦*_𝒯, replace the Sobolev sentence by: the inserted factors have, by Lemma 3.1, a joint Fourier measure in (k,x,y) whose k-dependence is the unimodular phase e(ζ_k·k). Like the e(λ·k) factor of Ŵ (T1009), they only modify the k-dependent parameters ξ, ξ′ and a unimodular prefactor. So T's uniform-in-k argument applies verbatim, with an extra factor TV ≤ B₀^h and the derivative moments as above. With this fix (4.1) holds for both objects. The statement is unchanged.
- At fixed k the inserted factors convolve Ŵ (T1007–1012). The final expression (incohproof8) is estimated "uniformly in all choices of (ξ_n, ξ′_n)" (T1017). So the bound is multiplied only by the TV.
- C_χ depends on d and χ only, so it is a C₀-type constant and δ-independent. The extra cost has no power of L. Correct.

### Lemma 4.2 — Fourier-measure `sumint`: **PASS**
Checked against T1595–1721:
- Step 1/2 (T1621–1670): W = ∏K_j^i L_j^i already depends on the output through h₁, h₂ (T1599(i)). Multiplying by a_o convolves Ŵ with μ_o at fixed o. Bound ×D. The absolute-value factorization in (Iboundstep2) survives because the Fourier expansion of a_o is a product of modulations.
- Negative endpoint (T1681–1697): the scalar quantity ‖𝒦‖_{L^∞_o L^1_t(𝒬*)} is multiplied by D, using |∫𝒦_ξ dμ_o| ≤ ∫|𝒦_ξ| d|μ_o|. The time-frequency majorant ⟨ξ+θ⟩^{−1}⟨ξ′⟩^{−1}⟨ξ″⟩^{−1} is independent of o. θ is built from time parameters only (T1679).
- Positive endpoint (T1713–1721): sup_o is replaced by Σ_o (≤ L^{4d}) **before** Plancherel. At fixed o, Minkowski in μ_o followed by the T1717 fixed-time estimates (uniform in spatial modulation) gives ×D. No extra output-counting loss.
- Interpolation is pointwise in λ, so it carries ×D. The affine-cutoff remark is correct because (3.4) is uniform in A_i, b_i.
- The closing caveat (S222) is correct and important: the amplitude may not supply alternatives (a)–(d).

### Lemma 5.1 — Coherent trunk factorization: **PASS** (scope clarification)
- Structure: T899 (`layerreg1`) puts side couples in their pair's layer. The trunk is nonincreasing from q to q′. T1235–1237 gives k_{r_[r]} = k at every layer junction. So: layer-p terminal pairs are pairs of original frontier leaves with common momentum u, giving χ(u/R)²; exactly one frontier crossing (momentum k) when q = p > q′, including the empty layer-p trunk and the trivial/type-1 couples at (p, q′); and none otherwise. Exhaustive.
- Factorization (T1241, T1244) and the definition of (·)_app via the single-layer factors (T1242) are correct with the substituted profiles. T1173 states that the D21/D23 single-layer theory needs only real inputs bounded in the regularity space. F^{[R]} is real, and (5.3) is correct by the product rule.
- The remainder χ^c 𝓡_𝒪[F^{[R]}] keeps the (layerregest3) bound because multiplication by χ(k/R)^c is bounded on X^{η,30d,30d}.
- **Scope clarification:** state explicitly that 𝒪 does not contain a flower–cap pair (input 1, pinned). The regular tree whose lone leaf is f_j pairs with the trivial cap tree, and it falls under OPEN 7.3, not 5.1. The convention "an edge ending at the lone port is assigned to that tree" is consistent with c(q,q′) = 1 when the only crossing is at the lone leaf.

### Lemma 5.2 — Weighted tuple identity: **PASS**
- For a fixed common R this is a direct corollary of `proplayer4` (T1118–1123) applied to the real input family F^{[R]}. The proof of `proplayer4` (T1251–1286) is algebraic (regref2-3, regref3, the tuple permutation) and uses only reality of the profiles, not smallness of 𝓡. The supplement re-derives it faithfully (S279–300 ↔ T1265–1286). The multiplicity discussion is correct under either reading of "all permutations".
- Common factor χ(k/R)^{2c(q,q′)}: correct, since 𝒬 and 𝒯 in `proplayer4` share (q,q′).
- R-derivatives: each fixed-order sum is a finite sum of multilinear expressions in F^{[R]}, smooth in R with S-bounded R-derivatives. A real-valued smooth function has real derivatives. Correct.
- "Common scale" is legitimate inside a (CL) realization: by `block_clcn`(1a)(iii) the realization is completely paired within the subtree of u₁. Any lower garden meeting it is irreducible and so lies wholly inside. All frontier vertices therefore lie in one B_j.

### Lemma 5.3 — Local weighted `vineest`: **PASS** (one clarification)
Checked against T1742–1923:
- Non-core / Step 3 (T1841–1848): weighted 𝒦*_𝒬, 𝒦*_𝒯 come from Lemma 4.1 (incoherent) or Lemma 5.1 plus `proplayer2` (coherent). The modulation expansion with S^{30d,30d} spatial coefficients is unchanged. Cutoffs at skeleton vertices of the realization are functions of alternative variables k_j^i, ℓ_j^i (T1797 (A-i)), so Lemma 4.2 applies.
- Equal upper layers (T1883–1907): with L_{u₃} = L_{u₄} both terms carry χ(x_*/R)^c χ(y_*/R)^c. Moving to a common argument splits as [χ^c(y)−χ^c(x)]M(y) + χ^c(x)[M(y)−M(x)]. The first part is Lemma 3.2 with factor |r|, i.e. case (b). The second is T1902. The leading term (d) is 2i·Im of the Lemma 5.2 sum, hence 0.
- Unequal upper layers (T1911–1922): I checked the c-bookkeeping. With L_{u₃} = p > L_{u₄}, II-a gives χ(y_*/R) from 𝒬̄ (upper layer p) and II-b gives χ(y_*/R) from 𝒯̄ (upper layer p). So the incoming factor is common, at the same momentum y_*. 𝔅″ objects have root layer ≤ L_{u₄} < p, so F^{[R]} = F there. Correct as stated.
- **Clarification:** the proof should say explicitly that the frontier *set* inside the realization is determined by layers (a frontier vertex is a layer-p leaf, or a layer < p vertex with a layer-p parent). LF twists preserve layers (`lftwist`, T1466ff), so outside (𝒬,𝒯) the frontier set and its momenta are permuted exactly as the decorations are (T1877). The proof uses this implicitly.

### Lemma 6.1 — One frontier derivative per tree: **PASS**
∂_Rχ(k/R) = R^{−1}D(k/R), with D(u) = −u·∇χ(u) ≥ 0 supported in 1 ≤ |u| ≤ 2 (χ is radial and nonincreasing). Integrate over [M/2, M] (mass log 2). |B_j| ≤ 2n_j ≤ 2n+1. Correct.

### Lemma 6.2 — Propagation and exact polynomial extraction: **PASS**
- (6.2) by iterating conservation through the lower insertions (no flower below a non-flower frontier vertex). Large-leaf claim by the triangle inequality.
- (6.3) is exact: b_{M,R}(x) = M^a⟨x⟩^{−a}D(x/R), and ⟨k_v⟩^a with a even is a polynomial. Coefficient sum ≤ (1+dm²)^{a/2} ≤ C_{d,a}(1+m)^a. The scaling and compact-support Sobolev argument is uniform for R ≥ 1, M/R ∈ [1,2].
- The bookkeeping after the lemma (S376: M₁^{−80dP}, ≤ 80dP modified leaf occurrences, (1+n)^{(80d+2)P}) is correct. (6.4) is correct for both root signs. The decay-budget paragraph (S385) is explicitly not a bound; correctly deferred to OPEN 6.3.

### Lemma 7.1 — Localized spectral fibers: **PASS**
Counting through tuples, (C_dL)^{4d} (consistent with, and stronger than, T2295's L^{10d}). (7.1) by Tonelli and the measure bound. It is uniform in centres because only tuple counts are used.

### Lemma 7.2 — Terminal-pin algebra: **PASS**
An elementary identity for a totally ordered chain. The translation phase e^{πiqΣβ} = 1 for complete pairs, and for the odd chain the phase is cancelled by e^{πiβ_{2m}(q+s′)}. The supplement correctly states that this is not the D21 analytic estimate.

### Lemma 9.1 — Exact time integration with faces: **PASS**
- On the raw garden the integrand depends on t_v only through e^{iω_v t_v} and the order constraints. All spatial filters are time independent. A selected v ∈ S_j is not f^pr, so it is unpinned. If f^pr is a child of v, the pinned value s is one of the ≤ 3 child times in A_v.
- Different original trees share no time constraints. (timegarden) T673 has only parent–child and layer constraints; lower trees hang below a single original tree's leaves; leaf pairings impose none. So iterated integration is legitimate. ≤ 4 maximizer pieces × 2 endpoints = 8 per selected vertex. (9.1) is immediate.

### Lemma 7.1 — Localized spectral fibers: **PASS AFTER FIX** (applicability)
- As stated (every incident momentum in a unit ball of a translate of ℤ_L^d = (L^{-1}ℤ)^d, T285) the count (C_dL)^{4d} and (7.1) are correct.
- **Fix:** T's localizations (T1002, T2295) fix *leaves* to unit balls, not node momenta. A node momentum is then known only to lie in a ball of radius ρ ≲ (number of descendant leaves) ≤ Cn. Either state the lemma for radius-ρ balls, with bound (C_dρL)^{4d} ≤ L^{4d+o(1)} since ρ ≤ (log L)^{C₂}, or record the refinement cost (Cn)^{4d} per marked vertex. That cost is polynomial in n and absorbed by Lemma 10.1. Both fit T2295's L^{10d}. Inside `sumint` the refinement already happens (T1621: ℓ_j^i are localized at cost C₀^M).

### Lemma 8.1 — Stability of the integrable coefficient: **PASS** (one transcription fix)
- Transcription of D23 965–967 is faithful: exponents 1−η/8, η/4, 1−η/2; variables (λ₁,λ₂,α[𝒩^ch∖Z]); C^n(2|ρ|)! for all ρ. The supplement writes C₀^m with m = number of integrable coordinates, where D23 uses C^n with n the half-order (n ≥ m). This is harmless. **Fix:** say "C₀^n, n the half-order" to match D23. Also note that D23 969 obtains these weights "by careful inspection of [DH21, §5]". Lemma 8.1 inherits that unproved-in-detail input, but does not add to it.
- Proof: |∂^νΘ| ≤ A₁^{m+|ν|}(2|ν|)! follows from Σ_μ C(ν,μ)(μ!)²((ν−μ)!)² ≤ 2^ν(ν!)², (ν!)² ≤ (2ν)! and S_j ≥ 1. Then Leibniz, and sup_r C^r(2r)!/(4r)! < ∞. (8.4) is immediate.
- **Sufficiency of (4|ρ|)!**: sufficient. The `approxnt` hypothesis itself is ‖∂^ρΨ₁‖_{L¹} ≤ C^n(4|ρ|)! (D23 999, `propertypsi2`; D21 1170–1172 with |ρ| ≤ 10n). The source feeds the (2|ρ|)! of D23 965 into a (4|ρ|)! hypothesis, and that slack is never used. The derivatives are used only in the minor-arc step (D21 1619: (8f)! absorbed by L^{−υf}). So C_A^{m+1}(4|ρ|)! meets the hypothesis literally. The supplement's own caveat (S533) is accurate: Lemma 8.1 does not touch the extracted reciprocal factors (8.7).

### Lemma 9.4 — Where filters may be discarded: **PASS**
Trivial monotonicity of a nonnegative counting sum. The counterexample showing it fails before absolute values is correct.

### Lemma 9.5 — Bottom blocks: **PASS**
Tautological substitution. It is used correctly in Prop 10.3. Note it presupposes that the bound "with nonbottom gains only" has been proved *with the bottom cutoff (A_{j,L} or U_{j,L}) inserted* — a weighted estimate covered by the OPEN items, not a free statement.

### Lemma 10.1 — Polynomial overhead: **PASS**
B_{P,δ} = sup(1+n)^{A}2^{−n} < ∞. δ is chosen with 2D_Pδ^{6ν} ≤ 1, independently of A_{P,δ}, E_{P,δ}. L is chosen last. Quantifier order correct: δ depends on (P, ν, D_P), L on (P, δ, ε).

## 3. Citation and text-level findings (not lemma failures)

- **S438 (after Lemma 7.2):** "retain integrability in all but at most two spectral variables per pin" is a miscount. D21 2689 loses integrability in β_{2m} only. Its linked partner β_a = −β_{2m} is the *same* α_j, handled as a "harmless class J operator". So the loss is one α-variable per pin; "at most two" (D21 2694) is the total for the two flowers. OPEN 7.3's |E| ≤ 2b is therefore generous, which is fine as a sufficient target. **Fix the sentence.** Also, calling D21 2684–2694 "an existing result" overstates it: D21 omits cases ("for simplicity we will omit this case", D21 2689; "Case 1 is much easier … directly calculate", 2688).
- **S456 (OPEN 7.3, "boundary modulations must be carried through the class-J/R recursion"):** partly overstated. Fixed phase shifts are already parameters of the D21 calculus (λ_a, λ₀ in D21 946; translation identity D21 948–949; uniformity in μ[E], D21 955–961). The genuinely new parts are the layer constraints and chains split across layers (D21 953: operators act on [0,1] with integration from 0).
- **S556:** `Psi_1` is missing its backslash. **S392:** "C_{P,χ}^{,n+1}" has a stray comma.
- **S566 (OPEN 8.2, order range):** D23 1002 indeed assumes n ≤ (log L)³. But D23 itself applies `approxnt` up to N³ = (log L)^{12} (D23 438, 1168). T's own `regref1` (T1145–1173) cites D21/D23 with no range comment while T allows n ≤ N_{p+1}^4. So the order-range objection applies equally to the unweighted results the supplement treats as legitimate. The proofs use the order bound only to absorb factorials, and any polylog bound works. Classify it as citation hygiene, not an obstruction specific to the truncated version.
- **T2299 vs D21 Cor 11.3 (D21 2699–2705):** D21's high-resonance gain is a single factor M₁^{−1/9}M₀^{5d}, even with several cutoffs. It comes from coefficient weights and denominators, not from integrating the selected time first. T's per-tree product M₂^{−P/9} therefore goes beyond what Cor 11.3 states. The supplement correctly treats (8.6) as a new requirement rather than a citation.

### Lemma 9.2 — High-root separation: **PASS AFTER FIX** (wording; the mathematics is right)
- First paragraph correct. On the support of the shell all |k_v| < 2R ≤ 2M₁. An off-stem top-tree vertex has |k_u| ≤ 2bM₁ and a stem vertex |k_u| ≥ |k| − 2bM₁, so any ±-combination is ≥ |k| − 4bM₁ ≥ |k|/2. Numerics: 8b ≤ M₁⁹ holds since b ≤ 2N_{p+1} + 1.
- Second paragraph: by T1349, u₂₁ (sign +) and u₂₂ (sign −) are **siblings, both children of u₂**, and u₂ ∈ 𝒢[𝔅] is a proper descendant of u₁ not below u₁₁. If u₂₁ or u₂₂ is on the stem, then u₂ is a layer-p stem vertex (T2261) and the other one is an off-stem child of u₂, i.e. a top-tree vertex or an original leaf. The SG gap at the joint is r = ±(k_{u₂₁} − k_{u₂₂}) with 0 < |r| ≤ L^{−γ+η} (T1938–1940, T1769). This contradicts the separation ≥ |k|/2. The third child u₂₃ lies in 𝒢[𝔅], which is completely paired, so the stem cannot exit there. Hence the stem exits through u₁₁.
- **Fixes:** (a) "the other is its off-stem child at a layer-p stem branching vertex" → "the other is the sibling, an off-stem child of the stem vertex u₂". (b) "an SG (CL) realization containing the flower" → "an SG (CL) block whose top u₁ is an ancestor of the flower". A realization never contains the flower. (c) The SG bound is |r| ≤ L^{−γ+η}, stronger than the "≤ 1" quoted.
- Consequence used below: when the gap is SG, only u₁ of the chain lies on the stem. When the stem exits through u₂₁/u₂₂, the block has |r| ≥ |k|/2, i.e. it is **large-gap**, and then the stem runs through the block interior: the parent chain from u₂ to u₁ passes through every rung group (T1519).

### Lemma 9.3 — Affine SG-top filter: **PASS AFTER FIX** (location wording, plus one missing sentence)
- Identity Ω = 2r·(a−f) is correct with T647/T564. r and f are outputs (T1763, T1769). a is the momentum of the middle (opposite-sign) child of u₁, which lies in 𝒢_sk[𝔘]∖{u₁}. So a is a `sumint` alternative variable, affine in **x** with constant 0/±1 coefficients and an output-dependent shift (T1797 (A-i), T1599(i)). The Fourier-measure claim and the derivative bound are correct.
- **Fix (location):** the filter sits at the **top u₁**, a stem vertex whose resonance involves its interior children. It does not sit "at a same-sign stem child". Also, Ω_{u₁} drops out of the phase through Γ (T1745, T1763–1767), so the filter is a genuinely extra amplitude.
- **Missing sentence (needed before the LF cancellation, cf. S316):** the filter must be common to all twisted terms. It is: a unit twist only exchanges the values k_{u₂}, k_{u₂₃} (T1458). For Vine (I) the middle slot of u₁ carries the value k_{u₂₃} in both (I-a) and (I-b); for the other vines u₁'s interior children are untouched. So ϑ(Ω_{u₁}/M₂) is a common factor and enters `sumint` through Lemma 4.2 only after the cancellation. Add this, or the derivative bound fallback (difference ≤ |r|²/M₂, case (b)).

### Lemma 7.4 — Graph bookkeeping for excision: **PASS** (two remarks)
- Algebra: e_S = (4|S| − D_S − q)/2 gives 2v′ − e′ = R + (q − D_S)/2, with parity guaranteed by 2e_S + q = 4|S| − D_S. Component and boundary counts correct.
- Conventions: R is half the total degree deficit, R = Σ(4 − deg)/2. This matches T1304 ("n atoms and 2n−R bonds, circular rank χ = n − R + 1"), T2042 and T2113. **Remarks:** (i) state that a self-loop counts twice in deg, as in T1295. (ii) For the capped garden R equals 2P, the capped half-width, not the flower R = P of T2288. Downstream uses such as (C₀R)! and the T2162 cut count must use the capped value.

### Proposition 10.3 (as a conditional): **PASS**
- Line by line: Lemma 10.1 with ε = 1; bottom cost (80d + 1/9)P; Σ_{n≥1}δ^{2νn} ≤ 1 for δ^{2ν} ≤ ½. The margin "+3" covers ε = 1, leftover constants, and the factor ½, and with (10.2) the total is ≤ ¾ of the right side. 𝔜/𝔚: original trees lie entirely in layer p (T2261; inserted gardens have all nodes in layer ≤ p−1, T698). So T2290's "number of layer-p branching nodes" equals the original-tree order, and the expanded order is ≥ 2P(N+1) ≥ N+1. e^{−102(N+1)}/(1−e^{−102}) ≤ e^{−100N}. All correct.
- **But note:** the proof uses only (10.2), (10.3), (10.4), Lemma 9.5 and Lemma 10.1. OPEN 6.3/7.3/7.5/8.2 appear in the hypothesis list but are logically idle: they are the intended route to (10.3), not inputs to this proof. See §4.
- (10.3) should state explicitly that E, A, D_P and B are uniform in (t,s,k,k′,M₁,M₂) and in ζ.

## 4. The OPEN items: correctness and joint sufficiency

### 4.1 Each OPEN item as stated
- **OPEN 6.3 — correct in substance; three fixes.**
  - (i) Stray comma in (6.5), "C_{P,χ}^{,n+1}".
  - (ii) The explicit retention clause names only *unmarked* incoherent objects and bad vines. The supplement concedes that a marked/protected object can have order ~ n (S398). Its incoherency gains are what absorb the δ-dependent layering and atom counts C₂^g C₀^{m+|q−q′|} (layerreg2, T932), C₂^{m_sb} (T2248) and C₂^{ḡ+ρ̄} (T2252). If they are dropped, the base becomes δ-dependent, which (6.5) forbids. State explicitly: all but O(P) units of the ḡ+ρ̄ gains, marked objects included, must be retained.
  - (iii) Uniformity in (t,s,k,k′,M₁,M₂,ζ).
- **OPEN 7.3 — correct, and sufficient as a target.** |E| ≤ 2b is generous: D21 2689 loses one α-variable per pin. It covers the Lemma 9.1 faces, including the face where the pinned child time s is the lower endpoint (v_j = grandparent of f_j). Only the motivating citation sentence S438 needs fixing (§3).
- **OPEN 7.5 — stated incompletely; restate before anyone proves it.**
  - (i) The `subpro` cites are off by two lines. "tame in the sense of T2046" should be **T2044**. "two SG bonds of T2048" should be **T2046**. "hinge configuration in T2049" should be **T2047**. (T2048/T2049 are `\end{enumerate}`/`\end{prop}`.)
  - (ii) Omitted from `subpro`: the second sentence of (5), "If v is also a joint of an SG vine (or HV) in 𝒞₁, then (ℓ₁,ℓ₂) is chosen to belong to this vine" (T2046), which T relies on at T2104; the case restriction "must be in one of the cases defined in Lemma subsetvc" (T2045); the hinge count "a total of q_sk atoms" (T2043); and the support hypothesis ε̃·𝒵 ≠ 0 (T2040), which must be restated with pins and cutoffs, including whether ε_v is kept at B-atoms (T1957 drops it only at hinges).
  - (iii) Clause 1 drops "connected" (T2042) but gives no replacement for the two places T uses connectivity: χ(𝕄_sb) = n_sb − R + 1 (T2113) and "at most 2R−1" component-creating cuts (T2162). Lemma 7.4 gives F′ ≤ c+q; the restated clause should carry χ′ = e′ − v′ + F′ with that bound.
  - (iv) Add "ladders are split at B-atoms", which is what makes T2081's independence hypothesis hold after excision.
- **OPEN 8.2 — correct within its scope.** That scope is "every regular-object reduction used in T1090–1244". It does not reach ladders of 𝕄_sb (see M2 below). The order-range remark (S566) applies equally to T's unweighted results (§3).
- **OPEN 10.2 — correct.** T803–807 bound ℰ^{(1)}, ℰ^{(2)} with no M₂-decay, and M₂ is unbounded relative to L, so a weighted argument really is required. The 𝔜/𝔚 e^{−100N} requirement is easy (ℰ^{(1)} ≲ e^{−N_p} with N_p = N_{p+1}^{(40d)²}).

### 4.2 Are the five OPEN items together sufficient for the assembly? **No.** Missing:
- **M1 — the aggregate (10.3)/(10.4) (a genuine sixth item).** Prop 10.3 assumes it separately, and the supplement half-concedes this (S727, S747). It is not implied by 6.3/7.3/7.5/8.2 as worded. It needs:
  - the T2237–2255 rigidity count for marked components with boundary, including the connectivity replacement in 7.5(iii);
  - the marked-gain retention of 6.3(ii), so that C₂^{ḡ+ρ̄} is absorbed and D_P is δ-independent;
  - the composition of the per-object costs of 6.3/7.3/7.5/8.2 into one δ-independent base D_P, with ρ̄ changing by only O(b) (cf. T2213);
  - an explicit numerical B with B + 80d + 1/9 + 3 ≤ (100d)³.

  Recommend listing it as **OPEN 10.3 (aggregate count and budget)**.
- **M2 — unselected stem upper filters on ladder rungs of 𝕄_sb (a genuine gap, not covered by any listed item).**
  - The setting. If the stem exits an SG-adjacent block through u₂₁/u₂₂, Lemma 9.2 forces a gap |r| ≥ |k|/2, i.e. a large-gap (LG) block. Its interior is then on the stem: the parent chain passes every rung group (T1519). Only SG chains are spliced (T1944–1946), so these LG ladders survive among the maximal ladders of 𝕄_sb.
  - The violation. `finalsbest1` (T2076, T2081) applies `ladderl1new` to them under the hypothesis "𝒦†(k[𝕎]) does not depend on any of the k_ℓ variables for ℓ ∈ 𝕃". `ladderl1new` is a pointwise *oscillatory* rung-sum estimate (T1989–1991; Poisson summation plus lemlayer1/2). A filter ϑ(Γ_v/M₂) with Γ_v = 2x_j·y_j or −2x_j·y_j + 2r·ζ_j (T1989) is a multi-bond, genuinely quadratic amplitude, and it violates that hypothesis.
  - Why it is uncovered. 8.2 is restricted to regular objects. Lemma 9.3 handles SG tops only. Lemma 9.4 applies only after T2090–2097. 6.3 and 7.3 concern marks and pins. 7.5 protects only O(P) vertices, while the stem can cross unboundedly many LG ladders. `finalsbest1` cannot be skipped: the interpolation with `finalsbest2` supplies the δ- and g-gains (T2079, T2220–2225).
  - T itself gives no argument: T2299 says the unselected cutoffs "play no role".
  - Likely repair (not done): Fourier-invert ϑ. Each filter becomes a shift v_j ↦ v_j ± 4τ/M₂ of v_j = δL^{2γ}(t_j − s_j) inside e^{πiv_j⟨x,y⟩}, plus an r-dependent linear modulation. lemlayer1 (T958) is uniform in shifts with |s| ≤ L, lemlayer2 (T972) tolerates shifted windows, and the Gevrey decay of 𝓕ϑ controls large τ. The cost would be ‖𝓕ϑ‖₁ per filter. Care is needed because the shift perturbs the time domain, and T1603(iii) only allows fixed order constraints.
  - Recommend **OPEN 8.3 (filtered ladders)**.
- **M3 — one missing sentence, not an open problem.** Single-bond frontier factors on ladder bonds — χ(k_ℓ/R) and the shell differences — fit `ladderl1new`'s factor class: ∏_{ℓ∈𝕃}𝒦_{(ℓ)} with unit-ball support and ≤ 30d derivatives bounded (T1965, T1983). The cost is C_χ per bond with a δ-independent base. Unmarked frontier cutoffs inside unprotected ladders are therefore fine, but the supplement should say so. Marked leaves (monomials, b_{M,R}) remain under 6.3.
- **M4 — downstream, outside `flowerest1` as printed (for wt-orch's campaign map).** The proof of `fixedpoint` consumes variants that neither (1.1) nor any OPEN item lists:
  - the 𝒥† kernel, with sibling momenta fixed and the pinned phase removed at cost M₁^{20dP} (T2327–2328);
  - the ∂_{t,s} versions with the extra pins δ(t_r − t) and δ(t_n − s), n the parent or a non-flower child of f^pr (T2331). The flower's grandparent is not in the protected list (S68), and the coincident pins t_{f^pr} = t_n = s give a face not among Lemma 9.1's;
  - the root-pinned ∂_t a^tr bound (T2312).

  These are not needed for `flowerest1` itself, but a campaign that targets `fixedpoint` needs an item for them.

## 5. Summary table

| Item | Verdict | Fix (if any) |
|---|---|---|
| 2.1 | PASS | — |
| 2.2 | PASS | — |
| 3.1 | PASS | editorial: "multiplies by", not "increases by" |
| 3.2 | PASS AFTER FIX (notation) | type b_i: scalars, or d×d matrices with operator norm |
| 4.1 | PASS AFTER FIX (proof) | tree half: replace the Sobolev/norm-order sentence by T1062–1092's uniform-in-k argument; the inserted factors enter only as k-dependent parameters and unimodular phases |
| 4.2 | PASS | — |
| 5.1 | PASS AFTER FIX (scope) | add the hypothesis "𝒪 contains no flower–cap pair" (that object belongs to OPEN 7.3) |
| 5.2 | PASS | — |
| 5.3 | PASS | recommended sentence: LF twists preserve layers, so the frontier set outside (𝒬,𝒯) is permuted with the decorations |
| 6.1 | PASS | — |
| 6.2 | PASS | — |
| 7.1 | PASS AFTER FIX (applicability) | state for radius-ρ balls, (C_dρL)^{4d}, or record the (Cn)^{4d} refinement cost; T localizes leaves, not node momenta |
| 7.2 | PASS | (fix the citation sentence after it: one α lost per pin, not two) |
| 7.4 | PASS | remarks: self-loops count twice; R = 2P for the capped garden |
| 8.1 | PASS AFTER FIX (transcription) | base C₀^n with n the half-order, as in D23 965 (not C₀^m). (4\|ρ\|)! is sufficient (D23 999) |
| 9.1 | PASS | — |
| 9.2 | PASS AFTER FIX (wording) | "the sibling, an off-stem child of the stem vertex u₂"; "block whose top is an ancestor of the flower"; SG means \|r\| ≤ L^{−γ+η} |
| 9.3 | PASS AFTER FIX (wording + one sentence) | the filter sits at the top u₁; add twist invariance (T1458: only k_{u₂} ↔ k_{u₂₃}, and the middle slot of u₁ is unchanged) so it is a common factor before the LF cancellation |
| 9.4 | PASS | — |
| 9.5 | PASS | — |
| 10.1 | PASS | — |
| 10.3 (conditional) | PASS | its proof uses only (10.2)+(10.3)+(10.4); state uniformity of (10.3) |
| OPEN 6.3 | correct; clarify | make marked-gain retention explicit; uniformity; typo |
| OPEN 7.3 | correct | — |
| OPEN 7.5 | incomplete | fix cites (T2044/2046/2047); restore subpro (5) second sentence, the subsetvc note, q_sk, the support hypothesis; give the connectivity replacement (T2113, T2162); split ladders at B |
| OPEN 8.2 | correct (scope regular objects only) | — |
| OPEN 10.2 | correct | — |
| **Missing** | M1 aggregate (10.3)/(10.4); **M2 filtered LG ladders in 𝕄_sb**; M3 one-line single-bond ladder remark; M4 downstream 𝒥†/∂_{t,s} (outside `flowerest1`) | |

**No FAIL** among the proved lemmas. Refutation attempts that did not succeed:
- multi-tree regular couples breaking the "common scale";
- a stem exit through u₂₃;
- frontier-crossing double counting at lone ports;
- unequal-layer weight mismatch in the LF cancellation;
- the Gevrey-4 degradation in 8.1;
- hidden L^{Cn} or C₂^n factors in the proved lemmas — none found: every base is C₀-, χ- or P-type, and the only L-powers are (C_dL)^{4d} per exceptional variable (7.1) and gains (9.1).

STATUS: REFEREED — 0 FAIL; 7 PASS AFTER FIX (3.2, 4.1, 5.1, 7.1, 8.1, 9.2, 9.3; none weakens a statement; 4.1 is the only proof-level fix); 14 PASS (of 21 lemmas) + Prop 10.3 PASS as conditional; OPEN list insufficient: add M1 (aggregate 10.3/10.4) and M2 (filtered LG ladders); OPEN 7.5 needs restatement.
