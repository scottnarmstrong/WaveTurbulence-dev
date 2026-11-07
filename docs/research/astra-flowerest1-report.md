# Independent assessment of `flowerest1`

## 1. Verdict, confidence, and scope

**Verdict: (C), with moderate confidence (approximately 75% in the assessment).**

The intended uncut flower estimate is credibly a bounded-mark modification of the existing proof, and the skeleton, Dirac, and exceptional-vine objections do not by themselves establish a serious mathematical gap. The printed cutoff argument is appreciably less complete: one must justify a weighted coherent summation and retain the unselected stem resonance cutoffs through the estimates. There is substantial machinery for these tasks in the three papers, including strong answers to objections based merely on the cutoffs being at internal momenta. I have not established either that the entire weighted bridge is routine or that its completion requires a genuinely new idea, so my referee recommendation would be to request a supplement, not reject the proposition as false. The project's inability to formalize the proposition establishes neither (A) nor (B), and the sources support a substantially narrower criticism than “seven adjustments, seven new mathematical gaps.”

**What this verdict does and does not settle.** I find concrete missing justifications in the printed argument, but do not have a counterexample to `flowerest1`. In particular, I do **not** certify the strong alternative (B) in the brief: that completing these justifications requires genuine new mathematics rather than expert technical work. Nor do I certify (A), because the weighted compatibility lemma specified below has not been proved in this audit. This distinction is essential: absence of a written argument, failure to find an argument, and a demonstrated obstruction to a routine argument are three different findings. The percentage above is not a probability that the theorem is true.

The verdict and classifications were fixed in `SOURCE-VERDICT.md` before opening any project report. Sections 2–3 below were also written before that opening. Sections 4–5 are the subsequent comparison.

**Scope and frozen inputs.** This is a focused, source-level audit of the transfer from `layergarden` to `flowerest1`, concentrating on \(1/2<\gamma<1\). It is not a fresh proof of all the number-theoretic and combinatorial results in Sections 4–11, and it does not inspect Lean implementation files. All references `T`, `21`, and `23` below are to the following frozen-v1 local files, respectively (SHA-256, 2026-11-07):

| Source | File | SHA-256 |
|---|---|---|
| T | `/home/scott/wave-turbulence/paper/source/WKE-Longer_times_Final_arXiv.tex` | `493eef6b7dec448bc5f9f1c3974c0cad7a85eca9bc428f5b35e968aad76727cb` |
| 21 | `/home/scott/wave-turbulence/references/src-2104.11204/Inventiones-Final_Version.tex` | `50d0e236a2df0cfd2b98bace6f0256043ee88fc05079ee44c3524ca9482fe402` |
| 23 | `/home/scott/wave-turbulence/references/src-2301.07063/Revision_Submit.tex` | `c7e47dfabf5a4cca6e3ad0399fc377f2809c12f58e1563640407fe0992335475` |

Bibliographic identities were checked against the primary arXiv records: [TARGET v2](https://arxiv.org/abs/2311.10082v2), [DH21](https://arxiv.org/abs/2104.11204), and [DH23](https://arxiv.org/abs/2301.07063). The mathematical evidence here is the local TeX, not the abstracts or a later replacement version.

The permission envelope was read-only everywhere except this scratch directory; no Lean, Lake, or repository-changing commands were used. I used the manuscript-audit protocol at focused-audit depth, with a separate adversarial reread of the candidate objections. This was a single-assessor audit, **not an independently delegated second review**; surviving concerns below therefore have the protocol status `UNREFUTED-TENTATIVE` wherever they depend on a global missing-lemma judgment. The elementary identities and counterexamples to particular shortcuts are directly checkable and should not be confused with a counterexample to the proposition.

**Two literal-source qualifications.** T671 and T712 use \((\delta/(2L^{d-\gamma}))^n\), whereas T2264–2265 print \((\delta/(2L^{d-1}))^n\). These differ by \(L^{(1-\gamma)n}\), which is not an \(L^{O(P)}\) loss uniformly in the allowed order. Moreover, with lower-layer insertions, the moment expansion at T2288 does not even have the displayed uniform prefactor if one follows both definitions literally: top-layer vertices and inserted vertices have different normalizations. This is a concrete normalization inconsistency, apparently inherited from the \(\gamma=1\) formulas in the earlier papers; the transfer discussion below concerns the intended normalization \(d-\gamma\), and is not a proof that the literal wrong-prefactor kernels satisfy the estimate. Also, the order-zero flower has no parent, so the identity term in the parametrix needs a separate convention; a delta kernel on \(t=s\) must not be treated as a pointwise function there. Neither observation supplies a counterexample to the intended flower estimate on \(p<s<t<p+1\).

## 2. The seven adjustments

The classifications separate a local calculation from the global assertion it is supposed to support. For the full weighted transfer, I cannot honestly distinguish (ii) from the stronger (iii) defined in the brief: a missing written justification is established, but nonroutine mathematical difficulty is not. The frozen source-only note called this “(iii), qualified”; the table below spells out that qualification as **(ii)/(iii) unresolved**, rather than redefining the user’s categories. This clarification does not change the frozen C verdict.

| Adjustment | Assessment |
|---|---|
| (1), T2294 | **(ii)** for external decay and the internal-momentum tail inequality; full weighted conclusion needs the compatibility argument in §3. |
| (2), T2295 | **(ii)**; fixing a resonance is only one part of the Dirac argument. |
| (3), T2296 | **(ii)**; uniform translated local estimates justify it, not the literal weighted norm of a translated delta. |
| (4), T2297 | **(ii)** for truncation and exceptional vines in the unweighted problem; do not invoke `subpro` unchanged after withholding splicing. |
| (5), T2298 | **(i)** once the marked-garden conventions are supplied. |
| (6), T2299 | **(ii)/(iii) unresolved** for the full weighted estimate; **(ii)** for the integration and the local multiplier steps written below. |
| (7), T2300 | **(ii)**; the separation estimate uses the original frontier, and proves invariance rather than the required analytic estimates. |

### Preliminary completion: flowers, components, and the skeleton

There is a particularly simple way to avoid inventing a new theory of skeletons for open gardens. To every flower \(f_j\), attach an **additional trivial tree** consisting of a root \(c_j\) of sign \(-\zeta_{f_j}\), and pair \(f_j\) with \(c_j\). Set its momentum to \(k'\) and its layer to \(p\). There are now \(4P\) trees, no new branching nodes, and all leaves are paired. The original moment expansion has balanced flower signs because its factors occur with their conjugates. The cap construction therefore gives an ordinary garden with a legitimate balanced signature.

Keep the cap pairs marked and give them the fixed-momentum input in place of an \(F_p\) factor. At the level of the original decoration sum this is an exact encoding, not an inequality or an assumption of independence. There is also no added molecular bond between branching nodes: the cap is a trivial tree. Its effect is an additional external momentum at the flower's parent, precisely of the kind already allowed by T1314–1321.

Apply the **ordinary** skeleton theorem. Contrary to the blanket premise that the skeleton requires irreducibility, T870 explicitly says “for any garden.” Irreducibility is required in the later connected counting statement T1304 and in the stated domain of the canonical LF-twist definition T1466, not in this skeleton theorem. Decompose the capped garden into components using T637. Each component has balanced roots, and there are at most \(2P\) components. Nontrivial components are canonical proper gardens or canonical couples: in the construction at T2261, lower-layer irreducible blocks cannot straddle two components. Alternatively, use `canonequiv`: any new completely paired sub-couple that includes a cap must include its flower, hence its other root lies on the layer-\(p\) stem; the required maximum-layer inequality is automatic. For sub-couples containing no cap it is the original canonical condition.

Use componentwise reductions, retaining the cap marks throughout collapsing and reinsertion. A mark swallowed by a regular object belongs to that regular object; it has not disappeared. The number of ways of marking \(O(P)\) locations is at most \((C(n+P))^{CP}\), and the component partition costs a constant depending on \(P\). These are harmless against the spare exponential decay in order, since \(P\) is fixed before \(\delta\). One may discard the componentwise negative powers associated with width; the flower estimate permits a positive \(L^{O(P)}\) loss. This resolves the open-leaf/irreducibility objection at the structural level. It does **not** permit applying an unmarked analytic estimate to a marked regular object without modification.

### (1) External decay and the internal \(M_1\) tail

Write \(B_j\) for the non-flower leaves of the **initial** layer-\(p\) tree, and \(D(v)\) for the final leaves descended from \(v\in B_j\) after insertion. Momentum conservation T641 gives

\[
 k-\zeta k'=\sum_{\ell\in\mathcal L_j\setminus\{f_j\}}
    \epsilon_\ell k_\ell,
 \qquad
 k_v=\sum_{\ell\in D(v)}\epsilon_{v\ell}k_\ell,
 \quad \epsilon_\ell,\epsilon_{v\ell}\in\{\pm1\}.
\]

No descendant in the second sum is a flower. Let \(m=3n+2P+1\), a generous upper bound for the number of leaves. Then

\[
 \langle k-\zeta k'\rangle\le C m
       \max_{\ell\in\mathcal L_j\setminus\{f_j\}}\langle k_\ell\rangle,
 \qquad |k_v|\le |D(v)|\max_{\ell\in D(v)}|k_\ell|.
\]

For each of the \(2P\) trees allocate \(2\Lambda_{p+1}\) powers to the first inequality. A paired input can be charged by at most its two endpoints, so at most \(4\Lambda_{p+1}\) powers are charged to any one \(F_q\). This gives exactly \(\langle k-\zeta k'\rangle^{-4\Lambda_{p+1}P}\), with a polynomial-in-\(n\) loss depending on \(P\). This is the leaf device at T2065, with the flower excluded.

If \(M_1>L\), the cutoff implies that each initial tree has some \(v\in B_j\) with \(|k_v|\gtrsim M_1\), hence some final non-flower leaf with \(\langle k_\ell\rangle\gtrsim M_1/(Cm)\). Charge \(40d\) powers for each tree. This gives \(M_1^{-80dP}\), with at most \(80d\) further powers charged to any one paired input. Combined with the external weight and the \(40d\) reserve for the analytic input norms, the charge is at most

\[
 4\Lambda_{p+1}+120d < \Lambda_p
\]

in the paper's parameter range, since \(\Lambda_p=40d\Lambda_{p+1}\) and \(\Lambda_{p+1}\ge40d\) (T611). Summing the possible choices contributes another polynomial in \(n\) for fixed \(P\), absorbable into an exponential in \(n\). One can implement this with smooth partitions or summable unit-ball localizations; a discontinuous “largest leaf” selector is unnecessary.

For \(M_1=L\), there is no large-momentum lower bound, so this tail argument does not apply. One instead spends \(L^{80dP}\) of the large allowed polynomial loss. There is ample numerical room in \(L^{(100d)^3P}\).

**Limit of this completion.** These inequalities prove where the powers come from and why an internal cutoff does not defeat the tail estimate. They do not prove that arbitrarily cutting an oscillatory sum preserves its estimate. The same localizations/weights must be compatible with the coherent LF summation, as discussed in §3. It would be wrong to promote the above elementary inequality alone to a proof of the full cutoff proposition.

### (2) Dirac factors

For \(v=f^{\rm pr}\), perform the Dirac integration exactly. The incident inequalities become bounds such as \(t_{v^{\rm pr}}>s\) and \(t_w<s\) for branching children \(w\) of \(v\); the factor is \(e^{i\pi\zeta_v\delta L^{2\gamma}\Omega_v s}\). Fixing \(\Omega_v\) makes this a constant of modulus one at fixed \(s\), but does **not** restore the lost time integration or remove its inequalities.

The right analytic precedent is 21 L2684–2694. In a regular chain the linked frequencies are \(\beta_a=\pm\alpha_j\). Pinning one time removes integrability in at most the corresponding linked frequency, while the integral in the remaining frequencies has the same chain structure (21 L2688–2690). For a residual molecule it removes one time-integration denominator (21 L2692). Thus the replacement is a mixed norm, schematically

\[
 L^1_{\alpha_1,\ldots,\alpha_m}
 \longrightarrow
 L^\infty_{\alpha_j}L^1_{\alpha_1,\ldots,\widehat{\alpha_j},\ldots,\alpha_m},
\]

with only boundedly many exceptional frequencies for each pinned node. It is not the assertion that the original \(L^1\) estimate remains unchanged.

For the layered application, retain the pinned node as a mark. If it is on a regular chain, split the chain at that node and, if necessary, its linked partner. The remaining pieces retain their original unit-interval constraints; pinning a time in layer \(p\) gives an endpoint in that interval. Any lost link/incoherency gain involves only the marked link, so it costs only a fixed power of \(L\). Outside regular objects, keep it out of ladder/vine elimination and use the missing-denominator argument. This is the same bounded-defect operation as in 21, with the layer labels retained; it does not require treating every stem node exceptionally.

Finally localize momenta. Four incident momenta in fixed unit balls have \(O(L^{4d})\) possible tuples, uniformly in the centers. If only the terminal leaves were localized first, internal momenta lie in balls of radius \(O(n)\); the corresponding count has an extra \(n^{O(d)}\), absorbable using \(n\le(\log L)^{C_2}\), or one can use the unit-ball refinement T1959. The possible resonance values therefore have polynomial cardinality even if their magnitudes are arbitrarily large. Sum the exceptional frequency classes or fix the incident tuples, paying \(L^{O(d)}\) per mark. With \(2P\) pins the loss is \(L^{O(dP)}\).

This supplies the missing logic behind T2295. The claim that one can simply erase the oscillation and reuse the original estimate is not correct; DH21 supplies the more careful argument. No counterexample to the pinned estimate follows from that defective shortcut.

### (3) Arbitrary \(k,k'\)

The literal norm example at T2295 needs care. If \(b_{k'}(x)=\psi(L(x-k'))\) equals \(\mathbf1_{x=k'}\) on the lattice, its **unweighted** derivative norm is \(O(L^{40d})\). Its \(\mathfrak S^{40d,40d}\) norm as defined at T585 is at least \(\langle k'\rangle^{40d}\), so it is not uniformly bounded by a power of \(L\) for arbitrary \(k'\).

The completion is to treat the marked input as a fixed external momentum, localize all other momenta, and use the estimates uniform in localization centers. T958–976 states precisely this uniformity for the basic exponential sums; T1617 states it for `sumint`; T1985 states it for the ladder bound. The flower carries no required decay in its absolute momentum. The missing decay is replaced by the external difference weight in (1). The finite-number-of-values argument in (2) is also uniform in centers, not in the diameter of a frequency interval around zero.

One must not use “translation invariance” as a substitute for checking the ladder Fourier estimate. DH23 actually discusses this issue at L2013–2018. TARGET incorporates arbitrary centers through the relations T2009–2013 and the bounded-rank linear-combination lemma; these are the appropriate statements to use. This is a local-norm repair, not an assumption that shifting all the input profiles leaves their weighted Schwartz norms unchanged.

### (4) Special nodes, truncations, and withheld splicing

The truncation conditions depend on the numbers of layer-\(p\) branching nodes in the indicated rooted subtrees, not on all nodes in lower-layer insertions (T2273, T2288–2290). A twist whose realization avoids the roots and the specified child/sibling boundary nodes operates entirely inside one of these subtrees, or outside it. LF replacement preserves its total number of layer-\(p\) nodes by T1476. Thus it preserves the relevant inequalities. The mark must be retained on the containing regular object if it has been collapsed; checking only whether the original node survives as a skeleton vertex would be insufficient. DH23 L2012 explicitly makes this convention for flowers swallowed by a regular couple.

There are only \(O(P)\) exceptional vine **ingredients in the selected disjoint vine-chain decomposition**. The bounded-degree and disjoint-interior properties give this bound; it is not a claim about all overlapping vine subgraphs one could enumerate.

There is indeed a mistake in a naive reuse of Stage 2: leave an ordinary SG (CL) ingredient unspliced, with no hinge and no enclosing exceptional object, and `subpro`(4), T2045, no longer follows. This is a counterexample to that proposed invocation of `subpro`, not a counterexample to the flower estimate.

A routine completion is to eliminate the exceptional pieces separately before calling the ordinary counting argument. Split their ladders at marked nodes and hinge endpoints, apply `ladderl1new` to the resulting unmarked ladders, and treat their bounded remaining cores trivially. A vine has at most three ladder portions and a bounded number of remaining atoms (T1519); its length does not enter the polynomial loss. Freeze the boundary momenta and retain the finitely many boundary times as external parameters. By Fubini, integrate the rest of the diagram with those times pinned before taking its absolute value; use the bounded-pin modification in (2) for that remaining diagram, and only then integrate the boundary times. This avoids replacing a globally oscillatory time integral by the integral of its absolute value. The exceptional ladder bound is uniform in those parameters, as required by T1985–1991. Removing \(O(P)\) such pieces creates only \(O(P)\) additional boundary incidences and components. Retain these as exceptional boundary data; when a garden representation is wanted, replace a severed subtree by a leaf with a trivial cap, and make detached retained subtrees additional roots. Thus the effective width increases only by \(O(P)\).

On the remaining unmarked pieces use the original maximal-vine decomposition and count. Any obstruction to the original `subpro` alternatives touching a removed piece is charged to its boundary; away from these boundaries the original classification is unchanged. The reconstruction count acquires \((n+1)^{CP}\) possible positions for the exceptional boundaries and an effective-width factorial depending only on \(P\). These costs are absorbed exactly as in the ordinary rigidity count T2239–2253. The positive \(L^{O(dP)}\) costs can be retained rather than claiming the original connected width gain.

The literal number \(L^{20d}\) per vine in T2297 is not established by the stated ladder bound: that bound already has \(L^{20d}\) per ladder, before the core cost. Replacing it by \(L^{Cd}\) for an absolute constant is harmless for the final enormous exponent, but should be done honestly. The structural repair is an additional boundary bookkeeping lemma, not evidence of a new dispersive phenomenon.

### (5) Stem layers

For the representative II-a/II-b operation, if the flower is in a free subtree carried by \(u_2\), the original stem includes \(u_2\), so its skeleton layer is \(p\). The admissibility condition for LF twisting is

\[
 \mathsf L_{u_2}\le\min(\mathsf L_{u_3},\mathsf L_{u_4})\le p.
\]

Consequently all three layers are \(p\). A regular tree inserted on the new stem has root-side layer at most \(p\) and lone-leaf layer \(p\), so monotonicity forces every node on its root-to-lone-leaf path to have layer \(p\). This proves the asserted preservation in both directions. The other unit-twist shapes have the same local argument; unaffected free subtrees retain their old stems. No equality of momenta or weighted estimate is being asserted here. T1463 correctly identifies the skeleton layer with the lone-leaf layer, which is essential to this argument.

### (6) The \(M_2\) gain

Separate the elementary operation from its proposed global consequence. On a piece of the time domain, after all other times are fixed, a selected stem time \(u\ne t_{f^{\rm pr}}\) ranges between

\[
 a=\max(\text{child times},p),\qquad
 b=\min(\text{parent time},p+1,t).
\]

For \(a<b\) and \(\omega=\pi\zeta_v\delta L^{2\gamma}\Omega_v\ne0\),

\[
 \int_a^b e^{i\omega u}\,du
   =\frac{e^{i\omega b}-e^{i\omega a}}{i\omega}.
\]

Partitioning according to the maximizing/minimizing endpoints introduces only a bounded number of terms at that vertex. If \(|\Omega_v|\asymp M_2>L\), this extracts \((\delta L^{2\gamma}M_2)^{-1}\). Freeze that resonance or its incident momenta; the new endpoint phases are fixed linear modulations of adjacent times, and the new constraints are endpoint-order inequalities. There are only \(O(P)\) selected vertices, so their exceptional treatment can cost \(L^{O(dP)}\). At \(M_2=L\), again there is no lower bound on the maximum resonance, and the requested factor is paid from the polynomial allowance.

**What is still missing from this calculation:** the decoration-dependent upper cutoffs at all the *other* stem nodes remain in every boundary term. They cannot be deleted inside an oscillatory decoration sum merely because their absolute values are at most one. There can be \(O(n)\) of them; fixing every affected momentum or resonance costs \(L^{O(n)}\), which the statement does not allow.

The strongest attempted refutation of this concern is the spectral approach in §3 below, not an argument that DH21 has no such cutoffs. DH21 Corollary 11.3 (L2699–2704) expressly allows “one (or more)” resonance cutoffs, and its endgame L2731–2743 uses maximum-resonance localization. DH23 L2021 explicitly invokes an analogous corollary. These are substantial precedents. They do not explicitly establish the needed layered estimate with internal frontier weights and the full uniform loss budget. A proof of that transfer would resolve the concern; this audit does not supply it and does not prove that it is nonroutine.

### (7) Small-gap twists and the high external momentum

Let \(b\le C N_{p+1}\) be the number of initial non-flower leaves of one tree, each with momentum \(O(M_1)\). For an initial node off the stem, conservation gives \(|k_v|\le CbM_1\). Along the stem, conservation gives \(k_v=\pm k+e_v\), with \(|e_v|\le CbM_1\); the sign matters when the stem changes sign. Thus

\[
 |k_v-k_w|\ge |k|-CbM_1\ge |k|/2
\]

if \(v\) is a stem node and \(w\) is an off-stem node in the top tree, for sufficiently large \(L\), using \(|k|\ge M_1^{10}\), \(M_1\ge L\), and the polylogarithmic bound on order.

This must not be asserted for *every descendant* in a lower-layer insertion: its internal momenta can be large and cancel. But in the application at T2300 one of \(u_{21},u_{22}\) is assumed to be on the stem. Its parent \(u_2\) is then on the stem in layer \(p\); the other child is either a top-tree node or the root of a lower-layer tree attached at the original frontier. In either case its momentum has the stated bound from the original cutoff. That is all the separation argument needs.

Since the SG gap is \(|k_{u_{21}}-k_{u_{22}}|\le L^{-\gamma+\eta}\le1\), exactly one of these children cannot carry the flower. Therefore a flower under \(u_1\) must lie under \(u_{11}\). The entire interior realization where twisting and coherent replacements occur is then off the stem. Its boundary stem momenta are fixed by the ordinary twist correspondence; its regular replacements also leave the root-to-lone-leaf momentum unchanged. Hence the original stem resonances and their cutoff values are unchanged. This validates the invariance assertion, but invariance is only a prerequisite for the weighted analytic argument in (6).

## 3. The cutoffs, in detail

### 3.1 A concrete useful cutoff class

“Smooth cutoff” should mean a fixed family with controlled seminorms, not an arbitrary bounded smooth function allowed to oscillate at a scale depending on \(L\). One standard implementation is

\[
 A_{j,M}=\prod_{v\in B_j}\chi(k_v/M),\qquad
 H_{j,M}=A_{j,M}-A_{j,M/2},
\]

where \(\chi\) is a fixed real even smooth low-pass function. The shell is \(H_{j,M}\) for \(M>L\), and the bottom piece is \(A_{j,L}\). Expanding the product of shell differences for \(2P\) trees costs at most \(2^{2P}\), not \(2^n\) times an uncontrolled constant. For resonances, use the corresponding products over \(v\in\mathcal S_j\). Smooth partitions selecting a large resonance have at most polynomial-in-\(n\) cost for fixed \(P\). No conclusion here is intended for cutoffs with uncontrolled derivatives.

The identity of \(B_j\) matters. After T2261, its nodes may be branching nodes in a vine or within a non-coherent regular object. Treating all of them as final paired leaves is incorrect. The correct weight is the product over the original frontier, carried through the replacements.

### 3.2 Internal momentum weights do fit the Fourier machinery

Write \(\mathcal A\) for the algebra of Fourier transforms of finite measures, with norm the total variation of the representing measure. If \(\chi_M(z)=\chi(z/M)\), then

\[
 \chi_M(Ax+b)=\int \widehat\chi(\xi)
       e^{2\pi i\xi\cdot b/M}
       e^{2\pi i(A^T\xi/M)\cdot x}\,d\xi,
 \qquad
 \|\chi_M(A\cdot+b)\|_{\mathcal A}\le\|\widehat\chi\|_1.
\]

This holds for rectangular or non-invertible \(A\); use a finite measure rather than claiming the pullback always has an integrable Fourier *density*. Products multiply the bounds. Thus a product of \(O(n)\) internal-momentum cutoffs costs \(C^n\), independent of their positions and of the magnitudes of the affine coefficients. Upon multiplication by the localized original amplitude, convolution with this finite measure gives the required Fourier \(L^1\) density.

This directly extends the amplitude step of `proplayer1`, T991–1017: multiply \(W\) by the cutoff factors, Fourier-expand, and use the estimates already uniform in all linear modulation parameters. A fixed number of output derivatives adds at worst a polynomial in \(n\), because each internal momentum is an integer linear combination of leaf momenta. It also directly extends the amplitude step of `sumint`, T1621–1625. There, a cutoff on a skeleton branching momentum can simply multiply the relevant \(\mathcal L_j^i(\ell_j^i)\); a cutoff at a skeleton leaf momentum can multiply \(\mathcal K_j^i(k_j^i)\). Their differentiability classes allow this. The same Fourier-measure argument handles products depending on several internal linear momenta.

**Refuted objection:** “It is an internal cutoff, so it cannot be absorbed in `sumint` or in the non-coherent regular-object estimate.” That is false for the natural smooth cutoff class. No new number theory is needed for this absorption.

### 3.3 A noninvariant cutoff does not automatically destroy vine cancellation

At an elementary twist, T1452 exchanges \(k_{u_2}\) and \(k_{u_{23}}\). With \(x-y=\pm r\),

\[
 \chi(x/M)-\chi(y/M)
 =\frac1M\int_0^1 r\cdot\nabla\chi((y+\theta r)/M)\,d\theta.
\]

For a product of cutoffs, telescope the product first. The difference is \(|r|\) times an amplitude whose Fourier-measure norm is bounded by \(C^n\) times a polynomial in the number of factors, since \(M\ge1\). This is exactly the type of extra factor admitted by `sumint` case (b), T1611, and used at T1902. Thus **exact invariance of every momentum cutoff is stronger than necessary**. A small-gap commutator error is already part of the paper's mechanism.

This observation does not by itself finish the argument. LF twisting includes replacement of the coherent regular couple/tree pair by *all* choices of fixed total order and layer-\(p\) order (T1472–1476), not merely a switch of two momentum variables in one fixed graph. The decisive leading cancellation at T1904–1907 uses the reality identity T1121–1123. Its proof T1263–1285 extracts common factors indexed by an unordered collection of extended tuples and then sums over all allocations of those tuples to three time chains. A general internal weight need not be such a common factor.

Here is the precise missing check for the actual cutoff family. Attach the original-tree label and the frontier cutoff to every node that crosses from layer \(p\) to lower layers, and attach the same cutoff to each terminal layer-\(p\) leaf. Show that, under the coherent-object expansion and the tuple permutations in T1267–1285, these decorations either give a common real factor for each fixed unordered collection, or yield commutator errors controlled in the same Fourier norms with a factor \(|r|\). At \(q=q'=p\), there is a strong simplification: the coherent object lies wholly in layer \(p\), and the common real leaf cutoff is just absorbed into \(F_p\), with one factor per occurrence. When \(q'<p=q\), T1235–1244 decomposes the object into single-layer pieces and a trunk of constant momentum; the frontier cutoffs on that trunk suggest the same conclusion. A (CL) realization lies within a single original tree (T1349), so its local weights do not have arbitrary incompatible tree labels.

These facts make a routine completion plausible. They are also why an arbitrary weighted-shuffle counterexample would not refute the **specific** cutoff in the proposition. But a proof must enumerate the frontier occurrences, including multiplicities when a pair is replaced and the dependence of the shell localization on the original tree. I have not completed that weighted identity here. Nor have I found an admissible configuration where it fails. The reported concern is the absence of this bridge, not a claim that the basic Fourier multiplier bounds fail.

### 3.4 Obtaining the \(M_1\) gain without spoiling the grouping

The numerical tail extraction was proved in (1). To incorporate it in the cancellation argument, one useful implementation is

\[
 A_{j,M}-A_{j,M/2}=\int_{M/2}^M\partial_R A_{j,R}\,dR.
\]

Each derivative term marks one original frontier momentum with size comparable to \(R\). There are only \(2P\) such marks after choosing one term for each tree. Propagate its large momentum to a final non-flower leaf using the inequality in (1), and charge the necessary polynomial weight there. Protect these extra marks in the reductions just as one protects the flowers; the number of exceptional locations is still \(O(P)\), although their depths can be arbitrarily large. This is a more credible route than demanding that a largest-leaf selector be invariant under every twist.

What still has to be proved for a complete argument is that the low-pass weighted coherent identity in §3.3 and the marked regular-object estimates hold together, with total cost \(C_P^nL^{C_dP}\), not \(L^{C_dn}\). A depth-dependent cost for every ancestor of a marked node would not suffice. The regular-chain decomposition is the natural way to avoid it. This is a finite technical task with an explicit endpoint, not a request to rediscover the proof of `layergarden`.

### 3.5 Upper \(M_2\) cutoffs: what the citations do provide

The crude objection based on derivatives

\[
 \partial_{k_v}\chi(\Omega_v/M_2)
 =M_2^{-1}\chi'(\Omega_v/M_2)\partial_{k_v}\Omega_v
\]

is not decisive. Although \(\partial\Omega_v\) can contain arbitrarily large \(k\), these cutoffs can be treated in **resonance variables**, rather than in momentum-space Schwartz norms.

DH23 L955–968 gives the spectral representation of a regular object with linked frequencies \(\alpha_v=\delta L^{2\gamma}\Omega_v\). In the integrable spectral variables, the cutoff is \(\chi(\alpha_v/S)\) with

\[
 S=\delta L^{2\gamma}M_2\gg1.
\]

Multiplication by such cutoffs preserves the weighted \(L^1\) bounds and their fixed-order derivative versions by the product rule; derivatives cost \(S^{-1}\), not \(|k|/M_2\). DH23 L984–1007 gives the corresponding sum-to-integral framework. For an extracted denominator variable, one must also handle a smoothly truncated \(\chi_\infty(\alpha)/\alpha\) kernel; even cutoffs preserve the elementary principal-value symmetry, and this is the appropriate place to check the estimate. Merely calling this a bounded momentum multiplier would be the wrong proof.

Furthermore, with the capped-garden construction, an embedded regular **couple** that contains a stem node must also contain the flower and its trivial cap; otherwise its leaves cannot be internally paired. Such an object is a paired tree viewed as a couple with a trivial tree. An embedded regular **tree** that meets the stem has its stem segment on the root-to-lone-leaf chain. These chain nodes all have layer \(p\); non-coherent side objects can be estimated separately. This gives a promising reduction of the stem filters to the one-layer chain spectral argument, with the lower-layer side objects appearing as time-modulated inputs.

On the residual molecule, after the oscillatory/time reductions have reached the absolute counting expression T2090–2097, upper cutoffs can indeed be discarded or retained as restrictions. At that stage they only decrease an absolute sum. They cannot be discarded earlier, inside the lattice exponential sum.

The remaining obligation is to combine these observations into a uniform **marked, layered, spectrally truncated chain estimate**, including the selected high-resonance node, the pinned flower parent, endpoint terms, and the side-object norms. DH21 provides the unlayered prototype, not a verbatim statement of this combined estimate. This is the most plausible route to finishing (6); it makes a claim of a fundamentally new obstruction premature.

### 3.6 Findings and adversarial checks

| Candidate objection | Best attempted refutation | Disposition |
|---|---|---|
| Flowers have no ordinary skeleton | Add trivial caps; T870 applies to any garden; split components | Refuted as a serious obstruction |
| Fixing \(\Omega\) alone proves the Dirac estimate | DH21 mixed norms, linked-frequency exceptions, bounded marked nodes | Shortcut invalid; routine completion available |
| Translated delta has uniformly bounded weighted Schwartz norm | Norm T585 includes absolute momentum weight | Literal norm claim invalid; local marked-input method repairs it |
| Special vines can be left in the original `subpro` input unchanged | Explicit withheld SG (CL) ingredient violates the rationale of (4) | Invocation invalid; remove exceptional pieces and keep boundary budget |
| Internal \(M_1\) cutoff cannot fit \(W\) or `sumint` | Fourier-measure algebra and uniform modulations | Refuted |
| Any cutoff mismatch destroys twist cancellation | Telescoping/mean-value formula gives \(|r|\), already covered by T1611/T1902 | Refuted for the simple momentum exchange |
| Full LF weighted coherent sum is automatic | Single-layer simplification and constant trunk momentum are promising, but full frontier tracking has not been supplied | `UNREFUTED-TENTATIVE`: missing weighted bridge |
| DH21 never handles upper resonance cutoffs | Its Corollary 11.3 and endgame expressly do | Refuted |
| All upper \(M_2\) filters can be dropped before oscillatory estimates | No monotonicity for oscillatory sums; spectral route needed | Shortcut invalid; full layered spectral transfer remains `UNREFUTED-TENTATIVE` |
| A proof gap implies the proposition is false | No admissible counterexample found | Rejected |

**Expected repair effort, not a promise.** The cap/component and exceptional-boundary bookkeeping should be a short lemma and a few pages for someone familiar with the reduction. The Dirac modification has an existing detailed prototype. The weighted frontier identity and marked spectral-chain estimate are the tasks to settle first; I would budget a focused mathematical note, plausibly days to several weeks for an expert already conversant with these papers, before undertaking a large formalization campaign. No lower bound on the intellectual difficulty has been proved, and these estimates are not evidence that completion requires a new dispersive or number-theoretic technique.

## 4. Comparison with the project's claims

I now compare the preceding, frozen source-only assessment with `FLOWEREST1.md`, E29–E39, and §1 of `PAPER-GAPS.md`. I have not imported their claims of Lean verification into my mathematical verdict; no such checks were rerun.

### 4.1 Where the project is right

The project correctly distinguishes original top-layer leaves from final input leaves. It correctly says that a cutoff inside a spliced region must be included **before** estimating that region, and that a bounded weight cannot simply be discarded from a complex sum. It correctly identifies the defect in calling the unchanged `subpro` after changing the splicing rule. Its product-partition correction E34 is a real correction of its own transcription, not a counterexample to the paper. Its warnings about cap/floor time faces and about preserving full coherent families are legitimate mathematical obligations.

The actual documents are more qualified than the broad assertion that the paper has substantial new gaps. E36–E38 are explicitly classified as **EXPOSITION** and describe mechanisms that should work. E39 is expressly **SUSPECTED**, not confirmed. `FLOWEREST1.md` acknowledges that exact-equality interfaces caused some of its difficulties. These qualifications should accompany any public account of the findings.

### 4.2 Where the claims are overstated or wrong

| Claim | Assessment |
|---|---|
| E29 / `FLOWEREST1` §3.1: the skeleton machinery requires irreducible gardens | Too broad. T870 states the skeleton theorem for **any garden**. Connected counting and the canonical twist interface have additional requirements; those are separate. |
| Pairing flowers “would not help” because the skeleton may become trivial | Overstated. A trivial skeleton means the marked contribution belongs to the regular-object case, which must be treated separately. It is not an obstruction to using the ordinary skeleton theorem. Trivial caps and component decomposition give another elementary encoding. |
| E29: the repair is “a new construction, not a routine fill” | The first half is a description; the second does not follow. Adding caps, retaining marks, and taking connected components is routine diagrammatic bookkeeping. The subsequent analytic estimates are the actual issue. |
| E30: fixing the resonance does not prove a trace estimate | Correct, but the comparison must include **21 L2684–2694**, not only Corollary 11.3. Those lines explicitly give the missing mixed-norm mechanism. The two-corolla test refutes an unchanged positive-time-volume representation, not this mechanism or the flower bound. |
| E31: a polynomial loss does not restore `subpro` | Correct as a logical statement. The intended completion removes/estimates the exceptional pieces and tracks their new boundaries; it does not assert that multiplying by a power of \(L\) repairs a false premise. The project's excision is one reasonable implementation, not the only one. |
| E33: extracting decay at an internal node is itself nonroutine | Not demonstrated. The conservation inequality and exponent allocation in §2(1) are elementary. Maintaining the grouped estimate while extracting that decay is the real obligation. The fact that their implementation required a new uniform-family identity is not evidence that every mathematical proof needs a new idea. |
| E36: differing cutoff values across a twist prove an obstruction | The revised document appropriately concedes the \(|r|\)-error route. The earlier exact-equality failure is an interface failure. The mean-value completion in §3.3 uses precisely an existing case of `sumint`. |
| E37–E38: new weighted estimates must be constructed | As formal declarations, yes. As new analytic ideas, no: the Fourier-measure calculation in §3.2 supplies the basic absorption. Calling these “two of the deepest estimates must be reproved” exaggerates the mathematical novelty unless the remaining coherent-family compatibility is exhibited. |
| E35/E39: DH21 is not a verbatim layered theorem | Correct. But DH21 really does contain the same cutoff placement and regular-chain prototype; it cannot be dismissed as a reference concerning only input-leaf weights. |
| `PAPER-GAPS` §1.7: cancellation survives “only if” the weight is identical across the class | False as a general necessity: controlled commutator errors are enough. The later refinements in the same report and in E36 correctly recognize this. |
| Formal code size, unsuccessful attempts, or two refuted internal interfaces establish nonroutine mathematical difficulty | They do not. These are evidence about this implementation and its architecture. |

E32 concerns the derivative use after the proposition rather than one of its seven adjustments. Its one-time root excision and allowance for wider connected components are sensible, and I agree that it is an exposition/assembly issue. The project's claims of completed formal proofs and its rebuild qualifications are outside this read-only source audit.

### 4.3 Post-comparison mathematical note: two useful simplifications

**The source-only verdict above remains C.** Reading the project prompted the following additional calculations. They make me more optimistic about routine completion and narrow the remaining concerns; they are recorded separately rather than silently changing the independent assessment.

**First, the coherent frontier weight is much more special than a general internal weight.** In a (CL) realization all relevant nodes lie in one original tree, say tree \(j\). Fix a low-pass term with scale \(M_j\). In a coherent regular object with upper layer \(q\) and lower layer \(q'\), T899–901 and T1235–1244 imply:

- A same-layer \(p\) side couple sees the cutoff at its actual leaves, so replace its paired profile by \(F_p\chi(\cdot/M_j)^2\).
- If \(q=p>q'\), a regular tree has exactly one trunk crossing from layer \(p\) to lower layers. Its momentum is the external momentum \(k\), so it contributes one additional factor \(\chi(k/M_j)\). A coherent couple with one parent at \(p\) and the other below \(p\) likewise has one such crossing on its upper trunk.
- If \(q<p\), there is no internal top-frontier cutoff. If \(q=q'=p\), all nodes of the coherent object are in layer \(p\), and the leaf-profile replacement accounts for the weight.

For the equal-upper-layer pair \((Q,T)\) in the leading cancellation T1883–1907, the product of trunk factors is therefore the common real scalar

\[
 \chi(k/M_j)^{2\mathbf1_{\{q=p>q'\}}}.
\]

The remaining modification is the same real profile replacement in every layer-\(p\) side object. It is invariant under the tuple rearrangement in T1267–1285. This supplies the crucial leading-reality check for these low-pass terms. In the unequal-upper-layer case, the number of top trunk entrances in the combined pair is still preserved when the two attachments are exchanged; the existing temporal-difference argument must be carried along as well. The shell partition is a finite linear combination of these low-pass terms. This supports the project's corrected skeleton reading, and shows why an arbitrary weighted-shuffle counterexample would be irrelevant here.

This calculation is a stronger local completion than the deliberately reserved statement in §3.3. It is **not** a completed bound for all marked extraction terms, nor a verification of the project's exact uniform-family interface. The latter additionally carries its artificial cuts, root-label sums, and quantitative budgets.

**Second, the region-top stem resonance has an affine form.** `PAPER-GAPS` §1.8(iii) and `CLOSURE` O5(c) describe a possible blocker involving a resonance cutoff at the top of a small-gap vine. In precisely the case protected by adjustment (7), the stem goes through the same-sign child \(u_{11}\). Write the root momentum as \(e=f+r\), where \(f=k_{u_{11}}\), and write the other two child momenta as \(a,a+r\), choosing their order according to signs. Then

\[
 \Omega_{u_1}
 =|f|^2-|a|^2+|a+r|^2-|f+r|^2
 =2r\cdot(a-f).
\]

The vine estimate fixes \(e,f,g,h\), hence fixes \(f\) and \(r\). Thus

\[
 \chi\!\left(\frac{\Omega_{u_1}}{M_2}\right)
 =\chi\!\left(\frac{2r\cdot(a-f)}{M_2}\right)
\]

is a smooth function of an **affine linear** internal momentum, with Fourier-measure mass bounded by \(\|\widehat\chi\|_1\), uniformly in \(f\), and derivative factors bounded by \(C|r|/M_2\). The internal child momentum \(a\) is itself affine in the variables of `sumint`. The output norm in the vine estimate has no spatial derivatives (T1749), so the large fixed \(f\) contributes only a unimodular factor in this Fourier representation. This is directly within the amplitude method of §3.2. It is not necessary to solve a general, center-uniform Fourier-measure problem for every indefinite quadratic form just to handle this particular top cutoff.

Accordingly, “no route as scoped” in O5(c) may accurately describe the project's chosen interface, but is not evidence that the paper's geometry has no route. Other stem cutoffs within regular chains still need the spectral argument in §3.5. This calculation does not identify all such weights with the affine vine-top case.

**Effect on my judgment:** more optimism about (A) for the intended statement, especially for the elementary weighted extensions; no change to the frozen C verdict, because the complete uniform marked-cutoff estimate has still not been checked end to end. I would give the authors or an expert a short list of explicit lemmas to supply, rather than label these observations proof of a nonroutine failure of the paper.

## 5. The project's approach

### 5.1 The four-input decomposition is mathematically reasonable

The latest decomposition in `CLOSURE` §1.2 and the final portion of `flower-top/HANDOFF.md` has these inputs:

| Input | Mathematical role | Judgment |
|---|---|---|
| `hStage1` | Ordinary Stage-1 estimate already on the `layergarden` path | Sensible reuse. |
| `hFam` | Uniform low-pass/tail family giving the \(M_1\) estimate and the uncut estimate by a limit | Sensible way to keep cancellation and avoid a decoration-dependent leaf choice. |
| `hCut2` | Positive resonance shells with the full \(M_2^{-P/9}\) gain | Natural separate analytic task. |
| `hCut2Zero` | Bottom resonance block, paid from the \(L\)-power budget | Routine but worth making explicit. |

Recovering the uncut clause by \(M\to\infty\) is a good simplification. For each fixed finite garden family, the decoration sum is absolutely summable using the input decay; bounded low-pass weights converge to one. Dominated convergence then gives the uncut estimate from a genuinely uniform family estimate. The handoff correctly distinguishes this limiting argument from proving the family estimate itself.

The decision to use garden excision, fixed external labels, and components is faithful to the paper's logic. It is more elaborate than the cap-only structural construction in §2, but it has a legitimate purpose: make pinned nodes pendant and protect truncation data so that more of the existing unmarked analytic library applies. It is not evidence that the team wandered into unrelated mathematics.

### 5.2 Where the implementation appears over-engineered

The difficulty is below the four-input theorem. `CLOSURE` §§1.3–1.5 and §2 records several incompatible descriptions of the same weights, repeatedly widened Stage-1 interfaces, and a consumer that requires local resonance weights while its producer accepts only global spatial presentations. It also records packet-level cycles and a root-label summation that diverged after artificial anchor labels were treated too freely. Those are substantial architecture problems. The affine calculation in §4.3 gives a concrete example where a more general interface problem was being treated as the mathematical problem.

The final handoff reports copying 120 modules, about 14.7k lines, to reconcile two incompatible environments, plus a 143-module assembly rebuild. Those figures measure integration and representation overhead, not the amount of new mathematics in `flowerest1`. The consistency objections in `CLOSURE` are sensible reasons not to certify the scratch build, but do not bear on whether the published mathematical argument is routine. I have not inspected the implementation, so I cannot quantify how much of the total project was unnecessary or endorse its claimed axiom status.

The uniform family in `hFam` is stronger than the final uncut statement; `CLOSURE` correctly says that its extra budget is used in the cutoff interpolation. Such strengthening can be appropriate. It should nevertheless be derived and tested on paper **before** its precise implementation becomes the obligatory route for every later estimate. Likewise, a fallback gain \(M_2^{-2P/25}\) does not supply \(M_2^{-P/9}\), and the handoff is right to keep that mismatch explicit.

### 5.3 A simpler mathematical plan consistent with the papers

I would first write and referee one short supplement with a common class of marked amplitudes, before restarting a large code campaign:

1. Use ordinary gardens with trivial caps and component decomposition; allow \(O(P)\) marked pins and exceptional boundaries. State a single quantitative rule for their total cost, independent of their depths and of order.
2. Use real low-pass products at the original layer frontier. Prove the coherent trunk/profile factorization in §4.3 and the Fourier-measure amplitude extension in §3.2. Keep the \(|r|\)-commutator case available instead of demanding exact equality everywhere.
3. Prove the large-frontier-momentum estimate with the conservation inequality in §2(1), inside that uniform family. Use a derivative/telescoping or polynomial-extraction identity that marks only \(O(P)\) inputs. Check its full decay and constant budget once.
4. Handle the positive \(M_2\) block by either the exact selected-time integration or the DH21 spectral-chain route. Keep unselected filters in resonance variables on regular stem chains, use the affine form at SG vine tops, and discard filters only after reaching absolute counting estimates. Include the bottom block explicitly.
5. Sum the order and reconstruction bounds, checking that every local loss is \(C_P^nL^{C_dP}\), with no hidden \(L^{cn}\), uncontrolled center dependence, or unweighted sum over anchor labels. Then freeze the smaller set of actual analytic interfaces and formalize it.

This plan uses the same broad mathematics as the project. Its simplification is to settle the special structure of the actual weights before building a general weighted framework. It does not assert that all the existing code should be discarded, or that the missing supplement is already proved here.

**Would my source-only completion have been a better plan?** As an initial mathematical scoping exercise, yes: it would have classified the skeleton and elementary Fourier-weight extensions as routine, isolated the full-family compatibility early, and demanded a single checked uniform-loss statement before extensive implementation. As a replacement completed proof, no: the audit deliberately does not claim to have finished the combined marked-cutoff estimate. The project deserves neither a declaration of mathematical success from its assembly theorem nor an automatic attribution of its difficulties to an error in the paper.

### Audit closeout

The requested sources and project documents have been read in the stipulated order; all seven adjustments are classified, with the local completions and the remaining proof obligations distinguished. No full counterexample is claimed. No Lean proof or build status has been independently verified. The fixed source-only verdict has not been revised after the comparison; the two subsequent mathematical observations are explicitly separated above.

Project-document hashes recorded at comparison:

- `FLOWEREST1.md`: `fc1df436d317801c6845400023b0978a18ff4624b1bbe7324d7b14204e1760e2`.
- `ERRATA-AND-DEVIATIONS.md`: `2d77a162e123c84f13f3e6d8f765271b50d63e97da95d809b89db083aa41a140`.
- `PAPER-GAPS.md`: `1dfdfacba942e03baf1ea00e5f94e2d99f4d80488a69ce840568fac0bf47f144`.
- `CLOSURE.md`: `4539f499ecc6f17ee57bbe72de7057646d1e3a6af21d258b352bfdc281ccd8b3`.
- `flower-top/HANDOFF.md`: `e7c825b25b2366241ad4b8d6398270e922f788a790a438042dee48f16b92e973`.

STATUS: DONE
