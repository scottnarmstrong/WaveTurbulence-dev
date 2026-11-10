# EV-C — independent verification of E2g, E39, E45

Verifier: EV-C (refute-first; I did not write these entries or their repairs). Date: 2026-11-10. Read-only; no builds.

**Sources** (sha256 checked against the pins in COMMON.md and the errata file):
- TARGET `WKE-Longer_times_Final_arXiv.tex`: `493eef6b7dec448b…` (2694 lines).
- DH21 `Inventiones-Final_Version.tex`: `50d0e236a2df0cfd…`.
- DH23 `Revision_Submit.tex`: `c7e47dfabf5a4cca…`.
- GIT20 `Kin8.tex`: `c02ccada9ba423c9…` (1271 lines).
- Entries: `git -C <repo> show origin/main:docs/ERRATA-AND-DEVIATIONS.md` (origin/main at
  `636c5a46`, 2026-11-10).

**Verdicts**

| Entry | Verdict | Main correction |
|---|---|---|
| E2g | CONFIRMED WITH CORRECTIONS | Class GAP → EXPOSITION (a half-page weighted replacement of one step, given below). The "Lemma 4.1 needs an unproved dispersive bound" sentence is unfair. The "only the blow-up criterion" scope is too narrow. The Lean status needs reconciling. |
| E39 | CONFIRMED WITH CORRECTIONS | Class GAP → EXPOSITION. "Fails" → "is not justified". The fill for unselected filters inside unprotected coherent stem trees is short (given below). The Lean status needs reconciling. |
| E45 | CONFIRMED WITH CORRECTIONS | GAP is right only through E30/E31; the points E45 adds are routine once those are repaired. Reword the title (the † kernel adds no pin), add a fairness note on DH21, and reconcile the Lean status. |

---

## E2g — GIT20 Remark 2.6; TARGET L2515

### 1. Pin

GIT20 L592–L594 (Remark 2.6; numbering checked: one counter per section, so Section 2 runs Thm 2.1, Thm 2.2, Prop 2.3,
Prop 2.4, Rem 2.5, Rem 2.6; the text is on L593):

> We are working in dimension $d=3$ mostly for the sake of concreteness. Similar theorems hold in any dimension
> $d\geq 2$, with the corresponding ranges of exponents $s>d-1$ for the $L^\infty_s$ local well-posedness theory, and
> $s>(d-2)/2$ for the $L^2_s$ local well-posedness theory.

GIT20 works in $\mathbb R^3$ throughout (L528: "initial-value problems in $\mathbb{R}^3\times[0,T]$"). Prop 2.4 (L579–L584)
is $d=3$, $s>1/2$. Section 4 has four numbered lemmas: Lemma 4.1 (`Lem1`, $\mathcal T_1$), Lemma 4.2 (`prop1`, $Q_2$),
Lemma 4.3 (`lem4`, technical), Lemma 4.4 (`prop2`, $Q_3$).

TARGET L2515 (Appendix C, after defining $Z_s$, $Z_{s,m}$):

> It is proved in \cite{GIT20}, see Lemmas 4.1--4.3 of \cite{GIT20} (also Remark 2.6 of \cite{GIT20}), that each
> $\mathcal K_j$ satisfies the trilinear estimate (schappend8) … It then follows that (wke) is locally well-posed in
> $Z_s$.

L2526 then uses (schappend8) "for $Z_{s,m}$ … which follows from the same proof" to get local well-posedness in
$Z_{s,m}$. That gives the common lifespan, Schwartz regularity, and the blow-up criterion (L2526–L2528).

### 2. What is claimed and used

TARGET needs (schappend8) for every $d\ge3$ and $s>d/2-1$. For $d=3$ this is GIT20 Prop 2.4 ($s>1/2$). For $d\ge4$ the
only source is Remark 2.6, whose threshold $s>(d-2)/2$ is the same as TARGET's. Remark 2.6 gives no argument.

### 3. Refutation attempts and checks

**(a) Does GIT20's $d=3$ proof transfer verbatim?** I rebuilt each step in dimension $d$.
- *Lemma 4.3(ii) (bil20).* The slab intersection has 2-D cross-section area $\varepsilon_1\varepsilon_2/|\sin\angle(v,w)|$.
  The remaining integral is $\int_{\mathbb R^{d-2}}\langle z+q\rangle^{-2s}\,dz$, which is uniformly bounded iff
  $2s>d-2$. So the $TT^*$ kernel bound
  $|K_s(y,y')|\lesssim |y|^{-1}|y'|^{-1}(|\hat y-\hat y'|^{-1}+|\hat y+\hat y'|^{-1})$ holds in every $d\ge3$.
  This transfers.
- *Lemma 4.2, the step before (bil7).* In dimension $d$, $dy=r^{d-1}dr\,d\theta$, so the radial integral is
  $\int_0^\infty g(r\theta)\langle r\theta+p\rangle^{-s}r^{d-2}dr$. Cauchy–Schwarz against
  $\tilde g(\theta)^2=\int|g(r\theta)|^2r^{d-1}dr$ leaves the weight
  $w_p(\theta)=\int_0^\infty\langle r\theta+p\rangle^{-2s}r^{d-3}\,dr$, and GIT20's argument needs $\sup_{p,\theta}w_p<\infty$.
  At $p=-R\theta$ the window $|r-R|<1$ alone gives $w\ge cR^{d-3}$, so the supremum is infinite for $d\ge4$.
  Numerically, with $s=(d-2)/2+0.05$, $w/R^{d-3}$ tends to a constant: 3.66, 3.00, 2.95 for $d=4$ and $R=10,10^2,10^3$;
  2.07, 1.94, 1.94 for $d=5$; 1.59, 1.54, 1.54 for $d=6$. **The entry is right: this step fails for $d\ge4$.**
- *Lemma 4.1 (ma13).* GIT20 does not prove the dispersive bound even for $d=3$: "this is a standard dispersive bound …
  can be proved by oscillatory integral estimates" (L957–L958). Its $d$-dimensional analogue is equally standard.
  Write $\langle p\rangle^{-2s}=\Gamma(s)^{-1}\int_0^\infty e^{-\lambda(1+|p|^2)}\lambda^{s-1}d\lambda$ and do the Gaussian
  integral. This gives $|K(y,t)|\lesssim\int_0^\infty\lambda^{s-1}e^{-\lambda}|\lambda+it|^{-d/2}d\lambda$, which is
  $\lesssim|t|^{s-d/2}$ for $|t|\le1$ (when $s<d/2$) and $\lesssim|t|^{-d/2}$ for $|t|\ge1$. That is (ma13) with
  $\delta=\min(s-d/2+1,\,d/2-1)/2>0$. Minkowski, the fractional Leibniz rule and $TT^*$ are dimension-free. **The
  entry's sentence "Lemma 4.1 would need a d-dimensional dispersive bound that is not proved" is true but misleading:**
  the $d=3$ bound is not proved in GIT20 either, and the $d$-dimensional one has a three-line proof.
- *Lemma 4.4 ($Q_3$).* Its $TT^*$ kernel uses offset slabs, which Lemma 4.3(ii) already allows, so it reduces to the
  same (bil7).

**(b) Is (bil7) itself true for $d\ge4$, and is the fix routine?** Yes to both, by a short argument of my own,
independent of the research note:
1. Keep the angular weight when applying Cauchy–Schwarz:
   $\text{LHS(bil7)}\le\iint|\theta-\theta'|^{-1}\,\tilde g(\theta)w_p(\theta)^{1/2}\,\tilde h(\theta')w_{p'}(\theta')^{1/2}d\theta d\theta'$.
2. Bound the weight uniformly in $p$. Let $\phi=\angle(\theta,-\hat p)$ and $R=|p|$. Then
   $\langle r\theta+p\rangle^2=1+(r-R\cos\phi)^2+R^2\sin^2\phi$ gives
   $w_p\lesssim1+R^{d-3}\langle R\phi\rangle^{1-2s}\mathbf 1_{\phi<\pi/2}$. Since $2s>d-2$, maximizing over $R$ gives
   $w_p(\theta)\lesssim1+|\theta+\hat p|^{3-d}$. Numerically, $\sup_R w_p\cdot\min(1,\phi^{d-3})\le 10.2$ for
   $d=4,5,6$ and $\phi\in[10^{-3},3.1]$; the constant is the tail value $1/(2s-d+2)$.
3. On $S^{n}$ with $n=d-1\ge3$, put $\beta=(d-3)/2=(n-2)/2$. Apply Hölder with $1/q=1/2+\beta/n+\epsilon$ on each side,
   then Young's inequality for the kernel $|\theta-\theta'|^{-1}\in L^{\sigma}$ with $1/\sigma=2/n-2\epsilon>1/n$. The
   exponents add up because $2(1/2+\beta/n)=2-2/n<2-1/n$, which leaves slack $1/n$. The $|\hat y+\hat y'|^{-1}$ half
   follows by $\theta'\mapsto-\theta'$. All constants are uniform in $p,p'$.

This is standard harmonic analysis, about half a page. **GIT20's (bil7) holds for all $d\ge3$; only the preceding step
must change, as the entry says.**

**(c) The $d=2$ remark.** I checked that the individual $L^\infty$ bound for $Q_2$ fails for $d=2$. At $p=0$,
$Q_2(F,G)(0)=\tfrac12\sum_\pm\int d\theta\,(\int F(r,\theta)dr)(\int G(\rho,\theta\pm\pi/2)d\rho)$. Take
$F=G=|x|^{-1}|\log|x||^{-1}\mathbf 1_{|x|<1/2}$: it lies in every $L^2_s$ but $\int F\,dr=\infty$. Near the singular
point, $Q_2\gtrsim(\log|\log|p||)^2$, so suitable $f\in L^2_s$ give $f\cdot Q_2\notin L^2$. This agrees with the entry,
which rightly does not claim to settle the full $d=2$ statement.

**(d) Scope of use.** The entry says "(only the blow-up criterion of Prop 3.2 uses it)" (summary table), and its text
says TARGET uses it "to obtain the blow-up criterion". That is too narrow. In Appendix C, (schappend8) gives local
well-posedness in $Z_s$ (L2515) and in $Z_{s,m}$ (L2526), hence the common lifespan, Schwartz regularity *and* the
blow-up criterion: all of Prop 3.2 as proved there. The conclusion "Main theorem: none" stands. Theorem 1.1's proof
uses only that $\varphi$ is a Schwartz solution on $[0,\tau_*]$ with $\mathfrak C<\infty$ (L606–L607), and the
estimate is true in any case.

### 4. Verdict: CONFIRMED WITH CORRECTIONS

The substance is correct. Remark 2.6 gives no proof; for $d\ge4$ TARGET relies on it; the natural transfer of the $d=3$
proof fails at exactly the stated step; and (bil7) remains true. The corrections:

1. **Class: GAP → EXPOSITION.** By the file's own definitions, a step "omitted but can be filled routinely" is
   EXPOSITION. The fill is the weighted Cauchy–Schwarz plus Hölder/Young on $S^{d-1}$ above. If the class changes, move
   E2g from summary item 4 ("Gaps that needed a new argument") to item 5.
2. **Replace** "Lemma 4.1 would need a d-dimensional dispersive bound that is not proved." **with:** "Lemma 4.1 uses
   the dispersive bound (ma13), which GIT20 calls standard; its $d$-dimensional form,
   $|K(y,t)|\lesssim|t|^{s-d/2}$ for $|t|\le1$ and $\lesssim|t|^{-d/2}$ for $|t|\ge1$, follows by the same standard
   argument, and Lemma 4.3(ii) transfers for $2s>d-2$."
3. **Scope.** In the summary row, replace "(only the blow-up criterion of Prop 3.2 uses it)" with "(Theorem 1.1 uses
   only a Schwartz solution on $[0,\tau_*]$; the estimate enters Appendix C's proof of Prop 3.2: local well-posedness in
   $Z_{s,m}$ and the blow-up criterion)". Make the matching change in the entry text ("to obtain local well-posedness in
   $Z_s$ and $Z_{s,m}$ and the blow-up criterion") and in Deviations §B ("For $d\ge4$ its proof (Appendix C) rests on
   GIT20 Remark 2.6 …").
4. **Lean status (consistency, for the doc owners).** origin/main has `WaveTurbulence/Provider/Wkelwp.lean`. It proves
   all conjuncts of `wkelwp`, the blow-up one via `WKEL2.wkelwp_blowup`, "which rests on the general-dimension weighted
   L² trilinear estimate". `Foundations/WKEL2` has no `sorry` in its `.lean` files, and the audits call `wkelwp`
   sealed. If that is right, the Main-theorem cell should read "repaired in Lean (and on paper)", and Deviations §B
   should say so. I did not check the Lean proof.
5. **Tone.** "Asserted without proof" is accurate but reads harsher than intended for a remark. Suggest "is stated in a
   remark without proof". Also "GIT20's d = 3 argument fails for d ≥ 4 at one step" → "GIT20's d = 3 argument does not
   transfer to d ≥ 4 at one step": the $d=3$ argument is correct; its $d$-dimensional adaptation is what fails.
6. **Optional, minor.** TARGET L2515 cites "Lemmas 4.1–4.3"; in the arXiv numbering the $Q_3$ lemma is 4.4, and 4.3 is
   the technical lemma. Journal numbering may differ, so mention this only if checked.

Once corrected, status may move to CONFIRMED.

---

## E39 — TARGET L2299: the upper $M_2$ cutoffs at unselected stem nodes inside coherent regular trees

### 1. Pin

TARGET L2285 (statement):

> Moreover, suppose $|k|\geq M_1^{10}$, and in (jtflower) we further restrict to
> $\max_{\mathfrak n\in\mathcal S}|\Omega_{\mathfrak n}|\sim_0 M_2$ … by a smooth cutoff function for the tree
> $\mathcal T$, where $\mathcal S$ is the set of all branching nodes $\mathfrak n$ in the stem of $\mathcal T$ other
> than the parent node $\mathfrak f^{\mathrm{pr}}$ …

TARGET L2299 (adjustment (6)), quoted correctly in the entry:

> if we insert the $M_2$ cutoff, then for each $j$ we fix a branching node $\mathfrak n_j\in\mathcal S_j$ and insert the
> cutoff such that $|\Omega_{\mathfrak n_j}|\sim_0 M_2$ (otherwise these cutoffs play no role in the proof).

DH21 L2699 (Cor 11.3) allows "one (or more)" lower cutoffs $|\Omega_{\mathfrak n_j}|\ge M_1$. DH21 L2703 treats the
selected node in case (a) (inside a regular couple or tree) and case (b). DH21 L2735 is the dyadic partition
(Rdecompose) of every $\Omega_{\mathfrak n_j}$, with $M$ the maximum. All line numbers check.

### 2. Reconstruction

Any smooth realization of "$\max_{\mathcal S}|\Omega|\sim M_2$" — DH21's product partition, or a telescoped
$\prod\chi_0(\Omega/M_2)-\prod\chi_0(2\Omega/M_2)$ — leaves a band cutoff at one selected node and upper cutoffs
$\chi_0(\Omega_{\mathfrak b}/2^jL)$ at the other stem nodes. These cannot be removed. `fixedpoint` (6) (L2328) uses
"$|\Omega_{\mathfrak n}|\le M_2$ for all branching nodes $\mathfrak n\neq\mathfrak f^{\mathrm{pr}}$ on the stem" for
the finite-representation step, so the estimated quantity must contain them. Oscillatory sums are not monotone, so
$|\chi|\le1$ does not let one drop them. Stem nodes can be chain nodes of regular trees on the stem: the regular tree
collapsed at a stem skeleton node carries the stem from its root to its lone leaf. All its nodes are in layer $p$
(Def `defflower`; Prop `layerreg1`), so such trees are typically coherent. The printed proof says nothing about these
cutoffs, and DH21 is equally silent outside the selected node. **The entry's factual claims are correct.**

### 3. Refutation attempt: is the fill routine?

I looked for a short fill. I find one for exactly the entry's scope: unselected filters in coherent regular trees that
carry no pin and no selected node. Those other cases are E30/E35.

- **(a) The filter is a function of one spectral coordinate and does not depend on $k$.** Inside a single-layer
  regular tree (TARGET reduces layered objects to these, L1234–L1246, using DH23 L950–L968), every branching node is
  linked. For each link, $\Omega=\pm2\langle x_j,y_j\rangle$ in DH23's link variables. Here the root momentum $k$
  enters only through $W$ (L1240: $k_{\mathfrak r_{[r]}}=k$; DH21 L2690: $W$ is the input tensor after a linear change
  of variables). The filter at a stem chain node is therefore $\vartheta(\alpha_j/S)$, with $S\asymp\delta L^{2\gamma}M_2\ge\delta L^{2\gamma+1}$.
  It is even, so a node and its partner give the same coordinate.
- **(b) Integrated coordinates, $j\notin Z$.** Multiply $\vartheta(\alpha_j/S)$ into $\mathcal C_Z$ (DH23 (maincoef1)).
  The bounds (maincoef2) and (maincoef2.5), and DH23 `approxnt` (propertypsi2), survive by the product rule, since
  $S\ge1$ and the cutoff is Gevrey. The leading term changes from $\int\Psi_1$ to $\int\Psi_1\vartheta$, a difference
  of at most $C^nS^{-(1-\eta/2)}$. This also covers non-dominant objects, whose leading terms change by the same tiny
  amount.
- **(c) Extracted coordinates, $j\in Z$.** Write $g\vartheta=g-g(1-\vartheta)$ with $g=\chi_\infty(\alpha)/\alpha$. The
  tail is at most $2/S$ pointwise. Sum it absolutely over the at most $(3\lambda L)^{2d}$ lattice points of that link,
  and apply `approxnt` to the remaining links with that link frozen ($\|\hat W\|_{L^1}$ does not increase). The tail
  term is then at most $\lambda^{C}(C^+L^{2d-2\gamma}\delta^{-1})^n\cdot\lambda^{2d}M_2^{-1}$. With
  $M_2\ge L$, $\lambda\le(\log L)^4$ and $\gamma_1=\min(2\gamma,1,2(d-1)(1-\gamma))\le1$ (L613), this is below the
  remainder size $L^{-(\gamma_1-\sqrt\eta)}$. Expanding over all filtered $Z$-links costs at most a factor
  $\lesssim n\lambda^{2d}/L$. So the untruncated principal value can be kept and no truncated-p.v. lemma is needed.
  o82 Prop 3.1 (a one-paragraph proof) and Props 2.1/4.1 take a different, also valid, route.
- **(d) Only bounds are consumed for stem objects.** Stage 1 consumes regular objects through their $\mathfrak X$ norms
  (T1959–T1965). The exact identities (regref2-3) and (layerregest10) are used only in the core-vine step
  (T1878–T1925), for $\mathcal T_{(\mathfrak u_2)}$ and $\mathcal Q_{(\mathfrak u_0,\mathfrak u_{23})}$ of a twisted SG
  vine. The $M_2$ cutoff is inserted only when $|k|\ge M_1^{10}$ (L2285, L2320). In that regime TARGET's own adjustment
  (7) (L2300) shows that the stem leaves such a vine through $\mathfrak u_{11}$, so these objects lie off the stem and
  carry no stem filter.

So the unselected filters inside unprotected coherent stem trees do "play no role" in the sense of costing nothing. What
the paper lacks is the short check (a)–(d). This matches the independent assessment the entry relies on, which says it
"ha[s] not established either that the entire weighted bridge is routine or that its completion requires a genuinely
new idea", and lists the point as UNREFUTED-TENTATIVE, not as non-routine (`astra-flowerest1-report.md` §1 and the §3.6
table).

### 4. Verdict: CONFIRMED WITH CORRECTIONS

1. **Class: GAP → EXPOSITION.** The omitted step is real, but in my judgment an expert in the DH21/DH23 machinery fills
   it routinely; (a)–(d) above is the fill.
2. **Summary row, replace the Claim with:** "'these cutoffs play no role' is not justified for the upper $M_2$ cutoffs
   left at unselected stem nodes inside coherent regular trees; they must be carried through the coherent asymptotics,
   which takes a short spectral check". In the heading, "can sit inside" is fine, but avoid "fails": the cutoffs do in
   the end cost nothing.
3. **Summary item 2** groups E39 with E44 under "arguments for the upper M₂ filters … (E39, E44)". Keep E44 there and
   list E39 with the exposition items (E36–E38).
4. **Main-theorem cell and "State of our Lean attempt".** Per the same file, `layergardenFlower_v3`/`v4` are proved and
   two-key audited (summary item 2; `docs/audits/v2-chain/Seal-layergardenFlower_v3.md`). Their frozen statement
   includes the product-form $M_2$ cutoffs (`cutWeight2P`, `prodDyadicCut`) on full gardens, so the upper filters at
   every stem node are inside a proved Lean statement. The paragraph saying the weighted coherent approximation "is
   not on main" and the cell "repaired on paper (refereed: o82 Thm 8.2′)" should be reconciled with that. Either say
   "repaired in Lean (`layergardenFlower_v3`/`v4`) and on paper", or explain why the Lean proof does not cover this
   point. I did not check the Lean proof.
5. **Fairness paragraph.** It is accurate and should stay. One could add that DH21 Cor 11.3 asserts its gain with "one
   (or more)" cutoffs inserted (L2699) and likewise does not discuss their effect elsewhere.

With these changes the status can move to CONFIRMED (as EXPOSITION).

---

## E45 — TARGET L2327–L2331: the derivative (and †) variants used for `fixedpoint`

### 1. Pin

TARGET L2327 (`fixedpoint` Part 2, item (5)): $\widetilde{\mathcal J}_{\mathcal T}=\sum e^{\zeta\pi i\delta L^{2\gamma}\Omega_{\mathfrak f^{\rm pr}}s}\cdot\mathcal J^\dagger_{\mathcal T}$,
summed over the sibling momenta, at a loss of at most $M_1^{10d}$.

TARGET L2331 (item (8)), quoted correctly in the entry:

> here the $\partial_t$ derivative introduces an extra $\delta(t_{\mathfrak r}-t)$ factor, while the $\partial_s$
> derivative introduces an extra $\delta(t_{\mathfrak n}-s)$ factor with $\mathfrak n$ being the parent or a non-flower
> child of $\mathfrak f^{\mathrm{pr}}$, and all these factors can be treated just as the one in (jtflower) (the case
> when $\mathfrak f^{\mathrm{pr}}=\mathfrak r$ only needs some trivial adjustments). This leads to a bound similar to
> (flowerest2) but with extra loss of at most $L^{(100d)^3P}$ and possibly without the $M_2^{-P/9}$ decay …

TARGET L2297, the special nodes: "the root $\mathfrak r_j$, any of the children nodes of $\mathfrak r_j$, the flower
$\mathfrak f_j$, the parent and any sibling node of $\mathfrak f_j$". Line numbers check.

### 2. Reconstruction

With $t_{\mathfrak f^{\rm pr}}=s$ pinned, $\mathcal J^\dagger$ depends on $s$ through the order constraints at
$\mathfrak f^{\rm pr}$. Differentiating gives boundary terms $\delta(t_{\rm gp}-s)$ (gp = the parent of
$\mathfrak f^{\rm pr}$) and $\delta(t_m-s)$ for branching siblings $m$ of $\mathfrak f$. $\partial_t$ gives
$\delta(t_{\mathfrak r}-t)$. The entry's "harmless overcount" is right. A child in a lower layer has
$t_m<p<s$ automatically, and leaves have no time variable, so only layer-$p$ branching siblings contribute.

### 3. Checks

- **(a) The grandparent pin is unprotected; this matters.** gp is not on the L2297 list unless it happens to be the
  root or one of its children. Is protection actually needed? For $|k|\ge M_1^{10}$, adjustment (7) (L2300) shows that
  SG twists do not touch the stem, so gp is safe there. But `fixedpoint` also needs the $\partial_{t,s}$ terms when
  $|k|\le M_1^{10}$ (item (2), L2324, together with items (7)–(8), "this applies to any of the cases considered above").
  There, (7) is not available. By Def `twist` (L1431), a unit twist re-attaches $\mathfrak u_2$ (to $\mathfrak u_3$ or
  $\mathfrak u_4$) and swaps the positions of $\mathfrak u_{21},\mathfrak u_{22}$. A concrete bad case: $\mathfrak f$ is
  a child of $\mathfrak u_{21}$, so $\mathfrak f^{\rm pr}=\mathfrak u_{21}$ (outside the block) and
  $\mathrm{gp}=\mathfrak u_2$, a joint of the vine. That vine contains no L2297 special node, so it may be twisted, and
  the dParent pin sits inside a twisted vine. Neither (4)'s scheme (protected vines estimated without twisting, at
  $L^{20d}$ each) nor the vine estimate covers that. **The entry's point is correct.** The fix is to add gp to the
  protected set: at most $2P$ more vines, at $L^{20d}$ each, well inside the extra $L^{(100d)^3P}$ of L2331.
- **(b) Coincident pins: correct.** In the dParent and dChild terms, two adjacent vertices are pinned at the same time
  $s$. In effect this is one pinned vertex of degree 6. Adjustment (2), which handles one pin per tree by fixing its
  $\Omega$, does not address this configuration. The configuration also inherits E30's time-trace problem. It is the
  same kind of object as E30's pin: a bounded number of extra pinned vertices per tree, each losing integrability in
  one spectral coordinate, as in DH21's own pin mechanism at L2684–L2694. So, in my judgment, it is routine once E30 is
  repaired.
- **(c) The mention of adjustment (6) is imprecise.** The derivative terms do not need the $M_2$ gain: L2331 says
  "possibly without the $M_2^{-P/9}$ decay", and (sobolev2) supplies $M_2^{-100P}$. So "which neither adjustment (2)
  nor adjustment (6) treats" should be "which adjustment (2) does not treat (the derivative terms need only the plain
  estimate, L2331)". Calling the configurations "faces" is a convenient description, not a requirement.
- **(d) †.** The entry identifies no gap specific to $\mathcal J^\dagger$; its own repair says † costs no power of $L$.
  The title and summary row ("the dagger and derivative variants … add an unprotected grandparent pin and coincident
  faces") attribute to † something only the derivative variants do.
- **(e) Fairness.** DH21 treats time derivatives just as briefly: L2716, "taking $\partial_t$ derivative just
  corresponds to omitting the $t_{\mathfrak r}$ integration and producing something like (defaltkq)", and L2733, "the
  corresponding bound for $t$ and $s$ derivatives (which can be obtained similarly as in Section 11)". TARGET L2331
  follows that practice. The entry should say so, as E39 does for its point.

### 4. Verdict: CONFIRMED WITH CORRECTIONS

The substance is correct. L2331's "treated just as the one in (jtflower)" inherits E30 and E31. It also places a pin at
the flower's grandparent, which L2297 does not protect and which an LF twist can reach when $|k|\le M_1^{10}$. And it
creates coincident pins at time $s$. The corrections:

1. **Class rationale.** Keep GAP, but write "GAP (through E30, E31)" in the table. State that the points E45 adds —
   protecting the grandparent, and treating the coincident pins and the pinned child face — are routine once E30 and
   E31 are repaired. Change summary item 2 accordingly: "the derivative variants used for `fixedpoint` inherit these
   gaps and need two routine additions (E45)". Do not present E45 as an independent non-routine gap.
2. **Title and summary row, replace with:** "the derivative variants (with the † kernel) used for `fixedpoint` inherit
   E30 and E31, put a pin at the flower's grandparent, which L2297 does not protect, and create coincident pins at time
   $s$".
3. **Wording:** "neither adjustment (2) nor adjustment (6) treats" → "adjustment (2) does not treat; the derivative
   terms do not need the $M_2$ gain of (6) (L2331)".
4. **Add a fairness sentence:** "DH21 treats its time-derivative terms in one sentence each (DH21 L2716, L2733); TARGET
   L2331 follows that practice."
5. **Main-theorem cell.** The frozen `layergardenFlower_v3`/`v4` statement contains the patterns `dRoot`, `dParent` and
   `dChild` (`Frozen/Defs/FixPat.lean`) and the † option (`flowerSumP`), and the file reports it proved and two-key
   audited. So "repaired on paper (o104 Thm 10.4), partly refereed" should become "repaired in Lean (clauses of
   `layergardenFlower_v3`/`v4`) and on paper (o104 Thm 10.4)", unless there is a reason the Lean proof does not cover
   these clauses. I did not check the Lean proof.

With these changes the status can move to CONFIRMED (as a GAP through E30 and E31).

---

## Reproducibility

- [`EV-C-scripts/wcheck.py`](EV-C-scripts/wcheck.py)
  (pure Python, no dependencies) computes $w_p(\theta)$ for $d=4,5,6$ and $s=(d-2)/2+0.05$. It checks the growth
  $R^{d-3}$ at $\phi=0$ and the uniform bound $\sup_R w_p\min(1,\phi^{d-3})\le 10.2$.
- The evidence files I read (assessment, o82, o104, REFEREE, REFEREE-82, REFEREE-73) were consulted only after I had
  reconstructed each claim from the printed sources. My verdicts rest on the printed text and the arguments above.
