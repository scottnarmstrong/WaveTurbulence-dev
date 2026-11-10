# Flower estimate: integrated supplement, version 2

This supplement proves the corrected `flowerest1` estimate and its fixed-time pattern and dagger extensions from the source results and the resolution packets listed below. Long packet proofs are incorporated by exact theorem and section references, with their hypotheses, loss estimates, and mechanisms restated here. The adopted construction leaves marked vines unspliced. The first-cutoff and external-decay gains use one real Lagrange extrapolation and introduce no leaf marks. The superseded excision and marked-leaf extraction are not used.

**Review status at assembly.** `REFEREE-82` is now available and its fixes are incorporated; it is no longer pending. The latest status of `REFEREE-73` is reported in Section 13. Mathematical theorem assertions below cite the packet proofs; a pending independent review is identified separately and is not silently treated as a proof or as a theorem hypothesis.

**Packet notation.** All paths in this list lie under `<scratch>/flower-open/`. Exact input hashes appear in Section 13.

| Notation | Packet and adopted result |
|---|---|
| O63 | [o63/RESOLUTION.md](<scratch>/flower-open/o63/RESOLUTION.md): Theorem 6.3′, Lemmas A–D, Proposition 10.3′, revision 2 |
| O73 | [o73/RESOLUTION.md](<scratch>/flower-open/o73/RESOLUTION.md): Theorem 7.3′, §21; elementary results §§3, 5, 12–13 and completed estimates §§17–22 |
| O75 | [o75/RESOLUTION.md](<scratch>/flower-open/o75/RESOLUTION.md): Theorem 7.5′, revision 1; numerical estimates §7 and aggregate count §8, with all §11 corrections |
| O82 | [o82/RESOLUTION.md](<scratch>/flower-open/o82/RESOLUTION.md): Theorem 8.2′, §19, and its proofs §§10–18; earlier conditional marked-coefficient proposals are not used |
| O83 | [o83/RESOLUTION.md](<scratch>/flower-open/o83/RESOLUTION.md): Theorem 8.3, Theorem K, Corollary 8.3.A and §§6–8 |
| O102 | [o102/RESOLUTION.md](<scratch>/flower-open/o102/RESOLUTION.md): Theorem R and the absolute remainder proof §§2–5 |
| O104 | [o104/RESOLUTION.md](<scratch>/flower-open/o104/RESOLUTION.md): Theorem 10.4, pattern identities §§3, 6–8; its former child-face obligation is supplied by O73 §21 |

The frozen v1 is `SUPPLEMENT-v1.md`, SHA256 `ddd81fe1238e7c51379a69981b4d10aa68690ced46d0fc1b115200fc0c3774d7`. Sections 2–5 below retain its numbered lemmas, with the changes required by [REFEREE.md](<scratch>/flower-open/ref/REFEREE.md). Additional referee fixes and all interface resolutions are listed in Section 12.

## 1. Sources, constants, and the target statement

We use the following frozen local sources; line numbers below refer to these files.

- **T:** `<sources>/paper/source/WKE-Longer_times_Final_arXiv.tex`, SHA256 `493eef6b7dec448bc5f9f1c3974c0cad7a85eca9bc428f5b35e968aad76727cb`.
- **D21:** `<sources>/references/src-2104.11204/Inventiones-Final_Version.tex`, SHA256 `50d0e236a2df0cfd2b98bace6f0256043ee88fc05079ee44c3524ca9482fe402`.
- **D23:** `<sources>/references/src-2301.07063/Revision_Submit.tex`, SHA256 `c7e47dfabf5a4cca6e3ad0399fc377f2809c12f58e1563640407fe0992335475`.

Assume $d\ge3$ and $1/2<\gamma<1$. Choose $\eta$ sufficiently small depending on $d,\gamma$, including $8\eta\le2\gamma-1$. The constants $C_0,C_1,C_2,\nu,\eta,\Lambda_p,N_p$ have the meanings and dependencies in T606–615. In particular, $C_2$ may depend on $\delta$; it cannot be used indiscriminately as the base of an exponential in the order. Choose $P$ first, $\delta$ second, and $L$ last. Constants depending on $\delta$ but independent of the order can be absorbed by increasing the final threshold for $L$. A factor $C_2^n$ cannot be absorbed by choosing $\delta$ smaller without an additional argument. A factor $L^{Cn}$ is inadmissible.

Write $\Lambda=\Lambda_{p+1}$ and $N=N_{p+1}$. The bounds proved below, for the three versions without cutoffs, with the first cutoff, and with both cutoffs, are

$$
\mathbb E_p|\mathfrak X_{kk'}^\zeta(t,s)|^{2P}
\le \langle k-\zeta k'\rangle^{-4\Lambda P}L^{(100d)^3P}
\begin{cases}
1,\\
M_1^{-80dP},\\
M_1^{-80dP}M_2^{-P/9}.
\end{cases}
\tag{1.1}
$$

The last line assumes $|k|\ge M_1^{10}$. For $\mathfrak Y$ and $\mathfrak W$ there is a further factor $e^{-100N}$. All kernel statements are on $p<s<t<p+1$.

**Normalization convention.** Throughout, each branching node contributes $\delta/(2L^{d-\gamma})$, as in T671 and T712. We correct the printed $d-1$ in T2264–2265 to $d-\gamma$. For order $n$ the difference is a factor $L^{(1-\gamma)n}$, so this is a substantive correction, not an absorbable constant.

**Order-zero convention.** The trivial flower tree contributes the identity operator in the positive-sign channel. Thus $\mathfrak X=I+\mathfrak X_{\mathrm{reg}}$ as an operator. Its formal identity kernel is $\mathbf1_{k=k'}\delta(t-s)$, not a function to which a pointwise $2P$ moment applies. In (1.1), $\mathfrak X$ denotes the regular kernel on the open triangle. No flower-parent pin is assigned to a nonexistent parent. There is no negative-sign order-zero contribution. The definitions of $\mathfrak Y=(1-\mathfrak L_1)\mathfrak X-I$ and $\mathfrak W=\mathfrak X(1-\mathfrak L_1)-I$ use this operator convention.

For reference, the relevant time Fourier norm is

$$
\|U\|_{X^{\theta,a,b}}
=\max_{|\rho|\le a}\int \max_i\langle\lambda_i\rangle^\theta
\sup_k\big|\langle k\rangle^b\partial_k^\rho\widehat U(\lambda,k)\big|\,d\lambda.
\tag{1.2}
$$

On a time domain it is the infimum over extensions. In particular the supremum in $k$ is **inside** the Fourier integral. We retain this order of norms.

## 2. Capping and the exact integrand

An original tree is a tree before the lower-layer cumulant insertions. Its nonflower leaves form its frontier $B_j$. A frontier vertex may become an internal vertex after an insertion. The index $j\in\{1,\ldots,2P\}$ always refers to the original tree, not a component or a subsequently collapsed regular object.

### Lemma 2.1 — Capped encoding

Let $\mathcal G$ be a canonical layered flower garden in T2261 with $2P$ ordered original trees. Adjoin, for each flower $f_j$, a new trivial tree $c_j$ whose sign is opposite to that of $f_j$, put $c_j$ in layer $p$, and pair $c_j$ with $f_j$. Keep the $2P$ original roots and append the labeled caps in their original-tree order. Then:

1. The result $\widehat{\mathcal G}$ is an ordinary completely paired garden of width $4P$, with the same branching nodes, branching signs, resonances, and order.
2. Its irreducible components have even width, at most $2P$ components occur, and every component is a canonical couple or a canonical proper garden at level $p+1$.
3. Restriction and extension give a bijection between the flower decorations with roots $k$ and flowers $k'$, and the ordinary decorations of $\widehat{\mathcal G}$ with original roots $k$ and all cap roots $k'$.
4. The construction preserves the full original-tree truncation data, provided those data are retained as labels. It does not turn the flower truncation into an unrestricted ordinary-garden truncation.

**Proof.** A cap adds one leaf, no branching node, and one opposite-sign pair. Every leaf is now paired. For a signed ternary tree, the sum of its leaf signs equals its root sign: replacing a parent sign $\sigma$ by $(\sigma,-\sigma,\sigma)$ preserves this sum. Consequently every completely paired component has total root sign zero and even width. It contains at least two roots, so there are at most $4P/2$ components.

For canonicity, use the recursive construction in T2261. At the top level, the flowers are now ordinary paired layer-$p$ leaves with their caps. All other top pairs and all lower-layer replacement gardens are unchanged. A lower replacement is irreducible, so all original trees incident to it belong to one connected pairing component. Thus passage to a component never cuts a lower replacement into pieces. Restricting the top-level construction to a component gives exactly the canonical construction: its pairs and replacement blocks do not connect to the complement, and its irreducibility supplies the last connectivity requirement. A two-root component is treated by the couple version of the construction. Equivalently, the only new completely paired rooted subtrees involving a cap have a root of layer $p$ (the cap itself), and hence satisfy the inequality of T889.

The decoration at a cap is fixed to $k'$. The equality across its leaf pair fixes $k_{f_j}=k'$. There is no additional conservation equation at a trivial tree and no additional phase. This proves the bijection and the preservation of all original vertex quantities.

Finally, retain the original top trees, their child-subtree orders, the two flower-sibling orders, the order after collapsing the flower parent, and every lower replacement's order. Adding a cap changes none of them. These labels give an inverse to capping, so membership in the $\mathfrak X$, $\mathfrak Y$, or $\mathfrak W$ truncation is preserved exactly. ∎

The basic protected vertices are the root, its three children, the flower, its parent, and its two siblings, with repetitions removed. There are at most $8$ per original tree, or $16P$ in total, and $2P$ caps. An object containing a protected vertex remains protected when collapsed. Selected frontier or resonance vertices will add further marks later.

### Lemma 2.2 — Decoration-sum and moment identities

Define $K^{\mathrm{cap}}_{\widehat{\mathcal G}}$ by the ordinary decoration sum, but assign input $1$ to each flower-cap pair, assign the original $F_q$ to every other pair, retain the original time domain, and insert $\prod_j\delta(t_{f_j^{\mathrm{pr}}}-s)$. With the normalization in Section 1,

$$
K^{\mathrm{cap}}_{\widehat{\mathcal G}}(t,s;k,k')
=\widetilde{\mathcal K}_{\mathcal G}(t,s,k,k').
\tag{2.1}
$$

A deterministic function of any collection of original decorations can be inserted on both sides. In particular, for real tree multipliers $w_j$, the moment expansion is exactly T2287–2290 with the summand multiplied by $\prod_{j=1}^{2P}w_j$, and with the same multipliers inserted in the cumulant-error terms.

**Proof.** Apply the bijection of Lemma 2.1 term by term. The branching-node products, signs, exclusion factors, and time constraints agree. The new pair has weight $1$, so it introduces no spurious factor $F_p(k')$. It introduces no time integration. The pins coincide. This proves (2.1), including its weighted version.

For the moment statement, expand the $2P$ tree sums and apply the moment-cumulant identity T565–575 to the nonflower random inputs. A deterministic multiplier is independent of the partition in that identity and stays in each summand. Expand each cumulant using the assumed lower-layer ansatz. Pair blocks supply $F_q$; higher blocks supply the lower gardens. Terms containing an ansatz error retain their deterministic multipliers. These operations are precisely those giving T2287. Capping is then the termwise bijection just proved. This identity asserts no estimate for the error terms. ∎

The capped input is not an ordinary Schwartz input, and the time pins are not ordinary integrations. Applying `layergarden` directly to (2.1) would therefore be invalid.

## 3. Frontier cutoffs and Fourier measures

Fix a real, even, radial $C^\infty$ function $\chi$ with $0\le\chi\le1$, $\chi=1$ on $|x|\le1$, $\chi=0$ on $|x|\ge2$, nonincreasing in $|x|$. Fix it once, independently of $P,\delta,L$. For $M>L$ dyadic define

$$
A_{j,M}=\prod_{v\in B_j}\chi(k_v/M),\qquad
H_{j,M}=A_{j,M}-A_{j,M/2},\qquad H_{j,L}=A_{j,L}.
\tag{3.1}
$$

Empty products equal $1$. A nonbottom shell is supported where $M/2\le\max_{v\in B_j}|k_v|\le2M$. These are concrete smooth cutoffs of the type requested in T2283. An arbitrary unspecified smooth function of a maximum does not have a uniform constant without specifying its derivative bounds; all claims here refer to (3.1) and finite linear combinations with controlled coefficients.

For a function on $\mathbb R^D$ represented as

$$
a(x)=\int e^{2\pi i\xi\cdot x}\,d\mu(\xi),
\tag{3.2}
$$

use the total variation of the chosen finite complex measure $\mu$. We do not require $\mu$ to have a density. Write

$$
B_s(\chi)=\int_{\mathbb R^d}(1+2\pi|\xi|)^s|\mathcal F\chi(\xi)|\,d\xi,
\qquad s\in\mathbb N_0.
\tag{3.3}
$$

Here $\mathcal F$ is a spatial Fourier transform, distinguished from the time transform in T.

### Lemma 3.1 — Fourier-measure algebra with constants

Let $a_i(x)=\chi((A_ix+b_i)/R_i)$, $1\le i\le h$, with arbitrary real matrices $A_i$, vectors $b_i$, and $R_i\ge1$. Then $\prod_i a_i$ has a representation (3.2) with

$$
\|\mu\|_{\mathrm{TV}}\le B_0(\chi)^h.
\tag{3.4}
$$

If only derivatives in an output variable $z$ are needed and $A_i^{(z)}$ denotes its coefficient block, then, for $s\ge1$, the corresponding measure has output-frequency moment at most

$$
h^{s-1}\sum_{i=1}^h
\max(1,\|A_i^{(z)}\|/R_i)^s B_s(\chi)B_0(\chi)^{h-1}.
\tag{3.5}
$$

For $h=0$ use the point mass at zero. If an existing amplitude has Fourier $L^1$ norm $D$, multiplication by these factors multiplies its Fourier $L^1$ norm by at most $B_0(\chi)^h$.

**Proof.** Fourier inversion represents $a_i$ as the pushforward of
$e^{2\pi i\xi\cdot b_i/R_i}\mathcal F\chi(\xi)\,d\xi$ under $\xi\mapsto A_i^T\xi/R_i$. Pushforward does not increase total variation, even if $A_i$ is not injective or surjective. Products correspond to convolutions of these measures, proving (3.4). For the output frequency $\sum_i(A_i^{(z)})^T\xi_i/R_i$, use
$(\sum_i u_i)^s\le h^{s-1}\sum_i u_i^s$ with $u_i=1+2\pi\|A_i^{(z)}\||\xi_i|/R_i$, and integrate. This gives (3.5). Finally, convolution of an $L^1$ density with a finite measure has $L^1$ norm at most the product of their norms, by Tonelli and translation invariance of Lebesgue measure. ∎

### Lemma 3.2 — Shell expansion and commutators

A product of $2P$ shell factors is a signed sum of at most $2^{2P}$ low-pass products (bottom factors need no expansion). For affine $z_i(x)$, fixed real $d\times d$ matrices $b_i$, fixed $r\in\mathbb R^d$, and $R_i\ge R_*$,

$$
\prod_i\chi((z_i+b_ir)/R_i)-\prod_i\chi(z_i/R_i)
\tag{3.6}
$$

is an integral of Fourier-measure amplitudes with a factor $|r|$, and with total variation, after that factor is removed, at most

$$
R_*^{-1}\sum_i\|b_i\|\, B_1(\chi)B_0(\chi)^{h-1}.
\tag{3.7}
$$

In (3.7), enlarge $B_1$ by an absolute dimensional constant if a coordinatewise derivative convention is used.

**Proof.** Expand each difference in (3.1). To prove (3.6), telescope the product in the index $i$. Its $i$th difference is

$$
\chi((z_i+b_ir)/R_i)-\chi(z_i/R_i)
=\int_0^1R_i^{-1}(b_ir)\cdot\nabla\chi((z_i+ub_ir)/R_i)\,du.
$$

Apply Lemma 3.1 to the other factors and Fourier inversion to $\nabla\chi$. Sum the resulting total-variation bounds. The translation $ub_ir$ has modulus-one Fourier factor and no effect on those bounds. ∎

## 4. Weighted localized estimates

The next two lemmas extend individual analytic estimates. They do not assert stability under arbitrary regrouping of weighted gardens.

### Lemma 4.1 — Frontier-weighted `proplayer1`

Let $\mathcal Q$ or $\mathcal T$ satisfy T953–955, have order $2n$ and incoherency index $g\ge1$. Insert $h$ factors $\chi(k_v/R_v)$, $R_v\ge L\ge1$, at arbitrary specified vertices of that object. In the regular-tree case exclude its unweighted lone port from the list, unless a factor at that port is explicitly assigned to this object. Let $K_w$ be the resulting kernel. There is a constant $C_\chi$, depending only on $d$ and $B_{32d}(\chi)$, such that

$$
\|K_{\mathcal Q,w}\|_{X^{\eta,30d,30d}}
+\|K_{\mathcal T,w}\|_{X^{\eta,30d,0}}
\lesssim_1 C_\chi^{h+1}(1+h)^{32d}
(C_1\delta)^n L^{-(\gamma_1-\sqrt\eta)g}.
\tag{4.1}
$$

Include only the terms that are defined. For $h\le c n$, the additional cost is at most $C_{\chi,c}^{n+1}$. It contains no power of $L$.

**Proof.** Use the coordinates $(k,x_v,y_v)$ of T981–1017. Conservation and the regular linkage show that every vertex momentum is $k$ plus an integer linear combination of the $x_v,y_v$. In particular its coefficient of $k$ is the identity, independently of its depth. The phases and exclusion factors have no $k$ dependence in these coordinates.

Differentiate the weighted expression in $k$. Of the at most $30d$ derivatives in the claimed norm and the further $2d$ derivatives used in the Sobolev step T1001–1005, any number may fall on the new factors. Lemma 3.1 bounds the sum of their Fourier-measure norms by $C_\chi^{h+1}(1+h)^{32d}$. Derivatives falling on the original inputs are exactly the derivatives already paid for in T995–1005. The output weight $\langle k\rangle^{30d}$ is paid from the original leaf inputs using T995, without using decay from the new factors.

Perform the same leaf localization and the same $C_0^n$ refinement to unit balls for $x_v,y_v$ as in T1007–1009. The new factors do not enlarge the support. Convolve the localized Fourier density in T1011–1015 with the measures from Lemma 3.1. The phase-modulated estimate T1017 and the rest of the proof are uniform in all the resulting spatial modulation parameters, so integration against the convolution measure multiplies the bound only by its total variation. For couples, the fixed extension and the Sobolev step T995–1000 give (1.2), with its output supremum inside the Fourier integral. For regular trees that Sobolev step is unavailable: there is no input at the lone leaf and hence no output decay (T1060). Instead use T1062–1092. The joint Fourier measure in $(k,x,y)$ adds a unimodular factor in $k$ and changes only the spatial modulation parameters, which T1065 explicitly permits to depend on $k$. The negative and positive Fourier-regularity endpoint estimates T1077–1091 are uniform in those parameters and in $k$. Integrating the measure multiplies both estimates by its total variation; output derivatives use the same frequency moments already bounded above. Their interpolation gives the regular-tree norm in (1.2). This proves (4.1) for both objects. Finally $(1+h)^{32d}\le C_{d,c}^{n+1}$ for $h\le cn$. ∎

### Lemma 4.2 — Fourier-measure extension of `sumint`

Keep all hypotheses, the time domain, and the bad-vine alternatives of T1595–1620. Denote its number of input vector variables by $m_{\mathrm{vec}}$, its incoherency sum by $G$, and its time-layer mismatch count by $m_0$; these are respectively $M,M_1,M_0$ in that proposition. Insert an amplitude $a_o(\boldsymbol x)$, where $o=(e,f,g,h)$ is the output, independent of every time variable. Suppose that, for each output, it has a measurable representation

$$
a_o(\boldsymbol x)=\int e^{2\pi i\xi\cdot\boldsymbol x}\,d\mu_o(\xi),
\qquad \sup_o\|\mu_o\|_{\mathrm{TV}}\le D.
\tag{4.2}
$$

Then the conclusion becomes

$$
\|\mathcal I_a\|_{X^{2\eta^8,0,0}}
\lesssim_1 D\,\max_{i,j}(\langle\lambda_j^i\rangle,
\langle\mu_j^i\rangle,\langle\sigma_j^i\rangle)^{\eta^6}
(C_1\delta^{-1/2})^{m_{\mathrm{vec}}}
L^{m_{\mathrm{vec}}(d-\gamma)-\eta^2(|\mathrm{Bad}|+G)-\eta^8m_0+\eta^7}.
\tag{4.3}
$$

Thus $h$ affine cutoff factors in the alternative variables cost at most $B_0(\chi)^h$. The affine maps may depend on the output; their coefficients need not be bounded for this zero-spatial-derivative conclusion.

**Proof.** At T1621–1625, the original amplitude is Fourier expanded after localization. At a fixed output, convolve that density with $\mu_o$. This preserves the incoherency factor in its bound and costs $D$. The scalar exponential-sum estimates used in Step 2 are uniform in all spatial modulation parameters, so their integrated estimates also cost only $D$.

One must still justify the order of norms in (1.2). It is insufficient to interchange the supremum over $o$ with an integral against output-dependent measures. Instead repeat the two endpoint estimates of Step 3. In T1680–1700 the negative-regularity bound is obtained from a scalar bound uniform in $o$ for $\|\mathcal K\|_{L^1_{\boldsymbol t}}$, multiplied by a common Fourier majorant in the three output time frequencies. Our insertion changes that scalar bound by $D$. The translation of the input times changes no spatial modulation, since the latter is time independent. The frequency shift $\theta$ in T1694 depends on the original time modulation parameters and is unchanged.

For the positive-regularity endpoint, T1712–1731 first replaces the output supremum by a sum over the at most $O(L^{4d})$ possible outputs in the fixed unit balls, then applies Plancherel at each fixed output. Integrate against $\mu_o$ by Minkowski at this fixed output. Both the estimates with three input times held fixed and those with fewer distinct held times remain uniform in the spatial modulations. The same $D$ therefore multiplies this endpoint estimate, with exactly the source's existing $L^{4d}$ and $L^{14d}$ losses. Interpolating the two endpoints multiplies the final estimate by $D$, since both endpoints have that factor. There is no additional output-counting loss beyond the one already present in T's proof.

For affine cutoffs apply Lemma 3.1 separately at each output. Its total-variation bound is uniform in the affine coefficients and translations. ∎

The amplitude in Lemma 4.2 may not remove the explicit $|r|$, time-interlacing restriction, time Hölder factor, or incoherency gain supplying a bad-vine alternative. Those hypotheses remain in force.

## 5. Coherent profiles and cancellation

Here the entire interior of a (CL) realization belongs to one original tree and uses one low-pass scale $R$. The regular objects in this section contain no flower–cap pair and no time pin; such objects are treated in Section 8. This is the relevant locality: separate original trees may have different scales after the shell expansion. A cutoff belonging to an exterior port is kept outside the realization. Incoming frontier edges are assigned to the first regular object they enter; an edge ending at the lone port of a regular tree is assigned once to that tree, and not again to the continuation.

### Lemma 5.1 — Coherent trunk factorization

For a coherent regular object of upper and lower parameters $(q,q')$, $q\ge q'$, put

$$
F_p^{[R]}(u)=F_p(u)\chi(u/R)^2,\qquad
F_r^{[R]}=F_r\quad(r<p),\qquad
c(q,q')=\mathbf1_{\{q=p>q'\}}.
\tag{5.1}
$$

Under the port convention above, its frontier-weighted kernel and its approximation are respectively

$$
K_{\mathcal O,R}(t,s,k)
=\chi(k/R)^{c(q,q')}K_{\mathcal O}[F^{[R]}](t,s,k),
\qquad
(K_{\mathcal O,R})_{\mathrm{app}}
=\chi(k/R)^{c(q,q')}(K_{\mathcal O}[F^{[R]}])_{\mathrm{app}}.
\tag{5.2}
$$

These formulas apply to couples and to regular trees with their lone port excluded from leaf inputs. The modified profiles are real and satisfy

$$
\|F_r^{[R]}\|_{S^{40d,40d}}
\le C_{d,\chi}\|F_r\|_{S^{40d,40d}},\qquad R\ge1.
\tag{5.3}
$$

**Proof.** Use the structure in T899–901. Every side couple attached to a linked trunk pair is entirely in the layer of that pair. If this is layer $p$, both leaves of each terminal pair belong to the original frontier. Their common momentum $u$ therefore contributes $\chi(u/R)^2$, exactly the modification in (5.1). Side couples in smaller layers lie below the original frontier and have no new internal cutoff.

The trunk layers are nonincreasing. If $q=p>q'$, the upper trunk crosses the original frontier once. All the momenta at the layer junctions are $k$, by T1235–1244. Thus its crossing contributes $\chi(k/R)$. This includes an empty layer-$p$ trunk: the incoming edge itself crosses the frontier. If $q<p$ there is no crossing of layer $p$. If $q=q'=p$, there is no lower-layer crossing; all actual frontier pairs have already been counted in (5.1). These alternatives exhaust the coherent structure, including the trivial and type-1 couples.

The raw time integrals factor over the layer intervals as in T1238–1244, and the new factors are independent of time. This proves the first formula. The approximation is constructed by taking the corresponding approximation of each single-layer factor. Applying the same profile substitution in those factors proves the second formula; no cutoff is being commuted through an approximation operator without a definition. The single-layer estimates used here allow real profiles bounded in the indicated Schwartz norm, as explained in T1174. Finally apply the product rule to $F_p\chi^2(\cdot/R)$; each derivative of the latter factor is bounded uniformly for $R\ge1$. ∎

### Lemma 5.2 — Weighted tuple identity, with multiplicities

Fix $(q,q')$, total order $2n$, and, optionally, the combined number of layer-$p$ branching nodes, exactly as in T1118–1123. Use a common scale $R$ for the couple and regular tree in every term. Then

$$
\sum_{(\mathcal Q,\mathcal T)}
(K_{\mathcal Q,R})_{\mathrm{app}}(t,s,k)
\overline{(K_{\mathcal T,R})_{\mathrm{app}}(t,s,k)}\in\mathbb R.
\tag{5.4}
$$

The sum has the ordinary multiplicities of the ordered-tree convention in T. The assertion also holds after differentiating the complete identity with respect to the common scale $R$ any fixed finite number of times.

**Proof.** Lemma 5.1 extracts the common real factor $\chi(k/R)^{2c(q,q')}$. It remains to prove the tuple identity for the common real profiles $F^{[R]}$.

Use the expansion T1252–1265. A term is indexed by an enhanced lone-pair class and by the multiset of extended tuples $(r,I,c,\mathcal X_1,\mathcal X_2)$. Replacing a real profile by another common real profile changes the spatial factors $\mathcal M[\mathcal X]$ and $\mathcal M[\mathcal Y]$, but not the time factors or their equivalence classes. The product of spatial factors is

$$
\mathcal M[\mathcal X_{\mathrm{lp}}](k)
\prod_{j=1}^m\mathcal M[\mathcal Y_j](k),
\tag{5.5}
$$

independent of how the tuples are distributed among the plus, minus, and regular-tree chains. The sign product is also unchanged, exactly as in T1269–1271. This argument uses a common profile; a separately labeled modification of one chosen leaf would not have this invariance.

If a side special set or the lone-pair special set is nonempty, sum its enhanced couple over its equivalence class. The time-factor cancellation `regref2-3` is unchanged, while (5.5) is constant on that class. The result is zero. It remains to treat trunk special sets. For an empty special set all factors in T1156–1167 are real after the paired branching signs are included, so its contribution is real.

For a nonempty trunk special set, label all occurrences of equal tuples temporarily. For a fixed ordered list of their merged times $t>v_1>\cdots>v_m>q'$, each occurrence with $v_j<s$ can belong to the plus or minus chain, and each occurrence with $v_j>s$ can belong to the plus or regular-tree chain. The common time factor is the product of the tuple time factors and the lone-pair factor at $\min(v_m,s)$; none depends on that choice. The sum of the signs over these choices is

$$
\prod_{j=1}^m\bigl(1+(-1)^{I_j}\bigr)=0,
\tag{5.6}
$$

since at least one $I_j=1$. Equal times have Lebesgue measure zero and do not affect the integral. The layer indicators are retained in the tuple time factors, so illegal layer orderings contribute zero.

To remove the temporary labels, let $m_\tau$ be the multiplicity of tuple type $\tau$. Every unlabelled assignment to the ordered chain positions has exactly $\prod_\tau m_\tau!$ labelled lifts. This number is independent of the chain allocation and of the times. Dividing the zero labelled sum by this number gives the unlabelled sum. If permutations in T are instead interpreted as permutations of a labeled sequence, division is unnecessary and (5.6) already proves the result with that convention. The $2^m$ choices of second code digits in T1273 have no dependence on the spatial profiles and give the same common factor on both sides. Fixing total order or combined top-layer count restricts the multiset, not these allocations, so introduces no extra multiplicity.

This proves (5.4). Each fixed-order sum is finite in combinatorial indices and is a smooth function of $R>0$; the spatial integrals and their derivatives are dominated by the finite weighted profile bounds and the corresponding source estimates. Differentiating its real-valued identity therefore gives a real-valued identity. This derivative is the **sum of all product-rule terms**, not any one chosen marked term. ∎

### Lemma 5.3 — Local weighted `vineest`

Consider the unpinned (CL) vine-chain expression of T1742–1750. Suppose its realization lies in one original tree, all frontier cutoffs inside it have a common scale $R\ge L$, and the full LF class is summed with the order and top-layer constraints of that proposition. Do not impose a distinguished leaf mark or a selected-time endpoint face inside this realization. With $h$ frontier factors, its low-pass weighted version satisfies

$$
\|\widetilde K_R^{\mathcal U}\|_{X^{2\eta^8,0,0}}
\lesssim_1 C_\chi^{n_{(2)}+h+1}(1+n_{(2)}+h)^{C_d}
(C_1\sqrt\delta)^{n_{(2)}}
L^{-\eta^8n_{(3)}-\eta^2b/2+\eta^7}.
\tag{5.7}
$$

The constants in the extra exponential depend on $d,\chi$, not $\delta$. An additional amplitude can be inserted after reduction to each `sumint` expression if it satisfies Lemma 4.2; its cost is its total-variation bound. This last assertion does not authorize an arbitrary amplitude before the LF cancellation.

**Proof.** In the reductions T1753–1881, attach to each regular object its assigned frontier factors. For an incoherent object use Lemma 4.1; its incoherency gain is unchanged. For a coherent object use (5.2), the single-layer profile estimates T1145–1174, and the layer factorization T1235–1244. These operations supply the same approximation and remainder decomposition with modified real profiles. The original frontier is determined by layers: it consists of layer-$p$ leaves and vertices below layer $p$ whose parents are in layer $p$. Outside the two coherent objects exchanged in the LF step, the frontier vertices and their momenta are carried by the decoration permutation, as in T1877. Thus no additional frontier factor is omitted. Their constants increase by $C_\chi$ per input and a polynomial of fixed degree per differentiated factor. Products of local polynomials are bounded by an exponential in the total number of local vertices and frontier factors.

For the equal-upper-layer cancellation T1883–1907, replace the two spatial arguments by the same argument before using the leading identity. Differences of ordinary spatial factors are handled as in T1902. Differences of new factors are handled by Lemma 3.2: the argument difference is $\pm r$, so they supply the required explicit $|r|$ for case (b) of `sumint`. Their remaining amplitudes have the stated Fourier-measure bounds. The leading sum is zero by Lemma 5.2, since it is the difference of a real number and its conjugate. The time-interlacing and time-Hölder errors are unchanged; multiplication by the time-independent factors preserves their bounds.

For unequal upper layers, use the time extensions in T1915–1920 with the E18 correction: the trivial factor is its exact $F\mathbf1_{t>q}$ kernel, and floor vanishing is used only for the nontrivial factors. The mixed-family identity is needed only off the boundary null set. Separated intervals supply the source's time-Hölder factor. In adjacent intervals, replacing the upper time by the lower time again produces that factor; the remaining sum is restricted to the common lower-root family in T1921. Keep incoming frontier factors assigned using the *original* parent layers. Their combined exponent is $c(q_1,q')+c(q_2,q')$, unchanged when the couple and tree are exchanged. At the common spatial argument their product is real and common to the two sums. If $q_1=p>q_2$, the surviving lower-root family has no internal layer-$p$ tuples, but the single incoming factor $\chi(k/R)$ must still be retained. The remaining common family is covered by Lemma 5.2. This accounts for the upper-layer mismatch without losing a frontier factor.

All uncanceled cutoff factors on the remaining alternative variables satisfy Lemma 4.2. Apply that lemma to each resulting expression, keeping its bad-vine alternative, and use the same order accounting and incoherency accounting as T1923. Reserve half the bad-vine gain for the late-constant class multiplicity in T1909 (E25); the other half is the exponent displayed in (5.7). For leaf lower children evaluate at the layer floor and take the order-zero trace (E14). Retain degeneracy factors by their character mixtures of mass at most $3^n$ and Lemma 4.2 (E4), rather than trivially summing a long restricted chain. These changes have fixed exponential cost only. This proves (5.7). ∎

Lemma 5.2 resolves the tuple issue for the actual common low-pass product. It does **not** prove a reality identity for arbitrary independently marked profiles. That stronger assertion is neither used nor claimed.

## 6. A single common-profile extrapolation

The profile class used downstream is
\[
 \mathcal P(C)=\{(G_q):G_q\text{ real},\ \sup_q\|G_q\|_{\mathfrak S^{40d,40d}}\le C\}.
\]
It has no heavy-decay requirement. The true inputs additionally have the heavier bounds supplied by T606–615. All estimates below are uniform over this class; finite differentiability suffices, by smooth approximation in the lower norms actually consumed.

### Theorem 6.3′ (O63, revision 2)

Fix order $n$ and any of the complete garden or LF sums in this proof. Write its profile-independent multiplier, including pins, cutoffs and optional dagger indicators, as $\Theta$. There are exactly $n$ noncap final pairs, so
\[
 S_\Theta[G]=\sum_\kappa\Theta(\kappa)\prod_{\pi}G_{q_\pi}(k_\pi),\qquad
 B_\Theta(C)=\sup_{G\in\mathcal P(C)}|S_\Theta[G]|,
 \quad B_\Theta(aC)=a^nB_\Theta(C).
\]
There are constants $D$ independent of $\delta$ and $C_{P,\delta},A_{P,\delta}$ independent of order and scales such that the true-profile sum is bounded by
\[
 D^nC_{P,\delta}(1+n)^{4\Lambda P}\langle k-\zeta k'\rangle^{-4\Lambda P}B_\Theta(C_1). \tag{6.1}
\]
On a positive first shell, the bound is
\[
 D^nC_{P,\delta}(1+n)^{(8\Lambda+80d)P}
 \langle k-\zeta k'\rangle^{-4\Lambda P}M_1^{-80dP}B_\Theta(C_1). \tag{6.2}
\]
There is **no additional power of $L$ and no marked leaf**.

**Proof.** Put $K=|k-\zeta k'|$, and let $C_\sharp(A)$ bound the true profiles in $\mathfrak S^{40d,40d+A}$. The choices $A=4\Lambda$ and $A=4\Lambda+80d$ are available since $40d+A\le\Lambda_p$. Set
\[
 w_{\rho,z}(u)=\chi(u/\rho)+z(1-\chi(u/\rho)),\quad
 Z=\rho^AC_1/C_\sharp(A),\quad z_r=rZ/n\quad(0\le r\le n).
\]
For $\rho\ge1$ and $Z\ge1$, the common real profiles $G_{q,r}=F_qw_{\rho,z_r}$ belong to $\mathcal P(2c_\chi C_1)$, where $c_\chi=2^{40d}\max_{|a|\le40d}\|\partial^a\chi\|_\infty$ enlarged to be at least one. This follows by the product rule, using the extra decay on the transition and exterior region.

Signed momentum conservation in each original tree gives $k-\zeta k'=\sum_{\ell\ne f_j}\epsilon_\ell k_\ell$. For external decay take $\rho=K/(4n)$. For a first shell take $\rho=M_1/(8n)$. In the latter case first propagate a high frontier momentum to a final descendant leaf. In either case every original tree has a nonflower final leaf with $|k_\ell|\ge2\rho$. A pair accounts for at most two trees. Thus at least $P$ final pairs have $w_{\rho,z}=z$.

For each decoration the polynomial $\Pi(z)=\prod_\pi w_{\rho,z}(k_\pi)$ has degree at most $n$ and is divisible by $z^P$. Define
\[
 \ell_r(x)=\prod_{s\ne r}\frac{nx-s}{r-s},\qquad
 \beta_r=\sum_{i=P}^nZ^{-i}[x^i]\ell_r(x).
\]
Polynomial interpolation gives the **termwise identity**
\[
 \Pi(1)=\sum_{r=0}^n\beta_r\Pi(z_r),\qquad
 \sum_r|\beta_r|\le {2n\choose n}2^nZ^{-P}\le8^nZ^{-P}. \tag{6.3}
\]
For the inequality, take absolute coefficients of $\prod_{s\ne r}(nx-s)$ and divide by $r!(n-r)!$; sum over $r$ and use $Z\ge1$. The coefficients are independent of decoration, pairing and LF allocation. Consequently (6.3) holds before all cancellations and integrations, with the same coefficients for a complete class. Homogeneity supplies $(2c_\chi)^n$, and $Z^{-P}$ supplies the decay. On the first shell, conservation also gives $K\le4nM_1$; allocating $4\Lambda P$ of the $A P$ powers to this inequality gives (6.2). If $\rho<1$ or $Z<1$, then $K$ or $M_1$ is bounded by $C_{\delta}n$; the trivial profile bound proves the same estimate after enlarging $C_{P,\delta}$. This proves the theorem. Full coefficient estimates and the small-$Z$ case are O63 Lemmas A–D and Theorem 6.3′, §§2–4.

The frozen product cutoff uses a different fixed dilation of $\chi$: its positive shell lies between $M_1/4$ and $M_1$. O63 Remark 2.1 applies with $\rho=c_-M_1/(4n)$ and $K\le2nc_+M_1$. Only $C_{P,\delta}$ changes. No smooth function of a maximum is substituted for this product cutoff.

## 7. The retained marked vines and the counting reduction

### Theorem 7.5′ (O75, revision 1)

In each original tree protect its root, up to three children, the flower, its parent, and its two siblings. For a positive second shell also protect its selected stem vertex, its parent and its children. Thus $b=|\Pi|\le26P$. Caps have no branching descendants and need no additional mark. For patterns in Section 11 add at most two vertices per original tree, giving $b\le30P$.

For a (CL) vine, its twist-active set consists of its realization except its top vertex, together with its attached regular objects. These sets are disjoint for the twist collection; therefore at most $b$ vines are marked. Marked vines are neither twisted nor spliced. Splice only unmarked small-gap runs. Their hinges form $H$, with exactly the original $q_{\rm sk}$ hinges. The surviving small-gap vines in affected chains form $\mathcal C_E$. Their joints form $B$. Then
\[
 N_E=|\mathcal C_E|\le2b,\quad |B|\le4b,\quad
 |\Pi_{\rm sb}|\le2b,\quad |S_{\rm split}|=|B\cup\Pi_{\rm sb}|\le6b. \tag{7.1}
\]
The resulting graph is the molecule of a genuine connected irreducible garden. If its width is $2R$, it has $v$ atoms, $2v-R$ bonds and cycle rank $v-R+1$. For all capped components together, $\sum R=2P$, not $P$.

Here is the full structural content used in the count (O75 §3, with the §11 amendments).

1. Connectedness and the preceding counts are unchanged. All original truncation and layer labels remain attached.
2. The ordinary disjoint collection $\mathcal C_1$ remains; survivors $\mathcal C_E$ can meet only at consecutive joints. The hinge count is $q_{\rm sk}$. Triple bonds have a hinge endpoint.
3. On the support $\widetilde\epsilon\mathcal Z\ne0$, every degenerate nonhinge atom is tame. Here $\widetilde\epsilon=\prod_{v\notin H}\epsilon_v$: in particular, the factors at protected atoms, survivors and joints in $B$ are retained.
4. An uncovered small-gap vine-like object avoiding $H\cup B$ is contained in a DV, LG or ZG object disjoint from the retained collections, with the `subsetvc` case distinction of T2045 retained.
5. Each genuine hinge has its designated small-gap pair in $\mathcal C_1\cup\mathcal C_E$. Every shared joint in $B$, even a nonhinge joint, also has a designated pair in a survivor that is removed first. This is a designated-pair property, not a declaration that the joint is a hinge.
6. The hinge-configuration assertion of T2047 is retained: an uncovered small-gap object avoiding $B$ and meeting a hinge has the unmatched hinge configuration used at T2104.
7. An object meeting $B$ is contained in a survivor, contains a survivor bond, or has the hinge configuration. It is destroyed by the survivor removals. A one-survivor hyper-vine is removed as an HV, including its additional bond.
8. Split every ladder at $H\cup B\cup\Pi_{\rm sb}$. The interiors of retained pieces have no protected amplitude dependence. Their gains and frontier factors are controlled by Section 8.3.
9. Stage 2 first removes ordinary CN/root-CL objects, then ordinary HV objects, then survivors one vine at a time, then $\mathcal C_2$, before proceeding with the remaining source operations. Isolated halves at a re-cut degree-two joint retain their original labels; a label is refunded only once, when its final isolated component is removed.

**Proof and quantitative content.** O75 Lemmas 1–2, §2.3–2.4, prove disjointness and invariance under the permitted twists. A mark in a chain leaves at most the two adjacent survivors, proving (7.1). The vine classification and bond-by-bond verification are O75 §§4.1–4.7, with corrections §11.1–11.4; these proofs are incorporated here. They retain the original garden, so they do not invoke an excision formula or a count for a newly disconnected boundary graph. In the hyper-vine case the full HV removal has $\Delta F=0$. A re-cut joint has $\Delta F=1$ and defect increment two; the isolated half is recorded and its cost is at most $L^{\gamma_0+2\eta^3}$. For a live hitting constraint its center is held at creation; a deleted hit supplies no later ball restriction.

There are at most $2R-1+N_E$ component-creating Operation-1 removals. The new imperfect components are charged to the survivors. In the $R=1$ case a component may contain a degree-three root; it has a label and $Z\le2\,\#\text{labels}$. The imperfect bound $L^{-\eta^4\rho+C_0\eta^2(\#\text{labels}+Z)}$ is absorbed by the existing $\alpha$ and $\beta$ label allowances when $\eta$ is small. No assertion excluding low-degree atoms is needed. Thus the extra sharp-count cost is
\[
 L^{(3\gamma_0+5\eta^2)N_E}\le L^{2N_E}\le L^{4b},\qquad \gamma_0=1-\gamma<1/2.
\]
Each additional ladder split costs at most $L^{60d+2}$. The resulting crude-bound cost is at most $L^{(360d+12)b}$. Combining them gives
\[
 L^{(360d+16)b}. \tag{7.2}
\]
No power depending on the order is introduced. The source gains on protected regular objects are retained by Theorems 7.3′ and 8.2′ below. Splitting loses at most $22b$ of the count's gain incidences; this bound includes all harmless overcounts in O75 §8. More precisely use $g_{\rm ret}\ge0$ and $\ell=g-g_{\rm ret}\in[0,22b]$. Never substitute a negative number for a retained gain count. Then
\[
 C_2^gL^{-\nu\eta g_{\rm ret}}=C_2^\ell(C_2L^{-\nu\eta})^{g_{\rm ret}}\le C_2^{22b}
\]
for sufficiently large $L$. The remaining $C_2^{O(b)}$ is an order-independent constant. This proves the form required in Section 10. ∎

## 8. Analytic estimates with the actual protected incidences

### 8.1 Theorem 7.3′: pins, individual faces, and residual selected frequencies

For the geometry and marks of Section 7, the pinned and individual-face estimates used by the count hold with total extra cost
\[
 L^{400db}\le L^{10400dP}\quad(b\le26P). \tag{8.1}
\]
They keep every original regular-object incoherency gain. They cover flower-parent pins, terminal, top, parent, stem-child, side-child and floor faces, with upper faces reunited over the maximizing-child cells and lower faces treated cell by cell, and the off-stem same-layer child face $F_{\rm ch}$ needed by `dChild`. They also cover still-integrated selected residual frequencies. The assertion is about these actual objects and their consumers; it is not a uniform positive-time-weight estimate for every arbitrarily punctured layered chain.

**Proof summary with the analytic interfaces explicit.** O73 Proposition 3.1 shows that a regular couple meeting the flower stem contains the cap, so one half is trivial and the other lies in a single original tree. A paired tree meeting the stem is rooted on it and has its lone port on it. The chain and its linked partners have layer $p$; layer incoherencies occur in its side couples. Thus arbitrary cross-layer linked punctures do not arise.

The elementary terminal operator is
\[
 T_AH(t,s)=\int_s^t e^{\pi iA(u-s)}H(t,u,s)\,du.
\]
On a Fourier atom it produces $e^{\pi i[\xi t+(\lambda+\nu)s]}h_{A+\lambda}(t-s)$, where $h_z(v)=(e^{\pi izv}-1)/(\pi iz)$, continuously interpreted at zero. With time cutoffs its Fourier norm of weight $0\le\theta\le1$ is uniform in the fixed real parameter $A$ (O73 Lemma 12.1). This does not justify interchanging an output supremum and a Fourier integral. The actual final-pair cut is the exact identity
\[
 \int_s^t e^{\pi iA(u-s)}K_{\rm pre}(t,u)K_{\rm in}(u,s)Q_1(u,s)Q_2(u,s)\,du. \tag{8.2}
\]
The legal noncrossing pairing makes the prefix and interior complete chains. These four ordinary pieces have total half-order one less than the original and retain all side gains (O73 Proposition 13.1). The exceptional pair's two normalizations and its $O(L^{2d})$ local tuples cost at most $L^2$. Extending local lattice-output values by disjoint bumps $\psi(L(k-k_0))$ costs $L^{31d}$ for $30d$ derivatives, once per protected object.

Root traces at a root in layer $p$ require their boundary phase to remain explicit. This layer hypothesis holds for every maximizing side root and every valid `dChild` here. The remainder can depend on a third boundary time, namely the port or floor. Write
\[
 Q_\rho=e^{\pi i\epsilon B(\sigma-q)}R_B,
 \qquad T_A[e^{\pi i\epsilon Bu}R_BQ_2]
 =e^{\pi i\epsilon Bs}T_{A+\epsilon B}[R_BQ_2].
\]
Only $R_B$ has a uniform positive-weight bound. The exterior phase is evaluated at a fixed time or passed as an exact frequency shift to the residual integral. For a paired tree in the same layer the lower endpoint is its lone-port time, not the layer floor. After integrating side objects first, the punctured-chain expansion of O73 Lemma 19.1 has the form
\[
 e^{\pi i\ell_E\cdot\tau}\sum_Z\prod_{j\in Z}
 \frac{\chi_\infty(\alpha_j)}{\epsilon_j\pi i\alpha_j}
 \int C_Z(\lambda,\alpha_J;\Lambda,E)e^{\pi i\lambda\cdot\tau}\,d\lambda. \tag{8.3}
\]
Its consumed coefficient norm is time weight **one**, with all required spectral derivatives. Before applying the discrete theorem, its coefficient estimate is taken at fixed side-frequency parameter $\Lambda$, with the derivative bound factorized in $\rho$ and a spatial-amplitude mass $D(\Lambda)$. Apply O82 Theorem 10.1 at fixed $(E,\Lambda)$ and integrate against that mass only afterwards; its bound is linear in the coefficient and amplitude. A fixed time cutoff converts the line-supported output Fourier measure into a density. The resulting integrated bound is
$C_{P,\eta}^{m+|\rho|+1}(4|\rho|)!(C_1\delta)^{m_{\rm side}}L^{-c_g g_{\rm side}}$ uniformly in the exceptional parameters. The poles are restored in their original coordinates. In the class-$J/R$ recursion use $\kappa=\eta/16$: the pole-translation difference has $L^1$ norm at most $C\log(2+|c|)\le C_\kappa\langle c\rangle^\kappa$, and the at most eight endpoint charges fit within the ordinary $\eta$ weight. No spectral-moment or principal approximation of a protected block is asserted.

For completeness the residual bound used to consume (8.3) is O73 Proposition 18.1. If at most $r$ original frequencies are fixed, pinned or left selected (allowing a bounded number of pins and at most one selected substitution per original tree), its mixed sum/supremum over available unit boxes is at most
\[
 C_r^{N+1}L^{4r}(C_1\delta^{-1/2-5\nu})^N
 L^{\delta^{5\nu}\rho_{\rm sb}}\prod_jX_j^{z_j}. \tag{8.4}
\]
The exceptional frequencies are taken in supremum, not integrated. Differentiate the full dephased expression of T2005 before estimating it. Removing at most $4r$ incident $X$ variables loses only $(N+1)^{4r}$. On the remaining forest the source minimal-$Y$ integrations give translated factors $\langle\alpha+c\rangle^{-1}$. A union of at most $L^{20d}$ available intervals has integral $O_d(\log L)$ uniformly in its center; at most $4r$ such costs give $L^{4r}$ for large $L$. This proves (8.4) without a false supremum-to-integral conversion. Finite spectral fibers can later be restored: a localized resonance has at most $(C_dL)^{4d}$ values, and integration over $Q$ intervals of length $c$ is bounded by $(cQ)^r$ times the exceptional supremum. Support restoration is separately charged in Section 10.

O73 Proposition 19.2 applies this machinery to each lower raw face, and to the upper face after summing its same-sign maximizing-child cells, without a reciprocal or an annular assumption. Before that reunion an upper cell can couple an internal side-root time to another side kernel, so an individual upper cell is not asserted to have (8.3). If the child face lies in a separate regular object (O104 case P8), its chain may have several layers: use the root-trace representation with four ordinary factors under $T_B$, not the single-layer punctured-chain formula. At most two exceptional linked pairs occur per incidence. Four side cuts, exceptional tuple sums and possible lost-pair restoration cost at most $L^{6r}$; local output extension gives
\[
 L^{(31d+6)r}\,G(O)
\]
in the consumed $X^{0,30d,0}$ norm. In particular $F_{\rm ch}$ fixes an off-stem branching sibling to $s$ and drops its inequality against its already pinned parent, while keeping every inequality involving a free variable. It is included individually, not merely in a signed derivative sum.

Finally O73 Proposition 20.1 proves the selected residual gain. Write $\beta_v=\delta L^{2\gamma}(-\Gamma_v+\Gamma_v^0)$ and $\alpha_v=\beta_v+\xi_v$. On $|\beta_v|\ge c\delta L^{2\gamma}M_2$, split at $|\xi_v|=|\beta_v|/2$. In the large-$\xi_v$ part the adjacent ordinary factors' $X^{1/4}$ norms supply $M_2^{-1/18}$; each factor meets at most two selected endpoints, and $2/18<1/4$. In the complementary part integrate by parts in the full total frequency $\alpha_v$, after Fourier expansion, and use (8.4) on every resulting face. At most seven adjacent factors occur per vertex. The gain therefore holds in both the coarse analytic and fine counting bounds, at cost
\[
 L^{7(47d+2)a+4r}M_2^{-a/18}.
\]
Every selected vertex and its child recipients are protected. A residual parent recipient need not be protected: a nontrivial attached tree can separate it from the protected raw parent. If this recipient lies inside a retained ladder, the new phase and remaining order indicators are independent of that ladder’s internal momenta, since the selected frequency depends only on bonds at the protected selected atom. They therefore come outside the absolute decoration sum in the unordered box core with modulus at most one. This is REFEREE-73 fix 73-REC and costs nothing. No unmarked spliced vine is an adjacent uncontrolled factor. Combining the regular and residual allocations gives
\[
 (47d+6)r_{\rm reg}+7(47d+2)a_{\rm res}+4r_{\rm res}
 \le(329d+18)b<400db.
\]
This proves Theorem 7.3′. The detailed recursions and their dependency check are O73 §§17–21; only the geometry and terminal identities §§3,12–13 are used in the independent part of O82. ∎

### 8.2 Theorem 8.2′: upper filters and whole protected regular objects

Fix an even real Gevrey-2 cutoff $\vartheta$, with $0\le\vartheta\le1$. The second product shell is
\[
 U_{j,M}=\prod_{v\in\mathcal S_j}\vartheta(\Omega_v/M),\quad
 V_{j,M}=U_{j,M}-U_{j,M/2}\ (M>L),\quad V_{j,L}=U_{j,L}, \tag{8.5}
\]
where $\mathcal S_j$ omits the flower parent. An empty positive shell is zero. For a linked spectral variable the cutoff scale is $S=\delta L^{2\gamma}M\ge1$ for large $L$.

Unprotected regular objects with these upper filters satisfy the ordinary estimates and coherent principal approximations, with the same leading term and gains. Protected objects are retained whole: their actual pins and signed face collections, with $a$ selected occurrences, satisfy the consumed local-output estimate with additional factor
\[
 L^{(47d+5)b_O}G(O)M_2^{-a/18},\qquad b_0+a\le b_O. \tag{8.6}
\]
Here $G(O)$ is the product of **all original** incoherency gains. A cap object has fixed output $k'$; it is not required to have global decay in the other external root. Summing $b_O\le b$ gives $(47d+5)b$, or $(1222d+130)P$ in the plain case. There is no gain on a residual selected frequency from this theorem; that is Proposition 20.1 above.

**Proof summary.** Multiplying the D23 965–967 integrable coefficients by at most two cutoffs per spectral coordinate preserves their bounds, replacing $(2|\rho|)!$ by $C^{m+1}(4|\rho|)!$. The product rule and $(2a)!(2b)!\le(2a+2b)!$ prove this directly. The moment bound is unchanged because the cutoff is at most one; restriction to $|\alpha|\ge S/2$ gives $S^{-(1-\eta/2)}$. Extracted poles instead require the discrete argument: $g_S(\alpha)=\chi_\infty(\alpha)\alpha^{-1}\prod\vartheta(\alpha/S)$ has uniform weighted Fourier controls, but does **not** have uniform $L^1(d\alpha)$ norm. O82 Theorem 10.1 applies simultaneous major/minor box decomposition in the independent linked variables of T1002–1017. If $f$ coordinates are minor, the derivative factorial $(8qf)!$ is absorbed per minor coordinate using $\log n/\log L\to0$, for $n\le N^4$. This yields neither $L^{\epsilon n}$ nor a $\delta$-dependent exponential base. Exclusions $x=0$ or $y=0$ vanish for the pole part and cost $\mu L^{-d}$ for the integrable part; $d-2\gamma>1$ pays this loss.

In the continuum comparison (O82 Lemma 11.2), the pushforward density under $x\cdot y$ has Fourier decay $|s|^{-d}$, uniformly under modulation, and is $C^1$ for $d\ge3$. The even cutoff preserves the principal value. Its tail changes the answer by $O(\mu^{-1}+L^{-1})$; the integrable coefficient's tail is controlled by its spectral moment. Interpolation gives the original $L^{-\gamma_1+\sqrt\eta}$ error. An incoherent side pair has density vanishing at the resonant origin; Fourier translation by an upper filter preserves the resulting gain.

For selected faces, the raw bound is $L^{3r}M_2^{-a}G(O)$ times the usual order factor. The strong bound is $L^{16d+2}G(O)$ in time weight $1/4$. For a **couple** the latter is $X^{1/4,30d,30d}$, including output decay: this is essential to sum exceptional-box centers through its two side couples (or the profile for a trivial side). For a tree there is no output decay. Use the per-frequency majorant independent of the output supplied by Theorem 10.1, so that the output supremum can remain inside the Fourier integral. These are fixes F2 and F3 of REFEREE-82, §§3–4.

Extend the square/triangle functions boundedly, with five folds costing $1/40$ each in the strong time exponent; interpolate $L^\infty$ with $A^{1/8}$ to obtain $A^\eta$. The raw bound's interpolation share is $(1-8\eta)/9\ge1/18$ for $\eta\le1/16$. Since both bounds carry the same $G(O)$, interpolation retains it to power one. Add the $L^{31dr}$ local output extension from Section 8.1 to obtain (8.6). The full proof is O82 §§10–18, assembled as Theorem 8.2′ in §19 and corrected as above. ∎
### 8.3 Theorem 8.3: filtered ladders and the box-robust core

Let a retained ladder have $m+1$ double bonds, $2m+2$ atoms and $4m+2$ internal bonds. Each localized bond factor has $C^{30d}$ norm at most $A$. Allow at any subset of atoms factors $\psi_v(\Omega_v/R_v)$, $R_v\ge1$, with
\[
 \mathfrak b(\psi)=\int(1+|\xi|)^2|\widehat\psi(\xi)|\,d\xi<\infty.
\]
The unordered kernel core (absolute value of the decoration sum **inside** the time integral) obeys the source ladder estimate with the additional factor $A^{4m+2}\prod_v\mathfrak b(\psi_v)$, the same incoherency gain, and the existing per-ladder allowance $L^{20d}$. Thus there is **zero additional flower $L$-cost**. This statement does not erase the ordinary $L^{20d}$ cost already charged by the source's ladder count.

**Proof of the required box estimate and its filtered form.** O83 Lemma R and Theorem K (§§4.2–4.4) give the following stronger intermediate assertion. On any product of unit intervals $I_v$, the unnormalized core is at most
\[
 A^{4m+2}C^mL^{4d}\prod_{j=1}^{m-1}\mathsf B_j,\qquad
 \mathsf B_j=\delta^{-1}L^{2(d-\gamma)}
 \min\{1,L^{-(\gamma_1-\sqrt\eta)}+|I_{v_j}\cap I_{w_j}|\}, \tag{8.7}
\]
when the indicated intervals lie in $[-1,\mathfrak D+1]$. Always $\mathsf B_j=C_dL^{2d}$ is available. End filters contribute their supremum norms. This is exactly O75's formerly conditional hypothesis (E5′).

To verify factorization, fix **both end double bonds**, costing $O(L^{4d})$. Interior rungs have variables $x_j,y_j$, with phases
\[
 \Gamma_{v_j}=2x_j\cdot y_j,\qquad
 \Gamma_{w_j}=-2x_j\cdot y_j+2\rho_j\cdot\lambda_j(x_j,y_j)+\kappa_j,
\]
where $\lambda_j$ is one of $\pm x_j,\pm y_j,\pm(x_j\pm y_j)$ and $\kappa_j$ is constant. The one remaining vector conservation law is $\sum_j\lambda_j=c_{m-1}-c_0$. On the finite localized lattice its indicator is the normalized average of characters of a sufficiently large finite torus. This has total variation one and separates the rungs. Fourier-expand the smooth bond factors, also at uniformly bounded total variation. For fixed characters and modulations, the interior sum now factors exactly. End rungs may have degree-three atoms and need not obey the displayed bilinear formula; they are only counted.

The nonsmooth $\epsilon_v\mathcal Z_v$ factors are retained. Expanding them gives a bounded number of rung terms with ball indicators in $x+\theta r$ or $y+\theta r$, radius at most $L^{-\gamma+\eta}$, and excluded zero vectors. For smooth terms, major-arc Poisson summation gives $L^{2d}\langle s\rangle^{-d}$ and the minor arcs use D23 Lemma 6.6(2). The overlap density of the two time intervals is bounded by $\min(1,|I_v\cap I_w|+|s|/\mu)$, $\mu=\delta L^{2\gamma}$, proving the corresponding rung factor in (8.7). If only $x$ is restricted to a small ball, retain the oscillation in $y$: the periodic-line bound is $L^d(L^{-1}+\mu^{-1}|x|^{-1})$ for $x\ne0$. Summing over the ball uses
\[
 \#B\lesssim(1+L\rho)^d,\qquad
 \sum_{x\in B,\ x\ne0}|x|^{-1}\lesssim L^d\rho^{d-1}+L.
\]
The zero-vector term is $O(L^d)$ separately. If both variables have ball restrictions, their cardinalities suffice. For $d\ge3$ and $\gamma>1/2$ these bounds give the same gain, after the stated $\sqrt\eta$ allowance. Constants depending on the finite layer range are absorbed in the small exponent **before** multiplying rung bounds, not into a forbidden $C_2^m$. This proves (8.7); the complete major/minor estimates are O83 Lemma R, steps 1–3.

Fourier expansion of a resonance filter translates $t_v$ by $2\zeta_v\xi/(\mu R_v)$; the $\Gamma_v^0$ term produces only a unit phase. For $|\xi|\le\mu/4$, apply (8.7) to the translated intervals. The overlap of previously disjoint adjacent layers grows by at most the sum of the translations, paid by the moment in $\mathfrak b$. On $|\xi|>\mu/4$, use the trivial rung count and the second Fourier moment. Its factor $\delta^{-2}L^{2d-4\gamma}$ is smaller than the required rung bound for large $L$. This proves O83 Theorem 8.3 and O75 Lemma F with a fixed, $\delta$-independent cutoff constant.

O83 normalizes by $(\delta/(2L^{d-\gamma}))^{2m+2}$, whereas T1980 uses exponent $2m+1$. The conversion factor is $2L^{d-\gamma}/\delta$; the resulting end loss $2\delta^2L^{d+3\gamma+2}$ fits inside $L^{20d}$. At most two frontier factors occur on a bond, so Section 3 gives $A\le c_\chi^2$. Factors strictly inside a spliced vine instead belong to Lemma 5.3. The weighted coarse bound is O83 Corollary 8.3.A. The fine absolute count can drop the upper filters; interpolation with share $40\nu/(1+20\nu)$ gives precisely the source order factor and retained gains. This completes the proof. ∎

## 9. The second shell and the positions of its filters

### Lemma 9.1: exact raw faces

For a raw decorated garden, a selected unpinned stem time $u_v$ ranges from the maximum of its layer floor and its constraining branching-child times to its parent time or the external top time. Partition according to the maximizing lower endpoint. There are at most four choices. If $|\Omega_v|\ge cM_2$, then
\[
 \int_{A_v}^{B_v}e^{i\omega_vu}\,du
 =\frac{e^{i\omega_vB_v}-e^{i\omega_vA_v}}{i\omega_v},\qquad
 \omega_v=\pi\zeta_v\delta L^{2\gamma}\Omega_v. \tag{9.1}
\]
Keep $A_v<B_v$ and all other inequalities, and add the selected frequency to the endpoint phase. For $a$ selected vertices in different original trees this gives at most $8^a$ individual faces and reciprocal bound $(\pi c\delta)^{-a}L^{-2\gamma a}M_2^{-a}$. Vertices in different trees share no time-order inequality, so the operations commute. All spatial cutoffs remain. This proves the raw identity; it is not a bound for a collapsed oscillatory sum. In the residual reduction the adjacent Fourier variables change the integrating frequency to $\alpha_v=\beta_v+\xi_v$, and **O73 Proposition 20.1**, not the bare reciprocal in (9.1), supplies the gain.

For a positive second shell, differentiate $U_{j,R}$ in $R$ and integrate $R$ from $M_2/2$ to $M_2$. This chooses one annular occurrence in each original tree, while retaining the other upper filters. The coefficient integral is bounded independently of $M_2$ and the number of choices is polynomial in $n$ for fixed $P$. Its selected profile $-u\vartheta'(u)$ has the Fourier moments used in Section 8.3. A linked pair may be selected at both vertices; occurrences, not distinct frequencies, are counted. Section 8.2 supplies at least $M_2^{-1/18}$ per regular occurrence, Section 8.1 the same per residual occurrence. There are $2P$ occurrences, so their product is $M_2^{-P/9}$.

### Lemmas 9.2–9.4: high-root separation, affine tops, and absolute counting

On a first low-pass term with scale $R\le M_1$, each original nonflower frontier momentum has size at most $2M_1$. If there are $b_j$ such vertices, conservation gives size at most $2b_jM_1$ for an off-stem vertex of the **original top tree**, or for a lower insertion's frontier root. A stem momentum has size at least $|k|-2b_jM_1$. Since $b_j\le2N^4+1$ and $|k|\ge M_1^{10}$, these are separated by $|k|/2$ for large $L$. No bound for all internal descendants of a lower insertion is asserted.

A spliced SG chain is unmarked, so its active realization contains neither the flower nor its parent. If the flower descends from its top $u_1$, it therefore descends from $u_{11}$, $u_{21}$ or $u_{22}$. It cannot descend from either of the latter two: the other is off the stem, contradicting their small gap. Hence it descends through $u_{11}$, which lies outside the realization. The only stem vertex in the realization is its **top**. This marking sentence is necessary; high-root separation alone would not exclude a flower inside the realization.

At that top write its momentum $e=f+r$ and the child momenta, in sign order, $f,a,a+r$. Then
\[
 \Omega_{\rm top}=2r\cdot(a-f),\qquad
 \vartheta(\Omega_{\rm top}/M_2)
 =\int\widehat\vartheta(\xi)e^{-4\pi i\xi r\cdot f/M_2}
 e^{4\pi i\xi r\cdot a/M_2}\,d\xi. \tag{9.2}
\]
This is an admissible Fourier-measure amplitude in $a$, uniformly in the outputs $r,f,M_2$. Its first derivative costs $2|r|/M_2$ times a fixed Fourier moment. The top and its resonance are unchanged under the permitted LF twists, so this amplitude is common to the class before Lemma 4.2 is applied. It does not authorize treating a quadratic regular-chain resonance as an affine amplitude.

The locations of every upper filter are now exhausted: inside a regular object use Theorem 8.2′; at an unmarked spliced top use (9.2); inside a retained ladder use Theorem 8.3; at other residual atoms retain it until the relevant absolute count and then use $|\vartheta|\le1$. Protected faces and residual selections use Theorem 7.3′. Dropping a bounded factor before an oscillatory cancellation is not allowed.

### Lemma 9.5: bottom blocks

A bottom first block has no annular extraction. Pay $L^{80dP}$ and write $L^{80dP}M_1^{-80dP}=1$ for $M_1=L$. Similarly pay $L^{P/9}$ for an all-plain bottom second block. Its upper filters are still present and covered by the preceding exhaustive list. The high-root condition applies to a bottom second block too. For nonplain patterns no second-block gain is requested.

## 10. Unconditional assembly and the actual loss budget

### Lemma 10.1: order-polynomial overhead

For $D_P\ge1$ independent of $\delta$, and finite $E_{P,\delta},A_{P,\delta}$ independent of $n,L$, choosing $\delta$ with $2D_P\delta^{6\nu}\le1$ and then $L$ sufficiently large gives
\[
 E_{P,\delta}(1+n)^{A_{P,\delta}}D_P^n\delta^{8\nu n}
 \le L^{\varepsilon P}\delta^{2\nu n}\quad(n\ge0). \tag{10.1}
\]
Indeed $\sup_n(1+n)^A2^{-n}<\infty$, and the latter constant is absorbed by the final $L$ threshold. The exponent $A$ may depend on $\delta$; the exponential base $D_P$ may not. This covers the interpolation coefficients, selected-vertex choices, shell expansions and component-order allocations. It does not absorb an arbitrary $C_2^n$.

### Theorem 10.2 (O102 Theorem R): weighted expansion errors

For the true profiles, the two errors in T2287–2290 satisfy
\[
 |\mathcal E^{(1)}|+|\mathcal E^{(2)}|
 \le\tfrac14L^{-P}e^{-100N}\langle k-\zeta k'\rangle^{-4\Lambda P}
 G(M_1,M_2), \tag{10.2}
\]
where $G$ contains each requested first-block factor and, for all-plain patterns only, each requested second-block factor. This costs no positive power in the flower budget.

**Proof summary.** There are at most $n_0\le2P(3N+1)\le8PN$ original branching nodes. The sizes of the blocks to which the ansatz is applied are at most $2P(6N+2)\ll2R_p$, within its scope. For an error term take absolute values: the original time domain has volume at most one. For a positive second shell in the all-plain case, integrate a selected nonparent time first and use (9.1); this gives $M_2^{-1}$ per original tree for large $L$. The dagger removes only parent phases, so it does not remove these phases. For other patterns no second-shell gain is needed.

Pointwise decay extraction is legitimate here because there is no cancellation left to preserve. Charge $2\Lambda+40d$ to an original leaf, at most $4\Lambda+80d$ to a pair; the remaining decay is at least $d+1$. Lattice summation and normalization cost at most $L^{(d+1)n_0}$. Tree and partition counts and all heavy-profile constants cost at most $\exp(8(d+2)PN^2)$. In $\mathcal E^{(1)}$ this is paid by $e^{-N_p}$ with $N_p=N^{1600d^2}$. In $\mathcal E^{(2)}$, the inserted total order is at least $N^4/2$; composition counts are at most $2^{m+h}$, and $\delta^\nu\le1/4$ leaves $2^{-N^4/2}$. Both dominate $L^{-(80d+2)P}e^{-100N}$ for large $L$. The remaining margin pays bottom-block factors and the factor $1/4$ in (10.2). Additional fixed times have volume at most one, sibling indicators are at most one, and removing parent phases does not change absolute values. Thus the same argument covers every pattern and dagger. Full summation and constants are O102 §§2–5, Theorem R and §8.4. ∎

### Proposition 10.3′: the profile-uniform count and extraction, with no open analytic premises

For each fixed order $n\le N^4$, each kind $\mathfrak X,\mathfrak Y,\mathfrak W$, and plain patterns, the true-profile garden sum satisfies
\[
 |S_n|\le E_{P,\delta}(1+n)^{A_{P,\delta}}D_P^{n+1}\delta^{8\nu n}
 L^{BP}\langle k-\zeta k'\rangle^{-4\Lambda P}
 M_1^{-80dP\,\mathbf1_{j_1>0}}
 M_2^{-P\mathbf1_{j_2>0}/9}, \tag{10.3}
\]
with absent cutoffs interpreted as absent factors. Here
\[
 \boxed{B=21006d+546.01.}
\]
The same proof, with the enlarged protected set and the budget below, covers the nonplain cases of Theorem 10.4. All constants have the dependence in Lemma 10.1.

**Proof.** First work uniformly over $\mathcal P(C_1)$, with no heavy decay. Cap and split into irreducible components by Lemmas 2.1–2.2, retaining original-tree labels. Theorem 7.5′ supplies the retained-vine reduction and the count. Every analytic input in its §8 contract is now a theorem: Theorem 7.3′ supplies pins, individual faces, retained protected gains and residual selected gains; Theorem 8.2′ supplies filtered ordinary and whole protected regular objects; Theorem 8.3 supplies (E5′) and Lemma F. Lemmas 4.1–5.3 and Section 9 supply all other weighted factors. No subtraction of a guessed principal approximation is made for a protected object.

The rigidity count is the one in T2237–2255, with the survivors of Section 7. Its factors are bounded by $C_0^n(C_0\rho)!(C_0R)!C_2^{g+\rho}$, times $C_2^{O(b)}$ and fixed-$P$ polynomial choices. The retained gain estimate in Section 7 absorbs $C_2^g$. Also $L^{-\nu\eta\rho}C_2^\rho(C_0\rho)!\le1$ for $\rho\le n\le(\log L)^{C_2}$ and sufficiently large $L$. The ordinary factor $(C_0C_1\delta^{10\nu})^n$ is at most $\delta^{8\nu n}$ after choosing $\delta$. The component partitions cost at most $(4P)^{4P}$ and the order allocations at most $(n+1)^{2P}$. Per-order bases from cutoffs and local analytic estimates are independent of $\delta$; their product is $D_P^{n+1}$. Every remaining $C_2$ factor is independent of $n$ and belongs to $E_{P,\delta}$. Apply Theorem 6.3′ once to this uniform estimate to obtain the external decay and positive first-shell gain. Section 9 gives the second-shell gain. This proves (10.3).

The following table records every positive $L$-cost. It uses the conservative crude splitting cost, not O75's sharper interpolated option.

| Contribution | Plain, per $P$ | Nonplain, per $P$ |
|---|---:|---:|
| Capping, common-profile extrapolation (6.3′) | $0$ | $0$ |
| Survivors: $4b$ | $104$ | $120$ |
| Ladder splitting: $(360d+12)b$ | $9360d+312$ | $10800d+360$ |
| Exceptional spectral supports, with polylog reserve | $24d+0.01$ | $56d+0.01$ |
| Theorem 7.3′: $400db$ | $10400d$ | $12000d$ |
| Theorem 8.2′: $(47d+5)b$ | $1222d+130$ | $1410d+150$ |
| Filtered ladder extension (8.3), beyond existing source ladder costs | $0$ | $0$ |
| Weighted expansion errors (10.2), estimated separately | $0$ | $0$ |
| **Subtotal** | **$21006d+546.01$** | **$24266d+630.01$** |
| Optional conservative pattern reserve | $0$ | $300d$ |
| Bottom first and second blocks | $80d+1/9$ | $80d+1/9$ |
| Polynomial overhead, constants and order sum | $3$ | $3$ |

The nonplain support allowance is the plain $24d$ plus $32d$ for at most $8P$ added exceptional coordinates. Its second-bottom allowance is redundant but harmless. The enlarged $b\le30P$ already charges the actual new pattern incidences in both analytic theorems. The additional $300d$ is only a conservative reserve; it does not assume O104's superseded excision estimate.

**Units in O75's formula.** That packet writes
\[
 B=9384d+416.01+26(c_{7.3}^{\rm incidence}+c_{8.2}^{\rm incidence}).
\]
Here the incidence costs are $400d$ and $47d+5$. The totals requested in the brief are $c_{7.3}^{\rm total}=10400d$ and $c_{8.2}^{\rm total}=1222d+130$. Substituting the latter **without another factor 26** gives the boxed value. Thus the exact (10.4) checks are
\[
 \begin{aligned}
 B+80d+\tfrac19+3&=21086d+549+\tfrac{109}{900}<10^6d^3,\\
 B_{\rm pat}+300d+80d+\tfrac19+3
 &=24646d+633+\tfrac{109}{900}<2\cdot10^6d^3.
 \end{aligned} \tag{10.4}
\]
Both hold already at $d=1$, and the proof uses $d\ge3$. Their differences are increasing for $d\ge1$. Lemmas 9.5 and 10.1 now give the desired fixed-order factor $\delta^{2\nu n}$ and leave ample strict margin for constants.

Summing orders gives (1.1). Every nontrivial original flower tree contributes positive order. In the $\mathfrak Y,\mathfrak W$ classes each of the $2P$ original trees has more than $N$ top-layer branching nodes, so $n\ge2P(N+1)$. Taking $\delta$ sufficiently small makes the geometric tail at most $e^{-100N}$, including its constant. Use the unused $L$ margin to allocate, for example, half the target to the principal sum; (10.2) occupies at most a quarter. This proves the moment statement with unit displayed constant, not just an unspecified multiple. ∎
## 11. Every frozen flower pattern and the dagger

### 11.1 Exact statement and domains

In this section $n$ denotes fixed **total garden order**; it is the variable called `N` in the frozen theorem. The cutoff $N_{p+1}$ is still denoted by $N$ elsewhere in this supplement. Fix $d\ge3$, $1/2<\gamma<1$, the source parameter prefix, $p<s<t<p+1$, roots $k$, flowers $k'$, kind $\mathfrak X,\mathfrak Y$ or $\mathfrak W$, and $n\le N_{p+1}^4$. Let $\mathrm{pat}$ assign to each of the $2P$ original trees one of `plain`, `dRoot`, `dParent`, `dChild(i)`, $i\in\{0,1,2\}$. Write $r$ for its root, $f$ for its flower, $\phi=f^{\rm pr}$ and $\pi=\phi^{\rm pr}$.

Every pattern pins $\phi$ to $s$. The additional pins and validity conditions are:

| Pattern | Additional pin | Validity |
|---|---|---|
| `plain` | none | always |
| `dRoot` | $r=t$ | $r\ne\phi$ |
| `dParent` | $\pi=s$ | $\phi\ne r$ |
| `dChild(i)` | the $i$th child of $\phi$ equals time $s$ | that child is branching and has layer $p$ |

The domain keeps the layer interval and upper-time condition for each **free** node. It keeps a parent-child inequality whenever at least one node is free; it drops that inequality only when both nodes are designated. Consequently a root designated at $t$ is legitimate and coincident parent/child pins do not create an empty strict-order domain. All other constraints remain.

For dagger data $c_{j,i}$, multiply by the indicators that each nonflower child momentum of $\phi_j$ equals $c_{j,i}$, and omit the phase at $\phi_j$. These are exactly `FixPat`, `fixPat`, `PatValid`, `kDomainFix`, `phaseProdOff`, `sibWeight` and `flowerSumP` in the frozen definitions listed in Section 13. Patterns and dagger labels may differ between trees.

### Theorem 10.4, with the packet's former hypotheses discharged

Let $c(\mathrm{pat})=1$ if all patterns are plain and $2$ otherwise. For optional dyadic product cutoffs $M_i=2^{j_i}L$, with a second cutoff allowed only when the first is present and $|k|\ge M_1^{10}$, the exact deterministic frozen flower sum satisfies
\[
 \boxed{\quad
 |\mathrm{flowerSumP}_n|
 \le\langle k-\zeta k'\rangle^{-4\Lambda P}
 L^{c(\mathrm{pat})10^6d^3P}\delta^{2\nu n}
 \big[M_1^{-80dP}\big]_{\mathrm{cut1}}
 \big[M_2^{-P/9}\big]_{\mathrm{cut2\ and\ all\ plain}} .\quad} \tag{11.1}
\]
It holds with or without dagger, including **all-plain dagger with the single budget and the second-shell gain**. Brackets denote a factor only when the subscript condition holds. The order-zero identity is excluded from the regular flower carrier as explained in Section 1.

**Proof.** The domain description follows by substitution in the exact frozen definitions. The derivative identities motivating it are $\partial_tJ^{\rm plain}=J^{\rm dRoot}$ and, with the flower-parent phase omitted,
\[
 \partial_sJ^{\rm off\,\phi}=-J^{\rm dParent}+\sum_iJ^{\rm dChild(i)}.
\]
Invalid terms are absent. Without the phase omission an additional $i\omega_\phi J$ occurs; it is not one of the listed patterns. We estimate each pattern separately, rather than infer an individual-face bound from this signed identity.

Add the designated vertices and any needed adjacent carrier vertices to $\Pi$, giving $b\le30P$. O104 Lemmas 3.1 and 6.1–6.2 identify the root and parent patterns with the raw faces already covered by Section 8.1. Its §7 reduces the child pattern to $F_{\rm ch}$, now proved individually by O73 Proposition 19.2 and Theorem 7.3′. For a regular object use that theorem and retain the whole object as in Theorem 8.2′; for a residual atom use the mixed estimate (8.4). A pin fixes a time, removes its integration, and leaves an explicit boundary phase. No resonance-dependent weight is placed on that phase. Coincident pins give distinct exceptional coordinates at the same external time. All untouched side-object gains remain.

Unmarked twists preserve the additional pins and their domains. Use precisely the retained-vine construction of Section 7; its proof depends on the size and locality of $\Pi$, not on a flower-parent-only list. This replaces O104's former boundary-excision hypothesis H3. There are no new induced boundary graphs. The numerical costs are exactly the nonplain column of Section 10, already with the enlarged incidence count. Upper second filters still pass through Section 8 and Lemma 9.3. Since no $M_2$ gain is requested for nonplain patterns, no selected-time operation at a newly pinned time is needed. Theorem 6.3′ applies unchanged because pins and omitted phases belong to $\Theta$ and do not change momentum conservation.

For dagger, partition into the at most $3^{2P}$ choices of the flower's child position. In each class, the prescribed sibling momenta and $k'$ determine $\Omega_{\phi_j}$; omitting its phase multiplies the corresponding non-omitted expression by a constant of modulus one. Keep all sibling indicators until the relevant sum has been made absolute. Both ends of their bonds are protected. In a regular object they restrict the exceptional linked tuples already summed absolutely in (8.2) and O73's face argument. In the residual molecule they restrict the count at protected atoms; those bonds cannot be internal variables of a retained ladder, because ladders were split at every protected endpoint. In a retained marked vine the same splitting exposes them before the absolute nonladder sum. This is the non-excision replacement for O104 Proposition 8.1's boundary-sum sentence. Alternatively a lattice equality is $\psi(L(k_e-c_e))$ for a fixed bump supported in $|z|<1$ with $\psi(0)=1$; its Fourier-measure norm is independent of $L,c_e$, and it can be retained as a zero-derivative amplitude at the permitted local step. Neither argument deletes an indicator inside an unestimated oscillatory sum.

Each flower-position class is a union of the allowed LF classes, so the count bounds it separately. The factor $3^{2P}$ is independent of order. For all-plain dagger the selected times exclude $\phi_j$, so none of their phases is omitted; the $2P$ selected gains of Section 9 remain. Thus dagger adds no $L$ exponent and does not change $c(\mathrm{pat})$. Apply Proposition 10.3′, Lemmas 9.5 and 10.1, and the exact inequalities (10.4) to obtain (11.1). Theorem 10.2 also gives the corresponding weighted moment remainders. ∎

**Scope of the frozen correspondence.** Equation (11.1) is the flower conjunct of `layergardenFlower_v3`, including every frozen pattern and dagger case. The separate ordinary-couple conjunct is not a flower sum; O104 §2.2 records that it is supplied on the port route by `coupleHalf_of_spine`. No claim about completion of that Lean proof or any provider is made here. The mathematical flower proof does not depend on that conjunct.

**The older FC23 auxiliary interface.** The direct proof of (11.1) should not be identified with a proof of `FC23UniformCut1At`. The latter quantifies over per-tree vectors `tail`, `small`, `z` and endpoint polynomials `flowerFamilyWeight` (port `Foundations/FC23/FlowerFamily.lean:35–65`). O63 instead proves the final cutoff estimate by one scalar common-profile interpolation. The two intermediate families are not definitionally the same, and O104's sentence “whatever proof FC23 gives” is not a proof of that stronger auxiliary premise. Our resolution is to prove the frozen flower inequality directly by Theorem 6.3′ and Proposition 10.3′; no FC23 auxiliary uniformity is assumed or claimed. The positive-second and bottom-second cases are direct instances of (11.1). A future formalization using the older three-premise route must either establish its larger family or replace that auxiliary route by the scalar interpolation proved here. This is a formal-interface distinction, not a missing premise of (11.1).

## 12. Errata, referee fixes, and interface reconciliation

The mathematical statement proved here is explicitly the $d-\gamma$ normalization and the regular-kernel interpretation on the open triangle. The former is an **erratum** to T2264–2265; the latter is an **order-zero reinterpretation**, not a claim that a Dirac distribution has pointwise moments. The restriction $1/2<\gamma<1$ is also substantive: the triangle and final counting inputs used here do not establish the complementary range.

### 12.1 Source repairs used

The named E entries below refer to [ERRATA-AND-DEVIATIONS.md](<worktrees>/report/docs/ERRATA-AND-DEVIATIONS.md), at the line locations listed here. These are mathematical repairs used by the packets, not assertions that this supplement independently verified their Lean implementations. Long graph proofs remain incorporated through O75's exact references and the linked repair discussions.

| Entry and source location | Repair used in this proof |
|---|---|
| E4, ledger 762–819; T1846, T1983 | Nonsmooth degeneracy indicators are not smooth Fourier amplitudes. Retain them in rung estimates; in a long vine use the character-mixture mass $3^n$ and modulation-uniform `sumint`, not trivial summation of all remaining variables. |
| G2/G3; T1989–1991 | Two exposition gaps in the printed `ladderl1new` sketch: the omitted $\epsilon,\mathcal Z$ analysis and the unproved last-rung factorization. O83 Lemma R handles the nonsmooth weights; Theorem K fixes both end double bonds and separates the remaining conservation law by characters. The general internal-ball case is proved, without claiming that every such ball necessarily occurs in T's particular construction. These gaps do not refute the ladder lemma. |
| E5, ledger 820–845; T2075–2083 | Ordered ladder kernel bounds do not multiply across time-order constraints. Use the unordered box core with the absolute decoration sum inside the time integral; discard inter-ladder ordering only there. Theorem K supplies its translated-box form (E5′). |
| E9/E11, ledger 916–990; T2152, T2185–2189, T2218 | Track tame-cluster removals and their extra imperfect components. A bridge pin is retained as data; an unpinned double-bond configuration uses the cycle-rank gain. Do not apply the nonzero-gap final estimate to an unpinned zero-gap cut half. |
| E16/E17, ledger 1078–1139; T2142, T2152, T2193–2197 | An Operation-2 hinge is not necessarily tame. Require its designated pair and nonzero third gap, skip ineligible triangles, and erase maximal tame clusters at the final stage. Use the damaged-component bound. For $R=1$, “imperfect” need not mean “odd”; the label interpolation in Section 7 replaces that assertion. |
| E10/E12/E13, ledger 944–961, 999–1035; D23 1815, 1876; T2101 | Identify a final vine through its two distinct ancestor joints, including the hyper-vine case; for degree-three odd atoms use the $L^{-3\gamma_0/5}$ alternative of D23 Proposition 10.2; apply the double-vine selection rule among maximal objects. These are the repaired ordinary count used by O75. |
| E14/E15, ledger 1036–1077; T1747, T1959–1962 | A leaf has no independent clock: use its floor value and an order-zero trace. Carry the node-center exponential explicitly even if no vine was spliced; it belongs to $D_P^n$, not to a zero power of $(C_1\sqrt\delta)$. |
| E18, ledger 1139–1164; T1918 | A trivial coherent approximant need not vanish at its layer floor. In Lemma 5.3 use the exact trivial kernel $F\mathbf1_{t>q}$, and the vanishing extension only for the nontrivial approximants. The mixed-family reality identity holds off a null set. |
| E19, ledger 1165–1179; T2213–2216 | A triangle operation can consume two critical atoms: use $p_{\rm sb}\le2p_{\rm op}$. The existing $\eta^3$ margin absorbs the factor two. |
| E20/E21, ledger 1180–1225; D23 1777, 1791–1803; T2131, T2142, T2165 | Already-cut halves retain their labels; charge a ghost's label at deletion and refund it at most once. Only a still-live earlier cut supplies a hitting ball, with its parameter fixed at creation. Choose $8\eta\le2\gamma-1$. |
| E22, ledger 1226–1246; T2140 | A hinge endpoint alone does not place a triple bond in a collected vine. Choose the small-gap external pair at the hinge and cut it in Operation 1, destroying that triple bond. |
| E23, ledger 1247–1316; T1304, T2122–2126 | Permit the low-degree atoms and self-loops actually produced by Stage 1; keep their charges and isolated halves. Do not import a graph theorem whose minimum-degree hypotheses fail. |
| E24, ledger 1317–1374; T2065–2067, T2293 | A decoration-selected heavy leaf or independently differentiated leaf profile does not preserve LF cancellation. The flower decay and first shell use the exact common-profile identity (6.3), with zero leaf marks. Ordinary weighted derivatives use the repaired common/type-uniform extraction, not the printed leafwise assertion. |
| E25, ledger 1375 onward; T1749, T1909 | The bad-vine class count has a late-constant factor. Reserve half the $L^{-\eta^2}$ bad-vine gain to pay it. Lemma 5.3 is used with $-\eta^2b/2$ after class counting; the remaining gain still dominates the downstream $\eta^6$ costs. |
| E26, ledger 1420–1464; T1726, T1737–1738, T1954–1957 | **Unresolved global interface in this integration:** lower external regular slots retain the integrated lower-joint clock. Section 12.3 states the missing clock-aware splicing estimate precisely. The printed factorization is not used as an established identity. |
| E27, ledger 1465–1502; T1944, T2250–2251 | Do not assert at most $2^n$ fine LF classes per coarse class. Count their representative layered gardens directly, with exponential fibre bound and $C_2^{g+\rho}$, then absorb that factor with retained gains. |
| E28, ledger 1503 onward; T2126, T2138, T2156–2162 | A degree-two cut creates an isolated half. Keep it when computing increments and refund its label only at final removal; do not mix compressed and uncompressed increment conventions. |
| E29/E30, ledger 1548–1644; T2259–2261, T2287, T2295 | Use separate trivial caps and retain the flower-parent pins. Pairing flowers directly need not preserve the marked regular reduction; fixing the parent resonance does not remove a Dirac trace. Lemmas 2.1–2.2 and Theorem 7.3′ replace those shortcuts. |
| E31, ledger 1645 onward; T2297 | Leaving special-node vines unspliced changes `subpro`. Theorem 7.5′ supplies the survivor collection, shared-joint pairs and the additional clause for objects meeting $B$. |
| E33/E34, ledger 1727–1822; T2283–2285; D21 2699–2704, 2731, 2735 | Use the product dyadic partition and all transported frontier weights. E34 is a deviation of the older frozen max-cutoff statement; the successor v3 is the target here. |
| E35, ledger 1823 onward; T2299 | Raw time integration needs individual face estimates and twist-compatible carriers. Section 9 keeps the raw identity, and O73 supplies the actual face and residual-frequency estimates. |
| E36/E37, ledger 1878/1921 onward; T2294, T2297 | Check original frontier weights under LF transport. Factors inside a spliced vine enter Lemma 5.3; they cannot be silently assigned only to surviving bonds. |
| E38, ledger 1955–1994; T2294, T2297 | Internal frontier cutoffs in incoherent regular objects enter the weighted norm argument of Lemma 4.1, including the correct tree output-supremum argument. |
| E39, ledger 1995 onward; T2299 | Upper resonance filters can occur inside coherent stem trees. Theorem 8.2′ treats their truncated poles and their discrete approximation, not just their integrable coefficients. |

Source references to the ordinary reduction use these repairs where supplied. E26 is the explicit exception identified in Section 12.3; the global assembly is not claimed to discharge it. The proof does not inherit the printed false minimum-degree, fixed-value, class-count or floor-vanishing assertions.

### 12.2 Packet interfaces and their resolutions

| Interface mismatch or possible ambiguity | Resolution in this supplement |
|---|---|
| V1 marked-leaf decay versus O63 | Delete Section-6 leaf marks entirely. Use one real scalar interpolation before absolute values. Only geometric, pin, selected and pattern marks remain. |
| Heavy true profiles versus O63's downstream class | The count is uniform over real $\mathfrak S^{40d,40d}$ profiles. Heavy norms are used only by the interpolation and the separate absolute remainder proof. |
| Different first-shell support constants | O63 Remark 2.1 changes the auxiliary radius by a fixed factor. Frozen product cutoffs are retained exactly. |
| Flower half-width versus capped half-width | Original width $2P$ becomes $4P$ after capping. Component half-widths sum to $2P$ in every factorial and defect count. |
| V1 excision versus O75 | Keep marked vines and regular objects whole. Use connected molecules, survivor removals and the split set $B\cup\Pi_{\rm sb}$. No excised-boundary theorem is invoked. |
| O75 one-survivor HVC wording | Its image is an HV, including the extra bond. Remove the full HV. |
| Designated pairs only at hinges | Shared nonhinge joints of survivors also receive the pair in the survivor removed first and the common gap label. |
| Re-cut halves, deleted hitting cuts and $R=1$ components | Keep the isolated-half ledger, live-hit rule and label interpolation of Section 7. These are REFEREE-2 fixes 75-F2/F3. |
| Claimed positive time weights on boundary phases | Keep pure phases explicit; shift the next integration exactly. The protected punctured-chain coefficient is consumed with weight one. Ordinary positive-weight factors are used only where their stated estimates apply. |
| Arbitrarily punctured chains versus actual flower geometry | O73 Proposition 3.1 restricts the geometry; its Theorem 7.3′ proves precisely the actual pins and faces, including $F_{\rm ch}$. |
| REFEREE-73 root traces and coefficient order | Require the traced root in layer $p$, allow its third boundary time, apply the discrete estimate at fixed side frequencies before integrating their amplitude mass, and smooth the line-supported Fourier measure by a fixed cutoff. |
| REFEREE-73 upper-face and separate-child scope | Reunite maximizing-child cells for upper faces; lower faces remain cellwise. For a separate child object use its root-trace formula, not a single-layer chain assertion. |
| REFEREE-73 residual parent recipient | The residual parent can lie inside a retained ladder. Its added factors are independent of internal ladder momenta and are harmless in the unordered absolute box core; no extra protected mark is claimed. |
| O73/O82 apparent dependency cycle | O82's ordinary discrete theorem uses only O73's elementary geometry and terminal identities §§3,12–13. O73's completed pin and residual estimates may then use that independent theorem. The earlier conditional marked-coefficient proposal is not used. |
| Pin gains versus protected-object gains | Both analytic theorems retain all original regular-object incoherency gains. Only the bounded ladder-split incidences are allowed to lose gains. |
| Possibly negative $g-22b$ | Use the actual nonnegative retained count and lost count $\ell\le22b$, as in Section 7. No negative gain count or compensating $L^{Cb}$ is introduced. |
| O75 selected residual vertices versus O82 selected regular occurrences | O73 Proposition 20.1 treats the former, including Fourier-shifted total frequencies. O82 treats only the latter. Count both vertices if a linked pair is selected twice. |
| Strong regular estimates in REFEREE-82 | Couples need $X^{1/4,30d,30d}$ to sum output centers. Trees use a per-frequency uniform-output majorant, not spatial Sobolev without decay or an exchanged supremum/integral. |
| Pole truncation versus integrable-coefficient multiplication | A truncated extracted pole is handled by O82 Theorem 10.1 and Lemma 11.2; it is not moved into a coefficient independent of that variable and is not assigned a uniform $L^1$ norm. |
| D23's smaller order range | The simultaneous discrete proof absorbs factorials per minor coordinate, uniformly for the actual $n\le N^4$ range. |
| O75 conditional Lemma F / E5′ | O83 Theorem K proves the exact arbitrary-unit-box core needed for translations; Theorem 8.3 supplies the Fourier-tail control. REFEREE-83 is complete. |
| Ladder normalizations $2m+1$ and $2m+2$ | Convert explicitly by $2L^{d-\gamma}/\delta$; the end allowance fits the existing $L^{20d}$. |
| Frontier cutoffs on bonds versus inside vines | At most two occur per bond; the internal factors belong to Lemma 5.3. Both placements are estimated. |
| High-root claim for arbitrary lower descendants | Use only original top vertices and frontier roots. Marking excludes the flower and its parent from a spliced realization before applying the $u_{11}$ argument. The affine filter is at the top. |
| O104 missing child face and old H3 | O73 Proposition 19.2 supplies the individual child face. Replace H3's excision with O75's retained construction at $b\le30P$. |
| Dagger indicators inside oscillatory sums | Retain them through the protected tuple reduction; discard them only in absolute sums, or use the local equality bump. All-plain dagger keeps its selected phases and its single budget. |
| O104's $300d$ versus the enlarged mark count | Recompute all costs at $30P$. The $300d$ is a further conservative reserve, so no unproved old excision cost is needed. |
| O75 costs per incidence versus the brief's totals per $P$ | Substitute $400d$ and $47d+5$ in O75's factor-26 formula, equivalently add $10400d$ and $1222d+130$ once. |
| Frozen total-order `N` versus the paper's truncation $N_{p+1}$ | Equation (11.1) uses $n$ for the frozen order and retains $N_{p+1}$ only as the cutoff. |
| O104's FC23 family remark versus scalar extrapolation | Prove the final frozen flower inequality directly. The older multivariable auxiliary family is not silently identified with the scalar common-profile class. |
| Packet historical OPEN labels and stale review statements | Only the final operative theorems listed in Section 13 are imported. Review completion is recorded separately; historical conditional proposals are not hypotheses of Proposition 10.3′. |

The editorial source corrections in REFEREE-82 are also adopted: T1050 is the strong tree estimate, T1030 the relevant regular-couple statement, and D23 1012–1034 is the cited nontrivial-chain approximation range. The supremum-inside-Fourier-integral correction in REFEREE.md is applied in Lemma 4.1. The Fourier-measure estimates in Lemma 3.2 use matrix-valued affine coefficients and total variation; they do not assert that multiplying a cutoff must increase a norm.
### 12.3 Remaining source-interface issue: E26, the native lower clock

**This issue prevents an unconditional closure claim.** It is separate from the seven flower packet obligations. O75 invokes the Stage-1 factorization T1954–1957; the local weighted-vine lemma estimates its stated local kernel. Neither is an explicit theorem for the lower-clock expression identified in E26. The diagnosis is recorded in [the E26 entry](<worktrees>/report/docs/ERRATA-AND-DEVIATIONS.md:1420), and [the lower-clock handoff](<worktrees>/report/docs/research/redvine-lower-clock-handoff.md:12). The main checkout's errata entry, at `docs/ERRATA-AND-DEVIATIONS.md:868–890`, also distinguishes the adopted repair from a proof of the factorization.

Here is the exact algebraic mismatch. Let an unmarked spliced unit have upper joint $a$, lower joint $b$, and a lower external branching child $c$. Attach a nontrivial regular tree at $c$, in the same layer. Before splicing its factor is
\[
 K_{\mathcal T_{(c)}}^*(\tau_b,\tau_c,k_c),\qquad
 \tau_c<t_2<t_1<\tau_b<t_a.
\]
The local vine kernel integrates $\tau_b$ but does not include this external-child factor. After splicing $c$ has parent $a$; the printed exterior factor in T1956 is $K_{\mathcal T_{(c)}}^*(t_a,\tau_c,k_c)$. These are different time domains. For a lower leaf, an external regular couple can similarly depend on two interior lower clocks belonging to different spliced units. Invariance of the *regular object* under a twist does not make its clock exterior. Marked vines being retained does not by itself eliminate this configuration for unmarked units.

The missing sufficient assertion, **U-clock**, is the following: retain the native parent clocks in the exact Stage-1 integrand; Fourier-expand the exterior regular slots in those clocks; establish the resulting identity and a modulated version of Lemma 5.3, uniformly over $\mathcal P(C_1)$ and the actual frontier filters; then consume every modulation against the available norms, retaining all required gains and the numerical budget in Section 10. For patterns and dagger this must include any protected exterior slot, whose supplied bound may have only time weight one (unweighted Fourier mass) with explicit boundary phases. An ordinary positive-weight estimate cannot silently be substituted for that consumed bound.

The proposed repair introduces $e^{\pi i\lambda\tau_b}$ into the vine and a factor $\langle\lambda\rangle^{6\eta^6}$. T1618 provides modulation tolerance for `sumint`, and the handoff's later sections report a per-mode algebraic identity for a general splice shape. This is useful progress, but neither a citation to the *unmodulated* Lemma 5.3 nor that identity alone proves the full norm consumption above. The examined packets contain no explicit U-clock statement or proof. This supplement therefore does not infer its closure from a formalization status label or from the fact that its proposed exponent is small.

**Effect on the assertions above.** Proposition 10.3′ discharges all the named flower contracts of O63/O75, with the numbers shown, **relative to U-clock**. Equation (11.1) and the moment conclusion inherit that one remaining source-interface premise. The standalone interpolation, pin/face, filtered regular-object, box-core, graph-survivor and remainder results do not acquire a new hypothesis. This is a proof-coverage finding, not a counterexample to `flowerest1`. A complete unconditional proof requires U-clock or a different exact reduction avoiding it. Thus the brief's request for an unconditional assembly is not fully met by the present input chain; that limitation is recorded prominently rather than hidden in a source citation.

## 13. Final dependencies, input versions, and review status

### 13.1 Source-level dependency list

All T/D21/D23 lines refer to the SHA256-pinned sources in Section 1. References in the errata table supplement this list; they are part of the dependency record.

| Source lines | Input and consumer |
|---|---|
| T568–576, T628–647, T671–674, T689–715 | Conditional moment–cumulant inversion, signs, leaf count, conservation, normalization, time domains and induction hypotheses: Lemmas 2.1–2.2 and Theorem 10.2. |
| T598, T606–615 | Profile bounds, constant order, $\Lambda_p=40d\Lambda_{p+1}$, polylog order scales and smallness: Sections 1, 6 and 10. |
| T803–807, T2259–2273, T2287–2290 | Error expansions, original flower truncations and the total-order cutoff: Lemma 2.2 and Theorem 10.2. |
| T826–877, especially T845–857 and T877 | Regular-chain construction and legal noncrossing pairing: O73 geometry and the exact terminal cut (8.2). |
| T951–977, T981–1017, T1021–1092 | Ordinary regular estimates, spatial localization, independent linked variables, couple output decay and the paired-tree endpoint argument: Lemma 4.1, O82 Theorem 10.1 and Lemma 16.1. |
| T1095–1123, T1143–1174, T1197–1244, T1270–1288 | Coherent approximations, one-layer profiles, principal-value factors, layer factorization and realness: Lemmas 5.1–5.3 and Theorem 8.2′. |
| T1295–1325, T1328–1382, T1384–1421 | Molecule counts, blocks, realizations, vines and hyper-vines: capping and Theorem 7.5′. |
| T1429–1489, T1501–1532 | Twist transport, layer counts, incoherency and decomposition into at most three ladders plus bounded residual atoms: Sections 5, 7 and 9. |
| T1595–1731, especially T1618, T1621–1660, T1681–1689 | Modulation-uniform `sumint`, Fourier endpoints and enlarged time intervals: Lemma 4.2, O83 Lemma R, and the identified U-clock obligation. |
| T1724–1760, T1753–1923 | Regular factorization and the corrected local `vineest` proof: Lemma 5.3. Its local conclusion is distinguished from the global clock issue. |
| T1927–1974, especially T1954–1957 | Stage-1 splicing, localized bond factors and residual phases: O75 reduction; **U-clock remains to justify the exact global factorization**. |
| T1978–1991, T2075–2083 | Ladder estimate and its coarse-bound consumer, with G2/G3 and E5 repaired: O83 Theorem K, Theorem 8.3 and Corollary 8.3.A. |
| T1994–2037, especially T2005 and T2013 | Dephased residual boxes, available frequency sets and $X/Y$ integrations: O73 Proposition 18.1. |
| T2040–2052 (clauses at T2042–2047), T2431–2437 | `subpro` and `subsetvc`: Theorem 7.5′ with the survivor amendments. |
| T2090–2218, T2459–2476 | Absolute count, cuts, component defects, final molecule estimates and atom counts, with the listed graph repairs: Section 7 and O75 §§4–8. |
| T2220–2256 | Coarse/fine interpolation, rigidity and layered-garden summation: Proposition 10.3′. |
| T2279–2304, T2327, T2330–2331 | Target proposition, its per-order conclusion, dagger and derivative uses: Sections 1, 9–11. |
| D21 925–961, 1011–1094, 1142–1146 | Class-$J/R$ calculus, arbitrary unpaired slots and restored-pole translation loss: O73 Lemma 19.1, in its fixed-side-frequency form. |
| D21 1305–1366, 1504–1622 | Continuum reciprocal estimates, symmetric principal values and many-variable comparison: O82 §§10–11. |
| D21 2684–2694, 2699–2704, 2731, 2735 | Terminal pin precedent, high-resonance estimate and product dyadic partitions. These precedents do not replace the new layered pin and cutoff proofs. |
| D23 440, 955–978, 984–1009, 1012–1034, 1076–1088, 1161–1162 | Spectral cutoffs, derivative/moment bounds, ordinary approximation and weighted bilinear sums: O82 discrete theorem and O83 Lemma R. |
| D23 1673, 1731–1756, 1788–1817, 1876, 1985 | Vine concatenation, original `subpro`, cut deviations, final components and degenerate-atom treatment, with the graph errata: O75. |

### 13.2 Exact packet results used

The noncircular order is: O73 geometry/terminal identities → O82 ordinary discrete and filtered-kernel estimates → O73 completed protected and residual estimates; independently O83 supplies the box core; these enter O75's count. O63 then extracts decay from that profile-uniform count. O102 treats the expansion errors separately. O104's pattern identities are combined with O73's individual-face result and O75's enlarged protected set. The global Stage-1 U-clock issue is independent of this packet dependency order.

| Packet | Operative theorem/proof locations |
|---|---|
| O63 | Lemmas A–D and Theorem 6.3′, §§2–4; Proposition 10.3′ and profile contract §5; revision-2 common-profile interpolation. |
| O73 | Proposition 3.1; Lemma 12.1 and Proposition 13.1; §17 regular estimates; Proposition 18.1; root trace §19.1, Lemma 19.1, Proposition 19.2; Proposition 20.1; Theorem 7.3′ §21; budget §22. Apply the REFEREE-73 fixes recorded in Section 12.2. |
| O75 | Lemmas 1–2, §2.3–2.4; Theorem 7.5′ §3 and proofs §§4.1–4.9; loss table §7 and Proposition 10.3-count §8; all revision-1 fixes §11. Lemma F's former hypothesis is O83 Theorem K. |
| O82 | Theorem 10.1; Lemma 11.2 and Theorem 11.3; Proposition 15.1, Corollary 15.2, Lemma 16.1; bounded-extension/interpolation lemmas §17; Theorem 18.2; Theorem 8.2′ §19; revision-1 fixes §22. |
| O83 | Lemma R §§4.2–4.3, Theorem K §4.4, filter translation and tail lemmas §§4.5–4.6; Theorem 8.3 and Corollary 8.3.A; frontier weights §7 and exhaustive filter placement §8; revision-1 referee fixes. |
| O102 | Lemmas R.0–R.5, §§2–5; Theorem R and its weighted/pattern extension §8.4. |
| O104 | Lemmas 3.1, 3.3, 6.1–6.3, Propositions 7.2–7.4 and cases P1–P8; Proposition 8.1; Theorem 10.4. Use the corrected port-domain/root-phase interpretation, the reunited upper faces, and the non-excision dagger argument of Section 11. Its old H1/H2 flower contracts are discharged by the listed packets; its H3 route is replaced, not assumed. |

The exact frozen flower carrier was read at `<repo>/WaveTurbulence/Frozen/`: `Theorems/LayergardenFlowerV3.lean:93–106`; `Defs/FlowerSumP.lean:68–82`; `Defs/FixPat.lean:30–34`; `Defs/LayeredGardenFixPat.lean:41–50`; `Defs/LayeredGardenPatValid.lean:43–48`; `Defs/KDomainFix.lean:40–44`; `Defs/KernelKgen.lean:54–66`; `Defs/PhaseProdOff.lean:39–43`; `Defs/LayeredGardenSibWeight.lean:44–48`. This is a mathematical correspondence check, not a Lean build or proof-status audit.
