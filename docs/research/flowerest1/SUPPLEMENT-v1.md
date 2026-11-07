# Supplement on the flower estimate

This document concerns Proposition `flowerest1`, TARGET lines 2279–2286, in the range $1/2<\gamma<1$ and under the other standing hypotheses of TARGET. It proves several of the required extensions, including the Fourier-measure extension of the localized exponential-sum estimate and the coherent-family cancellation for a common frontier cutoff. It does **not** prove the proposition in full. The unresolved statements are explicitly numbered OPEN below. In particular, the conditional assembly at the end is not a proof of `flowerest1`.

The distinction matters: an algebraic cancellation, a bound for an individual oscillatory expression, and a bound after a marked reduction of a whole family are different assertions. The first two do not automatically imply the third.

## 1. Sources, constants, and the intended statement

We use the following frozen local sources; line numbers below refer to these files.

- **T:** `/home/scott/wave-turbulence/paper/source/WKE-Longer_times_Final_arXiv.tex`, SHA256 `493eef6b7dec448bc5f9f1c3974c0cad7a85eca9bc428f5b35e968aad76727cb`.
- **D21:** `/home/scott/wave-turbulence/references/src-2104.11204/Inventiones-Final_Version.tex`, SHA256 `50d0e236a2df0cfd2b98bace6f0256043ee88fc05079ee44c3524ca9482fe402`.
- **D23:** `/home/scott/wave-turbulence/references/src-2301.07063/Revision_Submit.tex`, SHA256 `c7e47dfabf5a4cca6e3ad0399fc377f2809c12f58e1563640407fe0992335475`.

The constants $C_0,C_1,C_2,\nu,\eta,\Lambda_p,N_p$ have the meanings and dependencies in T606–615. In particular, $C_2$ may depend on $\delta$; it cannot be used indiscriminately as the base of an exponential in the order. Choose $P$ first, $\delta$ second, and $L$ last. Constants depending on $\delta$ but independent of the order can be absorbed by increasing the final threshold for $L$. A factor $C_2^n$ cannot be absorbed by choosing $\delta$ smaller without an additional argument. A factor $L^{Cn}$ is inadmissible.

Write $\Lambda=\Lambda_{p+1}$ and $N=N_{p+1}$. The desired bounds, for the three versions without cutoffs, with the first cutoff, and with both cutoffs, are

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

**Order-zero convention.** The trivial flower tree contributes the identity operator in the positive-sign channel. Thus $\mathfrak X=I+\mathfrak X_{\mathrm{reg}}$ as an operator. Its identity contribution is $\mathbf1_{k=k'}\delta(t-s)$, not a function to which a pointwise $2P$ moment applies. In (1.1), $\mathfrak X$ denotes the regular kernel on the open triangle. No flower-parent pin is assigned to a nonexistent parent. There is no negative-sign order-zero contribution. The definitions of $\mathfrak Y=(1-\mathfrak L_1)\mathfrak X-I$ and $\mathfrak W=\mathfrak X(1-\mathfrak L_1)-I$ use this operator convention.

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

For $h=0$ use the point mass at zero. If an existing amplitude has Fourier $L^1$ norm $D$, multiplication by these factors increases its Fourier $L^1$ norm by at most $B_0(\chi)^h$.

**Proof.** Fourier inversion represents $a_i$ as the pushforward of
$e^{2\pi i\xi\cdot b_i/R_i}\mathcal F\chi(\xi)\,d\xi$ under $\xi\mapsto A_i^T\xi/R_i$. Pushforward does not increase total variation, even if $A_i$ is not injective or surjective. Products correspond to convolutions of these measures, proving (3.4). For the output frequency $\sum_i(A_i^{(z)})^T\xi_i/R_i$, use
$(\sum_i u_i)^s\le h^{s-1}\sum_i u_i^s$ with $u_i=1+2\pi\|A_i^{(z)}\||\xi_i|/R_i$, and integrate. This gives (3.5). Finally, convolution of an $L^1$ density with a finite measure has $L^1$ norm at most the product of their norms, by Tonelli and translation invariance of Lebesgue measure. ∎

### Lemma 3.2 — Shell expansion and commutators

A product of $2P$ shell factors is a signed sum of at most $2^{2P}$ low-pass products (bottom factors need no expansion). For affine $z_i(x)$, fixed vectors $b_i$, fixed $r\in\mathbb R^d$, and $R_i\ge R_*$,

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

Perform the same leaf localization and the same $C_0^n$ refinement to unit balls for $x_v,y_v$ as in T1007–1009. The new factors do not enlarge the support. Convolve the localized Fourier density in T1011–1015 with the measures from Lemma 3.1. The phase-modulated estimate T1017 and the rest of the proof are uniform in all the resulting spatial modulation parameters, so integration against the convolution measure multiplies the bound only by its total variation. The extension in time is the fixed one described in T995 and is independent of the derivatives and modulation parameters. Thus the Sobolev step gives the norm (1.2), not just its version with the supremum outside the integral. This proves (4.1). Finally $(1+h)^{32d}\le C_{d,c}^{n+1}$ for $h\le cn$. ∎

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

Here the entire interior of a (CL) realization belongs to one original tree and uses one low-pass scale $R$. This is the relevant locality: separate original trees may have different scales after the shell expansion. A cutoff belonging to an exterior port is kept outside the realization. Incoming frontier edges are assigned to the first regular object they enter; an edge ending at the lone port of a regular tree is assigned once to that tree, and not again to the continuation.

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

This proves (5.4). Each fixed-order sum is finite in combinatorial indices and is a smooth function of $R>0$; the spatial integrals and their derivatives are dominated by the Schwartz bounds and the corresponding source estimates. Differentiating its real-valued identity therefore gives a real-valued identity. This derivative is the **sum of all product-rule terms**, not any one chosen marked term. ∎

### Lemma 5.3 — Local weighted `vineest`

Consider the unpinned (CL) vine-chain expression of T1742–1750. Suppose its realization lies in one original tree, all frontier cutoffs inside it have a common scale $R\ge L$, and the full LF class is summed with the order and top-layer constraints of that proposition. Do not impose a distinguished leaf mark or a selected-time endpoint face inside this realization. With $h$ frontier factors, its low-pass weighted version satisfies

$$
\|\widetilde K_R^{\mathcal U}\|_{X^{2\eta^8,0,0}}
\lesssim_1 C_\chi^{n_{(2)}+h+1}(1+n_{(2)}+h)^{C_d}
(C_1\sqrt\delta)^{n_{(2)}}
L^{-\eta^8n_{(3)}-\eta^2b+\eta^7}.
\tag{5.7}
$$

The constants in the extra exponential depend on $d,\chi$, not $\delta$. An additional amplitude can be inserted after reduction to each `sumint` expression if it satisfies Lemma 4.2; its cost is its total-variation bound. This last assertion does not authorize an arbitrary amplitude before the LF cancellation.

**Proof.** In the reductions T1753–1881, attach to each regular object its assigned frontier factors. For an incoherent object use Lemma 4.1; its incoherency gain is unchanged. For a coherent object use (5.2), the single-layer profile estimates T1145–1174, and the layer factorization T1235–1244. These operations supply the same approximation and remainder decomposition with modified real profiles. Their constants increase by $C_\chi$ per input and a polynomial of fixed degree per differentiated factor. Products of local polynomials are bounded by an exponential in the total number of local vertices and frontier factors.

For the equal-upper-layer cancellation T1883–1907, replace the two spatial arguments by the same argument before using the leading identity. Differences of ordinary spatial factors are handled as in T1902. Differences of new factors are handled by Lemma 3.2: the argument difference is $\pm r$, so they supply the required explicit $|r|$ for case (b) of `sumint`. Their remaining amplitudes have the stated Fourier-measure bounds. The leading sum is zero by Lemma 5.2, since it is the difference of a real number and its conjugate. The time-interlacing and time-Hölder errors are unchanged; multiplication by the time-independent factors preserves their bounds.

For unequal upper layers, use the continuous constant time extensions in T1915–1920. Separated intervals supply the source's time-Hölder factor. In adjacent intervals, replacing the upper time by the lower time again produces that factor; the remaining sum is restricted to the common lower-root family in T1921. Keep incoming frontier factors assigned using the *original* parent layers. Their combined exponent is $c(q_1,q')+c(q_2,q')$, unchanged when the couple and tree are exchanged. At the common spatial argument their product is real and common to the two sums. If $q_1=p>q_2$, the surviving lower-root family has no internal layer-$p$ tuples, but the single incoming factor $\chi(k/R)$ must still be retained. The remaining common family is covered by Lemma 5.2. This accounts for the upper-layer mismatch without losing a frontier factor.

All uncanceled cutoff factors on the remaining alternative variables satisfy Lemma 4.2. Apply that lemma to each resulting expression, keeping its bad-vine alternative, and use the same order accounting and incoherency accounting as T1923. This proves (5.7). ∎

Lemma 5.2 resolves the tuple issue for the actual common low-pass product. It does **not** prove a reality identity for arbitrary independently marked profiles. That stronger assertion is neither used nor claimed.

## 6. Extracting the first cutoff gain

### Lemma 6.1 — One frontier derivative per tree

For a nonbottom shell, with $D(u)=-u\cdot\nabla\chi(u)$,

$$
H_{j,M}=\int_{M/2}^M\frac{dR}{R}
\sum_{v\in B_j}D(k_v/R)\prod_{w\in B_j\setminus\{v\}}\chi(k_w/R).
\tag{6.1}
$$

Consequently a product of $2P$ nonbottom shells is an integral of at most $\prod_j|B_j|$ summands, each having one selected frontier vertex per tree. Its parameter measure has mass $(\log2)^{2P}$. If the expanded garden has order $n$, then $\prod_j|B_j|\le(2n+1)^{2P}$ whenever all these shells are nonzero.

**Proof.** Differentiate $A_{j,R}$ by the product rule and use $\partial_R\chi(k/R)=R^{-1}D(k/R)$. Integrate between $M/2$ and $M$ and multiply the resulting identities. A ternary tree with $a$ branching nodes has $2a+1$ leaves, so the original frontier has at most $2n+1$ vertices. If it is empty, the nonbottom shell is zero and the assertion has no nonzero summand. ∎

### Lemma 6.2 — Propagation and an exact polynomial extraction

Let $v$ be a nonflower frontier vertex and let $\mathcal L(v)$ be its final descendant leaves. Then

$$
k_v=\sum_{\ell\in\mathcal L(v)}\epsilon_{v\ell}k_\ell,
\qquad \epsilon_{v\ell}\in\{+1,-1\}.
\tag{6.2}
$$

If $D(k_v/R)\ne0$, $R\in[M/2,M]$, some such leaf satisfies $|k_\ell|\ge M/(2|\mathcal L(v)|)$. More precisely, for every fixed even integer $a\ge0$, the factor $D(k_v/R)$ has an exact representation

$$
D(k_v/R)=M^{-a}\,b_{M,R}(k_v)
\sum_{\boldsymbol\beta}c_{\boldsymbol\beta}
\prod_{\ell\in\mathcal L(v)}k_\ell^{\beta_\ell},
\tag{6.3}
$$

where $\sum_\ell|\beta_\ell|\le a$, $\sum_{\boldsymbol\beta}|c_{\boldsymbol\beta}|\le C_{d,a}(1+|\mathcal L(v)|)^a$, and $b_{M,R}$ has Fourier-measure norm at most $C_{d,a,\chi}$ uniformly for $M\ge2$. At most $a$ distinct final leaves are modified in a monomial of (6.3).

**Proof.** Iterating $k_{\mathrm{parent}}=k_1-k_2+k_3$ proves (6.2); no flower occurs below a nonflower frontier vertex. Since $D$ is supported in $1\le|u|\le2$, the triangle inequality proves the large-leaf assertion.

Set

$$
b_{M,R}(x)=M^a\langle x\rangle^{-a}D(x/R).
$$

On writing $x=Ru$, this is $(M/R)^a(R^{-2}+|u|^2)^{-a/2}D(u)$. It is supported in a fixed annulus and has uniformly bounded derivatives of every fixed order for $R\ge1$, $M/R\in[1,2]$. The usual compact-support Sobolev estimate for the Fourier $L^1$ norm follows directly by integrating by parts $d+1$ times in each coordinate, and is uniform in $M,R$. Scaling preserves that norm. Expand the polynomial
$(1+|\sum_\ell\epsilon_{v\ell}k_\ell|^2)^{a/2}$. The multinomial theorem gives total degree at most $a$ and coefficient sum at most $C_{d,a}(1+|\mathcal L(v)|)^a$. Multiplication by $M^{-a}b_{M,R}(k_v)$ proves (6.3). ∎

Taking $a=40d$ in every tree extracts exactly $M_1^{-80dP}$. A final pair can receive monomials from its two leaves, so its total added degree is at most $80d$. There are at most $80dP$ modified leaf occurrences. The coefficient sum and selected-vertex choices are bounded by $C_{d,P}(1+n)^{(80d+2)P}$. This is an exact extraction before taking absolute values, which avoids replacing a cancellation-sensitive integrand by its pointwise majorant.

For the external weight, conservation also gives, in each original tree,

$$
k-\zeta k'=\sum_{\ell\ne f_j}\epsilon_{j\ell}k_\ell.
\tag{6.4}
$$

Pointwise, $2\Lambda$ powers of decay per tree pay for the requested $4\Lambda P$ powers; a paired input is charged by at most two trees. Together with the first-cutoff charge and a $40d$ analytic reserve, this requests at most $4\Lambda+80d+40d$ powers of decay from one input. The available $\Lambda_p=40d\Lambda$ exceeds this under the source's parameter choices. This observation is only a decay budget, not a bound for the grouped sum.

### OPEN 6.3 — Marked grouped estimates and external decay

The missing assertion is the following stability statement. Start with any complete LF family used in the proof of `layergarden`, with the original-tree labels and truncation constraints retained. Insert the sum of the marked terms in (6.1)–(6.3), and the capped/pinned modifications of Section 2. After extracting $M_1^{-80dP}$ and $\langle k-\zeta k'\rangle^{-4\Lambda P}$, the remaining family must admit the source's reductions with additional cost

$$
C_{P,\chi}^{,n+1}\,C_{P,\delta}\,(1+n)^{A_{P,\delta}}L^{c_dP},
\tag{6.5}
$$

where the exponential base $C_{P,\chi}$ is independent of $\delta$, and the integer $A_{P,\delta}$ and constant $C_{P,\delta}$ are independent of $n,L,M_1,M_2,k,k'$. The loss exponent $c_d$ must be explicit and fit the total budget in Section 10. Gains attached to every unmarked incoherent object and every unmarked bad vine must be retained. For bottom first blocks no extraction is required; their requested factor will be paid from the $L$ budget.

**What remains unproved.** Formula (6.3) modifies different final-leaf profiles in different summands. Lemma 5.2 permits a common profile change, or the full derivative of a common-scale identity. It does not permit independently discarding marked summands and applying the leading cancellation to each remaining summand. Protecting every object touched by one of the at most $80dP$ leaf occurrences is a plausible repair, but a protected object can have arbitrarily large order. Estimating its entire interior trivially would lose $L^{Cn}$. The required repair is a decomposition into ordinary pieces and a bounded number of marked chain segments, retaining their analytic gains.

The external-decay extraction has the same grouping issue. Expanding a polynomial of degree $2\Lambda$ and declaring every resulting leaf protected would allow $O(\Lambda P)$ protected leaves. Since $\Lambda$ depends on $\delta$, a loss $L^{C\Lambda P}$ is not the required $L^{c_dP}$. An acceptable proof must keep the external-weight extraction within the weighted amplitude estimates or another argument with a bounded number of protected boundaries. No such complete argument is supplied here.

## 7. Pins and boundary graphs

### Lemma 7.1 — Localized spectral fibers and mixed-norm conversion

Suppose every incident momentum at a marked branching node belongs to a fixed unit ball in a translate of $\mathbb Z_L^d$. The set of possible values of its resonance $\Omega$ has cardinality at most $(C_dL)^{4d}$, uniformly in the centers of the balls. The same bound holds for the number of intervals of fixed length needed to cover the corresponding discrete values of $\alpha=\delta L^{2\gamma}\Omega$.

If $B(\alpha_E,\alpha_J)$ is any measurable coefficient, and each of the $b$ exceptional variables $\alpha_E$ is restricted to a union of at most $Q$ intervals of length at most $c$, then

$$
\int_{\alpha_E\text{ allowed}}\int|B(\alpha_E,\alpha_J)|\,d\alpha_Jd\alpha_E
\le(cQ)^b\sup_{\alpha_E}\int|B(\alpha_E,\alpha_J)|\,d\alpha_J.
\tag{7.1}
$$

**Proof.** A unit ball contains at most $(C_dL)^d$ points of the translated lattice. There are at most four incident momenta, so there are at most $(C_dL)^{4d}$ tuples and hence at most this many resonance values. Cover each value by one fixed-length interval; overlaps only improve the bound. Fubini and the measure bound $(cQ)^b$ prove (7.1). No bound on the locations of these intervals is used. ∎

### Lemma 7.2 — The terminal-pin algebra

Let a regular chain have linked phases $\beta_1,\ldots,\beta_{2m}$, with a legal pairing and each pair equal to $(\alpha_j,-\alpha_j)$. Inserting a pin at its last time gives the exact expression

$$
\int_{t>t_1>\cdots>t_{2m}>a}
\delta(t_{2m}-s)e^{\pi i\sum_\ell\beta_\ell t_\ell}
\,dt_1\cdots dt_{2m}
=
\mathbf1_{a<s<t}e^{\pi i\beta_{2m}s}
\int_{t>t_1>\cdots>t_{2m-1}>s}
 e^{\pi i\sum_{\ell<2m}\beta_\ell t_\ell}
\,dt_1\cdots dt_{2m-1}.
\tag{7.2}
$$

Fixing $\beta_{2m}$ fixes its linked partner also. Translating a chain contained in a single layer $[q,q+1]$ to $[0,1]$ changes only an explicit phase; with all pairs present that phase is $1$.

**Proof.** Evaluate the Dirac integral in the last variable. The remaining inequalities are exactly those on the right. A linked partner has the opposite frequency by definition. Under translation by $q$, the phase multiplier is $e^{\pi iq\sum\beta_\ell}$; the sum is zero for complete pairs. For the odd integral the missing phase is canceled by the translated pinned factor. ∎

D21 2684–2694 uses (7.2), the class-$J$ and class-$R$ calculus of D21 955–1098, and the residual-molecule denominators to retain integrability in all but at most two spectral variables per pin. In its single-layer setting, this is an existing result. Lemma 7.1 explains the finite spectral-fiber cost once its hypotheses are available; it does not establish the mixed-norm premise.

### OPEN 7.3 — Layered pinned estimate

A sufficient precise extension is: for $b$ marked flower-parent times in a localized layered expression, the coefficient decomposition of the ordinary reduction can be replaced by a decomposition with at most $2b$ exceptional spectral variables. In each term, leave the source's explicit factors $\chi_\infty(\alpha_j)/\alpha_j$ outside the integrable coefficient. For the remaining coefficient $C$, replace every source $L^1$ norm in the spectral variables by

$$
\sup_{\alpha_E}\int\!\int
 w(\lambda)\,|\partial_{\alpha_J}^{\rho}C(\lambda,\alpha_E,\alpha_J)|
\,d\lambda\,d\alpha_J,
\qquad |E|\le2b,
\tag{7.3}
$$

with the same derivative orders, time-frequency weights $w$, and per-unmarked-piece bounds required in the particular reduction. Pure boundary oscillations are to be recorded separately; if a Fourier variable is shifted by a fixed exceptional resonance, its center must be shifted in (7.3) and the resulting modulation must be passed to the adjacent integral. The representation must preserve those identities, not bound a rapidly oscillating boundary phase by a uniform weighted Fourier norm.

After restricting the exceptional variables to their available unit intervals, the extra cost must be at most $C_{P,\chi}^{n+1}C_{P,\delta}L^{c_db}$, including all modulations subsequently consumed. The estimate must hold uniformly in layer assignments and unit-ball centers, and retain the powers of $L$ from unmarked incoherencies. It must also hold for the bounded collection of endpoint faces in Lemma 9.1 below.

**Where the proof stops.** The terminal odd-chain mechanism is explicit in (7.2), and D21 proves its single-layer analytic estimate. A coherent object containing a layer-$p$ flower and its cap has equal parent layers $p$, so its coherent part reduces to that setting. This does not cover an incoherent regular object containing the pin, a split chain with a linked partner in another layer, or a new face created by selected-time integration. The independent layer restrictions and the boundary modulations must be carried through the class-$J/R$ recursion. Neither (7.2) nor the unpinned estimate (4.1) proves that recursion. Taking a trace of a previously integrated kernel is not a replacement: point evaluation of an integrand is not bounded by the absolute value or norm of its integral.

### Lemma 7.4 — Graph bookkeeping for excision

Let a finite molecule have $v$ atoms, $e=2v-R$ bonds, and maximum degree four, counting bond multiplicity. Delete an atom set $S$ and all its incident bonds. Write $e_S$ for the number of bonds inside $S$, $q$ for the number crossing from $S$ to its complement, and $D_S=\sum_{x\in S}(4-\deg x)$. The remaining graph satisfies

$$
v'=v-|S|,\qquad e'=e-e_S-q,\qquad
2v'-e'=R+\frac{q-D_S}{2}.
\tag{7.4}
$$

It has at most $c+q$ nonempty components if the original graph had $c$ components. There are at most $q$ remaining atoms incident to a deleted bond. In particular, if $|S|=b$, then $q\le4b$; if instead $S$ is large but $q=O(b)$, the boundary count is still $O(b)$.

**Proof.** Count deleted bonds and atoms. The degree identity $2e_S+q=4|S|-D_S$ gives (7.4). A remaining component either equals an original component disjoint from $S$, or contains an endpoint of a crossing bond. There are at most $c$ of the first kind and $q$ of the second. Every remaining atom adjacent to the deletion uses at least one crossing bond. ∎

### OPEN 7.5 — Exceptional pieces and the modified `subpro`

The required statement is a version of T2040–2052 for components with boundary. Protect the special vertices listed after Lemma 2.1, the marks required in Section 6, the pins, and the selected-face vertices. There must be a reduction with at most $c_db$ additional boundary atoms when there are $b$ protected incidences, with the following properties:

1. The remaining components satisfy the exact bond count (7.4), with the original component defects and all new crossing bonds recorded. They need not be connected or ordinary irreducible gardens.
2. There is a disjoint collection $\mathcal C_1$ of the surviving SG HV, (CN), and root-(CL) objects, together with the genuine hinge set $H$ from unmarked VC contractions and a separate exceptional boundary set $B$ of size at most $c_db$.
3. Every triple bond has an endpoint in $H\cup B$. Every degenerate atom outside $H\cup B$ is tame in the sense of T2046, with the fixed boundary momenta included among the allowed fixed values.
4. An SG vine-like object disjoint from $H\cup B$ and not contained in $\mathcal C_1$ is contained in a DV, LG, or ZG object disjoint from $\mathcal C_1$ and $H\cup B$.
5. Each genuine hinge has the two SG bonds of T2048. No SG-pair property is asserted for an arbitrary atom of $B$.
6. An SG object disjoint from $B$, not contained in $\mathcal C_1$, and meeting $H$ has the hinge configuration in T2049. Objects meeting $B$ are handled by the exceptional-piece estimate, not by pretending that $B$ consists of ordinary hinges.

The accompanying counting and analytic estimates must extend T2075–2255 with cost $C_{P,\chi}^{n+1}C_{P,\delta}L^{c_db}$ and the same gains away from the exception set. Retained ladder pieces must be independent of the external nonsmooth amplitude in their internal variables, the hypothesis used at T2083.

**Available part and missing part.** T1519 decomposes an ordinary vine into at most three ladders and fewer than twenty additional atoms. T1978–1991 bounds a ladder by $(C_1\delta)^m L^{-(\gamma_1-\sqrt\eta)g+20d}$ uniformly in its boundary data. If a bounded number of such pieces can be isolated with boundary data satisfying OPEN 7.3, they cost $L^{c_db}$ rather than $L^{Cn}$. Already three ladders can cost $L^{60d}$; the claim of only $L^{20d}$ per entire exceptional vine in T2297 is not obtained by adding these quoted bounds.

Lemma 7.4 proves the elementary boundary counts. It does not prove clauses 2–6 after a new excision, or the counting estimate for objects meeting $B$. Deleting a marked vertex can change which vine is maximal, and a regular object containing one mark can be long. A proof needs to specify the cuts through those objects and check the six clauses for the resulting graph. This construction and its quantitative analytic bound remain open here.

## 8. Resonance cutoffs on regular chains

Choose an even real Gevrey-2 cutoff $\vartheta$ on $\mathbb R$, equal to one on $[-1,1]$ and zero outside $[-2,2]$, with $0\le\vartheta\le1$. Fix $A$ such that $\|\vartheta^{(r)}\|_\infty\le A^{r+1}(r!)^2$. For each original tree put

$$
U_{j,M}=\prod_{v\in\mathcal S_j}\vartheta(\Omega_v/M),\qquad
V_{j,M}=U_{j,M}-U_{j,M/2}\ (M>L),\qquad V_{j,L}=U_{j,L},
\tag{8.1}
$$

where $\mathcal S_j$ is the stem branching set with the flower parent omitted. Empty products are again one. A nonbottom shell vanishes if $\mathcal S_j$ is empty. Its derivative expansion selects one $|\Omega_v|\asymp M$ in each tree, leaving the other upper filters present.

For a regular linked pair the independent spectral coordinate is $\alpha=\delta L^{2\gamma}\Omega$, up to a harmless fixed factor of two according to the bilinear convention. Thus its upper filter is $\vartheta(\alpha/S)$ with $S=\delta L^{2\gamma}M$. Since $M\ge L$, we may assume $S\ge1$ by choosing $L$ after $\delta$.

### Lemma 8.1 — Stability of the integrable coefficient

Let $C(\lambda,\alpha_1,\ldots,\alpha_m)$ satisfy the coefficient estimates D23 965–967, namely

$$
\int w_1(\lambda)|\partial_\alpha^\rho C|\,d\lambda d\alpha
\le C_0^m(2|\rho|)!,\qquad
\int w_0(\lambda)\max_j\langle\alpha_j\rangle^{1-\eta/2}|C|
\,d\lambda d\alpha\le C_0^m,
\tag{8.2}
$$

where $w_1=\max\langle\lambda_i\rangle^{1-\eta/8}$ and $w_0=\max\langle\lambda_i\rangle^{\eta/4}$. Multiply $C$ by at most two factors $\vartheta(\alpha_j/S_j)$ per coordinate, with $S_j\ge1$. The product $C_*$ satisfies

$$
\int w_1|\partial_\alpha^\rho C_*|\le C_A^{m+1}(4|\rho|)!,\qquad
\int w_0\max_j\langle\alpha_j\rangle^{1-\eta/2}|C_*|\le C_0^m.
\tag{8.3}
$$

The constant $C_A$ depends on $A,C_0$, not on the scales. If a bounded factor additionally restricts one integrable coordinate to $|\alpha_j|\ge S/2$, then

$$
\int w_0|C_*|\le C_{\eta} C_0^m S^{-(1-\eta/2)}.
\tag{8.4}
$$

**Proof.** Each differentiated cutoff product is bounded by $A_1^{m+|\nu|}(2|\nu|)!$ for a constant $A_1$ depending on $A$. Apply the product rule, (8.2), and the inequalities
$(2a)!(2b)!\le(2a+2b)!$ and $\sum_{\nu\le\rho}\binom\rho\nu=2^{|\rho|}$. This bounds the first integral by $C_1^{m+|\rho|+1}(2|\rho|)!$. For fixed $C_1$, the supremum of $C_1^r(2r)!/(4r)!$ over integers $r\ge0$ is finite; the ratio tends to zero by its successive-term ratio. Absorb that supremum into $C_A^{m+1}$. The second inequality follows from $|\vartheta|\le1$. On the restricted support $\langle\alpha_j\rangle^{1-\eta/2}\ge c_\eta S^{1-\eta/2}$, which proves (8.4). ∎

This lemma closes the integrable-coefficient part of the cutoff question. It does not cover a coordinate already extracted as a reciprocal spectral factor, nor does it prove the discrete sum-to-integral step after such a factor is truncated.

### OPEN 8.2 — Layered, spectrally truncated regular-chain estimate

Here is the missing analytic claim in a form suitable for direct verification. In every regular-object reduction used in T1090–1244, allow the multiplier (8.1) at any subset of the layer-$p$ stem vertices, with multiplicity at most two per independent linked frequency. Also allow the protected pins and selected-time faces of OPEN 7.3, and the modified final profiles of Section 6. For an object of order $2m$, the normalized coefficient and decoration sum must admit the same approximation/error reduction as required for its unmarked portions, with extra cost

$$
C_{P,\chi,\vartheta}^{m+1}C_{P,\delta}L^{c_d b},
\tag{8.5}
$$

where $b$ is its number of protected incidences, independently of all upper scales and output momenta. The bound must hold for $2m\le N^4$, retain every unmarked incoherency gain, and keep the principal-value interpretation of extracted reciprocal factors. If $a$ selected high-resonance occurrences are assigned to the object, the bound after their time integrations, or an equivalent direct spectral estimate, must include at least

$$
\prod_{\text{selected occurrences}} M_2^{-1/18}.
\tag{8.6}
$$

Here a linked frequency can be selected on both of its vertices; the occurrences, rather than only distinct frequencies, are counted. A proof may group those two occurrences and obtain $M_2^{-1/9}$. Bounds for individual endpoint terms may be replaced by bounds for explicitly retained signed collections of faces, but those collections and their multiplicities must be specified before their absolute values are taken.

**Exact obstruction to applying a quoted statement.** The spectral form in D23 995 is

$$
\Psi(\alpha)=\prod_{j\in Z}\frac{\chi_\infty(\alpha_j)}{\alpha_j}\,Psi_1(\alpha_{Z^c}).
$$

After (8.1), an extracted factor becomes

$$
\frac{\chi_\infty(\alpha_j)\vartheta(\alpha_j/S_j)}{\alpha_j}.
\tag{8.7}
$$

It cannot be included in $\Psi_1(\alpha_{Z^c})$, which has no dependence on $\alpha_j$. Lemma 8.1 therefore does not verify the hypotheses of `approxnt` for (8.7). Evenness preserves the odd parity of the reciprocal factor, but parity alone is not the quantitative discrete estimate. One needs to repeat the proof with the uniformly scaled numerator in (8.7), including a selected high-frequency factor and the mixed norm (7.3). D23 1002 also states $m\le(\log L)^3$, whereas T allows order up to $N^4$, a much larger fixed power of $\log L$. Using T's existing unweighted regular-object results is legitimate; claiming a newly truncated version by directly citing D23 requires addressing this order range as well.

A route is to extend the class-$J/R$ decomposition with explicit truncated reciprocal factors and fixed exceptional frequencies, then rerun the bilinear sum estimates with that class. The integrable factors have already been handled by Lemma 8.1. Uniform control of the extracted factors and the combined pins/faces is not proved in this document. This is a missing proof, not a demonstrated counterexample.

## 9. Selected-time integration and small-gap tops

### Lemma 9.1 — Exact time integration with faces

Fix a raw decorated flower garden before collapsing regular objects. Select one vertex $v_j\in\mathcal S_j$ in each of $a\le2P$ different original trees, and suppose $|\Omega_{v_j}|\ge cM_2>0$. Keep all other times fixed. With $\omega_v=\pi\zeta_v\delta L^{2\gamma}\Omega_v$, integration in the selected times replaces the expression by a signed sum of endpoint-face expressions with factors

$$
\prod_{j=1}^a(i\omega_{v_j})^{-1},\qquad
\left|\prod_{j=1}^a(i\omega_{v_j})^{-1}\right|
\le (\pi c\delta)^{-a}L^{-2\gamma a}M_2^{-a}.
\tag{9.1}
$$

There are at most $8^a$ terms after partitioning according to the maximizing child time. Each face substitutes a selected time by its parent time, the external top time, its maximal branching-child time, or the layer floor. It imposes the corresponding remaining inequalities and adds the selected frequency to the phase at that endpoint. All spatial filters remain unchanged.

**Proof.** The raw amplitude is independent of branching times except for the displayed exponential phases, order inequalities, and the already fixed pins. A selected vertex is not a flower parent, so its time is not pinned. Its allowed interval is $(A_v,B_v)$, where $A_v$ is the maximum of its layer floor and the times of its branching children that constrain it, and $B_v$ is its parent time or external top time, intersected with the layer ceiling. On the layer-$p$ stem the ceiling is redundant with this upper bound. There are at most four candidates for $A_v$. Partition the remaining time domain according to the largest, assigning ties arbitrarily, and retain the indicator $A_v<B_v$.

On each piece,

$$
\int_{A_v}^{B_v}e^{i\omega_v u}\,du
=(i\omega_v)^{-1}(e^{i\omega_v B_v}-e^{i\omega_v A_v}).
$$

There are at most eight resulting terms. Selected vertices in different trees are not related by parent-child time inequalities, so repeat this operation for each of them. Leaf pairings impose no equality of their time variables. This proves the formula, the term count, and the bound (9.1). Substitution into the original exponentials gives exactly the stated phase changes. ∎

A selected resonance can be frozen using Lemma 7.1 after incident-momentum localization. Alternatively retain its reciprocal as a spatial multiplier supported on its annulus. Either procedure must be done inside the protected reduction; freezing a fiber that is not invariant under a cancellation would itself require protection.

### Lemma 9.2 — High-root separation at the relevant frontier

Assume $A_{j,R}\ne0$ with $R\le M_1$ and $|k|\ge M_1^{10}$. Let $b$ be the number of nonflower original frontier vertices in the tree. Every off-stem vertex of the original top tree has momentum of magnitude at most $2bM_1$. Every stem vertex has magnitude at least $|k|-2bM_1$. For $2bM_1\le|k|/4$, a stem vertex and such an off-stem vertex have momentum difference of magnitude at least $|k|/2$.

In particular, an SG (CL) realization containing the flower cannot have its stem leave through one of the opposite-sign free children $u_{21},u_{22}$: it must leave through the same-sign child $u_{11}$.

**Proof.** Express the momentum of an original top subtree as the signed sum of its original frontier momenta, including the flower if present. For an off-stem subtree there is no flower, and the bound follows from $|k_v|\le2M_1$ at the nonflower frontier. For a stem vertex, solve the conservation identity between the root and that vertex; all complementary top subtrees together use at most $b$ frontier vertices. The relative sign of the stem momentum may be negative, but the magnitude estimate is unchanged. Subtract the two magnitude bounds to obtain the separation.

If one of $u_{21},u_{22}$ is on the stem, the other is its off-stem child at a layer-$p$ stem branching vertex. It is a vertex of the original top tree or the root of a lower insertion, hence is included in the preceding frontier bound. Their difference is therefore at least $|k|/2$, contradicting the SG bound $|k_{u_{21}}-k_{u_{22}}|\le1$. Since $b\le2n+1\le2N^4+1$ and $M_1\ge L$, the numerical condition holds for sufficiently large $L$ chosen after $\delta$. ∎

The lemma deliberately does not bound all internal descendants of a lower insertion. Such descendants can have large cancelling momenta while their frontier root is small. That stronger assertion, as suggested by the literal wording at T2300, does not follow from the first cutoff.

### Lemma 9.3 — The affine small-gap-top filter

At a same-sign stem child of a small-gap vine top, write the parent momentum as $e=f+r$ and the three child momenta, in sign order, as $f,a,a+r$. Then

$$
\Omega_{\mathrm{top}}
=|f|^2-|a|^2+|a+r|^2-|f+r|^2
=2r\cdot(a-f).
\tag{9.2}
$$

For fixed vine outputs $r,f$, the upper filter $\vartheta(\Omega_{\mathrm{top}}/M_2)$ is a Fourier-measure amplitude in $a$ with norm at most $\|\mathcal F\vartheta\|_1$, uniformly in $f,r,M_2$. A product of $h$ such factors costs at most $\|\mathcal F\vartheta\|_1^h$ in Lemma 4.2. Its first derivative in $a$ has Fourier-measure norm at most $2|r|M_2^{-1}\int2\pi|\xi||\mathcal F\vartheta(\xi)|\,d\xi$.

**Proof.** Expand the four squares; the $|a|^2,|f|^2,|r|^2$ terms cancel. Fourier inversion in the one-dimensional resonance variable gives

$$
\vartheta(2r\cdot(a-f)/M_2)
=\int\mathcal F\vartheta(\xi)
 e^{-4\pi i\xi r\cdot f/M_2}
 e^{4\pi i\xi r\cdot a/M_2}\,d\xi.
$$

This is a pushforward measure of the asserted total variation. Differentiation inserts $4\pi i\xi r/M_2$. The output-dependent phase has modulus one; the frequency map may depend on $r$. Lemma 4.2 permits both dependencies and proves the claimed use in the time Fourier norm. ∎

This treats the upper filters at those SG tops; it does not turn the quadratic regular-chain filter into a uniformly controlled spatial Fourier amplitude.

### Lemma 9.4 — Where upper filters may be discarded

After the reduction has reached the absolute counting factor in T2090–2097, any remaining product of factors of modulus at most one may be deleted without increasing that factor. This is not valid before the oscillatory sums and grouped cancellations have been estimated.

**Proof.** In the counting factor, every summand is already an absolute value and all restrictions define a subset of the admissible decorations. Removing a multiplier of modulus at most one or enlarging that subset increases the nonnegative sum. Before taking absolute values, the assertion would require $|\sum_z a_z w_z|\le|\sum_z a_z|$, which is false: take $a_1=1,a_2=-1,w_1=1,w_2=0$. ∎

### Lemma 9.5 — Bottom blocks

Suppose a moment bound has been proved with power $L^{BP}$ and the nonbottom gains only. The corresponding desired bottom-block gains are obtained by changing the power to

$$
L^{(B+80d+1/9)P}M_1^{-80dP}M_2^{-P/9}
\tag{9.3}
$$

when both $M_1=M_2=L$. If only one block is bottom, add only its corresponding exponent.

**Proof.** Substitute $M_1=M_2=L$ into (9.3); the factors cancel exactly to $L^{BP}$. No lower bound on a bottom-block resonance is needed or available. ∎

## 10. Conditional assembly and the outstanding loss budget

### Lemma 10.1 — Polynomial overhead and the order of choices

Fix $P$ and a constant $D_P\ge1$ independent of $\delta$. Let $A_{P,\delta}\ge0$ and $E_{P,\delta}<\infty$ be arbitrary constants independent of $n,L$. For every fixed $\varepsilon>0$, if $\delta$ is sufficiently small depending on $D_P,\nu$ and $L$ is then sufficiently large depending on $P,\delta,\varepsilon$, then for all integers $n\ge0$,

$$
E_{P,\delta}(1+n)^{A_{P,\delta}}D_P^n\delta^{8\nu n}
\le L^{\varepsilon P}\delta^{2\nu n}.
\tag{10.1}
$$

**Proof.** The constant
$B_{P,\delta}=\sup_{n\ge0}(1+n)^{A_{P,\delta}}2^{-n}$ is finite: the exponential dominates every fixed power. Choose $\delta$ with $2D_P\delta^{6\nu}\le1$, which uses no $A_{P,\delta}$. Then the left side of (10.1) is at most $E_{P,\delta}B_{P,\delta}\delta^{2\nu n}$. Choose $L$ large enough that $E_{P,\delta}B_{P,\delta}\le L^{\varepsilon P}$. ∎

This handles the shell choices, fixed-degree leaf expansions, choices of selected stem vertices, and distributions among a bounded number of components, provided the grouped estimates have first been established. It does not handle an uncontrolled exponential $C_2^n$.

### OPEN 10.2 — Weighted expansion remainders

Let $\mathcal E^{(1)}$ be the moment-expansion error in T2287, and let $\mathcal E^{(2)}$ be the sum of orders above $N^4$ removed in T2290. For each of the three multiplier choices in (1.1), the required assertion is

$$
|\mathcal E^{(1)}|+|\mathcal E^{(2)}|
\le \tfrac14\langle k-\zeta k'\rangle^{-4\Lambda P}
L^{(100d)^3P}\,G(M_1,M_2),
\tag{10.2}
$$

where $G$ is respectively $1$, $M_1^{-80dP}$, or $M_1^{-80dP}M_2^{-P/9}$. For the $\mathfrak Y$ and $\mathfrak W$ expansions the right side must additionally contain $e^{-100N}$. These estimates are uniform in the dyadic scales, including arbitrarily large $M_2$, and in the external momenta under the stated hypotheses.

The identity in Lemma 2.2 retains the cutoffs in these errors, but is not their estimate. T2290 invokes the earlier unweighted remainder argument without writing its weighted version. The decay extraction and selected-time calculation can also be performed in the error expressions, but one must verify the resulting moment/ansatz bounds and endpoint losses there. No such verification is completed here. An unweighted error bound alone cannot be multiplied by an arbitrarily small $M_2^{-P/9}$.

### Proposition 10.3 — What the missing estimates would imply

Suppose OPEN 6.3, OPEN 7.3, OPEN 7.5, OPEN 8.2, and OPEN 10.2 hold. Suppose in addition that their reduction and counting estimates give, using T2237–2255, the following explicit aggregate bound for the order-$n$ contribution before the polynomial absorption of Lemma 10.1:

$$
E_{P,\delta}(1+n)^{A_{P,\delta}}D_P^{n+1}\delta^{8\nu n}
\langle k-\zeta k'\rangle^{-4\Lambda P}L^{BP}
\,G_{\mathrm{nonbottom}}(M_1,M_2),
\tag{10.3}
$$

where $D_P$ is independent of $\delta$, and the **numerically verified** loss exponent satisfies

$$
B+80d+\frac19+3\le(100d)^3.
\tag{10.4}
$$

Then (1.1) holds, as do its $e^{-100N}$ versions for $\mathfrak Y,\mathfrak W$, with the normalization and order-zero conventions of Section 1.

**Proof.** Use Lemma 10.1 with $\varepsilon=1$ and absorb the extra fixed $D_P$ by increasing the threshold for $L$. Lemma 9.5 supplies any bottom gains at cost at most $(80d+1/9)P$ powers of $L$. Thus the sum of the retained orders for $\mathfrak X_{\mathrm{reg}}$ is bounded by

$$
\langle k-\zeta k'\rangle^{-4\Lambda P}
L^{(B+1+80d+1/9)P}G(M_1,M_2)
\sum_{n\ge1}\delta^{2\nu n}.
$$

The last sum is at most one if $\delta^{2\nu}\le1/2$. Any fixed constants left in this estimate are absorbed using one further $L^P$ of the margin in (10.4), and $L$ can be increased so this main contribution is at most half the right side of (1.1). Add (10.2).

For $\mathfrak Y$, every original top tree has order above $N$, and its three root-child subtrees have orders at most $N$. For $\mathfrak W$, every original top tree has order above $N$, both flower-sibling subtrees and the tree obtained by collapsing the flower parent have orders at most $N$. These are the exact T2273 restrictions retained in Lemma 2.1. Consequently the expanded total order is at least $N+1$ in either moment expansion; lower-layer insertions cannot reduce it. The complete marked reduction assumed above respects these original-tree restrictions, so (10.3) can be summed only over $n\ge N+1$. Choose $\delta$ additionally so $\delta^{2\nu}\le e^{-102}$. Then

$$
\sum_{n\ge N+1}\delta^{2\nu n}
\le\frac{e^{-102(N+1)}}{1-e^{-102}}
\le e^{-100N}.
$$

Apply the $\mathfrak Y$ or $\mathfrak W$ version of (10.2). These choices of $\delta$ depend on $P$ and the exponential base in (10.3), and precede the choice of $L$. ∎

The aggregate hypothesis (10.3) is deliberately explicit. It includes the extension of the ordinary rigidity count to marked components with boundary; it is not inferred merely from the scalar lemmas above.

The loss accounting currently established and required is as follows.

| Operation | Established extra cost | Remaining requirement |
|---|---:|---|
| Capping and exact moment identity | No branching normalization or decoration multiplicity loss | Capped inputs and pins require OPEN 7.3 |
| Low-pass/shell algebra | $B_0^h$ and $2^{2P}$ | None at the algebraic level |
| Weighted incoherent object | $C_\chi^{h+1}(1+h)^{32d}$ | Marked/pinned extension is separate |
| Unmarked local weighted LF chain | (5.7), no new power of $L$ | Marked pieces must be removed or estimated by OPEN 6.3/7.5 |
| First-shell extraction | $M_1^{-80dP}C_{d,P}(1+n)^{(80d+2)P}$ | Grouping and external decay: OPEN 6.3 |
| One exceptional spectral variable | At most $(C_dL)^{4d}$ in Lemma 7.1 | Existence and number of exceptional variables: OPEN 7.3 |
| Ordinary ladder | Source loss $L^{20d}$ per ladder | Boundary reduction and affected-vine count: OPEN 7.5 |
| Selected time | At most $8$ faces and $(c\delta L^{2\gamma}M_2)^{-1}$ per selected vertex | Uniform estimates of the faces and remaining filters: OPEN 7.3/8.2 |
| SG-top upper filter | $\|\mathcal F\vartheta\|_1$ per filter | No local amplitude gap remains |
| Integrable regular spectral coefficient | Lemma 8.1 | Extracted reciprocal factors and combined marked estimate: OPEN 8.2 |
| Bottom first/second blocks | $L^{80dP}$ and $L^{P/9}$ | Must fit (10.4) |
| Polynomial choices and order sum | Lemma 10.1 and a geometric series | Requires a $\delta$-independent exponential base |
| Expansion errors | Exact weighted identity only | OPEN 10.2 |

In particular, an unspecified $L^{C_dP}$ does not establish the printed numerical exponent $(100d)^3P$. A completed proof must assign numerical upper bounds to the exceptional-piece and mixed-norm losses and verify (10.4). This budget check is part of OPEN 7.5 and the aggregate requirement (10.3), not an additional proved estimate.

## 11. Dependency list

The following list separates proved-source inputs actually used in the lemmas from proposed extensions. A reference to the flower proof itself identifies the requested modification; it is not used as a proof of that modification.

| Source and lines | Result or construction | Use here |
|---|---|---|
| T565–575 | Moment-cumulant identity and balanced blocks | Lemma 2.2, conditional on the assumed lower-layer ansatz |
| T581–591 | $X$ and Schwartz norms; restricted extension norm | (1.2), Lemmas 4.1–4.2 |
| T606–615 | Constant dependencies and $\Lambda_p,N_p$ | Quantifier order, decay reserve, Lemma 10.1 |
| T630–647 | Signs, gardens, decorations, and resonances | Lemmas 2.1, 6.2, 9.2–9.3 |
| T650–662 | Layering and recursive canonical construction | Lemma 2.1 |
| T671–674; T712–714 | Ordinary garden/tree normalization and time domains | Section 1; Lemmas 2.2 and 9.1 |
| T689–708 | Lower-layer ansatz and error bounds assumed in the induction | Lemma 2.2; the weighted use remains OPEN 10.2 |
| T731–738 | Ordinary truncation data | Comparison with retained flower labels in Lemma 2.1 |
| T761–779 | `layergarden` statements | Unweighted target for the conditional reduction; not directly applied to caps |
| T826–879, especially T870 | Regular objects, linkage, prime decomposition | Coordinates in Lemma 4.1; the source decomposition underlying the proposed marked reduction |
| T889–903 | `canonequiv` and `layerreg1` | Canonicity in Lemma 2.1; full coherent structure in Lemma 5.1 |
| T953–976 | `proplayer1` and basic modulated sum estimates | Source analytic bound in Lemma 4.1 |
| T981–1017 | Derivative reserve, localization, Fourier amplitude removal | Detailed extension in Lemma 4.1 |
| T1090–1123 | Coherent approximation and reality statements | Lemmas 5.1–5.3; scope of OPEN 8.2 |
| T1145–1174 | `regref1`, including real-profile input flexibility | Lemmas 5.1–5.3 |
| T1175–1231 | `regref2`, `regref3`, time cancellation, spatial tuple factors | Lemma 5.2 |
| T1235–1244 | Exact coherent layer factorization | Lemma 5.1 |
| T1249–1286 | Expanded tuple identity and time merging | Full multiplicity argument in Lemma 5.2 |
| T1295–1321 | Molecules, bonds, external root constraints | Graph context for Lemma 7.4 and OPEN 7.5 |
| T1345–1353 | (CL) realization and free children | Locality in Section 5; Lemma 9.2 |
| T1447–1454; T1463–1487 | Unit twist, LF replacement families, layer/order preservation | Lemma 5.3; original-label restrictions retained in OPEN 7.5 |
| T1501–1519 | Ladder/vine structure and layer counts | Exceptional-piece discussion in OPEN 7.5 |
| T1595–1625 | `sumint`, its hypotheses, and Fourier reduction | Lemma 4.2 |
| T1627–1732 | Scalar exponential-sum bounds and two Fourier-norm endpoint bounds | Norm-order justification in Lemma 4.2 |
| T1733–1755 | Reduced vine expression and `vineest` | Lemma 5.3 |
| T1770–1881 | Alternative variables and regular-object reductions in a vine | Lemma 5.3 |
| T1883–1907 | Equal-layer LF cancellation and error cases (a)–(d) | Lemmas 3.2 and 5.2–5.3 |
| T1911–1923 | Unequal-layer time extension and common surviving family | Lemma 5.3, including the retained incoming frontier factor |
| T1926–1961 | Stage-1 splicing and boundary amplitude | Ordinary reference construction for OPEN 7.5 |
| T1978–1991 | `ladderl1new` | Source bound quoted in OPEN 7.5 and loss table |
| T1994–2013 | `ladderl1old` and available spectral sets | Source coefficient norm to be extended in OPEN 7.3 |
| T2040–2052 | `subpro`, all six clauses | Exact modifications stated in OPEN 7.5 |
| T2075–2083 | Coarse ladder estimate and splitting at hinges | Independence and boundary requirements in OPEN 7.5 |
| T2090–2097 | Absolute spectral-fiber counting reduction | Lemma 9.4 |
| T2237–2255 | Rigidity count and final spare $\delta$ powers | Conditional hypothesis (10.3) and Lemma 10.1 |
| T2259–2273 | Flowers, raw kernels, $\mathfrak X,\mathfrak Y,\mathfrak W$ | Sections 1–2; exact top-tree conditions in Proposition 10.3 |
| T2279–2286 | `flowerest1` | Intended conclusion only |
| T2287–2303 | Flower expansion and proposed proof adjustments | Identification of errors and required extensions; not assumed as their proof |
| D21 955–1098 | Class-$J/R$ calculus and regular-chain decomposition | Existing single-layer mechanism described after Lemma 7.2; proposed layered extension is OPEN 7.3 |
| D21 2682 | Localized flower input | Comparison with cap/fixed-input modification; no automatic Schwartz bound is inferred |
| D21 2684–2694 | Terminal pin, odd chain, residual denominator, mixed-norm conversion | Existing single-layer input for OPEN 7.3; (7.1)–(7.2) are proved independently here |
| D21 2699–2705 | Corollary 11.3, high-resonance gain | Motivation for OPEN 8.2; not cited as a layered truncated-chain theorem |
| D23 949–978 | Regular spectral coefficient decomposition and bounds | Lemma 8.1; form of the extracted factors in OPEN 8.2 |
| D23 984–1009 | `approxnt`, amplitude assumptions, spectral class, order limit | Exact hypothesis comparison in OPEN 8.2; no unproved weighted version is applied |

The proof of Lemma 5.3 uses the regular-object estimates as stated in T; it does not independently reprove their entire imported D21/D23 theory. The new coefficient estimate in Lemma 8.1 is independent of the unsupplied extension of `approxnt`. The graph identity in Lemma 7.4 is independent of the unsupplied extension of `subpro`.

## 12. Completion status

The capped identity, cutoff algebra, incoherent weighted estimate, Fourier-measure `sumint` estimate, common-profile tuple identity, unmarked local weighted vine estimate, exact first-shell extraction, elementary spectral-fiber accounting, selected-time faces, affine SG-top cutoff, and bottom-block accounting have proofs above.

The full flower estimate has **not** been established. Five explicit assertions remain: the marked grouped estimate and external decay (OPEN 6.3), the layered pinned/face estimate (OPEN 7.3), the exceptional-piece reduction and its numerical loss/counting budget (OPEN 7.5), the combined spectrally truncated regular-chain estimate (OPEN 8.2), and the weighted moment-expansion remainders (OPEN 10.2). Proposition 10.3 shows the final summation once these assertions and the stated aggregate budget are verified. No Lean formalization or source-file change has been made.

STATUS: DONE WITH OPEN ITEMS: 6.3 marked grouped estimates and external decay; 7.3 layered pinned and endpoint-face estimates; 7.5 exceptional-piece reduction, modified subpro, and numerical counting/loss budget; 8.2 layered spectrally truncated regular-chain estimate; 10.2 weighted expansion remainders.
