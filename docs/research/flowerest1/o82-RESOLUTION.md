# OPEN 8.2: truncated reciprocal factors and the remaining marked-chain estimate

## 1. Result and scope

**Current status: CLOSED WITH VARIANT in §19 (Theorem 8.2′); see the final STATUS line and the referee revision in §22. The following text records the earlier partial analysis.**

OPEN 8.2 is not closed. This note proves uniform estimates for the truncated reciprocal factors, the exact cutoff version of the **unpinned spectral decomposition**, and the **one-frequency discrete-to-principal-value approximation**. In particular, the extracted factor in supplement (8.7) is not itself an obstruction to a uniform scalar sum-to-integral estimate. The outstanding assertion is the simultaneous reduction of long marked chains, with pins, endpoint faces, and modified profiles, retaining all the specified gains. The scalar results below do not imply that assertion.

The assertion requested in OPEN 8.2 is the following. For every regular object of order $2m\le N^4$ occurring in T1090–1244, one must allow the upper resonance filters of supplement (8.1), the pins and faces of OPEN 7.3, and the profiles of Section 6, and obtain the required approximation and error estimates on its unmarked portions with additional cost

$$
 C_{P,\chi,\vartheta}^{m+1}C_{P,\delta}L^{c_db}.
 \tag{1.1}
$$

Here $b$ counts protected incidences; $c_d$ must be numerical; the exponential base must be independent of $\delta$. If $a$ high-resonance occurrences have been selected, one additionally needs $M_2^{-a/18}$, counting both occurrences of a selected linked frequency. All constants must be uniform in upper scales and external momenta. Extracted reciprocals retain their principal-value interpretation. Estimates of signed face collections are allowed only if the collection is specified before taking absolute values.

The results proved here are Propositions 2.1, 3.1, 4.1, and 5.1. None is asserted as a sufficient replacement for (1.1). Section 6 gives an exact chain calculation identifying what a face estimate must retain. Section 7 states the remaining obligations and the conditional loss calculation.

The files were checked against the supplement's frozen hashes:

| Source | SHA-256 |
|---|---|
| Supplement | `ddd81fe1238e7c51379a69981b4d10aa68690ced46d0fc1b115200fc0c3774d7` |
| TARGET | `493eef6b7dec448bc5f9f1c3974c0cad7a85eca9bc428f5b35e968aad76727cb` |
| DH21 | `50d0e236a2df0cfd2b98bace6f0256043ee88fc05079ee44c3524ca9482fe402` |
| DH23 | `c7e47dfabf5a4cca6e3ad0399fc377f2809c12f58e1563640407fe0992335475` |

Below D21 and D23 refer to the line-numbered local sources specified in COMMON.md. We use the corrected branching normalization $\delta/(2L^{d-\gamma})$ from the supplement. No source file was changed and no Lean build was run.

## 2. Uniform Fourier bounds for the extracted factor

Write $\mu=\delta L^{2\gamma}$ and use the Fourier convention

$$
 \widehat f(\sigma)=\int_{\mathbb R}f(\alpha)e^{-2\pi i\alpha\sigma}\,d\alpha.
$$

Fix a smooth even cutoff $\chi_0$, equal to one on $[-1/2,1/2]$ and zero outside $[-1,1]$, and put $\chi_\infty=1-\chi_0$. This is the cutoff convention of D23 L440, with the even choice used in the reciprocal calculus. Its derivatives are fixed independently of all scales. Let $\vartheta$ be the supplement's fixed even Gevrey cutoff. For $0\le h\le2$ and $S_i\ge1$, set

$$
 g(\alpha)=\frac{\chi_\infty(\alpha)}{\alpha},\qquad
 H_{\boldsymbol S}(\alpha)=\prod_{i=1}^h\vartheta(\alpha/S_i),\qquad
 g_{\boldsymbol S}=gH_{\boldsymbol S}.
 \tag{2.1}
$$

All expressions are defined to be zero near $\alpha=0$ where appropriate; for $h=0$, $g_{\boldsymbol S}=g$.

**Proposition 2.1.** For every integer $r\ge0$ there is a finite constant $K_r$, depending only on the two fixed cutoffs and $r$, such that

$$
 \sup_{\boldsymbol S}\sup_{\sigma\in\mathbb R}
 \langle\sigma\rangle^r|\widehat g_{\boldsymbol S}(\sigma)|\le K_r,
 \qquad
 \sup_{\boldsymbol S}\|\widehat g_{\boldsymbol S}\|_{L^1}\le K_2\int\langle\sigma\rangle^{-2}\,d\sigma.
 \tag{2.2}
$$

For $h=0$ the transform is a tempered-distribution transform represented by a bounded function, with the value at zero immaterial. In addition, for every integer $r\ge1$,

$$
 \sup_{\boldsymbol S}\|g_{\boldsymbol S}^{(r)}\|_{L^1}<\infty.
 \tag{2.3}
$$

These are scale-uniform statements; in contrast, there is no scale-uniform $L^1_\alpha$ bound for $g_{\boldsymbol S}$.

**Proof.** First $g^{(r)}\in L^1$ for $r\ge1$: it is smooth near zero and is a constant multiple of $\alpha^{-r-1}$ outside $[-1,1]$. To bound $\widehat g$ near zero, use oddness to write it as a sine integral. The contribution of $0<\alpha<1$ is bounded. For $0<|\sigma|\le1$, split the remaining integral at $|\sigma|^{-1}$. On $1<\alpha<|\sigma|^{-1}$, use $|\sin(2\pi\sigma\alpha)|\le2\pi|\sigma|\alpha$. On $\alpha>|\sigma|^{-1}$, one integration by parts bounds the integral by a constant independent of $\sigma$. For $|\sigma|\ge1$, the distributional identity

$$
 (2\pi i\sigma)^r\widehat g(\sigma)=\widehat{g^{(r)}}(\sigma)
$$

and the preceding $L^1$ bound give arbitrary polynomial decay. Thus $\sup\langle\sigma\rangle^r|\widehat g(\sigma)|$ is finite for every $r$.

The transform of $\vartheta(\alpha/S)$ is $S\widehat\vartheta(S\sigma)$. For $S\ge1$,

$$
 \int\langle\sigma\rangle^r S|\widehat\vartheta(S\sigma)|\,d\sigma
 =\int\langle u/S\rangle^r|\widehat\vartheta(u)|\,du
 \le\int\langle u\rangle^r|\widehat\vartheta(u)|\,du.
 \tag{2.4}
$$

Multiplication in (2.1) is convolution on the Fourier side. Apply (2.4) at most twice and use $\langle x+y\rangle^r\le2^{r/2}\langle x\rangle^r\langle y\rangle^r$. This proves the first assertion of (2.2), and its second assertion follows by integrating the case $r=2$.

For (2.3), expand by the product rule. Terms with a positive derivative on $g$ are bounded by its $L^1$ derivative norm and the uniform $L^\infty$ derivative bounds of the cutoff factors. Otherwise at least one factor has a positive derivative, say the factor at scale $S_i$. Its support lies in $S_i\le|\alpha|\le2S_i$. On that support, $|g(\alpha)|\le|\alpha|^{-1}$, so its integral is at most $2\log2$. The scale factors from all derivatives are at most one. There are finitely many terms for fixed $r$, uniformly in the scales.

Finally, with one cutoff at scale $S\ge2$, $g_S(\alpha)=1/\alpha$ on $1\le|\alpha|\le S$. Consequently

$$
 \|g_S\|_{L^1}\ge2\log S.
 \tag{2.5}
$$

This proves the last assertion. ∎

Thus absorbing every extracted reciprocal into the integrable coefficient would introduce an unbounded $\log S$ cost. Proposition 2.1 instead leaves the reciprocal explicit and supplies the Fourier bounds needed by a scalar oscillatory-sum estimate. Oddness alone would not prove (2.2); the Fourier calculation does.

## 3. The unpinned spectral decomposition with all upper filters

**Proposition 3.1.** Consider an unpinned regular couple whose coefficient has the decomposition D23 L960–968. Multiply its linked spectral variables by at most two factors $\vartheta(\alpha_j/S_{ji})$ per coordinate, $S_{ji}\ge1$. The resulting coefficient has the exact decomposition

$$
 \sum_Z\left(\prod_{j\in Z}\frac{g_{\boldsymbol S_j}(\alpha_j)}{\zeta_j\pi i}\right)
 \int C_{Z,*}(\lambda,\alpha_{Z^c})e^{\pi i(\lambda_1t+\lambda_2s)}\,d\lambda,
 \tag{3.1}
$$

with at most $2^m$ terms. The coefficients $C_{Z,*}$ satisfy supplement (8.3), uniformly in the scales. No new power of $L$ is incurred and no additional factor depending exponentially on $\delta$ is introduced. The proposition concerns the coefficient before the decoration sum, and has no order restriction beyond the source coefficient theorem.

**Proof.** Multiply each term of D23 L962 by the original product of cutoffs. A linked pair has opposite signed spectral frequencies, and evenness assigns its two possible factors to the same independent coordinate. For a coordinate in $Z$, keep its cutoff factors with its explicit reciprocal. For a coordinate outside $Z$, put its cutoff factors into $C_Z$. This is exactly (3.1). There is no expansion and hence no increase in the number of terms. Supplement Lemma 8.1 applies to $C_Z$ and gives the stated estimates. Proposition 2.1 controls the new explicit factors when Fourier bounds for them are needed. ∎

The same multiplication argument works **conditionally** in the mixed norm of supplement (7.3): if a coefficient with exceptional parameters $\alpha_E$ has already been constructed, bounded cutoffs in $\alpha_E$ cannot increase its norm, and the product rule in the integrable coordinates gives the cutoff derivative bounds. This statement does not construct that coefficient. It also does not control a boundary modulation by an unshifted Fourier weight.

## 4. A scalar discrete-to-principal-value estimate

Here the source's scalar number-theoretic estimates give an actual truncated discrete estimate, not just coefficient stability. We state precisely its scope.

Let $d\ge3$, $1/2<\gamma<1$, and

$$
 \gamma_1=\min\{1,2(d-1)(1-\gamma)\},\qquad \mu=\delta L^{2\gamma}.
$$

This is T613 in the specified range. Let $W\in C_c^\infty(\mathbb R^{2d})$ be supported in

$$
 |x-a|\le\lambda,\quad |y-b|\le\lambda,\qquad 1\le\lambda\le(\log L)^4,
$$

and set

$$
 D(W)=\int_{\mathbb R^{2d}}(1+|\xi|+|\zeta|)|\widehat W(\xi,\zeta)|\,d\xi\,d\zeta.
 \tag{4.1}
$$

Take $h\le2$, $S_i=\mu M_i$, and $M_i\ge L$; assume $L$ is large enough that $\mu>1$ and $S_i\ge1$. Empty products are allowed. Write $\Omega=x\cdot y$ and

$$
 I_{\boldsymbol S}=\sum_{x,y\in\mathbb Z_L^d}W(x,y)g_{\boldsymbol S}(\mu\Omega),\qquad
 J_{\boldsymbol S}=L^{2d}\int W(x,y)g_{\boldsymbol S}(\mu\Omega)\,dx\,dy.
$$

**Proposition 4.1.** For every fixed sufficiently small $\varepsilon>0$, the following bounds hold, uniformly in $a,b,M_i$:

$$
 |I_{\boldsymbol S}-J_{\boldsymbol S}|
 \le C_{d,\gamma,\varepsilon,\vartheta,\chi_0}
 D(W)\lambda^{4d}\frac{L^{2d}}\mu L^{-\gamma_1+\varepsilon},
 \tag{4.2}
$$

and

$$
 \left|I_{\boldsymbol S}-\frac{L^{2d}}\mu
   \operatorname{pv}\!\int\frac{W(x,y)}{x\cdot y}\,dx\,dy\right|
 \le C_{d,\gamma,\varepsilon,\vartheta,\chi_0}
 D(W)\lambda^{4d}\frac{L^{2d}}\mu L^{-\gamma_1+\varepsilon}.
 \tag{4.3}
$$

In (4.3), the lower threshold for $L$ may also depend on $\delta$. The principal value is the symmetric resonance principal value of D21 L1312–1323. The constant outside the displayed normalization is independent of $\delta$.

**Proof of (4.2).** Choose a smooth localization $\Upsilon(x,y)$ with a fixed cutoff profile, equal to one on the support of $W$, supported in slightly enlarged balls of radius $C\lambda$. Fourier inversion of $W$ gives $W=W\Upsilon$ and reduces the proof to $\Upsilon e(\xi\cdot x+\zeta\cdot y)$, followed by integration against $\widehat W$. This reduction retains the first Fourier moment (4.1).

By Proposition 2.1, Fourier inversion of $g_{\boldsymbol S}$ is absolutely convergent. Set $f=\widehat g_{\boldsymbol S}$. The difference in (4.2), after the preceding reduction, is

$$
 \mu^{-1}\int_{\mathbb R} f(s/\mu)
 \left[\sum_{x,y\in\mathbb Z_L^d}\Upsilon(x,y)e(\xi\cdot x+\zeta\cdot y+s x\cdot y)
 -L^{2d}\int\Upsilon(x,y)e(\xi\cdot x+\zeta\cdot y+s x\cdot y)\,dx\,dy\right]ds.
 \tag{4.4}
$$

Take a fixed smooth $\kappa(s/L)$ equal to one for $|s|\le L/2$ and zero for $|s|\ge L$. We estimate its contribution and the complementary contribution separately. Use the scalar estimates of D23 with an auxiliary small parameter $\eta_0<\varepsilon/4$; their constants are allowed to depend on $\varepsilon$.

For the part with $\kappa$, Poisson summation turns the bracket in (4.4) into $L^{2d}$ times the sum of nonzero dual-lattice integrals. The amplitude $\kappa(s/L)f(s/\mu)$ is independent of $x,y$ and uniformly bounded by Proposition 2.1. D23 L1013–1038, part (2), gives

$$
 C\mu^{-1}L^{2d}\lambda^{2d}L^{-1+2\eta_0}(1+|\xi|+|\zeta|).
 \tag{4.5}
$$

Only spatial derivatives of the amplitude are required by D23 L1014–1018; no uniform bound on its $s$ derivatives is being assumed.

For the lattice part with $1-\kappa$, choose a fixed integer $q>\eta_0^{-2}$. Proposition 2.1 gives $|f(s/\mu)|\le K_q\langle s/\mu\rangle^{-q}$. Apply D23 L1076–1086, part (2), to obtain

$$
 C_q\mu^{-1}\lambda^{4d}L^{2d-2(d-1)(1-\gamma)+\eta_0}.
 \tag{4.6}
$$

For the continuum part, the stationary-phase estimate underlying D23 L1042, or D21 L1538–1544 with one pair of variables, is

$$
 \left|\int\Upsilon(x,y)e(\xi\cdot x+\zeta\cdot y+s x\cdot y)\,dx\,dy\right|
 \le C\lambda^{2d}\langle s\rangle^{-d},
$$

uniformly in the ball centers and modulations. Use the boundedness of $f$ and integrate over $|s|\ge L/2$. The result is

$$
 C\mu^{-1}L^{2d}\lambda^{2d}L^{-(d-1)}.
 \tag{4.7}
$$

Integrating (4.5)–(4.7) against $|\widehat W|$, and using $\gamma_1\le1\le d-1$, proves (4.2). All uses of Poisson summation and Fubini are justified first on bounded $s$ intervals; (4.6) and (4.7) supply the integrable tails. For $h=0$, the Fourier representative from Proposition 2.1 gives the same justification.

**Passage to (4.3).** Put $M_* =\min_i M_i$ when $h>0$. Since $0\le H_{\boldsymbol S}\le1$ and $H_{\boldsymbol S}(\mu\Omega)=1$ for $|\Omega|\le M_*$,

$$
 |J_{\boldsymbol S}-J_{\varnothing}|
 \le \frac{L^{2d}}{\mu M_*}\int_{\operatorname{supp}W}|W(x,y)|\,dx\,dy
 \le C D(W)\lambda^{2d}\frac{L^{2d}}\mu M_*^{-1}.
 \tag{4.8}
$$

This step is an absolute bound on a **continuum tail**, after the sum-to-integral estimate; it does not discard a cutoff inside the original discrete sum.

D21 L1305–1323, with $\beta=1$ and arbitrary $\mu>1$, gives

$$
 \left|J_{\varnothing}-\frac{L^{2d}}\mu
 \operatorname{pv}\!\int\frac{W}{\Omega}\right|
 \le C D(W)\lambda^{2d}\frac{L^{2d}}\mu\,\mu^{-1}.
 \tag{4.9}
$$

Indeed, apply that lemma to $\Upsilon e(\xi\cdot x+\zeta\cdot y)$ and integrate against $\widehat W$. The lemma is a continuum statement uniform in $\mu$, so replacing $\delta L^2$ by $\delta L^{2\gamma}$ is legitimate here. Now $M_*^{-1}\le L^{-1}$, and $\mu^{-1}=\delta^{-1}L^{-2\gamma}\le L^{-\gamma_1+\varepsilon}$ for sufficiently large $L$ chosen after $\delta$, since $2\gamma>1\ge\gamma_1$. Combining (4.2), (4.8), and (4.9) proves (4.3). For $h=0$, omit (4.8). ∎

The harmless factor two in the paper's relation $\Omega=2x\cdot y$ changes only fixed constants and the definition of $\mu$. It does not change any exponent above.

Proposition 4.1 addresses a scalar ingredient of D23 `approxnt`. It does not claim its full triangular, many-variable version, its application to a marked coefficient, or stability of the entire approximation under taking time faces. In particular it must not be iterated after a coefficient becomes nonsmooth or depends on earlier variables without checking the derivative hypotheses at each step.

## 5. A selected extracted coordinate

**Proposition 5.1.** Under the support assumptions of Section 4, let $M\ge L$, $c>0$, and let $B(\alpha)$ be any bounded multiplier, $|B|\le B_0$, supported in $|\alpha|\ge c\mu M$. It may include the shell derivative and the remaining upper filters in that coordinate. Then

$$
 \left|\sum_{x,y\in\mathbb Z_L^d} W(x,y)g(\mu x\cdot y)B(\mu x\cdot y)\right|
 \le C_{d,c} B_0D(W)\lambda^{2d}\frac{L^{2d}}\mu M^{-1}.
 \tag{5.1}
$$

The corresponding absolute continuum integral, multiplied by $L^{2d}$, satisfies the same bound. If one or two selected occurrences use this coordinate, the gain in (5.1) is at least $M^{-a/18}$ for $a=1,2$.

**Proof.** On the support of $B$, $|g(\mu\Omega)|\le(c\mu M)^{-1}$. Each ball of radius $\lambda\ge1$ contains at most $C_d(\lambda L)^d$ lattice points. Also $\|W\|_\infty\le\|\widehat W\|_1\le D(W)$. Taking the absolute value of this single localized two-vector sum proves (5.1); integration over the support proves the continuum assertion. Finally $M^{-1}\le M^{-a/18}$ for $M\ge1$ and $a\le2$. ∎

For the actual shell expansion, $-u\vartheta'(u)$ is a fixed bounded factor supported in $1\le|u|\le2$. Its scale lies in $[M_2/2,M_2]$, so Proposition 5.1 applies with a fixed $c$. A product of two such factors is still bounded and has the required support. This checks the two-occurrence convention at a **single extracted coordinate**. It does not assert that an arbitrary coupled coefficient has a product of these gains in all selected coordinates.

Nor does the proposition license taking the absolute value of an entire regular object. Applying the same raw count to all its unselected variables could destroy every oscillatory gain and produce an inadmissible loss depending on its order.

## 6. Pins and faces: an exact minimal calculation

The following calculation records the face terms and signs before estimating them. It also shows why a scalar reciprocal estimate is not the whole marked-chain argument.

For one adjacent linked pair, let $\omega=\pi\alpha$ and

$$
 K(t,s;\alpha)=\int_s^t\int_s^u e^{i\omega(u-v)}\,dv\,du.
$$

Integrating the unpinned outer time $u$ with $v$ fixed gives the exact signed collection of two faces

$$
 K(t,s;\alpha)
 =\frac{1}{i\omega}\left[
 e^{i\omega t}\int_s^t e^{-i\omega v}\,dv
 -\int_s^t1\,dv\right]
 =\frac{e^{i\omega(t-s)}-1}{(i\omega)^2}-\frac{t-s}{i\omega}.
 \tag{6.1}
$$

The upper face is $u=t$ and the lower face is $u=v$. Each has multiplicity one and their signs are respectively plus and minus. On the lower face the two linked phases cancel. The coefficient left after removing the displayed reciprocal is $t-s$, independent of $\alpha$. With a cutoff $\vartheta(\alpha/S)$, its spectral $L^1$ norm is exactly

$$
 (t-s)S\int_{\mathbb R}\vartheta(u)\,du.
 \tag{6.2}
$$

Consequently there is no uniform estimate obtained by applying the original integrable-coefficient norm to this bare face. The reciprocal must stay explicit, or the coordinate must be handled as exceptional. This is a counterexample to that particular shortcut, not to OPEN 8.2: (6.1) is compatible with an appropriate reciprocal decomposition.

Pinning the last time to $s$ instead gives

$$
 K_{\rm pin}(t,s;\alpha)
 =e^{-i\omega s}\int_s^t e^{i\omega u}\,du
 =\frac{e^{i\omega(t-s)}-1}{i\omega}.
 \tag{6.3}
$$

Thus $|K_{\rm pin}|\le\min(t-s,2/|\omega|)$. On $|\alpha|\ge c\mu M_2$, this single pinned pair has the required high-resonance decay with room to spare. This is the $m=1$ instance of D21 L2688–2690.

The separate boundary phase in (6.3) is not bounded in a uniformly centered weighted Fourier norm. For example, if $\phi\in C_c^\infty(\mathbb R)$ is nonzero and $\theta>0$, then

$$
 \int\langle\lambda\rangle^\theta
 \left|\mathcal F_t[\phi(t)e^{\pi i\alpha t}](\lambda)\right|d\lambda
 =\int\langle u+\alpha/2\rangle^\theta|\widehat\phi(u)|\,du
 \gtrsim_\phi\langle\alpha\rangle^\theta
 \quad (|\alpha|\to\infty).
 \tag{6.4}
$$

For the lower bound, choose a fixed bounded interval on which $\int|\widehat\phi|>0$ and restrict the integral to it. A centered weight $\langle\lambda-\alpha/2\rangle^\theta$ removes this particular growth, but then the modulation has to be passed into the adjacent time integral. This is exactly the bookkeeping required in supplement (7.3).

For multiple selected times in different original trees, supplement Lemma 9.1 gives a specified collection: choose, for each selected vertex, one of at most four maximizing-child regions and one of its two endpoints, assign the sign of that endpoint, and retain the product of these choices. There are at most $8^a$ terms and the common reciprocal is $\prod_v(i\pi\zeta_v\mu\Omega_v)^{-1}$. This specifies the raw collection but does not bound its reduced coefficient. Neither (6.1) nor (6.3) proves the needed recursion when linked partners, other pins, and layer endpoints are present.

## 7. What remains, and the numerical losses

### 7.1 The missing simultaneous estimate

A sufficient next step is to construct, for each marked chain and each retained face collection, a decomposition with explicit factors (2.1) and a coefficient satisfying supplement (7.3), together with a rule that sends every exceptional modulation to the adjacent integral. The construction must establish a bound on the **total** number of exceptional coordinates, not repeatedly charge the same pin when it occurs inside nested regular pieces. It must keep the unmarked incoherency gains and verify the spatial Fourier hypotheses for the profiles of supplement Section 6.

This is not established by the unmarked class-$J/R$ composition lemmas D21 L955–1094. Their coefficient classes have specific bundles, special indices, and weighted Fourier variables; see especially L957 and L961. D21 L2688–2694 gives the single-layer terminal-pin mechanism and mixed-norm conversion, but it does not supply the simultaneous layered, face-modified construction requested here. The identity T1241–1244 factors coherent unpinned objects into single-layer pieces. To apply it after a marked operation one must prove the corresponding identity with its boundary inequalities and modulations retained; it does not follow from merely translating a layer.

Propositions 2.1–4.1 remove a local obstacle in the unmarked reciprocal part. They do not prove this marked decomposition, even if OPEN 7.3 is assumed only in its untruncated form: one must still verify that its explicit spectral coordinates and the original upper filters are compatible throughout the marked reduction.

### 7.2 The many-variable discrete step and the order range

The one-frequency result (4.3) must be extended to the triangular support structure of D23 L991–993, with coefficients depending on the exceptional parameters and with the required derivatives and time-frequency weights. D21 L1591–1605 explains the iterative derivative control in the unmarked proof; D23 L1161 invokes that proof with its replacement scalar lemmas. These passages identify where the scalar result must be inserted, but are not a verification for the new marked coefficients.

There is also an order-range check. D23 L1002 states $m\le(\log L)^3$. T612 gives $N^4\le C_{\delta}(\log L)^{K_\delta}$ for a fixed, possibly very large exponent after $\delta$ is chosen. The elementary factorial absorption at D21 L1619–1620 can be extended to any such fixed exponent: for fixed integers $q,K$ and $1\le f\le m\le C(\log L)^K$,

$$
 (qf)!\le(qm)^{qf}\le L^{\varepsilon f}
 \tag{7.1}
$$

for sufficiently large $L=L(C,K,q,\varepsilon)$, since $q\log(qC(\log L)^K)=o(\log L)$. This costs exactly $\varepsilon f$ in that inequality, paid from the corresponding per-coordinate minor-arc gain; it is not an admissible independent $L^{\varepsilon m}$ overhead for the final theorem. Formula (7.1) resolves this particular factorial comparison. A full extension still has to audit every other use of the order restriction and choose the spare minor-arc exponent before $L$.

The exponential base need not depend on $K_\delta$ in (7.1); only the final threshold for $L$ does. No $C_2^m$ is absorbed in this argument.

### 7.3 Selected occurrences

For selected integrable coordinates, supplement (8.4) gives a tail in one coordinate. Its hypothesis contains a **maximum** of the coordinate weights, not their product. Accordingly it cannot by itself be multiplied once for every selected occurrence. For a selected extracted coordinate Proposition 5.1 proves the required scalar gain, including two occurrences of that coordinate. For a selected exceptional coordinate one needs a marked chain or face estimate, as in the special calculation (6.3), or an estimate of the complete signed collection after the raw time integrations. These cases must be combined before asserting supplement (8.6).

### 7.4 Loss accounting

**Current status: CLOSED WITH VARIANT in §19 (Theorem 8.2′); see the final STATUS line and the referee revision in §22. The following text records the earlier partial analysis.**

The extra losses proved in this note are numerical:

| Operation proved here | Additional positive power of $L$ |
|---|---:|
| Uniform reciprocal Fourier bounds, Proposition 2.1 | $0$ |
| Cutoff spectral decomposition, Proposition 3.1 | $0$ |
| Scalar truncated approximation, Proposition 4.1 | $0$; retains the scalar error gain $L^{-\gamma_1+\varepsilon}$ |
| A selected extracted scalar coordinate, Proposition 5.1 | $0$; gain $M_2^{-1}$ |
| The exact one-pair identities (6.1), (6.3) | $0$; no estimate for a general marked chain is implied |

The factor $L^{2d}\mu^{-1}=\delta^{-1}L^{2d-2\gamma}$ in Section 4 is the source's ordinary normalization for one independent pair, not an additional loss. Multiplication by the two branching prefactors gives

$$
 \left(\frac{\delta}{2L^{d-\gamma}}\right)^2
 \frac{L^{2d}}\mu=\frac\delta4.
 \tag{7.2}
$$

Thus no hidden loss per unit of order is introduced by the scalar normalization.

There is a useful **conditional** numerical calculation for the remaining mixed-norm step. If a construction gives at most $2b$ exceptional coordinates, and each has the unit-interval cover in supplement Lemma 7.1, then its conversion from supplement (7.3) costs at most

$$
 C_{d,b}L^{4d(2b)}=C_{d,b}L^{8db}.
 \tag{7.3}
$$

If, in addition, each of the $8^a$ selected-time face terms satisfies the needed coefficient and decoration estimate after the selected reciprocals are removed, uniformly in the fixed resonances and their transmitted modulations, with every fixed selected resonance included in the exceptional-coordinate budget, its contribution has the extra factor

$$
 8^a C_{d,b}(\pi c\delta)^{-a}
 L^{8db-2\gamma a}M_2^{-a}
 \le C_{P,\delta,d,b}L^{8db}M_2^{-a/18},
 \qquad a\le2P.
 \tag{7.4}
$$

This inequality proves the arithmetic **under the stated uniform face premise**. That premise is precisely one of the unproved analytic assertions; (7.4) is not a proof of it. If signed collections are used instead, their estimate must replace that premise explicitly.

For illustration of the already identified budget only, $2P$ pins with at most two exceptional coordinates each cost $L^{16dP}$ by (7.3). Adding the bottom-block allowance and the margin in supplement (10.4) gives

$$
 16d+80d+\frac19+3=96d+\frac{28}{9}<(100d)^3
 \quad(d\ge3).
 \tag{7.5}
$$

This does not account for additional boundaries, affected ladders, missing gains, or the modulation consumption in the general marked construction. No value of $c_d$ for that construction has been proved here, and therefore the aggregate budget in supplement (10.4), including its derivative version, is **not certified**.

## 8. Dependencies and conclusion

**Current status: CLOSED WITH VARIANT in §19 (Theorem 8.2′); see the final STATUS line and the referee revision in §22. The following text records the earlier partial analysis.**

| Source | Verified use in this note |
|---|---|
| Supplement Lemma 8.1 | The integrable factors of (3.1), with uniform cutoff derivative bounds |
| Supplement Lemmas 7.1 and 9.1 | Conditional fiber loss (7.3), raw face collection and its reciprocal factors |
| D23 L440 | Fixed low/high spectral cutoff convention |
| D23 L955–968 | Linked frequencies and the unpinned coefficient decomposition |
| D23 L984–1009 | Comparison with the full `approxnt` statement; not invoked as a truncated marked theorem |
| D23 L1013–1071 | Scalar continuum and nonzero Poisson-mode estimates used in (4.5), (4.7) |
| D23 L1076–1086 | Scalar minor-arc bound used in (4.6) |
| D21 L1305–1366 | Continuum reciprocal estimate, its symmetric principal value and low-frequency error |
| D21 L1504–1622; D23 L1161–1162 | Location of the many-variable iteration and its order-dependent factorial estimate |
| D21 L955–1094 | Unmarked class-$J/R$ calculus; comparison with the missing marked recursion |
| D21 L2684–2694 | Terminal-pin precedent; the special computation (6.3) is proved directly here |
| D21 L2699–2704 | High-resonance precedent, not a substitute for the required combined estimate |
| T606–615 | Constant order, polylogarithmic truncation, and $\gamma_1$ |
| T1097–1123; T1145–1174 | Approximation, error, and norm obligations to be retained |
| T1197–1231 | Principal-value factors in the required coherent spatial profiles |
| T1235–1244 | Exact unmarked coherent layer factorization; no marked extension is assumed |

The smallest remaining route is to prove the marked coefficient/face recursion and its many-variable decoration estimate together, using explicit truncated reciprocals controlled by Proposition 2.1 and the scalar estimates in Sections 4–5. The recursion must track exceptional coordinates and modulation centers, provide the occurrence gains, and assign a numerical boundary cost before supplement Proposition 10.3 can be applied. There is no demonstrated counterexample to OPEN 8.2 here, but the combined assertion and a sufficient variant both remain unproved.


## 9. Continuation: interface requested from o73

This section and the sections that follow are the continuation requested in CONTINUE.md. Sections 1–8 record the first pass; their OPEN assertions are to be read subject to the new results below. This interface is a **hypothesis to be supplied by o73**, not a theorem about marked chains proved here.

**Coefficient interface I.** After fixing a unit-box spatial localization as in T1002–1017, a retained marked-chain term has the following data.

1. The original independent linked coordinates remain $\alpha_j=\mu x_j\cdot y_j$, $1\le j\le m$, up to the fixed signs and factors two. There is a partition $[m]=E\sqcup Z\sqcup J$. Each selected occurrence has its linked coordinate in $E$. The set $E$ has size $e\le2r$, where $r$ is the number of pin/face incidences charged to this term. Extracted coordinates $Z$ are disjoint from $E$; no change to a bundle of linked frequencies is implicit in this notation.
2. For every fixed exceptional spatial tuple $z_E=(x_j,y_j)_{j\in E}$, the remaining coefficient is a sum/integral of terms

$$
 R_E(z_E)\prod_{j\in Z}g(\alpha_j)
 \int C_F(\lambda,\alpha_E,\alpha_J)
 e^{\pi i(\lambda+\ell_F(\alpha_E))\cdot\tau}\,d\lambda.
 \tag{9.1}
$$

Here $F$ labels an explicitly retained signed face or face collection, $C_F$ has no dependence on $\alpha_Z$, and $\ell_F$ records the actual boundary modulation. The selected reciprocals are contained in $R_E$. The total coefficient mass includes the sum over $F$; one must not count the same faces again below.
3. The coefficient estimate must be uniform in $z_E$ and spatial centers. After setting $\nu=\lambda+\ell_F(\alpha_E)$, let $\widetilde C_F(\nu,\alpha_E,\alpha_J)=C_F(\nu-\ell_F(\alpha_E),\alpha_E,\alpha_J)$. For the time weight $w$ actually consumed by the surrounding reduction, require

$$
 \sup_{z_E}\sum_F\int w(\nu)
 \|\partial_{\alpha_J}^{\rho}\widetilde C_F(\nu,\alpha_E,\cdot)\|_{L^1_{\alpha_J}}\,d\nu
 \le B\,A^{m+|\rho|}(4|\rho|)!.
 \tag{9.2}
$$

The base $A$ is independent of $\delta$. The factor $B$ must explicitly contain the retained unmarked gains and a numerical $L$ loss per marked incidence. A bound with a centered weight is also usable if o73 proves a downstream consumption rule giving (9.2) for the resulting expression. Merely recentering the weight is not that rule.
4. For a selected occurrence with $|\Omega_v|\asymp M_2$, it is sufficient to replace $B$ in (9.2) by $B\prod_v\langle\mu\Omega_v\rangle^{1/4}$, provided the factor $(i\pi\zeta_v\mu\Omega_v)^{-1}$ is retained in $R_E$ for **each occurrence**. This explicitly allows a modulation cost. The exponent $1/4$ is a proposed sufficient interface, not a conclusion inferred from a centered estimate. Pins that were not selected must not introduce unbounded factors of their exceptional resonances.
5. The spatial amplitude has a finite Fourier-measure representation in the remaining variables, uniformly after fixing $z_E$, with mass $D$ (and the first spatial Fourier moment when an approximation error is requested). The source localizations and the modified final profiles must give $D\le C_{P,\chi}^{m+1}C_{P,\delta}$, with the prescribed output derivatives. Constants and powers already in $B,D$ are recorded only once. For output suprema inside Fourier integrals one needs a uniform integrable majorant or the source Sobolev reduction T997–1000; a pointwise-in-output bound does not suffice.

For a pure upper-cutoff estimate, no selected occurrences or factors $R_E$ are needed. For an asymptotic principal-value formula, add the source's weighted $\alpha_J$ moment, in the same consumed time norm, to (9.2). For a bound on a protected piece that is removed from the unmarked cancellation, (9.2) alone will suffice for the spatial estimate below.

**Why exceptional spatial tuples are fixed rather than spectrally integrated.** There are at most $(CL)^{2de}$ such tuples in fixed unit boxes. Restricting a Fourier-measure amplitude to fixed coordinates does not increase its total variation. This avoids deducing point values in $\alpha_E$ from an integrated estimate or differentiating an exceptional-coordinate cutoff. The loss relative to the ordinary linked-pair normalization will be $\mu^e\le L^{2e}$, rather than a spectral-volume loss. The many-variable proof will make this statement precise. The momenta are fixed only in the exceptional coordinates; none of the other $m-e$ pairs is summed trivially.

This interface is posted before the remaining argument so that o73 can supply its actual representation or identify a mismatch. In particular, (9.2), the numerical factor $B$, the count $e\le2r$, and the consumption of $\ell_F$ are not assumed proved merely because they are stated here.


## 10. A many-variable discrete estimate in independent unit boxes

The unit-box refinement T1002–1017 allows a simpler proof than the general triangular-support induction in D21 L1591–1605. The refinement costs $C_0^m$ after leaf localization, and leaves the original linked phases unchanged. It is important that the following theorem is for **independent fixed boxes**. It does not replace a triangular support by its bounding box, which could cost a factorial.

Put $n=|Z|+|J|$, and use fixed smooth profiles $\psi_j(x_j-a_j)\psi'_j(y_j-b_j)$ supported in balls of a fixed radius, with the bounded derivatives required by D23 L1014–1018. Their product is $\Upsilon(z)$. Let $W(z)$ have a finite Fourier-measure representation $d\omega(\xi,\zeta)$ and define

$$
 D_0=\|\omega\|_{\rm TV},\qquad
 D_1=\int\left(1+\sum_{j=1}^n(|\xi_j|+|\zeta_j|)\right)d|\omega|.
 \tag{10.1}
$$

Using a measure permits affine frontier multipliers and restrictions of a larger spatial amplitude to fixed exceptional tuples. The compact support of the full summand is supplied by $\Upsilon$, so $W$ itself need not be compactly supported.

Let $v$ denote any external parameter, held fixed throughout the following estimates, and let

$$
 \Psi_{v,\nu}(\alpha)
 =\prod_{j\in Z}g_{\boldsymbol S_j}(\alpha_j)\,
 C_*(\nu,v,\alpha_J).
 \tag{10.2}
$$

All upper scales are at least one. Suppose that, for all multi-indices $\rho$,

$$
 \int w(\nu)\|\partial_{\alpha_J}^{\rho}C_*(\nu,v,\cdot)\|_1\,d\nu
 \le B A^{n+|\rho|+1}(8|\rho|)!.
 \tag{10.3}
$$

The estimates are uniform in $v$. The factorial $8|\rho|$ allows the cutoff multiplication in §11; it can be replaced by any fixed multiple, without changing the argument. Define

$$
 I_v(\nu)=\sum_{z\in(\mathbb Z_L^d)^{2n}}\Upsilon(z)W(z)
                  \Psi_{v,\nu}(\mu\Omega(z)),\qquad
 I_v^c(\nu)=L^{2dn}\int\Upsilon(z)W(z)
                  \Psi_{v,\nu}(\mu\Omega(z))\,dz,
 \tag{10.4}
$$

where $\Omega_j=x_j\cdot y_j$ and $\mu=\delta L^{2\gamma}$. The case $J=\varnothing$ means no spectral integral in (10.3).

**Theorem 10.1.** Fix $\varepsilon>0$ sufficiently small relative to $\gamma_1$. For every fixed $K,H<\infty$, the estimates

$$
 \int w(\nu)|I_v(\nu)|\,d\nu
 +\int w(\nu)|I_v^c(\nu)|\,d\nu
 \le B D_0 C^{n+1}(L^{2d}/\mu)^n,
 \tag{10.5}
$$

and

$$
 \int w(\nu)|I_v(\nu)-I_v^c(\nu)|\,d\nu
 \le B D_1 C^{n+1}(L^{2d}/\mu)^nL^{-\gamma_1+\varepsilon}
 \tag{10.6}
$$

hold for $n\le H(\log L)^K$ and sufficiently large $L$. The base $C$ depends on $d,\gamma,\varepsilon,A$ and the fixed profiles, but **not** on $\delta,H,K$, the centers, the scales, or $v$. The threshold for $L$ may depend on $\delta,H,K$. If $n=0$, (10.5) is the coefficient estimate and the difference in (10.6) is zero.

**Proof.** Assume $n\ge1$. Write $f_{v,\nu}=\widehat\Psi_{v,\nu}$ for the spectral Fourier transform. Proposition 2.1, (10.3), and integration by parts in $\alpha_J$ give, for every subset $F\subset[n]$ of size $f$ and every fixed integer $q\ge1$,

$$
 \int w(\nu)\sup_{\sigma}
 \left|f_{v,\nu}(\sigma)\prod_{j\in F}\langle\sigma_j\rangle^q\right|\,d\nu
 \le B C_q^{n+1}(8qf)!,
 \tag{10.7}
$$

with the right side interpreted as $BC_q^{n+1}$ if $f=0$. To justify (10.7), replace $\langle\sigma_j\rangle^q$ by a constant times $1+|2\pi\sigma_j|^q$. Expanding the product gives at most $2^f$ terms. For indices in $J$, each term is bounded by an $L^1$ derivative of $C_*$ of total order at most $qf$. For indices in $Z$, use the weighted $L^\infty$ Fourier estimate of Proposition 2.1. Factors $A^{qf}$ and constants depending on $q$ are bounded by a new $C_q^{n+1}$ since $f\le n$. Integrate in $\nu$ last. In particular (10.7) respects the position of the time-frequency integral.

Fix a spatial modulation $(\xi,\zeta)$. For each coordinate define

$$
 A_j(s)=\sum_{x,y\in\mathbb Z_L^d}\psi_j(x-a_j)\psi'_j(y-b_j)
 e(\xi_j\cdot x+\zeta_j\cdot y+s x\cdot y),
$$

and let $B_j(s)$ be $L^{2d}$ times its continuum analogue. Choose the same cutoff $\kappa(s/L)$ as in §4. The scalar estimates used in Proposition 4.1 yield, uniformly in all centers and modulations,

$$
 \int\kappa(s/L)(|A_j(s)|+|B_j(s)|)\,ds\le C L^{2d},
 \tag{10.8}
$$

$$
 \int\kappa(s/L)|A_j(s)-B_j(s)|\,ds
 \le C L^{2d-1+2\eta_0}(1+|\xi_j|+|\zeta_j|),
 \tag{10.9}
$$

and, for $q>\eta_0^{-2}$ and $a_\gamma=2(d-1)(1-\gamma)$,

$$
 \int(1-\kappa(s/L))\langle s/\mu\rangle^{-q}|A_j(s)|\,ds
 \le C_q L^{2d-a_\gamma+\eta_0}.
 \tag{10.10}
$$

Finally stationary phase gives

$$
 \int(1-\kappa(s/L))|B_j(s)|\,ds
 \le C L^{2d-(d-1)}.
 \tag{10.11}
$$

Take $0<\eta_0<\varepsilon/8$, also small relative to $a_\gamma$, and then fix the integer $q>\eta_0^{-2}$. This integer is fixed before $\delta$ and the order exponent $K$.

Fourier inversion writes the fixed-modulation version of $I_v(\nu)$ as

$$
 \mu^{-n}\int f_{v,\nu}(s/\mu)\prod_{j=1}^n A_j(s_j)\,ds,
 \tag{10.12}
$$

and its continuum version has $B_j$ instead of $A_j$. Insert

$$
 1=\sum_{F\subset[n]}\prod_{j\in F}(1-\kappa(s_j/L))
                         \prod_{j\notin F}\kappa(s_j/L).
 \tag{10.13}
$$

For $F=\varnothing$, the bound follows from (10.7) with $f=0$ and (10.8). The difference of the products in (10.12) is the exact telescoping sum

$$
 \prod_j A_j-\prod_j B_j
 =\sum_{i=1}^n(A_i-B_i)\prod_{j<i}A_j\prod_{j>i}B_j.
$$

Use (10.9) for its $i$th factor and (10.8) for the others. Integrating the resulting sum against $d|\omega|$ costs only $nD_1$, bounded by $2^nD_1$. This gives (10.6) for the all-major term with $L^{-1+2\eta_0}$.

For a nonempty $F$, apply (10.7), (10.8), and (10.10) to the lattice expression. Its absolute weighted integral is at most

$$
 B C_q^{n+1}(L^{2d}/\mu)^n(8qf)!\,
 L^{-(a_\gamma-\eta_0)f}.
 \tag{10.14}
$$

For $1\le f\le n\le H(\log L)^K$, choose $L$ so large that

$$
 (8qf)!\le(8qn)^{8qf}\le L^{\eta_0 f}.
 \tag{10.15}
$$

The second inequality is equivalent to $8q\log(8qH(\log L)^K)\le\eta_0\log L$, and is valid for each fixed $H,K$. It changes the threshold, not $C_q$. Thus every term (10.14) has gain at least $L^{-a_\gamma+2\eta_0}$. The at most $2^n$ subsets are absorbed in $C^{n+1}$. For the continuum contribution use (10.7) with $f=0$, (10.8), and (10.11); no factorial is needed, and every nonempty subset gives at least $L^{-(d-1)}$. Combining these estimates and using $\gamma_1=\min(1,a_\gamma)\le d-1$ proves (10.6). The same estimates, including the all-major terms, prove (10.5).

For rigor in (10.12), the smooth integrable coefficient and its derivatives have an integrable spectral Fourier transform in every finite dimension, and Proposition 2.1 supplies the same for each extracted factor. This first justifies Fourier inversion for almost every $\nu$ and fixed $n$. Truncating the $s$ and modulation integrations and then using (10.7)–(10.15) justifies all limiting interchanges by absolute majorants. No constant from that preliminary finite-dimensional justification is used in the estimates. ∎

**Exclusion factors.** For an actual linked sum, $\epsilon_j$ is the factor of T1025. At least one of $x_j,y_j$ is zero in every term of $A_j^\epsilon-A_j$. Hence $|A_j^\epsilon-A_j|\le CL^d$, uniformly in $s$. If $j\in Z$, $g_{\boldsymbol S_j}(\mu x_j\cdot y_j)=0$ on this exceptional set, so no correction occurs. For $j\in J$, the correction can be bounded by evaluating the coefficient at $\alpha_j=0$ and using the one-dimensional trace estimate

$$
 \int|C(0,\alpha_{J\setminus\{j\}})|\,d\alpha_{J\setminus\{j\}}
 \le\int(|C|+|\partial_{\alpha_j}C|)\,d\alpha_J.
 \tag{10.16}
$$

A simultaneous correction in $f$ coordinates requires derivatives of total order at most $f$, and its factorial is absorbed as in (10.15). Relative to the ordinary factor $L^{2d}/\mu$, each correction costs at most $C\mu L^{-d}\le C L^{-(d-2\gamma)}$. Since $d-2\gamma>1\ge\gamma_1$ for $d\ge3$, these corrections fit (10.5)–(10.6), after reducing the auxiliary $\eta_0$ if necessary. The exact subset expansion has at most $2^n$ terms. This includes simultaneous zero-vector exclusions rather than treating them as an unquantified error.

**Scope of the reduction to boxes.** Theorem 10.1 applies after the specific refinement T1002–1004, whose number of subterms and total spatial Fourier mass are charged before using the theorem. If another application supplies only D23's triangular boxes with arbitrary radii, it needs the original triangular induction or an independently bounded refinement; Theorem 10.1 alone does not assert such a refinement. For the original regular-object variables in T981–1017 the cited refinement is available. Fixing some of those independent variables leaves the remaining unit boxes independent, which is why the exceptional-coordinate application below uses this version.


## 11. Cutoff insertion and the continuum principal-value limit

**Lemma 11.1 (mixed coefficient stability).** Suppose the coefficient before inserting upper filters satisfies (9.2). Multiply it in each coordinate $j\in J$ by at most two factors $\vartheta(\alpha_j/S)$, $S\ge1$. The new coefficient satisfies (10.3), with the same $B$ and a new base $A'$ independent of all scales and $\delta$. Cutoffs in $Z$ replace $g$ by $g_{\boldsymbol S_j}$; cutoffs in $E$ are bounded scalar multipliers after the exceptional tuple is fixed. If the original coefficient has the source weighted moment in $\alpha_J$, the new coefficient has the same moment bound.

**Proof.** In the product rule, a multi-index $\beta$ falling on cutoffs gives a bound $A_0^{2n+|\beta|}(2|\beta|)!$, because there are at most two factors per coordinate and their scales are at least one. Apply (9.2) to the other $|\rho|-|\beta|$ derivatives. The inequalities

$$
 (2|\beta|)!(4|\rho|-4|\beta|)!\le(4|\rho|)!,\qquad
 \sum_{\beta\le\rho}\binom\rho\beta=2^{|\rho|}
$$

bound the result by $B A_1^{n+|\rho|+1}(4|\rho|)!$, which is stronger than (10.3). Frequency recentering depends only on exceptional coordinates, so these derivatives do not differentiate the center. The last statement uses only $|\vartheta|\le1$. ∎

Here is a direct continuum argument in the same independent boxes. It supplies the principal-value interpretation without iterating a scalar estimate through a newly nonsmooth amplitude.

**Lemma 11.2 (one-coordinate density).** For fixed spatial modulations, the pushforward under $(x,y)\mapsto x\cdot y$ of

$$
 \psi(x-a)\psi'(y-b)e(\xi\cdot x+\zeta\cdot y)\,dx\,dy
$$

has a density $h(r)$ such that

$$
 \|h\|_1+\|h\|_\infty+\|h'\|_\infty\le C,
 \tag{11.1}
$$

uniformly in $a,b,\xi,\zeta$. The derivative is the classical derivative of the continuous Fourier representative. Its principal value $p=\operatorname{pv}\int h(r)/r\,dr$ exists and satisfies $|p|\le C$.

**Proof.** Its Fourier transform is the continuum oscillatory kernel of §10, without the factor $L^{2d}$. The stationary-phase bound used in (10.11) gives $|\widehat h(s)|\le C\langle s\rangle^{-d}$. Since $d\ge3$, both this function and $s\widehat h(s)$ are integrable. Fourier inversion therefore gives a continuously differentiable density with the stated suprema. The pushforward of the absolute value of the original finite measure has total mass bounded by the volume of its fixed boxes, which proves $\|h\|_1\le C$. For the principal value, the integral over $|r|\ge1$ is bounded by $\|h\|_1$. Over $0<|r|<1$, pair $r$ with $-r$ and use $|h(r)-h(-r)|\le2\|h'\|_\infty r$. This proves the assertion. ∎

For $j\in Z$ define

$$
 p_{j,\boldsymbol S}=\int\frac{\chi_\infty(\mu r)}r
       \prod_i\vartheta(r/M_{ji})h_j(r)\,dr,
 \qquad S_{ji}=\mu M_{ji},\quad M_{ji}\ge L.
$$

Evenness of $\chi_0$ and (11.1) imply

$$
 |p_{j,\boldsymbol S}-p_j|\le C(\mu^{-1}+L^{-1}),\qquad
 |p_{j,\boldsymbol S}|+|p_j|\le C.
 \tag{11.2}
$$

Indeed, the low-frequency difference is the symmetric integral of $\chi_0(\mu r)h_j(r)/r$ and is at most $C\mu^{-1}$ by the Lipschitz bound. The upper-cutoff difference is supported in $|r|\ge\min_i M_{ji}$ and is at most $L^{-1}\|h_j\|_1$. For $j\in J$, (11.1) gives, for every $0<p\le1$,

$$
 |h_j(\alpha/\mu)-h_j(0)|\le C\min(1,|\alpha|/\mu)
 \le C\mu^{-p}\langle\alpha\rangle^p.
 \tag{11.3}
$$

**Theorem 11.3 (many-variable principal-value formula).** In Theorem 10.1 suppose, in addition, that the unfiltered coefficient $C$ obeys

$$
 \int w_0(\nu)\int\max_{j\in J}\langle\alpha_j\rangle^p
       |C(\nu,v,\alpha_J)|\,d\alpha_Jd\nu\le BA^{n+1},
 \tag{11.4}
$$

with $0<p\le1$; an empty maximum means one. Let $C_*$ be obtained by upper filtering $C$ as in Lemma 11.1, with $S_{ji}=\mu M_{ji}$ and $M_{ji}\ge L$. The principal approximation uses the **unfiltered** coefficient:

$$
 I_v^{\rm pv}(\nu)=\left(\frac{L^{2d}}\mu\right)^n
 \left(\int C(\nu,v,\alpha_J)\,d\alpha_J\right)
 \int\Upsilon(z)W(z)
 \prod_{j\in Z}\operatorname{pv}\frac1{\Omega_j}
 \prod_{j\in J}\delta_0(\Omega_j)\,dz.
 \tag{11.5}
$$

The product distribution in (11.5) acts on independent coordinate pairs, and its pairing with the Fourier-measure amplitude is defined by the absolutely convergent modulation representation from Lemma 11.2. Then

$$
 \int w_0|I_v^c-I_v^{\rm pv}|\,d\nu
 \le BD_0 C^{n+1}(L^{2d}/\mu)^n
       (\mu^{-p}+\mu^{-1}+L^{-1}).
 \tag{11.6}
$$

The approximation itself has weighted norm at most $BD_0C^{n+1}(L^{2d}/\mu)^n$.

**Proof.** Fix one spatial Fourier modulation. Integrate first in the $Z$ coordinate pairs and then use the densities $h_j$ for $j\in J$. After factoring out $(L^{2d}/\mu)^n$, the exact continuum expression is

$$
 \prod_{j\in Z}p_{j,\boldsymbol S}
 \int C_*(\nu,v,\alpha_J)\prod_{j\in J}h_j(\alpha_j/\mu)\,d\alpha_J.
 \tag{11.7}
$$

In (11.7), replace each $p_{j,\boldsymbol S}$ by $p_j$ using (11.2). Telescope the product of $h_j$ and replace each factor by $h_j(0)$, using (11.3). The latter error is bounded by $nC^{n+1}\mu^{-p}$ times the moment in (11.4); it uses a sum of coordinate moments, each bounded by the one maximum moment, and does **not** claim a product moment.

Finally remove the upper factors from $C_*$. The identity

$$
 \left|1-\prod_{j,i}\vartheta(\alpha_j/S_{ji})\right|
 \le\sum_{j,i}\mathbf1_{|\alpha_j|\ge S_{ji}}
$$

shows that the integrated difference is at most $2n(\mu L)^{-p}$ times (11.4). This is a coefficient integral, not removal of a cutoff inside an oscillatory lattice sum. All other factors are bounded by $C^{n+1}$ from Lemma 11.2. Absorb $n\le2^n$, integrate against the spatial Fourier measure, and obtain (11.6). The resulting main term is precisely (11.5). ∎

For the D23 moment $p=1-\eta/2$ and $0<\eta\ll1$, the continuum error has the source size after $L$ is chosen after $\delta$:

$$
 \mu^{-p}+\mu^{-1}+L^{-1}\le C L^{-\gamma_1+\eta}.
 \tag{11.8}
$$

For the first term note explicitly that $2\gamma p=2\gamma-\gamma\eta>1-\eta\ge\gamma_1-\eta$. Thus the factor $\delta^{-p}$ is absorbed by the strict exponent margin in (11.8), and is not raised to the order $n$. The second term has the same property because $2\gamma>1$.

**Time-weight interpolation.** In the coherent source case, (10.3) is available with $w_1=\max_i\langle\nu_i\rangle^{1-\eta/8}$, and (11.4) with $w_0=\max_i\langle\nu_i\rangle^{\eta/4}$. Equations (10.5) and (11.5) give a uniform bound for the difference in the $w_1$ norm without a gain; equations (10.6), (11.6), and (11.8) give the error $L^{-\gamma_1+\eta}$ in the $w_0$ norm. Weighted Hölder interpolation with

$$
 t=\frac{\eta-\eta/4}{1-\eta/8-\eta/4}
   =\frac{3\eta/4}{1-3\eta/8}\le\eta\quad(\eta\le2/3)
$$

therefore gives in the required $X^\eta$ Fourier weight the error

$$
 C^{n+1}BD_1(L^{2d}/\mu)^n
 L^{-(\gamma_1-\eta)(1-t)}
 \le C^{n+1}BD_1(L^{2d}/\mu)^n
 L^{-(\gamma_1-\sqrt\eta)}
 \quad(0<\eta\le1/16).
 \tag{11.9}
$$

Indeed $(\gamma_1-\eta)(1-t)\ge\gamma_1-2\eta$ and $2\eta\le\sqrt\eta$. The gain is the T1100/T1148 allowance. This calculation explains exactly how the two different coefficient weights are used. It does not require the strong time weight on the spectral moment.

Consequently, for an **unpinned coherent regular object** with the source amplitude hypotheses and the unit-box refinement, inserting all the upper filters changes the source principal approximation by an error of the allowed size. Its principal value, its unfiltered coefficient, and hence its existing coherent algebraic identities remain the same. No additional positive power of $L$ is spent. This conclusion is local to the stated regular object; applying it inside a family still requires the source grouping hypotheses and the separate marked-family results.


## 12. Addendum 2: common profiles and the reduced mark set

The user has directed us to use o63's Theorem 6.3′ and Proposition 10.3′. Accordingly, every continuation statement is uniform over

$$
 \mathcal P(C_1)=\{(F_q)_{q\le p}:F_q\text{ real},\
                    \sup_q\|F_q\|_{\mathfrak S^{40d,40d}}\le C_1\}.
 \tag{12.1}
$$

The references in §§1–9 to selected frontier vertices and modified final-leaf monomials are superseded for this application. No such vertices or leaves are marked or charged. External decay and the first-shell gain are extracted by o63's exact common-profile identity, at additional $L$ exponent **zero**. That identity is applied outside the local analytic estimates here; it does not alter their original-tree labels, second-cutoff factors, or selected-time faces.

For (12.1), the source amplitude argument T995–1013 applies uniformly: take the required output derivatives before the localization; retain the reserve used by T997–1000; Fourier expand the tensor product of the localized leaf profiles; and use the stated integer linear coordinate map. The first spatial Fourier moment is controlled by one further spatial derivative. The remaining $8d$ reserve in T1000 is sufficient for this operation and the fixed-dimensional Fourier $L^1$ estimates on each leaf factor. Polynomial factors in the number of leaves are bounded by a fixed base to the power $m+1$.

The affine frontier cutoffs retained after expanding each shell as a difference of low-pass products are handled by supplement Lemma 3.1. Their Fourier-measure total variation has a fixed base per factor. The first moment of their pushforward measures is bounded by a polynomial in $m$ times that base: each original vertex momentum is a signed sum of at most $O(m)$ independent vector coordinates, and every scale is at least $L\ge1$. The product first moment is a sum of individual first moments, not a product of them. Thus the amplitude quantities $D_0,D_1$ in (10.1), summed over the source localizations, are bounded by $C_{P,\chi}^{m+1}$ for ordinary input slots, uniformly over (12.1). There is no $\delta$-dependent exponential base.

Caps and special boundary inputs remain separate from these ordinary profile slots. No Schwartz bound for a constant cap input is inferred. Their exact boundary encoding and any output derivatives they require belong to the marked-object interface and the exceptional-piece construction. In particular, this amendment removes the Section 6 marks but does not erase flower-parent pins or special-node boundaries.

## 13. The simultaneous conditional estimate and all occurrence gains

**Theorem 13.1 (consumer of the marked coefficient interface).** Assume interface I of §9 for an order-$2m$ localized regular piece, with $r$ charged pin/face incidences and $e=|E|\le2r$. Suppose its coefficient factor is

$$
 B=B_{\rm mark}\,G_{\rm unmarked},\qquad
 B_{\rm mark}\le C_{P,\delta}L^{\kappa_d r},
 \tag{13.1}
$$

where $G_{\rm unmarked}$ denotes the product of all gains that the producer has retained on unmarked portions, and $\kappa_d$ is a numerical loss supplied by that producer. All coefficients obey the original-coordinate requirement of §9. The amplitude is uniform over (12.1), with the boundary-input costs, if any, included explicitly in its bound.

Then arbitrary upper filters with multiplicity at most two per independent frequency can be inserted. The normalized decoration sum in the consumed time norm is bounded by

$$
 C_{P,\chi,\vartheta}^{m+1}C_{P,\delta}\,
 (C_1\delta)^m L^{(\kappa_d+4)r}
 G_{\rm unmarked}.
 \tag{13.2}
$$

If $a$ selected occurrences are present and their raw integration reciprocals are retained, the stronger bound is

$$
 C_{P,\chi,\vartheta}^{m+1}C_{P,\delta}\,
 (C_1\delta)^m L^{(\kappa_d+4)r}
 G_{\rm unmarked}\,M_2^{-3a/4}.
 \tag{13.3}
$$

Here we allow the $1/4$ modulation cost per selected occurrence in §9, item 4. Without that cost the gain is $M_2^{-a}$. Either estimate implies the requested $M_2^{-a/18}$. Multiple selected occurrences of the same linked frequency are counted separately. This is a conditional theorem: it proves the insertion and spatial-summation implications of the interface, not the construction of its coefficient representation.

**Proof.** Fix an exceptional spatial tuple $z_E$ in its independent unit boxes. There are at most $C^eL^{2de}$ choices. The exceptional upper filters and annular factors are now scalar factors, uniformly bounded independently of all scales. Restricting the spatial Fourier measure to $z_E$ replaces it by a phase-weighted projection, so it does not increase $D_0$ or $D_1$.

Apply Lemma 11.1 to the integrable-coordinate factors and Proposition 2.1 to the extracted factors. Theorem 10.1 applies to the remaining $m-e$ coordinates with $v=z_E$. All fixed exceptional resonances and their Fourier centers are genuine parameters during this application. In particular no derivative in an exceptional direction, no spectral box supremum inferred from an integral, and no restriction to a frequency fiber inside an oscillatory sum is used.

Theorem 10.1 gives the factor $(L^{2d}/\mu)^{m-e}$. Sum the resulting **absolute** bounds over the exceptional tuples. Multiplying by the full branching normalization gives the exact identity

$$
 \left(\frac{\delta}{2L^{d-\gamma}}\right)^{2m}
 L^{2de}\left(\frac{L^{2d}}\mu\right)^{m-e}
 =\left(\frac\delta4\right)^m\mu^e.
 \tag{13.4}
$$

Since $\delta\le1$, $2\gamma<2$, and $e\le2r$, we have $\mu^e\le L^{2e}\le L^{4r}$. This proves (13.2), including the same factor $G_{\rm unmarked}$ as in the interface. An exceptional-coordinate factor already extracted by the producer may be kept in the scalar coefficient; no additional summation loss is needed for it if its stated uniform bound is included in (13.1).

For the selected gain, on every selected annulus $c\mu M_2\le|\alpha_{j(v)}|\le C\mu M_2$. Since $\mu M_2\ge1$,

$$
 \prod_{v\ {\rm selected}}
 \frac{\langle\alpha_{j(v)}\rangle^{1/4}}
      {\pi|\alpha_{j(v)}|}
 \le C^a(\mu M_2)^{-3a/4}.
 \tag{13.5}
$$

This is a product over occurrences. If a coordinate is selected twice, its factor is explicitly $\langle\alpha_j\rangle^{1/2}/(\pi^2|\alpha_j|^2)$; it is not replaced by a single reciprocal. The total face coefficient mass in (9.2) is estimated after multiplying by (13.5). Use $\mu\ge1$ and then (13.4) to obtain (13.3). The constant $C^a$ has no $L$ or $\delta$ dependence. Because $M_2\ge1$, $M_2^{-3a/4}\le M_2^{-a/18}$, including when several occurrences share a coordinate. ∎

**Face multiplicities and signs.** For a per-face interface, first partition each selected time interval by its maximizing child/floor endpoint, then choose its upper or lower endpoint. Keep all at most $8^a$ resulting expressions with their original signs and indicators, exactly as supplement Lemma 9.1. Apply the theorem to each one and sum its coefficient mass. The total extra constant is $8^a$; it is included once in $B_{\rm mark}$ or in the coefficient sum in (9.2). If the producer instead proves a signed-collection estimate, preserve that collection and apply the theorem to its representation without splitting its signs. The theorem does not assert that an isolated face satisfies an estimate which was proved only for its signed collection.

**Approximation on the nonexceptional variables.** Under the moment hypothesis of Theorem 11.3, the same argument retains the discrete exceptional sum exactly and replaces only the remaining variables by their principal-value/delta formula. Its error has the additional gain in (10.6), followed by (11.9) when the source two time weights are used. Thus the exceptional-coordinate treatment does not consume the approximation gain on the nonexceptional block. This is a partial, or hybrid, principal approximation; no asymptotic formula for an exceptional coordinate is claimed.

**Quantifier order.** The constants in Lemma 11.1, the fixed derivative order $q$ in Theorem 10.1, and the exponential base in (13.2) depend on the fixed cutoffs, $d,\gamma,\eta,C_1$, and $P$. They are chosen before $\delta$. For a fixed $\delta$, T612 supplies fixed $H_\delta,K_\delta$ for $m\le N^4$; (10.15) only enlarges the last threshold for $L$. The normalization (13.4) supplies $(C_1\delta)^m$, not $(C_2\delta)^m$. A factor $C_{P,\delta}$ occurring in the marked coefficient estimate remains a single such factor. No per-order $C_2$ factor is hidden in the estimate.

**Comparison with o73's posted interface.** At the time of this continuation, o73 §10 states the same partition $E\sqcup Z\sqcup J$, the same original-coordinate extracted factors, the bound $e\le2(b+a)$, the same occurrence product, and the source coefficient moments. Its explicitly recorded modulation agrees with $\ell_F$ in §9. Its displayed norms are centered before consumption, whereas Theorem 13.1 uses the consumed norm (9.2), or its permitted selected-frequency growth. Consequently Theorem 13.1 applies when o73 supplies that consumption estimate and its numerical $\kappa_d$. It must not be applied solely to the centered inequalities in that provisional interface.


## 14. Upper filters preserve the raw incoherent pair gains

The preceding conditional theorem requires a coefficient interface that retains the gains of unmarked side objects. The following independent result verifies the preservation of those gains at the raw, pointwise-in-boundary-times stage. It extends the pointwise estimate in o73 §4 to the remaining upper resonance filters, and is available as an input to its Fourier-norm argument.

**Lemma 14.1.** Let $A(s)$ be the localized linked exponential sum of T1030, initially with exclusion factor replaced by one, and let

$$
 A_H(s)=\sum_{x,y\in\mathbb Z_L^d}\psi(x-a)\psi'(y-b)
 e(\xi\cdot x+\zeta\cdot y+s x\cdot y)
 \prod_{i=1}^h\vartheta((x\cdot y)/M_i),
 \qquad h\le2,\quad M_i\ge L.
$$

For unit layer intervals $I_q=[q,q+1]$ and $I_{q'}=[q',q'+1]$, the estimates

$$
 \int_{I_q\times I_{q'}}|A_H(\mu(u-v))|\,du\,dv
 \le C\frac{L^{2d}}\mu
 \begin{cases}
 1,&q=q',\\
 L^{-(\gamma_1-\sqrt\eta)},&q\ne q'
 \end{cases}
 \tag{14.1}
$$

hold uniformly in all centers and modulations, for $L$ sufficiently large after $\delta$. The base constant $C$ is independent of $\delta$. The same result holds with the exclusion factor of T1025.

**Proof.** Fourier inversion of the at most two filters gives

$$
 A_H(s)=\int A(s+\tau)\,d\omega_M(\tau),\qquad
 \int(1+M_*|\tau|)^q\,d|\omega_M|(\tau)\le C_q,
 \tag{14.2}
$$

where $M_*=\min_i M_i$, and for $h=0$ use the unit point mass at zero. The moment bound follows from scaling the Fourier transform of $\vartheta$ and convolution; it is uniform in all scales.

T958–968 and Poisson summation give $|A(r)|\le CL^{2d}\langle r\rangle^{-d}$ for $|r|\le L$. In particular the integrals of $|A(r)|$ and $|rA(r)|$ over this range are both at most $CL^{2d}$. For $|r|\ge L$, D23 L1084–1086 gives, for one fixed $q>\eta_0^{-2}$,

$$
 \int_{|r|\ge L}\langle r/\mu\rangle^{-q}|A(r)|\,dr
 \le C_q L^{2d-a_\gamma+\eta_0},
 \qquad a_\gamma=2(d-1)(1-\gamma),
 \tag{14.3}
$$

where $0<\eta_0<\eta$ is fixed.

The difference $z=u-v$ of two independent unit intervals has a density $\ell_{q,q'}(z)$ with $0\le\ell\le1$. For equal layers it is supported in $|z|\le1$. Thus, after setting $r=\mu z+\tau$, the equal-layer integral is bounded by

$$
 \mu^{-1}\int d|\omega_M|(\tau)
                  \int_{|r|\le\mu+|\tau|}|A(r)|\,dr.
$$

Its $|r|\le L$ part is bounded by $CL^{2d}/\mu$. For its other part, use (14.3) and
$\langle r/\mu\rangle^q\le C_q(1+|\tau|/\mu)^q$ on the integration region. Equation (14.2), $\mu\ge1$, and $M_*\ge1$ bound the resulting moment independently of $\delta$. This proves the equal-layer line of (14.1), since $a_\gamma>\eta_0$.

For unequal integer layers, $\ell_{q,q'}(z)\le\min(1,|z|)$. On $|r|\le L$ it gives the bound

$$
 C L^{2d}\mu^{-2}\int(1+|\tau|)\,d|\omega_M|(\tau)
 \le C L^{2d}\mu^{-2}.
 \tag{14.4}
$$

On $|r|\ge L$, use only $\ell\le1$. The layer difference is bounded by the source's fixed $\mathcal D$, so $|r|\le(\mathcal D+1)\mu+|\tau|$ on the support. Equations (14.2)–(14.3) give
$C_{\delta}L^{2d}\mu^{-1}L^{-a_\gamma+\eta_0}$. Relative to $L^{2d}/\mu$, (14.4) costs $\mu^{-1}=\delta^{-1}L^{-2\gamma}$. Since $\gamma_1\le2\gamma,a_\gamma$ and $\sqrt\eta>\eta_0$, choose $L$ so large that these constants depending on $\delta$ are absorbed into
$L^{-(\gamma_1-\sqrt\eta)}$. This is a per-unequal-pair absorption using its existing gain, not an uncontrolled exponential $C_\delta^m$.

Finally, the zero-vector exclusion changes the sum by $O(L^d)$, since on either zero-vector set the upper factors equal one. The integrated error has the same bound. Dividing by $L^{2d}/\mu$ gives at most $L^{-(d-2\gamma)}$, because $\delta\le1$. As $d-2\gamma>1\ge\gamma_1$, this error fits both lines of (14.1). ∎

**Proposition 14.2 (pointwise pinned and face estimate with all upper filters).** Use the raw regular-object variables of T981–1017. Delete $b$ time integrations by pins and $a$ further integrations by a fixed legal selected-time face, and let $E$ be the links incident to these deleted times. Set $e=|E|\le b+a$ and let $g_J$ count the unequal-layer links outside $E$. Let the remaining spatial amplitude have Fourier-measure mass at most $K$, uniformly in the fixed external data. Insert upper filters of Lemma 14.1 at any of the links, and a bounded multiplier $R_E$ depending only on the exceptional link variables, $|R_E|\le R$.

The fully normalized raw expression obeys

$$
 |I_F|\le KR(C\delta)^m\mu^e
                    L^{-(\gamma_1-\sqrt\eta)g_J}.
 \tag{14.5}
$$

In particular it obeys
$KR(C\delta)^mL^{3e}L^{-(\gamma_1-\sqrt\eta)g}$, where $g$ is the original incoherency count. For original stem pins/faces in the geometry of o73 Proposition 3.1, all exceptional links are same-layer and the cost is $L^{2e}$ while the full $g$ gain is retained.

**Proof.** Fourier expand the spatial amplitude. Fix all exceptional lattice variables, or equivalently bound their joint sum by $RC^eL^{2de}$. Every boundary phase carried by those links has modulus one and is removed only at this point, in a pointwise bound. No time integration associated with an untouched link has been deleted. The remaining product of linked sums consists exactly of the filtered sums in Lemma 14.1. Take its absolute value, enlarge the remaining time domain to the product of its original unit intervals, and apply (14.1) pair by pair. The branching normalization is exactly (13.4). This proves (14.5).

At most $e$ unequal-layer links were made exceptional. Paying $L^{(\gamma_1-\sqrt\eta)e}$ restores the original $g$ exponent, while $\mu^e\le L^{2e}$ and $\gamma_1\le1$, giving $L^{3e}$. For a same-layer stem link no incoherency was removed, giving the improved $L^{2e}$. ∎

If the $a$ raw selected reciprocals are retained, set
$R=(\pi c\mu)^{-a}M_2^{-a}$. This counts repeated occurrences exactly. The number of faces is at most $8^a$. Consequently the pointwise argument supplies the full occurrence gain and, for $b+a\le4P$, costs at most $L^{12P}$ in general or $L^{8P}$ for original stem marks, with no additional $L$ cost from upper filters.

The proposition is explicitly a **pointwise** statement. It does not bound a weighted Fourier norm of an isolated face, discard a boundary modulation before its neighboring integration, or prove the producer interface. Its contribution is to remove the remaining-upper-filter limitation from o73's pointwise estimate.


## 15. Filtered ordinary kernels and the terminal-pin consequence

The pointwise pair estimate in Lemma 14.1 has a sharper version that leaves room for the source time-Fourier argument. In its unequal-layer line one may use $L^{-(\gamma_1-2\eta)}$ instead of $L^{-(\gamma_1-\sqrt\eta)}$: choose $\eta_0<\eta$ in (14.3), and absorb each fixed $C_\delta$ into $L^{2\eta-\eta_0}$. This does not change any equal-layer constant or introduce a positive $L$ loss. Below assume the standing smallness of $\eta$ is strong enough that $200d\eta\le\sqrt\eta$.

**Proposition 15.1 (ordinary kernels with upper filters).** Let $\mathcal Q$ or $\mathcal T$ be an ordinary layered regular object of order $2m$, with incoherency index $g$, supplied with profiles in (12.1). Insert at most two upper factors $\vartheta(\Omega_v/M_v)$ per independent linked frequency, with $M_v\ge L$, and the admitted affine frontier low-pass factors of the supplement, with their Fourier-measure costs counted. No pin or time face is present in this proposition.

For $g\ge1$ the source bound holds with a new $\delta$-independent exponential base:

$$
 \|K_{\mathcal Q,H}\|_{X^{\eta,30d,30d}}
 +\|K_{\mathcal T,H}\|_{X^{\eta,30d,0}}
 \le C_{\chi,\vartheta}^{m+1}(C_1\delta)^m
        L^{-(\gamma_1-\sqrt\eta)g}.
 \tag{15.1}
$$

Only defined terms are included. For $g=0$, the same bound without the negative $L$ power holds, and the source principal approximation with its admitted spatial amplitude is unchanged by the **upper resonance filters**, up to an error bounded by the right side of (15.1) with $g=1$. This statement does not change whatever first-cutoff profile hypotheses are required for an algebraic family cancellation.

**Proof for $g\ge1$.** Repeat the source proof T981–1092 with the following explicit replacements.

* The coordinate change, output derivatives, leaf localization, and spatial Fourier expansion at T981–1017 are unchanged. The resonance upper factors depend on $(x_j,y_j)$ only and have no $k$ dependence; output derivatives still fall on the spatial input amplitude. The affine frontier factors have the Fourier-measure bounds recorded in §12.
* In the product of linked sums T1021, replace each $\mathcal S_j$ by its filtered sum $A_{H_j}(\mu(t_j-t'_j))$, including its exclusion factor. The trivial supremum remains $CL^{2d}$, since all new multipliers have modulus at most one. Lemma 14.1 in its sharpened form gives exactly the equal-layer integrated bound and the unequal-layer bound with exponent $\gamma_1-2\eta$. Thus the product estimates needed at T1043 and T1051 hold with a new fixed base.
* For a couple, the double primitive, its bounds at T1050, and its canonical extension T1054 have the same domains and boundary variables. The bounds at T1050 use only the preceding integrated and supremum estimates. The time-integration lemma and interpolation used at T1052–1057 therefore apply without any new cutoff derivative or time oscillation.
* For a regular tree, the two legal endpoint configurations T1067, and the expressions T1069 and T1072, are unchanged. The estimates T1080 use the same pairwise integrated bounds. In T1084 expand the one or two designated endpoint linked sums into their lattice exponentials. Each coefficient has merely acquired its scalar upper factor, of modulus at most one. The number of tuples remains at most $C L^{4d}$; every bound there is uniform in the resulting frequencies. In the mixed boundary derivatives T1086–1089, the upper filters are time-independent, and the explicit exponentials involving the two differentiated boundary times are still precisely the designated endpoint sums. Differentiation of the remaining time integrals only creates the same boundary evaluations as in the source. Their estimates use the unchanged supremum bound and the sharpened pairwise bounds. Thus the source negative Fourier norm, positive $1/4$ Fourier norm, and their interpolation still apply.

For completeness, these replacements give the source losses at most $100d\eta$ per incoherency in the intermediate bounds. In interpolating from exponent $-\eta$ to $1/4$, the interpolation parameter is $2\eta/(1/4+\eta)\le8\eta$. The extra $L^{4d}$ at the positive endpoint contributes at most $32d\eta$. Since $g\ge1$, charging this to $g$ and allowing $200d\eta$ covers both the original intermediate losses and this interpolation. The imposed smallness $200d\eta\le\sqrt\eta$ gives (15.1). The canonical time extensions are the source's fixed extensions, independent of $k$, spatial modulation, and output differentiation. Hence this argument preserves the source order of output supremum and time-frequency integral; it is not a passage from a pointwise $X^\eta$ norm to the full norm.

**Proof for $g=0$.** The coherent factorization T1235–1244 separates the object into single-layer regular pieces with their original linkage. The inserted filters separate with those independent linked coordinates. For each piece use the unpinned decomposition (3.1), Theorems 10.1 and 11.3, and the time-weight interpolation (11.9). The principal coefficient is the unfiltered one. Source D23/T spatial amplitude hypotheses and the output derivative reserve are uniform over (12.1); §12 verifies the added affine factors at the same Fourier-measure level. There are at most $2^m$ spectral terms, absorbed in the base. Multiplying the single-layer decompositions gives the coherent product estimate and the allowed remainder, just as T1242. Every factor has a base independent of $\delta$; the number of nontrivial factors is at most $m$.

For coherent paired trees, the output supremum inside the time-Fourier integral does not require output decay: in this application the unpinned time coefficient is independent of $k$, and the proofs of Theorems 10.1 and 11.3 give, at each time frequency, a $k$-independent majorant formed from the spectral Fourier suprema of that coefficient and the spatially uniform lattice or continuum bounds. After the output derivatives are charged to the profile reserve and the spatial Fourier amplitudes are integrated with their common finite total variation, this majorant is integrable with the required time weight. Thus $\sup_k$ may be taken inside the $\lambda$-integral, as required by $X^{\eta,30d,0}$; no interchange of an integral and a supremum of arbitrary fixed-$k$ bounds is used. ∎

This proposition supplies actual **kernel** estimates for filtered ordinary layered components, including incoherent components, without requiring a raw mixed spectral coefficient representation for every incoherent side object.

**Corollary 15.2 (filtered terminal pin).** For the geometry and decomposition of o73 Proposition 13.1, insert all the upper stem filters and the admitted affine spatial factors. The terminal-pin bounds o73 (13.2)–(13.3) remain valid with a new cutoff-dependent, $\delta$-independent exponential base. Explicitly, at fixed lattice output,

$$
 \|K_{{\rm pin},H}(\cdot,\cdot,k)\|_{X^\eta}
 \le C_{\chi,\vartheta}^{m+1}(C_1\delta)^m
 L^2 L^{-(\gamma_1-\sqrt\eta)g}.
 \tag{15.2}
$$

On a fixed unit output ball, the local extension has $X^{\eta,30d,0}$ norm bounded by the same expression with $L^{31d+2}$ in place of $L^2$. A cap constraint may be included as in that packet's finite-output construction.

**Proof.** In the exact cut at the pinned node's linked partner, the four components are ordinary layered regular objects. The original upper filters are a product of the filters assigned to those four components and at most two factors in the one exceptional linked coordinate. Fix that exceptional spatial pair. Its filters are bounded scalar factors. Proposition 15.1 supplies the required time-Fourier bounds for each of the four filtered components, with all their incoherency gains. Apply o73 Lemma 12.1 to the product in its formula (13.1); that lemma consumes the pin modulation uniformly. Sum the exceptional spatial tuples and restore their two branching normalizations, exactly as o73 Proposition 13.2. The loss is $L^{2\gamma}\le L^2$. The exceptional box centers are summable because their two side-couple output momenta parametrize the exceptional pair, and Proposition 15.1 supplies $\langle k_{Q_1}\rangle^{-30d}\langle k_{Q_2}\rangle^{-30d}$ decay (the corresponding profile decay when a side couple is trivial), uniformly in the fixed boundary momentum. Its finite-output interpolation construction costs $L^{31d}$ and applies unchanged. ∎

Thus the unresolved raw coefficient representation for incoherent side objects is not an obstacle to this terminal-pin corollary. This corollary does not assert the corresponding result for a child-endpoint face; its exact remaining geometry is different.


## 16. A direct high-frequency estimate for the partner of a terminal pin

This section addresses a concrete face configuration now posted in o73 §15. The root-trace counterexample there is valid for an inference from an $X^\eta$ norm alone. For an actual ordinary side kernel there is also a stronger, coarse Fourier norm available, at a numerical $L$ cost. Keeping the full signed face collection and using that norm gives a direct high-resonance estimate in this configuration.

**Lemma 16.1.** The ordinary filtered regular couples and paired trees in Proposition 15.1 satisfy the additional weighted bounds
$$
 \|K_{\mathcal Q,H}\|_{X^{1/4,30d,30d}}
 +\|K_{\mathcal T,H}\|_{X^{1/4,30d,0}}
 \le C_{\chi,\vartheta}^{m+1}(C_1\delta)^m
 L^{4d}L^{-(\gamma_1-\sqrt\eta)g}.
 \tag{16.1}
$$
Only defined terms are included, with each object's own order and incoherency index. In particular these imply the $X^{1/4}$ bounds at fixed spatial boundary data. For an incoherent couple alone the factor $L^{4d}$ improves to $L^d$, with the same output derivatives and weight. For a coherent object the positive power of $L$ can be omitted.

**Proof.** For an incoherent regular tree, retain the positive endpoint bound T1091 in the proof of Proposition 15.1, before its final interpolation. Its gain has exponent $\gamma_1-100d\eta$, which is at least $\gamma_1-\sqrt\eta$ under the standing smallness used there. For an incoherent couple, the double primitive has the source bounds at T1050, $\|S\|_1\le A$ and $\|S\|_\infty\le A L^{2d}$, with $A=(C\delta)^mL^{-(\gamma_1-2\eta)g}$. Hence $\|S\|_2\le A L^d$.

The kernel bound T2364–2366 gives $\|\mathcal I_\chi S\|_{X^{1/4}}\le C\|S\|_2$. To check this version explicitly, after integrating the output Fourier variables the one-coordinate convolution is bounded by
$C\langle\xi'\rangle^{-3/4}\log(2+|\xi'|)\le C\langle\xi'\rangle^{-2/3}$. The product of the two resulting weights is in $L^2(\mathbb R^2)$. Cauchy–Schwarz and Plancherel give the assertion. The resulting $L^d$ cost is bounded by $L^{4d}$. To obtain the stated couple output weight and derivatives, apply T995–T1000 before this argument: charge the $30d$ derivatives and $\langle k\rangle^{30d}$ weight to the $\mathcal S^{40d,40d}$ profiles, then use the remaining $2d$ derivatives and decay in T999 to put the output supremum inside the Fourier integral. This uses the same canonical extension for every derivative and every $k$, and introduces no further $L$ power, so the couple cost remains $L^d$. The paired-tree derivatives use the same profile reserve as Proposition 15.1. The canonical extensions and the upper-filter replacement are those of that proposition.

For a coherent object, the strong coefficient weight $1-\eta/8>1/4$ and Theorem 10.1 give a uniform bound in that stronger norm; no small error estimate is needed for this assertion. For coherent paired trees, use the $k$-independent majorant at each time frequency described in Proposition 15.1's coherent proof, now with weight $1/4$; it justifies the output supremum inside the Fourier integral without assuming decay in $k$. Couples retain their output weight by T995–T1000 as above. The product over coherent layer pieces has a fixed base per branching pair. ∎

**Lemma 16.2 (decay after consuming the pin modulation).** For $0\le\theta<\sigma\le1$, define
$\mathcal T_A H(t,s)=\int_s^t e^{\pi iA(u-s)}H(t,u,s)\,du$ on the unit triangle. Then

$$
 \|\mathcal T_A H\|_{X^\theta}
 \le C_{\theta,\sigma}\langle A\rangle^{-(\sigma-\theta)}
       \|H\|_{X^\sigma}.
 \tag{16.2}
$$

The right side is the Fourier-measure norm of an extension in the three input time variables.

**Proof.** For a Fourier atom with frequencies $(\xi,\lambda,\nu)$ the output is the atom used in o73 (12.3):
$e^{\pi i[\xi t+(\lambda+\nu)s]}h_{A+\lambda}(t-s)$.
With one fixed output cutoff, the $X^\theta$ norm of $h_z(t-s)$ is bounded by $C_\theta\langle z\rangle^{\theta-1}$ for $|z|\ge1$ and by $C_\theta$ otherwise. This follows directly by expanding its two exponentials for large $z$, and by its integral representation for small $z$.

Write $R=\max(1,|\xi|,|\lambda|,|\nu|)$. If $R\ge|A|/2$, the uniform bound for $h_z$ gives an output norm at most $C R^\theta\le C\langle A\rangle^{-(\sigma-\theta)}R^\sigma$. If $R<|A|/2$, then $|A+\lambda|\ge|A|/2$, and the output norm is at most $CR^\theta\langle A\rangle^{\theta-1}\le CR^\sigma\langle A\rangle^{-(\sigma-\theta)}$, since $\sigma\le1$. The bounded range of $A$ is included in these constants. Integrate this atom estimate against the input Fourier measure. The modulation has been consumed in the actual formula, not dropped or merely recentered. ∎

**Corollary 16.3 (one selected occurrence linked to the terminal pin).** In Corollary 15.2 suppose the selected stem vertex is the linked partner of the pinned terminal vertex, and impose its annulus $|\Omega_v|\asymp M_2$. For $\eta\le1/16$, at fixed lattice output,

$$
 \|K_{{\rm pin},H,{\rm ann}}\|_{X^\eta}
 \le C_{\chi,\vartheta}^{m+1}(C_1\delta)^m
 L^{16d+2}L^{-(\gamma_1-\sqrt\eta)g}
 M_2^{-1/18}.
 \tag{16.3}
$$

The local $X^{\eta,30d,0}$ extension on a unit output ball costs $L^{47d+2}$ instead. The selected annular multiplier and all remaining upper filters are retained.

**Proof.** Fix the exceptional linked spatial pair in o73's exact terminal-pin cut. By Lemma 16.1, each of its at most four ordinary components has an $X^{1/4}$ norm with at most $L^{4d}$ cost and its full incoherency gain. Pullback to $(t,u,s)$ and the Fourier algebra bound the product by $C^m(C_1\delta)^{m-1}L^{16d}$ times the product of those gains. Apply (16.2) with $\theta=\eta$, $\sigma=1/4$. On the selected annulus $|A|\asymp\mu M_2$ and $\mu\ge1$, its gain is at least $C M_2^{-(1/4-\eta)}\le C M_2^{-1/18}$. The exceptional spatial sum and branching factors cost $L^{2\gamma}\le L^2$, as in Corollary 15.2. The finite-output construction costs the additional $L^{31d}$. ∎

This is the permitted direct spectral alternative to estimating individual faces. Equivalently, keep the **entire** signed collection produced by integrating this selected time: the upper endpoint and every maximizing-child lower endpoint, with the regions and signs of supplement Lemma 9.1, all of multiplicity one before ties are removed. Their signed sum times the selected reciprocal is exactly the original annular kernel estimated in (16.3). No child term is separately bounded by differentiating an $X^\eta$ input. In the two-node geometry, this collection is exactly o73 (15.2).

This resolves that particular arbitrary-side example using an actual stronger source norm. It does not yet provide the insertion estimate for an arbitrary internal selected link inside a longer enclosing regular chain; no such conclusion is inferred from (16.2).



## 17. A bounded extension and interpolation on the time triangle

This section passes from the pointwise selected-time estimate to a time-Fourier estimate of the **whole** selected kernel. A small loss in the strong time exponent is harmless. The extension used in interpolation must preserve the small pointwise bound; an arbitrary near-minimizing extension need not do so.

Write $\mathcal A^\sigma(\mathbb R^j)$ for the Fourier algebra with norm
$\int\langle\xi\rangle^\sigma|\widehat H(\xi)|\,d\xi$. Fourier measures are also allowed. In fixed dimension this weight is equivalent to the source's maximum-coordinate time weight. A restricted norm is the infimum over extensions. Put
$$
 D_\triangle=\{(t,s):0\le s\le t\le1\},\qquad D_\square=[0,1]^2.
$$

**Lemma 17.1 (folding).** For either domain there is a linear extension $E$ such that
$$
 Ef=f\text{ on }D,\quad \operatorname{supp}Ef\subset[-1/4,5/4]^2,\quad
 \|Ef\|_\infty\le C\|f\|_{L^\infty(D)},\quad
 \|Ef\|_{\mathcal A^{1/8}}\le C\|f\|_{\mathcal A^{1/4}(D)}. \tag{17.1}
$$
The constants and operator are independent of the function, its spatial parameters, and its frequencies. Translated unit domains have the same constants.

*Proof.* A fold across a fixed line, in orthonormal coordinates, is $(x,y)\mapsto(|x|,y)$. With fixed compact cutoffs it satisfies
$$
 \|\chi H(|x|,y)\|_{\mathcal A^\sigma}
 \le C_{\sigma,\epsilon,\chi}\|H\|_{\mathcal A^{\sigma+\epsilon}},
 \qquad 0<\sigma<1,\quad\epsilon>0. \tag{17.2}
$$
To prove this on Fourier atoms, take an even cutoff $\varphi$ and set
$G(z)=\int_0^\infty\varphi(x)e^{-2\pi izx}\,dx$.
Two integrations by parts give $G(z)=\varphi(0)/(2\pi iz)+O_\varphi(|z|^{-2})$ for $|z|\ge1$. The Fourier transform of $\varphi(x)e^{2\pi ia|x|}$ is $G(\xi-a)+G(-\xi-a)$. The two unit neighborhoods of $\pm a$ contribute at most $C\langle a\rangle^\sigma$ to its weighted integral. In the intervening region $|\xi|\le2|a|+2$, the bound $|G(z)|\le C\min(1,|z|^{-1})$ gives at most $C\langle a\rangle^\sigma\log(2+|a|)$. Outside that region the leading reciprocals cancel:
$$
 |G(\xi-a)+G(-\xi-a)|\le C(1+|a|)|\xi|^{-2}.
$$
The tail integral is at most $C_\sigma\langle a\rangle^\sigma$, since $\sigma<1$. The bounded range of $a$ is included by the same estimates.

Tensor with a tangential cutoff times $e^{2\pi iby}$. Using
$\langle(\xi,\zeta)\rangle^\sigma\le C(\langle\xi\rangle^\sigma+\langle\zeta\rangle^\sigma)$, the atom norm is at most
$C_\sigma\langle(a,b)\rangle^\sigma\log(2+|a|+|b|)
 \le C_{\sigma,\epsilon}\langle(a,b)\rangle^{\sigma+\epsilon}$.
Multiplication by another fixed smooth cutoff is bounded. Integration against the input Fourier measure proves (17.2). Fixed rotations and translations do not change the conclusion.

Let $r(x)=1-|1-|x||$, and on the outer square define
$$
 F_\square(t,s)=(r(t),r(s)),\qquad
 F_\triangle(t,s)=(\max(r(t),r(s)),\min(r(t),r(s))).
$$
Here $r$ maps the outer interval to $[0,1]$ and is the identity on $[0,1]$. The square map is four folds, two per coordinate; sorting adds one fold across the diagonal. Choose $\chi(t)\chi(s)$ supported in the outer square and equal to one on the unit square. Define
$$
 Ef(t,s)=\chi(t)\chi(s)f(F_D(t,s)). \tag{17.3}
$$
This uses only values on $D$, and proves the restriction, support, and supremum assertions. For any $\mathcal A^{1/4}$ extension $H$ of $f$, it also equals $\chi(t)\chi(s)H(F_D(t,s))$. Such extensions are continuous, so equality holds on the closure of $D$. Apply (17.2) at each of the at most five folds, losing $1/40$ each time. Insert intermediate cutoffs equal to one on the images of the final compact set. The final exponent is at least $1/4-5/40=1/8$. Taking the infimum over $H$ proves (17.1). ∎

**Lemma 17.2.** If $0\le\eta<1/8$, $\|f\|_{L^\infty(D)}\le A$, and $\|f\|_{\mathcal A^{1/4}(D)}\le B$, then
$$
 \|f\|_{\mathcal A^\eta(D)}\le C_\eta A^\tau B^{1-\tau},
 \qquad \tau=\frac{1-8\eta}{9}. \tag{17.4}
$$
For $\eta\le1/16$, $\tau\ge1/18$.

*Proof.* Lemma 17.1 gives $\|Ef\|_2\le CA$ and $\|Ef\|_{\mathcal A^\sigma}\le CB$, $\sigma=1/8$. Cauchy–Schwarz on a frequency ball of radius $R\ge1$, Plancherel, and the strong norm outside it give
$$
 \|Ef\|_{\mathcal A^\eta}\le C_\eta(AR^{1+\eta}+BR^{-(\sigma-\eta)}).
$$
For $B\ge A>0$, take $R=(B/A)^{1/(1+\sigma)}$. For $B<A$, the strong norm suffices, since $B\le A^\tau B^{1-\tau}$. The zero cases follow directly. ∎

No spectral derivative, root trace, or Fourier norm of an individual face indicator is used here.


## 18. Occurrence gains for arbitrary selected positions

All profile hypotheses in this section and below mean precisely
$$
 (F_q)_q\in\mathcal P(2c_\chi C_1),\qquad F_q\text{ real},\qquad
 \sup_q\|F_q\|_{\mathcal S^{40d,40d}}\le2c_\chi C_1. \tag{18.1}
$$
The fixed $2c_\chi$ is absorbed in the exponential base. This is Addenda 2–3's class, replacing the old independently modified leaves.

An annular multiplier below is the fixed smooth function $D(u)=-u\vartheta'(u)$, or the fixed smooth annular factor supplied by the shell formula, evaluated at $\Omega/M$, $M\ge L$, and supported in $c\le|u|\le C$. Bounds also allow two annular factors or an annular and an upper factor at one linked coordinate. The total multiplicity is at most two.

**Lemma 18.1.** Lemma 16.1 and the bound (15.1), without its assertion about an unchanged principal term, hold when upper factors are replaced by these annular factors, uniformly in their scales.

*Proof.* The moment bound (14.2) uses only fixed Schwartz seminorms of the one-dimensional multiplier, also available for $D$. Its bounded supremum is absorbed once per factor. All pair and endpoint arguments in §§14–16 are unchanged. In the coherent proof the mixed derivative bounds follow by the product rule as in Lemma 11.1; the strong coefficient weight gives (16.1) without a small-error claim. On a zero-vector exclusion set an annular multiplier vanishes. ∎

Let $\mathcal O$ be an embedded regular object before new excision, as in o73 Proposition 3.1. It may have a flower–cap constraint and one original terminal flower-parent pin, counted by $b_0\in\{0,1\}$. Let $a$ selected occurrences belong to the selection of S Lemma 9.1; no selected vertex is already pinned. Put $r=b_0+a$. Original stem selections lie in the layer-$p$ root-to-port chain. Unselected stem filters may occur anywhere on that chain. Side objects are arbitrary ordinary layered regular objects.

The following bounds are first for a localized decoration expression with unit boxes and summable spatial Fourier amplitude as in T1002–1017. They are uniform in every box center, output momentum, and spatial Fourier modulation. Localization coefficients have the usual fixed exponential base. Write $G(\mathcal O)=L^{-(\gamma_1-\sqrt\eta)g(\mathcal O)}$.

**Theorem 18.2.** Assume $r\ge1$, $2m\le N^4$, $\eta\le1/16$, and $200d\eta\le\sqrt\eta$. The original annular kernel, with selected times still integrated, satisfies at fixed lattice output
$$
 \|K_{\mathcal O,H,\mathrm{ann}}\|_{X^\eta}
 \le C_{P,\chi,\vartheta}^{m+1}(C_1\delta)^m
 L^{(16d+5)r}G(\mathcal O)M_2^{-a/18}. \tag{18.2}
$$
On any prescribed unit output ball it admits an extension satisfying
$$
 \|K_{\mathcal O,H,\mathrm{ann}}\|_{X^{\eta,30d,0}}
 \le C_{P,\chi,\vartheta}^{m+1}(C_1\delta)^m
 L^{(47d+5)r}G(\mathcal O)M_2^{-a/18}. \tag{18.3}
$$
The bounds are uniform over (18.1); the exponential base is independent of $\delta$. Every incoherency unit is retained.

*Proof.* Suppose first $a\ge1$. Apply S Lemma 9.1 before taking an absolute value. Its at most $8^a$ signed faces carry $a$ reciprocals, including repeated occurrences. Proposition 14.2 applied to each face gives, with $A_0=C^{m+1}(C_1\delta)^mG(\mathcal O)$,
$$
 \|K_{\mathcal O,H,\mathrm{ann}}\|_{L^\infty(D)}
 \le A_0 L^{3r}M_2^{-a}. \tag{18.4}
$$
In fact the sharper bound $A_0L^{2b_0}M_2^{-a}$ holds in (18.4): all exceptional stem links are same-layer, and their normalization and selected reciprocals combine to $\mu^{e-a}\le\mu^{b_0}\le L^{2b_0}$, since $e\le b_0+a$ and $\mu\ge1$. We retain the weaker $L^{3r}$ for the unchanged interpolation and loss table. In particular we did not discard $\delta^{-a}$ independently of its $L^{-2\gamma a}$. The domain is the unit triangle for the same-layer paired chain, or the source rectangle for independent boundary intervals. Continuity gives the bound on its closure. The Fourier amplitude mass and $8^a$ are included in $A_0$.

For the strong estimate, keep the original integrated kernel. If $b_0=0$, Lemma 18.1 gives
$$
 \|K_{\mathcal O,H,\mathrm{ann}}\|_{X^{1/4}(D)}\le A_0L^{4d}. \tag{18.5}
$$
If $b_0=1$, use the exact terminal cut in o73 (13.1). The four ordinary components have total half-order $m-1$; apply Lemma 18.1 to each, with its assigned upper and annular factors. Their product in the three boundary variables has $X^{1/4}$ norm bounded by the product of the four norms. Apply o73 Lemma 12.1 at exponent $1/4$, without requesting pin-frequency decay. Summing the one exceptional pair in its unit boxes and restoring its two vertex normalizations costs at most $L^2$ relative to $(C_1\delta)^m$, as in Corollary 15.2. Thus
$$
 \|K_{\mathcal O,H,\mathrm{ann}}\|_{X^{1/4}(D)}\le A_0L^{16d+2}. \tag{18.6}
$$
The weighted couple bound in Lemma 16.1, inherited by Lemma 18.1, supplies summable decay in the two side-couple output momenta (or their profiles for trivial side couples), so summing the exceptional unit-box centers introduces no further $L$ power. All selected positions inside the four components are permitted; the selected vertex need not be the pin's partner. The exceptional stem link is same-layer. The four incoherency indices therefore sum to the original $g$.

Apply Lemma 17.2 to (18.4) and (18.6). The exponent is
$3r\tau+(16d+2)(1-\tau)\le3r+16d+2\le(16d+5)r$;
also $M_2^{-a\tau}\le M_2^{-a/18}$. The common $A_0$, including its full gain, remains to power one. This proves (18.2). For $a=0$, $r=1$, Corollary 15.2 is stronger.

On a chosen unit output ball there are at most $(C_dL)^d$ lattice values. At each value use the extension just constructed, multiply by a disjoint bump $\psi(L(k-k_0))$ as in o73 (13.4), and sum. The output derivatives cost $L^{30d}$; bringing the supremum inside the Fourier integral costs $L^d$. Since $r\ge1$, $31d+(16d+5)r\le(47d+5)r$. This gives (18.3), including zero data forced by a cap. ∎

**Specified signed collection.** At each selected vertex partition by the maximizer among its floor and branching-child times, assigning ties once, and take the upper endpoint minus that lower endpoint. Retain the Cartesian product of these choices for all selected vertices with the signs, restrictions, and phase substitutions of S Lemma 9.1. Each nonempty cell/endpoint choice has multiplicity one, and there are at most $8^a$. The Fourier norm above is the norm of this entire signed sum with its reciprocal product, equal to the original kernel. Only the intermediate pointwise bound separates its faces. No individual child-face Fourier estimate is asserted.

**Repeated frequency.** Two selected occurrences at coordinate $j$ contribute $|\pi\alpha_j|^{-2}$ in (18.4), and the strong bound permits their two annular factors. Interpolation gives $M_2^{-2\tau}\le M_2^{-1/9}$. The argument counts occurrences, not distinct coordinates.



## 19. The sufficient replacement for OPEN 8.2

This is the operative statement after Addenda 2 and 3. The earlier conditional coefficient interface in §§9 and 13 remains a valid implication, but is not an additional premise of this theorem.

**Theorem 8.2′ (regular-object kernel version).** Use the common real profiles (18.1), the cutoff multiplicity of S OPEN 8.2, and the order range $2m\le N^4$. In the capped flower expansion and the non-excision reduction of o75 Theorem 7.5′, replace each regular object as follows.

1. An object without a flower pin or a selected occurrence has the ordinary filtered bounds and, where the unmarked reduction uses it, the coherent principal approximation of Proposition 15.1. Its extracted reciprocals keep their original coordinates and their principal-value interpretation, as in §§2–3 and 10–11. There is no additional positive power of $L$.
2. A regular object carrying an original flower-parent pin or a selected occurrence is retained as a whole kernel. Use its local $X^{\eta,30d,0}$ extension from Theorem 18.2, with all original upper and selected annular factors. A flower–cap constraint is imposed on its lattice data. If $b_{\mathcal O}$ counts all protected incidences assigned to the object, its additional cost is at most
   $$
   C_{P,\chi,\vartheta}^{m+1}C_{P,\delta}
   L^{c_{8.2}b_{\mathcal O}},\qquad c_{8.2}=47d+5, \tag{19.1}
   $$
   relative to its ordinary $(C_1\delta)^m$ normalization and retained incoherency gain. Each selected occurrence **inside this protected regular object** supplies $M_2^{-1/18}$. Here $b_0+a\le b_{\mathcal O}$; additional special-node protection does not itself alter the kernel.
3. The selected faces inside that object are retained in the exact signed collection specified after Theorem 18.2. No assertion about an isolated face's weighted Fourier norm is needed.
4. If $g_{\mathcal O}$ is the object's original incoherency index, its bound retains
   $$
   L^{-(\gamma_1-\sqrt\eta)g_{\mathcal O}}. \tag{19.2}
   $$
   In particular the number of lost units is zero, hence at most $10b_{\mathcal O}$ as required by Addendum 3 and o75 (G-ret).

All bounds are uniform in the upper scales, selected scale, layer assignments, localized output centers, fixed external momenta, and profiles in $\mathcal P(2c_\chi C_1)$. Their per-order bases are independent of $\delta$. The final large-$L$ threshold may depend on $\delta$ and the resulting fixed exponent in the polylogarithmic order range.

The claim concerns regular objects in the initial skeleton factorization and those left intact by the stated non-excision reduction. It is not a claim about arbitrarily excised chains with new interior pins. The $M_2^{-1/18}$ conclusion applies only to selected occurrences inside protected regular objects. Inside regular objects, use S Lemma 9.1 with its reciprocal kept, as in Theorem 18.2. At skeleton and residual selected vertices, use the split in o73 Proposition 20.1, giving $M_2^{-1/18}$ per occurrence: its high adjacent-Fourier-frequency region keeps the time integration and pays the gain from a Fourier moment; its low region integrates at the total frequency $\beta_v+\xi_v$ and retains that reciprocal. This does not require retaining the raw reciprocal (9.1) at skeleton or residual vertices. The separate ladder and counting inputs remain those of S 9.2–9.3 and o75. The theorem closes the regular-object assertion of OPEN 8.2; it does not declare these other analytic assertions proved.

*Proof and sufficiency for Proposition 10.3.* The bounds are Propositions 15.1–15.2 and Theorem 18.2. To check the replacement in the assembly, use the following order of operations.

**The factorization precedes selected-time expansion.** Start with T1724–1730, formula (redkg), retaining the original upper/annular multipliers. This is an exact product of the embedded regular kernels and the skeleton expression. Assign every selected occurrence either to the unique regular factor containing its branching vertex or to the remaining skeleton. Inside each regular factor retain the whole signed collection of Theorem 18.2; equivalently, do not expand its selected time at this stage. Fubini and S Lemma 9.1 identify these two expressions exactly. The selected times in different original trees have independent interval constraints conditional on the remaining times. Thus no multiplicity or sign is changed by this choice of grouping.

**No further boundary geometry is introduced inside a protected regular factor.** The objects containing original stem vertices have the geometry of o73 Proposition 3.1: a layer-$p$ root-to-port chain, arbitrary layered side objects, and, when present, a terminal flower-parent pin. This is exactly Theorem 18.2's geometry. By Addendum 3, marked vines are left unspliced as exceptional survivors. Consequently their attached regular factors are not cut into newly pinned pieces. The protection also prevents the marked factor from participating in an unmarked LF cancellation. This is the point at which the variant uses o75 Theorem 7.5′ rather than the supplement's earlier excision plan.

**Local output norms are the norms consumed by Stage 1.** At T1959 the leaf momenta are first localized to unit balls, and the node momenta are then localized by the tree lemma at a fixed exponential cost. At T1961–1965 the regular kernels are expanded in time Fourier variables; their coefficients become the unit-ball spatial amplitudes with derivatives through $30d$ used in (redvine2). The extension (18.3) has exactly the required order of norm: the output supremum and the spatial derivatives are inside the Fourier integral. After division by its displayed bound, it is an admissible amplitude at this step. Smooth unit-ball cutoffs cost fixed constants.

For completeness, the spatial localization does not require a false global decay assertion for a capped factor. Any regular couple containing an original stem vertex contains the trivial cap, by o73 Proposition 3.1. Its output is therefore the fixed cap momentum, and is not a new freely summed leaf momentum requiring a decay weight. For every other regular couple the ordinary $30d$ output decay from Proposition 15.1 supplies the summability in T1959. Regular paired trees require no output decay; their output balls are supplied by the same tree lemma. Internal leaf localizations and their coefficients are those of T1002–1017, uniformly over (18.1). Thus the local extension is used after, not in place of, the available spatial localization. In a wholly regular component the external output momentum is fixed, so (18.2) already suffices.

**Unmarked approximation and cancellation survive.** Unmarked regular components retain the full source approximation/error reduction: §§10–11 prove the simultaneous discrete and principal-value steps with the upper filters for the actual order range, and Proposition 15.1 supplies the layered kernel bounds. The leading coherent term is the original one, with the common real profiles (18.1). Hence the unmarked tuple/reality cancellations and the unmarked vine estimates use exactly their previous leading terms and their previous error gains. The signed selected collection is estimated only in its protected factor. We do not replace any unmarked bad-vine cancellation by a bound for an individual member.

**Gains and bases.** Theorem 18.2 preserves every original incoherency unit of a protected regular object. Products of these gains therefore satisfy o75 (G-ret) with zero loss here. Unmarked vine and ladder gains are unchanged by the replacement; the separately protected survivors and ladder splits are the already accounted operations of o75. In that packet's layering count one can keep its upper bound $C_2^{22b}$, although this theorem needs none of its $10b$ regular-object allowance. The remaining $C_2$ factors are absorbed into existing gains exactly as in o75 §8(iv), never into a per-order base.

The family of protected factors has at most $b$ members, where $b\le26P$ in the main flower moment. Summing their incidences gives the loss $L^{(47d+5)b}$. Their selected gains multiply over occurrences inside protected regular objects. Combining these with the skeleton and residual selected-occurrence split of o73 Proposition 20.1 gives $M_2^{-P/9}$ for the $2P$ nonbottom selections. This assembly uses that separate proposition; the raw reciprocal argument inside regular objects is not imposed on skeleton or residual vertices. The factors $8^a$ and the selection and shell choices are the same bounded or polynomial factors already counted in S Lemmas 9.1 and 10.1 and o75 §8. This verifies precisely the regular-object replacement needed in Proposition 10.3. ∎

The profile change of Addendum 2 causes no new $L$ loss: o63 Theorem 6.3′ applies its exact common-profile extrapolation after this uniform estimate. In particular the old selected-frontier and modified-leaf marks do not reappear in (19.1).


## 20. Numerical loss table and the Addendum 3 contract

Here $r=b_0+a$ for a regular factor carrying a pin or selected occurrence. The following table lists actual bounds, not ceilings left for another packet.

| Operation in this packet | Additional $L$ exponent | Reason |
|---|---:|---|
| Upper multipliers in the integrable coefficient | $0$ | Lemma 11.1 |
| Extracted truncated reciprocals | $0$ | Proposition 2.1; Theorem 10.1 |
| Simultaneous lattice-to-continuum step, $2m\le N^4$ | $0$; error gain $\gamma_1-\varepsilon$ | Theorem 10.1, including simultaneous exclusions |
| Continuum principal-value/delta reduction | $0$; source error gain $\gamma_1-\sqrt\eta$ after interpolation | Theorem 11.3 |
| Ordinary incoherent objects with upper/annular filters | $0$; all $g$ units retained | Propositions 15.1 and 18.1 |
| Pointwise bound on all selected faces | $3r$ (sharper: $2b_0$); gain $M_2^{-a}$ | Proposition 14.2 and (18.4) |
| Strong $X^{1/4}$ bound for one ordinary factor | $4d$ | Lemma 16.1 |
| Strong bound after a terminal pin | $16d+2$ | Four factors plus one exceptional-pair sum, (18.6) |
| Bounded extension and time interpolation | no new exponent beyond the preceding two bounds | Lemmas 17.1–17.2 |
| Combined fixed-output marked bound | $(16d+5)r$; gain $M_2^{-a/18}$ | (18.2) |
| Unit-ball output extension, through $30d$ derivatives | $31d$ per protected factor, at most $31dr$ | (18.3) |
| **Total regular-object loss** | **$(47d+5)b$** | Theorem 8.2′ |
| Incoherency units lost in a protected regular factor | **$0\le10b$** | (19.2) |
| Common-profile extrapolation / removed Section 6 marks | $0$ | o63 Theorem 6.3′ |

The exceptional linked-pair sum in the pin bound is already included in $16d+2$. This proof does not additionally freeze a spectral fiber. Retaining o75's separate row 12 for other parts of the proof is a permissible overestimate, not an additional charge required here.

There are two ways the exponent contract is expressed. In o75's per-incidence convention,
$$
 c_{8.2}=47d+5\le19{,}000d^3. \tag{20.1}
$$
In the literal per-$P$ convention of Addendum 3, the main expansion has
$$
 L^{cP},\qquad c=26(47d+5)=1222d+130
                    \le19{,}000d^3 \quad(d\ge3). \tag{20.2}
$$
Thus the result meets either convention. In fact the pins and selections themselves number at most $4P$, giving the smaller $c=188d+20$; (20.2) deliberately uses the full protected-incidence allowance, including special-node protection.

Substitute (20.1) into o75 §7's aggregate table. Leaving its remaining $c_{7.3}$ contract untouched gives
$$
 B=9384d+416.01+26(c_{7.3}+47d+5)
   =10606d+546.01+26c_{7.3}. \tag{20.3}
$$
With $c_{7.3}\le19{,}000d^3$,
$$
 B+80d+\tfrac19+3
 \le494{,}000d^3+10686d+549.13
 <(100d)^3\qquad(d\ge3). \tag{20.4}
$$
This is a check of this packet's contribution and the agreed remaining ceiling. It is not a claim that OPEN 7.3 or the expansion-error packet has been completed.

**Derivative-pattern accounting.** With o75's enlarged incidence allowance $b\le30P$, applying the same regular-factor theorem where its geometry holds costs at most $(1410d+150)P$. Its budget table would then total at most
$$
 570{,}000d^3+12346d+633.2<2(100d)^3\quad(d\ge3)
$$
when the remaining pin estimates meet their ceiling. This arithmetic does not prove a new analytic rule for a root pin or for a selected vertex whose integration has already been deleted by differentiation. Such extra pin patterns belong to the separate pinned/residual estimate; neither an interior-pin coefficient theorem nor an isolated root trace is inferred here. The sufficient variant above is the one for S Proposition 10.3's original capped flower moments.

## 21. Dependency and scope check

| Input | Exact use |
|---|---|
| D23 L955–978 | Ordinary unpinned spectral representation, derivative and moment bounds; extracted factors are kept outside the coefficient |
| D23 L1013–1038, L1076–1086; T958–977 | Uniform major- and minor-frequency scalar estimates used in §§4, 10, 14 |
| T981–1017 | Linked coordinates, derivative reserve, summable localization, independent unit boxes, spatial Fourier amplitude |
| T1021–1092 | Linked pair estimates and ordinary incoherent time-Fourier extensions, with the explicit upper-filter replacements in §15 |
| T1097–1110, T1235–1244 | Coherent one-layer approximation and layered factorization |
| T2353–2379 | Time-integration kernels used for the coarse positive Fourier endpoint |
| S Lemma 8.1 | Integrable coefficient stability; supplemented, not treated as sufficient for extracted reciprocal factors |
| S Lemma 9.1 | Exact signs, domain partitions, occurrence reciprocals, and $8^a$ face count |
| o73 §§3, 12–13 | Initial flower-stem geometry, proved uniform pin operator, exact terminal cut; no unproved general coefficient assertion from that packet is assumed |
| o63 Theorem 6.3′ | Common real profile class and zero-$L$ extrapolation, replacing Section 6 marks |
| o75 Theorem 7.5′ and §§7–8 | Non-excision geometry, the exponent ceiling, and the gain-retention requirement; its remaining analytic contracts are kept separate |
| T1724–1730, T1959–1965 | Exact regular factorization and the localized time-Fourier/spatial-derivative norm actually consumed in Stage 1 |

The conclusion does not rely on the conditional mixed-norm producer assertion of §9. Theorems 10.1 and 11.3 prove the many-variable spectral steps independently; §§14–18 supply a different, direct kernel estimate for protected regular factors. This avoids the unproved inference from a centered coefficient norm to a consumed boundary modulation, and the root-trace inference refuted in o73 §15.

Sections 1–16 are retained as the requested record of the earlier partial analysis. Their provisional OPEN descriptions are superseded, for the scope just stated, by Theorem 8.2′. The original stronger assertion for arbitrary excised marked chains is not claimed. No such chains are needed by the non-excision variant in Addendum 3.



**Verification notes.** The interpolation exponent is exactly $(1-8\eta)/9$, and equals $1/18$ at $\eta=1/16$. The common factor $G(\mathcal O)$ appears in both interpolated bounds and is therefore not weakened. The five-fold extension uses a total exponent loss $5/40=1/8$. All output supremum/Fourier integral exchanges in the protected estimate are replaced by the explicit finite-lattice extension, whose full $31d$ cost is charged.

In Theorem 10.1's exclusion paragraph, a correction in $f$ coordinates combined with a minor-frequency set of size $h$ in the remaining coordinates uses coefficient derivatives of total order at most $f+qh$. The resulting factorial is bounded by $C^{n+1}(8(f+qh))!$ and then by $C^{n+1}L^{\eta_0(f+h)}$ after increasing the final threshold. Each corrected coordinate supplies $L^{-(d-2\gamma)}$, and each minor coordinate supplies $L^{-a_\gamma+\eta_0}$. Since $d-2\gamma>1\ge\gamma_1$ and $a_\gamma\ge\gamma_1$, the simultaneous expansion has the same admitted error exponent. Thus the trace argument does not presuppose a derivative-independent constant.

The displayed aggregate inequalities have been checked algebraically. The report has been checked for unmatched display delimiters and accidental control bytes. This is a Markdown proof packet; no LaTeX/PDF build, Lean build, source mutation, or mutating git operation was performed.



## 22. Revision 1 following REFEREE-82

Applied the fixes requested in REVISE.md and [REFEREE-82](REFEREE-82.md), §4, on 2026-11-07. The referee reported no failed step and passed Theorem 8.2′, subject to the statement and scope clarifications below. The audited pre-revision file had SHA-256 `7038cf6b5b1a2d3475171de7ab204381df4ce31b3ac19bd8caed1fb254b24e92`.

| Finding | Correction made in place | Effect on the theorem |
|---|---|---|
| F1 — scope, updated by 73-W | §19 and the final STATUS specify selected occurrences **inside protected regular objects**: there S Lemma 9.1 is used with its reciprocal kept (Theorem 18.2); at skeleton and residual selected vertices, o73 Proposition 20.1's split gives $M_2^{-1/18}$ per occurrence | Matches the distinct regular-object and residual mechanisms; does not assert a skeleton or residual gain from this packet alone |
| F2 — output decay and box-center summation | Lemma 16.1 states $X^{1/4,30d,30d}$ for couples and proves the weighted bound using T995–T1000, still with $L^d$ for incoherent couples; Corollary 15.2 and (18.6) explicitly sum exceptional box centers using side-couple output decay or trivial-side profile decay | No exponent change |
| F3 — coherent paired-tree norm order | Proposition 15.1 and Lemma 16.1 explain the $k$-independent majorant at each time frequency from Theorems 10.1/11.3 | Justifies $\sup_k$ inside the Fourier integral without tree output decay |
| F4 — historical status text | Headers in §1, §7.4, and §8 point to the closure in §19 and the final STATUS | Earlier partial results remain identifiable as history |
| F5 — sharper pointwise bound | After (18.4), record $\mu^{e-a}\le\mu^{b_0}\le L^{2b_0}$ | The existing larger charge and all numerical budgets are retained |
| F6 — line citations | Lemma 14.1 cites T1030; Lemma 16.1's primitive bounds and the corresponding reference in Proposition 15.1 cite T1050 | Citation correction only |

The operative loss remains $c_{8.2}=47d+5$ per protected incidence, at most $L^{(1222d+130)P}$ under $b\le26P$. All original incoherency units are retained, and the profile class remains $\mathcal P(2c_\chi C_1)$. This revision does not claim a general marked spectral-coefficient decomposition, change the signed face collections, or enlarge the pin geometry of Theorem 8.2′.

Verification: checked the edits against F1–F6 and T995–T1000, checked the corrected scalar-sum and primitive-bound citations, and checked display delimiters and control bytes. No source outside this packet was changed; no Lean or LaTeX build was needed for these Markdown proof corrections.



### 22.1 Addendum: REFEREE-73 fix 73-W

Applied the REVISE.md addendum to §19 and row F1 above, and synchronized the final STATUS. The regular-object argument keeps the raw reciprocal of S Lemma 9.1 in Theorem 18.2. The skeleton/residual argument instead uses o73 Proposition 20.1: on $|\xi_v|\ge|\beta_v|/2$ it keeps the selected time integral and extracts a $1/18$ Fourier moment; on the complementary region it integrates with reciprocal $(\pi i(\beta_v+\xi_v))^{-1}$. Both regions give $M_2^{-1/18}$ per occurrence. The Fourier-level faces are not identified term by term with the raw faces of S Lemma 9.1.

Checked this wording against o73 (20.4)–(20.5) and its paragraph following Proposition 20.1. This is an assembly-reference correction, not a new premise in the proof of Theorem 8.2′: that proof still uses only the earlier o73 geometry and pin results listed in §21. The regular-object loss, gain retention, and numerical budget are unchanged.

STATUS: CLOSED WITH VARIANT (Revision 1 and addendum, §22, apply REFEREE-82 F1–F6 and REFEREE-73 fix 73-W; see §19, Theorem 8.2′: whole protected regular kernels and full signed selected-face collections, uniform over real profiles in 𝒫(2cχC₁), cost L^{(47d+5)b} ≤ L^{(1222d+130)P}, zero lost incoherency units, and M₂^{-1/18} per selected occurrence INSIDE a protected regular object; inside regular objects S Lemma 9.1 keeps its reciprocal (Theorem 18.2), while skeleton and residual selected vertices use the o73 Proposition 20.1 split for M₂^{-1/18} per occurrence; budget §20).
