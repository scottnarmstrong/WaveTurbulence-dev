# The GIT20 trilinear estimate in general dimension

Date: 2026-11-03. Scope: pen-and-paper analysis of the estimate (schappend8) that Deng–Hani
(arXiv:2311.10082, Appendix C, TeX L2487–L2528) cite from Germain–Ionescu–Tran (GIT20,
arXiv:1711.05587, Lemmas 4.1–4.3/4.4, Remark 2.6 at Kin8.tex L592–L594).

## Verdict

| Claim | Status |
|---|---|
| (schappend8) for $\mathcal K_0,\dots,\mathcal K_3$, every $d\ge 3$, every $s>d/2-1$ | **Proved below (Theorem 7)**, elementary, no Fourier analysis |
| Failure for $s<d/2-1$ (each $j$) | Proved (scaling, §8.1) |
| Failure at $s=d/2-1$ for $j=1,2,3$ | Proved (divergent hyperplane integrals, §8.2) |
| Endpoint $s=d/2-1$ for $j=0$ | Not determined; not needed |
| $d=2$ (GIT Remark 2.6 asserts $d\ge2$) | Loss-operator bound fails for every $s$ (§8.3); irrelevant for DH ($d\ge3$) |
| The specific step of GIT's proof (radial Cauchy–Schwarz before (bil7)) in $d\ge4$ | Fails, as the prover found ($\sup_\theta A_p(\theta)\asymp|p|^{d-3}$). The inequality (bil7) itself is still **true** in every $d\ge3$ (§9) |
| Blow-up criterion of Prop. `wkelwp`, all $s>d/2-1$, $d\ge 3$ | Follows from Theorem 7 by DH Appendix C verbatim (§10) |
| Published $d$-dimensional proof | None found (§11) |

**Recommendation: keep the frozen statement "for every $s>d/2-1$" (with $d\ge3$).** No restriction is needed.

---

## 0. Conventions

$\langle k\rangle=(1+|k|^2)^{1/2}$, $\|f\|_{Z_s}=\|\langle k\rangle^s f\|_{L^2(\mathbb R^d)}$, $S=S^{d-1}$ with surface
measure $d\theta$. For a linear subspace $V$, $\sigma_V$ is Lebesgue (surface) measure on $V$. For
$\varphi\in S$, $\sigma_\varphi$ is the $(d-2)$-dimensional surface measure on the great sphere $S\cap\varphi^\perp$.

**Resonant measure.** As in DH (schappend5) and the Lean definition, for Borel $F\ge 0$ on $\mathbb R^d\times\mathbb R^d$,
$$\iint F(\ell_1,\ell_3)\,\delta(2\langle\ell_1,\ell_3\rangle)\,d\ell_1 d\ell_3
 :=\int_{\mathbb R^d}\frac{1}{2|\ell_1|}\int_{\ell_1^\perp}F(\ell_1,\ell_3)\,d\sigma_{\ell_1^\perp}(\ell_3)\,d\ell_1\in[0,\infty].$$
($\delta(-2\langle\cdot,\cdot\rangle)$ is the same thing.) Then, for $\varphi_i\ge0$,
$$\mathcal K_0(\varphi_1,\varphi_2,\varphi_3)(k)=\iint \varphi_1(k+\ell_1)\varphi_2(k+\ell_1+\ell_3)\varphi_3(k+\ell_3)\,\delta(2\ell_1\!\cdot\!\ell_3),$$
and, writing out the loss terms (DH (schappend2)–(schappend4)) in the same variables,
$$\mathcal K_1=\varphi_1(k)\,Q_1(\varphi_2,\varphi_3)(k),\quad
\mathcal K_2=\varphi_2(k)\,Q_2(\varphi_1,\varphi_3)(k),\quad
\mathcal K_3=\varphi_3(k)\,Q_1(\varphi_2,\varphi_1)(k),$$
$$Q_1(g,h)(k):=\iint g(k+\ell_1+\ell_3)\,h(k+\ell_3)\,\delta(2\ell_1\!\cdot\!\ell_3),\qquad
Q_2(g,h)(k):=\iint g(k+\ell_1)\,h(k+\ell_3)\,\delta(2\ell_1\!\cdot\!\ell_3).$$
(For $\mathcal K_3$ use the $\ell_1\leftrightarrow\ell_3$ symmetry of Lemma 1.) In GIT's notation $Q_2$ is their
$Q_2$ (bil1) and $Q_1$ is their $Q_3$ (bil30); $\mathcal K_0$ is their $\mathcal T_1$.

**Reduction to nonnegative functions.** Every $\mathcal K_j$ is a positive trilinear operator, and
$|\mathcal K_j(\varphi_1,\varphi_2,\varphi_3)|\le\mathcal K_j(|\varphi_1|,|\varphi_2|,|\varphi_3|)$ wherever the right side is
finite. So it suffices to prove all bounds for Borel $\varphi_i\ge0$, with integrals in $[0,\infty]$.
Finiteness of the right-hand side then gives absolute convergence of the signed integrals:
for $j\ge1$ at every $k$, and for $j=0$ at a.e. $k$.

Throughout, $d\ge3$ and $s>d/2-1$, i.e. $2s>d-2$. Constants depend only on $(d,s)$.

---

## 1. Symmetry of the resonant measure

**Lemma 1.** Let $d\ge2$. For every Borel $F\ge0$ on $\mathbb R^d\times\mathbb R^d$,
$$\int_{\mathbb R^d}\frac1{|a|}\int_{a^\perp}F(a,b)\,d\sigma(b)\,da=\int_{\mathbb R^d}\frac1{|b|}\int_{b^\perp}F(a,b)\,d\sigma(a)\,db .$$

*Proof.* Each side is $\int F\,d\mu_i$ for a Borel measure $\mu_i$ on $\mathbb R^{2d}$. Each $\mu_i$ is locally finite, since
$\int_{|a|\le L}|a|^{-1}da<\infty$ for $d\ge2$. Fix $F\in C_c$ supported in $\{|a|,|b|\le L\}$. For $a\neq0$ write
$b=t\hat a+y$ with $y\in a^\perp$, so $db=dt\,d\sigma(y)$, and set $\Phi_a(t)=\int_{a^\perp}F(a,t\hat a+y)\,d\sigma(y)$. Then $\Phi_a$ is
continuous in $t$ (uniform continuity of $F$) and $|\Phi_a|\le\|F\|_\infty|B^{d-1}_L|$. Hence
$$\frac1{2\varepsilon}\int_{|a\cdot b|<\varepsilon}F(a,b)\,db=\frac1{|a|}\cdot\frac{|a|}{2\varepsilon}\int_{|t|<\varepsilon/|a|}\Phi_a(t)\,dt\ \xrightarrow[\varepsilon\to0]{}\ \frac{\Phi_a(0)}{|a|},$$
dominated by $\|F\|_\infty|B^{d-1}_L|\,|a|^{-1}\mathbf 1_{|a|\le L}\in L^1(da)$. By dominated convergence,
$\lim_{\varepsilon\to0}(2\varepsilon)^{-1}\iint_{|a\cdot b|<\varepsilon}F=\int F\,d\mu_1$. The set $\{|a\cdot b|<\varepsilon\}$ and Lebesgue
measure are invariant under $(a,b)\mapsto(b,a)$, so the same limit equals $\int F\,d\mu_2$. Two locally finite Borel
measures on $\mathbb R^{2d}$ that agree on $C_c$ are equal (uniqueness in the Riesz representation theorem). $\square$

**Corollary 2 (polar form).** For Borel $F\ge0$,
$$\int\frac1{|a|}\int_{a^\perp}F\,d\sigma\,da=\int_S\int_{S\cap\varphi^\perp}\int_0^\infty\!\!\int_0^\infty F(\rho\varphi,r\theta)\,\rho^{d-2}r^{d-2}\,d\rho\,dr\,d\sigma_\varphi(\theta)\,d\varphi .$$
Write $d\nu(\varphi,\theta)=d\sigma_\varphi(\theta)\,d\varphi$. Then $\nu$ is symmetric:
$\int_S\int_{S\cap\varphi^\perp}G(\varphi,\theta)\,d\sigma_\varphi(\theta)\,d\varphi=\int_S\int_{S\cap\theta^\perp}G(\varphi,\theta)\,d\sigma_\theta(\varphi)\,d\theta$.

*Proof.* The formula is polar coordinates $a=\rho\varphi$ in $\mathbb R^d$, followed by polar coordinates $b=r\theta$ in the
$(d-1)$-space $\varphi^\perp$. For the symmetry, apply Lemma 1 to $F(a,b)=G(\hat a,\hat b)\eta(|a|)\eta(|b|)$ with $\eta\ge0$
and $\int_0^\infty\eta(\rho)\rho^{d-2}d\rho=1$. $\square$

## 2. The radial weight $A_k$

For $k\in\mathbb R^d$ and $\theta\in S$ set
$$A_k(\theta):=\int_0^\infty\langle k+\rho\theta\rangle^{-2s}\rho^{d-3}\,d\rho ,$$
which is finite since $d\ge3$ and $2s>d-2$. For $f\ge0$ set
$\Gamma^k_f(\theta)^2:=\int_0^\infty f(k+\rho\theta)^2\langle k+\rho\theta\rangle^{2s}\rho^{d-1}d\rho$, so that
$\int_S(\Gamma^k_f)^2\,d\theta=\|f\|_{Z_s}^2$ (polar coordinates about $k$).

**Lemma 3 (radial Cauchy–Schwarz).** $\displaystyle\int_0^\infty f(k+\rho\theta)\rho^{d-2}d\rho\le\Gamma^k_f(\theta)\,A_k(\theta)^{1/2}.$
*Proof.* Split $\rho^{d-2}=\big(\langle\cdot\rangle^{s}\rho^{(d-1)/2}\big)\big(\langle\cdot\rangle^{-s}\rho^{(d-3)/2}\big)$ and apply Cauchy–Schwarz. $\square$

*What happens in $d\ge4$.* Write $R=|k|\ge1$ and let $\alpha$ be the angle between $\theta$ and $-\hat k$. Splitting at
$\rho=2R$ gives the bound and the matching lower bound
$$A_k(\theta)\le C\big(1+R^{d-3}\langle R\alpha\rangle^{1-2s}\mathbf 1_{\alpha<\pi/2}\big).$$
So $\sup_\theta A_k(\theta)\asymp R^{d-3}$, attained on a cap of radius $1/R$ around $-\hat k$. In $d=3$, $A_k\le C$ uniformly,
and that is the only place GIT's proof uses $d=3$. The cure is to integrate $A_k$ against the angular kernel
rather than take its supremum:

**Lemma 4 (two uniform integrals).** Let $d\ge3$ and $2s>d-2$. Then
$$M_2:=\sup_{k\in\mathbb R^d,\ \varphi\in S}\int_{S\cap\varphi^\perp}A_k(\theta)\,d\sigma_\varphi(\theta)<\infty,\qquad
M_1:=\sup_{k\in\mathbb R^d,\ \theta\in S}\int_S\frac{A_k(\theta')}{|\sin\angle(\theta,\theta')|}\,d\theta'<\infty .$$

*Proof.* (a) Use polar coordinates in the $(d-1)$-space $\varphi^\perp$. There $\rho^{d-3}d\rho\,d\sigma_\varphi=|u|^{-1}d\sigma_{\varphi^\perp}(u)$, so
$$\int_{S\cap\varphi^\perp}A_k\,d\sigma_\varphi=\int_{\varphi^\perp}\langle k+u\rangle^{-2s}|u|^{-1}du\le\int_{\mathbb R^{d-1}}\langle k'+u\rangle^{-2s}|u|^{-1}du ,$$
with $k'=P_{\varphi^\perp}k$, because $|k+u|\ge|k'+u|$. The part $|u|<1$ is at most $\int_{|u|<1}|u|^{-1}<\infty$ since $d-1\ge2$. For the
part $|u|\ge1$ use Hölder with $|u|^{-1}\mathbf 1_{|u|\ge1}\in L^p(\mathbb R^{d-1})$ for $p>d-1$ and $\langle u\rangle^{-2s}\in L^{p'}(\mathbb R^{d-1})$
for $p'>(d-1)/(2s)$. Since $2s>d-2$ we have $(d-1)/(2s)<(d-1)/(d-2)=(d-1)'$, so some $p'$ satisfies both conditions. The bound is
uniform in $k'$ by translation invariance.

(b) Use polar coordinates in $\mathbb R^d$: $|u|^{2}|\sin\angle(\hat u,\theta)|=|u|\,|u_\perp|$ with $u_\perp=u-(u\cdot\theta)\theta$, so
$$\int_S\frac{A_k(\theta')}{|\sin\angle(\theta,\theta')|}d\theta'=\int_{\mathbb R^d}\frac{\langle k+u\rangle^{-2s}}{|u|\,|u_\perp|}\,du .$$
Coordinates $(u\cdot\theta,|u_\perp|)=(R\cos\psi,R\sin\psi)$ give $du=|S^{d-2}|R^{d-1}\sin^{d-2}\psi\,dR\,d\psi$. Hence
$\int_{|u|<1}|u|^{-1}|u_\perp|^{-1}<\infty$ (because $d\ge3$), and $f_2:=|u|^{-1}|u_\perp|^{-1}\mathbf 1_{|u|\ge1}\in L^p(\mathbb R^d)$ iff $d/2<p<d-1$.
We also need $\langle u\rangle^{-2s}\in L^{p'}$, i.e. $p'>d/(2s)$. Since $d/(2s)<d/(d-2)=(d/2)'$, the interval
$p'\in\big(\max(d/(2s),(d-1)/(d-2)),\,d/(d-2)\big)$ is nonempty. Hölder then gives a bound uniform in $k$ and $\theta$. $\square$

*Numerical sanity check* (not part of the proof): the reduced integral in (b) with $k=-R\theta$ (the worst alignment,
where the weight concentrates on the singular line) at $s=d/2-1+0.05$ gives
$d=4$: 16.1, 15.8, 13.4, 10.0, 7.2, 4.9 for $R=0,1,10,10^2,10^3,10^4$, and the same decreasing behaviour for
$d=5$ and $d=7$. By contrast, GIT's $\sup_\theta A_k$ grows like $R^{d-3}$.

## 3. The loss operator $Q_2$ (GIT Lemma 4.2, $\mathcal K_2$)

**Proposition 5.** For $g,h\ge0$ and every $k$: $\ Q_2(g,h)(k)\le \tfrac12 M_2\,\|g\|_{Z_s}\|h\|_{Z_s}$.

*Proof.* By Corollary 2 with $F(a,b)=g(k+a)h(k+b)$,
$$Q_2(g,h)(k)=\tfrac12\iint\mathcal G(\varphi)\mathcal H(\theta)\,d\nu(\varphi,\theta),\qquad
\mathcal G(\varphi)=\int_0^\infty g(k+\rho\varphi)\rho^{d-2}d\rho,\ \ \mathcal H(\theta)=\int_0^\infty h(k+r\theta)r^{d-2}dr.$$
By Lemma 3 and AM–GM, for any $\lambda>0$,
$$\mathcal G(\varphi)\mathcal H(\theta)\le\big[\Gamma_g(\varphi)A_k(\theta)^{1/2}\big]\big[\Gamma_h(\theta)A_k(\varphi)^{1/2}\big]\le\tfrac12\big(\lambda^2\Gamma_g(\varphi)^2A_k(\theta)+\lambda^{-2}\Gamma_h(\theta)^2A_k(\varphi)\big).$$
Integrate against $\nu$. The first term is $\le M_2\|g\|_{Z_s}^2$ by direct disintegration. The second is $\le M_2\|h\|_{Z_s}^2$ after the swap
in Corollary 2. Then optimize over $\lambda$. $\square$

## 4. The loss operator $Q_1$ (GIT Lemma 4.4/(bil33), $\mathcal K_1,\mathcal K_3$)

**Proposition 6.** For $g,h\ge0$ and every $k$:
$\ Q_1(g,h)(k)\le\tfrac12(c_{d,s}M_1)^{1/2}\|g\|_{Z_s}\|h\|_{Z_s}$, where $c_{d,s}=\int_{\mathbb R^{d-2}}\langle z\rangle^{-2s}dz<\infty$ (finite because $2s>d-2$).

*Proof.* By Lemma 1 (take $\ell_3$ as base variable), then polar coordinates $\ell_3=t\theta$ and Fubini on
$\mathbb R^d=\mathbb R\theta\oplus\theta^\perp$:
$$Q_1(g,h)(k)=\tfrac12\int_S\int_0^\infty h(k+t\theta)t^{d-2}\int_{\theta^\perp}g(k+t\theta+a)\,d\sigma(a)\,dt\,d\theta=\int_{\mathbb R^d}g(k+w)\,\mathcal Sh(w)\,dw,$$
$$\mathcal Sh(w):=\tfrac12\int_S h\big(k+(w\cdot\theta)\theta\big)\,(w\cdot\theta)_+^{d-2}\,d\theta .$$
(Geometrically, $\mathcal Sh(w)$ averages $h$ over the Thales sphere with diameter $[k,k+w]$.) By Cauchy–Schwarz,
$Q_1\le\|g\|_{Z_s}N$ with $N^2=\int\langle k+w\rangle^{-2s}\mathcal Sh(w)^2dw$. Expand the square and use Tonelli:
$$N^2=\tfrac14\int_S\!\int_S\int_{\mathbb R^d}\langle k+w\rangle^{-2s}h(k+(w\cdot\theta)\theta)h(k+(w\cdot\theta')\theta')(w\cdot\theta)_+^{d-2}(w\cdot\theta')_+^{d-2}\,dw\,d\theta\,d\theta'.$$
Fix $\theta'\ne\pm\theta$ (a null set is excluded) and let $V=\{\theta,\theta'\}^\perp$. The linear map $w\mapsto(w\cdot\theta,w\cdot\theta',P_Vw)$ has
Jacobian $|\sin\angle(\theta,\theta')|$. For fixed $(t,t')$, $w$ runs over an affine translate of $V$, and
$\int_V\langle k+x+v\rangle^{-2s}dv\le\int_V\langle P_V(k+x)+v\rangle^{-2s}dv=c_{d,s}$. Hence
$$N^2\le\tfrac{c_{d,s}}4\iint\frac{\mathcal H(\theta)\mathcal H(\theta')}{|\sin\angle(\theta,\theta')|}\,d\theta\,d\theta'
\le\tfrac{c_{d,s}}4\iint\frac{\Gamma_h(\theta)^2A_k(\theta')}{|\sin\angle(\theta,\theta')|}\,d\theta\,d\theta'\le\tfrac{c_{d,s}}4M_1\|h\|_{Z_s}^2 .$$
The middle step uses Lemma 3, $\Gamma(\theta)a(\theta)\Gamma(\theta')a(\theta')\le\frac12(\Gamma(\theta)^2a(\theta')^2+\Gamma(\theta')^2a(\theta)^2)$ with $a=A_k^{1/2}$, and the symmetry of the kernel. $\square$

## 5. The gain operator $\mathcal K_0$ (GIT Lemma 4.1)

**Lemma (weight transfer).** If $\ell_1\perp\ell_3$ then $|k+\ell_1|^2+|k+\ell_3|^2=|k|^2+|k+\ell_1+\ell_3|^2$. Hence on the support
$\langle k\rangle^2\le\langle k+\ell_1\rangle^2+\langle k+\ell_3\rangle^2$, and so $\langle k\rangle^s\le2^{s/2}(\langle k+\ell_1\rangle^s+\langle k+\ell_3\rangle^s)$.

**Proposition 7a.** For $F_1,F_4,f_2,f_3\ge0$, with $C_Q:=\tfrac12(c_{d,s}M_1)^{1/2}$:
$$\Lambda:=\int F_4(k)\,\mathcal K_0(F_1,f_2,f_3)(k)\,dk\le C_Q\,\|F_1\|_{L^2}\|F_4\|_{L^2}\|f_2\|_{Z_s}\|f_3\|_{Z_s}.$$

*Proof.* Write $\Lambda=\int\!\int\frac1{2|a|}\int_{a^\perp}F_4(k)F_1(k+a)f_2(k+a+b)f_3(k+b)\,d\sigma(b)\,da\,dk$ and bound
$F_4(k)F_1(k+a)\le\frac12(\lambda^2F_1(k+a)^2+\lambda^{-2}F_4(k)^2)$.
* The $F_4^2$ term equals $\int F_4^2\,Q_1(f_2,f_3)\,dk\le C_Q\|F_4\|^2\|f_2\|_{Z_s}\|f_3\|_{Z_s}$ by Proposition 6.
* For the $F_1^2$ term, substitute $k=k_1-a$ (translation for fixed $a$) and then $a\mapsto-a$ (which preserves $a^\perp$). It becomes
  $\int F_1(k_1)^2\,Q_1(f_3,f_2)(k_1)\,dk_1\le C_Q\|F_1\|^2\|f_2\|_{Z_s}\|f_3\|_{Z_s}$.

Optimize over $\lambda$. (This is a Schur test. It replaces GIT's Fourier/Strichartz argument.) $\square$

By $L^2$ duality, $\|\mathcal K_0(F_1,f_2,f_3)\|_{L^2}\le C_Q\|F_1\|_{L^2}\|f_2\|_{Z_s}\|f_3\|_{Z_s}$. Now combine weight transfer,
positivity, and $\mathcal K_0(\varphi_1,\varphi_2,F)=\mathcal K_0(F,\varphi_2,\varphi_1)$ (Lemma 1):
$$\|\mathcal K_0(\varphi_1,\varphi_2,\varphi_3)\|_{Z_s}\le2^{s/2}\big(\|\mathcal K_0(\langle\cdot\rangle^s\varphi_1,\varphi_2,\varphi_3)\|_{L^2}+\|\mathcal K_0(\langle\cdot\rangle^s\varphi_3,\varphi_2,\varphi_1)\|_{L^2}\big)\le2^{1+s/2}C_Q\prod_i\|\varphi_i\|_{Z_s}.$$

## 6–7. Main theorem

**Theorem 7.** Let $d\ge3$ and $s>d/2-1$. For all measurable $\varphi_1,\varphi_2,\varphi_3$ with finite $Z_s$ norms and each $j\in\{0,1,2,3\}$,
$$\|\mathcal K_j(\varphi_1,\varphi_2,\varphi_3)\|_{Z_s}\le C(d,s)\,\|\varphi_1\|_{Z_s}\|\varphi_2\|_{Z_s}\|\varphi_3\|_{Z_s}.$$
The constants are: $j=0$: $2^{1+s/2}C_Q$; $j=1,3$: $C_Q$; $j=2$: $M_2/2$.

*Proof.* Use §0 to reduce to nonnegative functions. For $j=0$ use §5. For $j=1,3$: $\|\langle k\rangle^s\varphi_1Q_1(\varphi_2,\varphi_3)\|_{L^2}\le\|\varphi_1\|_{Z_s}\sup_kQ_1$
together with Proposition 6. For $j=2$ use Proposition 5 the same way. $\square$

The $Z_{s,m}$ version DH need (L2526) follows from Theorem 7, the Leibniz rule (schappend6), and the multiplier identity
(schappend7), exactly as DH say.

**What the proof uses:** Tonelli, polar coordinates, one linear change of variables, Hölder, Cauchy–Schwarz/AM–GM, and the
weak-limit identity of Lemma 1. There is no Fourier transform, Strichartz estimate, oscillatory integral or $\varepsilon$-regularization of $\delta$.
That makes it suitable for formalization. Lemma 1 is the only measure-theoretic input; it is unnecessary if the Lean
definition of the resonant measure is already shown to be symmetric.

## 8. Sharpness

**8.1 ($s<d/2-1$, every $j$).** In the $\ell$-parametrization, $\mathcal K_j(f(\cdot/\lambda))(k)=\lambda^{2d-2}\mathcal K_j(f)(k/\lambda)$.
Take $f$ Gaussian, so that $\mathcal K_j(f,f,f)>0$. As $\lambda\to\infty$, $\|f(\cdot/\lambda)\|_{Z_s}\sim\lambda^{s+d/2}\||k|^sf\|_{L^2}$ and
$\|\mathcal K_j(f_\lambda)\|_{Z_s}\ge\lambda^{2d-2+d/2+s}\||k|^s\mathcal K_j(f)\|_{L^2}$. The ratio grows like $\lambda^{d-2-2s}\to\infty$.

**8.2 ($s=d/2-1$, $j=1,2,3$).** Let $h(x)=\langle x\rangle^{-(d-1)}\log^{-1}(2+|x|)$. Then $\|h\|_{Z_{d/2-1}}^2=\int\langle x\rangle^{-d}\log^{-2}(2+|x|)\,dx<\infty$,
but every hyperplane integral of $h$ is $+\infty$ (it behaves like $\int^\infty r^{-1}\log^{-1}r\,dr$). $Q_1(g,h)(k)$ contains the hyperplane integrals of
its first argument, and $Q_2(g,h)(k)$ those of its second. So $Q_1(h,\psi)\equiv\infty$ and $Q_2(\psi,h)\equiv\infty$ for any $\psi\ge0$,
$\psi\not\equiv0$. Hence $\mathcal K_1,\mathcal K_2,\mathcal K_3$ are infinite on a set of positive measure. The range $s>d/2-1$ is therefore sharp.
For $j=0$ at $s=d/2-1$: not determined (DH only use $s>d/2-1$).

**8.3 ($d=2$, side remark).** GIT Remark 2.6 claims $d\ge2$. Take $g(u)=|u|^{-1}\log^{-1}(1/|u|)\mathbf 1_{0<|u|<1/2}\in L^2(\mathbb R^2)$, which is compactly supported
and lower semicontinuous with $g(0)=\infty$. Its radial integrals $\int_0 g(\rho\varphi)\,d\rho$ diverge, so $Q_2(g,g)(0)=\infty$. By Fatou,
$Q_2(g,g)(k)\to\infty$ as $k\to0$. Then $\varphi_2=\mathbf 1_{B_\varepsilon}$ shows $\|\mathcal K_2(g,\varphi_2,g)\|_{Z_s}/\prod\|\cdot\|_{Z_s}$ is unbounded for every $s$.
So in $d=2$ the individual loss-operator bound fails. Whether the full combination does is not addressed. This does not concern DH, who
take $d\ge3$ (Thm 1.1, L314; Lean `hd : 3 ≤ d`).

## 9. Where GIT's argument breaks, and the minimal patch

* **Lemma 4.3(ii) (bil20)** holds in every $d$ when $2s>d-2$. Rotate, integrate $x_1,x_2$ against the two slabs, and the remaining
  $\mathbb R^{d-2}$ integral is $\le c_{d,s}$. This confirms the prover.
* **(bil7) in $d\ge4$.** GIT bound $\int_0^\infty g(r\theta)\langle r\theta+p\rangle^{-s}r^{d-2}dr$ by $\tilde g(\theta)\cdot\sup_\theta A_p(\theta)^{1/2}$. That
  supremum is $\asymp|p|^{d-3}$, so the step fails, as the prover found. **But (bil7) itself is true in every $d\ge3$, for all $p,p'$.**
  Keep $A_p(\theta)^{1/2}$ inside, apply AM–GM so that $A_p$ sits on the *integrated* angular variable, and use Lemma 4(b)
  (note $|\theta-\theta'|\ge|\sin\angle(\theta,\theta')|$). With this one-line replacement, GIT's proofs of Lemmas 4.2 and 4.4 go through verbatim in $d\ge3$.
* **Lemma 4.1 kernel bound (ma13)** is true in $d\ge3$. Take a Littlewood–Paley piece $K_N$ ($N\ge1$ dyadic) of
  $K(y,t)=\int\langle p\rangle^{-2s}e^{-ip\cdot y-it|p|^2}dp$. It satisfies $|K_N|\lesssim N^{d-2s}$, and also
  $|K_N|\le(4\pi|t|)^{-d/2}\|\mathcal F^{-1}[\psi(\cdot/N)\langle\cdot\rangle^{-2s}]\|_{L^1}\lesssim N^{-2s}|t|^{-d/2}$, because the free Schrödinger kernel has modulus
  $(4\pi|t|)^{-d/2}$ and the $L^1$ norm of the inverse Fourier transform of a rescaled bump is scale invariant. Summing over $N$:
  $|K|\lesssim|t|^{-(d-2s)/2}$ for $|t|\le1$ and $|K|\lesssim|t|^{-d/2}$ for $|t|\ge1$. This lies in $L^1_t$ iff $d-2s<2$ and $d>2$, which gives
  $|K|\lesssim|t|^{-1+\delta}\langle t\rangle^{-2\delta}$ with $\delta=\min(s-\tfrac{d-2}2,\tfrac{d-2}4)$. Equivalently: the Keel–Tao endpoint
  $L^2_tL^{2d/(d-2)}_x$ plus Sobolev $W^{s,2d/(d-2)}\subset L^\infty$ for $s>d/2-1$. GIT's Fourier route is therefore also valid. It still needs a
  regularization of $\delta$ to be made rigorous, which the Schur route of §5 avoids.

## 10. Question 2: the blow-up criterion

Theorem 7 supplies (schappend8) for all $d\ge3$ and $s>d/2-1$. I checked DH Appendix C step by step, and nothing else in it depends on $d$:
Picard local well-posedness in $Z_s$ with $T\gtrsim\|\varphi_0\|_{Z_s}^{-2}$; the $Z_{s,m}$ estimates via (schappend6)–(schappend7); the Gronwall
induction (schappend10); and the equality of all $\tau_{\max}^{(s,m)}$ (Schwartz class = $\bigcap Z_{s,m}$).

The genuine limit $\lim_{\tau\to\tau_{\max}}\|\varphi(\tau)\|_{Z_s}=\infty$, not just limsup, follows from the local existence time. If
$\|\varphi(\tau_n)\|_{Z_s}\le R$ along $\tau_n\to\tau_{\max}<\infty$, the $Z_s$ solution from $\tau_n$ lives until $\tau_n+cR^{-2}>\tau_{\max}$ and stays
Schwartz by (schappend10). That is a contradiction. This is exactly the shape of the frozen Lean clause ($\forall M\,\exists\tau_0\ldots$).

On the "other route" question: it is moot. Note also that a weaker estimate, valid only for $s\ge s_0$, would give the criterion only for
$s\ge s_0$. The statement for small $s$ (bounded $Z_s$ prevents blow-up) needs a $Z_s$-level estimate such as a tame bound
$\|\mathcal K(f,f,g)\|_{Z_{s'}}\lesssim\|f\|_{Z_s}^2\|g\|_{Z_{s'}}$, which is no easier. Persistence or interpolation alone gives no cheap substitute.

## 11. Question 3: literature

I found no published proof for general $d$ in a limited web search on 2026-11-03.
* GIT20 Remark 2.6 asserts $d\ge2$, $s>(d-2)/2$ without proof ([arXiv:1711.05587](https://arxiv.org/abs/1711.05587)). As §8.3 shows, the $d=2$ case is false at least for the individual loss operator.
* Ampatzoglou–Léger, *On the optimal local well-posedness of the wave kinetic equation in $L^r$* ([arXiv:2511.15587](https://arxiv.org/abs/2511.15587)), covers weighted $L^r$ with $2\le r\le\infty$ but only in 3D. It recovers GIT at $r=2$ with weight $1/2+\delta$.
* Other hits concern different settings: inhomogeneous or $L^\infty$ ([arXiv:2405.03984](https://arxiv.org/abs/2405.03984)), gravity water waves ([arXiv:2603.10882](https://arxiv.org/abs/2603.10882)), and 2D Boussinesq ([arXiv:2608.15340](https://arxiv.org/abs/2608.15340)).

## 12. Recommendation for the frozen statement

**Keep "for every $s>d/2-1$" with $d\ge3$.** The range is exactly right: it is proved for all $s>d/2-1$ and fails below it, and at the
endpoint for the loss terms. For the Lean proof of `wkelwp`, the dependency list is:
1. Lemma 1 (symmetry of the resonant measure).
2. Lemma 3 together with Lemma 4 (two Hölder bounds).
3. Propositions 5 and 6.
4. Proposition 7a with weight transfer.
5. Theorem 7, then the $Z_{s,m}$ version, then DH Appendix C.

The GIT20 citation should be replaced by Theorem 7 above, or by GIT20 plus the §9 patch.
