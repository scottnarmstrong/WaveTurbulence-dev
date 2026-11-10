# RESOLUTION — OPEN 6.3 (marked grouped estimates and external decay)

Packet o63 (FLOWER-OPEN), for wt-orch, 2026-11-07.

**Pinned inputs** (sha256 verified at first read):

- SUPPLEMENT-v1.md `ddd81fe1238e7c51379a69981b4d10aa68690ced46d0fc1b115200fc0c3774d7`. "S n.m" refers to its sections and lemmas.
- TARGET `WKE-Longer_times_Final_arXiv.tex` `493eef6b7dec448bc5f9f1c3974c0cad7a85eca9bc428f5b35e968aad76727cb`. "T…" refers to its lines.
- COMMON.md `a165bad5…`, o63/BRIEF.md `fb5aaa77…`.
- Revision 2 also uses: ref/REFEREE.md `c31ee38a…` (§3 on (10.3); §4.1 OPEN 6.3 (ii)–(iii); §4.2 M1, M3) and o102/RESOLUTION.md `772bac47…` (step 2 allocation).

No DH21/DH23 statement is used in the proof below. They enter only through the downstream items that this resolution feeds (§5).

---

## 0. Result

**OPEN 6.3 is closed with a variant: Theorem 6.3′ (§2), with its sufficiency for the assembly in Proposition 10.3′ (§5).**

Both gains requested in OPEN 6.3, $M_1^{-80dP}$ and $\langle k-\zeta k'\rangle^{-4\Lambda P}$, are extracted by an **exact identity**. It writes the weighted order-$n$ family as a fixed linear combination of $n+1$ copies of the **same unmarked family**. In each copy, every leaf pair carries **one common real profile tuple**:

$$
G^{(r)}_q=F_q\,w_{\rho,z_r},\qquad w_{\rho,z}(u)=\chi(u/\rho)+z\bigl(1-\chi(u/\rho)\bigr).
$$

The gain comes from two facts.

1. **Vanishing order.** On the support of the weights, at least $P$ leaf pairs have momentum $\ge 2\rho$. On such a pair $w_{\rho,z}=z$ exactly. So, decoration by decoration, the profile product is a polynomial in $z$ of degree $\le n$ that is divisible by $z^P$.
2. **One-shot extrapolation.** Real Lagrange interpolation on $[0,Z]$, evaluated at $z=1$, gives the factor $Z^{-P}$. Here $Z\simeq\rho^{A}$ is the largest parameter for which the profiles stay bounded in $S^{40d,40d}$; it is large because the inputs have $\Lambda_p=40d\Lambda$ powers of decay.

The coefficients depend only on $(n,P,Z)$. The identity therefore holds garden by garden and decoration by decoration, and it commutes with every LF-class grouping, cancellation and reduction applied afterwards.

What this removes:

- **No marks.** No leaf, frontier vertex, or regular object is marked or protected.
- **No new weights.** No new weight or marked object enters any reduction. The only $\rho$-dependence sits inside the common profiles, which are uniformly bounded in $\mathcal P(2c_\chi C_1)$.
- **Section 6 machinery unused.** Lemmas 6.1–6.2 (the $R$-derivative and the polynomial leaf extraction) are not used.
- **No $L$-loss.** The cost is $(16c_\chi)^n\,C_{P,\delta}\,(1+n)^{(8\Lambda+80d)P}$, with no power of $L$, so $c_d=0$.
- **No lost gains, marked objects included.** By (G), the identity holds class by class, with one common factor for every class. So every per-class gain the downstream retains, on marked or unmarked objects, transfers unchanged. The extraction loses zero units of $\bar g+\bar\rho$.
- **Uniformity.** By (U), all constants are uniform in $(t,s,k,k',\zeta,M_1,M_2)$ and in $p$.

---

## 1. Setting and notation

### 1.1 Capped garden families with a profile slot

Fix the following data:

- $p\le\mathrm D-1$ (with $\mathrm D=\tau_*/\delta$, T609), $P$, a kernel type in $\{\mathfrak X,\mathfrak Y,\mathfrak W\}$, and $p<s<t<p+1$;
- $\zeta\in\{\pm\}$ and $k,k'\in\mathbb Z_L^d$;
- an order $n\ge1$.

Write $\Lambda=\Lambda_{p+1}=(40d)^{\mathrm D-p}$ (T611). Note that $\Lambda\ge 40d$ and $\Lambda_q\ge\Lambda_p=40d\Lambda$ for every $q\le p$.

**Gardens.** Let $\mathfrak F_n$ be the finite set of labelled capped gardens $\widehat{\mathcal G}$ of S Lemma 2.1. These come from flower gardens $\mathcal G\in\mathcal H^{\rm tr}_{p+1}$ of width $2P$ and order $n$ that satisfy the truncation of the chosen kernel type, retained as labels (S Lemma 2.1(4)).

Each $\mathcal G$ consists of $2P$ ternary trees $\mathcal T_1,\dots,\mathcal T_{2P}$; inserting lower-layer gardens at frontier leaves glues trees to trees. Use the following notation:

- tree $j$ contains the original layer-$p$ tree $\mathcal T^p_j$ as its top part;
- $B_j$ is the original frontier, i.e. the nonflower leaves of $\mathcal T_j^p$;
- $\mathcal L^\circ_j$ is the set of nonflower leaves of $\mathcal T_j$;
- $\mathcal L(v)$, for $v\in B_j$, is the set of leaves of the subtree of $\mathcal T_j$ rooted at $v$;
- $\mathrm{Pr}(\widehat{\mathcal G})$ is the set of non-cap leaf pairs, i.e. the pairs of nonflower leaves;
- for $\pi\in\mathrm{Pr}(\widehat{\mathcal G})$, $q_\pi$ is its layer and $k_\pi$ its common momentum.

**Integrands.** A *profile-independent integrand* is a family $\Theta=(\Theta_{\widehat{\mathcal G}})_{\widehat{\mathcal G}\in\mathfrak F_n}$ of bounded functions of the decorations $\mathfrak D$ of $\widehat{\mathcal G}$ (original roots $k$, cap roots $k'$). Let $G=(G_q)_{0\le q\le p}$ be real functions on $\mathbb R^d$ with $|G_q(u)|\lesssim\langle u\rangle^{-40d}$, and set

$$
S_\Theta[G]:=\sum_{\widehat{\mathcal G}\in\mathfrak F_n}\ \sum_{\mathfrak D}\ \Theta_{\widehat{\mathcal G}}(\mathfrak D)\prod_{\pi\in\mathrm{Pr}(\widehat{\mathcal G})}G_{q_\pi}(k_\pi).
\tag{1.1}
$$

The sum converges absolutely, since a decoration is determined by $(k_\pi)_\pi\in(\mathbb Z_L^d)^{n}$ and $\sum_{u\in\mathbb Z^d_L}\langle u\rangle^{-40d}<\infty$.

**The cases of interest.** $\Theta_{\widehat{\mathcal G}}(\mathfrak D)$ is the integrand of $K^{\rm cap}_{\widehat{\mathcal G}}$ in S (2.1), with the profile factors removed. It comprises:

- the normalization $(\delta/2L^{d-\gamma})^n$ (S §1), $\zeta(\mathcal G)$ and $\epsilon_{\mathfrak D}$;
- the time integral over the layered domain with phases and the pins $\prod_j\delta(t_{f_j^{\rm pr}}-s)$, carried out inside $\Theta$;
- the multiplier $W(\mathfrak D)$.

$W$ is one of the following:

- $W=1$ (plain);
- $W=\prod_jA_{j,L}$ (bottom first block);
- $W=\prod_jH_{j,M_1}$ with $M_1>L$ (nonbottom first block, S (3.1));
- any of the above times $\prod_jV_{j,M_2}$ (S (8.1)).

By S Lemma 2.2, $S_\Theta[F]$ with the true inputs $F_q=\varphi(\delta q)+\mathcal R_q$ (T693, T698; profile slot T2265) is exactly the order-$n$ part of the main term $\sum_{\mathcal G}\widetilde{\mathcal K}_{\mathcal G}$ in T2288, with the chosen cutoffs.

The frozen variants are also covered: the derivative patterns `dRoot`/`dParent`/`dChild i` (extra time pins), the $\dagger$ variant (fixed sibling labels, phase at $f^{\rm pr}$ removed) and per-tree labels. Each of these only changes $\Theta$; see the audit FLOWER-redraft §4.2 and T2327, T2331.

**Weight hypothesis.**

> **(Hb)** $\Theta_{\widehat{\mathcal G}}(\mathfrak D)=0$ whenever $\prod_{j=1}^{2P}H_{j,M_1}(\mathfrak D)=0$, for a fixed dyadic $M_1>L$.

(Hb) holds whenever $W$ contains the factor $\prod_jH_{j,M_1}$.

### 1.2 Profile classes and constants

- $\mathcal P(C)$: tuples $G=(G_q)_{q\le p}$ of real $C^{40d}$ functions on $\mathbb R^d$ with $\max_q\|G_q\|_{S^{40d,40d}}\le C$. The norm is T585.
- $\mathcal B_\Theta(C):=\sup_{G\in\mathcal P(C)}|S_\Theta[G]|$. Since $S_\Theta$ is homogeneous of degree $|\mathrm{Pr}|=n$ (Lemma C(i)),
$$\mathcal B_\Theta(\lambda C)=\lambda^n\mathcal B_\Theta(C)\qquad(\lambda>0).\tag{1.2}$$
- $c_\chi:=2^{40d}\max_{|\gamma|\le40d}\max(1,\|\partial^\gamma\chi\|_{L^\infty})$. It depends only on $d$ and the fixed $\chi$ of S §3, not on $P,\delta,L$.
- $C_1\ge1$ with $\max_{q\le p}\|F_q\|_{S^{40d,40d}}\le C_1$, as at T2069.
- For $A\in\{4\Lambda,\,4\Lambda+80d\}$: $C_\sharp(A):=\max\bigl(C_1,\max_{q\le p}\|F_q\|_{S^{40d,40d+A}}\bigr)$, finite and $C_2$-type (Lemma D), and $\kappa(A):=(C_\sharp(A)/C_1)^{1/A}\ge1$.
- $K:=|k-\zeta k'|$.
- Lagrange data: for integers $1\le P\le n$ and real $Z\ge1$, put $z_r:=rZ/n$ for $0\le r\le n$,
$$
\ell_r(x):=\prod_{0\le s\le n,\,s\ne r}\frac{nx-s}{r-s},\qquad
\beta_r=\beta_r(n,P,Z):=\sum_{i=P}^{n}Z^{-i}\,[x^i]\ell_r .
\tag{1.3}
$$

---

## 2. Statement

### Theorem 6.3′ (exact one-shot extraction of the first-cutoff gain and the external decay)

Let $\Theta$ be any profile-independent integrand as in §1.1.

**(a) External decay; no hypothesis on $W$.** Put $A:=4\Lambda$, $\rho:=K/(4n)$ and $Z:=\rho^{A}C_1/C_\sharp(A)$. If $Z\ge1$, then

$$
S_\Theta[F]=\sum_{r=0}^{n}\beta_r(n,P,Z)\,S_\Theta\bigl[F\,w_{\rho,z_r}\bigr],
\tag{2.1}
$$

where $F\,w_{\rho,z}$ denotes the tuple $(F_q\,w_{\rho,z})_{q\le p}$.

**(b) First-cutoff gain together with the external decay; under (Hb).** Put $A:=4\Lambda+80d$, $\rho:=M_1/(8n)$ and $Z:=\rho^AC_1/C_\sharp(A)$. If $Z\ge1$, then (2.1) holds.

**Properties of (2.1).** In both cases:

1. (2.1) holds **termwise**: for every $\widehat{\mathcal G}\in\mathfrak F_n$ and every decoration $\mathfrak D$,
   $$\Theta_{\widehat{\mathcal G}}(\mathfrak D)\prod_\pi F_{q_\pi}(k_\pi)=\sum_r\beta_r\,\Theta_{\widehat{\mathcal G}}(\mathfrak D)\prod_\pi (F_{q_\pi}w_{\rho,z_r})(k_\pi).$$
   It therefore holds for every subfamily of $\mathfrak F_n$, in particular for every LF or congruence class, with the same coefficients.
2. The coefficients satisfy $\sum_r|\beta_r|\le\binom{2n}{n}2^nZ^{-P}\le 8^nZ^{-P}$.
3. Each $F\,w_{\rho,z_r}$ is a common real layer-indexed profile tuple in $\mathcal P(2c_\chi C_1)$.

**Consequence (all cases, including $Z<1$).**

$$
|S_\Theta[F]|\le (16c_\chi)^n\,C^{(a)}_{P,\delta}\,(1+n)^{4\Lambda P}\,\langle K\rangle^{-4\Lambda P}\,\mathcal B_\Theta(C_1)
\quad\text{for every }\Theta,
\tag{2.2a}
$$

$$
|S_\Theta[F]|\le (16c_\chi)^n\,C^{(b)}_{P,\delta}\,(1+n)^{(8\Lambda+80d)P}\,M_1^{-80dP}\langle K\rangle^{-4\Lambda P}\,\mathcal B_\Theta(C_1)
\quad\text{under (Hb)},
\tag{2.2b}
$$

with the constants

- $C^{(a)}_{P,\delta}:=(C_\sharp(4\Lambda)/C_1)^{P}\,(6\kappa(4\Lambda))^{4\Lambda P}$;
- $C^{(b)}_{P,\delta}:=(C_\sharp(4\Lambda+80d)/C_1)^P\,(40\kappa(4\Lambda+80d))^{(8\Lambda+80d)P}$.

These depend on $P$, $d$, $\Lambda$ (hence $\delta$), $\tau_*$ and $\varphi_{\rm in}$, and not on $n,L,M_1,M_2,k,k',t,s$. The exponential base $16c_\chi$ depends only on $d$ and $\chi$.

**Relation to the wording of OPEN 6.3.** In the notation of OPEN 6.3 (S (6.5)), the "remaining family" consists of the $n+1$ unmarked families $S_\Theta[F w_{\rho,z_r}]$. Each is literally the original capped/pinned weighted family with a different common real profile tuple, so it admits exactly the reductions available for the unmarked family. The additional cost (6.5) holds with:

- base $C_{P,\chi}:=16c_\chi$, independent of $\delta$ (and of $P$);
- $A_{P,\delta}:=(8\Lambda+80d)P$ and $C_{P,\delta}:=\max(C^{(a)}_{P,\delta},C^{(b)}_{P,\delta})$;
- loss exponent $c_d:=0$.

All gains of unmarked objects are retained because nothing is marked. For marked objects, see (G) below.

**(G) Gain retention, marked objects included (class-level form).**

*Setting.* Let $\mathfrak F_n=\bigsqcup_\alpha\mathfrak F_{n,\alpha}$ be any partition determined by profile-independent data. Examples:

- the congruence classes (Def. `defcong` T1934; class sums T1942–1944);
- their refinements by $(\bar g,\bar\rho)$ (T2237) or by the ladder and VC structure;
- the protected or marked structures of OPEN 7.3/7.5/8.2.

More generally, allow $\Theta$ to be multiplied by any bounded profile-independent decoration multiplier, such as unit-ball localizations or fixed $\sigma_v$-cells (T2085–2097). Let $S_{\Theta,\alpha}$ be (1.1) restricted to $\mathfrak F_{n,\alpha}$, and set $\mathcal B_{\Theta,\alpha}(C):=\sup_{G\in\mathcal P(C)}|S_{\Theta,\alpha}[G]|$.

*Claim.* For every $\alpha$,
$$
|S_{\Theta,\alpha}[F]|\le\mathfrak e_n\,\mathcal B_{\Theta,\alpha}(C_1),\qquad
\mathfrak e_n:=(16c_\chi)^n\,C_{P,\delta}\,(1+n)^{A_{P,\delta}}\,\langle K\rangle^{-4\Lambda P}\,M_1^{-80dP\cdot\mathbf 1_{\rm (b)}},
\tag{2.3}
$$
with **the same** $\mathfrak e_n$ for all $\alpha$. Here $\mathbf 1_{\rm(b)}=1$ under (Hb) and $0$ otherwise.

*Consequences.*

- **Every downstream gain transfers.** Suppose a downstream argument proves a per-class bound $\mathcal B_{\Theta,\alpha}(C_1)\le\mathcal R_\alpha$, carrying whatever gains it retains on incoherent objects, bad vines and ladders, **marked or unmarked**. Examples are the factor $L^{-\nu\eta(\bar g+\bar\rho)}$ of (finalprooffin) T2252, which absorbs $C_2^{\bar g+\bar\rho}$ (T2251) and $C_2^{m_{\rm sb}}$ (T2248), and the gains absorbing $C_2^{g}C_0^{m+|q-q'|}$ (layerreg2, T932). Then the weighted class obeys $\mathfrak e_n\mathcal R_\alpha$, and $\sum_\alpha$ is taken exactly as in the gain-free proof.
- **The extraction consumes no gain.** It changes none of the following:
  - the garden, molecule, layering or truncation label;
  - any incoherency index $g$, or $\bar g$, $\bar\rho$, $q_{\rm sk}$, $m_{\rm sb}$;
  - any ladder, vine or protected set.
- **Its cost needs no gain.** The cost $(16c_\chi)^nC_{P,\delta}(1+n)^{A_{P,\delta}}$ is absorbed by S Lemma 10.1 alone, with a $\delta$-independent base.

In the referee's terms (REFEREE §4.1, 6.3(ii)): the 6.3 extraction loses **zero** units of $\bar g+\bar\rho$, on marked and unmarked objects alike. The $O(P)$ units that may be lost at marks created by OPEN 7.3/7.5/8.2 belong to those items and to the aggregate count. The extraction neither adds to them nor depends on them.

**(U) Uniformity.**

- The coefficients $\beta_r$ depend only on $(n,P,Z)$.
- Take $C_{P,\delta}:=\max_{0\le p\le\mathrm D-1}\max(C^{(a)}_{P,\delta},C^{(b)}_{P,\delta})$ and $A_{P,\delta}:=(8\Lambda_1+80d)P$ with $\Lambda_1=(40d)^{\mathrm D}$. With this choice, $16c_\chi$, $C_{P,\delta}$ and $A_{P,\delta}$ are independent of:
  - $(t,s,k,k',\zeta,M_1,M_2)$ and the layer index $p$;
  - the kernel type and the cutoff choice;
  - the frozen pattern and $\dagger$ labels;
  - the partition $\alpha$.
- The evaluation profiles $Fw_{\rho,z_r}$ depend on $(n,K)$ or $(n,M_1)$, but always lie in the fixed class $\mathcal P(2c_\chi C_1)$.

Hence (2.2a), (2.2b) and (2.3) hold uniformly in all these parameters.

**Remark 2.1 (other dyadic first cutoffs).** Part (b) uses only two support properties of the shell:

- $H_{j,M_1}\ne0$ implies $\max_{v\in B_j}|k_v|>c_-M_1$;
- $H_{j,M_1}\ne0$ implies $\max_{v\in B_j}|k_v|<c_+M_1$.

S (3.1) has $c_-=\tfrac12$ and $c_+=2$. The frozen `dyadicCut` (FLOWER-redraft D7: support $M/4<\max<M$) has $c_-=\tfrac14$ and $c_+=1$. For any fixed $0<c_-\le c_+$, replace (Hb) by

> **(Hb′)** $\Theta(\mathfrak D)=0$ unless $c_-M_1<\max_{v\in B_j}|k_v|<c_+M_1$ for every $j$.

Then take $\rho:=c_-M_1/(4n)$, and use $K<2nc_+M_1$ in place of Lemma C(iv)(v). Theorem 6.3′(b) then holds with $40$ in $C^{(b)}_{P,\delta}$ replaced by a constant depending only on $c_\pm$. The proof is otherwise verbatim.

---

## 3. Lemmas

### Lemma A — One-shot real extrapolation

Let $1\le P\le n$ and $Z\ge1$. For every polynomial $\Pi$ with complex coefficients, degree $\le n$ and $z^P\mid\Pi$,

$$
\Pi(1)=\sum_{r=0}^n\beta_r\,\Pi(z_r),\qquad \sum_{r=0}^n|\beta_r|\le \binom{2n}{n}2^n Z^{-P}\le 8^nZ^{-P}.
\tag{3.1}
$$

Only the values of $\Pi$ at the $n+1$ points $z_r\in[0,Z]$ are used.

**Proof.** Write $\Pi(z)=\sum_{i=P}^nc_iz^i$ and $p(x):=\Pi(Zx)$. The nodes $x_r=r/n$ are distinct and $\deg p\le n$, so $p=\sum_rp(x_r)\ell_r$ exactly. Comparing the coefficients of $x^i$ gives $c_iZ^i=\sum_r\Pi(z_r)[x^i]\ell_r$, so

$$\Pi(1)=\sum_{i\ge P}c_i=\sum_r\Pi(z_r)\sum_{i=P}^nZ^{-i}[x^i]\ell_r=\sum_r\beta_r\Pi(z_r).$$

For the bound:

- The denominator of $\ell_r$ has modulus $\prod_{s\ne r}|r-s|=r!(n-r)!$.
- The coefficients of $\prod_{s\ne r}(nx-s)$ are bounded in modulus by those of $\prod_{s\ne r}(nx+s)$. These are nonnegative with sum $\prod_{s\ne r}(n+s)\le (2n)!/n!$, using $\prod_{s=0}^n(n+s)=(2n)!/(n-1)!$ and $n+r\ge n$.
- Hence $\sum_i|[x^i]\ell_r|\le\binom{2n}{n}\binom nr$, and $\sum_r\sum_i|[x^i]\ell_r|\le\binom{2n}n2^n\le8^n$.
- Since $Z\ge1$, $|\beta_r|\le Z^{-P}\sum_i|[x^i]\ell_r|$.

∎

The identity and the bound were checked in exact rational arithmetic: the coefficient bound for $n\le30$ (the maximum ratio to $8^n$ is $0.375$), and the identity in random trials. A toy garden check of the termwise identity under (∗) of Lemma C also passed (scratch script `chk/lagr.py`).

*Remark (polynomial refinement, not needed).* Suppose the unmarked bound is used for $z\in[-Z,Z]$; the profiles $Fw_{\rho,z}$ with $z<0$ are real and obey the same norm bound. Then Taylor's formula and V. A. Markov's inequality for $\Psi^{(P)}$, applied to real and imaginary parts, replace $8^n$ by $2n^{2P}/P!$.

### Lemma B — The profile split

Let $\rho\ge1$, $A\ge0$, $z\ge0$, and let $F$ be real with $\|F\|_{S^{40d,40d+A}}<\infty$. Then $Fw_{\rho,z}$ is real, $w_{\rho,1}\equiv1$, and

$$
\|F w_{\rho,z}\|_{S^{40d,40d}}\le c_\chi\Bigl(\|F\|_{S^{40d,40d}}+z\,\rho^{-A}\|F\|_{S^{40d,40d+A}}\Bigr).
\tag{3.2}
$$

**Proof.** $\chi$ is real with $0\le\chi\le1$; hence $w_{\rho,z}$ is real and $w_{\rho,1}=1$.

*Low part.* For $|\beta|\le40d$, Leibniz gives
$$\partial^\beta(F\chi(\cdot/\rho))=\sum_{\gamma\le\beta}\binom\beta\gamma\partial^{\beta-\gamma}F\,\rho^{-|\gamma|}(\partial^\gamma\chi)(\cdot/\rho).$$
Since $\rho\ge1$ and $\sum_\gamma\binom\beta\gamma=2^{|\beta|}$, this yields $\|F\chi(\cdot/\rho)\|_{S^{40d,40d}}\le c_\chi\|F\|_{S^{40d,40d}}$.

*High part.* In the expansion of $\partial^\beta(F(1-\chi(\cdot/\rho)))$:

- every term is supported in $|u|\ge\rho$, because $1-\chi(u/\rho)=0$ and $\partial^\gamma\chi(u/\rho)=0$ ($\gamma\ne0$) for $|u|\le\rho$;
- there $\langle u\rangle^{40d}\le\rho^{-A}\langle u\rangle^{40d+A}$;
- also $|1-\chi|\le1$.

Hence $\|F(1-\chi(\cdot/\rho))\|_{S^{40d,40d}}\le c_\chi\rho^{-A}\|F\|_{S^{40d,40d+A}}$. Add the two parts. ∎

### Lemma C — Leaf combinatorics and vanishing order

Let $\widehat{\mathcal G}\in\mathfrak F_n$ and let $\mathfrak D$ be a decoration.

**(i) Counts.** The sets $\mathcal L^\circ_j$ partition the nonflower leaves, and $|\mathcal L^\circ_j|\le2n$. The sets $\{\mathcal L(v)\}_{v\in B_j}$ partition $\mathcal L^\circ_j$, and $|B_j|\le2n$. Moreover $|\mathrm{Pr}(\widehat{\mathcal G})|=n$.

*Proof.* Tree $\mathcal T_j$ has $a_j$ branching nodes, with $\sum_ja_j=n$, and $2a_j+1$ leaves, one of which is the flower $f_j$.

- So $|\mathcal L^\circ_j|=2a_j\le 2n$. There are $2n$ nonflower leaves in all, completely paired among themselves (T2261), giving $n$ pairs. The flowers are paired only with the caps (S Lemma 2.1).
- The stem ends at $f_j$, a leaf of $\mathcal T^p_j$, and all stem nodes are in layer $p$ (T2261). So every nonflower leaf of $\mathcal T_j$ descends from exactly one $v\in B_j$.
- $|B_j|\le 2a_j$, since $\mathcal T^p_j$ has at most $a_j$ branching nodes.

**(ii) Conservation** (T630–647; S (6.2), (6.4)). For every $v\in B_j$, $k_v=\sum_{\ell\in\mathcal L(v)}\pm k_\ell$. In every tree,
$$k-\zeta k'=\sum_{v\in B_j}\pm k_v=\sum_{\ell\in\mathcal L^\circ_j}\pm k_\ell .$$
Paired leaves carry equal momenta.

**(iii) Vanishing order.** Let $\rho>0$ and suppose

> (∗) for each $j$ there is $\ell\in\mathcal L^\circ_j$ with $|k_\ell|\ge2\rho$.

Then $h:=\#\{\pi\in\mathrm{Pr}:|k_\pi|\ge2\rho\}\ge P$, and $\Pi(z):=\prod_{\pi\in\mathrm{Pr}}w_{\rho,z}(k_\pi)$ is a polynomial of degree $\le n$ divisible by $z^P$.

*Proof.* The high pairs contain a leaf of every one of the $2P$ trees. A pair has two leaves, so it meets at most two trees; hence $h\ge P$. If $|u|\ge2\rho$ then $\chi(u/\rho)=0$ and $w_{\rho,z}(u)=z$. Therefore $\Pi(z)=z^h\prod_{|k_\pi|<2\rho}w_{\rho,z}(k_\pi)$, and each factor is affine in $z$.

**(iv) When (∗) holds.**

- (∗) holds at every decoration if $K\ge4n\rho$. Indeed, by (ii) and (i), some $\ell\in\mathcal L^\circ_j$ has $|k_\ell|\ge K/|\mathcal L^\circ_j|\ge K/(2n)\ge2\rho$.
- (∗) holds at every decoration with $\prod_jH_{j,M}(\mathfrak D)\ne0$, if $M>L$ and $\rho\le M/(8n)$. Indeed, $H_{j,M}\ne0$ forces some $v\in B_j$ with $|k_v|>M/2$: if all $|k_v|\le M/2$, then $A_{j,M/2}=A_{j,M}=1$ because $\chi=1$ on $|x|\le1$. Then $\sum_{\ell\in\mathcal L(v)}|k_\ell|>M/2\ge4n\rho$ and $|\mathcal L(v)|\le 2n$, so some $\ell\in\mathcal L(v)\subset\mathcal L^\circ_j$ has $|k_\ell|>2\rho$.

**(v) Size of $K$ on the shell support.** If $A_{j,M}(\mathfrak D)\ne0$ for some $j$, then $K<4nM$, since all $|k_v|<2M$ for $v\in B_j$ and $|B_j|\le2n$. Moreover $H_{j,M}\ne0$ implies $A_{j,M}\ne0$: if $A_{j,M}=0$, some $|k_v|\ge2M$, and then also $A_{j,M/2}=0$. ∎

### Lemma D — Tail norms of the true inputs

For $0\le A\le 4\Lambda+80d$,
$$\max_{q\le p}\|F_q\|_{S^{40d,40d+A}}\le 2+\sup_{0\le\tau\le\tau_*}\|\varphi(\tau)\|_{S^{40d,40d+A}}<\infty .$$
The right side depends only on $(d,A,\tau_*,\varphi_{\rm in})$, so it is a $C_2$-type constant (T610).

**Proof.** $F_q=\varphi(\delta q)+\mathcal R_q$ with $\mathcal R_q$ real and $\|\mathcal R_q\|_{S^{\Lambda_q,\Lambda_q}}\le L^{-\theta_q}\le 1$ (T698, T695). The norm of a lattice function is an infimum over extensions (T591). Take the real part of a near-minimizing extension; this does not increase the norm. That gives a real extension of norm $\le2$.

Since $40d\le\Lambda_q$ and $40d+A\le 4\Lambda+120d\le 40d\Lambda=\Lambda_p\le\Lambda_q$ (using $\Lambda\ge40d$, T611), we get $\|\mathcal R_q\|_{S^{40d,40d+A}}\le2$.

For $\varphi$: T2518–2525 (schappend10) with $T=\tau_*<\tau_{\max}$ bounds $\sup_{\tau\le\tau_*}\|\varphi(\tau)\|_{Z_{s,m}}$ for every $m$. The embedding $H^d(\mathbb R^d)\hookrightarrow L^\infty$, together with $\langle k\rangle^{w}\lesssim_w\sum_{|\alpha|\le w}|k^\alpha|$ and $s>0$, gives $\|\varphi(\tau)\|_{S^{40d,40d+A}}\lesssim_{d,A}\|\varphi(\tau)\|_{Z_{s,\,81d+A}}$. The source makes the same use at T2065: "$\langle k\rangle^{4\Lambda}F_q$ … bounded in $S^{40d,40d}$ … with norm $C_2$". ∎

---

## 4. Proof of Theorem 6.3′

**Termwise identity (property 1), case (a).** Fix $\widehat{\mathcal G}$ and $\mathfrak D$ with $\Theta_{\widehat{\mathcal G}}(\mathfrak D)\ne0$; otherwise there is nothing to prove.

- Here $K=4n\rho$, so (∗) holds by Lemma C(iv).
- By Lemma C(iii), $\Pi(z)=\prod_\pi w_{\rho,z}(k_\pi)$ has degree $\le n$ and $z^P\mid\Pi$. Note $P\le n$, since every original tree of $\mathfrak X_{\rm reg}$ has order $\ge1$ (S §1), so $n\ge 2P$.
- Lemma A gives $1=\Pi(1)=\sum_r\beta_r\Pi(z_r)$.
- Multiply by $\Theta(\mathfrak D)\prod_\pi F_{q_\pi}(k_\pi)$ and use $F_{q_\pi}(k_\pi)w_{\rho,z_r}(k_\pi)=(F_{q_\pi}w_{\rho,z_r})(k_\pi)$.

**Termwise identity, case (b).** If $\Theta(\mathfrak D)\ne0$, then $\prod_jH_{j,M_1}(\mathfrak D)\ne0$ by (Hb). Since $\rho=M_1/(8n)$, (∗) holds by Lemma C(iv). The rest is identical.

**Summation.** Each of the $n+1$ sums $S_\Theta[Fw_{\rho,z_r}]$ converges absolutely, by §1.1 and Lemma B. Summing the termwise identity over $\mathfrak D$ and $\widehat{\mathcal G}$ (or over any subfamily) gives (2.1). Property 2 is Lemma A.

**Property 3.** $Z\ge1$ means $\rho^A\ge C_\sharp(A)/C_1\ge1$, so $\rho\ge1$. For $0\le z\le Z$, Lemma B and the definition of $Z$ give
$$\|F_qw_{\rho,z}\|_{S^{40d,40d}}\le c_\chi\bigl(C_1+Z\rho^{-A}C_\sharp(A)\bigr)=2c_\chi C_1.$$

**Bound (2.2a).**

- *If $Z\ge1$:* by (2.1), properties 2–3 and (1.2),
  $$|S_\Theta[F]|\le 8^nZ^{-P}(2c_\chi)^n\mathcal B_\Theta(C_1)=(16c_\chi)^n\Bigl(\tfrac{C_\sharp}{C_1}\Bigr)^P\rho^{-4\Lambda P}\mathcal B_\Theta(C_1).$$
  Here $\rho^{-4\Lambda P}=(4n)^{4\Lambda P}K^{-4\Lambda P}$. Also $\rho\ge1$ forces $K\ge4n\ge1$, hence $K^{-1}\le\sqrt2\langle K\rangle^{-1}$. Since $(4\sqrt2)^{4\Lambda P}\le 6^{4\Lambda P}$, this is within (2.2a).
- *If $Z<1$:* then $\rho<\kappa$, so $K<4n\kappa$ and $\langle K\rangle\le 5n\kappa$. Hence $1\le(5n\kappa)^{4\Lambda P}\langle K\rangle^{-4\Lambda P}$, while trivially $|S_\Theta[F]|\le\mathcal B_\Theta(C_1)$ because $F\in\mathcal P(C_1)$.

**Bound (2.2b).**

- *If $K\ge4nM_1$:* every decoration has $\prod_jH_{j,M_1}=0$ by Lemma C(v). So $S_\Theta\equiv0$ by (Hb).
- *Otherwise:* $\langle K\rangle\le1+4nM_1\le 5nM_1$, i.e. $M_1^{-1}\le 5n\langle K\rangle^{-1}$.
  - *If $Z\ge1$:* as above, $|S_\Theta[F]|\le(16c_\chi)^n(C_\sharp/C_1)^P\rho^{-AP}\mathcal B_\Theta(C_1)$, and
    $$\rho^{-AP}=(8n)^{AP}M_1^{-80dP}M_1^{-4\Lambda P}\le (8n)^{(4\Lambda+80d)P}(5n)^{4\Lambda P}M_1^{-80dP}\langle K\rangle^{-4\Lambda P}.$$
  - *If $Z<1$:* then $M_1<8n\kappa$. Hence $M_1^{80dP}\langle K\rangle^{4\Lambda P}\le(8n\kappa)^{80dP}(40n^2\kappa)^{4\Lambda P}$, and again $|S_\Theta[F]|\le\mathcal B_\Theta(C_1)$.

  Both branches fit $(40\kappa)^{(8\Lambda+80d)P}(1+n)^{(8\Lambda+80d)P}$, because $\kappa\ge1$. ∎

**Proof of (G) and (U).**

- *Termwise identity on a class.* Property 1 holds for each garden and decoration. So it holds for $\mathfrak F_{n,\alpha}$, and for $\Theta\psi$ with $\psi$ any bounded profile-independent multiplier: (Hb) persists under multiplication by $\psi$, and case (a) needs no hypothesis. This gives $S_{\Theta,\alpha}[F]=\sum_r\beta_rS_{\Theta,\alpha}[Fw_{\rho,z_r}]$.
- *Homogeneity on a class.* Every garden in $\mathfrak F_{n,\alpha}$ has exactly $n$ profile pairs (Lemma C(i)). So $S_{\Theta,\alpha}$ is homogeneous of degree $n$, and $\mathcal B_{\Theta,\alpha}(2c_\chi C_1)=(2c_\chi)^n\mathcal B_{\Theta,\alpha}(C_1)$.
- *The bounds.* The coefficient bound, the branches $Z<1$ and $K\ge4nM_1$, and the conversions to $\langle K\rangle$ and $M_1$ in the proofs of (2.2a)/(2.2b) do not involve the family. Repeating them verbatim gives (2.3) with the same $\mathfrak e_n$.
- *Uniformity in $p$.* $(1+n)^{(8\Lambda_{p+1}+80d)P}\le(1+n)^{A_{P,\delta}}$, and $C_{P,\delta}$ is a maximum over finitely many $p$.
- *Other parameters.* Independence of every other parameter in (U) is read off the definitions.
- *Summing classes.* Finally $|S_\Theta[F]|\le\sum_\alpha|S_{\Theta,\alpha}[F]|\le\mathfrak e_n\sum_\alpha\mathcal B_{\Theta,\alpha}(C_1)$. ∎

---

## 5. Sufficiency for the assembly: Proposition 10.3′

### Hypothesis (10.3′) — gain-free, profile-uniform aggregate bound

This replaces S (10.3). For each $n$ in the ranges used in S Prop. 10.3, each of the three cutoff choices in S (1.1), and each truncation $\mathfrak X/\mathfrak Y/\mathfrak W$, let $\Theta$ be the corresponding capped/pinned weighted integrand of §1.1. The hypothesis is

$$
\mathcal B_\Theta(C_1)\le E_{P,\delta}(1+n)^{A_{P,\delta}}D_P^{\,n+1}\delta^{8\nu n}L^{BP}\,G_2(M_2),
\tag{5.1}
$$

where:

- $G_2(M_2)=M_2^{-P/9}$ when the second block is present and nonbottom (with $|k|\ge M_1^{10}$), and $G_2=1$ otherwise;
- $D_P$ is independent of $\delta$;
- $B$ satisfies (10.4).

**Two further requirements on (5.1).**

- *Class-summed form allowed.* By (2.3), it is equally sufficient to prove the class-summed form
  $$\sum_\alpha\mathcal B_{\Theta,\alpha}(C_1)\le\text{RHS of (5.1)},$$
  for whatever partition the downstream count uses. This is the form T2237–2255 actually produces: a per-congruence-class bound carrying $L^{-\nu\eta(\bar g+\bar\rho)}$, times the class count $C_0^n(C_0\bar\rho)!(C_0R)!C_2^{\bar g+\bar\rho}$.
- *Uniformity* (REFEREE §3, on S (10.3)). $E_{P,\delta}$, $A_{P,\delta}$, $D_P$ and $B$ must be uniform in $(t,s,k,k',\zeta,M_1,M_2)$.

(5.1) is the gain-free form of the aggregate item the referee proposes as "OPEN 10.3 (aggregate count and budget)" (REFEREE §4.2 M1). In that composition, Theorem 6.3′ contributes:

- the base factor $16c_\chi$;
- no change to $\bar\rho$ (no excision);
- no lost gain units;
- no marks.

### Proposition 10.3′

Assume OPEN 7.3, 7.5, 8.2 and 10.2 as stated in S, and (5.1). OPEN 6.3 is now not an assumption: it is replaced by Theorem 6.3′. Then S (10.3) holds with

$$
E'=E_{P,\delta}\,C_{P,\delta},\qquad A'=A_{P,\delta}+(8\Lambda+80d)P,\qquad D_P'=16c_\chi D_P,\qquad B'=B .
$$

Consequently S (1.1) holds, and so do its $e^{-100N}$ versions for $\mathfrak Y,\mathfrak W$, by the unchanged proof of S Prop. 10.3.

**Proof.** Treat the cutoff versions in turn.

- *Plain version, and versions whose first block is bottom ($W\ni\prod_jA_{j,L}$):* apply (2.2a). Here $G_{\rm nonbottom}$ contains no $M_1$ factor, and the bottom first-block factor is paid by S Lemma 9.5, exactly as before.
- *Nonbottom first block:* (Hb) holds; apply (2.2b).
- *In every case:* multiply by (5.1). If (5.1) is given in class-summed form, use (2.3) and sum over $\alpha$ instead. This yields S (10.3), with $G_{\rm nonbottom}(M_1,M_2)$ assembled from $M_1^{-80dP}$ (from (2.2b)) and $G_2$ (from (5.1)).
- *Uniformity.* By (U), the resulting constants $E',A',D_P',B$ are uniform in $(t,s,k,k',\zeta,M_1,M_2)$ whenever those of (5.1) are.

S Prop. 10.3 uses (10.3) only through S Lemma 10.1. That lemma needs a $\delta$-independent base, here $16c_\chi D_P$, and allows arbitrary $E_{P,\delta}$ and $A_{P,\delta}$. It also uses the order restriction $n\ge N+1$ for $\mathfrak Y,\mathfrak W$; that restriction is a property of $\mathfrak F_n$ and is untouched by (2.1). The exponent $B$ is unchanged, so (10.4) is unaffected. ∎

### Why (5.1) is not a stronger demand than the original plan

(5.1) is exactly the estimate that the unmarked reduction proves.

- **Profiles enter only through reality and the $S^{40d,40d}$ bound.** The source uses the input profiles only in these ways:
  - T995: "each $F_{\mathcal L_\ell}(k_\ell)$ is bounded in $\mathfrak S^{40d,40d}$ by assumption";
  - T1173: "real valued, and … bounded in the same regularity space";
  - T2069: "bounded in $\mathfrak S^{40d,40d}$ by $C_1$".

  The supplement's own downstream lemmas also take modified common real profiles: S Lemma 5.1 and (5.3) use $F_p\chi(\cdot/R)^2$, and S Lemma 5.2 uses "another common real profile". A proof of the downstream estimates of this kind is automatically uniform over $\mathcal P(C_1)$, and the constants $\mathcal B_\Theta(C_1)$ inherit only $C_1$.
- **The original route needed more.** Under S's own plan, OPEN 6.3's remaining families carried leaf profiles $k_\ell^{\beta}F$ at up to $80dP$ marked leaves, plus $2P$ selected frontier vertices. Bounding those required the downstream items for *marked* families with modified profiles. (5.1) requires them only for *unmarked* families with common profiles.

### Consequences for the other OPEN items (all simplifications)

- **OPEN 7.5:** "the marks required in Section 6" is now the empty set. The protected incidences $b$ are only the basic special vertices ($\le16P$), the $2P$ caps, the pins, and the selected-face vertices of Lemma 9.1 / OPEN 7.3.
- **OPEN 8.2:** "the modified final profiles of Section 6" become common real profile tuples in $\mathcal P(2c_\chi C_1)$, i.e. ordinary inputs. No separately labelled leaf modification remains.
- **S Lemmas 6.1 and 6.2:** remain true but are unused by the assembly.
- **S Lemma 5.2:** its caveat (no reality identity for independently marked profiles) is no longer relevant. Only common profiles occur.
- **The decay budget after S (6.4):** it is realized exactly. The weight $40d+A=4\Lambda+120d\le\Lambda_p$ is the only use of input decay.

---

## 6. Why this is not a forbidden regrouping

1. **Exact before absolute values.** (2.1) is an identity of integrands, decoration by decoration. Its coefficients $\beta_r$ are universal; they depend only on $(n,P,Z)$. No summand is discarded, so S Lemma 9.4's warning does not apply. Every evaluation $S_\Theta[Fw_{\rho,z_r}]$ is the complete family, with every LF class intact and one common real profile at every leaf pair. This is the case S Lemma 5.2 explicitly permits ("Replacing a real profile by another common real profile …").
2. **No profile-dependent selection.** OPEN 6.3's obstruction was that (6.3) "modifies different final-leaf profiles in different summands". Here the splitting into $\chi(\cdot/\rho)$ and $1-\chi(\cdot/\rho)$ is never expanded inside an estimate. It is used only through the vanishing order of a polynomial in $z$, which is a pointwise algebraic fact.
3. **One shot, not iterated.** The campaign's R47 design notes (<scratch>/research-twistprof/NOTES.md, P-1) rejected non-central Lagrange nodes because $2^{\deg}$ *raised to the number $r\le 8m\Lambda$ of iterated first-order extractions* is not absorbable. Here there is a single extrapolation; its cost $8^n$ is not raised to any $\Lambda$-dependent power. The $\Lambda$-dependence sits only in the interval length $Z\simeq\rho^{4\Lambda+80d}$, which is a gain, and in the polynomial $(1+n)^{(8\Lambda+80d)P}$. P-2 there (one global scale sees only $\max_j|k_j|$) concerns distinct root momenta in `layergarden`. In the flower moment, all $2P$ trees share $K=|k-\zeta k'|$ and the same $M_1$ (T2294), so one global scale suffices.
4. **Reality is preserved.** Only real $z_r\in[0,Z]$ are used, so the profiles stay real. No complex Cauchy radius is involved.

---

## 7. Loss accounting

**Inputs.** $C_1$ is the $S^{40d,40d}$ bound of the true inputs; $C_\sharp\in C_2$ (Lemma D); $c_\chi=c_\chi(d,\chi)$.

| Operation | Extra cost | Power of $L$ | Marks |
|---|---|---:|---:|
| External decay, plain/bottom versions, (2.2a) | $(16c_\chi)^n(C_\sharp/C_1)^P(6\kappa)^{4\Lambda P}(1+n)^{4\Lambda P}$ | $0$ | $0$ |
| First-cutoff gain + external decay, (2.2b) | $(16c_\chi)^n(C_\sharp/C_1)^P(40\kappa)^{(8\Lambda+80d)P}(1+n)^{(8\Lambda+80d)P}$ | $0$ | $0$ |
| Input decay used per leaf pair | weight $40d+4\Lambda+80d\le\Lambda_p=40d\Lambda$ (e.g. $d=3$, $\Lambda\ge120$: $840\le14400$) | — | — |

**Consistency with o102.** The OPEN 10.2 packet extracts the same two factors pointwise in the remainder terms, with allocation $4\Lambda+80d+(d+1)\le\Lambda_p$ per input. The $(d+1)$ there pays for absolute decoration summation. Here the corresponding reserve is the $40d$ weight kept in the profile class $\mathcal P(\cdot)$, which the downstream analysis uses (T995, T2069).

- Both allocations fit under $\Lambda_p=40d\Lambda$.
- They are never charged to the same input in the same term. The main term (here) and the remainder terms (o102) are disjoint summands of T2288.

**Fit with the quantifier order** (C₀, η, C₁, ν, δ, C₂, L; $P$ before $\delta$):

- the base $16c_\chi$ is absolute: it depends on $d$ and the fixed $\chi$ only;
- $A_{P,\delta}=(8\Lambda+80d)P$ and $C_{P,\delta}$ are fixed after $\delta$ and before $L$;
- S Lemma 10.1 absorbs $(1+n)^{A_{P,\delta}}$ and $C_{P,\delta}$, with the $\delta$-choice using only $D_P'=16c_\chi D_P$.

**Fit with the S §10 table.**

- The row "First-shell extraction: $M_1^{-80dP}C_{d,P}(1+n)^{(80d+2)P}$ — Grouping and external decay: OPEN 6.3" is replaced by the two rows above. Its "Remaining requirement" becomes **none**.
- The row "Unmarked local weighted LF chain" now covers everything that the first-cutoff families need.
- 6.3 contributes **$0$** to $B$ in (10.4): $B+80d+\tfrac19+3\le(100d)^3$ is unaffected.
- **Frozen derivative patterns** ($c=2$, i.e. $L^{2(100d)^3P}$, with the $M_1$ factor kept): these patterns only add time pins to $\Theta$. Theorem 6.3′ applies verbatim, with the same extracted factors and the same zero $L$-loss. The same holds for the $\dagger$ variant (fixed sibling labels, removed $f^{\rm pr}$ phase) and for per-tree labels and patterns.

---

## 8. Dependencies

| Source | Content | Use |
|---|---|---|
| T585, T589–591 | $\mathfrak S^{\Lambda_1,\Lambda_2}$ norm; lattice functions by infimum over extensions | $\mathcal P(C)$; Lemmas B, D |
| T606–613 | $C_1$, $C_2$, $\Lambda_p=(40d)^{\mathrm D-p+1}$ | constants; $\Lambda\ge40d$; Lemma D |
| T630–647 | decorations and conservation | Lemma C(ii) |
| T671 (defkg0) | profile enters only as $\prod_{\ell}^{(+)}F_{\mathcal L_\ell}(k_\ell)$, one factor per pair | homogeneity (1.2), (1.1) |
| T693–698 (ansatz1–3) | $F_q=\varphi(\delta q)+\mathcal R_q$, real; $\|\mathcal R_q\|_{\mathfrak S^{\Lambda_q,\Lambda_q}}\le L^{-\theta_q}$ | Lemma D |
| T995, T1173, T2069 | profiles used only through reality and the $\mathfrak S^{40d,40d}$ bound | §5, justification of (5.1)'s form |
| T2065 | source's leaf device (pointwise, erratum E24/E-TWPROF) and the $C_2$ bound on weighted inputs | replaced by (2.1); Lemma D comparison |
| T2259–2265, T2283–2285 | flower trees/gardens, stems in layer $p$, (kqflower), the two cutoffs | §1.1; Lemma C(i) |
| T2288–2294 | moment expansion; item (1) (decay and $M_1$ "in the same way") | target of Theorem 6.3′ |
| T2327, T2331 | $\dagger$ variant and derivative patterns | $\Theta$ covers them (§1.1, §7) |
| T932 (layerreg2), T1934–1944, T2085–2097, T2237–2253 | layering count $C_2^gC_0^{m+|q-q'|}$; congruence classes; $\sigma$-cells and absolute counting; $C_2^{m_{\rm sb}}$ (T2248), class count $C_2^{\bar g+\bar\rho}$ (T2251), gain $L^{-\nu\eta(\bar g+\bar\rho)}$ (T2252) | (G): per-class gains transfer; class-summed (5.1) |
| T2518–2525 (schappend10) | uniform Schwartz bounds for $\varphi$ on $[0,\tau_*]$ | Lemma D |
| S Lemma 2.1, 2.2 | capped encoding; multipliers in the moment identity | $S_\Theta[F]$ is the main term |
| S (3.1) | $A_{j,M},H_{j,M}$ with the fixed $\chi$ | Lemma C(iv)(v) |
| S (6.2), (6.4) | conservation to final leaves | Lemma C(ii) |
| S Lemma 9.5, 10.1, Prop. 10.3 | bottom blocks; polynomial absorption; assembly | §5 |
| S Lemma 3.2, 5.1–5.3 | unmarked low-pass weighted families | downstream bound of $\mathcal B_\Theta(C_1)$ (not used in this proof) |

---

## 9. Remaining OPEN sub-items

**For OPEN 6.3 itself: none.** The referee's two clarifications are built in: marked-gain retention is (G), and uniformity is (U). The referee's M3 residual ("marked leaves (monomials, $b_{M,R}$) remain under 6.3") is moot, since the variant creates no marked leaves. The stray comma in S (6.5) is a typo in the read-only supplement.

One interface statement must be recorded downstream. It is not a new mathematical claim; it states the existing form of the estimates.

- **I-6.3 (profile uniformity).** The gain-free family bound must be stated as (5.1), possibly in class-summed form, i.e. uniformly over real layer-indexed profile tuples in $\mathcal P(C_1)$. Its constants must depend on $C_1$ only, and must be uniform in $(t,s,k,k',\zeta,M_1,M_2)$.
- The downstream items OPEN 7.3/7.5/8.2 and the count T2237–2255 must deliver (5.1) for **unmarked** first-cutoff families. This was already their job; it is now strictly smaller, because the Section 6 marks are gone.
- A downstream proof that used a property of $F_q$ beyond reality and the $\mathfrak S^{40d,40d}$ bound would also need that property for $Fw_{\rho,z}$. No such use exists in T or S.

**Side remark for o102 (OPEN 10.2), outside scope.**

- The main terms of $\mathcal E^{(2)}$ (orders $>N^4$) have the form (1.1). Theorem 6.3′ applies to them verbatim, for every $n$.
- The terms of $\mathcal E^{(1)}$ that contain $\mathcal E_p$ or $\widetilde{\mathcal E}_p$ are not polynomial in a common profile. They are not covered.

STATUS: CLOSED WITH VARIANT (see §2 Theorem 6.3′ and §5 Proposition 10.3′)
