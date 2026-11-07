# o102 — Resolution of OPEN 10.2 (weighted expansion remainders)

Packet o102 of FLOWER-OPEN. Binding context: `COMMON.md` (sha256 `a165bad5…`), `o102/BRIEF.md` (sha256 `b087db21…`),
`SUPPLEMENT-v1.md` (sha256 `ddd81fe1238e7c51379a69981b4d10aa68690ced46d0fc1b115200fc0c3774d7`).

The sources were read from pinned copies, with hashes checked at first read:

- **T** `WKE-Longer_times_Final_arXiv.tex`, sha256 `493eef6b7dec448b…`. "T*n*" means line *n* of this file.
- **D21** `Inventiones-Final_Version.tex`, sha256 `50d0e236…`; **D23** `Revision_Submit.tex`, sha256 `c7e47dfa…`.
  Neither is used below (§9 explains why).
- **S** = the supplement. "S(x.y)" is its display (x.y); "S-Lemma x.y" is its lemma.

## 0. Summary

The remainders $\mathcal E^{(1)},\mathcal E^{(2)}$ of T2288–2290 are never fed into the `layergarden` machinery. T bounds them
with absolute values only (T803–807), and the weighted versions can be bounded the same way. Three facts make this
work.

1. **Weights.** The cutoff weights depend only on momenta, have modulus $\le1$, and have explicit supports. After
   absolute values have been taken they can be discarded (this is S-Lemma 9.4), except that their supports are used.
2. **First cutoff and external decay.** On the support of the first cutoff some frontier leaf of each original tree
   has $|k_\ell|\ge M_1/2$. This gives $M_1^{-80dP}$ and $\langle k-\zeta k'\rangle^{-4\Lambda P}$ **pointwise** from
   the inductive decay $\langle k_\ell\rangle^{-\Lambda_p}$ of the cumulants. In these terms nothing has to be
   grouped, so the grouping obstruction of OPEN 6.3 does not arise.
3. **Second cutoff.** For each **fixed** decoration, a stem time whose resonance satisfies $|\Omega_v|>M_2/2$ can be
   integrated exactly. Taking absolute values gives $|\int e^{i\omega u}du|\le2/|\omega|$, so each tree gains
   $4/(\pi\delta L^{2\gamma}M_2)$. This holds uniformly in $M_2$, and there are no endpoint faces to estimate.

All losses are explicit powers $L^{O(PN_{p+1})}$ and fixed combinatorial factors. They are paid by $e^{-N_p}$ (in
$\mathcal E^{(1)}$) or by $2^{-N_{p+1}^4/2}$ (in $\mathcal E^{(2)}$). Since $N_p=N_{p+1}^{1600d^2}$, the result has
an extra factor $L^{-P}e^{-100N_{p+1}}$ beyond what (10.2) requires. **None of the $L^{(100d)^3P}$ budget is used.**

---

## 1. The statement proved

### Standing data

- Fix $0\le p\le\mathfrak D-1$. Assume the induction hypotheses available at T708: Proposition `propansatz` (1)–(4)
  for every $q\le p$ (T689–707).
- Write $\Lambda=\Lambda_{p+1}$, $N=N_{p+1}$, $\Lambda_p=40d\Lambda$ (T611), and $N_p=N^{1600d^2}$, $R_p=N^{40d}$
  (T612).
- The normalization is $\delta/(2L^{d-\gamma})$ per branching node (S§1).
- $\mathfrak X$ denotes the regular kernel $\mathfrak X_{\rm reg}$, i.e. the sum over flower trees of order $\ge1$
  (S§1, order-zero convention).
- The original trees have the orders of T2271 and T2273:
  - $1\le n_j\le N$ for $\mathfrak X$;
  - $N+1\le n_j\le 3N+1$ for $\mathfrak Y$ and $\mathfrak W$.

### Weights

For the $j$-th original tree let $B_j$ be its nonflower leaves and $\mathcal S_j$ its stem branching nodes other than
$\mathfrak f_j^{\rm pr}$. The three multiplier choices of S(1.1) are

$$
\text{(i) } w_j\equiv1,\qquad
\text{(ii) } w_j=H_{j,M_1}\ \text{(S(3.1))},\qquad
\text{(iii) } w_j=H_{j,M_1}V_{j,M_2}\ \text{(S(3.1), S(8.1))},
$$

with $M_1,M_2\ge L$ dyadic. In choice (iii) the supplement assumes $|k|\ge M_1^{10}$; this hypothesis is not used
below.

### Theorem R (weighted expansion remainders)

Let $P\ge1$ be an integer. Assume $\delta^{\nu}\le1/4$; this is implied by the standing choice $\delta^\nu\ll_11$ of
T615. Then there is $L_0=L_0(d,\gamma,P,\delta,\mathfrak D,\varphi_{\rm in})$ with the following property.

For $L\ge L_0$, $\mathfrak K\in\{\mathfrak X,\mathfrak Y,\mathfrak W\}$, $\zeta\in\{\pm\}$, $p<s<t<p+1$,
$k,k'\in\mathbb Z_L^d$, all dyadic $M_1,M_2\ge L$, and each multiplier choice (i)–(iii), the remainders of the
weighted moment expansion of $\mathbb E_p|\mathfrak K^{w}{}^{\zeta}_{kk'}(t,s)|^{2P}$ (defined in §2) satisfy

$$
|\mathcal E^{(1)}|+|\mathcal E^{(2)}|
\le\tfrac14\,L^{-P}e^{-100N}\,\langle k-\zeta k'\rangle^{-4\Lambda P}\,G(M_1,M_2),
\tag{R.1}
$$

where $G=1$, $M_1^{-80dP}$ or $M_1^{-80dP}M_2^{-P/9}$ respectively.

**Corollary (OPEN 10.2 exactly as stated).** Since $L^{-P}e^{-100N}\le\min(1,e^{-100N})\,L^{(100d)^3P}$, (R.1)
implies S(10.2) for all three multiplier choices, together with the extra factor $e^{-100N}$ for $\mathfrak Y$ and
$\mathfrak W$. The bound is uniform in $M_1,M_2$ (including arbitrarily large $M_2$), in $k,k',\zeta$, and in
$(t,s)$.

### Theorem R′ (general weights)

The proof uses only the following properties of the weights.

- **(W0)** $w_j$ is a deterministic function of the decoration of the $j$-th original tree, and $|w_j|\le1$.
- **(S1)** In choices (ii) and (iii), if $M_1>L$, then $w_j=0$ unless $\max_{\ell\in B_j}|k_\ell|>M_1/2$.
- **(S2)** In choice (iii), if $M_2>L$, then $w_j=0$ unless $\max_{v\in\mathcal S_j}|\Omega_v|>M_2/2$.

(R.1) holds for any weights with these properties. The constant $1/2$ in (S1)/(S2) may be replaced by any fixed
$c\in(0,1]$; this changes only constants absorbed into $L_0$.

**Lemma R.0. The concrete weights satisfy (W0)–(S2).**

- *Modulus of $H$.* We have $0\le A_{j,M}\le1$ for every $M$, so $|H_{j,M}|=|A_{j,M}-A_{j,M/2}|\le1$; for $M=L$,
  $H_{j,L}=A_{j,L}\in[0,1]$.
- *Support of $H$.* Suppose $M_1>L$ and $|k_\ell|\le M_1/2$ for all $\ell\in B_j$. Then
  $\chi(k_\ell/M_1)=\chi(k_\ell/(M_1/2))=1$, since $\chi=1$ on $|x|\le1$. Hence $A_{j,M_1}=A_{j,M_1/2}=1$ and
  $H_{j,M_1}=0$.
- *Modulus of $V$.* We have $U_{j,M}\in[0,1]$, so $|V_{j,M}|\le1$.
- *Support of $V$.* If $|\Omega_v|\le M_2/2$ for all $v\in\mathcal S_j$, then $\vartheta(\Omega_v/M_2)=
  \vartheta(\Omega_v/(M_2/2))=1$, since $\vartheta=1$ on $[-1,1]$. Hence $V_{j,M_2}=0$.
- *Products and conjugates.* The product in (iii) has modulus $\le1$ and both supports. The weights are real, so the
  conjugated copies carry the same weights. ∎

---

## 2. The weighted moment expansion and the exact definition of the remainders

### 2.1 Tree factors

We have $|\mathfrak K|^{2P}=\prod_{j=1}^{2P}\mathfrak K_{(j)}$, where $\mathfrak K_{(j)}$ is $\mathfrak K$ for odd
$j$ and $\overline{\mathfrak K}$ for even $j$. Thus the root signs are $(+,-,\dots)$; in a conjugated copy all node
signs flip, and in particular the flower sign is $-\zeta$.

For a $2P$-tuple $\mathbf T=(\mathcal T_1,\dots,\mathcal T_{2P})$ of flower trees in the ranges of §1, and leaf
momenta $k_{B_j}=(k_\ell)_{\ell\in B_j}\in(\mathbb Z_L^d)^{B_j}$, define

$$
\Phi_j(k_{B_j})=\Big(\frac{\delta}{2L^{d-\gamma}}\Big)^{n_j}\zeta(\mathcal T_j)\,\epsilon_{\mathscr D_j}\,
\mathbf 1[\mathscr D_j\text{ is a }(k,k')\text{-decoration}]\;w_j(\mathscr D_j)\;I_j(\mathscr D_j),
\tag{2.1}
$$

$$
I_j(\mathscr D_j)=\int_{\mathcal D_j}\prod_{\mathfrak n\in\mathcal N_j}e^{i\omega_{\mathfrak n}t_{\mathfrak n}}
\,\boldsymbol\delta(t_{\mathfrak f_j^{\rm pr}}-s)\prod_{\mathfrak n}dt_{\mathfrak n},
\qquad \omega_{\mathfrak n}=\pi\zeta_{\mathfrak n}\delta L^{2\gamma}\Omega_{\mathfrak n}.
\tag{2.2}
$$

The ingredients are as follows.

- $\mathscr D_j$ is the decoration determined by $k_{B_j}$ and $k_{\mathfrak f_j}=k'$ (T641).
- $\mathcal D_j=\{p<t_{\mathfrak n'}<t_{\mathfrak n}<t$ whenever $\mathfrak n'$ is a child of $\mathfrak n\}$ (T714).
- The Dirac factor is evaluated by substitution: $I_j$ is the integral over the remaining $n_j-1$ times with
  $t_{\mathfrak f_j^{\rm pr}}=s$ (T2264; S-Lemma 7.2 uses the same reading).
- $|\epsilon_{\mathscr D_j}|\le1$ (T646) and $|\zeta(\mathcal T_j)|=1$ (T630).

Then

$$
\mathfrak K^w_{(j)}=\sum_{\mathcal T_j}\sum_{k_{B_j}}\Phi_j(k_{B_j})\prod_{\ell\in B_j}a_{k_\ell}(p)^{\zeta_\ell}.
$$

The conjugation $a^{\zeta_\ell}$ at negative leaves is the convention displayed in T737; T712 and T2264 suppress it
from the notation.

### 2.2 Cumulant expansion

Expand $\mathbb E_p\prod_\ell a_{k_\ell}(p)^{\zeta_\ell}$ by the moment–cumulant inversion T573. Here
$\mathbb E_p=\mathbb E(\mathbf 1_{\mathcal F_p}\,\cdot)$; the inversion is a Möbius identity on the partition lattice
and holds for this functional (T576, T2345). The sum runs over partitions $\mathscr P$ of $B=\bigsqcup_jB_j$, with
$|B|=2n_0$ and $n_0=\sum_jn_j$. The block cumulants $\mathbb K_p(\beta)$, $\beta\in\mathscr P$, are as follows.

- **Unbalanced blocks.** $\mathbb K_p(\beta)=0$ exactly unless $\beta$ has half $+$ and half $-$ signs, by gauge
  invariance (T568, T576).
- **Pairs.** For $\beta=\{\ell,\ell'\}$ with $\zeta_\ell=+$,
  $\mathbb K_p(\beta)=\mathbf 1_{k_\ell=k_{\ell'}}(F_p+\mathscr E_p)(k_\ell)$ with $F_p=\varphi(\delta p)+\mathscr R_p$
  (T693). Write $\mathfrak m_\beta$ for the part with $F_p$ and $\mathfrak e_\beta$ for the part with $\mathscr E_p$.
- **Blocks with $|\beta|=2R'\ge4$.** We have $R'\le|B|/2\le P(6N+2)\le R_p$ for $L$ large, so T698 applies:
  $\mathbb K_p(\beta)=\mathfrak m_\beta+\mathfrak e_\beta$ with
  $\mathfrak m_\beta=\sum_{n'=0}^{N_p}\mathscr K_{p,n'}(\beta)$ (T702) and $\mathfrak e_\beta=\widetilde{\mathscr E}_p$.

### 2.3 Definition of the remainders

The supplement defines these (S-OPEN 10.2) by reference to T2288 and T2290. Their exact form, with the weights
retained as in S-Lemma 2.2, is

$$
\mathcal E^{(1)}=\sum_{\mathbf T}\sum_{\mathscr P}\sum_{k_B}\prod_j\Phi_j
\Big[\prod_{\beta\in\mathscr P}(\mathfrak m_\beta+\mathfrak e_\beta)-\prod_{\beta\in\mathscr P}\mathfrak m_\beta\Big],
\tag{2.3}
$$

$$
\mathcal E^{(2)}=\sum_{\mathbf T}\sum_{\mathscr P}\ \sum_{\substack{(n'_\beta)_{|\beta|\ge4},\ n'_\beta\le N_p\\ n_0+\sum_\beta n'_\beta>N^4}}
\ \sum_{k_B}\prod_j\Phi_j\prod_{|\beta|=2}\mathfrak m_\beta\prod_{|\beta|\ge4}\mathscr K_{p,n'_\beta}(\beta).
\tag{2.4}
$$

- $\mathcal E^{(1)}$ collects every term containing at least one ansatz error $\mathscr E_p$ or
  $\widetilde{\mathscr E}_p$ (T2288).
- $\mathcal E^{(2)}$ is the main-term contribution of total order $n(\mathcal G)=n_0+\sum_\beta n'_\beta>N^4$ (T2290).
  Expanding $\mathscr K_{p,n'}$ into its gardens (T702) and assembling them with the original trees gives exactly
  $\widetilde{\mathcal K}_{\mathcal G}$ for a garden $\mathcal G\in\mathscr H^{\rm tr}_{p+1}$ of order
  $n_0+\sum n'_\beta$ (T2261, T2288; S-Lemma 2.2). This is the bookkeeping by which the time domain of T673
  factorizes:
  - every lower-layer node has time $<p$;
  - every original node has time $>p$;
  - so the cross-layer ordering constraints are automatic.

By S-Lemma 2.2 (weighted form),

$$
\mathbb E_p|\mathfrak K^w|^{2P}=\sum_{\mathcal G\in\mathscr H_{p+1}^{\rm tr},\ n(\mathcal G)\le N^4}\widetilde{\mathcal K}^w_{\mathcal G}+\mathcal E^{(1)}+\mathcal E^{(2)}.
$$

Only the estimate of $\mathcal E^{(1)},\mathcal E^{(2)}$ is at issue here; the identity is S-Lemma 2.2. See §8.1 for
the absolute convergence it needs.

---

## 3. Inputs, with lines

| Label | Statement used | Source |
|---|---|---|
| (H1) | $\|\mathscr R_p\|_{\mathfrak S^{\Lambda_p,\Lambda_p}}\le L^{-\theta_p}\le1$ and $|\mathscr E_p(k)|\le\langle k\rangle^{-\Lambda_p}e^{-N_p}$ | T695 |
| (H2) | $|\widetilde{\mathscr E}_p|\le\prod_i\langle k_i\rangle^{-\Lambda_p}e^{-N_p}$ for $2\le R'\le R_p$ | T698–700 |
| (H3) | $|\mathscr K_{p,n}|\le\prod_i\langle k_i\rangle^{-\Lambda_p}L^{-(R'-1)/6}\delta^{\nu n}$, $n\le N_p$ | T702–705 |
| (H4) | $C_\varphi:=\sup_{0\le\tau\le\tau_*}\sup_k\langle k\rangle^{\Lambda_0}|\varphi(\tau,k)|<\infty$, a $C_2$-constant | T598, T606–610 (see below) |
| (P) | $N_p=R_p^{40d}$, $R_{p}=N_{p+1}^{40d}$, $R_{\mathfrak D}=\lfloor(\log L)^{40d}\rfloor$; $\Lambda_p=(40d)^{\mathfrak D-p+1}$ | T611–612 |
| (C) | Signed conservation $\zeta_{\mathfrak n}k_{\mathfrak n}=\sum_{\text{children}}\zeta_ck_c$; $|\mathcal L|=2n+1$ | T641, T628 |

**On (H4).**

- $\varphi$ is the Schwartz-class solution on $[0,\tau_{\max})\ni\tau_*$ (T598, T606). Its Schwartz seminorms are
  uniformly bounded on the compact interval $[0,\tau_*]$; T757 uses the same fact when it asserts
  $\|\mathcal U_0\|_{\mathfrak S^{4\Lambda_{p+1},4\Lambda_{p+1}}}\le C_2$.
- An equivalent route uses T753–757 one step earlier, for $p\ge1$: $\|\varphi(p\delta)\|_{\mathfrak S^{4\Lambda_p,4\Lambda_p}}\le\sum_n C_2(C_1\delta)^n\le2C_2$. For $p=0$ use $\varphi_{\rm in}\in\mathscr S$.
- **Only decay of order $4\Lambda+81d+1<\Lambda_p$ is used.**
- Define

$$
C_F:=1+C_\varphi,\qquad\text{so } |F_p(k)|\le C_F\langle k\rangle^{-\Lambda_p}.
$$

---

## 4. Lemmas

### Lemma R.1 — Time integrals (plain pattern)

For every decoration, $|I_j|\le1$. Moreover

$$
|I_j|\le 2/|\omega_v|\qquad\text{for every }v\in\mathcal N_j\setminus\{\mathfrak f_j^{\rm pr}\}.
$$

Consequently, if (S2) holds, $M_2>L$ and $w_j(\mathscr D_j)\ne0$, then

$$
|I_j|\le\frac{4}{\pi\delta L^{2\gamma}M_2}.
\tag{R.2}
$$

**Proof.** After the Dirac substitution, $I_j$ integrates a function of modulus $1$ over a subset of
$(p,t)^{n_j-1}$. Since $t-p<1$, its volume is at most $1$; this gives the first bound.

Fix $v\ne\mathfrak f_j^{\rm pr}$. The only constraints in $\mathcal D_j$ involving $t_v$ are:

- $t_v>t_c$ for each branching child $c$ of $v$; if $c=\mathfrak f^{\rm pr}_j$, then $t_c=s$;
- $t_v>p$;
- $t_v<t_{v^{\rm pr}}$, or $t_v<t$ if $v$ is the root.

So, for fixed values of the other times, the admissible set of $t_v$ is an interval $(A_v,B_v)$, possibly empty.
The integrand depends on $t_v$ only through $e^{i\omega_vt_v}$, because the weights and $\epsilon$ do not depend on
times. By Fubini,

$$
|I_j|\le\int\Big|\int_{A_v}^{B_v}e^{i\omega_vu}\,du\Big|\,\prod_{\mathfrak n\ne v,\mathfrak f_j^{\rm pr}}dt_{\mathfrak n}
\le\frac{2}{|\omega_v|}\cdot1,
$$

since $|(e^{i\omega B}-e^{i\omega A})/(i\omega)|\le2/|\omega|$ and the remaining volume is at most $1$.

Under (S2) with $w_j\ne0$, some $v\in\mathcal S_j$ has $|\Omega_v|>M_2/2$, and $v\ne\mathfrak f^{\rm pr}_j$ by the
definition of $\mathcal S_j$. Then $|\omega_v|=\pi\delta L^{2\gamma}|\Omega_v|>\pi\delta L^{2\gamma}M_2/2$, which
gives (R.2). ∎

This is applied **for each fixed decoration**, before the decoration sum. The vertex $v$ may depend on the
decoration, and no smooth selection (S(6.1)-type) or face decomposition (S-Lemma 9.1) is needed. Absolute values
are legitimate here because the whole remainder is estimated in absolute value; S-Lemma 9.4 is the relevant
permission.

### Lemma R.2 — Pointwise extraction of external decay and of $M_1$

Let $\widetilde M_1:=M_1$ in choices (ii)/(iii) with $M_1>L$, and $\widetilde M_1:=1$ otherwise. For every decoration
of the $2P$ original trees with roots $k$ and flowers $k'$,

$$
\langle k-\zeta k'\rangle^{4\Lambda P}\,\widetilde M_1^{\,80dP}\prod_j\mathbf 1[w_j\ne0]
\le K_0\prod_{\ell\in B}\langle k_\ell\rangle^{2\Lambda+40d},
\qquad K_0:=2^{80dP}\prod_{j}(2n_j)^{2\Lambda}.
\tag{R.3}
$$

**Proof.** Iterating (C) from the root gives the signed leaf sum. For an unconjugated tree (root sign $+$, flower
sign $\zeta$) it reads $k-\zeta k'=\sum_{\ell\in B_j}\zeta_\ell k_\ell$. For a conjugated tree it reads
$k-\zeta k'=-\sum_{\ell\in B_j}\zeta_\ell k_\ell$; this is S(6.4).

Since $|B_j|=2n_j\ge2$ and $\langle mx\rangle\le m\langle x\rangle$ for $m\ge1$,

$$
\langle k-\zeta k'\rangle\le|B_j|\max_{\ell\in B_j}\langle k_\ell\rangle\le 2n_j\prod_{\ell\in B_j}\langle k_\ell\rangle.
$$

If $\widetilde M_1=M_1$ and $w_j\ne0$, then (S1) gives $\ell\in B_j$ with $\langle k_\ell\rangle\ge|k_\ell|>M_1/2$.
Hence

$$
M_1^{40d}\le2^{40d}\prod_{\ell\in B_j}\langle k_\ell\rangle^{40d}.
$$

Raise the first bound to the power $2\Lambda$, multiply by the second, and take the product over $j$. The sets $B_j$
are disjoint, so each leaf is charged at most $2\Lambda+40d$. ∎

### Lemma R.3 — Block factors

Let $\beta$ be a balanced block. The factors appearing in (2.3)–(2.4) obey the following bounds.

| Block | Factor | Bound |
|---|---|---|
| Pair $\{\ell,\ell'\}$ | $\mathfrak m_\beta$ | $C_F\,\mathbf 1_{k_\ell=k_{\ell'}}\langle k_\ell\rangle^{-\Lambda_p}$ |
| Pair $\{\ell,\ell'\}$ | $\mathfrak e_\beta$ | $e^{-N_p}\,\mathbf 1_{k_\ell=k_{\ell'}}\langle k_\ell\rangle^{-\Lambda_p}$ |
| $\lvert\beta\rvert\ge4$ | $\mathscr K_{p,n'}(\beta)$ | $\delta^{\nu n'}\prod_{\ell\in\beta}\langle k_\ell\rangle^{-\Lambda_p}$ |
| $\lvert\beta\rvert\ge4$ | $\mathfrak m_\beta$ | $2\prod_{\ell\in\beta}\langle k_\ell\rangle^{-\Lambda_p}$ |
| $\lvert\beta\rvert\ge4$ | $\mathfrak e_\beta$ | $e^{-N_p}\prod_{\ell\in\beta}\langle k_\ell\rangle^{-\Lambda_p}$ |

**Proof.**

- *Pairs.* These follow from (H1), (H4) and T693.
- *Fixed-order blocks.* (H3) applies with $L^{-(R'-1)/6}\le1$.
- *Main part of a higher block.* $|\mathfrak m_\beta|\le\sum_{n'\le N_p}\delta^{\nu n'}\prod\langle k_\ell\rangle^{-\Lambda_p}$,
  and $\sum_{n'}\delta^{\nu n'}\le(1-\delta^\nu)^{-1}\le2$.
- *Error part of a higher block.* This is (H2). ∎

### Lemma R.4 — The decoration sum for fixed $(\mathbf T,\mathscr P)$

Put

$$
\tau_j:=\frac{4}{\pi\delta L^{2\gamma}M_2}\ \text{ in choice (iii) with }M_2>L,\qquad \tau_j:=1\ \text{ otherwise}.
$$

Let $c_\beta$ be any of the factors in Lemma R.3, with constant $\gamma_\beta\in\{C_F,2,e^{-N_p},\delta^{\nu n'}\}$.
Assume (L2) of §5. Then

$$
\sum_{k_B}\prod_j|\Phi_j|\prod_{\beta}|c_\beta|
\le\langle k-\zeta k'\rangle^{-4\Lambda P}\,\widetilde M_1^{-80dP}\Big(\prod_j\tau_j\Big)\,K_0\,L^{(d+1)n_0}\prod_\beta\gamma_\beta .
\tag{R.4}
$$

**Proof.** By (2.1), (W0) and Lemma R.1,

$$
|\Phi_j|\le(\delta/2L^{d-\gamma})^{n_j}\,\mathbf 1[w_j\ne0]\,\tau_j .
$$

Multiply and divide by $\langle k-\zeta k'\rangle^{4\Lambda P}\widetilde M_1^{80dP}$ and apply (R.3). Then drop the
root indicators in (2.1). They are $\le1$ and all summands are now nonnegative, so this gives an upper bound.

The resulting sum factorizes over the free variables:

- one variable per pair, with exponent $-\Lambda_p+2(2\Lambda+40d)$;
- one variable per leaf of a higher block, with exponent $-\Lambda_p+2\Lambda+40d$.

Since $\Lambda\ge40d$ (because $p\le\mathfrak D-1$),

$$
\Lambda_p-4\Lambda-80d=(40d-4)\Lambda-80d\ge1600d^2-240d\ge d+1 .
$$

So each variable contributes at most

$$
S_d:=\sum_{x\in\mathbb Z_L^d}\langle x\rangle^{-(d+1)}\le C_dL^d .
$$

This is a Riemann-sum comparison with $L^d\int\langle z\rangle^{-(d+1)}dz$, using $\mathbb Z_L^d=(L^{-1}\mathbb Z)^d$
(T285). There are at most $|B|=2n_0$ variables and $S_d\ge1$, hence the total factor is

$$
(\delta/2)^{n_0}L^{-(d-\gamma)n_0}S_d^{2n_0}\le(\delta C_d^2L^{d+\gamma}/2)^{n_0}\le L^{(d+1)n_0}
$$

by (L2). ∎

### Lemma R.5 — Counts

1. **Tree tuples.** The number of tuples $\mathbf T$ is at most $\mathsf T:=[(3N+1)(6N+3)8^{3N+1}]^{2P}$. A ternary
   tree of order $n$ is one of at most $\binom{3n}{n}/(2n+1)\le8^n$ shapes, and the flower is one of $2n+1$ leaves.
2. **Partitions.** The number of partitions of $B$ is at most $|B|^{|B|}\le(2n_{\max})^{2n_{\max}}$.
3. **Blocks.** The number of blocks satisfies $|\mathscr P|\le n_0$. The number $h$ of blocks of size $\ge4$
   satisfies $h\le n_0/2$.

Here

$$
n_{\max}:=2P(3N+1)\le8PN .
$$

---

## 5. Proof of Theorem R

Thresholds on $L$ are taken in this order: after $P$, $\delta$, and the $C_2$-constants $\mathfrak D,\Lambda,C_F$.

- **(L1)** $\delta L^{2\gamma}\ge2$.
- **(L2)** $\delta C_d^2\le2L^{1-\gamma}$.
- **(L3)** $P(6N+2)\le R_p$ and $n_{\max}\le N^4/2$.
- **(L4)** $\log L\le N$. This holds once $L\ge e^{e}$, since
  $N\ge N_{\mathfrak D}=\lfloor(\log L)^{40d}\rfloor^{40d}$, by (P) and because $N_q$ decreases in $q$.
- **(L5)** $\Xi\le8(d+2)PN^2$, where $\Xi$ is defined below. This holds for $N\ge N_\sharp(P,d,\Lambda,C_F)$.
- **(L6)** $e^{8(d+2)PN^2}\big(e^{-N_p}+2^{-N^4/2}\big)\le\frac14L^{-(80d+2)P}e^{-100N}$. This holds for large $L$:
  by (L4) the right side is $\ge\frac14e^{-(80d+2)PN-100N}$, and $N_p\ge N^{1600}$.

Each threshold can be met by taking $L$ large depending only on $(d,\gamma,P,\delta,\mathfrak D,\varphi_{\rm in})$.

### Bound for $\mathcal E^{(1)}$

Expand the bracket in (2.3) as $\sum_{\emptyset\ne\mathscr S\subset\mathscr P}\prod_{\beta\in\mathscr S}\mathfrak e_\beta\prod_{\beta\notin\mathscr S}\mathfrak m_\beta$.
Each term has at least one factor $e^{-N_p}$, and its other constants are at most $C_F':=\max(C_F,2)$. By (R.4),

$$
|\mathcal E^{(1)}|\le\langle k-\zeta k'\rangle^{-4\Lambda P}\widetilde M_1^{-80dP}\prod_j\tau_j\cdot
\sum_{\mathbf T}\sum_{\mathscr P}2^{|\mathscr P|}C_F'^{|\mathscr P|}K_0L^{(d+1)n_0}\,e^{-N_p}
\le\langle k-\zeta k'\rangle^{-4\Lambda P}\widetilde M_1^{-80dP}\prod_j\tau_j\cdot e^{\Xi-N_p},
$$

where, by Lemma R.5 and $K_0\le2^{80dP}(6N+2)^{4\Lambda P}$,

$$
\Xi:=\log\mathsf T+2n_{\max}\log(2n_{\max})+n_{\max}\log(2C_F')+80dP\log2+4\Lambda P\log(6N+2)+(d+1)n_{\max}\log L .
$$

With $n_{\max}\le8PN$ and (L4), the last term is at most $8(d+1)PN^2$. Every other term is $O_{P,\Lambda,C_F}(N\log N)$.
This is (L5).

### Bound for $\mathcal E^{(2)}$

Fix $(\mathbf T,\mathscr P)$ and let $h\ge1$ be the number of blocks of size $\ge4$; if $h=0$ the inner sum in (2.4)
is empty. The constraint is

$$
\sum_\beta n'_\beta\ge m_0:=N^4+1-n_0\ge N^4/2,
$$

by (L3). The number of $h$-tuples of nonnegative integers with sum $m$ is
$\binom{m+h-1}{h-1}\le2^{m+h-1}$. Hence, since $2\delta^\nu\le1/2$,

$$
\sum_{\sum n'_\beta\ge m_0}\prod_\beta\delta^{\nu n'_\beta}\le2^{h-1}\sum_{m\ge m_0}(2\delta^\nu)^m\le2^{h}(2\delta^\nu)^{m_0}\le2^{h}2^{-N^4/2}.
$$

With (R.4), the pair constants $C_F$ and $h\le n_0/2$,

$$
|\mathcal E^{(2)}|\le\langle k-\zeta k'\rangle^{-4\Lambda P}\widetilde M_1^{-80dP}\prod_j\tau_j\cdot e^{\Xi}\,2^{-N^4/2}.
$$

### Conclusion

By (L5) and (L6),

$$
|\mathcal E^{(1)}|+|\mathcal E^{(2)}|\le\tfrac14L^{-(80d+2)P}e^{-100N}\,\langle k-\zeta k'\rangle^{-4\Lambda P}\widetilde M_1^{-80dP}\prod_j\tau_j .
$$

Compare with (R.1) case by case.

- **Choice (i).** $G=1$, $\widetilde M_1=1$, $\tau_j=1$; the extra $L^{-(80d+1)P}\le1$ is discarded.
- **Choice (ii).**
  - If $M_1>L$: $\widetilde M_1^{-80dP}=M_1^{-80dP}=G$.
  - If $M_1=L$: $G=L^{-80dP}$, which is paid from $L^{-(80d+2)P}$.
- **Choice (iii).** The $M_1$ part is as in (ii).
  - If $M_2>L$: by (L1), $4/(\pi\delta L^{2\gamma})\le2/\pi<1$. So $\prod_j\tau_j\le M_2^{-2P}\le M_2^{-P/9}$,
    since $M_2\ge1$.
  - If $M_2=L$: the factor $L^{-P/9}$ is paid from the margin, since $80d+2\ge80d+1+\tfrac19$.

In every case the margin $L^{-P}$ of (R.1) remains. This proves (R.1), and hence S(10.2). ∎

---

## 6. Why no forbidden loss occurs, and the quantifier order

### No $L^{Cn}$ loss against $\delta^{2\nu n}$

The only $L$-powers are $L^{(d+1)n_0}$ (decoration counting) and the bottom-block payments
$L^{80dP}$, $L^{P/9}$. The original order $n_0$ is **bounded** by $n_{\max}=2P(3N+1)$; nothing here sums over an
unbounded order range against $\delta^{2\nu n}$.

The lower-layer insertions, of total order up to $\sim PN\cdot N_p$, are **never expanded**. Their sums are bounded
as wholes by the induction hypotheses (H2)/(H3), at no $L$-cost and with the gain $\delta^{\nu n'}$.

The superpolynomial factors $e^{-N_p}=e^{-N^{1600d^2}}$ and $2^{-N^4/2}$ dominate $e^{O(N^2)}$. This is exactly the
mechanism of T804 and T807, where $L^{20R_{p+1}N_{p+1}}$ is paid by $e^{-N_p}$, respectively $e^{-N_{p+1}^2}$.

### Exponential bases

There are three sources of exponential factors.

- Factors exponential in the original order ($8^{n}$, $C_F^{|\mathscr P|}$, $2^{|\mathscr P|}$) involve bounded
  orders only. They are absorbed at fixed $L$ by $e^{-N_p}$ or $2^{-N^4/2}$. No geometric series in $n$ with a
  $\delta$-dependent base appears as a loss.
- The only order series are $\sum_{n'}\delta^{\nu n'}\le2$ and $\sum_m(2\delta^\nu)^m$. Both are gains, and they
  need only $\delta^\nu\le1/4$, which is independent of $P$.
- The Proposition 10.3 requirement that $D_P$ be independent of $\delta$ concerns (10.3), the main term. Theorem R
  imposes nothing on it.

### Quantifier order

The order is $C_0,\eta,C_1,\nu,\delta$, then $P$ (any $P\ge1$ works), then $C_2$ (that is $\mathfrak D$, $\Lambda$,
$C_F$), then $L$. $P$ is never chosen after $\delta$, and no constant depending on $L$ enters a lower-level choice.

### Gains retained

The remainders never enter the `layergarden` reductions. The main term
$\sum_{n(\mathcal G)\le N^4}\widetilde{\mathcal K}^w_{\mathcal G}$, which contains no ansatz error factor, is exactly
the object handed to OPEN 6.3/7.3/7.5/8.2. Its unmarked incoherent objects, bad vines and ladders are untouched, so
Theorem R neither uses nor removes any of their gains.

---

## 7. Loss accounting

| Operation in the remainders | Factor (numerical) | Charged to |
|---|---|---|
| Normalization and decoration count, per original branching node | $(\delta/2)L^{-(d-\gamma)}\cdot(C_dL^{d})^2\le L^{d+1}$; total $\le L^{(d+1)n_0}\le L^{8(d+1)PN_{p+1}}$ | $e^{-N_p}$ ($\mathcal E^{(1)}$), $2^{-N^4/2}$ ($\mathcal E^{(2)}$) |
| External decay $\langle k-\zeta k'\rangle^{-4\Lambda P}$ | $K_0\le2^{80dP}(6N+2)^{4\Lambda P}$ (no $L$); $\le2\Lambda$ powers per leaf | same, after (L4) |
| First cutoff $M_1^{-80dP}$ (nonbottom) | $2^{80dP}$ (no $L$); $\le40d$ powers per leaf | same |
| Per-input decay budget | pair: $4\Lambda+80d+(d+1)\le\Lambda_p=40d\Lambda$ | inductive decay (H1)/(H4) |
| Second cutoff $M_2^{-P/9}$ (nonbottom) | **gain** $\prod_j4/(\pi\delta L^{2\gamma}M_2)\le M_2^{-2P}$ | time integration, Lemma R.1 |
| Bottom first block ($M_1=L$) | $L^{80dP}$ | the margin $L^{-(80d+2)P}$ |
| Bottom second block ($M_2=L$) | $L^{P/9}$ | the margin $L^{-(80d+2)P}$ |
| Combinatorics (trees, flowers, partitions, error subsets, constants) | $e^{O_{P,\Lambda,C_F}(N\log N)}$, no $L$ | $e^{-N_p}$, $2^{-N^4/2}$ |
| Endpoint faces of selected times | none (absolute bound $2/\lvert\omega\rvert$) | — |
| **Net use of the $L^{(100d)^3P}$ budget** | **0**; the result carries an extra $\tfrac14L^{-P}e^{-100N_{p+1}}$ | — |

**Consequences for the S§10 table and (10.4).**

- The row "Expansion errors | Exact weighted identity only | OPEN 10.2" becomes "Theorem R: $\le\frac14L^{-P}e^{-100N}\times$ RHS of (1.1); no $L$-budget".
- $B$ in (10.4) is unaffected.
- In the proof of S-Proposition 10.3, the step "Add (10.2)" now uses (R.1): main part $\le\frac12$ RHS, remainders
  $\le\frac14$ RHS.
- For $\mathfrak Y$ and $\mathfrak W$ the needed $e^{-100N}$ is present. For $\mathfrak X$ it is a bonus.

---

## 8. Remarks

### 8.1 The identity and absolute convergence

The splitting in §2.3 is S-Lemma 2.2, which is proved in the supplement and is not part of OPEN 10.2.

Lemma R.4 shows, as a by-product, that every series in (2.3)–(2.4) converges absolutely. For each
$(\mathbf T,\mathscr P)$, $\sum_{k_B}\prod|\Phi_j|\prod|c_\beta|<\infty$.

The interchange $\mathbb E_p\sum_{k_B}=\sum_{k_B}\mathbb E_p$ used in that lemma needs a dominating bound:

- **$p=0$.** The data are Gaussian (T292–294). Hölder gives
  $\mathbb E\prod_{\ell\in B}|a_{k_\ell}(0)|\le C_{|B|}\prod_\ell\varphi_{\rm in}(k_\ell)^{1/2}$, which is summable.
- **$p\ge1$.** On $\mathcal F_p$, which T796 constructs from Proposition `fixedpoint` at level $p-1$, one has
  $|a_k(p)|\le|a^{\rm tr}_k(p)|+|b_k(p)|\le2\langle k\rangle^{-(5/4)\Lambda_p}e^{3N_p}$ by T782 and T793.

This is recorded for completeness. It is a hypothesis of S-Lemma 2.2, not of Theorem R.

### 8.2 $|k|\ge M_1^{10}$ and SG/LF issues

Theorem R does not use $|k|\ge M_1^{10}$, LF twisting, or Lemma 9.2. In the remainders no twist class is formed.

### 8.3 Normalization

Theorem R is insensitive to the $d-1$ versus $d-\gamma$ issue of S§1. With T2264's printed $L^{-(d-1)}$ the
per-node factor becomes at most $L^{d+2}$, which is absorbed identically.

### 8.4 Derivative patterns and $\dagger$ (beyond OPEN 10.2 as stated)

This remark is for the frozen gate `layergardenFlower_v3`, whose clause (D1) leaves the expansion errors to
T.flowerest1 and T.fp.part1. Its fixed-time patterns `FixPat` are `dRoot`, `dParent` and `dChild i`, and it has a
$\dagger$ variant that removes the $\mathfrak f^{\rm pr}$ phase and fixes the sibling momenta (T2312, T2327, T2331).
Each of these modifies $\Phi_j$ only as follows:

- it adds one more substituted time ($t$ or $s$); the integrand still has modulus $\le1$ and the remaining volume is
  still $\le1$;
- it adds a deterministic indicator weight in $\{0,1\}$, or removes a unimodular phase.

So the first part of Lemma R.1 and Lemmas R.2–R.5 hold verbatim. Therefore (R.1) holds for every pattern vector, with
or without $\dagger$, with $G\in\{1,M_1^{-80dP}\}$, and with no use of the doubled allowance
$L^{2(100d)^3P}$.

- **When the $M_2$ factor also holds.** It holds whenever, in each tree, every vertex of $\mathcal S_j$ is
  unsubstituted and keeps its phase. This includes all plain patterns, with or without $\dagger$, because
  $\mathfrak f^{\rm pr}\notin\mathcal S_j$.
- **When it is not claimed.** It is not claimed for `dRoot` or `dParent`, where the substituted vertex lies in
  $\mathcal S_j$. This matches the frozen convention that the $M_2$ factor applies only when all patterns are plain.
  It is also all that T2330 needs, since the derivative term there carries $M_2^{-100P}$.
- **Out of scope.** A raw $\partial_s$ that differentiates the $\mathfrak f^{\rm pr}$ phase, without $\dagger$, is not
  a `FixPat` object, and this remark does not cover it.

---

## 9. Dependencies

| Source and lines | Use |
|---|---|
| T285 | $\mathbb Z_L^d=(L^{-1}\mathbb Z)^d$, lattice sum $S_d\le C_dL^d$ |
| T292–294 | Gaussian data at $p=0$ (§8.1 only) |
| T568–576 | Gauge vanishing of unbalanced cumulants; moment–cumulant inversion under $\mathcal F_p$ |
| T598, T606–610 | Schwartz solution $\varphi$, constant classes $C_1,C_2$; (H4) |
| T611–612 | $\Lambda_p=40d\Lambda_{p+1}$; $N_p=N_{p+1}^{1600d^2}$, $R_p=N_{p+1}^{40d}$, $R_{\mathfrak D}=\lfloor(\log L)^{40d}\rfloor$ |
| T615 | $\delta^\nu\ll_11$ |
| T628, T630, T641, T646–647 | Leaf count, signs, conservation, $|\epsilon|\le1$, $\Omega$ |
| T671–674 | Garden normalization and time domain; factorization in §2.3 |
| T689–707 | Induction hypotheses (H1)–(H3) |
| T708 | Induction set-up; $p=0$ trivial ($\mathscr E_0=\widetilde{\mathscr E}_0=0$, $\mathscr G_0=\varnothing$) |
| T711–715, T737 | Tree expressions, time domain, conjugation convention at negative leaves |
| T753–757 | Alternative route to (H4) |
| T782, T793, T796 | Bound on $a_k(p)$ under $\mathcal F_p$ (§8.1 only) |
| T803–807 | The unweighted remainder argument being extended |
| T2259–2273 | Flower trees and gardens, $\widetilde{\mathcal J}_{\mathcal T}$, $\mathfrak X,\mathfrak Y,\mathfrak W$, order ranges |
| T2279–2290 | `flowerest1` and its moment expansion, $\mathcal E^{(1)},\mathcal E^{(2)}$ |
| T2312, T2327, T2330–2331 | Derivative patterns and $\dagger$ (§8.4 only) |
| S§1, S(1.1) | Target bounds, normalization, order-zero convention |
| S(3.1), S(8.1) | Concrete cutoffs (Lemma R.0) |
| S-Lemma 2.2 | Weighted moment identity (§2.3) |
| S(6.4) | Signed conservation for $k-\zeta k'$ |
| S-Lemma 9.4 | Discarding modulus-$\le1$ factors after absolute values |
| S-Proposition 10.3 | Consumer of (R.1) |

D21 and D23 are not used. In particular, neither D21 Corollary 11.3 nor S-Lemma 9.1 is needed: the remainders allow
an absolute bound on the selected-time integral.

---

## 10. Remaining OPEN sub-items

None for OPEN 10.2. Theorem R proves S(10.2) exactly as stated, in the stronger form (R.1), for all three kernels
and all three multiplier choices, uniformly in $M_1,M_2,k,k',\zeta,(t,s)$.

The only outside inputs are:

- the induction hypotheses of T689–707, i.e. the "same induction hypotheses" the brief requires;
- the uniform Schwartz bound (H4) for $\varphi$;
- the identity S-Lemma 2.2.

OPEN 6.3, 7.3, 7.5 and 8.2 and the aggregate hypothesis (10.3)/(10.4) are unaffected.

STATUS: CLOSED
