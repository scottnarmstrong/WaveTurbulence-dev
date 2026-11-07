# RESOLUTION — OPEN 8.3 (upper M₂ resonance filters on the stem rungs of ladders)

Packet o83 (FLOWER-OPEN), for wt-orch, 2026-11-07. This file also contains the independent check of o75 Lemma F (§6) and
the answers to the Lean-plan risks R2 (§7) and R3 (§8).

**Pinned inputs** (sha256 checked at first read; copies were taken in the session scratchpad):

| File | sha256 |
|---|---|
| T = `WKE-Longer_times_Final_arXiv.tex` | `493eef6b…727cb` |
| D23 = `Revision_Submit.tex` | `c7e47dfa…35475` |
| S = `SUPPLEMENT-v1.md` | `ddd81fe1…74d7` |
| COMMON.md, o83/BRIEF.md | `a165bad5…`, `16074447…` |
| RR = `ref/REFEREE.md` (live draft, pinned) | `c31ee38a…d6d` |
| O63 = `o63/RESOLUTION.md` (live draft, pinned) | `c28aad09…2ad9`; revision 2 `a50e0f93…` re-read at the end (adds (G)/(U); see §5.3) |
| O75 = `o75/RESOLUTION.md` (live draft, pinned) | `d7102c43…74eb8` |
| E = `report/docs/ERRATA-AND-DEVIATIONS.md` (E4 L780–816, E5 L820–852) | `2d77a162…a140` |
| PLAN = `leanplan/PLAN.md` (§5, R2/R3) | `84a98ebf…17a6` |

"T n" are TARGET lines; "D23 n" are DH23 lines.

---

## 0. Result

**OPEN 8.3 is closed, as stated in §2 (Theorem 8.3 and Corollary 8.3.A).**

- **What is proved.** `ladderl1new` (T1978–1987) holds for ladders of $\mathbb M_{\rm sb}$ carrying arbitrary resonance
  filters $\psi_v(\Omega_{\mathfrak n(v)}/R_v)$, $R_v\ge1$, on any subset of their atoms. The bound is proved in the E5
  kernel-core form (time-$L^1$ over the unordered box), which is the form that the gluing into (finalsbest1) needs.
  - It is uniform in the boundary data, the scales and the layers.
  - The cost is $\mathfrak b(\psi_v)=\int(1+|\xi|)^2|\widehat{\psi_v}(\xi)|\,d\xi$ per filter. For the fixed Gevrey cutoff
    this is an absolute constant, independent of $\delta$ and $L$.
  - There is no power of $L$ per filter. The $L$-power per ladder is $L^{4\gamma+2}$, inside the source's $L^{20d}$.
  - Every incoherency gain of T is retained: $L^{-(\gamma_1-\sqrt\eta)}$ per incoherent double bond.
- **Mechanism.** It is the referee's route, made exact by o75 Lemma F. A Fourier-inverted filter is a time translation
  of one atom by $\tau_v=O(\xi/(\delta L^{2\gamma}R_v))$. In the kernel core the ordering is already dropped, so
  only the unit box is translated. The rung bounds use the box only through three properties, which survive the
  translation; the incoherency gain degrades by the factor $1+|\xi_v|+|\xi_w|$.
- **What had to be supplied.** T's proof of `ladderl1new` is a sketch (T1989: "We shall only sketch the proof here").
  E5 and Lemma F inherit four gaps from it, and Lemma F adds a fifth:
  - (G1) the kernel-core bound for translated boxes, which is not the statement of E5/`ladderL1Gate`;
  - (G2) the sharp SG/LG/ZG indicators $\mathcal Z_v$ inside the rung sums, to which Poisson summation does not apply;
  - (G3) the end rungs, where global conservation couples all rungs;
  - (G4) the enlarged `lemlayer2` window;
  - (G5) `lemlayer1` with a radius-4 bump.

  §4 proves all five.
- **o75 Lemma F (§6).** VERIFIED. Its mechanism is correct, its claim that the box enters only through
  (B1)–(B3) is correct, and translation commutes with the E5 repair. Its proof is complete once (G1)–(G5) are filled,
  as here. There is no obstruction.
- **R2 (§7).** CONFIRMED. Frontier $M_1$ cutoffs on Stage-2 ladder bonds are single-bond factors. They stay in the
  class of T1965 at cost $c_\chi$ per cutoff, at most two per bond, and they are not part of $\mathcal K^\dagger$, so
  T2081/T2083 is untouched.
- **R3 (§8).** COVERED. Every possible position of a stem vertex is listed with the item that handles it. Interior
  nodes of spliced SG vines cannot carry a stem filter (Lemma 9.2/T2300(7)). Interior nodes of LG vines, and of every
  other unspliced vine, are atoms of $\mathbb M_{\rm sb}$: ladder atoms are covered by Theorem 8.3, the other atoms by the
  trivial and absolute parts. The case $|k|<M_1^{10}$ does not arise: the $M_2$ clause assumes $|k|\ge M_1^{10}$ in T2285,
  in S (1.1), and in the frozen Lean clause `FlowerCaseAt`.

---

## 1. The gap (REFEREE M2), restated

If the stem leaves an SG-adjacent block through $\mathfrak u_{21}$ or $\mathfrak u_{22}$, the gap is large (S Lemma 9.2),
and the stem runs through the rung groups of the block's ladders (T1519). Those ladders are not spliced (only SG chains
of $\mathscr V_0$ are, T1944–1946), so they are maximal ladders of $\mathbb M_{\rm sb}$. (finalsbest1) (T2076) applies
`ladderl1new` to them (T2081). The surviving upper filters $\vartheta(\Omega_v/R)$ on stem atoms are amplitudes that
depend on the internal ladder variables quadratically ($\Gamma_v=2x_j\cdot y_j$, T1989). They are not single-bond
factors, so `ladderl1new` as stated does not apply. There can be $O(n)$ such atoms, so an $L$-loss per filter is not
allowed.

Lemma 9.3 covers only SG tops, Lemma 9.4 only the absolute counting stage (finalsbest2), OPEN 7.5 only $O(P)$ protected
atoms, and OPEN 8.2 only regular objects. T2299 gives no argument.

---

## 2. Statement

### 2.1 Setting and notation

- **The ladder.** $\mathbb L\subset\mathbb M_{\rm sb}$ is a ladder of length $m\ge1$ (T1384: $m+1$ double bonds,
  parallel single bonds of opposite directions). It contains no hinge atom (T1978) and, in the flower setting, no atom of
  the split set ($H\cup S_{\rm split}$ of O75 Theorem 7.5′(8), or the protected set of S OPEN 7.5).
  - Atoms: $v_0,\dots,v_m$ on one rail and $w_0,\dots,w_m$ on the other.
  - Double bond $\{v_j,w_j\}$ with momenta $a_j,b_j$.
  - Rail bonds $c_j$ (between $v_j,v_{j+1}$) and $d_j$ (between $w_j,w_{j+1}$), $0\le j\le m-1$.
  - Rungs $0$ and $m$ are the **end rungs**; rungs $1,\dots,m-1$ are **interior**.
  - The incoherency index $g$ is the number of $j$ with $\mathfrak L_{v_j}\ne\mathfrak L_{w_j}$ (T1489).
- **Boundary data.** The momenta of the at most four bonds joining $\mathbb L$ to the rest are fixed.
- **Bond factors.** $\mathcal K_{(\ell)}$, $\ell\in\mathbb L$, are supported in $|k-k_\ell^0|\le1$ and satisfy
  $\|\partial^\alpha\mathcal K_{(\ell)}\|_\infty\le A$ for $|\alpha|\le30d$. T1965 has $A=1$. With frontier cutoffs
  (§7), $A=c_\chi^2$.
- **Degeneracy and gap factors.**
  - $\epsilon_v$ is defined in T556–564.
  - $\mathcal Z_v$ is a product of at most four indicators $\mathbf 1_E(k_{\ell_1}-k_{\ell_2})$, with $(\ell_1,\ell_2)$ an
    opposite-direction pair at $v$ and $E\in\{\{0\},\{0<|z|\le L^{-\gamma+\eta}\},\{|z|>L^{-\gamma+\eta}\}\}$ (T1938, T1970).
    *Why at most four.* $\mathcal Z$ records the SG/LG/ZG type of the vine-like objects of the collection $\mathscr C$
    (T1944, T1970). These are disjoint atomic groups (Lemma `vinechainlem`, T1930), and each gap is read at one joint,
    so an atom carries $O(1)$ such indicators. Four is the number of opposite-direction pairs at a degree-4 atom. Only
    an absolute bound is needed, for $K_0$.
- **Phases.** $\alpha_v=\delta L^{2\gamma}(-\Gamma_v+\Gamma_v^0)+\xi_v$ (T1968, T1973, T2073), with
  $\zeta_{\mathfrak n(v)}\Omega_{\mathfrak n(v)}=-\Gamma_v+\Gamma_v^0$.
- **Filters.**
  - $F\subset\mathbb L$ is any set of atoms.
  - For $v\in F$, $\psi_v:\mathbb R\to\mathbb C$ is continuous with
    $$\mathfrak b(\psi):=\int_{\mathbb R}(1+|\xi|)^2|\widehat\psi(\xi)|\,d\xi<\infty,\qquad \widehat\psi(\xi)=\int\psi(u)e^{-2\pi i\xi u}du,$$
    and $R_v\ge1$.
  - Set $\mathfrak b(\psi_v):=1$ for $v\notin F$. Note $\|\psi\|_\infty\le\|\widehat\psi\|_1\le\mathfrak b(\psi)$.
  - Covered: $\psi=\vartheta$ (S §8, Gevrey-2, $0\le\vartheta\le1$), the frozen low-pass filter $\chi_0$, and the derivative
    profile $D_\vartheta(u)=-u\vartheta'(u)$. All three are $C_c^\infty$, so $\mathfrak b<\infty$, and $\mathfrak b$ is an
    absolute constant.
- **The kernel core (E5).** Let $\mathfrak B=\prod_{v\in\mathbb L}[\mathfrak L_v,\mathfrak L_v+1]$ be the layer box,
  with no ordering. Define
  $$
  \mathfrak K^\Psi(\mathbb L)=\Big(\frac{\delta}{2L^{d-\gamma}}\Big)^{2m+2}\int_{\mathfrak B}\Big|\sum_{k[\mathbb L]}\Phi\prod_{v\in F}\psi_v\big(\Omega_{\mathfrak n(v)}/R_v\big)\prod_{v\in\mathbb L}e^{\pi i\alpha_vt_v}\Big|\,dt,\qquad
  \Phi=\prod_{v\in\mathbb L}\epsilon_v\mathcal Z_v\prod_{\ell\in\mathbb L}\mathcal K_{(\ell)} .
  \tag{2.1}
  $$
  Here $k[\mathbb L]$ runs over the decorations of the internal bonds with the boundary data fixed. E5 and T1980 use
  the power $2m+1$; see Remark 2.2.
- **Constants.** $C_3,C_4,\dots$ depend only on $(d,\gamma)$ and the fixed bump $\phi$ of §4.2, so they are $C_0$-type.
  $L_0$ is a threshold depending on $(d,\gamma,\eta,\tau_*,\delta)$, so it is $C_2$-type. Neither depends on
  $m,F,(\psi_v),(R_v)$ or the boundary data.

### 2.2 Theorem 8.3 (filtered ladders; the statement of OPEN 8.3)

Let $d\ge3$ and $\tfrac12<\gamma<1$, with T's standing parameters (T600–613). There are $C_3=C_3(d,\gamma)$ and a
$C_2$-type $L_0$ such that, for $L\ge L_0$ and every ladder, filter set, filter family, boundary data, centres
$k^0_\ell$, parameters $\xi_v$ and layers as in §2.1,
$$
\mathfrak K^\Psi(\mathbb L)\le A^{4m+2}\,(C_3\delta)^m\,\Big(\prod_{v\in F}\mathfrak b(\psi_v)\Big)\,L^{-(\gamma_1-\sqrt\eta)g}\;\delta^3L^{4\gamma+2}.
\tag{2.2}
$$
For the time-ordered local kernel $\mathcal K^{\mathbb L}_\Psi$ of T1978 (with the filters inserted), at any fixed
outside times,
$$
|\mathcal K^{\mathbb L}_\Psi|\le A^{4m+2}(C_1\delta)^m\Big(\prod_{v\in F}\mathfrak b(\psi_v)\Big)L^{-(\gamma_1-\sqrt\eta)g+20d}.
\tag{2.3}
$$
So (redladder2) holds with the extra factor $\prod_{v\in F}\mathfrak b(\psi_v)$.

**Remark 2.1 (form).** (2.2) is the form that is glued (E5 steps 2–4). Filters at atoms of $\mathbb L$ depend only on
bonds at those atoms, i.e. on internal bonds and boundary bonds. So the filtered ladder weight is local in the sense of
E5 step 2, and the filtered kernel cores are multiplicative over disjoint hinge-free ladders.

**Remark 2.2 (normalization).** $\mathbb L$ has $2m+2$ atoms. With T's printed power $2m+1$, (2.2) is multiplied by
$2L^{d-\gamma}/\delta$. The result, $A^{4m+2}(C_3\delta)^m\prod\mathfrak b\,L^{-(\gamma_1-\sqrt\eta)g}\cdot2\delta^2L^{d+3\gamma+2}$,
is still at most $L^{20d}$ times the main factor. That is (2.3).

### 2.3 Corollary 8.3.A (filtered Stage 2 bounds)

Let $\mathcal K^\Psi_{\mathcal G_{\rm sb}}$ be (redvine3) (T1973) with $\prod_{v\in F}\psi_v(\Omega_{\mathfrak n(v)}/R_v)$
inserted, where $F$ is any set of non-hinge atoms of $\mathbb M_{\rm sb}$. In the flower setting the protected atoms
are handled by OPEN 7.3/8.2, or by O75. Then:

1. (finalsbest1) (T2076) holds with the extra factor $\prod_{v\in F}\mathfrak b(\psi_v)$. This holds in its E5 form,
   with ladders split at hinges, and also in O75's form (8), split at $H\cup S_{\rm split}$.
2. (finalsbest2) (T2078) holds with the extra factor $\prod_{v\in F}\|\psi_v\|_\infty$, which is at most $1$ for
   $\vartheta,\chi_0$.
3. (finalproof1)/(finalproof2) (T2221–2225) hold with the extra factor $\prod_{v\in F}\mathfrak b(\psi_v)^{\theta}\le\mathfrak b_*^{\theta|F|}$.
   Here $\theta=40\nu/(1+20\nu)$ and $\mathfrak b_*:=\max(1,\mathfrak b(\vartheta),\mathfrak b(\chi_0),\mathfrak b(D_\vartheta))$.
   Since $|F|\le n$, this changes $C_1$ into $C_1\mathfrak b_*^{\theta}\le C_1\mathfrak b_*$ in T2225 and T2253. That is a
   $\delta$-independent base.
4. All bounds are uniform over real layer-indexed profile tuples in $\mathcal P(C_1)$ (O63 §1.2, interface I-6.3). The
   reason is given in §5.3.

---

## 3. Overview of the proof

1. **Lemma P (§4.1).** Describes the decorations of a ladder:
   - a universal bilinear identity for $\Gamma$ at a degree-4 atom;
   - rung variables $(x_j,y_j)$ with $\Gamma_{v_j}=2x_j\cdot y_j$ and $\Gamma_{w_j}=-2x_j\cdot y_j+(\text{affine in }(x_j,y_j))$;
   - after fixing the two end double bonds, a bijection with interior rung variables subject to one linear constraint;
   - every $\epsilon$- and $\mathcal Z$-condition is a ball condition on a single shifted rung variable $x_j+\theta r$ or $y_j+\theta r$.
2. **Lemma S (§4.2).** The two exponential-sum inputs: `lemlayer1` with a bump, and the weighted DH23 Lemma 6.6(2).
3. **Lemma R (§4.3).** Bounds one rung on arbitrary unit time intervals $I,J\subset[-1,\mathrm D+1]$:
   $$\mathfrak M\le C_4\delta^{-1}L^{2(d-\gamma)}\min\{1,\,L^{-(\gamma_1-\sqrt\eta)}+|I\cap J|\}.$$
   The $\epsilon,\mathcal Z$ indicators are included. This is the box-robust core.
4. **Theorem K (§4.4).** Box-robust kernel core: a product of Lemma R over interior rungs, times $L^{4d}$ for the end
   rungs. The constraint is resolved by a mass-one character average (the device of E4).
5. **Lemma T (§4.5).** A filter is a translation of the box (o75 Lemma F, Step 1).
6. **Proof of Theorem 8.3 (§4.6).** Integrate Theorem K over the filter frequencies.

---

## 4. Proofs

### 4.1 Lemma P — structure of ladder decorations

**(P1) Universal identity.** Let an atom have degree $4$ with $c_v=0$, outgoing momenta $p_1,p_2$ and incoming
$q_1,q_2$, so that $p_1+p_2=q_1+q_2$ (T1308). Put $x=p_1-q_1$ and $y=p_1-q_2$. Then
$$
\Gamma_v=|p_1|^2+|p_2|^2-|q_1|^2-|q_2|^2=2\,x\cdot y .
$$
- Every difference of two of the four momenta lies in $\{0,\pm x,\pm y,\pm(x+y),\pm(x-y)\}$.
- The differences of **opposite-direction** pairs are exactly $\pm x,\pm y$.
- Given any one of the four momenta, $(x,y)\in(\mathbb Z_L^d)^2$ parametrizes the solutions of the conservation law
  bijectively.

*Proof.* Substitute $q_1=p_1-x$, $q_2=p_1-y$, $p_2=p_1-x-y$:
$$\Gamma_v=|p_1|^2+|p_1-x-y|^2-|p_1-x|^2-|p_1-y|^2=|x+y|^2-|x|^2-|y|^2=2x\cdot y .$$
The pairwise differences are read off from these formulas, and the opposite pairs are $(p_i,q_k)$. (This is T564,
$\Omega=2\langle k_1-k,k-k_3\rangle$, in molecular form.) ∎

**(P2) Interior atoms.** For $1\le j\le m-1$, all four bonds at $v_j$ and at $w_j$ are internal to $\mathbb L$. So these
atoms have degree $4$, $c_v=0$, and $\Gamma^0_v=0$ (T1308, T1320: degree $<4$ only at root and root-paired atoms).

**(P3) Gap and the second atom of a rung.**
- **Directions.** A bond outgoing at one end is incoming at the other. For the parallel pair $(c_{j'},d_{j'})$, opposite
  directions (T1384) mean $\zeta_{w_j,d_{j'}}=-\zeta_{v_j,c_{j'}}$ for $j'\in\{j-1,j\}$.
- **Gap.** Adding the conservation laws at $v_j$ and $w_j$, the double bond cancels:
  $$\zeta_{v_j,c_{j-1}}(c_{j-1}-d_{j-1})+\zeta_{v_j,c_j}(c_j-d_j)=0 .$$
  So $r_j:=c_j-d_j=\pm r_{j-1}$, with a sign fixed by the directions. This is the gap $r$ of T1938, up to sign. Put
  $\rho_j:=\zeta_{v_j,c_j}r_j=-\zeta_{v_j,c_{j-1}}r_{j-1}$.
- **The second atom.** In $\Gamma_{v_j}+\Gamma_{w_j}$ the double bond again cancels, and
  $$
  \Gamma_{v_j}+\Gamma_{w_j}=\sum_{j'\in\{j-1,j\}}\zeta_{v_j,c_{j'}}\big(|c_{j'}|^2-|c_{j'}-r_{j'}|^2\big)=2\rho_j\cdot(c_j-c_{j-1})+\kappa_j,\qquad\kappa_j\in\{0,\pm2|r|^2\}.
  $$
- **Conclusion.** Let $(x_j,y_j)$ be the variables of (P1) at $v_j$. Then $c_j-c_{j-1}=\lambda_j(x_j,y_j)$, where $\lambda_j$
  is a fixed element of $\{\pm x,\pm y,\pm(x+y),\pm(x-y)\}$, and
  $$
  \Gamma_{v_j}=2x_j\cdot y_j,\qquad \Gamma_{w_j}=-2x_j\cdot y_j+2\rho_j\cdot\lambda_j(x_j,y_j)+\kappa_j .
  \tag{4.1}
  $$
  This is the form claimed at T1989 (with $\zeta_j=\pm\lambda_j$), now valid for every orientation.

**(P4) Parametrization with fixed end double bonds.**
- **End data.** Fix $(a_0,b_0)$ and $(a_m,b_m)$. At each of $v_0,w_0,v_m,w_m$, every other bond is either a boundary bond
  (fixed) or absent, in which case $c_v$ is fixed. So conservation there determines $c_0,d_0,c_{m-1},d_{m-1}$.
- **Interior rungs.** For $1\le j\le m-1$: given $c_{j-1}$, (P1) at $v_j$ gives a bijection from $(x_j,y_j)$ to the four
  momenta at $v_j$. Set $d_j=c_j-r_j$; then conservation at $w_j$ holds, by the sum identity in (P3).
- **The constraint.** Hence, for fixed end double bonds, the decorations of $\mathbb L$ are in bijection with the tuples
  $(x_j,y_j)_{j=1}^{m-1}$ that satisfy
  $$
  \sum_{j=1}^{m-1}\lambda_j(x_j,y_j)=c_{m-1}-c_0 ,
  \tag{4.2}
  $$
  together with a consistency condition on the end data alone ($d_{m-1}=c_{m-1}-r_{m-1}$). When that condition fails,
  the fibre is empty. For $m=1$ there are no interior rungs, and (4.2) is a condition on the end data.
- **Localization.** If every bond lies in its unit ball, then $|x_j-x_j^0|\le2$ and $|y_j-y_j^0|\le2$, where
  $x_j^0,y_j^0$ are the same differences of the centres $k_\ell^0$. Each end double bond takes at most $(C_dL^d)^2$
  values.

**(P5) The degeneracy and gap conditions at interior rungs.**
- **At $v_j$.** By the direction rule of T1297 (a child of sign $+$ gives an incoming bond, a child of sign $-$ an
  outgoing one; the parent bond is outgoing iff $\zeta_{\mathfrak n}=+$), the two conditions $k_2=k_1$ and $k_2=k_3$ in
  $\epsilon_v=1-\mathbf 1[k_2=k_1]-\mathbf 1[k_2=k_3]$ (T556) are equalities of opposite-direction pairs. By (P1) they
  read $z=0$ with $z\in\{\pm x_j,\pm y_j\}$. Every $\mathcal Z_{v_j}$-condition is a condition on such a $z$.
- **At $w_j$.** Its bonds are $a_j,b_j$, with directions reversed relative to $v_j$, and $d_{j'}=c_{j'}-r_{j'}$, with
  directions reversed relative to $c_{j'}$ at $v_j$. So the opposite-direction pairs at $w_j$ are the images of those at
  $v_j$, and their differences are $z+\theta r$ with $z\in\{\pm x_j,\pm y_j\}$ and $\theta\in\{0,\pm1,\pm2\}$.
- **Consequence.** $\epsilon_{v_j}\epsilon_{w_j}\mathcal Z_{v_j}\mathcal Z_{w_j}$ belongs to the class
  $$
  \mathcal W_r:=\Big\{\sum_i c_i\prod_k\mathbf 1_{\bar B(0,\rho_{ik})}(z_{ik})\Big\},\qquad \sum_i|c_i|\le K_0:=3^2\cdot2^8 .
  $$
  Here each $z_{ik}\in\{x_j+\theta r,\ y_j+\theta r\}$ and $0\le\rho_{ik}\le L^{-\gamma+\eta}$. For the expansion use
  $\mathbf 1[|z|>\rho]=1-\mathbf 1_{\bar B(0,\rho)}$, $\mathbf 1[0<|z|\le\rho]=\mathbf 1_{\bar B(0,\rho)}-\mathbf 1_{\bar B(0,0)}$,
  and the three terms of $\epsilon$; there are at most eight $\mathcal Z$-indicators per rung. The constant term (the
  empty product) has coefficient of modulus at most $1$; it is $0$ as soon as one $\mathcal Z$ is of SG or ZG type. ∎

### 4.2 Lemma S — two exponential-sum inputs

Fix $\phi\in C_c^\infty(B(0,4))$ with $\phi=1$ on $B(0,2)$ and $0\le\phi\le1$. Write $e(z)=e^{2\pi iz}$, and recall
$\mathbb Z_L^d=(L^{-1}\mathbb Z)^d$ (T287). Set
$$\Sigma_0(s)=\sum_{(x,y)\in\mathbb Z_L^{2d}}\phi(x-a)\phi(y-b)\,e(\langle x,\xi\rangle+\langle y,\xi'\rangle+s\langle x,y\rangle).$$

- **(S1)** For $|s|\le L$, uniformly in $(a,b,\xi,\xi')$, $|\Sigma_0(s)|\le C_\phi L^{2d}\langle s\rangle^{-d}$.
  - *Proof.* By Poisson summation, $\Sigma_0=L^{2d}\sum_{(g,h)\in\mathbb Z^{2d}}\int\phi\phi\,e[\langle\xi-Lg,x\rangle+\langle\xi'-Lh,y\rangle+s\langle x,y\rangle]$.
    Then apply `lemlayer1` (T958–968) with $\chi_0$ replaced by $\phi$.
  - That proof uses only smoothness and compact support of the cutoff: integration by parts in case (i) and stationary
    phase in case (ii). With support radius $4$, replace $10dL$ by $40dL$; case (ii) then has at most $(80d+1)^{2d}$
    terms. This is gap (G5).
- **(S2)** Let $P_\eta:=\lceil\eta^{-2}\rceil+1$. Uniformly in $(a,b,\xi,\xi')$,
  $$\int_{|s|\ge L}\langle s/(\delta L^{2\gamma})\rangle^{-P_\eta}|\Sigma_0(s)|\,ds\le C_{\phi,\eta}\,L^{2d-2(d-1)(1-\gamma)+\eta}.$$
  - *Proof.* This is DH23 Lemma 6.6(2) (D23 1076–1088) with $\lambda=8$ and $\Phi(s,x,y)=\mathbf 1_{|s|\ge L}\phi(x-a)\phi(y-b)$.
    Its $x,y$-derivatives up to order $10d$ are bounded by $C_\phi$; the $s$-dependence is arbitrary. Also
    $\chi_0((x-a)/8)=1$ on ${\rm supp}\,\phi(\cdot-a)$.
  - The case $\gamma\ge\frac12$ of that proof is the relevant one.
  - Consequence: on any window $L<|s|\le K\delta L^{2\gamma}$, the unweighted integral is at most
    $\langle K\rangle^{P_\eta}C_{\phi,\eta}L^{2d-2(d-1)(1-\gamma)+\eta}$. T's `lemlayer2` (T970–977) is the case $K=\mathrm D$.
    This is gap (G4).

### 4.3 Lemma R — one rung on arbitrary unit intervals

Let $I,J\subset[-1,\mathrm D+1]$ be intervals of length $1$ (for $t_v$ and $t_w$). Let $a,b\in\mathbb R^d$, let
$\xi,\xi':J\to\mathbb R^d$ be measurable, and let $W\in\mathcal W_r$ (for some fixed $r\in\mathbb Z_L^d$). Put
$$
\Sigma(t_v,t_w)=\sum_{(x,y)\in\mathbb Z_L^{2d}}\phi(x-a)\phi(y-b)W(x,y)\,e\big(\langle x,\xi(t_w)\rangle+\langle y,\xi'(t_w)\rangle+\delta L^{2\gamma}(t_w-t_v)\langle x,y\rangle\big),
\qquad
\mathfrak M=\int_J\!\!\int_I|\Sigma|\,dt_v\,dt_w .
$$
**Claim.** For $L\ge L_0$,
$$
\mathfrak M\le C_4\,\delta^{-1}L^{2(d-\gamma)}\min\big\{1,\ L^{-(\gamma_1-\sqrt\eta)}+|I\cap J|\big\}.
\tag{4.3}
$$
Moreover $\mathfrak M\le C_dL^{2d}$ for any two unit intervals, with no containment hypothesis.

For the layer box, $|I\cap J|=1$ for a coherent rung and $|I\cap J|=0$ for an incoherent one (adjacent layers meet in a
point). So (4.3) is the rung bound of T1991, now with the $\epsilon,\mathcal Z$ factors included.

*Proof.*

**Step 0 (time geometry).**
- Substitute $t_v=t_w-s/(\delta L^{2\gamma})$:
  $$\int_J\!\int_I G\,dt_v\,dt_w=(\delta L^{2\gamma})^{-1}\int_{\mathbb R}\!ds\int_{E_s}G\,dt_w,\qquad E_s=J\cap\big(I+s/(\delta L^{2\gamma})\big).$$
- For intervals, $|J\cap(I+\Delta)|\le|J\cap I|+|\Delta|$. Hence
  $$|E_s|\le\mu(s):=\min\{1,\ |I\cap J|+|s|/(\delta L^{2\gamma})\}.\tag{B3}$$
- $E_s=\emptyset$ unless $|s|\le S:=\delta L^{2\gamma}(\mathrm D+2)$ (B2). Each interval has length $1$ (B1).
- The trivial bound $\mathfrak M\le\#\{(x,y)\}\le C_dL^{2d}$ uses (B1) only.

**Step 1 (generic term, $W\equiv1$).** At fixed $t_w$, $\Sigma$ is $\Sigma_0(s)$ with modulations $\xi(t_w),\xi'(t_w)$.
- *Region $|s|\le L$.* By (S1) and (B3), the contribution is at most
  $$(\delta L^{2\gamma})^{-1}C_\phi L^{2d}\int\langle s\rangle^{-d}\mu(s)\,ds\le C_\phi c_0\,\delta^{-1}L^{2(d-\gamma)}\min\{1,|I\cap J|+(c_1/c_0)(\delta L^{2\gamma})^{-1}\},$$
  with $c_k=\int\langle s\rangle^{-d}|s|^k\,ds$. Here $c_1<\infty$ because $d\ge3$.
- *Region $L<|s|\le S$.* Use $|E_s|\le1$, Fubini ($E_s\subset J$) and (S2) at each fixed $t_w$, with
  $\langle s/(\delta L^{2\gamma})\rangle^{-P_\eta}\ge\langle\mathrm D+2\rangle^{-P_\eta}$. The contribution is at most
  $$\langle\mathrm D+2\rangle^{P_\eta}C_{\phi,\eta}\,\delta^{-1}L^{2(d-\gamma)}L^{-2(d-1)(1-\gamma)+\eta}.$$
- *Absorption.* Recall $\gamma_1=\min(2\gamma,1,2(d-1)(1-\gamma))$ (T613).
  - $(c_1/c_0)\delta^{-1}L^{-2\gamma}\le\tfrac12L^{-(\gamma_1-\sqrt\eta)}$ once $L^{2\gamma-\gamma_1+\sqrt\eta}\ge2c_1/(c_0\delta)$.
  - $\langle\mathrm D+2\rangle^{P_\eta}C_{\phi,\eta}L^{-2(d-1)(1-\gamma)+\eta}\le\tfrac12L^{-(\gamma_1-\sqrt\eta)}$ once
    $L^{\sqrt\eta-\eta}\ge2\langle\mathrm D+2\rangle^{P_\eta}C_{\phi,\eta}$.

  Both thresholds are $C_2$-type. So the generic term satisfies (4.3).

**Step 2 (terms with indicators).** Take one term $\pm\prod_k\mathbf 1_{\bar B(0,\rho_k)}(z_k)$ of $W$ with at least one
factor. There are three cases.

*(a) Only $x$-type factors.*
- After taking the modulus inside the $x$-sum, keep one factor $\mathbf 1[|x+\theta r|\le\rho]$ and drop the others
  (positivity). With $B:=\{x\in\mathbb Z_L^d:|x+\theta r|\le\rho\}$,
  $$\mathfrak M_{\rm term}\le\sum_{x\in B}(\delta L^{2\gamma})^{-1}\int_Jdt_w\int_{J'(t_w)}\Big|\sum_y\phi(y-b)e(\langle y,\xi'(t_w)+sx\rangle)\Big|\,ds,$$
  where $J'(t_w)=\{s:t_w-s/(\delta L^{2\gamma})\in I\}$ has length $\delta L^{2\gamma}$.
- By Poisson summation, $|\sum_y|\le C_NL^d\sum_{g\in\mathbb Z^d}\langle Lg-w\rangle^{-2d}\le C L^d\varphi(w_i)$, where
  $w=\xi'+sx$, $\varphi(u)=\sum_{g\in\mathbb Z}\langle Lg-u\rangle^{-2}$ is $L$-periodic with $\int_0^L\varphi=\int\langle u\rangle^{-2}=\pi$,
  and $i$ maximizes $|x_i|$.
- Along the line $s\mapsto w_i(s)=\xi'_i+sx_i$, an $s$-interval of length $\ell$ gives
  $\int\varphi\le\pi(\ell/L+1/|x_i|)$, and $|x_i|\ge|x|/\sqrt d$. So for $x\ne0$ the inner double integral is at most
  $CL^d\big(1/L+\delta^{-1}L^{-2\gamma}/|x|\big)$; for $x=0$ it is at most $CL^d$.
- Counting: $\#B\le C(1+L\rho)^d$, and $\sum_{x\in B\setminus0}|x|^{-1}\le C(L^d\rho^{d-1}+L)$. For the latter, split
  $|x|\le2\rho$, where $B\subset\bar B(0,2\rho)$ and the radial sum is $\le CL^d\rho^{d-1}$, from $|x|>2\rho$, where
  $|x|^{-1}<1/(2\rho)$; if $L\rho<1$, $\#B\le C$ and $|x|\ge1/L$.
- Hence
  $$\mathfrak M_{\rm term}\le C\big[L^d+L^{d-1}(1+L\rho)^d+\delta^{-1}L^{2d-2\gamma}\rho^{d-1}+\delta^{-1}L^{d+1-2\gamma}\big].$$
  Relative to $\delta^{-1}L^{2(d-\gamma)}$, the four terms are at most $\delta L^{-(d-2\gamma)}$,
  $2^d\delta L^{-1-(d-2)\gamma+d\eta}$, $L^{-(d-1)(\gamma-\eta)}$ and $L^{1-d}$.
- Each is at most $2^dL^{-\min(1,\,2\gamma-2\eta)}$: use $d-2\gamma>1$, $(d-2)\gamma\ge d\eta$, and $(d-1)(\gamma-\eta)\ge2\gamma-2\eta$.
  The factor $2^d$ comes from the second term and is absorbed by the strict margin below.
  Since $\min(1,2\gamma-2\eta)>\gamma_1-\sqrt\eta$ (as $2\gamma>1\ge\gamma_1$ and $2\eta<\sqrt\eta$), for $L\ge L_0$ the term is
  at most $(2K_0)^{-1}\delta^{-1}L^{2(d-\gamma)}L^{-(\gamma_1-\sqrt\eta)}$.

*(b) Only $y$-type factors.* Symmetric: exchange $x$ and $y$; the phase becomes $\langle x,\xi+sy\rangle$ plus the modulus.

*(c) Both types.* Bound trivially: $\#\{(x,y)\}\le C(1+L\rho)^{2d}\le CL^{2d(1-\gamma+\eta)}$, times measure $1$. The
relative size $\delta L^{-2(d-1)\gamma+2d\eta}$ is far below $L^{-(\gamma_1-\sqrt\eta)}$.

Summing at most $K_0$ terms gives (4.3) with $C_4=K_0(C_\phi c_0+1)$. ∎

**Comment on (G2).** T1991 and Lemma F apply Poisson summation and `lemlayer1` to the rung sum, but $\mathcal Z_v$ is a
sharp indicator of a ball of radius $L^{-\gamma+\eta}$. Its Fourier mass is not $O(1)$, so it is not an admissible
modulation. Step 2 replaces that step. The $\epsilon$ factors alone could instead be handled by E4's character
mixture, which has mass $1$ per hyperplane indicator. Step 2 treats both uniformly, and every indicator term carries at
least the incoherency gain.

### 4.4 Theorem K — box-robust kernel core

Let $\mathfrak B'=\prod_{v\in\mathbb L}I_v$ with each $I_v$ an interval of length $1$. Let $\mathfrak K(\mathbb L;\mathfrak B')$
be (2.1) with $\mathfrak B'$ in place of $\mathfrak B$, without the normalization, and with $F$ contained in the two
end rungs. Then
$$
\mathfrak K(\mathbb L;\mathfrak B')\le A^{4m+2}C_5^{\,m}L^{4d}\prod_{v\in F}\|\psi_v\|_\infty\prod_{j=1}^{m-1}\mathsf B_j .
\tag{4.4}
$$
Here $\mathsf B_j:=C_dL^{2d}$ always, and, if $I_{v_j},I_{w_j}\subset[-1,\mathrm D+1]$,
$\mathsf B_j:=\delta^{-1}L^{2(d-\gamma)}\min\{1,L^{-(\gamma_1-\sqrt\eta)}+|I_{v_j}\cap I_{w_j}|\}$ is also admissible.

*Proof.*
1. **Localize.** Insert $\prod_{j=1}^{m-1}\phi(x_j-x_j^0)\phi(y_j-y_j^0)$, which equals $1$ on the support (P4).
2. **End rungs outermost.** By (P4),
   $$\Big|\sum_{k[\mathbb L]}\cdots\Big|\le\sum_{(a_0,b_0),(a_m,b_m)}|\text{end factors}|\cdot\Big|\sum_{(x_j,y_j):\,(4.2)}\cdots\Big| .$$
   - The end factors are: $\mathcal K_{(\ell)}$ for the at most eight bonds $a_0,b_0,c_0,d_0,a_m,b_m,c_{m-1},d_{m-1}$ (each at
     most $A$); $\epsilon,\mathcal Z$ (at most $1$); the end filters (at most $\|\psi_v\|_\infty$); and unimodular phases.
   - There are at most $(C_dL^d)^4$ end choices. Their times contribute measure $1$.
3. **Interior amplitude.** The interior bonds $a_j,b_j$ ($1\le j\le m-1$) and $c_j,d_j$ ($1\le j\le m-2$) have momenta
   affine in the rung variables, with coefficients in $\{0,\pm1\}$. There are $4m-6$ of them for $m\ge2$; with the
   eight end bonds this accounts for all $4m+2$ internal bonds. Fourier-expand their $\mathcal K_{(\ell)}$, using
   $\|\widehat{\mathcal K_{(\ell)}}\|_{L^1}\le C_dA$ ($30d\ge d+1$ derivatives and unit support). This gives a measure
   $\mu$ of mass at most $(C_dA)^{4m-6}$ over linear modulations $\prod_je(\langle x_j,\nu_j\rangle+\langle y_j,\nu'_j\rangle)$.
4. **Constraint (gap G3).** All rung variables are bounded and lie in one coset of $\mathbb Z_L^d$. For $N$ large,
   $$\mathbf 1[(4.2)]=N^{-d}\sum_{\zeta\in\{0,\dots,N-1\}^d}e\big(\zeta\cdot L(\textstyle\sum_j\lambda_j-c_{m-1}+c_0)/N\big),$$
   a mixture of linear modulations of total mass $1$.
5. **Phases.** By (4.1) and $\Gamma^0=0$ (P2),
   $$e^{\pi i(\alpha_{v_j}t_{v_j}+\alpha_{w_j}t_{w_j})}=(\text{unimodular in }t)\cdot e\big(\delta L^{2\gamma}(t_{w_j}-t_{v_j})\langle x_j,y_j\rangle-\delta L^{2\gamma}t_{w_j}\langle\rho_j,\lambda_j(x_j,y_j)\rangle\big).$$
   The second term is a linear modulation depending on $t_{w_j}$ only.
6. **Factorize.** For fixed $(t,\nu,\zeta)$ the interior sum equals a unimodular constant times $\prod_j\Sigma_j(t_{v_j},t_{w_j})$.
   Each $\Sigma_j$ has the form of Lemma R, with $W_j=\epsilon_{v_j}\epsilon_{w_j}\mathcal Z_{v_j}\mathcal Z_{w_j}\in\mathcal W_r$ by (P5).
   So
   $$\int_{\mathfrak B'}|\text{interior}|\,dt\le\|\mu\|\max_\zeta\prod_j\int\!\!\int|\Sigma_j|\le(C_dA)^{4m-6}\prod_j\mathfrak M_j .$$
   With the end factors ($A^8$ and $(C_dL^d)^4$) this gives (4.4), with $C_5\ge C_d^{8}C_4$.
7. **Conclude.** Apply Lemma R (or its trivial bound) to each $\mathfrak M_j$, uniformly in the modulations. ∎

**Comment on (G3).** T1991 bounds "the last remaining sum ... trivially by $L^{2d}$". But global conservation makes
$x_m$ (or the last single bond) a function of all earlier rung variables, so the summand does not factor rung by rung.
Fixing both end double bonds and averaging over characters restores an exact factorization at mass $1$. The end rungs
may contain degree-3 atoms ($c_v\ne0$, $\Gamma^0_v\ne0$), where (4.1) can fail; they are only counted.

### 4.5 Lemma T — filters are translations (o75 Lemma F, Step 1)

Let $v$ be an interior atom in $F$. Since $\zeta_{\mathfrak n}\Omega_{\mathfrak n}=-\Gamma_v+\Gamma^0_v$ (T1968),
$$\psi_v(\Omega/R_v)=\int\widehat{\psi_v}(\xi)\,e^{2\pi i\xi\zeta_{\mathfrak n}(-\Gamma_v+\Gamma^0_v)/R_v}\,d\xi .$$
With $\tau_v:=2\zeta_{\mathfrak n}\xi/(\delta L^{2\gamma}R_v)$,
$$e^{2\pi i\xi\zeta_{\mathfrak n}(-\Gamma_v+\Gamma^0_v)/R_v}\,e^{\pi i\alpha_vt_v}=e^{-\pi i\xi_v\tau_v}\,e^{\pi i\alpha_v(t_v+\tau_v)} .$$
The identity holds at every atom, including those with $\Gamma^0_v\ne0$. The restriction to interior atoms is only a
choice: end-rung filters are bounded by $\|\psi_v\|_\infty$ in Theorem K.
So, for fixed frequencies, the filtered lattice sum at $t$ is a unimodular constant times the lattice sum with only
the end filters left, evaluated at $t+\tau(\xi)$; here $\tau_u=0$ for atoms not filtered in the interior. The sum is
finite and $\widehat\psi\in L^1$. By Fubini and Minkowski,
$$
\int_{\mathfrak B}\big|\Sigma^\Psi(t)\big|\,dt\le\int\prod_{v\in F_{\rm int}}|\widehat{\psi_v}(\xi_v)|\ \mathfrak K_{\Psi_{\rm end}}\big(\mathbb L;\mathfrak B+\tau(\xi)\big)\,d\xi .
\tag{4.5}
$$
Only the box moves. No ordering constraint is present, because the kernel core has none (E5). This settles RR's
caution about T1603(iii). ∎

### 4.6 Proof of Theorem 8.3

Apply (4.5), then (4.4) to each translated box. By (4.4), the bound is a product over interior rungs of a factor that
depends only on that rung's two frequencies $(\xi_{v_j},\xi_{w_j})$; use $\xi=0$, a Dirac mass, when an atom is not
filtered. So the $\xi$-integral factorizes. Fix an interior rung $j$ and write $v=v_j$, $w=w_j$.

- **Good frequencies: $|\xi_v|,|\xi_w|\le\delta L^{2\gamma}/4$.**
  - Then $|\tau_\cdot|\le2|\xi_\cdot|/(\delta L^{2\gamma})\le\frac12$, so the translated intervals lie in $[-1,\mathrm D+1]$.
  - By the interval inequality, $|(I_v+\tau_v)\cap(I_w+\tau_w)|\le|I_v\cap I_w|+|\tau_v|+|\tau_w|$.
  - *Coherent rung:* $\mathsf B_j\le\delta^{-1}L^{2(d-\gamma)}$.
  - *Incoherent rung:* $|I_v\cap I_w|=0$ and
    $$\mathsf B_j\le\delta^{-1}L^{2(d-\gamma)}\big(L^{-(\gamma_1-\sqrt\eta)}+2(|\xi_v|+|\xi_w|)/(\delta L^{2\gamma})\big)\le\delta^{-1}L^{2(d-\gamma)}L^{-(\gamma_1-\sqrt\eta)}(1+|\xi_v|+|\xi_w|)$$
    for $L\ge L_0$, since $2\gamma>\gamma_1-\sqrt\eta$.
- **Tail: some $|\xi|>\delta L^{2\gamma}/4$.**
  - Use $\mathsf B_j=C_dL^{2d}$ and $\int_{|\xi|>X}|\widehat\psi|\le X^{-2}\mathfrak b(\psi)$.
  - The tail contributes at most $32C_d\,\delta^{-2}L^{2d-4\gamma}\mathfrak b(\psi_v)\mathfrak b(\psi_w)$.
  - This is at most $\delta^{-1}L^{2(d-\gamma)}L^{-(\gamma_1-\sqrt\eta)}\mathfrak b(\psi_v)\mathfrak b(\psi_w)$ once
    $32C_d\delta^{-1}L^{-(2\gamma-1)}\le1$; here $\gamma>\frac12$ is used.
- **Per rung.** Since $\int\!\int(1+|\xi_v|+|\xi_w|)|\widehat\psi_v||\widehat\psi_w|\le\mathfrak b(\psi_v)\mathfrak b(\psi_w)$,
  each interior rung contributes at most
  $$2\,\delta^{-1}L^{2(d-\gamma)}\,\mathfrak b(\psi_v)\mathfrak b(\psi_w)\cdot\big(1\ \text{or}\ L^{-(\gamma_1-\sqrt\eta)}\big).$$
- **Assemble.** Let $g_{\rm int}\ge g-2$ be the number of incoherent interior rungs. Then
  $$
  \mathfrak K^\Psi(\mathbb L)\le\Big(\frac{\delta}{2L^{d-\gamma}}\Big)^{2m+2}A^{4m+2}C_5^mL^{4d}\prod_{v\in F}\mathfrak b(\psi_v)\,\big(2\delta^{-1}L^{2(d-\gamma)}\big)^{m-1}L^{-(\gamma_1-\sqrt\eta)(g-2)} .
  $$
  - The $\delta$-powers combine to $\delta^{m+3}$.
  - The $L$-powers combine to $L^{-4(d-\gamma)+4d}=L^{4\gamma}$, times $L^{2(\gamma_1-\sqrt\eta)}\le L^2$.

  This is (2.2) with $C_3=2C_5$.
- **(2.3).** The ordered domain is contained in $\mathfrak B$, so the modulus of the ordered integral is at most the
  core with T's normalization. Then use Remark 2.2 and $C_1\ge C_3$. ∎

### 4.7 Proof of Corollary 8.3.A

1. **(finalsbest1).** Repeat T2081–2083 in E5 form: ladders are split at hinges (or at $H\cup S_{\rm split}$ in O75).
   - By Remark 2.1, E5 steps 2–4 (locality, fibre factorization, gluing) apply to the filtered integrand. The filters
     at ladder atoms belong to the ladder weights; all others belong to the rest amplitude. An atom outside $\mathbb L$
     has no internal bond of $\mathbb L$.
   - Each ladder contributes (2.2). The rest is bounded trivially, with filters at most $\|\psi_v\|_\infty\le\mathfrak b(\psi_v)$.
   - The exponent bookkeeping of T2082 (or O75 (finalsbest1′)) is unchanged, because (2.2) has the same $\delta^m$,
     $L^{-(\gamma_1-\sqrt\eta)g}$ and at most $L^{20d}$ per ladder as (redladder2).
2. **(finalsbest2).** In (redvine5), the filters are part of the absolute decoration sum. So
   $|\cdot|\le\prod\|\psi_v\|_\infty$ (S Lemma 9.4). `ladderl1old` concerns only $\mathfrak B(\alpha)$, which carries no filter.
3. **Interpolation.** (T2221) is the geometric mean (1)$^\theta$(2)$^{1-\theta}$. The exponent $\theta$ is fixed by
   $\theta/2-10\nu(1-\theta)=10\nu$, i.e. $\theta=40\nu/(1+20\nu)$. The filter factor becomes $\prod\mathfrak b^\theta\|\psi\|_\infty^{1-\theta}$.
   Each node lies on at most one stem, and each low-pass product has one factor per stem vertex, so $|F|\le n_{\rm sb}\le n$.
4. **Uniformity over profiles.** See §5.3. ∎

---

## 5. Sufficiency for the assembly

### 5.1 Where Theorem 8.3 enters

- **S's original plan.** S Proposition 10.3 (or O63 Proposition 10.3′) needs the aggregate (10.3)/(5.1) for families
  carrying the $M_2$ shells. The shells expand into at most $2^{2P}$ products of low-pass stem filters, or into the
  $R$-derivative form of S §8 with one selected vertex per tree. In either case every non-selected stem vertex carries
  one filter $\psi(\Omega/R)$ with $\psi\in\{\vartheta,\chi_0\}$ and $R\ge L$. Selected vertices are protected
  (OPEN 7.3/7.5), so they are never ladder atoms.
  - Stem vertices inside regular objects belong to OPEN 8.2.
  - SG tops belong to Lemma 9.3.
  - Ladder atoms of $\mathbb M_{\rm sb}$ belong to Theorem 8.3.
  - Every other atom of $\mathbb M_{\rm sb}$ is treated trivially in finalsbest1 and absolutely in finalsbest2.

  With Corollary 8.3.A, the chain (redvine3) → (finalsbest1)/(finalsbest2) → (finalproof2) → T2237–2255 goes through
  with $C_1$ replaced by $C_1\mathfrak b_*$, and with no new $L$-power.
- **O75's route.** Theorem 7.5′(8) cites Lemma F for exactly this step, with the extra factor $C_\vartheta^{n_{\rm sb}}$.
  Theorem 8.3 is a complete proof of that step, with $\mathfrak b_*$ in place of $C_\vartheta$. O75's budget row 7
  (zero $L$-power) stands.
- **The flower's special vines (T2297, S OPEN 7.5).** Where `ladderl1new` is applied directly, without interpolation,
  the cost is $\prod\mathfrak b\le\mathfrak b_*^{2m+2}\le(\mathfrak b_*^4)^m$ per ladder. It is absorbed by enlarging
  $C_1$ by the absolute factor $\mathfrak b_*^4$, not by the smallness of $\delta$.

### 5.2 Quantifier order

- $\mathfrak b_*$ depends only on the fixed $\vartheta,\chi_0$.
- $C_3,C_4,C_5$ depend on $(d,\gamma)$ and $\phi$.
- $L_0$ depends on $(d,\gamma,\eta,\tau_*,\delta)$ and is chosen last.

The order C₀, η, C₁, ν, δ, C₂, L is respected. No exponential base depends on $\delta$.

### 5.3 Uniformity over profiles (O63 interface I-6.3)

Theorem 8.3 involves no profile: the bond factors are abstract members of the class of T1965. In (redvine3) the
profiles enter only through the normalized bond factors and the regular-object bounds (T995, T1173, T2069). Those use
only reality and the $\mathfrak S^{40d,40d}$ bound (O63 §5). So Corollary 8.3.A holds uniformly over
$G\in\mathcal P(C_1)$ with the same constants. By the homogeneity O63 (1.2), it then holds over $\mathcal P(2c_\chi C_1)$
as well.

**O63 revision 2.** Revision 2 (`a50e0f93…`, (G) and (U)) states the extraction class by class: one common factor
$\mathfrak e_n$ for every partition class $\alpha$ fixed by profile-independent data, and for $\Theta$ multiplied by any
bounded profile-independent multiplier. Corollary 8.3.A meets this as follows:
- the stem filters and frontier cutoffs are profile-independent multipliers;
- the bound is proved per congruence class $\mathscr K^{\rm eqc}_{p+1,n}$ (T1946, T2221–2225).

So it is a per-class bound $\mathcal B_{\Theta,\alpha}(C_1)\le\mathcal R_\alpha$ in the sense of (G), and every gain it
retains (incoherency, $\eta^6$ per unit of $\bar\rho$) transfers through the O63 extraction unchanged.

---

## 6. Independent check of o75 Lemma F

**Verdict: VERIFIED. The mechanism and the three-property claim are right, and translation commutes with E5. The proof
is complete once gaps (G1)–(G5) are filled, which §4 does. There is no obstruction.**

1. **Step 1 (filter ⇒ translation).** Correct, exactly as Lemma T. The algebra
   $e^{2\pi i\xi(-\Gamma+\Gamma^0)/R}e^{\pi i\delta L^{2\gamma}(-\Gamma+\Gamma^0)t}=e^{\pi i\delta L^{2\gamma}(-\Gamma+\Gamma^0)(t+\tau)}$
   holds with $\tau=2\xi/(\delta L^{2\gamma}R)$. The time-modulation phase gives a unimodular constant. Minkowski is
   legitimate because the sum is finite and $\widehat\vartheta\in L^1$. (O75 writes $\xi$ both for T's time parameters
   and for the Fourier variable; the argument is unaffected.)
2. **"The box enters only through (B1)–(B3)."** Correct. Lemma R uses the box only through:
   - unit length of each interval (B1);
   - the window $|t_w-t_v|\le\mathrm D+2$ (B2);
   - the overlap measure (B3).

   (B3) holds in the sharper general form $|E_s|\le\min\{1,|I\cap J|+|s|/(\delta L^{2\gamma})\}$ for *arbitrary*
   intervals. This is what makes translated boxes harmless. The indicator terms of Lemma R and the end rungs of
   Theorem K use (B1) only.
3. **Does translation commute with the E5 repair?** Yes, with one caveat.
   - (a) Minkowski is applied to the kernel core, i.e. with the modulus inside the time integral. That is E5's form.
   - (b) E5 steps 2–4 need only locality of the ladder weights. Filters at ladder atoms are local (Remark 2.1), so the
     filtered cores are multiplicative over disjoint ladders.
   - (c) *Caveat (G1).* E5's proved bound (Lean `ladderL1Gate`, report `Spine/LadderL1Gate.lean` L15–33) is stated for
     the layer `timeBox` only. Lemma F applies it to $\mathfrak B+\tau$, which is not an instance. This is O75's own
     Audit note A. Theorem K is the required box-robust bound, with the overlap term made explicit.
4. **Gaps inherited from T's sketch, all filled here.**
   - (G2) $\mathcal Z$ indicators in the rung sums (§4.3 Step 2).
   - (G3) The end-rung constraint and degree-3 end atoms (§4.4 step 4).
   - (G4) The enlarged `lemlayer2` window: DH23 Lemma 6.6(2) in weighted form, not T970 as stated (§4.2).
   - (G5) `lemlayer1` with a radius-4 bump (§4.2).
5. **Constants.** Lemma F's $C_\vartheta=40\int(1+|\xi|)|\widehat\vartheta|$ plus a tail $C_NL^{-N}$ is valid for
   $L\ge L_0(\vartheta)$. I use $\mathfrak b(\psi)=\int(1+|\xi|)^2|\widehat\psi|$, which makes $L_0$ independent of $\psi$
   and needs only two moments. Lemma F's $R_v\ge L/2$ can be relaxed to $R_v\ge1$.
6. **Lean note (not a mathematical gap).** The Lean `ladderWeight` (report `Spine/LadderTime.lean` L61–66) already
   contains `epsCoef` and `localLadderGapIndicator`, so (G2) has some Lean treatment for the layer box. To use Lemma F
   or Theorem 8.3 in Lean, either:
   - generalize `LadderL1At` to boxes $\prod[\mathfrak L_v+\theta_v,\mathfrak L_v+1+\theta_v]$, $|\theta_v|\le\frac12$, with
     the gain term $\min\{1,L^{-(\gamma_1-\sqrt\eta)}+|I_v\cap I_w|\}$ per rung; or
   - formalize Lemma R and Theorem K directly.

---

## 7. R2 — frontier $M_1$ cutoffs on Stage-2 ladder bonds

**Verdict: CONFIRMED** (RR M3 is right).

1. **They are still present.** Under O63 Theorem 6.3′ the integrand $\Theta$ still contains $W=\prod_jH_{j,M_1}$ (O63
   §1.1). Only the gain is extracted, through common profiles. By S Lemma 3.2, $W$ is a signed sum of at most $2^{2P}$
   products of $\chi(k_u/R_j)$, $u\in B_j$, $R_j\in\{M_1,M_1/2\}$, with $R_j\ge L$.
2. **Where they sit.** A frontier vertex $u$ has momentum $k_u$, which is one of:
   - interior to a regular object: S Lemmas 4.1 and 5.1 (OPEN 8.2 if protected);
   - interior to a spliced vine: S Lemma 5.3;
   - the momentum $k_\ell$ of a bond of $\mathbb M_{\rm sb}$. This covers a skeleton node or leaf, and the root or lone
     leaf of a regular tree or couple, whose momentum equals the bond momentum (T1235–1244).
3. **On a ladder bond $\ell\in\mathbb L$.** The cutoff is a single-bond factor, so it multiplies $\mathcal K_{(\ell)}$.
   - For $R\ge1$, Leibniz gives $\|\partial^\alpha(\chi(\cdot/R)\mathcal K_{(\ell)})\|_\infty\le c_\chi$ for
     $|\alpha|\le30d$, with $c_\chi:=2^{30d}\max_{|\alpha|\le30d}\|\partial^\alpha\chi\|_\infty$ (O63 §1.2). The support is
     unchanged.
   - A PC bond carries one node and an LP bond two leaves, and each node is a frontier vertex of at most one tree. So
     there are at most two cutoffs per bond, and $A\le c_\chi^2$ in Theorem 8.3.
   - The proof uses only $\|\widehat{\mathcal K_{(\ell)}}\|_{L^1}\le C_dA$ and the support.
   - The cost is $\le c_\chi^2$ per bond, an absolute base.
4. **T2081/T2083.** The hypothesis concerns only $\mathcal K^\dagger(k[\mathbb W])$, a function of the bonds at hinge
   atoms (T1965, T1970). Frontier cutoffs are not part of $\mathcal K^\dagger$. The hypothesis is untouched.
5. **Elsewhere.** On boundary or non-ladder bonds: $|\chi|\le1$ in the trivial part. In finalsbest2: absolute (S Lemma 9.4).

---

## 8. R3 — stem filters at interior nodes of vines

**Verdict: every position is covered.** Let $\mathfrak n$ be a stem vertex carrying a filter ($\mathfrak n\in\mathcal S_j$,
$|k|\ge M_1^{10}$). Exactly one of the following holds.

| Position of $\mathfrak n$ | Handled by |
|---|---|
| (a) Inside a regular tree $\mathcal T_{(\mathfrak m)}$ (e.g. on the root–lone-leaf chain of the regular tree at a stem skeleton node) or inside a regular couple. A regular couple can contain stem vertices only when it contains the flower–cap pair. | OPEN 8.2, which allows the multiplier at any set of layer-$p$ stem vertices; plus OPEN 7.3 for the flower–cap object |
| (b) A node of the realization $\mathcal G_{\rm sk}[\mathbb U]$ of a spliced SG chain $\mathbb U\in\mathscr V_0$. A spliced SG chain is unmarked (o75 Def 2.3, Lemma 2(d)), so its realization contains no special node, in particular not $\mathfrak f_j$ or $\mathfrak f_j^{\rm pr}$. Hence, if the flower descends from $\mathfrak u_1$, it descends from one of $\mathfrak u_{11},\mathfrak u_{21},\mathfrak u_{22}$, and Lemma 9.2 excludes $\mathfrak u_{21},\mathfrak u_{22}$. So it descends from $\mathfrak u_{11}$, a child of $\mathfrak u_1$ whose subtree the realization excludes (T2300(7)). Therefore $\mathfrak n=\mathfrak u_1$, the hinge atom. | S Lemma 9.3 (with RR's twist-invariance sentence) |
| (c1) A non-hinge atom of $\mathbb M_{\rm sb}$ lying in a ladder (after splitting at hinges and protected atoms). This includes ladder atoms of LG/ZG vines, of unspliced SG vines (HV, DV, CN, skipped tops of HVC/root VC; O75's $\mathscr C_E$ and marked vines), and of everything else. | **Theorem 8.3** |
| (c2) A non-hinge, non-ladder atom of $\mathbb M_{\rm sb}$ (at most 20 per vine, T1519, plus the remaining atoms). | Trivial part of finalsbest1 ($|\psi|\le1$); finalsbest2 absolute (S Lemma 9.4) |
| (c3) A protected or split atom (pins, faces, special nodes). | OPEN 7.3/7.5 (O75) |

**Remarks.**
- **No twist invariance is needed outside (b).** The equivalence classes use twists at $\mathscr V_0$ only (T1946). LG
  and ZG vines, and unspliced SG vines, are not twisted; O75's marked vines are neither twisted nor spliced. Inside
  (b), Lemma 9.2 makes the stem, hence every $\Omega_{\mathfrak n}$ on it, twist-invariant (T2300(7)).
- **$|k|<M_1^{10}$ does not arise.** The $M_2$ restriction is imposed only under $|k|\ge M_1^{10}$:
  - in T2285;
  - in S (1.1), last line;
  - in the frozen Lean clause, `FlowerCaseAt` hypothesis `∀ j₂ ∈ cut2, ∃ j₁ ∈ cut1, ((2^{j₁}L))^{10} ≤ ‖n/L‖` (main
    `FlowerTop/CaseAssembly.lean` L47), which also covers `cut2 = some 0`;
  - and in `PositiveCut2At` (main `Cut2EB/Target.lean` L43).

  If a downstream consumer ever needed filtered bounds with $|k|<M_1^{10}$, case (b) would fail: twists move the stem
  inside SG vines, so the filters are not common to a twist class. That would be a new item, outside `flowerest1` and
  outside the frozen statement.

---

## 9. Loss accounting

| Operation | Extra cost | $L$-power | Base | Where |
|---|---|---:|---|---|
| Filter on a ladder atom | $\mathfrak b(\psi)\le\mathfrak b_*$ | $0$ | absolute | Thm 8.3 |
| Filter on a non-ladder atom | $\|\psi\|_\infty\le1$ | $0$ | — | Cor 8.3.A |
| Filters after interpolation | $\mathfrak b_*^{\theta|F|}$, $\theta\le40\nu$ | $0$ | absolute | Cor 8.3.A(3) |
| Frontier cutoff on a ladder bond (R2) | $\le c_\chi^2$ per bond | $0$ | absolute | §7 |
| $\epsilon\mathcal Z$ expansion (pre-existing in T's sketch) | $K_0=2304$ per interior rung | $0$ | absolute | Lemma R |
| Bond Fourier expansion (pre-existing) | $(C_dA)^4$ per rung | $0$ | absolute | Thm K |
| End rungs (pre-existing, made exact) | $(C_dL^d)^4$ per ladder | inside $L^{4\gamma+2}$ per ladder | — | Thm K |
| Per ladder, total | $(C_3\delta)^m\delta^3$ | $L^{4\gamma+2}\le L^6$ (core normalization); $L^{d+3\gamma+2}$ (T's $2m+1$ form) | — | (2.2), (2.3) |
| Incoherency gains | all retained: $L^{-(\gamma_1-\sqrt\eta)}$ per incoherent interior rung; end rungs' at most $2$ units are absorbed in the per-ladder power | — | — | (2.2) |

**Fit with the budget.**
- The per-ladder power is at most T's $L^{20d}$, which is already in (finalsbest1) as $L^{80d(\rho_{\rm sb}+q_{\rm sk})}$.
  After interpolation it is absorbed by $L^{-\eta^6\bar\rho/2}$ (T2221–2225). It never enters $L^{(100d)^3P}$.
- **OPEN 8.3 contributes $0$ to $B$ in (10.4)**, for plain and derivative patterns alike. The frozen doubling
  $L^{2(100d)^3P}$ is untouched.
- In S §10's table, add one row: "Stem filters on ladder rungs | $\mathfrak b(\psi)$ per filter, no $L$-power | none".
  In O75 §7, row 7 stands with $C_\vartheta\to\mathfrak b_*$.
- Uses of $\gamma>\frac12$: the tail in §4.6 and the margin $2\gamma-2\eta>\gamma_1-\sqrt\eta$ in §4.3. Uses of $d\ge3$:
  $c_1<\infty$ and $d-2\gamma>1$.

---

## 10. Dependencies (with lines)

| Source | Content | Use |
|---|---|---|
| T287 | $\mathbb Z_L^d=(L^{-1}\mathbb Z)^d$ | Poisson summation, §4.2–4.3 |
| T556–564 | $\epsilon_{k_1k_2k_3}$, $\mathfrak G$, $\Omega=2\langle k_1-k,k-k_3\rangle$ | (P1), (P5) |
| T600–613 | constants, $\mathrm D=\tau_*/\delta$, $\gamma_1$ | thresholds, §4.3 |
| T1295–1320 | molecules, directions, decorations, $c_v$, $\Gamma_v$, (molegammav) | (P1)–(P5) |
| T1384 (defvine) | ladders: $m+1$ double bonds, opposite parallel bonds | (P3) |
| T1489 (cohmol) | ladder incoherency | $g$ |
| T1519 (layervine) | vine = at most 3 ladders + fewer than 20 atoms | §8 (c2) |
| T1595–1660 (`sumint`, Step 2) | rung quantity $\mathcal M^i_j$, (timeintgap) | template for Lemma R |
| T958–977 (`lemlayer1/2`) | exponential sums | (S1); window, (S2) |
| D23 1076–1088 (Lemma 6.6(2)) | weighted large-$s$ bilinear sum bound | (S2) |
| T1926–1946 | $\mathscr V$, gaps, $\mathscr V_0$ splicing | §1, §8 |
| T1962–1973 (redvine2/3) | bond factors class (T1965), $\mathcal K^\dagger$ on hinge bonds (T1970), phases | §2.1, §7 |
| T1978–1991 (`ladderl1new`) | statement and sketch | Thm 8.3 extends and completes it |
| T2075–2083 | (finalsbest1/2), the ladder step | Cor 8.3.A |
| T2090–2097, (redvine5) | absolute counting | Cor 8.3.A(2) |
| T2221–2225, T2253 | interpolation, final sum | Cor 8.3.A(3) |
| T2283–2285, T2297–2300 | $M_2$ clause ($|k|\ge M_1^{10}$), adjustments (4)–(7) | §5, §8 |
| E4 (E L780–816) | indicator = mass-one character mixture | Thm K step 4; alternative for $\epsilon$ |
| E5 (E L820–852) | kernel-core form; gluing over disjoint ladders | Remark 2.1, Cor 8.3.A(1), §6 |
| S Lemmas 3.2, 9.2–9.4; §8 (8.1) | shells, separation, SG tops, absolute counting, filters | §5, §7, §8 |
| O63 §1.2, (1.2), §5, I-6.3 | $c_\chi$, homogeneity, profile uniformity | §5.3, §7 |
| O75 Thm 7.5′(8), Lemma F (§4.8), Audit note A | consumer; the claim checked | §5.1, §6 |
| main `FlowerTop/CaseAssembly.lean` L44–49; `Cut2EB/Target.lean` L36–50 | frozen high-root hypothesis for any cut2 | §8 |
| report `Spine/LadderL1Gate.lean` L15–33; `Spine/LadderTime.lean` L61–66 | Lean layer-box core; weight with $\epsilon$, gap indicator | §6 (3c), (6) |

---

## 11. Remaining OPEN sub-items

**For OPEN 8.3: none.**

Notes for wt-orch:
- **(N1) Lean.** `LadderL1At` is stated for the layer box. Formalizing Theorem 8.3 needs either the box-robust
  generalization of §6(6) or Lemma R and Theorem K directly. This is a formalization task, not mathematics.
- **(N2) Errata candidates against T1989–1991.** These are independent of filters and should be recorded:
  - the rung sum with the sharp $\mathcal Z$ indicators (G2);
  - "the last remaining sum" versus global conservation (G3);
  - the end-rung degree-3 case.

  §4.3–4.4 prove the stated bound, so `ladderl1new` is true as stated (with $L^{20d}$).
- **(N3)** The derivative profile $D_\vartheta$ and the selected-vertex reciprocals stay at protected vertices
  (OPEN 7.3/7.5). Theorem 8.3 would also accept $D_\vartheta$ on a ladder atom, since $\mathfrak b(D_\vartheta)<\infty$.

---

## 12. Revision 1 (REFEREE-83)

REFEREE-83 (`ref/REFEREE-83.md`, sha256 `56f98c77…760a`) gave 0 FAIL, one PASS AFTER FIX (R3 row (b)) and editorial
notes. All are applied in place above.

1. **Fix, R3 row (b) (§8).** Inserted: a spliced SG chain is unmarked (o75 Def 2.3, Lemma 2(d)), so its realization
   contains no special node, in particular not $\mathfrak f_j$ or $\mathfrak f_j^{\rm pr}$. Hence, if the flower
   descends from $\mathfrak u_1$, it descends from one of $\mathfrak u_{11},\mathfrak u_{21},\mathfrak u_{22}$, and
   Lemma 9.2 excludes $\mathfrak u_{21},\mathfrak u_{22}$.
   - This closes the case where the flower lies inside the realization, which Lemma 9.2 alone does not exclude.
   - The conclusion $\mathfrak n=\mathfrak u_1$ is unchanged.
2. **Lemma T (§4.5).** The restriction "$\Gamma^0_v=0$" is removed. The translation identity holds at every atom with
   $-\Gamma_v+\Gamma^0_v$ (T1968). Restricting to interior atoms is kept only as a choice.
3. **Lemma R, Step 2(a) (§4.3).** The relative bound now carries the factor $2^d$, absorbed by the strict margin
   $\min(1,2\gamma-2\eta)>\gamma_1-\sqrt\eta$.
4. **§2.1.** Added the reason for "at most four $\mathcal Z$-indicators per atom": $\mathscr C$ consists of disjoint
   vine-like objects whose gaps are read at one joint. In (P5), the constant term's coefficient is now stated as having
   modulus at most $1$.
5. **§5.1.** The cost $\mathfrak b_*^{2m+2}\le(\mathfrak b_*^4)^m$ of direct uses is absorbed by an absolute enlargement
   of $C_1$, not by the smallness of $\delta$.
6. **§8.** The `FlowerCaseAt` high-root hypothesis is cited at main `FlowerTop/CaseAssembly.lean` **L47**.

None of these changes the statement of Theorem 8.3 or Corollary 8.3.A, or the loss accounting of §9.

STATUS: CLOSED (revision 1: REFEREE-83 fix to R3 row (b) and editorial notes applied; no change to the statement or the loss accounting)
