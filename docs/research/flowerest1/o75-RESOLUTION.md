# RESOLUTION — OPEN 7.5 (exceptional pieces and the modified `subpro`; loss/count budget)

## 0. Result

**OPEN 7.5 is closed with a variant: Theorem 7.5′ (§3), proved in §4; its sufficiency for the assembly is §5; the budget table, with a number in every row, is §7.** A separately marked §8 carries out the aggregate count of OPEN 10.3 (T2237–2255 for marked components), conditional only on the contracted exponents of OPEN 7.3 and OPEN 8.2.

**The variant in one paragraph.** The supplement's plan was to *excise* exceptional pieces and to estimate them separately against pinned boundary data. Theorem 7.5′ does not excise anything. A vine of the twist collection $\mathscr V$ (T1934) is *marked* when its twist-active region (Definition 2.3) contains a protected vertex. Marked vines are neither twisted nor spliced. Everything else in Stage 1 is unchanged, so $\mathcal G_{\rm sb}$ is still a genuine irreducible garden and $\mathbb M_{\rm sb}=\mathbb M(\mathcal G_{\rm sb})$ is still connected with $n_{\rm sb}$ atoms and $2n_{\rm sb}-R$ bonds. The surviving small-gap vines of each affected vine chain form a third collection $\mathscr C_E$. Operation 1 of Stage 2 removes them one vine at a time, by the same cut-and-count step that T uses for $\mathscr C_1$. A removal either creates no component and satisfies (excesseqn2), or creates one component and satisfies (excesseqn2+). The six clauses of `subpro` then hold with $\mathscr C_1$ replaced by $\mathscr C_1\cup\mathscr C_E$ in clauses 4 and 6. A further clause 6′ shows that every small-gap vine-like object meeting the exceptional boundary $B$ is destroyed by those removals.

**Costs.** With $b:=|\Pi|\le 26P$ protected vertices (after Theorem 6.3′ removed the Section-6 marks) we have:

- $N_E:=|\mathscr C_E|\le 2b$ survivors;
- $|B|\le 4b$;
- an extra counting factor $L^{(3\gamma_0+5\eta^2)N_E}\le L^{2N_E}$;
- an extra crude-bound factor $L^{(60d+2)\cdot 6b}$ from splitting ladders at $B\cup\Pi_{\rm sb}$.

In total the extra factor is $L^{(360d+16)b}\le L^{(9360d+416)P}$. Every exponential base is independent of $\delta$.

**What is not done here.** The analytic estimates of regular objects that contain a pin, a cap, or a selected-face vertex are OPEN 7.3 and OPEN 8.2, as the supplement designed. They enter only through their contracted exponents.

**Referee item M2.** M2 is the stem upper filters on ladder rungs of $\mathbb M_{\rm sb}$ (REFEREE §4.2). It lies inside the extension of T2075–2083 that 7.5 requires. It is closed by Lemma F (§4.8), relative to the E5-repaired form of `ladderl1new`.

---

## 1. Inputs, pins, and adopted corrections

**Pinned sources** (hashes verified at first read):

- T: `WKE-Longer_times_Final_arXiv.tex`, sha256 `493eef6b…727cb`.
- D23: `Revision_Submit.tex`, sha256 `c7e47dfa…35475`.
- S: `SUPPLEMENT-v1.md`, sha256 `ddd81fe1…74d7`.
- RR: `ref/REFEREE.md`, sha256 `c31ee38a…d6d`.
- O63: `o63/RESOLUTION.md`, sha256 `c28aad09…2ad9`.

Line numbers "T…" and "D23…" refer to these files.

**Corrections adopted from RR (as relayed by wt-orch):**

1. **Citations.** The `subpro` clauses are cited as T2042 (1), T2043 (2), T2044 (3), T2045 (4), T2046 (5) and T2047 (6).
2. **Restored hypotheses.**
   - The second sentence of subpro (5) (used at T2104) is restored, and extended to $\mathscr C_E$: clause (5) of Theorem 7.5′.
   - The `subsetvc` case note (T2045) is restored: clause (4).
   - The hinge count $q_{\rm sk}$ (T2043) is restored: clause (2).
   - The support hypothesis $\widetilde\epsilon\cdot\mathcal Z\ne0$ (T2040) is restated, with pins and cutoffs, and with $\epsilon_v$ kept at every non-hinge atom including $B$: §2.5.
3. **Connectedness.** It is *kept*: clause (1) of Theorem 7.5′. Both of its uses are supplied.
   - The use at T2113, $\chi(\mathbb M_{\rm sb})=n_{\rm sb}-R+1$, holds verbatim.
   - At T2162, "at most $2R-1$ component-creating Operations 1" becomes $2R-1+N_E$: Proposition 4.7(3).
4. **Ladders.** Ladders are split at $H\cup B\cup\Pi_{\rm sb}$: Theorem 7.5′(8).
5. **Budget.** The aggregate (10.3)/(10.4) is the separate item OPEN 10.3.
   - §7 gives every row a number.
   - §8 does the 10.3 count, conditional on the 7.3/8.2 contracts.

**Adopted from O63 (Theorem 6.3′, Proposition 10.3′, (5.1)).**

- The Section-6 marks no longer exist. The exceptional data are only:
  - the flower pins and caps;
  - the selected $M_2$ vertices with their faces;
  - the special-node vines.
- The downstream bound to be delivered is O63 (5.1), uniformly over real profiles in $\mathcal P(C_1)$.

**RR remark on Lemma 7.4.** For the capped garden, $R$ is the capped half-width, so $\sum_{\rm components}R=2P$. Every $(C_0R)!$ and every cut count below uses this value.

---

## 2. Setting

### 2.1 The component

- Fix a capped garden $\widehat{\mathcal G}$ (S Lemma 2.1) and one irreducible component $\mathcal G$ of it. $\mathcal G$ is a canonical couple or canonical proper garden at level $p+1$, of width $2R$ and order $n\le N^4$ (the restriction of T2290).
- Its skeleton is $\mathcal G_{\rm sk}$ (T870). Its regular objects are $\mathcal T_{(\mathfrak m)}$ and $\mathcal Q_{(\mathfrak l,\mathfrak l')}$, and $\mathbb M_{\rm sk}=\mathbb M(\mathcal G_{\rm sk})$ (T1297).
- The integrand is O63's $\Theta_{\widehat{\mathcal G}}$ restricted to $\mathcal G$:
  - normalization $\delta/(2L^{d-\gamma})$ per branching node (S §1);
  - $\zeta(\mathcal G)$ and $\epsilon$;
  - the layered time domain (T673), with the pins $\delta(t_{f_j^{\rm pr}}-s)$;
  - the multiplier $W$ (O63 §1.1): frontier shells $A_{j,L}$ or $H_{j,M_1}$, times, in the third version of S (1.1), the stem shells $V_{j,M_2}$;
  - common real profiles $G\in\mathcal P(C)$ with $C\le 2c_\chi C_1$ (O63).
- Everything below is uniform in $(t,s,k,k',M_1,M_2,\zeta)$ and in $G$. Profiles enter only through the bound on their $\mathfrak S^{40d,40d}$ norm and their reality (O63 §5).

### 2.2 The protected set $\Pi$

For each original tree $j$ (T2259–2261), $\Pi$ contains:

- **(Π1)** the root $\mathfrak r_j$, its $\le3$ children, the flower $\mathfrak f_j$, $\mathfrak f_j^{\rm pr}$ (the pin), and the two siblings of $\mathfrak f_j$: at most $8$;
- **(Π2)** in the $M_2$ version only: the selected stem vertex $\mathfrak v_j\in\mathcal S_j$ of the derivative expansion of $V_{j,M_2}$ (S §8, S Lemma 9.1), its parent, and its $\le3$ children (the possible endpoint faces of S Lemma 9.1): at most $5$.

A vertex of $\mathcal G$ inside a regular object is protected if it is listed; the regular object then counts as protected (S §2, "an object containing a protected vertex remains protected when collapsed").

The caps $c_j$ need not be listed. A cap is a trivial tree, so it is not a descendant of any branching node and lies in no realization (T1349). Its partner $\mathfrak f_j$ is listed.

Thus
$$
b:=|\Pi|\le 13\cdot 2P=26P .\tag{2.1}
$$
For the derivative patterns of `fixedpoint` (T2312, T2331; RR M4, outside `flowerest1`) one adds the extra pinned vertices, at most $2$ per tree, so $b\le30P$.

Let $\Pi_{\rm sb}$ be the set of atoms of $\mathbb M_{\rm sb}$ whose node, or whose attached regular object, contains a protected vertex. A protected leaf, or a regular couple on a leaf pair, contributes the $\le2$ parent atoms. Hence $|\Pi_{\rm sb}|\le 2b$.

### 2.3 Twist-active sets and marked vines

**Definition 2.3.** Let $\mathbb V\subset\mathbb M_{\rm sk}$ be a (CL) vine with nodes $\mathfrak u_1,\mathfrak u_{11},\mathfrak u_2,\mathfrak u_{21},\mathfrak u_{22},\dots$ (T1349, T1396). Its *twist-active set* $\mathbf A(\mathbb V)$ is:

- the set of nodes of $\mathcal G_{\rm sk}[\mathbb V]\setminus\{\mathfrak u_1\}$ (T1377);
- together with all vertices of $\mathcal G$ in $\mathcal T_{(\mathfrak m)}$, $\mathfrak m\in\mathcal N[\mathbb V]\setminus\{\mathfrak u_1\}$;
- and all vertices of $\mathcal G$ in $\mathcal Q_{(\mathfrak l,\mathfrak l')}$, $\mathfrak l,\mathfrak l'\in\mathcal L[\mathbb V]$.

These are exactly the data of $\mathcal K^{\mathbb V}_{(\mathcal G)}$ (T1730–1739), i.e. everything a unit LF twist at $\mathbb V$ can change (T1470–1477, T1731).

$\mathbb V\in\mathscr V$ (T1934) is **marked** if $\mathbf A(\mathbb V)\cap\Pi\neq\varnothing$, and **unmarked** otherwise. Put $b_V:=\#\{\text{marked vines in }\mathscr V\}$.

**Lemma 1 (disjointness).** The sets $\mathbf A(\mathbb V)$, $\mathbb V\in\mathscr V$, are pairwise disjoint. Hence $b_V\le b$.

### 2.4 Invariance under unmarked twists

**Lemma 2.** Let $\mathbb V\in\mathscr V$ be unmarked, core, and satisfy the assumptions of Definition `lftwist` (T1468). Let $\mathcal G'$ be a unit LF twist of $\mathcal G$ at $\mathbb V$. Then:

- **(a)** $\Pi_{\mathcal G'}=\Pi_{\mathcal G}$, under the identification of all vertices outside $\mathbf A(\mathbb V)$ (T1470–1472). Also $\mathbf A_{\mathcal G'}(\mathbb V)\cap\Pi_{\mathcal G'}=\varnothing$. Markedness of every vine of $\mathscr V$ is unchanged.
- **(b)** The truncation labels of S Lemma 2.1(4) (T2273, T2290), hence membership in $\mathcal H^{\rm tr}_{p+1}$ of the chosen type, are unchanged.
- **(c)** The stem-layer property (T2261) is unchanged (T2298).
- **(d)** In the $M_2$ version, i.e. with $|k|\ge M_1^{10}$, an SG vine satisfies $\mathbf A(\mathbb V)\cap{\rm stem}=\varnothing$. The stem filters $\vartheta(\Omega_{\mathfrak w}/R)$, the selected vertex, its faces and its frozen resonance are common to $\mathcal G$ and $\mathcal G'$.
- **(e)** Pins and caps are untouched.
- **(f)** The frontier shells are handled family-wise by S Lemma 5.3, which sums the full LF class with a common scale per original tree.

Consequently "LF twist at unmarked vines of $\mathscr V_0$" is an equivalence relation on the summed family. Each class sum is the sum of one fixed integrand over an LF family, as T1936–1944 require.

### 2.5 Stage 1′ (the modified reduction)

Use the notation of T1927–1965. Let:

- $\mathscr C$ be the collection of Lemma `vinechainlem` (T1930) for $\mathbb M_{\rm sk}$;
- $\mathscr V$ be T's collection (T1934, unchanged; in particular one ingredient of each HVC and of each root VC is still skipped);
- $\mathscr V^\natural:=\mathscr V\setminus\{\text{marked}\}$.

**Congruence′** is LF twisting at the core vines of $\mathscr V^\natural$ that satisfy the assumptions of T1468. As in T1944, decompose into SG/LG/ZG specifications for every object of $\mathscr C$. These are invariant under congruence′, by the decoration bijection T1452. Then restrict to twists at the SG ones.

- $\mathscr V_0$: the vines of $\mathscr V$ in SG chains (T1944).
- $\mathscr V_0^\natural:=\mathscr V_0\cap\mathscr V^\natural$.
- A **run** is a maximal concatenation of consecutive vines of $\mathscr V_0^\natural$ inside one chain of $\mathscr V_0$. The runs are $\mathbb U_1,\dots,\mathbb U_{q_{\rm sk}}$. Each run is a (CL) vine chain, by Corollary `blockchainprop` (T1379).
- $\mathcal G_{\rm sb}$: the result of splicing all vines of $\mathscr V_0^\natural$ (T1352). $\mathbb M_{\rm sb}:=\mathbb M(\mathcal G_{\rm sb})$.
- $H$: the hinge atoms, i.e. the merged runs ($|H|=q_{\rm sk}$).

For an SG object $\mathbb W\in\mathscr C$ that is a VC or HVC, let $m_{\mathbb W}$ be its number of marked ingredients. Its **survivors** are:

- the ingredient skipped by T1934 (or the (CN) ingredient of a non-root VC), if any;
- its marked ingredients.

Let $\mathscr W_E:=\{\mathbb W:\ m_{\mathbb W}\ge1\}$ and
$$
\mathscr C_E:=\{\text{survivors of }\mathbb W:\ \mathbb W\in\mathscr W_E\},\qquad N_E:=|\mathscr C_E|\le\sum_{\mathbb W\in\mathscr W_E}(1+m_{\mathbb W})\le 2b_V\le 2b .\tag{2.2}
$$

- $\mathscr C_1$: T's collection (T2050), formed only from the objects with $m_{\mathbb W}=0$. These are SG HV's (marked or not, since nothing of an HV is in $\mathscr V$), and the SG (CN) or root (CL) vines into which SG VC/HVC's with $m_{\mathbb W}=0$ reduce.
- $B$: the set of joints of the vines of $\mathscr C_E$, so $|B|\le 2N_E\le4b$.

**Support hypothesis (restating T2040 with the RR correction).** All decorations $\mathfrak O_{\rm sb}$ are inherited from $(k_1,\dots,k_{2R})$-decorations of $\mathcal G_{\rm sk}$. Here $(k_1,\dots,k_{2R})$ are the original roots $k$ and the cap roots $k'$. The decorations satisfy
$$
\widetilde\epsilon_{\mathfrak O_{\rm sb}}\cdot\mathcal Z_{\mathfrak O_{\rm sb}}\neq0,\qquad
\widetilde\epsilon=\prod_{v\notin H}\epsilon_v,\tag{2.3}
$$
where:

- $\epsilon_v$ is T646 at $\mathfrak n(v)$, kept at **every** non-hinge atom: atoms of $B$, of survivors, pinned atoms and face atoms included. T1957 drops it only at hinges.
- $\mathcal Z$ is the product of the SG/LG/ZG indicators of all objects of $\mathscr C$.
- Pins, caps and cutoffs impose no support restriction. Pins fix times; caps fix $k_{\mathfrak f_j}=k'$ through the decoration; cutoffs are weights.

---

## 3. Statement

> **Theorem 7.5′.** Let $\mathcal G,\Pi,b$ be as in §2, with Stage 1′ performed. For every decoration satisfying (2.3):
>
> **(1) Bond count and connectedness (T2042 kept).** $\mathbb M_{\rm sb}$ is connected, with $n_{\rm sb}$ atoms and $2n_{\rm sb}-R$ bonds, so $\chi(\mathbb M_{\rm sb})=n_{\rm sb}-R+1$ (T2113). Every later removal of a vine of $\mathscr C_E$ obeys the cut bookkeeping (4.6), the specialization of S (7.4).
>
> **(2) Collections (T2043).**
> - $\mathscr C_1$ is a disjoint collection of SG vine-like objects, each an HV, a (CN) vine or a root (CL) vine.
> - There are exactly $q_{\rm sk}$ hinge atoms, and every triple bond has an endpoint in $H$.
> - $\mathscr C_E$ consists of $N_E\le 2b$ objects. Each is an SG vine, or an SG HV when the image of an HVC is a single survivor [Rev. 1, 75-W1; §11.1]. Each is disjoint from every object of $\mathscr C_1$. Two of them share at most one joint, and only if they are consecutive survivors of one $\mathbb W\in\mathscr W_E$.
> - $|B|\le 4b$.
>
> **(3) Degenerate atoms (T2044).** Every degenerate (ZG) atom not in $H$ is tame. Its fixed values range over $\{k,k'\}$ when $d(v)<4$.
>
> **(4) Uncovered SG objects (T2045).** Let $\mathbb U$ be an SG vine-like object with $\mathbb U\cap(H\cup B)=\varnothing$ that is not a subset of an object of $\mathscr C_1\cup\mathscr C_E$. Then $\mathbb U$ is a subset of a DV, or of an LG or ZG vine-like object, of $\mathbb M_{\rm sb}$. That object is disjoint from all objects of $\mathscr C_1\cup\mathscr C_E$ and from $H\cup B$. Here $\mathbb U$ is in one of the cases of Lemma `subsetvc` (T2431).
>
> **(5) Hinge pairs (T2046).** For each hinge $v$ there are bonds $(\ell_1,\ell_2)$ at $v$ with $(v,\ell_1,\ell_2)$ SG.
> - If $v$ is a joint of an SG vine (or HV) of $\mathscr C_1$, then $(\ell_1,\ell_2)$ is chosen to belong to that vine (or to the adjoint vine).
> - If $v$ is a joint of a vine of $\mathscr C_E$, then $(\ell_1,\ell_2)$ is chosen in that vine. Between two consecutive survivors, choose it in the one removed first.
> - **[Rev. 1, 75-F1; §11.2]** The same rule gives the designated pair of requirement (e) at **every** joint $J\in B$ shared by two consecutive survivors, hinge or not: the pair is the bonds of the survivor removed first. Both survivors have the gap of their chain, so requirement (f)'s single label $Q_J$ is consistent.
>
> **(6) Hinge configuration (T2047).** Let $\mathbb U$ be an SG vine-like object with $\mathbb U\cap B=\varnothing$, not a subset of an object of $\mathscr C_1\cup\mathscr C_E$, that contains a hinge. Then $\mathbb U$ contains a hinge $v$ that is interior to $\mathbb U$, or is a joint of $\mathbb U$ with exactly one of $(\ell_1,\ell_2)$ in $\mathbb U$.
>
> **(6′) Objects meeting $B$.** Every SG vine-like object $\mathbb U$ with $\mathbb U\cap B\neq\varnothing$ satisfies one of:
> - it is a subset of an object of $\mathscr C_E$;
> - it contains a bond of an object of $\mathscr C_E$;
> - it contains a hinge in the configuration of (6).
>
> **(7) Counting.** Run Stage 2 (T2101–2148) with these changes:
> - $\mathscr C_2$ is built from the containers of (4).
> - Requirement (e) is extended to joints of $\mathscr C_E$, and requirement (f) to SG atoms not interior to an object of $\mathscr C_1\cup\mathscr C_2\cup\mathscr C_E$.
> - Operation 1 is applied in the order: $\mathscr C_1$ (CN, root CL), $\mathscr C_1$ (HV), then $\mathscr C_E$ vine by vine along each chain, then $\mathscr C_2$.
>
> Then:
> - Proposition `excessprop1` (1),(2) hold verbatim, and (3) holds with $2R-1+N_E$.
> - Proposition `finalmol` holds, with "at most $R$ imperfect components" (in its campaign-repaired form, E9) increased by $N_E$.
> - (finalcount1) (T2115) holds with the extra factor $L^{(3\gamma_0+5\eta^2)N_E}\le L^{2N_E}$.
>
> **(8) Crude bound.** (finalsbest1) (T2076) holds with the extra factor $L^{(60d+2)|S_{\rm split}|}C_\vartheta^{\,n_{\rm sb}}$, where $S_{\rm split}:=B\cup\Pi_{\rm sb}$, $|S_{\rm split}|\le 6b$, and $C_\vartheta$ is the absolute constant of Lemma F. Here:
> - maximal ladders are split at $H\cup S_{\rm split}$;
> - stem filters on ladder atoms are allowed (Lemma F);
> - frontier factors on ladder bonds are allowed (§4.8, RR M3);
> - protected objects enter only through their OPEN 7.3/8.2 bounds.
>
> **(9) Same gains away from the exception set.** The interpolated bound (finalproof2) (T2225) holds with the extra factor $L^{(60d+2)|S_{\rm split}|+2N_E}\,C_\vartheta^{\,n}\le L^{(360d+16)b}C_\vartheta^{\,n}$, times the contracted costs of OPEN 7.3/8.2 for protected objects, pins and faces. All of the following are retained:
> - every incoherency gain, except $\le2$ units per atom of $S_{\rm split}$;
> - every $\eta^6$ gain per unit of $\rho_{\rm sb}+q_{\rm sk}$, survivors included;
> - every bad-vine gain of every unmarked SG vine.
>
> Retained ladder pieces contain no atom of $H\cup S_{\rm split}$. Hence $\mathcal K^\dagger(k[\mathbb W])$ and the protected amplitudes do not depend on their internal variables, which is the hypothesis of T2081/T2083.

**Lemma F (filtered ladders).** *[Rev. 1, 75-LF: Lemma F is proved relative to the explicit hypothesis (E5′) of §11.5.]* Let $\mathbb L$ be a ladder as in `ladderl1new` (T1978–1987), with no atom in $H\cup S_{\rm split}$. Let $\mathcal S\subset\mathbb L$ and scales $R_v\ge L/2$, $v\in\mathcal S$, be arbitrary. Insert $\prod_{v\in\mathcal S}\vartheta(\Omega_{\mathfrak n(v)}/R_v)$ into the ladder kernel $\mathcal K^{\mathbb L}$, and into the E5-repaired kernel core.

Then (redladder2) holds with the extra factor $C_\vartheta^{|\mathcal S|}$, uniformly in the boundary data and in $(R_v)$, where
$$
C_\vartheta:=40\int_{\mathbb R}(1+|\xi|)\,|\widehat\vartheta(\xi)|\,d\xi<\infty .
$$
$C_\vartheta$ depends only on the fixed Gevrey-2 cutoff $\vartheta$ of S §8.

---

## 4. Proofs

### 4.1 Proof of Lemma 1

**Branching nodes.** By Proposition `block_clcn`(2) (T1352), the branching nodes of $\mathcal G_{\rm sk}[\mathbb V]$ are exactly the nodes $\mathfrak n(v)$, $v\in\mathbb V$. So the skeleton branching nodes of $\mathbf A(\mathbb V)$ are $\mathfrak n(v)$ for $v\in\mathbb V\setminus\{v_1\}$, where $v_1$ is the atom of $\mathfrak u_1$.

**Leaves.** The leaves of $\mathcal G_{\rm sk}[\mathbb V]$ are completely paired among themselves (T1349(iii)). Each has its parent in $\mathcal G_{\rm sk}[\mathbb V]$, so the parent is $\mathfrak n(v)$ for some $v\in\mathbb V$.

**Regular objects.** Each regular object sits on exactly one skeleton node or leaf pair (T870).

**Pairs of vines of $\mathscr V$.** Two vines of $\mathscr V$ are either atom-disjoint, or consecutive ingredients of one (CL) chain sharing exactly one joint (T1433, T1936).

- *Atom-disjoint.* The branching nodes are disjoint. A common leaf would have a common parent atom. Hence the two sets $\mathbf A$ are disjoint.
- *Consecutive.* Order the chain upward: $\mathbb V_j$ below $\mathbb V_{j+1}$. Then $\mathfrak u_1^j=\mathfrak u_2^{j+1}$ and $\mathfrak u_{11}^j=\mathfrak u_{23}^{j+1}$ (D23 1673; T2246 for the monotone layers).
  - The two children of $\mathfrak u_1^j$ other than $\mathfrak u_{11}^j$ are therefore $\mathfrak u_{21}^{j+1},\mathfrak u_{22}^{j+1}$.
  - $\mathcal G_{\rm sk}[\mathbb V_j]\setminus\{\mathfrak u_1^j\}$ lies among the descendants of these two children (T1349).
  - Those descendants are excluded from $\mathcal G_{\rm sk}[\mathbb V_{j+1}]$ (T1349).
  - The shared node $\mathfrak u_1^j$, and $\mathcal T_{(\mathfrak u_1^j)}$, belong to $\mathbf A(\mathbb V_{j+1})$ only.

So the sets $\mathbf A$ are pairwise disjoint. Each protected vertex lies in at most one of them, hence $b_V\le|\Pi|=b$. ∎

### 4.2 Proof of Lemma 2

**What a unit LF twist changes** (T1429–1434, T1447–1454, T1470–1477). It changes only:

- (i) the parent of $\mathfrak u_2$ within $\{\mathfrak u_3,\mathfrak u_4\}$ (for Vine (I): its slot among the children of $\mathfrak u_1$);
- (ii) the sign of $\mathfrak u_2$, and the positions of the free subtrees at $\mathfrak u_{21},\mathfrak u_{22}$, which are switched as wholes;
- (iii) $\mathcal T_{(\mathfrak u_2)}$ and $\mathcal Q_{(\mathfrak u_{23},\mathfrak u_0)}$, which are replaced by coherent objects with the same total order and the same total number of layer-$p$ branching nodes (T1476).

Every vertex outside $\mathbf A(\mathbb V)$ keeps its identity, sign, layer and parent, and the free subtrees keep their contents. The decorations correspond bijectively, with only $k_{\mathfrak u_2}$ and $k_{\mathfrak u_{23}}$ exchanged (T1452).

**(b) Truncation labels.** Take a vertex $x\notin\mathbf A(\mathbb V)$.

- If $x$ lies outside the subtree of $\mathfrak u_1$, or inside a free subtree, its subtree is unchanged.
- If $x=\mathfrak u_1$ or $x$ is an ancestor of $\mathfrak u_1$, its subtree changes only internally, and its layer-p count is preserved by (iii).

With $n\le N^4$, the labels of S Lemma 2.1(4) are layer-$p$ counts (T1483, T2290). Original trees lie entirely in layer $p$ (T2261; RR §3). The labels are the layer-p counts of:

- the trees;
- the subtrees at root children;
- the subtrees at flower siblings;
- the tree with $\mathfrak f^{\rm pr}$ collapsed, whose count is the tree count minus the two sibling counts minus one (T2273).

Every one of these is rooted at a vertex of $\Pi$, and $\Pi\cap\mathbf A(\mathbb V)=\varnothing$. Hence all labels are preserved. The orders of the child subtrees and of the lower replacements are handled by T1483 in the same way.

**(a) The protected set.**

- *Roots.* A root is never in a realization.
- *Root children.* The only vertex of $\mathbf A(\mathbb V)$ whose parent can change is $\mathfrak u_2$ (together with the root of the replacing $\mathcal T'_{(\mathfrak u_2)}$, which takes its slot). For vines (II), its parents $\mathfrak u_3,\mathfrak u_4$ lie in $\mathcal G_{\rm sk}[\mathbb V]\setminus\{\mathfrak u_1\}$ (T1405–1413). Neither is a root, since a root lies in no realization. So $\mathfrak u_2$ cannot become a root child. For Vine (I), $\mathfrak u_2$ is a child of $\mathfrak u_1$ in both $\mathcal G$ and $\mathcal G'$. If $\mathfrak u_1$ is a root, then $\mathfrak u_2\in\Pi\cap\mathbf A(\mathbb V)$ already in $\mathcal G$, which is excluded.
- *Flower, parent, siblings.* The flower is a leaf outside $\mathbf A(\mathbb V)$. If its parent were $\mathfrak u_2$ (i.e. $\mathfrak f=\mathfrak u_{21}$ or $\mathfrak u_{22}$), then $\mathfrak f^{\rm pr}\in\Pi\cap\mathbf A$, which is excluded. So $\mathfrak f$, $\mathfrak f^{\rm pr}$ and the siblings lie in a free subtree or outside the subtree of $\mathfrak u_1$, and are unchanged.
- *Selected vertices.* These are treated in (d).

Hence $\Pi_{\mathcal G'}=\Pi_{\mathcal G}$ and $\mathbf A_{\mathcal G'}(\mathbb V)\cap\Pi=\varnothing$.

**Markedness of the other vines.** For $\mathbb V''\ne\mathbb V$, the set $\mathbf A(\mathbb V'')$ is unchanged as a set, and its data are unaffected (Lemma 1; T1948):

- if $\mathbb V''$ is the consecutive vine above, $\mathbf A(\mathbb V'')\ni\mathfrak u_1^{\mathbb V}$ and $\mathcal T_{(\mathfrak u_1^{\mathbb V})}$, and the twist replaces neither;
- if it is below, $\mathbf A(\mathbb V'')$ lies inside a free subtree.

**(c) Stem layers.** This is T2298, which RR does not dispute.

**(d) The $M_2$ version.** Here $|k|\ge M_1^{10}$. By S Lemma 9.2 in RR's corrected form, an SG (CL) block whose top $\mathfrak u_1$ is an ancestor of the flower has its stem exiting through $\mathfrak u_{11}$. If $\mathfrak u_1$ is not an ancestor of the flower, the stem avoids its subtree. In both cases ${\rm stem}\cap\mathbf A(\mathbb V)=\varnothing$.

*Stem filters.* A stem filter $\vartheta(\Omega_{\mathfrak w}/R)$ depends on the momenta at $\mathfrak w$ and its children. Since only $k_{\mathfrak u_2},k_{\mathfrak u_{23}}$ move, and the parent of $\mathfrak u_{23}$ is $\mathfrak u_2\in\mathbf A$, only $\mathfrak w=\mathfrak u_1$ could see a change. By RR's added sentence to Lemma 9.3, the middle slot of $\mathfrak u_1$ carries $k_{\mathfrak u_{23}}$ in both (I-a) and (I-b), and for the other vines the interior children of $\mathfrak u_1$ are untouched. So all stem filters are common to $\mathcal G$ and $\mathcal G'$.

*Selected vertex.* Its children are in $\Pi$. If $\mathfrak v_j=\mathfrak u_1$, then its children other than $\mathfrak u_{11}$ lie in $\mathbf A$, which is excluded. Hence $\mathfrak v_j$, its parent and its children lie outside $\mathbf A(\mathbb V)$, and its resonance, faces and frozen value are common to both gardens.

**(e) Pins and caps.** $\mathfrak f^{\rm pr}\notin\mathbf A$ and the caps lie in no realization.

**(f) Frontier shells.** This is S Lemma 5.3, together with RR's recommended sentence: LF twists preserve layers, so the frontier set outside $(\mathcal Q,\mathcal T)$ is permuted together with the decorations.

**Consequence.** Congruence′ classes partition the family. A class sum is a sum over all LF twists at the unmarked core vines of each run. That is the family required by T1742–1755 and S Lemma 5.3, whose hypotheses all hold for runs:

- the realization lies in one original tree (T1349);
- there is a common scale per tree, after S Lemma 3.2;
- no mark (O63);
- no face, since face vertices are in $\Pi$. ∎

### 4.3 Stage 1′ identity

T1942–1965 apply with $\mathscr V_0$ replaced by the runs. The three observations T1948–1950 hold for the runs:

- Runs of one chain are separated by at least one survivor, so they share no atom.
- Different chains are disjoint.
- The SG/LG/ZG indicators depend only on the chain-level gaps.

Therefore (redvine) (T1955–1957) holds with $q_{\rm sk}$ runs $\mathbb U_j$ and with $\widetilde\epsilon=\prod_{v\notin H}\epsilon_v$, as in (2.3). The nodes of the survivors are ordinary nodes of $\mathcal G_{\rm sb}$, with their $\epsilon$, phases and regular objects.

(redvine2) (T1959–1965) follows from:

- `proplayer1/2` and S Lemma 4.1 for unprotected regular objects;
- S Lemma 5.3 for the runs, giving the factor $L^{-\eta^8g_{\rm sk}-\eta^2b_{\rm sk}+\eta^7q_{\rm sk}}$, with $b_{\rm sk}$ the bad vines in runs;
- OPEN 7.3/8.2 for protected regular objects.

$\mathcal K^\dagger$ depends only on $k[\mathbb W]$, the bonds at hinge atoms (T1970).

### 4.4 Reductions of chains; clauses (1)–(3)

**Lemma 3 (images of SG chains).** Let $\mathbb W\in\mathscr C$ be an SG VC or HVC.

- (i) If $m_{\mathbb W}=0$, its image in $\mathbb M_{\rm sb}$ is as in T2050: a single atom, an SG HV, an SG (CN) vine, or an SG root (CL) vine.
- (ii) If $m_{\mathbb W}\ge1$, its image $\mathbb W'$ is a VC (an HVC if $\mathbb W$ is one). If $\mathbb W$ is an HVC with a single survivor, $\mathbb W'$ is that survivor plus the extra bond $e^*$, i.e. an SG **HV** [Rev. 1, 75-W1; §11.1].
  - Its ingredients are exactly the survivors $\mathbb S_1,\dots,\mathbb S_s$, $s\le 1+m_{\mathbb W}$, in their order.
  - Consecutive survivors share one joint, which is a hinge exactly when a run lay between them.
  - An outer joint of $\mathbb W'$ is a hinge exactly when the corresponding end run was spliced.
  - Each $\mathbb S_i$ is an SG vine of the same type and gap as in $\mathbb M_{\rm sk}$, with unchanged interior atoms.

*Proof.* A run is a (CL) block (T1379). Splicing it merges exactly its atoms, including its two outer joints, into one atom, and keeps every other bond, redirecting its endpoint (T1352(2)). A survivor adjacent to a run has one joint in the run. That joint becomes the hinge, and the survivor's two bonds at it become two bonds at the hinge. Interior atoms keep all their bonds. The block conditions (T1328) are degree conditions within the group, so $\mathbb S_i$ is still a block of the same vine type. Its gap is unchanged because the decoration is inherited (T1938). Part (i) is Corollary `blockchainprop` exactly as in T2050. ∎

**Clause (1).** $\mathcal G_{\rm sk}$ is irreducible because $\mathcal G$ is: the replacements of T870 do not change the pairings between trees. Splicing a (CL) block removes a completely paired region inside one tree (T1349(iii)) and keeps every pairing between distinct trees and the width. So $\mathcal G_{\rm sb}$ is irreducible of width $2R$, as T2052 says for $\mathcal G_{\rm sb}$. Proposition `propcplmol` (T1304) then gives:

- $\mathbb M_{\rm sb}$ is connected, with $n_{\rm sb}$ atoms and $2n_{\rm sb}-R$ bonds;
- $\chi=E-V+F=n_{\rm sb}-R+1$, which is the identity used at T2113.

The bookkeeping (4.6) is proved in §4.6.

**Clause (2).**

- The objects of $\mathscr C_1$ come from distinct objects of $\mathscr C$, one each. Distinct objects of $\mathscr C$ are disjoint (T1930), and every hinge belongs to the reduction of one object. Hence $\mathscr C_1$ is disjoint.
- $|H|=q_{\rm sk}$ by construction.
- Triple bonds of $\mathbb M_{\rm sb}$ arise only at merged atoms, because $\mathbb M_{\rm sk}$ has none (T2043, T2052 via D23 1741(c)). Survivors are not merged.
- $N_E\le2b$ is (2.2). The disjointness from $\mathscr C_1$ and the sharing structure are Lemma 3.
- $|B|\le2N_E\le4b$.

**Clause (3).** Let $v\notin H$ be degenerate, i.e. have two bonds of opposite directions with equal momenta. Write $\mathfrak n=\mathfrak n(v)$ with children $(\mathfrak n_1,\mathfrak n_2,\mathfrak n_3)$.

- Opposite directions are opposite signs in (decmole1) (T1309), so the equal pair is one of $(\mathfrak n_1,\mathfrak n_2)$, $(\mathfrak n_3,\mathfrak n_2)$, $(\mathfrak n,\mathfrak n_1)$, $(\mathfrak n,\mathfrak n_3)$.
- By conservation, the last two cases imply the first two.
- So $k_{\mathfrak n_2}\in\{k_{\mathfrak n_1},k_{\mathfrak n_3}\}$. Then $\epsilon_v\neq0$ (by (2.3), since $v\notin H$) forces $k_{\mathfrak n_1}=k_{\mathfrak n_2}=k_{\mathfrak n_3}=k_{\mathfrak n}$ (T556, T564).
- Every bond at $v$ therefore carries this common value. A missing bond, when $d(v)<4$, is an edge to a root or a pairing with a root, and carries an external value $k$ or $k'$ (T1314–1316).

This is tameness in the sense of T2044. ∎

### 4.5 Clauses (4), (5), (6), (6′)

**Two facts.**

- **(P)** If $\mathbb U$ is a vine-like object of $\mathbb M_{\rm sb}$ with $\mathbb U\cap H=\varnothing$, then $\mathbb U$ is a vine-like object of $\mathbb M_{\rm sk}$ with the same atoms, bonds and gap. Bonds between unmerged atoms are unchanged, and the defining conditions are internal (T1328, T1384).
- **(Q)** Every vine-like object of $\mathbb M_{\rm sk}$ lies in a unique $\mathbb Y\in\mathscr C$. The objects of $\mathscr C$ are pairwise disjoint atomic groups (T1930).

*Remark.* A DV is saturated: each of its atoms has degree 4 inside it. So a DV is a whole saturated component, which T1295(ii) excludes from the connected, unsaturated $\mathbb M_{\rm sb}$. DVs are kept in the statements only for fidelity to T.

**Clause (4).** Let $\mathbb U$ be as in (4), and let $\mathbb Y\supset\mathbb U$ be given by (P) and (Q).

- (a) $\mathbb Y$ is a DV, or an LG or ZG vine-like object. None of its vines is in $\mathscr V_0$, which contains only SG chains. DV's and HV's contribute nothing to $\mathscr V$ (T1934). So $\mathbb Y$ is intact in $\mathbb M_{\rm sb}$. By (Q) it is disjoint from every other object of $\mathscr C$, hence from all objects of $\mathscr C_1\cup\mathscr C_E$ and from $H$ and $B$, which are atoms of, or merged runs of, SG objects $\ne\mathbb Y$. Lemma `subsetvc` (T2431) applies because $\mathbb Y\supset\mathbb U$ with $\mathbb U$ SG.
- (b) $\mathbb Y$ is an SG HV. Then $\mathbb Y\in\mathscr C_1$, which is excluded by hypothesis.
- (c) $\mathbb Y$ is an SG VC/HVC with $m_{\mathbb Y}=0$. The unmerged atoms of $\mathbb Y$ are those of its $\mathscr C_1$-object (Lemma 3(i)), so $\mathbb U$ lies in that object. This is excluded (T2052; D23 1743).
- (d) $\mathbb Y\in\mathscr W_E$. The unmerged atoms of $\mathbb Y$ are the non-hinge atoms of its survivors. Suppose $\mathbb U$ meets two survivors.
  - $\mathbb U$ is connected (T1386 with T1339(i)).
  - Among the survivors' atoms, bonds are survivors' bonds or the extra bond of an HVC, whose endpoints lie in $B\cup H$.
  - A survivor's bond joins two atoms of that survivor.
  - So a path inside $\mathbb U$ from one survivor to another passes through a shared joint, which lies in $B$, or uses the extra bond. Both are excluded.

  Hence $\mathbb U$ lies in one survivor, which is excluded.

Only case (a) remains. ∎

**Clause (5).** A hinge $h$ is a merged run. At each of the run's outer joints, the bonds not in the run form a pair with the run's gap, which is SG. When the joint has degree $4$ there are two such pairs, one at each end (D23 1741(d); T2050).

- If $h$ is a joint of a survivor $\mathbb S$, then $\mathbb S$'s two bonds at $h$ are the non-run bonds of the run's outer joint at that end, i.e. one of these pairs. Choose them.
- If $h$ lies between two survivors, both pairs are survivor bonds. Choose the pair of the survivor removed first.
- For $\mathscr C_1$ the choice is exactly T2050.

The choices are consistent with requirement (e) (T2104), because each hinge belongs to the reduction of one object. ∎

**Clause (6).** Suppose (6) fails for some $\mathbb U$. Then every hinge of $\mathbb U$ is a joint of $\mathbb U$ whose two $\mathbb U$-bonds are both in $(\ell_1,\ell_2)$ or both outside it.

- If $d(h)\le3$, two opposite-direction bonds not both in $(\ell_1,\ell_2)$ contain exactly one of them, so this case cannot occur.
- If $d(h)=4$, the complementary pair is the run's other-end pair, again SG with the same gap.

Replace each such hinge by its run in $\mathbb M_{\rm sk}$. The result is a concatenation (T1330, disjointlem (b) T1341), hence an SG vine-like object of $\mathbb M_{\rm sk}$, exactly as in D23 1745–1746. By (Q) it lies in a unique SG $\mathbb Y\in\mathscr C$. Its ingredients other than the runs are those of $\mathbb U$; they are unspliced, hence survivors or the $\mathscr C_1$-ingredient.

- If $m_{\mathbb Y}=0$, then $\mathbb U$ lies in the $\mathscr C_1$-object of $\mathbb Y$, which is excluded.
- If $m_{\mathbb Y}\ge1$, the hinge joint of $\mathbb U$ is a joint of a survivor, hence lies in $B$, contradicting $\mathbb U\cap B=\varnothing$. ∎

**Clause (6′).** Let $J\in\mathbb U\cap B$ be a joint of a survivor $\mathbb S\subset\mathbb W'$, with $\mathbb W\in\mathscr W_E$.

- If $J$ is interior to $\mathbb U$, then $\mathbb U$ contains all bonds at $J$, including those of $\mathbb S$.
- If $J$ is a joint of $\mathbb U$ and a $\mathbb U$-bond at $J$ is an $\mathbb S$-bond, we are done.
- If $J$ is shared with a consecutive survivor $\mathbb S'$ and the $\mathbb U$-bonds are $\mathbb S'$-bonds, we are done.

It remains that $J$ is an outer joint of $\mathbb W'$ and the $\mathbb U$-bonds at $J$ are not survivor bonds. Assume that $\mathbb U$ contains no hinge in configuration (6). Then every hinge of $\mathbb U$ is an "aligned" joint, as in the proof of (6). Replace each such hinge by its run, as there.

- If $J$ is itself a hinge (its run $\mathbb R_J$ is the spliced end of $\mathbb W$), $\mathbb U$ uses at $J$ the pair of $\mathbb R_J$'s outer joint lying outside $\mathbb W$.

In every sub-case we obtain an SG vine-like object of $\mathbb M_{\rm sk}$ that contains an atom of $\mathbb W$: $J$, or the run $\mathbb R_J\subset\mathbb W$. By (Q) it is contained in $\mathbb W$. But at $J$ (or at $\mathbb R_J$'s outer joint) it uses bonds leaving $\mathbb W$, while $\mathbb W$ is an atomic group containing all bonds between its atoms.

- If the bond is the extra bond $e^*$ of an HVC, the other $\mathbb U$-bond at $J$ is either an $\mathbb S$-bond (done) or a bond leaving $\mathbb W$ (the same contradiction).

This contradiction proves (6′). ∎

### 4.6 Destruction, single-vine removal, bookkeeping

**Lemma 4 (destruction).**

- (i) Cutting an atom $v$ along $(\ell_1,\ell_2)$ (T2119) destroys every vine-like object $\mathbb U$ in which $v$ is interior, or is a joint with exactly one of $\ell_1,\ell_2$ in $\mathbb U$. After the cut, the $\mathbb U$-bonds at $v$ end at two distinct atoms.
- (ii) Removing a block $\mathbb S$ destroys every $\mathbb U$ that contains a bond of $\mathbb S$.

*Proof.* Immediate. ∎

**Lemma 5 (single SG vine removal, joints of any degree).** Let $\mathbb M_{\rm pre}$ be a molecule of the Stage-2 process. Let $\mathbb S$ be an SG vine of gap $r$, $|r|\sim_0Q$, all of whose bonds are present, with joints $J_1\ne J_2$ of arbitrary degree. Cut $J_1,J_2$ along the bonds of $\mathbb S$ and delete $\mathbb S$. Then $\Delta F\in\{0,1\}$, and:

- if $\Delta F=0$, the deviation satisfies (excesseqn2), with two new $\alpha$-atoms labelled $Q$;
- if $\Delta F=1$, it satisfies (excesseqn2+). A fresh remnant becomes $\beta$. A re-cut remnant, i.e. the isolated half at a joint that was already cut, keeps its $\alpha/\beta$ label [Rev. 1, 75-F2; ledger in §11.3].

*Proof.* **$\Delta F\le1$.** Interior atoms of $\mathbb S$ have all their bonds in $\mathbb S$. So every remaining atom of the old component of $\mathbb S$ is joined to $J_1^o$ or to $J_2^o$, and that component becomes at most two components.

**The deviation bounds.** These are the computations of D23 1797–1801 for $\Delta F=0$ (with the $\kappa$-refinement D23 1803), and of T2169–2177 for $\Delta F=1$. They use only:

- (i) the unit-ball localization of all bonds;
- (ii) the gap restriction at one joint;
- (iii) the $\Gamma$-restrictions at the atoms of $\mathbb S$. Through the reparametrization of `vineest` (T1772ff) these give (basiccount01)/(basiccount02) (T2459–2466) for the rung and core variables, and the factors $\mathfrak X_j^{z_j}$ of the $\le3$ ladders inside $\mathbb S$ (T1519);
- (iv) when $\Delta F=1$, the conservation law and the $\Gamma$-restrictions summed over the new component. These fix $k_{\ell_1}\pm k_{\ell_2}$ and confine $|k_{\ell_1}|^2\pm|k_{\ell_2}|^2$ to an interval of length $\le n_{\rm sb}\delta^{-1}L^{-2\gamma}$, after which (atomcountbd) (T2472) applies.

None of these uses $\deg J_i$.

**Exceptional atoms.** At pins and face atoms, the resonance is frozen by summing over its at most $(C_d\rho L)^{4d}$ values (S Lemma 7.1 in RR's radius-$\rho$ form, $\rho\le Cn$). This cost is booked as row 12 of §7. After freezing, every atom carries a $\Gamma$-restriction.

**Ladders.** The maximal ladders through a joint change length by $O(1)$ (as at D23 1788). This costs $(\log L)^{O(1)}$, which is absorbed by $L^{-\eta^3}$. ∎

**Bookkeeping (4.6).** Let
$$
D:=\sum_{\varepsilon\text{-atoms}}(4-d(v))+\sum_{\alpha,\beta\text{-atoms}}(2-d(v))=4V-2E-2(V_\alpha+V_\beta).\tag{4.6}
$$
Initially $D=2R$ (T2189).

- A removal as in Lemma 5 changes $D$ by $2\,\#\{i:\ J_i\text{ was already an }\alpha/\beta\text{-atom}\}$. In terms of S (7.4): deleting the interior $S_{\rm int}$ (with $q=4$, $D_{S_{\rm int}}=0$) gives $2v'-e'=R+2$. Re-labelling the two remnants with reference degree $2$ restores the defect. Re-cutting an $\alpha/\beta$-atom of degree $2$ to degree $0$ adds $2$.
- In the chain order of Theorem 7.5′(7), each internal joint of a chain is re-cut exactly once and the outer joints never. The label ledger of a re-cut is §11.3 [Rev. 1, 75-F2].

Hence $D_{\rm fin}\le D_{\rm T}+2N_E$, where $D_{\rm T}$ is the value produced by T's own operations.

### 4.7 Stage 2′

**Proposition 4.7 (`excessprop1`′).**

- (1) and (2) hold for all operations.
- (3) The number of component-creating Operations 1 is at most $2R-1+N_E$. If T's part reaches $2R-1$, one created component is an isolated $\beta$-atom (T2179, T2211).

*Proof.*

- *$\mathscr C_1$ (CN, root CL), removed first.* These are disjoint CN and root (CL) blocks of the garden molecule $\mathbb M(\mathcal G_{\rm sb})$. Proposition `cnblock` (T1367) bounds the result by $2R$ components, i.e. at most $2R-1$ creating operations, with the isolated-atom alternative (T2179).
- *HV's.* The extra bond keeps the two remnants connected, so $\Delta F=0$ (T2179).
- *$\mathscr C_E$.* Lemma 5 gives $\Delta F\le1$ each.
- *$\mathscr C_2$.* By (4), the containers are disjoint from all previously removed objects, from $H$ and from $B$. Earlier removals only cut atoms of $B$ or $\mathscr C_1$-joints and delete atoms of objects, so the containers are intact. Lemma `subsetvc` then gives $\Delta F=0$ (T2167).
- *Operations 2–4* are unchanged.
- The deviation bounds (1) and (2) are T2165–2177, together with Lemma 5. ∎

**Proposition 4.8 (`finalmol`′).** Every conclusion that T derives for $\mathbb M_{\rm fin}$ (T2183–2189, D23 1806–1817, with the campaign repairs E9, E11, E16, E17) holds, with one change: the bound on imperfect components is increased by $N_E$.

*Proof.*

- **$\alpha$-labels.** As in T.
- **$\varepsilon$-atoms.** An atom that is never cut is an $\varepsilon$-atom. If it were SG in $\mathbb M_{\rm sb}$, then either it is interior to an object of $\mathscr C_1\cup\mathscr C_2\cup\mathscr C_E$, and was deleted, or requirement (f) covers it and it was cut in Operations 1–3 (T2213). A ZG $\varepsilon$-atom is not a hinge, since hinges are SG (clause 5) and not interior to objects (T2116), hence cut. So it is tame by (3) and is handled as at T2152 / D23 §10.5 with the repairs above.
- **No triple bond.** A triple bond has a hinge endpoint (2). It is either an SG HV collected in Operation 1 (T2140), or it lies in a chain of $\mathscr W_E$ and is destroyed with its survivor.
- **Imperfect components.** The defect of each component is even (parity, T2189) and positive when imperfect. So $F_{\rm im}\le D_{\rm fin}/2\le R'+N_E$, where $R'$ is T's repaired bound.
- **Perfect components.** Their structure is unchanged, since Operations 2 and 4 are run to exhaustion (T2187, D23 1813–1815).
- **Vine components.** Let a component of $\mathbb M_{\rm fin}$ be an SG vine $\mathbb U$ with two degree-2 joints. Then $\mathbb U$ is a vine-like object of $\mathbb M_{\rm sb}$ that survived. By Lemma 4 it contains no bond of a removed object, and every cut atom in it was cut aligned.
  - (α) $\mathbb U$ lies in an object of $\mathscr C_1\cup\mathscr C_2\cup\mathscr C_E$. These are atomic groups, so the bonds of $\mathbb U$ were deleted. Contradiction.
  - (β) $\mathbb U\cap B\ne\varnothing$. By (6′), either it contains a $\mathscr C_E$ bond, which was deleted; or it contains a hinge in configuration (6), which was cut along its designated pair (in Operation 1E if the hinge is in $B$, otherwise in Operation 3), so $\mathbb U$ was destroyed by Lemma 4(i); or it is case (α).
  - (γ) $\mathbb U\cap B=\varnothing$ and $\mathbb U\cap H\neq\varnothing$. Destroyed by (6).
  - (δ) $\mathbb U\cap(H\cup B)=\varnothing$ and $\mathbb U$ is not in any object. By (4), $\mathbb U$ lies in a container and is T's own case (D23 1815–1817).

Our modification creates no new case. ∎

**(finalcount1′).** (together2) (T2207) multiplies the deviations and the final counts, and holds verbatim. Insert:

- $F_{\rm im}\le R'+N_E$;
- $p^+_{\rm op}\le(2R-2)+N_E$, after the isolated-$\beta$ observation of T2211 for the `cnblock` part;
- $Z_{\rm tot}$ as at T2212. Operation 1E creates no $\varepsilon$-atom and changes no $\varepsilon$-degree.

Also $\rho_{\rm fin}\ge\rho_{\rm sb}-C_0p_{\rm op}$, since each removal deletes one vine with at most three ladders and fewer than 20 other atoms (T1519, T2213). And $p_{\rm sb}\le p_{\rm op}$ (up to the factor 2 of E19), since the survivors' joints are SG atoms covered by requirement (f) and are cut in Operation 1E. Hence
$$
\mathfrak A_{\rm sb}\le L^{(2\gamma_0+5\eta^2)N_E+\gamma_0N_E}\cdot L^{-\eta^5(\rho_{\rm sb}+p_{\rm sb})}L^{(R-1)(4\gamma_0+1/10)} .
$$
For $R=1$, the $N_E$ additional imperfect components are bounded by the α/β-remnant argument of §11.4 [Rev. 1, 75-F3]. This replaces the earlier claim that they contain no low-degree $\varepsilon$-atom, which is withdrawn. Since $\gamma_0=1-\gamma<\tfrac12$, we have $3\gamma_0+5\eta^2<2$. This is (finalcount1) with the extra factor $L^{2N_E}$.

**(finalsbest2′).** Combine (redvine5) (T2091–2093), (ladderl1) (T1998) and (finalcount1′). The pins and faces in the time-$L^1$ factor belong to OPEN 7.3, and the frozen exceptional variables to row 12. The result is
$$
|\mathcal K_{\mathcal G_{\rm sb}}|\lesssim_1 L^{2N_E}(C_1\delta^{-10\nu})^{n_{\rm sb}}L^{-\eta^6(\rho_{\rm sb}+q_{\rm sk})}L^{-(R-1)(1/4+1/50)}\times[\text{7.3/7.1 costs}].
$$
The stem filters, the frontier factors and the shells $H_{j,M}$ (with $|H_{j,M}|\le1$) are multipliers of modulus at most one inside the absolute counting factor of (redvine5). They are deleted there by S Lemma 9.4.

### 4.8 Lemma F, frontier factors, and (finalsbest1′)

**Step 0: the form of the ladder bound that is used.** By erratum E5 (`docs/ERRATA-AND-DEVIATIONS.md` L820–845), (finalsbest1) is proved through the **kernel core**
$$
\mathfrak K(\mathbb L;\mathfrak B)=\Big(\tfrac{\delta}{2L^{d-\gamma}}\Big)^{2m+1}\int_{\mathfrak B}\Big|\sum_{k[\mathbb L]}\Phi\ \prod_{v\in\mathbb L}e^{\pi i[\delta L^{2\gamma}(-\Gamma_v+\Gamma_v^0)+\xi_v]t_v}\Big|\,dt .
$$
Here:

- $\mathfrak B=\prod_{v\in\mathbb L}[\mathfrak L_v,\mathfrak L_v+1]$ is the unit time box, with the ordering dropped;
- $\Phi$ collects the factors $\epsilon_v,\mathcal Z_v,\mathcal K_{(\ell)}$ of $\mathbb L$.

$\mathfrak K$ is bounded by the right side of (redladder2), and it is multiplicative over disjoint ladders. Its proof, made explicit from T1989–1991 via T1627–1660, goes as follows:

- reparametrize by the rung variables $(x_j,y_j)$, with $\Gamma_v=2x_j\cdot y_j$ and $\Gamma_w=-2x_j\cdot y_j+2r\cdot\zeta_j$ (T1989);
- bound each rung quantity $\mathfrak M_j=\int_{I_v\times I_w}|\sum_{x_j,y_j}\cdots|$ in the variable $v=\delta L^{2\gamma}(t_w-t_v)$, using Poisson summation and `lemlayer1` (T958) on $|v|\le L$, and `lemlayer2` (T970) on $|v|\ge L$;
- incoherent rungs ($\mathfrak L_v\neq\mathfrak L_w$) gain through the measure of the time set (T1652, (timeintgap));
- bound the last rung trivially by $L^{2d}$.

The box enters only through three properties:

- **(B1)** $|I_v|=1$;
- **(B2)** $|t_w-t_v|\le\mathrm D+2$, which sets the $C_2$-constant of `lemlayer2` (T976);
- **(B3)** for incoherent rungs, $\mu(v):=|\{t_v\in I_v:\ t_v+v/(\delta L^{2\gamma})\in I_w\}|\le\min\big(1,\ |v|/(\delta L^{2\gamma})+\lambda_{vw}\big)$, with $\lambda_{vw}:=|I_v\cap I_w|$. For the layer box, $\lambda_{vw}=0$.

**Step 1: filters are time translations.** By T1968, $\zeta_{\mathfrak n}\Omega_{\mathfrak n}=-\Gamma_v+\Gamma_v^0$. Since $\vartheta$ is even,
$$
\vartheta(\Omega_{\mathfrak n(v)}/R_v)=\int\widehat\vartheta(\xi)\,e^{2\pi i\xi(-\Gamma_v+\Gamma^0_v)/R_v}\,d\xi .
$$
Moreover
$$
e^{2\pi i\xi(-\Gamma_v+\Gamma_v^0)/R_v}\,e^{\pi i\delta L^{2\gamma}(-\Gamma_v+\Gamma_v^0)t_v}=e^{\pi i\delta L^{2\gamma}(-\Gamma_v+\Gamma_v^0)(t_v+\tau_v)},\qquad \tau_v:=\frac{2\xi}{\delta L^{2\gamma}R_v},
$$
and $e^{\pi i\xi_vt_v}=e^{\pi i\xi_v(t_v+\tau_v)}e^{-\pi i\xi_v\tau_v}$. So, for fixed $(\xi_v)_{v\in\mathcal S}$, the filtered integrand at $t$ is a unimodular constant times the unfiltered integrand at $t+\tau$, where $\tau_v=0$ for $v\notin\mathcal S$. The absolute value sits inside the time integral, so Minkowski's inequality gives
$$
\mathfrak K^{\vartheta}(\mathbb L;\mathfrak B)\le\int\prod_{v\in\mathcal S}|\widehat\vartheta(\xi_v)|\ \mathfrak K(\mathbb L;\mathfrak B+\tau(\xi))\,d\xi .\tag{4.8}
$$
This is the referee's suggested repair. The box is translated, but there is no ordering left to perturb, which answers RR's caution about T1603(iii).

**Step 2: translated boxes.**

*All $|\xi_v|\le L$.* Since $R_v\ge L/2$, we have $|\tau_v|\le 4|\xi_v|/(L\,\delta L^{2\gamma})\le 4(\delta L^{2\gamma})^{-1}\le\tfrac14$ for $L$ large. Then:

- (B1) holds;
- (B2) holds with $\mathrm D+3$, which changes only the $C_2$-constant;
- (B3) holds with $\lambda_{vw}\le|\tau_v|+|\tau_w|\le 4(|\xi_v|+|\xi_w|)(L\,\delta L^{2\gamma})^{-1}$.

On $|v|\le L$, an incoherent rung is therefore bounded by
$$
(\delta L^{2\gamma})^{-1}\,CL^{2d}\int\langle v\rangle^{-d}\big(|v|(\delta L^{2\gamma})^{-1}+\lambda_{vw}\big)dv\le C'\,\delta^{-1}L^{2(d-\gamma)}(\delta L^{2\gamma})^{-1}(1+|\xi_v|+|\xi_w|),
$$
using $d\ge3$. This is the untranslated incoherent gain times $(1+|\xi_v|+|\xi_w|)$. The region $|v|\ge L$ uses only $\mu\le1$ and `lemlayer2`, so it is unchanged. Coherent rungs use only $\mu\le1$.

*Some $|\xi_v|>L$.* Bound the rung containing $v$ trivially by $C L^{2d}$, and use $\int_{|\xi|>L}|\widehat\vartheta|\le C_NL^{-N}$ with $N=4d$. This is admissible since $\vartheta\in C_c^\infty$; its Gevrey decay $e^{-c|\xi|^{1/2}}$ is more than enough. The product $C_NL^{2d-4d}$ is smaller than the incoherent rung bound $\delta^{-1}L^{2(d-\gamma)-\gamma_1}$ for $L$ large.

**Step 3: integration.** Integrating against (4.8), each filter costs at most $10\int(1+|\xi|)|\widehat\vartheta|$, plus the tail $\le L^{-2d}$. This gives $C_\vartheta^{|\mathcal S|}$, uniformly in $R_v\ge L/2$, in the boundary data, and in $\delta$. Note that $\lambda_{vw}$ is of the same order as the gain scale $(\delta L^{2\gamma})^{-1}$. ∎

**Frontier factors on ladder bonds (RR M3).** By S Lemma 3.2, each frontier multiplier is a signed sum of at most $2^{2P}$ products of single-bond factors $\chi(k_\ell/R_j)$, $R_j\ge L$. On a ladder bond such a factor multiplies $\mathcal K_{(\ell)}$, which has unit-ball support and at most $30d$ derivatives bounded by $1$ (T1965, T1983). The product stays in the same class up to $c_\chi$ (O63 §1.2). So the cost is $c_\chi$ per bond, with a base independent of $\delta$.

**(finalsbest1′).** Repeat T2081–2083 with split set $H\cup S_{\rm split}$. Each atom of $S_{\rm split}$ removes itself and its rung partner from the ladders and splits at most one ladder into two. Hence
$$
q'\le q_{\rm sb}+q_{\rm sk}+|S_{\rm split}|,\qquad m'\le m_{\rm sb}+2q_{\rm sk}+2|S_{\rm split}|,\qquad g'\ge g_{\rm sb}-2q_{\rm sk}-2|S_{\rm split}|.
$$

- **Pieces are admissible.** Each piece contains no atom of $H\cup S_{\rm split}$. $\mathcal K^\dagger$ depends only on bonds at hinges (T1970). The protected amplitudes (objects of OPEN 7.3/8.2, pins, faces) depend only on bonds at atoms of $\Pi_{\rm sb}$. So the hypothesis of T2081 holds. Apply the E5-repaired `ladderl1new`, Lemma F and the frontier remark. The gluing over disjoint maximal ladders (E5 steps 3–4) is unchanged, since splitting preserves disjointness.
- **Atoms outside the pieces** are bounded trivially:
  - unit balls and unit intervals; pinned and face atoms carry no time integral;
  - filters, shells, $\epsilon$ and $\mathcal Z$ are bounded by $1$;
  - protected objects are bounded by their OPEN 7.3/8.2 bounds.

Therefore
$$
|\mathcal K_{\mathcal G_{\rm sb}}|\le C_\vartheta^{n_{\rm sb}}c_\chi^{2n_{\rm sb}}(C_1\sqrt\delta)^{n_{\rm sb}-m'}\delta^{m'}L^{-(\gamma_1-\sqrt\eta)g'+20dq'+20dm'}\le\text{(T2076)}\cdot L^{(60d+2)|S_{\rm split}|}\,C^{n_{\rm sb}} .
$$

### 4.9 Interpolation (finalproof1′/2′)

T2220–2225 interpolate (finalsbest1)$^\theta$ against (finalsbest2)$^{1-\theta}$ with $\theta=40\nu$. With the extra factors above, (finalproof1) acquires
$$
L^{\theta(60d+2)|S_{\rm split}|+(1-\theta)2N_E}\,C^{\theta n}\le L^{(60d+2)|S_{\rm split}|+2N_E}\,C_\vartheta^{\,n}.
$$
(finalproof2) then follows as in T2224–2225. Here $q_{\rm sk}$ counts runs, and the $L^{\eta^7q_{\rm sk}}$ of (redvine2′) is absorbed by $L^{-\eta^6q_{\rm sk}/2}$ exactly as there.

*Sharp form.* If moreover $\nu\le 1/(240(60d+2))$, a condition depending only on $d$ and compatible with "ν small depending on $C_1$" (T609), then $\theta(60d+2)|S_{\rm split}|\le|S_{\rm split}|/6\le b$, and the extra factor is $\le L^{b+2N_E}\le L^{5b}$. This proves Theorem 7.5′(9). ∎

---

## 5. Sufficiency for the assembly (Proposition 10.3 / O63 Proposition 10.3′)

**What must be delivered.** O63 Proposition 10.3′ assumes (5.1): the gain-free, profile-uniform bound $\mathcal B_\Theta(C_1)\le E(1+n)^AD_P^{n+1}\delta^{8\nu n}L^{BP}G_2(M_2)$ for the capped and pinned integrands. For a non-regular component, the chain of T that produces such a bound is:

> (redvine) → (redvine2) → (finalsbest1)/(finalsbest2) → (finalproof2) → class count (T2237–2255).

Theorem 7.5′ supplies every combinatorial and counting step of T2040–2225 in the presence of $\Pi$, with the explicit extra factor of (9). The class count with survivors is carried out in §8.

**Clause-by-clause match with OPEN 7.5 as stated in S** (RR-corrected citations):

| S OPEN 7.5 requirement | Theorem 7.5′ | Remark |
|---|---|---|
| reduction with $\le c_db$ additional boundary atoms | $|B|\le4b$, $|S_{\rm split}|\le6b$ | no excision, so no new crossing bonds |
| 1. exact bond count (7.4), defects recorded; connectivity may drop | (1): connected, $2n_{\rm sb}-R$ bonds; (4.6) for Operation 1E | RR (iii): T2113 holds verbatim; T2162 becomes Prop. 4.7(3) |
| 2. disjoint $\mathscr C_1$, hinge set $H$ ($q_{\rm sk}$), exceptional $B$ | (2), plus the collection $\mathscr C_E$ | **variant:** survivors form $\mathscr C_E$ |
| 3. triple bonds; degenerate atoms tame (T2044), boundary values allowed | (2), (3) | fixed values $\{k,k'\}$ |
| 4. uncovered SG objects lie in DV/LG/ZG (T2045, `subsetvc` note) | (4) with "$\mathscr C_1\cup\mathscr C_E$" | **variant** in wording |
| 5. hinge SG pairs (T2046), second sentence | (5), extended to $\mathscr C_E$ | RR (ii) |
| 6. hinge configuration (T2047); objects meeting $B$ handled separately | (6), (6′) | (6′) is the "exceptional-piece" statement |
| counting/analytic extension of T2075–2255 with cost $C^{n+1}_{P,\chi}C_{P,\delta}L^{c_db}$, same gains | (7)–(9) and §8 | $c_d=360d+16$ (crude) or $5$ (sharp) |
| ladder pieces independent of the nonsmooth amplitude (T2083) | (8)/(9): split at $H\cup B\cup\Pi_{\rm sb}$ | RR (iv) |

**Why the variant suffices.** The supplement required clauses 1–6 only so that Stage 2 (T2101–2216) and its rigidity count go through, with exceptional pieces paid at $L^{c_db}$.

- In the variant, the exceptional pieces are paid inside Stage 2 itself. Lemma 5 gives at most $L^{3\gamma_0+5\eta^2}$ per survivor in the count, and the survivors' ladders enter (finalsbest1) like every other ladder.
- No pinned-boundary estimate of an excised piece is needed. So the variant places no demand on OPEN 7.3 beyond what the pins and faces already require.
- Every place where T used `subpro` (T2097, T2104, T2113, T2116, T2140, T2162, T2167, T2187) has been re-derived above.

---

## 6. Loss accounting for Theorem 7.5′

The numbers below use $b\le26P$ (2.1), $b_V\le b$ (Lemma 1), $N_E\le2b$ (2.2), $|B|\le2N_E$, $|\Pi_{\rm sb}|\le2b$ and $|S_{\rm split}|\le6b$.

| Item | Bound | $L$-exponent per $P$ | Base (δ-independent) |
|---|---|---:|---|
| Removal of survivors in the count (Lemma 5, Prop. 4.7–4.8) | $L^{(3\gamma_0+5\eta^2)N_E}\le L^{2N_E}\le L^{4b}$ | $104$ | — |
| Ladder splits at $B\cup\Pi_{\rm sb}$ in (finalsbest1′) | $L^{(60d+2)|S_{\rm split}|}\le L^{(60d+2)6b}$ | $9360d+312$ (crude) | — |
| — the same after interpolation, if $\nu\le1/(240(60d+2))$ | $\le L^{b}$ | $26$ (sharp) | — |
| Stem filters on ladder rungs (Lemma F) | $C_\vartheta^{\#\rm filters}$ | $0$ | $C_\vartheta$ |
| Frontier factors on ladder bonds (§4.8) | $c_\chi^{2n+1}$, $2^{2P}$ terms | $0$ | $c_\chi$ |
| Incoherency lost at splits (≤ 2 per split atom) | $C_2^{12b}$ in the layering count (§8) | $0$ | $C_{P,\delta}$ (n-independent) |
| Lost bad-vine cancellation of marked vines | none needed: the survivors are counted (Lemma 5) | $0$ | — |
| **Total for 7.5′** | $L^{(360d+16)b}$ crude; $L^{5b}$ sharp | **$9360d+416$** crude; $130$ sharp | — |

---

## 7. Budget table for (10.3)/(10.4): every row numbered

**Conventions.** Each entry is the contribution to $B$ in $L^{BP}$, for `flowerest1` with $b\le26P$.

- Rows marked *contract* are OPEN items. The number shown is the **ceiling allotted** to them; (10.4) holds whenever they meet it.
- The supplement's §10 rows and O63 are included.
- Gains appear as $0$ with the gain noted.

| # | Operation | Source | $B$-contribution | Exponential base / constants | Status |
|---:|---|---|---:|---|---|
| 1 | Capping and moment identity | S L2.1–2.2 | $0$ | — | proved (RR PASS) |
| 2 | Low-pass/shell expansion of frontier and stem shells | S L3.2, S §8 | $0$ | $2^{4P}$ | proved |
| 3 | External decay $\langle k-\zeta k'\rangle^{-4\Lambda P}$ and gain $M_1^{-80dP}$ | O63 Thm 6.3′ | $0$ | $(16c_\chi)^n$, $C_{P,\delta}$, $(1+n)^{(8\Lambda+80d)P}$ | closed (6.3′) |
| 4 | Unprotected incoherent objects, frontier-weighted | S L4.1 | $0$ | $C_\chi^{h+1}(1+h)^{32d}$ | proved |
| 5 | Runs (unmarked LF chains) | S L5.3, T1742 | $0$ (the $L^{\eta^7q_{\rm sk}}$ is beaten by $L^{-\eta^6q_{\rm sk}/2}$) | $C_\chi$ | proved |
| 6 | SG-top stem filter | S L9.3 + RR sentence | $0$ | $\|\mathcal F\vartheta\|_1$ per filter | proved |
| 7 | Stem filters on ladder rungs (RR M2) | Lemma F | $0$ | $C_\vartheta$ per filter | proved here |
| 8 | Frontier factors on ladder bonds (RR M3) | §4.8 | $0$ | $c_\chi$ per bond | proved here |
| 9 | Exceptional survivors, counting | Thm 7.5′(7) | $104$ | — | proved here |
| 10 | Ladder splits at $B\cup\Pi_{\rm sb}$ | Thm 7.5′(8) | $9360d+312$ (sharp: $26$) | — | proved here |
| 11 | Incoherency lost at splits and at protected objects (layering) | §8 | $0$ | $C_2^{22b}\subset E_{P,\delta}$ | proved here / contract (G-ret) |
| 12 | Exceptional spectral variables: $\le2$ per pin (S 7.3), $1$ per face; $(C_d\rho L)^{4d}$ each | S L7.1 (RR fix) | $6\cdot4d=24d$, plus $0.01$ (polylog $\rho$) | — | proved (counting part) |
| 13 | Selected-time faces and the $M_2$ gain | inside regular objects: S L9.1 with the reciprocal kept (o82 Thm 18.2); at skeleton and residual selected vertices: o73 Prop 20.1's split | $0$; gain $M_2^{-1/18}$ per occurrence (no ledger number uses the extra $(c\delta L^{2\gamma})^{-1}$) | $8^{2P}$ | proved / contract [Rev. 2, 73-W] |
| 14 | Pinned/face analytic estimates of protected objects, beyond row 12 | OPEN 7.3 | $26\,c_{7.3}\le 26\cdot19{,}000\,d^3=494{,}000\,d^3$ | $C^{(7.3)}_{P,\chi}$ | **contract** |
| 15 | Spectrally truncated regular chains (and gain $M_2^{-1/18}$ per selected occurrence **inside a regular object**) | OPEN 8.2 | $26\,c_{8.2}\le 494{,}000\,d^3$ | $C^{(8.2)}_{P,\chi}$ | **contract** |
| 16 | Integrable spectral coefficient | S L8.1 (RR fix) | $0$ | $C_A^{m+1}$ | proved |
| 17 | T's own Stage 1–2 and rigidity count, per component | T2040–2255 | $0$ (net gain $L^{-\eta^7}$; width gain dropped) | $C_0,C_1$ absorbed by $\delta^{2\nu n}$ | T + errata |
| 18 | Polylog factors from $n\le(\log L)^{C_2}$ | — | $\le0.01$ (included in row 12) | — | — |
| 19 | Bottom first/second blocks | S L9.5 | $80d+\tfrac19$ | — | proved; enters (10.4) separately |
| 20 | Polynomial choices, order sum, constants | S L10.1, Prop. 10.3 | $3$ | $E_{P,\delta}(1+n)^{A_{P,\delta}}$ | proved; enters (10.4) separately |
| 21 | Expansion errors $\mathcal E^{(1)},\mathcal E^{(2)}$ | o102 Theorem R | $0$ (separate right side, $\tfrac14$) | — | closed (o102) [Rev. 1] |

**The numerical $B$.** Sum rows 1–18:
$$
B=104+(9360d+312)+24d+0.01+26(c_{7.3}+c_{8.2})=9384d+416.01+26(c_{7.3}+c_{8.2}).
$$

**Check of (10.4) against $L^{(100d)^3P}$.** With the ceilings $c_{7.3},c_{8.2}\le19{,}000\,d^3$,
$$
B+80d+\tfrac19+3\le 988{,}000\,d^3+9464\,d+419.13\le 10^6d^3 = (100d)^3 .
$$
The last inequality is $9464d+419.13\le12{,}000\,d^3$: at $d=1$ it reads $9883.13\le12{,}000$, and the right side grows faster in $d$. So (10.4) holds for every $d\ge1$, in particular for $d\ge3$.

- With the sharp row 10 ($26$ instead of $9360d+312$), the margin left for 7.3 and 8.2 is larger still.
- 6.3 contributes $0$ (O63 §7).

**Derivative patterns** (frozen allowance $2(100d)^3P$; RR M4). Here $b\le30P$. Rows 9, 10, 12, 14, 15 become $120$, $10800d+360$, $56d$, $30c_{7.3}$, $30c_{8.2}$. The total is $\le1{,}140{,}000\,d^3+10{,}936\,d+483.2\le 2\cdot10^6d^3$.

---

## 8. [SEPARATE ITEM] OPEN 10.3 — aggregate count and budget (conditional)

This section answers wt-orch item (5). It is **not** part of OPEN 7.5. It uses Theorem 7.5′ together with the following explicit contracts for the remaining analytic items.

- **(C7.3)** OPEN 7.3 holds with extra cost $C^{(7.3)\,n+1}_{P,\chi}C_{P,\delta}L^{c_{7.3}b}$, besides row 12, with:
  - $C^{(7.3)}_{P,\chi}$ independent of $\delta$;
  - uniformity in $(t,s,k,k',M_1,M_2,\zeta)$ and over profiles in $\mathcal P(2c_\chi C_1)$;
  - **gain retention (G-ret):** the estimate of each protected object retains its incoherency gain except at most $10$ units per protected incidence. This is RR's 6.3(ii), transferred to the objects that remain protected after 6.3′.
- **(C8.2)** The same for OPEN 8.2 with $c_{8.2}$, together with (8.6), i.e. the factor $M_2^{-1/18}$ per selected occurrence inside a regular object. At skeleton and residual selected vertices the $M_2$ gain comes instead from o73 Prop 20.1's split, giving $M_2^{-1/18}$ per occurrence [Rev. 2, 73-W; §11.6, §12].
- **(E5)** The E5-repaired `ladderl1new` (used in Lemma F).

> **Proposition 10.3-count.** Under (C7.3), (C8.2) and (E5), O63 (5.1) holds for every capped/pinned weighted integrand $\Theta$ of O63 §1.1, all three cutoff versions and $\mathfrak X/\mathfrak Y/\mathfrak W$, with:
> - $G_2(M_2)=M_2^{-P/9}$ in the nonbottom $M_2$ version;
> - a base $D_P$ independent of $\delta$, given in (8.1);
> - $B=9384d+416.01+26(c_{7.3}+c_{8.2})$.
>
> Consequently, if $c_{7.3},c_{8.2}\le19{,}000\,d^3$, then (10.4) holds, and O63 Proposition 10.3′ gives S (1.1).

*Proof.*

**(i) Factorization.** Fix $(t,s,k,k')$. Then $K^{\rm cap}_{\widehat{\mathcal G}}$ factorizes over the components of $\widehat{\mathcal G}$:

- the time domains are independent across trees (T673; RR §2 on Lemma 9.1);
- the decorations are per component;
- the multiplier $W$ and the truncation labels are per original tree, and each original tree lies in one component;
- congruence′ acts inside one component.

So the order-$n$ sum is a sum, over partitions of the $4P$ capped trees into components ($\le(4P)^{4P}$ choices) and over the order splittings ($\le(n+1)^{2P}$), of products of component class sums.

**(ii) Non-regular components.** Theorem 7.5′(9) with (C7.3)/(C8.2) gives, per congruence′ class, (finalproof2) times $L^{(360d+16)b_c}C_\vartheta^{n_c}\cdot[\text{contract costs}]\cdot[\text{row-12 costs}]$.

**(iii) Regular components.** These are the terms (c)/(d) of T2058–2060, with no $\mathcal U$ subtracted in the moment. Use T2231–2235 and the bounds of T1145–1174 (`layerregest`). This gives $\lesssim_2(C_1\delta)^{n_c/2}\le\delta^{8\nu n_c}$, with protected objects (flower–cap pairs, RR's fix to S Lemma 5.1) bounded under (C7.3)/(C8.2).

**(iv) Class count (T2237–2253) for components with survivors and protected objects.** Let $\bar\rho=\rho_{\rm sb}+q_{\rm sk}$, where $\mathbb M_{\rm sb}$ now contains the survivors, and $\bar g=g_{\rm sk}+g_{\rm sb}$.

- *Molecule and garden.* $\mathbb M_{\rm sb}$ has at most $C_0\bar\rho$ non-ladder atoms and at most $C_0\bar\rho$ maximal ladders. Inserting the $q_{\rm sk}$ runs gives $\mathbb M_{\rm sk}$. Propositions `propcplmol` and `propstructure2` then give at most $C_0^n(C_0\bar\rho)!(C_0R)!$ gardens, verbatim as T2239.
- *Protected data.* The special vertices are determined by the garden. The selected vertices give $\le(n+1)^{2P}$ choices, the faces $8^{2P}$, the shell terms $2^{4P}$.
- *Layerings* (T2241–2248):
  - survivors' ladders by `layerlad` and their other atoms at $C_2$ each, as atoms of $\mathbb M_{\rm sb}$;
  - unprotected regular objects by `layerreg2`;
  - protected objects by `layerreg2`, paid by their retained gains except $\le10b$ units (G-ret).

  Adding the $\le12b$ units lost at splits, the number of congruence′ classes is
  $$
  \le C_0^n(C_0\bar\rho)!(C_0R)!\,C_2^{\bar g+\bar\rho}\,C_2^{22b}\,(n+1)^{2P}8^{2P}2^{4P}.
  $$
- *Combination.* Set $\bar g_{\rm ret}=\bar g-22b$. Then
  $$
  L^{-\nu\eta\bar g_{\rm ret}}C_2^{\bar g}=C_2^{22b}(L^{-\nu\eta}C_2)^{\bar g_{\rm ret}}\le C_2^{22b},
  $$
  and $L^{-\nu\eta\bar\rho}C_2^{\bar\rho}(C_0\bar\rho)!\le1$ since $\bar\rho\le n\le(\log L)^{C_2}$ (T2253). **No power of $L$ is lost for the unretained units.** Finally $(C_0C_1\delta^{10\nu})^n\le\delta^{8\nu n}$ once $\delta^{2\nu}C_0C_1\le1$ (T2253–2254).

**(v) Bases.** Every per-object base is independent of $\delta$:

- $16c_\chi$ (O63);
- $C_\vartheta$ (Lemma F);
- $c_\chi$ per bond;
- $\max(1,\|\mathcal F\vartheta\|_1)$ (S L9.3);
- $C^{(7.3)}_{P,\chi}$, $C^{(8.2)}_{P,\chi}$.

Each is raised to a power at most $2n+1$. So their product is at most $D_P^{\,n+1}$ with
$$
D_P:=\big(16c_\chi\,C_\vartheta\,c_\chi\,\max(1,\|\mathcal F\vartheta\|_1)\,C^{(7.3)}_{P,\chi}C^{(8.2)}_{P,\chi}\big)^{2}.\tag{8.1}
$$
All $C_2$-type and polynomial factors ($C_2^{22b}$, $(C_0R)!$ with $R\le2P$, $(4P)^{4P}$, $8^{2P}$, $(n+1)^{O(P)}$) go into $E_{P,\delta}(1+n)^{A_{P,\delta}}$.

**(vi) $L$-powers.** These are rows 9–15 and 18 of §7, i.e. the stated $B$. The $M_2$ gain is attributed in §11.6 [Rev. 1, 75-§8]: inside regular objects, S Lemma 9.1 with the reciprocal kept (o82 Thm 18.2); at skeleton and residual selected vertices, o73 Prop 20.1's split [Rev. 2, 73-W]. There are $2P$ occurrences, each giving at least $M_2^{-1/18}$, so the total is at least $M_2^{-P/9}$ without grouping.

This is (5.1). The numerical check is §7. ∎

**What 10.3 still needs.**

- The contracts (C7.3) and (C8.2). Note that (G-ret) is a requirement on those items: the referee's 6.3(ii) point now applies to the objects protected because of pins and faces.
- An audit item for Lemma F, stated in §10.

Nothing else: the rigidity count itself (T2237–2255) is carried out above for components with survivors.

---

## 9. Dependencies (with lines)

| Source and lines | Content | Use here |
|---|---|---|
| T1295–1325 | molecules, decorations, (decmole1), (molegammav), restricted decorations | §4.4 clause (3); §4.8 Step 1 (T1968) |
| T1304 | `propcplmol` | clause (1); §8 (iv) |
| T1328–1343 | blocks, concatenation, `disjointlem` | Lemma 3; clauses (6), (6′) |
| T1345–1353, T1377 | `block_clcn`, splicing, realization | Def. 2.3; Lemmas 1, 3 |
| T1367–1376 | `cnblock` | Prop. 4.7(3) |
| T1379–1382 | `blockchainprop` | runs are (CL) blocks; Lemma 3(i) |
| T1384–1421 | vines, HV/VC/HVC, `molecpl` | Def. 2.3; Lemma 2 |
| T1429–1454 | twists and their facts (T1452 decoration bijection) | Lemma 2 |
| T1466–1488 | LF twists; T1476 layer-$p$ count; `lftwistprop` | Lemma 2(b) |
| T1501–1532 | `layerlad`, `layervine` (T1519: ≤3 ladders + <20 atoms) | Lemma 5; §8 (iv) |
| T1595–1660; T958–977 | `sumint`, its Step 2, `lemlayer1/2` | Lemma F |
| T1724–1755 | `regred`, `vineest` | §4.3 |
| T1927–1965 | $\mathscr C$, $\mathscr V$, gaps, Stage 1, (redvine), (redvine2) | §2.5, §4.3 |
| T1966–2038 | (redvine3), `ladderl1new`, `ladderl1old` | §4.7, §4.8 |
| T2040–2052 | `subpro` (1)–(6) at T2042–2047, and its proof | Theorem 7.5′(1)–(6) |
| T2073–2116 | (finalsbest1/2), requirements (a)–(f), (finalcount1) | §4.7–4.9 |
| T2118–2218 | cuts, Operations 1–4, `excessprop1`, `finalmol`, `lgmolect`, proof of (finalcount1) | §4.6–4.7 |
| T2220–2256 | interpolation; proof of `layergarden` (T2237–2255 count) | §4.9, §8 |
| T2259–2304 | flower section; T2297–2300 adjustments | §2.2, Lemma 2 |
| T2431–2437 | `subsetvc` | clause (4); Prop. 4.7 |
| T2459–2476 | `countlem`, `atomcountlem` | Lemma 5 |
| D23 1673 | $\mathfrak u_1^j=\mathfrak u_2^{j+1}$, $\mathfrak u_{11}^j=\mathfrak u_{23}^{j+1}$ | Lemma 1 |
| D23 1731–1756 | original `subpro` and proof | clauses (2), (5), (6) |
| D23 1788–1803 | Step-1 deviation for a single vine | Lemma 5 |
| D23 1806–1817 | final molecule properties | Prop. 4.8 |
| S L2.1, 2.2, 3.2, 4.1, 5.3, 7.1, 7.4, 8.1, 9.1–9.5, 10.1, Prop. 10.3 | proved supplement lemmas | throughout |
| RR §3 (L7.1, 9.2, 9.3, 7.4), §4.1 (7.5 i–iv), §4.2 (M1–M4) | referee corrections | §1, Lemma 2, §4.8, §7, §8 |
| O63 Thm 6.3′, (5.1), Prop. 10.3′ | marks removed; profile-uniform target | §2, §5, §8 |
| ERRATA E5 (L820–845) | kernel-core form of (finalsbest1) | Lemma F, (finalsbest1′) |
| ERRATA E9, E11, E16, E17, E19, E20, E23, E27 | T-side repairs, used unchanged | Prop. 4.7–4.8 |

---

## 10. Remaining OPEN sub-items and audit notes

**OPEN 7.5 itself.** No OPEN sub-item. The analytic estimates of the protected regular objects, pins and faces are OPEN 7.3 and 8.2 by design: S's 7.5 says exceptional pieces "with boundary data satisfying OPEN 7.3". The variant here asks less of 7.3 than S's excision plan, since no excised piece needs a pinned-boundary estimate.

**Audit note A (Lemma F).** *[Rev. 1: superseded by the explicit hypothesis (E5′) of §11.5, which o83 Theorem K proves (referee pending).]* Lemma F uses the E5-repaired kernel-core bound only through the box properties (B1)–(B3) of §4.8. These properties are read off T1989–1991 and T1627–1660, but T's proof of `ladderl1new` is itself a sketch (T1989: "We shall only sketch the proof here"). An auditor should confirm that the Lean `ladderL1Gate` proof depends on the box only through (B1)–(B3). If it does not, RR's M2 reverts to an OPEN 8.3 with the route of §4.8.

**Audit note B (T-side errata).** Theorem 7.5′ changes T's Stage 1/2 only by excluding marked vines and adding Operation 1E. Every T-side erratum and its campaign repair (E5, E9, E11, E16, E17, E19, E20, E23, E27) is used unchanged. The extra factors of Theorem 7.5′ multiply T's repaired bounds. In particular, Operation 1E creates further already-cut atoms, which may enter Operation-2 triangles; that situation is the one handled by the E20 repair for $\gamma>1/2$.

**Note C (downstream, RR M4).** For the `fixedpoint` variants (the $\mathcal J^\dagger$ kernel, the $\partial_{t,s}$ pins, the root-pinned $\partial_ta^{\rm tr}$), Theorem 7.5′ applies verbatim with $\Pi$ enlarged by the extra pinned vertices ($b\le30P$). The numbers are in §7.

**Note D (for OPEN 7.3/8.2 owners).** The gain-retention clause (G-ret) of §8 is needed for the δ-independence of $D_P$. It must be part of those items' statements.

---

## 11. Revision 1: fixes from REFEREE-2

**Pin.** `ref/REFEREE-2.md`, sha256 `028e5595…d4e7`, §3.

**Verdicts recorded.**

| Part | Verdict |
|---|---|
| Theorem 7.5′ | PASS AFTER FIX |
| Lemma F | PASS AFTER FIX |
| §7 budget | PASS, conditional on the labelled contracts |
| §8 count | PASS as a conditional |

There is no FAIL. None of the fixes below changes a statement or a number.

**Ruling recorded (wt-orch).** Supplement v2 and the Lean work follow the route of Theorem 7.5′, not ruling R61's excision. The two routes are not mixed.

In-place edits elsewhere in the file are tagged "[Rev. 1]".

### 11.1 Fix 75-W1: an HVC with a single survivor

Let $\mathbb W\in\mathscr W_E$ be an HVC whose image has exactly one survivor $\mathbb S$. Then $\mathbb W'=\mathbb S\cup\{e^*\}$ is an SG **HV** of $\mathbb M_{\rm sb}$, the adjoint of $\mathbb S$. It belongs to $\mathscr C_E$ as an HV. Operation 1E removes it exactly as T removes HV's: cut both joints along the bonds of $\mathbb S$, then delete $\mathbb S$.

- **No new component.** $e^*$ keeps the two remnants connected, so $\Delta F=0$ and (excesseqn2) holds (T2179). The count is Lemma 5's, which uses only the bonds of $\mathbb S$.
- **Triple bonds.** This case contains the only triple bonds that touch survivors: $\mathbb S$ a vine (I) whose joints are joined by $e^*$, i.e. the HV of a vine (I). The removal deletes it (REFEREE-2 §3.1(2)).
- **Two or more survivors.** For $s\ge2$, $\mathbb W'$ is an HVC of survivor vines. These are removed one at a time, and $e^*$ remains. Nothing else changes.

$N_E$, $B$ and all bounds are unchanged.

### 11.2 Fix 75-F1: designated pairs at every shared joint in $B$

Every joint $J\in B$ receives exactly one designated pair under requirement (e) (T2104).

- If $J$ is a joint of a single survivor (an outer joint of $\mathbb W'$), the pair is that survivor's two bonds at $J$.
- If $J$ is shared by two consecutive survivors, **hinge or not**, the pair is the two bonds of the survivor removed first.

$J$ is an SG atom not interior to any object, so requirement (f) fixes one gap label $Q_J$. Both survivors carry the chain's gap $r$, so either pair has difference $\pm r$ and $Q_J$ is consistent. This fills the gap REFEREE-2 found: clause (5) had stated the rule only for hinges.

### 11.3 Fix 75-F2: the label ledger of a re-cut

**Setting.** Let $J$ be shared by consecutive survivors $\mathbb S$ (removed first) and $\mathbb S'$.

**The creation step** (removal of $\mathbb S$, $J$ fresh):

- $J^{\mathbb S}$ is deleted.
- The remnant $J^o$ has degree $2$, with both bonds in $\mathbb S'$. It receives an $\alpha$ label $Q_J$, or a $\beta$ label if that step has $\Delta F=1$.
- Its label factor $L^{(\gamma+3\eta)/2-\kappa\eta}Q_J$ is **paid at creation**, as in T. $\kappa$ is fixed now, with $\iota$ defined through live cuts (E21).

**The re-cut step** (removal of $\mathbb S'$):

- $J^o$ is cut along its two bonds. $J^{\mathbb S'}$ is deleted with $\mathbb S'$.
- The isolated half $J^{oo}$ (degree $0$) is **kept** as a separate component, so $\Delta F=1$. This is E28's literal convention.
- $J^{oo}$ **keeps $J^o$'s label**. No new label is created at $J$. Only the other joint of $\mathbb S'$, if fresh, may become $\beta$.

**Bound for the re-cut step, without refund.**

- $J^o$'s own parameters $(c_{J^o},\beta_{J^o})$ fix $k_{\ell_1}-k_{\ell_2}$ and confine $|k_{\ell_1}|^2-|k_{\ell_2}|^2$ to an interval of length $\delta^{-1}L^{-2\gamma}$.
- So the number of choices of $(k_{\ell_1},k_{\ell_2})$ is $\le L^{d-\gamma+\gamma_0+\eta^3}$, uniformly in the gap: (atomcountbd) with $|r|\ge L^{-1}$, as in T2174.
- With $\Delta\chi=-(m-1)$ as in T2169, the step deviation is $\lesssim L^{\gamma_0+2\eta^3}$.
- This lies within (excesseqn2+) with $\Delta F=1$ and $\Delta V_\beta\in\{0,1\}$, the latter being $\le L^{2\gamma_0-\eta^3+3\eta^2}$ when $\Delta V_\beta=1$.

**Refund, exactly once, at the final molecule.** $J^{oo}$ is an isolated imperfect component with one labelled atom, so $\mathfrak A=1$ (since $\chi=0$). The right side of (finalcount) for it is at least $1$:

- for an $\alpha$ label, $L^{-(\gamma+3\eta)/2+\kappa\eta}Q_J^{-1}\ge L^{(\gamma-5\eta)/2}\ge1$;
- for a $\beta$ label (with $G=0$), $L^{\gamma_0+2\eta^2-\eta^5}\ge1$.

**Consistency with the errata.**

- **E20 / R38:** each label factor is paid once and refunded at most once. $J^{oo}$ has degree $0$, so it can never be a triangle ghost.
- **E21:** $\iota$ uses live cuts only, and $\kappa$ is kept from creation.
- **E28:** the isolated half is kept, with $\Delta F=1$.

**Effect on the totals.** In (together2), the re-cut raises the defect $D$ by $2$ and $p^+_{\rm op}$ by $1$. This is exactly the accounting $F_{\rm im}\le R'+N_E$, $p^+_{\rm op}\le 2R-2+N_E$ already used, so the total extra factor is still $L^{(3\gamma_0+5\eta^2)N_E}\le L^{2N_E}$.

**Interaction with E20 ghosts** (REFEREE-2 §3.1).

- Operation 1E runs before Operation 2.
- The internal-joint remnants are isolated, so they cannot enter a triangle.
- The outer-joint remnants of $\mathbb W'$ are degree-2 ghosts of the same type as T's $\mathscr C_1$-joint remnants. R38's per-ghost repair covers them for $\gamma>1/2$.
- The number of ghosts grows by $\le2N_E$, with no extra power of $L$.

### 11.4 Fix 75-F3: the extra imperfect components when $R=1$

The earlier sentence ("contain no low-degree $\varepsilon$-atom") is withdrawn. A removal with $\Delta F=1$ can split off the component that holds a degree-3 root-type atom of the couple molecule.

**Replacement argument.** Each additional imperfect component created by Operation 1E contains at least one $\alpha/\beta$ remnant: it is either an isolated remnant, or the side of a split that holds a remnant. So $V_\alpha+V_\beta\ge1$. The imperfect branch of T2197 gives two bounds:

- $\mathfrak A\lesssim_1 1$, by the DH23 Prop 9.6 argument as extended in T2197;
- $\mathfrak A\lesssim_1L^{-\eta^2\rho+C_0(V_\alpha+V_\beta+Z)}$, by D23 Lemma 10.2.

Interpolating,
$$
\mathfrak A\lesssim_1L^{-\eta^4\rho+C_0\eta^2(V_\alpha+V_\beta+Z)} .
$$

**Bounding $Z$.** $Z$ counts the $\varepsilon$-atoms not of degree 4. The couple molecule has only two such atoms (T1304), so $Z\le2\le2(V_\alpha+V_\beta)$.

**Absorption.** On the right side of (finalcount):

- each $\alpha$-atom contributes at least $L^{\gamma/4}$ (T2198);
- each $\beta$-atom contributes $L^{\gamma_0+2\eta^2}$.

Since $\eta$ is small depending on $C_0$, we have $3C_0\eta^2\le\tfrac12\min(\gamma/4,\gamma_0)$. Hence
$$
L^{C_0\eta^2(V_\alpha+V_\beta+Z)}\le L^{3C_0\eta^2(V_\alpha+V_\beta)}
$$
is absorbed. So $\mathfrak A$ is at most the right side of (finalcount) with the component's own $V_\beta$ and $G=0$, and no $Z$-term is needed. These components are counted in $F_{\rm im}\le R'+N_E$. The totals are unchanged.

### 11.5 Fix 75-LF: the hypothesis (E5′) of Lemma F

> **(E5′)** The kernel-core bound (redladder2) holds for every product $\mathfrak B'=\prod_{v\in\mathbb L}I_v$ of unit intervals with $I_v\subset[-1,\mathfrak D+1]$, with the incoherent rung factor
> $$\min\{1,\ L^{-(\gamma_1-\sqrt\eta)}+|I_v\cap I_w|\}.$$

**Lemma F is proved relative to (E5′).** In §4.8, Steps 1–3 apply (E5′) to the translated box $\mathfrak B+\tau(\xi)$.

- *For $|\xi|\le L$:* the intervals lie in $[-\tfrac14,\mathfrak D+\tfrac14]$. The overlap satisfies
  $$
  |I_v\cap I_w|\le|\tau_v|+|\tau_w|\le4(|\xi_v|+|\xi_w|)(\delta L^{2\gamma+1})^{-1}\le L^{-(\gamma_1-\sqrt\eta)}(|\xi_v|+|\xi_w|)
  $$
  for $L$ large, since $2\gamma+1>\gamma_1$. So the incoherent factor is at most $L^{-(\gamma_1-\sqrt\eta)}(1+|\xi_v|+|\xi_w|)$.
- *For $|\xi|>L$:* the trivial rung bound and the tail of $\widehat\vartheta$ suffice.

**Why (E5′) is expected.** The box properties (B1)–(B3) of §4.8 explain it. (B3) holds for arbitrary unit intervals: for adjacent layers translated by $\tau_v,\tau_w$, $\mu=\max(0,1-|1+\tau_w-\tau_v-h|)\le|h|+|\tau_v|+|\tau_w|$ (REFEREE-2 §3.2). This is T's own enlarged-interval device, T1681–1689: "replace (timeintgap) with $|t-q|\le 2L^{-\beta}+|t-s|$".

**Status of the hypothesis.**

- (E5′) is **proved by o83 Theorem K** (`o83/RESOLUTION.md` §4.4, sha256 `71946247…d014`), with end-rung factor $L^{4d}$. Its referee (REFEREE-83) is pending.
- Until it passes, Lemma F, and with it the closure of RR's M2, is conditional on (E5′). Audit note A (§10) is superseded.
- o83 also records two T-side gaps in `ladderl1new` (T1989–1991) that afflict the untranslated bound too: G2, the sharp $\mathcal Z_v$ indicators; G3, the factorization of the last rung. Theorem K fills them. They are not introduced by Lemma F.

**Minor.** $R_v\ge1$ suffices. Only the scales $M_2,M_2/2\ge L$, or $L$ in the bottom block, occur.

**Scope.** Lemma F covers ladder atoms only. Stem filters elsewhere are handled as follows:

- at non-ladder atoms, by the trivial bound;
- at hinge tops, by S Lemma 9.3;
- in the count, by S Lemma 9.4;
- inside regular trees, by E39 under OPEN 8.2.

o83 Theorem 8.3 also closes RR's M2. wt-orch should keep one; REFEREE-2 suggests o83's, which carries the proofs of G1–G5.

### 11.6 Fix 75-§8: attribution of the $M_2$ gain

*[Rev. 2, 73-W: wording replaced.]*

- **Inside regular objects:** S Lemma 9.1 with the reciprocal kept (o82 Thm 18.2), under (C8.2) with (8.6). See rows 13 and 15.
- **At skeleton and residual selected vertices:** o73 Prop 20.1's split, giving $M_2^{-1/18}$ per occurrence, with its face estimates under (C7.3). See row 13.

No ledger number uses the extra $(c\delta L^{2\gamma})^{-1}$ of the raw reciprocal. Row 13's contribution to $B$ is $0$, and face atoms pay row 12 separately.

Either way there are $2P$ occurrences, each giving at least $M_2^{-1/18}$. The total is at least $M_2^{-P/9}$, and no grouping of linked pairs is needed. The in-place edits are in (C8.2), in §8(vi), and in rows 13 and 15.

### 11.7 Fix 75-C: citations

- **E31** (TARGET L2297 vs L2045). Theorem 7.5′'s restated clauses (4), (6) and (6′), with $\mathscr C_E$ and $B$, are precisely the structural premise E31 identifies as missing. This is a **different route** from ruling R61, which detaches the protected subtrees as separately capped trees with pendant anchored stubs. As recorded above, the formalization follows Theorem 7.5′.
- **E22** (hinge triple bonds; R37). For hinges of chains with $m_{\mathbb W}=0$, the designated pair is E22's pigeonhole pair. For hinges in $B$, it is the survivor pair of clause (5). The only triple bonds touching survivors are the HV case of §11.1, which Operation 1E removes.
- **E28** (degree-2 cuts). Its isolated-half convention is the one used in §11.3.
- **E35** (time integration and faces).
  - The face bounds remain OPEN 7.3 and are part of (C7.3).
  - The twist-compatibility of the selected vertex, its faces and its frozen resonance under congruence′ is Lemma 2(d). So congruence′ needs no cut-label fibres for special-node vines. REFEREE-2 notes that this bypasses that part of E35's R63/R64 programme.
- **E20, E21.** See §11.3.

### 11.8 Editorial fixes (REFEREE-2 §3.3)

- **"If", not "iff".** (10.4) holds **if** $c_{7.3},c_{8.2}\le19{,}000\,d^3$. The ceilings are sufficient, not necessary.
- **Sharp row 10.** With row 10 $=26$, $B=24d+130.01+26(c_{7.3}+c_{8.2})$. Then (10.4) holds if $c_{7.3}+c_{8.2}\le(10^6d^3-104d-133.13)/26$, for example if both are $\le19{,}200\,d^3$.
- **Row 21** is closed by o102 Theorem R, with zero contribution to $B$ (edited in place).
- **Natural count for the contracts.** The contracts are charged per $|\Pi|\le26P$ protected incidences, which is generous. The natural count for OPEN 7.3 is pins plus selected vertices, $\le4P$, so its real ceiling per natural incidence is about $26/4$ times larger. For example, $c_{7.3}\le123{,}500\,d^3$ per pin or face still fits.

---

## 12. Revision 2: fix from REFEREE-73

**Pin.** `ref/REFEREE-73.md`, sha256 `6b4b64eb…fd2d`, §2.10.

REFEREE-73 passed o73's Theorem 7.3′ and checked it against Rev. 1 of this file (sha256 `ab0c438c…5931`).

### 12.1 Fix 73-W: attribution of the $M_2$ gain

Row 13 and §11.6 used to read "gain $(c\delta L^{2\gamma}M_2)^{-1}$ from S Lemma 9.1". Both now read:

> inside regular objects: S Lemma 9.1 with the reciprocal kept (o82 Thm 18.2); at skeleton and residual selected vertices: o73 Prop 20.1's split, giving $M_2^{-1/18}$ per occurrence.

The same wording replaces the matching sentences in (C8.2) and §8(vi), so that the file is consistent.

**Why this changes no number.** What the ledger consumes is $M_2^{-1/18}$ per occurrence, counting repeated occurrences, on both the crude bound and the counting bound, before interpolation. Row 13 contributes $0$ to $B$, face atoms pay row 12 separately, and no row of §7 uses the extra factor $(c\delta L^{2\gamma})^{-1}$ of the raw reciprocal. So $B$, the check of (10.4), and the conclusion of §8 are all unchanged.

### 12.2 A consistency remark from REFEREE-73 (fix 73-REC, which belongs to o73)

**The issue.** Take a residual face that substitutes $t_v$ by the time of the residual parent $v^{\rm pr}$. When $\mathcal T_{(v)}$ is nontrivial, the face's recipient $v^{\rm pr}$ need not lie in $\Pi_{\rm sb}$. It may be an interior atom of a retained ladder.

**Why (finalsbest1′) and Lemma F are unaffected.** Both use the E5-repaired kernel core (§4.8, Step 0), in which the absolute value sits inside the time integral and the ordering is dropped. The face adds two kinds of factor at the recipient:

- the phase $e^{\pi i\alpha_vt_{v^{\rm pr}}}$, whose frequency $\alpha_v$ depends only on the bonds at $v\in\Pi_{\rm sb}$, which are boundary bonds of the ladder;
- order indicators in $t_{v^{\rm pr}}$.

Neither depends on $k[\mathbb L]$, and each has modulus at most $1$. So both leave $|\sum_{k[\mathbb L]}\cdots|$ unchanged in size. Under the time translation of Lemma F the phase only acquires a unimodular constant.

**Precise form of the hypothesis.** The independence hypothesis of T2081 is used in exactly this form: the protected amplitudes may depend on the internal times of a piece, through factors of modulus at most $1$ that do not depend on the piece's momenta, but not on its internal momenta $k[\mathbb L]$. This sharpens the last sentence of Theorem 7.5′(9). Its conclusion is unchanged.

STATUS: CLOSED WITH VARIANT (Rev. 2: REFEREE-2 fixes 75-W1, F1, F2, F3, C, LF, §8 in §11 and REFEREE-73 fix 73-W in §12; see §3 Theorem 7.5′: marked SG vines left unspliced as the collection 𝒞_E and removed in Operation 1, with no excision and 𝕄_sb connected; this is the route adopted for supplement v2 and Lean; extra cost L^{(360d+16)b}, b ≤ 26P; M₂ gain M₂^{−1/18} per occurrence from o82 Thm 18.2 inside regular objects and from o73 Prop 20.1 at skeleton and residual vertices; Lemma F conditional on (E5′) = o83 Theorem K, referee pending; budget §7: B = 9384d+416.01+26(c_{7.3}+c_{8.2}), and (10.4) holds if c_{7.3}, c_{8.2} ≤ 19,000 d³; the OPEN 10.3 count §8 is conditional on (C7.3) including faces and (G-ret), on (C8.2), and on (E5′))
