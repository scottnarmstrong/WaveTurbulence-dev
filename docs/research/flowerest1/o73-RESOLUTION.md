# OPEN 7.3: partial resolution and the remaining coefficient estimate

The full assertion of OPEN 7.3 is **not closed**. This packet proves a localized, pointwise estimate for regular objects with pinned times and endpoint identifications, retaining the gains of all untouched linked pairs. It also gives the exact numerical cost of the spectral-fiber conversion, conditional on the requested mixed-norm decomposition. Neither result supplies the weighted time-Fourier coefficient decomposition required by OPEN 7.3.

This file was written within the packet's permission envelope: writes only in this packet's directory, read-only elsewhere. No source edits, Lean builds, or mutating git operations were used. References below use the frozen sources in §1. The other packets are not assumed to have proved anything beyond the statements in the supplement.

## 1. Frozen inputs and scope

The SHA-256 hashes checked on 2026-11-07 are:

| Abbreviation | Source | SHA-256 |
|---|---|---|
| S | `/home/scott/wt-scratch/flower-open/SUPPLEMENT-v1.md` | `ddd81fe1238e7c51379a69981b4d10aa68690ced46d0fc1b115200fc0c3774d7` |
| T | `/home/scott/wave-turbulence/paper/source/WKE-Longer_times_Final_arXiv.tex` | `493eef6b7dec448bc5f9f1c3974c0cad7a85eca9bc428f5b35e968aad76727cb` |
| D21 | `/home/scott/wave-turbulence/references/src-2104.11204/Inventiones-Final_Version.tex` | `50d0e236a2df0cfd2b98bace6f0256043ee88fc05079ee44c3524ca9482fe402` |
| D23 | `/home/scott/wave-turbulence/references/src-2301.07063/Revision_Submit.tex` | `c7e47dfabf5a4cca6e3ad0399fc377f2809c12f58e1563640407fe0992335475` |

The target is S440–456, in particular the phrases “with the same derivative orders, time-frequency weights” and “including all modulations subsequently consumed.” The endpoint requirement is S450 and Lemma 9.1, S572–590. A pointwise decoration-sum estimate is therefore strictly short of the requested result.

Use the corrected normalization `δ/(2L^{d−γ})` per branching node. Below an object has order **2m**, not m. Constants denoted C depend only on the already chosen analytic constants; their exponential bases do not depend on δ. The final threshold for L may depend on δ. The parameter choices are C₀, η, C₁, ν, then P before δ, and finally C₂ and L, with the standing smallness conditions on η. No change to these choices is made here.

## 2. Exact target versus what is proved here

OPEN 7.3 asks for a replacement of the ordinary coefficient decomposition with at most 2b exceptional spectral coordinates, explicit extracted reciprocal factors kept outside the coefficient, and bounds

\[
\sup_{\alpha_E}\int w(\lambda)
 |\partial_{\alpha_J}^{\rho}C(\lambda,\alpha_E,\alpha_J)|
 \,d\lambda\,d\alpha_J
\]

at every norm and derivative order used in the original reduction. It also asks for an exact account of boundary phases and their consumption by adjacent integrals, preservation of the unmarked gains, and a total additional cost of the prescribed exponential form times an explicit `L^{c_d b}`. The analogous assertion is required for selected-time faces.

The propositions below prove only:

1. the top-layer chain geometry of actual flower marks before excision;
2. a scalar localized estimate for the actual regular-object decoration sum after pins/faces;
3. a one-linked-pair test case for the terminal-pin Fourier norm;
4. the conversion cost once the full mixed-norm premise is available.

The missing extension is specified at the end. In particular these propositions are not claimed to be a sufficient variant for Proposition 10.3.

## 3. A geometric reduction for actual flower marks

**Proposition 3.1 (before any new excision).** In a capped flower garden of S Lemma 2.1, let an embedded regular object contain a node of an original flower stem as one of its branching vertices. If it is an embedded couple, it consists of a subtree of that original tree paired with its trivial cap. If it is an embedded paired tree, its root and its lone port lie on the original stem. In either case its root-to-lone-port regular chain is entirely in layer p. Every linked partner of a stem branching vertex of this object is another vertex of this chain and is in layer p. If the flower parent is a branching vertex of the object, that parent is the terminal branching vertex of the chain.

**Proof.** Use the definition of embedded objects at T845–846. An embedded couple containing a stem branching node contains the subtree below that node, hence the flower. Complete internal pairing forces it to contain the flower's paired leaf, namely its cap. The cap is a trivial original tree and has no ancestor inside another tree. Thus one of the couple's two trees is exactly the cap, and the other is a subtree of the original flower tree.

For an embedded paired tree, write u for its root and h for the root of the subtree replaced by the lone port. The root u is an ancestor of the stem node in question, hence lies on the original stem. If h were off the stem, the flower would remain among the leaves that must be internally paired. Its cap lies outside the original tree, a contradiction. Thus h is on the stem. T857 describes the unique regular chain from the root to the lone port; inserting the side couples leaves this path unchanged. T877 links each chain node to another chain node. All these nodes are on the original stem and therefore have layer p by T2261. For the couple with a trivial cap, apply the same argument to the associated regular paired tree, using T828.

If the flower parent belongs to this chain as a branching node, its lone port is a strict stem descendant of the flower parent. The only such vertex is the flower itself. Consequently the parent is the last chain node. ∎

This applies even when the whole object is incoherent: its incoherent links are then in side couples. It narrows the initial regular-object problem compared with a statement for arbitrary marked layered chains. It does **not** describe the residual molecule, or prove that every later boundary reduction preserves this form. It also does not supply an estimate for a chain fed by incoherent side objects. In particular, the latter supply the X^η norm at T953–955, whereas D23 965–967 uses stronger coefficient weights; one cannot silently identify these inputs.

## 4. A pointwise pinned/face estimate with numerical loss

Here is a precise new estimate at the level of the localized sum in T1014–1024. It avoids taking a trace of a previously integrated kernel.

Let V be the 2m branching vertices of a regular object, with links `{v_j,w_j}`, `1≤j≤m`. For each link introduce its independent lattice variables x_j,y_j and fixed unit-ball localization functions as in T1002–1017. Set

\[
\alpha_j=2\zeta_{v_j}\delta L^{2\gamma}x_j\cdot y_j,
\qquad
e^{\pi i\alpha_j(t_{v_j}-t_{w_j})}
\]

for its phase. The exclusion factor ε_j has modulus at most one and depends only on this pair of lattice variables, as in T1023–1025.

Allow a time-independent spatial amplitude A, represented by a finite Fourier measure of total variation at most K, in all the link variables. Its affine arguments and measure can depend on fixed external data. The bound K is required uniformly in those data. This includes the localized input amplitude when the Fourier-measure hypothesis is verified, but does not assert that all resonance filters in OPEN 8.2 have that property. To use the result with the required order dependence, K must itself have a δ-independent exponential base, for example `K≤C_{P,χ}^{m+1}C_{P,δ}`. The proposition does not improve an inadmissible dependence already present in K.

Delete a set R of time integrations by pinning b distinct times and making a fixed choice of faces for a selected set of a other times. Each eliminated time is replaced by a fixed time or a remaining time; all remaining time variables are still integrated with ordinary Lebesgue measure over a subset D_F of their original unit layer boxes. The substitutions and D_F are independent of the lattice variables. The faces of S Lemma 9.1 have exactly this form. Let

\[
E=\{j:\{v_j,w_j\}\cap R\ne\varnothing\},\quad r=|E|\le b+a,
\qquad
g_J=\#\{j\notin E:\mathcal L_{v_j}\ne\mathcal L_{w_j}\}.
\]

An additional multiplier H_E depending only on the lattice variables of the links in E is permitted, with `|H_E|≤H`. It can include the reciprocals and selected annular restrictions of Lemma 9.1 when the selected vertices belong to this regular object. No arbitrary bounded multiplier in the other link variables is permitted.

Denote the resulting localized decoration sum and face integral, with the full branching normalization `(δ/(2L^{d−γ}))^{2m}`, by I_F.

**Proposition 4.1.** Uniformly in all spatial centers, external times, layers in the source's range, and spatial Fourier modulations, for L sufficiently large after δ,

\[
|I_F|\le KH(C\delta)^m\delta^r L^{2\gamma r}
 L^{-(\gamma_1-\sqrt\eta)g_J}.
\tag{4.1}
\]

If g is the original total incoherency index, this implies

\[
|I_F|\le KH(C\delta)^m L^{3r}
 L^{-(\gamma_1-\sqrt\eta)g}.
\tag{4.2}
\]

When all eliminated vertices are original stem vertices in an object of Proposition 3.1, `g_J=g`, and the factor `L^{3r}` in (4.2) improves to `L^{2r}`. There is no cost proportional to the object's depth or order in these L powers.

**Proof.** Expand A using its finite measure. It suffices to fix one spatial modulation and multiply the final uniform bound by K. All localized lattice sums are finite, so the interchanges with the measure and the time integral are justified by its finite total variation.

For j outside E, neither of its times has been eliminated. Its sum is exactly S_j from T1023–1024 with two unchanged, independent time coordinates. T1029 and T1034–1043 give

\[
\|S_j\|_\infty\le C L^{2d},\qquad
\int_{\mathcal B_j}|S_j(u,v)|\,du\,dv
\le C\delta^{-1}L^{2(d-\gamma)}
\begin{cases}
1,&\mathcal L_{v_j}=\mathcal L_{w_j},\\
C_2L^{-(\gamma_1-\eta)},&\mathcal L_{v_j}\ne\mathcal L_{w_j}.
\end{cases}
\tag{4.3}
\]

Here C₂ is uniform over the allowed layers, centers and modulations and is independent of m. The same-layer constant can be made δ-independent by choosing L sufficiently large, as in the source's product bound T1043. Choose L also so that `C₂≤L^{√η−η}`. This is legitimate since η is fixed with `0<η<1`. Thus the unequal-layer line of (4.3) is bounded by `Cδ^{-1}L^{2(d−γ)}L^{−(γ₁−√η)}`. Crucially the constant C₂ has been absorbed separately into an existing gain for each unequal-layer link, not left as an uncontrolled exponential in m.

For the links in E, keep their sums together if H_E couples them. There are at most `(CL)^{2dr}` lattice tuples. Every phase, including every phase transferred to an endpoint by a substitution, has modulus one. Their joint sum is therefore at most `H C^r L^{2dr}` in absolute value. This estimate is pointwise in every remaining time, so it also removes all time dependence of that exceptional sum from the majorant.

After this step the integrand is bounded by

\[
H C^rL^{2dr}\prod_{j\notin E}|S_j(t_{v_j},t_{w_j})|.
\]

Enlarge D_F to the product of all remaining unit layer intervals. The integrations associated with each untouched pair now separate and are bounded by (4.3); every remaining coordinate belonging to an exceptional pair has interval length at most one. No endpoint indicator is estimated in a Fourier norm in this argument; it is removed only from an already nonnegative integral. We obtain

\[
|I_F|\le KH
 \left(\frac{\delta}{2L^{d-\gamma}}\right)^{2m}
 C^m L^{2dr}
 \left(\delta^{-1}L^{2(d-\gamma)}\right)^{m-r}
 L^{-(\gamma_1-\sqrt\eta)g_J}.
\]

The remaining powers are exactly `δ^{m+r}L^{2γr}`. This proves (4.1). Since `g−g_J≤r`, `γ₁≤1` by T613, and `2γ<2`,

\[
L^{2\gamma r}L^{(\gamma_1-\sqrt\eta)(g-g_J)}\le L^{3r}.
\]

Dropping `δ^r≤1` gives (4.2). Proposition 3.1 gives `g−g_J=0` for the stated stem case. ∎

**Selected-time reciprocals.** If all a selected vertices assigned to this object satisfy `|Ω_v|≥cM₂`, their reciprocal product is an admissible H_E with

\[
H=(\pi c\delta)^{-a}L^{-2\gamma a}M_2^{-a}.
\tag{4.4}
\]

Selections on both vertices of the same link are counted twice in a and once in r. Thus this local scalar estimate retains both reciprocal factors. At most `8^a` faces occur. This statement does not discard any remaining upper resonance cutoff: such a cutoff must either be contained in the admitted amplitude A with its norm K accounted for, or the proposition is inapplicable. This limitation is exactly why (4.4) does not solve OPEN 8.2.

**Cap constraint at the scalar level.** A fixed lattice equality can be included here without a center-dependent Fourier-measure cost. Choose a smooth function ψ supported in `|z|<1`, with ψ(0)=1. On `k_f,k'∈L^{-1}Z^d`, the factor `ψ(L(k_f−k'))` equals `1_{k_f=k'}`. Since k_f is affine in the link variables, Fourier inversion and pushforward give total variation at most `||Fψ||₁`, uniformly in L and k'. This observation is only about total variation, not output-frequency moments or output derivatives; the latter can cost powers of L. It is not an assertion that a constant capped input has an ordinary Schwartz norm.

## 5. A terminal-pin Fourier calculation, and its boundary limit

**Proposition 5.1 (one link).** For `q<s<t<q+1`, consider the linked two-time chain with phases `+α` and `−α`, pinned at its last time. Its value is

\[
K_\alpha(t,s)=e^{-\pi i\alpha s}\int_s^t e^{\pi i\alpha u}\,du
=\begin{cases}
\dfrac{e^{\pi i\alpha(t-s)}-1}{\pi i\alpha},&\alpha\ne0,\\
t-s,&\alpha=0.
\end{cases}
\tag{5.1}
\]

For every `0≤θ≤1`, it has an extension for which

\[
\sup_\alpha\int\max(\langle\lambda_1\rangle,\langle\lambda_2\rangle)^\theta
 |\widehat K_{\alpha,\mathrm{ext}}(\lambda_1,\lambda_2)|\,d\lambda_1d\lambda_2
\le C_\theta,
\tag{5.2}
\]

uniformly in q. This is the mixed norm with the single linked spectral coordinate exceptional and no integrable spectral coordinate.

**Proof.** Fix a smooth compactly supported Φ(t,s) equal to one on `[0,1]^2`. Extend (5.1) by multiplying its globally smooth formula by Φ(t−q,s−q). For `|α|≥1`, its transform is `1/(πiα)` times the difference of two translates of the Schwartz transform of Φ, with centers `(α/2,−α/2)` and zero, up to unimodular translation phases. Its weighted L¹ norm is at most `Cθ(1+|α|^θ)/|α|≤2Cθ`. For `|α|≤1`, use

\[
K_\alpha(t,s)=(t-s)\int_0^1 e^{\pi i u\alpha(t-s)}\,du.
\]

All translations now lie in a fixed compact frequency set, giving a uniform weighted L¹ bound for the transform of `(t−s)Φ(t−q,s−q)`. Translation of both t and s by q changes the Fourier transform only by a phase. The extension agrees with the original expression only on the open triangle, as required by T588–591; no discontinuous zero extension across its boundary has been used. ∎

The full terminal odd-chain identity is S Lemma 7.2. D21 2688–2690 explicitly uses the remaining class-J operator for its linked partner. Proposition 5.1 verifies a basic case directly; it is not a proof of the arbitrary-length recursion or its layered side-input extension.

A single endpoint of the numerator in (5.1) illustrates why boundary phases need their own bookkeeping. For nonzero Φ, the uncentered weighted Fourier norm of

\[
\Phi(t,s)e^{\pi i A(t-s)}
\]

grows like `|A|^θ` for `θ>0`. To see the lower bound, choose a fixed bounded region with positive integral of `|Φ̂|`; on its translate by `(A/2,−A/2)`, the weight is at least `c|A|^θ` for large A. Its norm centered at that translated frequency is constant. Thus recentering is an exact local operation, but the corresponding phase still has to be passed into the adjacent integral.

For example, with `J_A f(t)=∫₀ᵗe^{πiAu}f(u)du`, one has `J_A1=(e^{πiAt}−1)/(πiA)` whereas `J_A(e^{−πiA·})(t)=t`. Ignoring an incoming modulation would incorrectly retain an `|A|^{-1}` gain. This is a counterexample to that shortcut, **not** to OPEN 7.3, which explicitly requires the modulation to be consumed correctly.

## 6. Conditional spectral-fiber conversion: explicit cost

**Proposition 6.1.** Suppose the coefficient estimate (7.3) has already been established with e exceptional coordinates and right-hand side B, and each exceptional coordinate has at most `(C_dL)^{4d}` available intervals of length at most c. These sets are fixed for the given external data, independently of λ and α_J. With the same derivatives and Fourier weights, restricting these coordinates to their available intervals gives the full integrated bound

\[
\int_{\mathrm{allowed}}\int w(\lambda)
 |\partial_{\alpha_J}^\rho C|\,d\lambda\,d\alpha_J\,d\alpha_E
\le c^e C_d^{4de}L^{4de}B.
\tag{6.1}
\]

In particular `e≤2b` costs at most a fixed base to the power b times `L^{8db}`.

**Proof.** Each exceptional coordinate ranges over a set of measure at most `c(C_dL)^{4d}`. Integrate first in the other variables and use the stipulated supremum. Tonelli and the product of these measure bounds prove (6.1). No bound on the location of any interval is used. This is S Lemma 7.1 applied also to the nonnegative λ-integrand. ∎

This does not authorize taking exceptional-coordinate derivatives or converting the result to the source's sum of local suprema without further estimates. In particular T1998 is a sum over σ of suprema on unit boxes, and T2004–2007 uses derivatives to reach an integral. Derivatives only in α_J in (7.3) do not by themselves supply local supremum estimates in the exceptional directions. A proof can instead count exceptional boxes and use a genuinely uniform remaining-variable box estimate, or prove the requisite exceptional-direction regularity. This is a consumer requirement, not an additional conclusion of (6.1).

## 7. Why these estimates do not close the packet

The following is a list of remaining proof obligations, not a claim that the assertion is false.

**7.1. A coefficient representation for the marked regular object.** Proposition 4.1 performs the lattice sums before taking the time absolute value. It proves no integrability or differentiability of a coefficient in its spectral variables. In contrast D23 960–967 keeps the extracted factors `χ∞(α_j)/α_j` outside C and imposes the stated norms on C. Reconstructing that representation from a pointwise estimate is unjustified. In particular `sup_k||·||_{X^η}` is not the `X^{η,0,0}` norm with `sup_k` inside the λ-integral (T581–582).

The geometric result in §3 reduces the initial flower-pin problem to a top-layer chain with layered side inputs. It does not establish that a chain with those inputs satisfies the D21/D23 coefficient estimates. The source's proof for an incoherent object handles its time-Fourier norm separately after obtaining its scalar integral bound: see T1046–1057, and especially the regular-tree discussion at T1060–1092. At T1084 it expands at most two designated linked sums, and at T1086–1089 it controls specific boundary derivatives. Pins and selected faces alter those designated integrals and boundary functions. That altered argument is the first analytic step still needed even for the restricted flower geometry.

**7.2. Closure of the class calculus with the actual layer and face operations.** D21 955–963 defines the class-J/R coefficients with precise weighted norms. D21 966–1094 proves closure under composition and linked-pair enclosure for the Volterra operators displayed there. In particular D21 1084–1086 uses concatenation of legal partitions and enclosure by a linked pair. An independent layer restriction at an internal time or a face identifying it with a parent/child time is not one of the stated operations. A raw layer indicator cannot just be treated as an L¹-Fourier multiplier: an interval indicator is discontinuous, whereas the inverse transform of a finite measure is continuous. Integration can repair that problem, but must be included in the recursion.

This does not contradict the one-layer terminal-pin argument at D21 2689–2690. It says exactly what extra closure statement must be proved when that argument is used with altered boundary data. For actual initial flower objects, §3 removes the need to handle a cross-layer link containing the pin itself. Any broader claim about split marked links produced later still needs either a geometric exclusion or an analytic estimate.

**7.3. Downstream consumption and residual coefficients.** Even a locally recentered bound has to keep its modulation attached to the next time integral. The example in §5 shows why a uniform weighted norm cannot simply be quoted after that attachment. The residual-molecule estimate T1994–2013 has a different norm, and its proof must be repeated with the missing integrations and endpoint phases. D21 2692 is the single-layer residual-denominator prototype; it is not the layered result with the specific T1998 norm.

**7.4. Spectral filters and family cancellation.** The proof of §4 permits bounded multipliers only in exceptional link variables, or amplitudes with a proved finite Fourier-measure bound. It neither estimates the truncated reciprocal factors (8.7) nor proves that marked estimates can be inserted into LF families while retaining bad-vine gains. These are the separately stated OPEN 8.2 and OPEN 6.3/7.5 obligations. No result from packet o82 is assumed here.

## 8. Loss ledger and the proposed continuation

| Operation | Proven or conditional loss | Scope |
|---|---:|---|
| Geometry of §3 | `L^0` | Initial embedded regular objects only |
| Scalar pin/face estimate, §4 | `L^{3(b+a)}` | Full original incoherency gain retained after paying this loss |
| Same estimate for original stem marks | `L^{2(b+a)}` | All exceptional links are same-layer |
| Face count | `8^a` | S Lemma 9.1; constant for `a≤2P` |
| Selected reciprocal product | `(πcδ)^{−a}L^{−2γa}M₂^{−a}` | Only under the §4 amplitude assumptions |
| One-link Fourier calculation | `L^0` | §5, exceptional linked coordinate fixed |
| Spectral conversion | `L^{8db}` times a fixed base to power b | Conditional on (7.3) and at most 2b exceptions |
| Derivatives, local suprema, consumed modulations | **Not established** | Must be proved, not assigned zero cost |
| Marked-family, ladder and counting losses | **Not established here** | OPEN 6.3/7.5 and aggregate (10.3) |

For the full moment there are `b≤2P` pins and `a≤2P` selected vertices. The general scalar estimate therefore costs at most `L^{12P}` (or `L^{8P}` in the stem situation). If a future coefficient theorem counts all `b+a≤4P` modified integrations and uses at most two exceptional coordinates per modification, the conversion alone costs at most `L^{32dP}`. The pin-only conversion costs `L^{16dP}`. These figures must not be mistaken for bounds on the currently unproved coefficient theorem.

For orientation only, even charging both the general scalar cost and that proposed conversion, plus the supplement's bottom-block costs and three-unit margin, gives

\[
12+32d+80d+\tfrac19+3=112d+15+\tfrac19<(100d)^3
\quad(d\ge1).
\]

Thus these particular operations do not exhaust the budget. The inequality **does not verify** (10.4), because the remaining rows have no established numerical losses. In the doubled derivative-pattern allowance these same known exponents double, but no derivative theorem is inferred from that arithmetic.

The smallest useful next task is a **restricted marked regular-object theorem** for the geometry of §3: a layer-p root-to-port chain, arbitrary ordinary layered side objects, a terminal pin, and the explicitly enumerated parent/child/floor/top faces. It should prove the source time-Fourier and coefficient estimates with boundary modulations carried as part of the representation. A proof can combine the original T1046–1092 argument for incoherent side contributions with the D21 1084–1098 recursion for coherent contributions, but must check their different norms at the interface. Then separately extend T1998 to the residual pieces and verify the derivative/local-supremum consumer described in §6. The sum of the resulting numerical losses, not just the conversion loss, must enter the Section 10 table.

This is a route and a precisely restricted remaining theorem, not a proved replacement for OPEN 7.3. No sufficient variant of Proposition 10.3 has been established by this packet.

## 9. Verification and provenance

The new proofs are §§3–6. Their inputs are: the frozen supplement's Lemmas 2.1, 3.1, 7.1, 7.2 and 9.1; T826–879 for embedded objects, the chain structure and linkage; T981–1043 for the localized factorization and pairwise estimates; T613 for `γ₁≤1`; and T588–591 for the extension convention. Source comparisons use D21 955–1098 and 2684–2694, D23 960–974, and T1994–2013. No new discrete spectral approximation is imported.

The review checked the `2m` normalization explicitly, repeated selection on one link, faces landing on already pinned times, exceptional times in different layers, arbitrary spatial centers, the placement of output suprema, the distinction between integrated and local-supremum spectral norms, and the order in which C₂ is absorbed. The nonnegative domain enlargement occurs only after the untouched lattice sums have been formed. The remaining upper filters have not been discarded.

This is a source-level partial proof/completion report, with a bounded self-review; it is not an independent closure audit. The missing target statements remain labeled OPEN rather than promoted to proved claims. Frozen hashes and line-numbered source reads were used; no Lean implementation was inspected or built, no source file was changed, and no other packet's result was used.


## 10. INTERFACE FOR o82 — continuation contract (not yet proved)

This section responds to the addendum in `CONTINUE.md`. It is a proposed producer interface, **not an established theorem**. Packet o82 owns insertion of upper filters/truncated reciprocals and the many-variable discrete estimate. This packet owns the unfiltered marked coefficient, the boundary-phase record, and its consumption. The earlier OPEN status remains in force during this continuation.

For a regular object with m linked coordinates, let b be the number of pins and a the number of selected integrations assigned to it. Retain each of the at most `8^a` raw faces with its sign and maximizing-child inequalities. On the selected annuli factor out

\[
P_F(\alpha)=\prod_{v\text{ selected}}(i\pi\epsilon_v\alpha_{j(v)})^{-1}.
\tag{10.1}
\]

The target representation for the remaining face coefficient is a finite sum (or a finite-measure superposition, with its total variation charged) of terms

\[
 e^{\pi i\,B_F(\alpha_E)\cdot\tau}
 \prod_{j\in Z}\frac{\chi_\infty(\alpha_j)}{\pi i\epsilon_j\alpha_j}
 \int C_F(\lambda,\alpha_E,\alpha_J)e^{\pi i\lambda\cdot\tau}\,d\lambda.
\tag{10.2}
\]

Here E, Z and J partition the linked coordinates, `|E|≤2(b+a)`, all selected coordinates belong to E, and τ lists surviving boundary times. Repeated selected occurrences of one linked coordinate remain repeated factors in (10.1). The linear phase B_F is recorded explicitly and is not assigned an uncentered weighted Fourier norm. An internal boundary time is not discarded: substitution into the neighboring integral adds its exact component of B_F to that vertex's phase. In particular the required bounds concern the expression after that operation, or an explicitly retained signed collection, not an isolated recentered coefficient alone.

The needed coefficient estimates are the mixed versions of D23 965–967 (and the particular weaker norm used for an incoherent piece):

\[
 \sup_{\alpha_E}\int w_1(\lambda)|\partial_{\alpha_J}^{\rho}C_F|
 \,d\lambda d\alpha_J\le \mathcal A_F(2|\rho|)!,
\quad
 \sup_{\alpha_E}\int w_0(\lambda)\max_{j\in J}\langle\alpha_j\rangle^{1-\eta/2}
 |C_F|\,d\lambda d\alpha_J\le\mathcal A_F.
\tag{10.3}
\]

An empty maximum is taken as 1. The weights have the source exponents, in the Fourier convention used for (10.2); changing between `πiλt` and `2πiλt` changes constants only. The total bound over the decomposition must have a δ-independent exponential base in the order. Spectral coordinates in the reciprocal factors are the **original** linked coordinates, not unrecorded translates by an exceptional frequency. If the construction instead produces translated poles or only weak side-input norms, that is an interface change requiring a proof, not something o82 should assume away.

The numerical fiber cost, if (10.2)–(10.3) are constructed, is `L^{8d(b+a)}` by §6. Other local costs are still being investigated; no budget for them is being asserted here. The residual local-supremum coefficient of T1998 is a separate required consumer and is not implied by this displayed regular-object interface.


## 11. Continuation scope after Addendum 2

The continuation now uses common real profiles G_q with

\[
\max_{q\le p}\|G_q\|_{S^{40d,40d}}\le C_1.
\tag{11.1}
\]

There are no selected-frontier or modified-leaf marks from the supplement's old Section 6. This follows the explicit direction in Addendum 2 and o63's Theorem 6.3′/Proposition 10.3′. The o63 file read during the continuation had SHA-256 `65315d5ad0ddea4e9c610c85c2be78f8aafd7c0cf4861e69dee52c8f86e4bba4`; it is a separately evolving packet, not part of the frozen S manifest. The remaining marks are pins/caps, selected M₂ vertices and special-node exceptional pieces. The old discussion of Section 6 marks above is historical and is not an assumption of the following results.

The o82 continuation's §9 supplies its requested interface: original linked coordinates, explicit reciprocals, exceptional spatial tuples fixed before the discrete estimate, and a **consumed** time-weight estimate. It allows a loss of `⟨α_selected⟩^{1/4}` per selected occurrence, but no uncontrolled resonance loss for an unselected pin. For a protected piece removed from cancellation it does not require the strong spectral moment needed for an asymptotic formula. These qualifications supersede any stronger provisional demand in §10.

## 12. A uniform one-time operator that consumes the pin modulation

For `0≤θ≤1`, write A^θ for the weighted Fourier L¹ norm with weight `max_i⟨λ_i⟩^θ`, allowing finite Fourier measures as well as densities. On bounded time domains use extensions. A fixed smooth cutoff turns the measure representations below into densities with a fixed norm cost. Fourier exponents in this section are `πiλt`.

**Lemma 12.1.** For A real and a three-time function H, define on `0<s<t<1`

\[
(\mathcal T_AH)(t,s)=\int_s^t e^{\pi iA(u-s)}H(t,u,s)\,du.
\tag{12.1}
\]

Then

\[
\|\mathcal T_AH\|_{A^\theta(0<s<t<1)}
\le C_\theta\|H\|_{A^\theta(\mathbb R^3)},
\tag{12.2}
\]

uniformly in A. The same holds after translating the unit layer. This is a bound for the **consumed** modulation, without a factor `⟨A⟩^θ` and without replacing it by a shifted norm.

**Proof.** Fourier-expand H. For a Fourier atom `e^{πi(ξt+λu+νs)}`, the output is exactly

\[
e^{\pi i[\xi t+(\lambda+\nu)s]}h_{A+\lambda}(t-s),
\quad h_z(v)=\frac{e^{\pi izv}-1}{\pi iz},\quad h_0(v)=v.
\tag{12.3}
\]

Choose one fixed smooth cutoff in (t,s), equal to one on the unit square. Proposition 5.1 gives a uniform A^θ bound for its product with h_z(t−s), for every z. Translating its Fourier transform by `(ξ,λ+ν)` multiplies that bound by at most `Cθ max(⟨ξ⟩,⟨λ⟩,⟨ν⟩)^θ`. Integrate this estimate against the Fourier measure of H. Its weighted total variation is precisely the right-hand side of (12.2). This defines an extension agreeing on the open triangle. Under translation of t,u,s by the layer index the phase A(u−s) is unchanged. ∎

The norm order here is fixed A followed by the Fourier integral. A supremum over another output on which A varies cannot be moved inside that integral for free. The finite-output construction in Proposition 13.2 below addresses this issue for localized lattice output data.

**Lemma 12.2 (tensor coefficient version).** Suppose four kernels H_i, each depending on two of (t,u,s), have coefficient decompositions with disjoint integrable spectral sets J_i and disjoint extracted sets Z_i. Suppose their coefficients satisfy weighted L¹ estimates with exponent θ and spectral derivatives bounded by `B_i C_i^{|ρ_i|}(2|ρ_i|)!`. Let their product be H and apply (12.1), with A an exceptional coordinate distinct from all those sets. Then the output has a decomposition with extracted set `Z=⋃Z_i`, integrable set `J=⋃J_i`, and the single new exception A, satisfying

\[
\sup_A\int w_\theta(\lambda_{\rm out})
 |\partial_{\alpha_J}^\rho C_{\rm out}|\,d\lambda_{\rm out}d\alpha_J
\le C_\theta\Bigl(\prod_iB_i\Bigr)
 C^{|\rho|}(2|\rho|)!.
\tag{12.4}
\]

Any spectral moment expressed as the maximum over J is also preserved if it is supplied by each input at the relevant time weight, with a further factor at most four. The number of output terms is at most the product of the numbers of input terms.

**Proof.** For each choice of extracted sets leave their reciprocal factors outside the u integral. The remaining coefficient is the integral of the product of the four input coefficients against the Fourier kernel of (12.3). Since the input spectral sets are disjoint, a prescribed multi-index splits uniquely into the four multi-indices ρ_i; the Fourier kernel of (12.3) has no dependence on α_J. Apply (12.2), Tonelli and the input estimates. Use `∏(2|ρ_i|)!≤(2|ρ|)!`. For a maximum spectral moment, bound the maximum over the union by the sum of the four individual maxima and apply the corresponding weighted input estimate in each term. The construction does not translate any spectral coordinate or extracted pole. ∎

Lemma 12.2 is a proved closure rule, not an assertion that arbitrary layered side objects already have every raw spectral coefficient estimate in its hypotheses. For spatially integrated ordinary kernels, their time-Fourier norms suffice for Lemma 12.1, as follows.

## 13. Terminal pins with arbitrary ordinary layered side objects

**Proposition 13.1 (exact cut at the linked partner).** Consider the regular tree in Proposition 3.1, with terminal node v_{2h} pinned at s. Suppose its partner is v_a and write A for the signed linked frequency, so the two phases are `+A t_{v_a}` and `−A s`. Then its chain splits into two complete legal chains: the prefix `1,…,a−1` and the interior `a+1,…,2h−1`. With the two ordinary side couples belonging to the link `{a,2h}`, the exact time expression is

\[
\int_s^t e^{\pi iA(u-s)}
 K_{\rm pre}(t,u)K_{\rm in}(u,s)Q_1(u,s)Q_2(u,s)\,du.
\tag{13.1}
\]

The expressions include all side subobjects in their corresponding factors, with the spatial boundary data inherited from the decoration. A trivial factor is 1. There is no multiplication of the terminal pin and no summation over alternative cuts.

**Proof.** If a prefix vertex i<a were linked to an interior vertex a<j<2h, then `(i,a,j,2h)` would be a crossing of the legal pairing, contrary to T849. Thus every prefix vertex is paired within the prefix. Every vertex strictly between a and 2h is then paired within the interior. The structure theorem T857 assigns each remaining side couple to precisely one of these links. The two side couples belonging to `{a,2h}` are Q₁,Q₂. Conditional on `t_{v_a}=u` and `t_{v_{2h}}=s`, the chain inequalities are exactly those of the two regular trees with boundary times (t,u) and (u,s). Each side couple has its original two upper times and its original layer restrictions. Its internal times are independent of the other factors. Integrating them and the two chains gives (13.1). The pin removes only the t_{v_{2h}} integration. ∎

Every link of the top chain lies in layer p. Consequently all incoherencies are in the four unmarked components of (13.1), and their incoherency indices add to that of the whole object.

**Proposition 13.2 (uncut terminal-pin time-Fourier bound).** Use the localized exceptional-pair boxes of T1002–1017 for the link `{a,2h}`. Let the whole tree have order 2m and incoherency index g. Assume (11.1), and insert no unresolved spectral filters into its components. For each fixed lattice output k, its pinned kernel satisfies

\[
\|K_{\rm pin}(\cdot,\cdot,k)\|_{X^\eta}
\le (C\delta)^m L^{2\gamma}
 L^{-(\gamma_1-\sqrt\eta)g}.
\tag{13.2}
\]

The fixed number of ordinary localization/Fourier-amplitude constants are charged in C or in their stated total variation. Uniformly on any fixed unit output ball, the lattice kernel admits an extension with

\[
\|K_{\rm pin}\|_{X^{\eta,30d,0}}
\le (C\delta)^m L^{31d+2}
 L^{-(\gamma_1-\sqrt\eta)g}.
\tag{13.3}
\]

The estimates are uniform in the center of this ball and in the layer assignments. They do not assert an unlocalized global X norm over arbitrary output centers, or any decay weight in k. These are bounds on each localized expression. The output decay of the side couples Q₁,Q₂ in their weighted `X^{η,30d,30d}` bounds, or profile decay when a side is trivial, sums the exceptional unit-box centres. The strong version below uses o82 Revision 1, Lemma 16.1, with the same output decay.

**Proof.** Fix the two exceptional spatial variables x,y first. The four components in (13.1) are ordinary unmarked regular objects with total half-order m−1. Their ordinary time-Fourier estimates are T953–955 for incoherent components and T1097–1110/T1145–1164 for coherent components. Retain the side-couple output decay for the subsequent sum over exceptional unit-box centres; it may be omitted only in the fixed-boundary time-norm display below. Their product, pulled back to the three coordinates (t,u,s), has a Fourier-measure norm bounded by

\[
C^{m}\delta^{m-1}L^{-(\gamma_1-\sqrt\eta)g}.
\]

The weighted Fourier algebra follows by convolution; there are only four factors. Boundary momenta of these components are fixed affine functions of k,x,y. All required bounds are uniform in these momenta. Apply Lemma 12.1 to (13.1). Sum the at most `(CL)^{2d}` exceptional lattice tuples and restore their two branching normalizations. The extra factor is

\[
\left(\frac\delta{2L^{d-\gamma}}\right)^2(CL)^{2d}
\le C\delta^2L^{2\gamma}.
\]

Thus the result is `C^mδ^{m+1}L^{2γ}` times the unchanged incoherency gain; use δ≤1 to get (13.2). This argument uses the source ordinary component bounds, not the scalar estimate (4.1) as a substitute for a Fourier norm.

For (13.3), the unit ball contains at most `(C_dL)^d` lattice outputs. For each output k₀ choose a time extension achieving (13.2) up to a fixed factor. Let ψ be a fixed smooth bump supported in `|z|<1/3` and equal to 1 at zero. Define

\[
K_{\rm ext}(t,s,k)=\sum_{k_0\text{ in the output ball}}
 \psi(L(k-k_0))\,G_{k_0}(t,s).
\tag{13.4}
\]

This agrees with the lattice data on the required ball. Each output derivative of order ≤30d costs at most `C_dL^{30d}`. Taking the output supremum inside the Fourier integral is now bounded by the finite sum of the norms of G_{k₀}. This costs at most `C_dL^{31d}`. Finally `2γ<2`. This proves (13.3) without interchanging a supremum and an integral. ∎

The cap constraint may be included in the finite lattice data before (13.4); zero data at incompatible k₀ produce zero coefficients. Thus at this local time-Fourier level it does not require an additional power of L. Formula (13.4) is a local extension for the marked kernel, not a change to the common real leaf profiles in (11.1).

**Coefficient consequence and limitation.** Whenever the four factors in (13.1) have the spectral coefficient representation required by o82, Lemma 12.2 supplies that representation for the terminal pin with **one** new exceptional linked coordinate and no resonance-dependent pin loss. Its cost is `L^0` before the exceptional spatial sum. This proves the pin insertion rule at that interface. Proposition 13.2 proves the time-Fourier conclusion for actual ordinary layered side objects even without those raw coefficient representations. It does not manufacture the latter for the components carrying upper stem filters; the general unfiltered-to-filtered coefficient interface is still a separate requirement.


## 14. The first genuine child face, with its frequency consumed

The following configuration is an actual regular object, rather than an arbitrary time multiplier. Take a two-node regular chain with nodes x>y, pin y=s, and insert a type-1 mini-couple in one of the two side leaf pairs of that chain. Denote its root times by u and v. Thus

\[
s<x<t,\quad 0<u<x,\quad 0<v<s,
\]

and its phases, after translating p to zero, are

\[
e^{\pi i[A(x-s)+\beta(u-v)]}.
\tag{14.1}
\]

The other side pair and the three leaf pairs of the mini-couple are trivial for this calculation. This is a coherent regular object of order four with one terminal pin and one selected stem vertex x. It is obtained by the operations in T826–828. The selected integration has lower endpoint `max(s,u)`.

Integrating x first gives the three terms

\[
K_{A,\beta}=\frac1{\pi iA}
\bigl(F^{\rm top}_{A,\beta}-F^{\rm pin}_{\beta}
-F^{\rm child}_{A,\beta}\bigr),
\tag{14.2}
\]

where, writing `H_z(r)=(e^{πizr}−1)/(πiz)` with its continuous value at z=0,

\[
\begin{aligned}
F^{\rm top}_{A,\beta}(t,s)&=
 e^{\pi iA(t-s)}H_\beta(t)H_{-\beta}(s),\\
F^{\rm pin}_{\beta}(t,s)&=H_\beta(s)H_{-\beta}(s),\\
F^{\rm child}_{A,\beta}(t,s)&=
 e^{-\pi iAs}\int_s^t e^{\pi i(A+\beta)u}\,du\ H_{-\beta}(s).
\end{aligned}
\tag{14.3}
\]

The top term is the sum of the two top-face pieces from u<s and u>s. They have the same sign and identical formula after their domains are reunited. The second term is the lower face on u<s. The third is the lower child face on u>s. Ties have zero Lebesgue measure. Thus (14.2) is an explicitly specified signed face collection; its three terms have multiplicity one.

**Proposition 14.1.** Put `0≤θ<1`. The child-face coefficient has an extension for which

\[
\sup_A\int_{\mathbb R}\int_{\mathbb R^2}
 w_\theta(\lambda)|\partial_\beta^r
 \widehat F^{\rm child}_{A,\beta}(\lambda)|\,d\lambda d\beta
\le C_\theta^{r+1}(2r)!.
\tag{14.4}
\]

For `p_0≥0`, `θ_0≥0`, `p_0+θ_0<1`, it also obeys

\[
\sup_A\int\langle\beta\rangle^{p_0}
 w_{\theta_0}(\lambda)
 |\widehat F^{\rm child}_{A,\beta}(\lambda)|\,d\lambda d\beta
\le C_{p_0,\theta_0}.
\tag{14.5}
\]

In particular the D23 exponents `θ=1−η/8`, `p₀=1−η/2`, `θ₀=η/4` are permitted. The actual modulation has been consumed in this estimate. There is no new positive L power, no dependence on A, and no exceptional β coordinate.

**Proof.** Multiply the smooth formula in (14.3) by one fixed compactly supported smooth cutoff in (t,s) equal to one on the square. For each fixed r, differentiated factors H_z and their differences have weighted Fourier estimates

\[
\int w_\theta|\partial_\beta^r\widehat F^{\rm child}_{A,\beta}|
\le C_\theta^{r+1}(2r)!
\frac{\langle A\rangle^\theta+
\langle\beta\rangle^\theta+
\langle A+\beta\rangle^\theta}
{\langle\beta\rangle\langle A+\beta\rangle}.
\tag{14.6}
\]

Here is a direct verification that does not differentiate a singular formula at zero. When both `|β|` and `|A+β|` exceed 1, expand the two differences of exponentials in (14.3). Each term is a fixed cutoff times an exponential, divided by `β(A+β)`. Its time frequencies are `(A+β,−A)`, `(A+β,−A−β)`, `(0,β)` or `(0,0)`. Every β derivative either differentiates a reciprocal, or inserts a bounded power of t,s. The differentiated reciprocal bounds are `r!|z|^{-r-1}≤r!|z|^{-1}`. The weighted Fourier norms of the cutoff times those powers are at most `C^{r+1}(2r)!`; a fixed finite number of integrations by parts proves this, or a fixed Gevrey cutoff gives it directly. These facts give (14.6).

If `|β|≤1`, use `H_{−β}(s)=s∫₀¹e^{−πiβsv}dv` and its differentiated version. The frequencies introduced are bounded; the other factor is treated by its large-frequency formula or its analogous small-frequency integral. Use the integral representation for the `(A+β)` factor when `|A+β|≤1`. These four regions cover all parameters and give (14.6) without a singularity.

It remains to integrate the right-hand side. For `|A|≤4`, it is bounded by `C⟨β⟩^{θ−2}`, which is integrable. For `|A|>4`, split into `|β|≤|A|/2`, `|A+β|≤|A|/2`, and the complement. In the first two regions the integral is at most `C|A|^{θ−1}log(2+|A|)`. In the complement, the bounded part with `|β|≤2|A|` contributes at most `C|A|^{θ−1}`, and the remaining tail is controlled by `∫_{2|A|}^∞r^{θ−2}dr`. All these expressions are bounded uniformly for θ<1. This proves (14.4). Inserting `⟨β⟩^{p₀}` makes the same argument bounded by a constant plus `C|A|^{p₀+θ₀−1}log(2+|A|)` and a tail with exponent `p₀+θ₀−2`. This proves (14.5). ∎

For the pin-face term F^pin the same argument with both denominators centered at β gives (14.4)–(14.5) without an exceptional A. For the top term, keep `e^{πiA(t−s)}` outside its coefficient. The remaining product H_β(t)H_{−β}(s) obeys the same two estimates. If its **consumed** time norm only requires exponent `θ≤1/4`, multiplying the phase costs at most `C⟨A⟩^θ≤C⟨A⟩^{1/4}`. This is exactly the modulation allowance in o82 §9, item 4, while the reciprocal `(πiA)^{-1}` remains outside. For the stronger exponent `1−η/8`, a standalone uncentered top-face bound would not have that `1/4` allowance; the separate-phase convention or a retained collection is essential.

## 15. Exact arbitrary-side face identity and the remaining norm issue

The geometry of §14 also gives a useful identity with arbitrary ordinary side couples. Suppose the two-node stem chain has side kernels Q₁(x,s), Q₂(x,s), and its terminal time is pinned at s. Before any selected integration its expression is

\[
K_A(t,s)=\int_s^t e^{\pi iA(x-s)}Q_1(x,s)Q_2(x,s)\,dx.
\tag{15.1}
\]

For A≠0 the exact signed collection is

\[
\begin{aligned}
\pi iA K_A(t,s)={}&e^{\pi iA(t-s)}Q_1(t,s)Q_2(t,s)
-Q_1(s,s)Q_2(s,s)\\
&-\mathcal T_A[(\partial_1Q_1)(u,s)Q_2(u,s)](t,s)
-\mathcal T_A[Q_1(u,s)(\partial_1Q_2)(u,s)](t,s).
\end{aligned}
\tag{15.2}
\]

For a trivial side tree the corresponding derivative is zero. If a side root lies below layer p its upper boundary is independent of x∈(p,p+1), so its derivative is also zero. Each nonzero derivative is a root-time trace of that side couple. Its raw child-root inequalities specify the maximizing-child face exactly as in §14. Expanding the product derivative in (15.2) partitions these child faces; coincidences of distinct branching-root times have measure zero. Formula (15.2) also follows directly by integration by parts, which checks its signs.

The floor face vanishes for the selected stem times in the original flower geometry: every selected stem branching vertex has a branching child on the stem, whose time is at least s>p (equal to s only for the pinned flower parent). Consequently the maximum lower endpoint is strictly greater than the layer floor p. This observation applies before new excisions; it does not discard a floor face in an artificially cut object with different boundary data.

**Why the available side-kernel norm is not itself a root-trace bound.** The operator in the child terms of (15.2) is not bounded uniformly in A on the sole input space X^η. This is an explicit norm-level obstruction, not a claimed counterexample to ordinary side couples. Take fixed smooth cutoffs equal to one on a compact rectangle inside `0<s<t<1`, and on that rectangle put

\[
Q_N(u,s)=N^{-\eta}e^{-\pi iNu},\qquad Q_2=1,
\quad A=N\longrightarrow\infty.
\tag{15.3}
\]

With the fixed cutoffs, `||Q_N||_{X^η}≤C`. But the child expression on that rectangle is

\[
\mathcal T_N(\partial_1Q_N)(t,s)
=-\pi iN^{1-\eta}(t-s)e^{-\pi iNs}.
\tag{15.4}
\]

Its modulus, hence even its unweighted Fourier norm on this domain, is at least `cN^{1−η}`. The bound remains false after recentering the displayed phase, since its amplitude grows. It also exceeds o82's permitted `⟨A⟩^{1/4}` modulation charge when `η<3/4`. Retaining the selected reciprocal makes (15.4) of size `N^{−η}`, which still does not by itself give the required fixed selected-occurrence power when η is chosen very small.

Thus applying T953–955 to Q₁ and then differentiating is not a completion of (15.2). The example is a counterexample to **that norm-only inference**. It is not asserted that Q_N is an ordinary side-couple kernel with bounded profiles (11.1); actual kernels have additional linked-frequency structure. Proposition 14.1 proves that this structure resolves the issue for a type-1 mini-couple with trivial descendants. A full solution must use that structure for arbitrary descendants and for internal selected vertices, rather than treating (15.3) as an admissible replacement or asserting a false operator bound.


## 16. INTERFACE FOR o82 — revised consumer after Addendum 3

This section supersedes the *required* interface in §10. The latter remains a possible stronger theorem, but is not needed for the following variant. Nothing in §§1–15 claimed its proof. The current variant uses **o75 Revision 1** and the ordinary-kernel results in **o82 Revision 1, §§14–18**, particularly Proposition 15.1, the weighted Lemma 16.1, and Theorem 18.2. It does not use the conditional Theorem 13.1 to prove its own premise.

The dependency versions used after Revision 1 (§23 below) have hashes:

| Packet | SHA-256 |
|---|---|
| o63 | `a50e0f93d68ac6fab7dfbfd59efb5808a1dc9717b391475c0d29d3cde7ddebc4` |
| o75 Revision 1 | `ab0c438cb930f505bb6644409516da6ad8c8b8ccf38ecc4ccaa2576768635931` |
| o82 Revision 1 | `d5b09e81385ba62908275a9655393db3442b80d061e6b68e5d2d7ddc2576bf57` |

These references specify statements, not a reliance on the other packet's final STATUS. In particular o82 Theorem 18.2 is an unconditional local theorem. The original continuation used the pre-revision o75 and o82 reports; the revisions cited here supply the clarified consumer contract and weighted ordinary-kernel bounds.

The coefficient consumers can be separated as follows.

1. **Ordinary coherent objects.** Use the original-coordinate decomposition and the two coefficient weights of o82 §§3, 10–11. Its principal approximation is needed for the unmarked cancellations. No pin or selected face is inserted into that decomposition here.
2. **A protected regular object containing a selected vertex.** Keep the original annular kernel. Its exact signed raw-face collection, with every selected reciprocal, is used only for the pointwise bound. The Fourier estimate is for that whole collection, reconstructed as the original kernel; it is o82 Theorem 18.2. Thus a Fourier estimate for each raw child face is unnecessary. All its incoherency gains survive.
3. **A protected regular object with a terminal pin but no internal selection.** Use §13 and o82 Corollary 15.2. If its boundary meets a selected residual vertex, use the stronger norm in §17 below.
4. **A selected vertex or pin in the residual garden.** Fourier expand the already estimated regular objects and unmarked vines first. The residual coefficient is the scalar time integral of T1996. Its mixed local-supremum estimate is proved in §18. Selected integration uses the *total* frequency, including the Fourier modulation. Section 20 proves the selected-occurrence estimate, also in the case of cancellation between the original and added frequencies.

There is no excision and no boundary object created by excising a marked vine. The special vertices of o75 remain in the residual garden; their unmodified attached regular objects have the ordinary estimates. There are no Section-6 selected frontier or modified-leaf marks.

For protected factors used outside unmarked vine interiors, **time Fourier mass without a weight is enough unless a selected residual vertex consumes that factor**. This assertion has a specific source-level justification. T1978–1991 is uniform in every modulation `ξ_v`. The coefficient estimate T1996–2037 is also uniform in them: they enter the constants `c_w,d_w` in T2009–2015, and all subsequent denominator estimates are uniform in their shifts. The counting estimate at T2091–2096 is uniform in the resulting `(β_v)`. The final bounds T2224–2225 have no positive power of `ξ_v`. Consequently one may omit the negative modulation factor in T1963 when estimating the moment at fixed external times. The positive source weight remains available on all unmarked factors. For the selected residual vertices we will instead consume an explicit product of `1/18` moments, supplied by an `X^{1/4}` bound on their adjacent regular factors. No unbounded exceptional phase is discarded inside a positive weighted Fourier norm.

All subsequent statements are uniform over exactly

\[
 (F_q)_q\in\mathcal P(2c_\chi C_1),\qquad
 F_q\text{ real},\qquad
 \sup_q\|F_q\|_{\mathfrak S^{40d,40d}}\le2c_\chi C_1.
 \tag{16.1}
\]

The fixed profile multiplier belongs to the exponential base. Every exponential base below is chosen before δ. Assume the source smallness of η, strengthened if necessary to `η≤1/16` and `200dη≤√η`, as in o82 §§15–18. No parameter chosen after δ is put in an exponential base.

## 17. The regular-object estimates actually used

Put `c_g=γ₁−√η` and `G(O)=L^{−c_g g(O)}`. A normalized regular object has order `2m`. Spatial localizations and affine low-pass factors are those in T995–1017 and S Lemma 3.1; their summed Fourier-measure costs are included in a fixed exponential base. The following statements concern values on the lattice, with an extension on any prescribed unit output ball.

**Proposition 17.1 (regular factors).** In the original flower geometry, before any excision, the following bounds hold.

(a) An ordinary factor has its source `X^{η,30d,30d}` couple bound or `X^{η,30d,0}` paired-tree bound. By o82 Revision 1, Lemma 16.1, it also has the weighted bounds
\[
 \|K_{\mathcal Q}\|_{X^{1/4,30d,30d}}
 +\|K_{\mathcal T}\|_{X^{1/4,30d,0}}
 \le C^{m+1}(C_1\delta)^m L^{4d}G(O).
 \tag{17.1}
\]
Only defined terms are included, each with its own order and incoherency index. These bounds imply the fixed-spatial-boundary `X^{1/4}` bound and retain the output decay needed when couple centres are summed.

(b) A terminal-pinned factor has
\[
 \|K_{O,\mathrm{pin}}\|_{X^{1/4}}
 \le C^{m+1}(C_1\delta)^m L^{16d+2}G(O).
 \tag{17.2}
\]
Its local `X^{1/4,30d,0}` extension costs `L^{47d+2}` instead. In `X^η` the sharper costs from §13 are `L²` at fixed output and `L^{31d+2}` locally.

(c) If it has `a` selected annular occurrences and `b₀∈{0,1}` terminal pins, put `r=a+b₀≥1`. Its **whole signed face collection with its reciprocal product** satisfies
\[
 \|K_{O,\mathrm{ann}}\|_{X^{\eta,30d,0}}
 \le C_{P,\chi}^{m+1}(C_1\delta)^m
 L^{(47d+5)r}G(O)M_2^{-a/18}.
 \tag{17.3}
\]
The complete original incoherency index occurs in each of these estimates. Upper filters may be present at all permitted stem positions. The constants are uniform over (16.1), the filter scales, and spatial centers. A cap is encoded by the paired-tree boundary condition and the exact lattice output indicator; no Schwartz estimate for a constant cap profile is used.

**Proof.** Part (a) is o82 Revision 1, Proposition 15.1 and its weighted Lemma 16.1. Their incoherent argument is the raw pair calculation T1021–1091 with the upper-filter convolution estimate, and their coherent argument uses the original coefficient representation. In particular this does not assume a mixed spectral decomposition for an arbitrary incoherent side object.

For (b), the exact legal-partition cut (13.1) has one exceptional linked pair and four ordinary factors of total half-order `m−1`. Use the weighted couple and paired-tree bounds (17.1), from o82 Revision 1, Lemma 16.1. Their product, pulled back to the three boundary variables, has `X^{1/4}` norm at most the product of these bounds, with cost at most `L^{16d}`. The side-couple output decay, or profile decay for trivial sides, sums the exceptional unit-box centres without a further L power. Lemma 12.1 consumes the phase of the fixed exceptional pair uniformly. Its two branching normalizations and its unit-box lattice sum cost at most `L²` relative to `(C₁δ)^m`. All incoherent links are in the four factors, by Proposition 3.1. Output interpolation by disjoint lattice bumps, (13.4), costs `L^{31d}`. The same argument with the ordinary `X^η` bounds gives the sharper assertion. The Fourier-measure localization is performed on the remaining exceptional pair; no additional arbitrary restriction on the internal variables of an ordinary factor is imposed. Summability of these localizations follows from the original leaf amplitude as in T995–1017.

For clarity, (c) uses the following precise interpolation, proved in o82 §§17–18. On a unit square or unit time triangle, there is an extension preserving the supremum and mapping the restricted Fourier algebra `A^{1/4}` into `A^{1/8}`. It reflects across the sides and sorts the two coordinates across the diagonal. Each fold loses at most `1/40` of an exponent: on a Fourier atom its weighted Fourier norm is bounded by `C⟨a⟩^σ log(2+|a|)`. The five folds therefore suffice. Frequency splitting followed by Plancherel gives
\[
 \|f\|_{A^\eta(D)}
 \le C_\eta\|f\|_{L^\infty(D)}^{\tau}
                  \|f\|_{A^{1/4}(D)}^{1-\tau},
 \qquad \tau=(1-8\eta)/9\ge1/18.
 \tag{17.4}
\]
The pointwise norm of the exact raw-face collection is at most
`C^{m+1}(C₁δ)^m G(O)L^{3r}M₂^{−a}`, by §4 and o82 Proposition 14.2. In the strong norm keep the original time integrations and use (17.1) or (17.2), now with the fixed annular multipliers. Their Schwartz Fourier moments have the same bounds as upper multipliers, so the proof is unchanged (o82 Lemma 18.1). Interpolation keeps `G(O)` to power one, gives `M₂^{−aτ}`, and costs at most `L^{(16d+5)r}`. The local output extension adds `31d≤31dr`. This proves (17.3).

In this argument the top, parent, child and floor faces have their original signs and multiplicities from S Lemma 9.1. The collection equals the original kernel exactly. Individual face indicators are never assigned a Fourier norm. In the original stem geometry the floor face is empty, as proved in §15. Repeated occurrences retain all their reciprocal factors in the pointwise estimate, hence retain the corresponding multiple of `1/18` after interpolation. ∎

**Boundary incidence observation.** A regular kernel in the collapsed garden has at most two time arguments. A residual vertex can occur as a boundary argument of at most seven regular kernels: the paired tree attached at that vertex, the at most three attached at its children, and the at most three leaf-pair couples incident there. This deliberately overcounts. If that vertex is selected, none of these kernels can contain another selected original stem vertex. Indeed a regular paired tree belongs to its one original tree, which has only one selection; a regular couple containing a stem vertex is paired with that tree's trivial cap, by Proposition 3.1, and cannot attach to a second original stem. A side couple can have two selected residual boundary arguments, but has no internal stem selection. Thus (17.1)–(17.2), rather than (17.3), supply the stronger norm at every selected residual boundary.

An unmarked spliced-vine kernel cannot have a selected residual boundary argument. Its time arguments are those of `u₁,u₂₁,u₂₂` (T1956). If the selected vertex is `u₁`, its child toward the vine, or the regular object containing that child, is protected by Π2. If it is `u₂₁` or `u₂₂`, its parent toward `u₂` is protected. In each case the twist-active set contains a protected vertex and the vine is marked. The same argument through the endpoint regular trees covers an original child replaced during the regular reduction. Such vines remain unspliced under o75. Hence no stronger estimate for an unmarked vine is required.

## 18. Residual coefficient: pins, endpoint faces, and local suprema

Here the frequency at a residual atom is
\[
 \beta_v=\delta L^{2\gamma}(-\Gamma_v+\Gamma_v^0),
 \qquad \alpha_v=\beta_v+\xi_v.
 \tag{18.1}
\]
The shifts ξ are fixed during the coefficient estimate. The garden and molecule are precisely the connected, unexcised objects of o75 Theorem 7.5′. Keep the maximal ladders, their lengths `z_j`, and `ρ_sb` from T1994. Put
\[
 \mathcal R_N=(C_1\delta^{-1/2-5\nu})^N
 L^{\delta^{5\nu}\rho_{\rm sb}}\prod_j\mathsf X_j^{z_j},
 \qquad N=n_{\rm sb}.
 \tag{18.2}
\]
Changing a fixed constant in the base of this expression is allowed below.

**Proposition 18.1 (mixed residual coefficient estimate).** Let E be a set of at most r residual atoms whose original frequencies β are fixed. At some of these atoms omit the time integration and set its time to a prescribed boundary time in its layer; at other atoms perform at most one selected endpoint substitution per original tree, using its parent, a maximizing child, or its layer endpoint. A bounded number of pins per tree is allowed, counted in r; in particular two atoms in one tree may be pinned at the same time. A selected time is not already pinned. Include the exact ordering inequalities for that endpoint and substitute its phase at the recipient. All eliminated atoms belong to E. Other atoms in E may retain their time integrations. Then the resulting coefficient B_F satisfies
\[
 \sup_{\beta_E}\ 
 \sum_{\sigma_{E^c}\ {
m available}}
 \sup_{|\alpha_v-\sigma_v|\le1,\ v\notin E}
 |B_F(\alpha_{E^c};\beta_E,\xi)|
 \le C_r^{N+1}L^{4r}\mathcal R_N.
 \tag{18.3}
\]
Here availability is defined using the original decoration constraints, with β_E fixed. The bound is uniform in all ξ, all external pin times, and all unit spatial boxes. The same estimate holds after including any of the dephased derivative factors needed in T2003–2007. No summation or unit-interval supremum in E is asserted in (18.3). Restoring the exceptional spectral supports is the separate finite-support cost of S Lemma 7.1, already o75 row 12.

**Proof.** The changes to the four steps of T2003–2037 are as follows.

*Localization and local suprema.* Apply T2005 only in Eᶜ. Before taking absolute values its derivatives insert products of `πi(t_v−L_v)` for distinct remaining variables. Each factor is bounded on the original unit layer interval. The eliminated phase is parameter dependent only in E; it is not differentiated. The same bounds apply to these polynomial insertions by the one-dimensional integration by parts used in the source. All affine rung relations T2013 persist with changed constant terms, since β_E and ξ are fixed. Retain their original anchor pairs. Every remaining α_v belongs to a translate of a union of at most `L^{20d}` unit intervals, as in T2015. Uniformly in its translate and in c,
\[
 \int_{\mathcal S_v}\langle\alpha_v+c\rangle^{-1}\,d\alpha_v
 \le C_d\log L.
 \tag{18.4}
\]
This follows by decreasing rearrangement of the integrable truncation of `⟨x⟩^{-1}` over a set of measure at most `CL^{20d}`; locations and overlaps of the intervals are immaterial.

*The X variables.* Start with the source orientations of the double bonds. Do not impose an orientation on a rung incident to an atom of E or to an endpoint recipient. Force every such rung's formerly chosen larger-time vertex out of X. An atom belongs to at most one rung pair of a maximal ladder; allowing two instead only enlarges the bound. There are at most r exceptional atoms and r recipients, so at most `h≤4r` variables are removed from the source X. Keep the remaining orientations and anchors. For every retained X variable its mate is still in Y or is a fixed-frequency atom; T2013 thus still confines its α coordinate to an interval of uniformly bounded length after α_Y is fixed. The source two-monotone-subsequence assertion remains true by taking limits from the legal strict time domains defining the face. There are finitely many choices of the two monotone subsequences, so a subsequence of an approximating sequence uses one fixed choice, whose weak ordering persists in the limit. The retained X sequence is a subsequence of that ordered sequence. Equalities cannot enlarge its integration volume. If h_j variables were lost from a ladder, its factorial denominator can therefore be replaced by `(z_j−d−h_j)!`, with negative factorial indices replaced by zero. Relative to the original bound this costs at most `(N+1)^{h_j}`. Its D power can be bounded by the original `D^{z_j}`. Fixed X times at pins simply restrict these domains further.

*The Y integration.* With X fixed, the remaining parent-child domain is a rooted forest with constant lower boundaries and a unique variable parent upper boundary. Contracting a parent-child face preserves this property. For a maximizing-child face, the inequalities that the other children lie below the recipient make them children of that recipient after contraction. A pin splits a tree at a fixed time and introduces constant boundaries. Any orientation involving a contracted or fixed vertex was removed above; every retained rung orientation only gives a constant boundary from a fixed X time. As in T2025–2029, integrate minimal Y vertices first. The integral at each vertex is an integral of an exponential, possibly times the bounded degree-one polynomial from the first step, over an interval of length at most one. It is a sum of a fixed number of terms with a bound `C⟨α_v+c⟩^{-1}`. A term with a retained time but fixed frequency in E can instead be bounded by C, losing its denominator. Elimination transfers frequencies to the unique parent and preserves the same form. The unintegrated α variables can be integrated in reverse elimination order using (18.4); the triangular changes of frequency have diagonal entries one, including when fixed E coordinates are omitted. Thus this step costs at most `C^{N+1}(log L)^{|Y\E|}`. The dephased polynomial insertions change the fixed base only: their primitives add a bounded number of endpoint terms, or a further denominator, per eliminated vertex. Equivalently they can be represented using fixed finite Fourier measures on each unit interval, after which (18.4) is uniform in the additional shifts.

*Completion.* Compared with the source Step 4, at most h extra logarithmic factors and at most h factorial factors have been introduced. Discarding fixed-frequency denominators creates no further logarithm. Therefore its bound is at most
\[
 C^{N+1}(N+1)^{4r}(\log L)^{4r}\mathcal R_N.
 \tag{18.5}
\]
For fixed r, `(N+1)^{4r}≤C_r^{N+1}`, with C_r independent of δ, and `(log L)^{4r}≤L^{4r}`. This proves (18.3). The orientation choices and face choices cost fixed exponentials already allowed. The source final comparison using `Dδ≤δ^{−ν}` is unchanged: we used its original D power and original N, not a smaller order with an inadmissible δ-dependent base. ∎

**Why this is a local-supremum result.** The dephased box inequality was applied before the coefficient was bounded, in the nonexceptional coordinates. Formula (18.3) is not obtained by bounding a supremum by an integral. In particular it fills the residual local-supremum obligation left open in §§6–10.


## 19. Addendum 4: individual faces, root traces, and F_ch

The added input is o104 Proposition 7.4 and the exact pattern formulas (P1)–(P8) in its Proposition 7.3; the report read here has SHA-256 `21e48492cd207fb986f37c9856f4b3ed49481a675f4b4cf7f89e6ea9fac273af`. We use its root-trace identity with the phase explicitly displayed, not a uniform positive Fourier norm of that phase. Thus the interpretation of o104 (7.2) here is a centered Fourier bound followed by the consumption described below. The elementary counterexample in §5 still rules out an uncentered positive-weight assertion for the pure phase in (P2).

### 19.1 Root trace and its modulation

Assume the traced root ρ is in layer p. Fix the spatial pair of its root link, with signed frequency B. Removing that link leaves at most four ordinary regular objects, of total half-order `m−1`. Their incoherency indices sum to `g−ε_g`, where `ε_g∈{0,1}` records whether the removed link is incoherent. The root trace has the representation
\[
 Q^\rho(\sigma,\ldots)
   =e^{\pi i\epsilon B(\sigma-q)}R_B(\sigma,\ldots),
 \qquad
 \|R_B\|_{A^\theta}\le C_\theta\prod_{i\le4}\|P_i\|_{A^\theta},
 \quad0\le\theta\le1,
 \tag{19.1}
\]
with ε either zero or one and q a fixed endpoint of a layer interval. The remainder R_B may depend on a third boundary time, such as the lone-port time, in addition to the two displayed or suppressed upper times; the Fourier norm includes all of these variables. Here and below all ordinary functions are evaluated only in their defining time domains.

The decomposition in o104 Proposition 7.4 proves (19.1): for a type-1 couple the mate-root is integrated against `e^{−πiBu}` and three child couples; for a type-2 root the first linked pair cuts off an interior paired tree, two side couples, and the remaining tree or couple. The fourth object in its case (c) is the other complete chain. A variable endpoint is treated by `T_B` or its mirror, a fixed layer interval by its Fourier-atom integral. One minor domain convention is essential for paired trees: the mate's range includes the lower bound from the lone port. If that port has the mate's layer, integrate from the port time, not from the layer floor. This is exactly `T'_B` with that port as lower endpoint. If the upper endpoint is a fixed layer endpoint q, write the phase as `e^{πiB(σ−q)}e^{πiB(q−u)}` and use the same mirror operator. If the port has a lower layer, the lower bound is the layer floor. These choices prove (19.1) without integrating an arbitrary extension outside an ordinary tree's triangle.

For the child expression of §15 this gives the identity
\[
 T_A[e^{\pi i\epsilon Bu}R_BQ_2]
   =e^{\pi i\epsilon Bs}T_{A+\epsilon B}[R_BQ_2].
 \tag{19.2}
\]
The right-hand integral has a uniform positive-weight norm; its remaining phase is recorded and consumed separately. If s is the external flower time, it has modulus one after the exceptional pair is fixed. If s is a residual boundary variable, it shifts that atom's ξ in (18.1), where Proposition 18.1 is uniform. In unweighted Fourier mass the shift itself is isometric. This is the actual-kernel resolution of §15, not an estimate of `∂Q` by the norm of Q.

### 19.2 The chain coefficient lemma needed for individual faces

Here is a smaller coefficient assertion than the full raw layered decomposition of §10. It integrates ordinary side objects first, preserving their full gains, and leaves the same-layer chain coordinates for the discrete estimate. This order is possible because all upper/selected stem filters are on that chain; a root trace adds just its one exceptional pair. It is not a claim of a raw coefficient decomposition for every incoherent side object.

**Lemma 19.1 (punctured legal chain).** Put `κ=η/16`. Start with a legal same-layer paired chain, insert arbitrary ordinary side kernels with their `X^{η,30d,30d}` bounds, and replace a bounded number of pairs by fixed-frequency, unpaired integration slots. Slots may have any real frequencies ω, including sums of exceptional frequencies. A pure exceptional boundary phase is allowed separately. Let h be the number of ordinary pairs remaining. For fixed side Fourier variables Λ and fixed exceptional spatial pairs, the chain has an exact representation
\[
 e^{\pi i\ell_E\cdot\tau}
 \sum_Z\prod_{j\in Z}g_j(\alpha_j)
 \int C_Z(\lambda,\alpha_J;\Lambda,E)e^{\pi i\lambda\cdot\tau}\,d\lambda,
 \quad J=\{1,\ldots,h\}\setminus Z,
 \tag{19.3}
\]
where `g_j(α)=χ∞(α)/(ε_jπiα)` is in the **original** linked coordinate. Put
\[
 B_\kappa(\Lambda)=\prod_{\ell\in\mathcal E_{\mathrm{side}}}
                    \langle\Lambda_\ell\rangle^{4\kappa}.
\]
Here ℰ_side indexes the side-endpoint Fourier variables. For each fixed Λ the coefficient bound is
\[
 \sup_E\sum_Z\int\!\int
 |\partial_{\alpha_J}^{\rho}C_Z(\lambda,\alpha_J;\Lambda,E)|
 \,d\alpha_Jd\lambda
 \le C_{P,\eta}^{m+|\rho|+1}(4|\rho|)!B_\kappa(\Lambda).
 \tag{19.4}
\]
At fixed (E,Λ), the separate spatial amplitude is W_{E,Λ}, represented by a Fourier measure of mass D_E(Λ). Its bound is
\[
 \sup_E\int B_\kappa(\Lambda)D_E(\Lambda)\,d\Lambda
 \le C_{P,\eta}^{m+1}(C_1\delta)^{m_{\rm side}}
                  L^{-c_g g_{\rm side}}.
 \tag{19.4a}
\]
The estimates are uniform in ω and ℓ_E. Multiply the chain's output extension by a fixed smooth Gevrey cutoff equal to one on its bounded time domain. Its Fourier transform convolves the possible line-supported Fourier measure into a density; its fixed Fourier mass changes only C_{P,η} and commutes with the spectral derivatives. Thus C_Z in (19.3)–(19.4) can be taken as a density. Its consumed time weight is **one**. All spectral derivatives required by o82 Revision 1, Theorem 10.1, are present. Apply that theorem at fixed (E,Λ), with coefficient factor B_κ(Λ) and amplitude mass D_E(Λ), and only then integrate in Λ using (19.4a). No strong spectral moment is asserted for this protected block; no principal approximation of it is used.

**Proof.** Use the J/R classes of D21 955–963 with their `1/4` weights replaced by κ. Each of the composition lemmas D21 966–1081 still holds with a fixed base C_κ. Here are the precise analytic reasons for the change of exponent. Their weight decompositions use subadditivity of `x↦x^κ`; their scalar integrals are products of two reciprocal denominators in one variable, three in two variables, or such products times a decaying Gevrey function. At most one κ weight is allocated in each summand. Replacing `1/4` by the smaller κ weakens every denominator power that is used to pay that weight, so each of the displayed uniform integrals in D21 1011–1067 remains bounded by the same splitting argument. For example the two-denominator integral is controlled by Cauchy–Schwarz with powers `1−κ` and 1, both greater than 1/2. The three-denominator integrals follow by first convolving two such factors; their tail has power at least `2−2κ`, and the remaining one-dimensional integral converges. Gevrey derivative convolution and the factorial combinatorics in D21 984–994 are unchanged. The constants depend on κ, chosen before δ.

An unpaired slot `I_ω` is the J operator `J_{0;0,ω}` with an empty spectral set. The γ₂ direction is explicitly unweighted in the J class, so its norm is uniform in ω. Delta measures in the unused coefficient directions can either be kept as finite measures or smoothed by the identity D21 1055. Insert these slots as the X_a operators in D21 1084–1094. Extract a reciprocal from an adjacent paired pair only when the intervening X_a is the identity, as in D21 1071–1081; otherwise use the enclosing-pair composition lemma. Removing adjacent pairs and concatenating or enclosing the resulting legal subpartitions is precisely the induction of D21 1086–1094. It gives at most a fixed exponential number of terms and the same fixed exponential bound, also with the inserted slots.

Apply the resulting J/R operators to the terminal exponential. D21 1122–1143 proves the final Fourier coefficient estimate; the same denominator argument applies with κ. Translate the layer and lower chain endpoint back. Complete unexceptional pairs have zero total frequency, so the only new pure phase involving linked frequencies is ℓ_E. The other translation phase uses Λ. For the **unweighted** output norm this phase has unit Fourier mass. Taking spectral derivatives in J does not differentiate ℓ_E.

Before the induction, normalize the two modulations at a pair as at D21 948: `α_j↦α_j+ε_jλ_a`. Here λ_a is a sum of side Fourier variables only; no exceptional ω is placed in a paired slot. Restore every extracted pole to its original α_j using
\[
 \|g(\cdot+c)-g\|_{L^1}
 \le C\log(2+|c|)\le C_\kappa\langle c\rangle^\kappa.
 \tag{19.5}
\]
For a positive derivative order, `g^{(r)}` is integrable and its translated difference has the same estimate with a Gevrey factorial. Move each difference term from Z into J. As in D21 1142–1146, a side endpoint variable is charged at most once for this pole correction and once for an output/translation weight if one retains the centered κ estimate. The generous charge `4κ` per endpoint therefore suffices. A side kernel has two endpoint variables; `8κ=η/2≤η`, so its ordinary time-Fourier norm pays all these charges. The source disjoint-variable factorial estimate, followed by Leibniz for (19.5), is bounded by the displayed `(4|ρ|)!`. This proves (19.4) pointwise in Λ, with the derivative-independent factor B_κ(Λ); the fixed output cutoff described above changes only the fixed base.

For the spatial statement, first put each side output in a smooth unit box and Fourier expand its output dependence. The `30d` spatial derivatives and decay dominate its Fourier-measure mass, integrated with the just-described time weight. Pullback by its affine chain momentum map pushes forward that measure and does not increase its mass. Products multiply these masses. No derivative in a formal α_J acts on this separate spatial amplitude. Trivial side factors are the ordinary profiles and satisfy the same assertion. The source localization/coordinate argument T995–1017 sums the unit boxes with a fixed base: the two off-chain momenta at each link are independent affine coordinates, and their side-output decay supplies the required summability. This is localization of side **outputs**; no arbitrary internal restriction is imposed on a side kernel after it has been integrated. All incoherencies in those kernels remain in their ordinary bounds. Their time weights pay B_κ(Λ), and integration of the spatial Fourier mass in Λ gives (19.4a). The discrete theorem is applied first at fixed (E,Λ); its resulting bound is linear in B_κ(Λ)D_E(Λ), so (19.4a) justifies the subsequent Λ integration. ∎

### 19.3 Applying the lemma to each individual face

**Proposition 19.2 (individual-face version, including F_ch).** Allow the original terminal pin and the top or parent (upper) face of S Lemma 9.1 **summed over its maximizer cells**, or an individual stem-child, side-child, or layer-floor lower face **per maximizer cell**, without its reciprocal and without any selected-annulus assumption. Each upper face is the same-sign collection obtained by reuniting those cells; no bound on a single upper-cell contribution is asserted. Also allow the additional face
\[
 F_{\rm ch}:\quad t_m=s,
 \quad m\text{ an off-stem branching layer-p sibling of the flower},
 \tag{19.6}
\]
with the constraint `t_m<t_{\mathfrak f^{pr}}` dropped on their common boundary, as in o104 Lemma 6.3. Count each pin or face as one incidence, with total r. For a regular object these expressions have a representation of form (19.3)–(19.4a), after ordinary sides are integrated, with at most `e≤2r` exceptional linked coordinates, except when F_ch is in a separate object (o104 case (P8)). In that case its chain need not be single-layer: use the root-trace representation (19.1) directly, with its at most four ordinary factors and one exceptional link, rather than Lemma 19.1. Their normalized local, consumed `X^{0,30d,0}` bound is
\[
 C_{P,\chi}^{m+1}(C_1\delta)^m
 L^{(31d+6)r}G(O).
 \tag{19.7}
\]
No M₂ gain and no reciprocal is used in (19.7). All gains are retained after paying the numerical loss displayed. For pattern faces the stronger centered time-Fourier estimates in o104 (P1)–(P8) are also available, with their external phases recorded.

**Proof and exact face enumeration.** Make the following choices before applying Lemma 19.1.

* A terminal pin makes its linked pair exceptional. The remaining mate is an unpaired slot, with its exact phase. Noncrossing of the remaining pairing is preserved upon deleting this pair.
* For an upper face, first reunite all maximizer cells. Their same-sign indicators sum to one on the original upper-face domain, so no comparison with an internal side-root time remains. For this reunited upper face or a stem-child lower face in its own cell, make the selected vertex's pair exceptional. If the recipient is an integrated chain vertex, make its pair exceptional also. Transfer the phase and the selected vertex's side endpoint modulations to the recipient. All surviving vertices of these pairs are now unpaired slots. The other pairs form a legal partition. If the recipient was already in that same pair, or is a boundary time, no second pair is needed. At a boundary time the transferred phase is part of ℓ_E. Side couples are simply evaluated at the substituted upper argument. For a maximizing stem-child face this also imposes the other children's upper bounds, exactly as required.
* For a side-child lower face, write the relevant side factor as its root trace (19.1), and make that root link and the selected stem link exceptional. The root time u replaces the selected chain time; its range lies between the same neighboring chain times. All other children have upper bound u. The phase `εBu` of (19.1) is added to the unpaired slot at u, so that its frequency is `±A+εB`. The selected pair's mate is the other unpaired slot. The remainder of the chain is still legally paired. The at most four ordinary factors in R_B retain their side-output and time norms. The one possibly lost incoherency is precisely that of the exceptional root link. This step is valid for arbitrary ordinary descendants, by (19.1), and uses no differentiation of an already estimated norm.
* The original selected stem floor face is empty by §15. A fixed layer endpoint arising in the endpoint operator formulas is instead substituted as a constant and contributes only its explicit exceptional phase; the fixed-interval case in (19.1) covers it.
* The `dRoot` and `dParent` specializations are the individual faces in o104 Lemmas 6.1–6.2. Their exact cuts are (P1)–(P6); the dRoot top face is reunited over its maximizer cells. The `F_ch` face is the root trace (19.1), either in a side factor at the terminal cut (P7), or directly in a separate regular object (P8). For (P8) no single-layer-chain representation (19.3) is invoked. It adds one exceptional link. No selected resonance or reciprocal is required. Coincident pins retain one time variable per unpinned vertex and drop precisely the designated strict inequality, not every ordering constraint.

These rules account for each lower maximizing-child cell with multiplicity one and for the same-sign sum of all cells of each upper face. They also show why no fixed exceptional frequency is inadvertently added to an unexceptional paired slot; making the recipient pair exceptional was included for that purpose. The number of exceptional pairs is at most two per incidence, including overlaps.

For the chain cases use (19.4) and the independent-box discrete estimate o82 Revision 1, Theorem 10.1, with time weight one. First fix the exceptional **spatial pairs** E and the side Fourier variables Λ, not a spectral fiber in an oscillatory sum. Apply the theorem to C_Z with the separate amplitude W_{E,Λ}, then integrate Λ using (19.4a). For (P8) instead apply (19.1) to its ordinary factors at the fixed exceptional pair; no chain discrete estimate is needed. In both cases the count of exceptional unit-box tuples is at most `C^eL^{2de}`. Restoring all vertex normalizations changes the ordinary `(C₁δ)^m` bound by at most
\[
 \mu^e\le L^{2e},\qquad \mu=\delta L^{2\gamma},
 \tag{19.8}
\]
as in o82 (13.4). At most e incoherencies have been removed; restoring them costs at most `L^e`. Thus the fixed-output cost is at most `L^{3e}≤L^{6r}`. The finite-output extension costs `L^{31d}` once per nonempty protected object, at most `L^{31dr}`. This proves (19.7). Upper filters, if present, are inserted by o82 Lemma 11.1 in the remaining coordinates and are bounded scalars on the exceptional tuples. This use of o82 is its proved discrete theorem, not its conditional marked-interface theorem.

The phase ℓ_E either multiplies fixed external times, or translates Fourier variables of the residual coefficient. Translation preserves the norm with weight one and Proposition 18.1 is uniform in the translated frequencies. Thus (19.7) includes the modulation actually consumed. It is not an assertion that an isolated phase has uniformly bounded positive-weight Fourier norm. ∎

For `F_ch` in the residual molecule, simply include m in E in Proposition 18.1. Both m and the flower parent may be pinned at s. Their connecting inequality is dropped, exactly as in (19.6). The remaining domain is the rooted forest with these fixed boundaries used in that proposition. Hence its coefficient and residual obligations are the same as those for the original flower-parent pin. This absorbs the remaining face in Addendum 4.


## 20. Selected residual vertices: the added frequency is consumed

The previous section estimates individual faces without using a reciprocal. For the M₂ occurrence gain at a **residual** selected vertex, the most economical representation integrates after the adjacent kernels have been Fourier expanded. This avoids a root trace of a Fourier amplitude and handles possible cancellation of its frequency with the selected resonance.

Let S be the residual selected vertices, with `a=|S|`, at most one on each original stem. Keep their original annular factors, so that
\[
 |\beta_v|\ge c\mu M_2\quad(v\in S),\qquad \mu=\delta L^{2\gamma}\ge1.
 \tag{20.1}
\]
Fix their exceptional original frequencies β_v. For each adjacent regular object use (17.1) in the weighted form supplied by o82 Revision 1, Lemma 16.1, or the terminal-pin estimate (17.2), and Fourier expand. Side-couple output decay, or profile decay for trivial sides, sums the exceptional and adjacent unit-box centres. Ordinary adjacent factors already have the required local output derivatives at cost L^{4d}; retaining the larger charge below is an overestimate. Write ξ_v for the sum of its endpoint frequencies at v. By the boundary incidence observation of §17, no unmarked vine factor contributes at v. A regular factor can contribute at at most two selected residual vertices. Consequently its `X^{1/4}` bound pays the moment
\[
 \prod_{v\in S}\langle\xi_v\rangle^{1/18}:
 \qquad 2/18<1/4.
 \tag{20.2}
\]
For completeness, `⟨x_1+⋯+x_k⟩^{1/18}≤C_k∏_i⟨x_i⟩^{1/18}`. Apply this at each selected vertex; k≤7. The exponent charged to any factor is at most `2/18`. Remaining Fourier variables are integrated with weight one. The source small positive weight may also be retained on unmarked factors; it is not needed by the residual estimates.

**Proposition 20.1 (residual occurrence gain).** Both the crude ladder bound and the fine coefficient/counting bound of o75 Theorem 7.5′ acquire the factor `M₂^{−a/18}` for the residual selections, with additional analytic cost at most
\[
 L^{7(47d+2)a+4r},
 \tag{20.3}
\]
where r counts the residual pins and selections. Exceptional spectral-support restoration is counted separately in row 12 of o75. All unmarked ladder and bad-vine gains remain the same.

**Proof.** For each v split the parameter space into
\[
 \mathcal H_v=\{|\xi_v|\ge|\beta_v|/2\},\qquad
 \mathcal L_v=\{|\xi_v|<|\beta_v|/2\}.
\]
There are at most `2^a` choices of these regions.

On H_v, keep its time integration. The inequality
\[
 1\le C(\mu M_2)^{-1/18}\langle\xi_v\rangle^{1/18}
 \tag{20.4}
\]
extracts the desired occurrence gain, which (20.2) pays. Include v in E even though its time is still integrated. Proposition 18.1 allows exactly this case.

On L_v, the **total** frequency satisfies `|α_v|=|β_v+ξ_v|≥|β_v|/2`. Once the adjacent kernels have been Fourier expanded, its time dependence is the single exponential `e^{πiα_v t_v}`. Integrate this exponential over its full residual interval, partitioning by its maximizing child/floor. This gives its upper face minus its lower face, with the exact factor
\[
 (\pi i\alpha_v)^{-1},\qquad
 |(\pi\alpha_v)^{-1}|\le C(\mu M_2)^{-1}
                         \le C M_2^{-1/18}.
 \tag{20.5}
\]
The selected vertices belong to distinct original trees, so these integrations commute. The new face phases are precisely the total frequencies α_v at their recipients. Both β_v and ξ_v are fixed parameters during Proposition 18.1; a recipient's ξ is translated by α_v. Its mixed local-supremum bound is uniform in this translation. There is no estimate of `1/β_v` when α_v is small: that case was H_v and was paid by (20.4).

For the fine bound, apply Proposition 18.1 to each resulting face, and then the original counting bound. The original decoration equations, including the fixed values at E, are retained; contraction here concerns time variables only and does not contract the counted molecule. Recover the finitely many exceptional supports as in S Lemma 7.1. This is o75's already reserved row 12. This operation does not change any counting gain away from that reserve.

For the crude bound, selected atoms and child recipients belong to the protected split set, but a residual parent recipient need not: the protected raw parent may lie inside the nontrivial regular tree attached at the selected atom. Use instead o75 Revision 1, §4.8, whose E5-repaired kernel core is the time integral of the absolute value of the ladder decoration sum, with ordering restrictions dropped. At fixed external Fourier parameters, the added phase at a recipient and the face indicators do not depend on the ladder summation variables. Indeed α_v depends only on the bonds at the selected atom v, which are ladder-boundary data, even when its residual parent is internal to the ladder. These factors therefore come outside the absolute value of the ladder sum and have modulus at most one, so they can be discarded there. The same holds for the dichotomy indicator and, after the bound (20.5), its reciprocal. Apply the uniform kernel-core estimate and the upper-filter version of o75 §4.8; the remaining unit-length time integrations are bounded trivially. No retained ladder frequency is fixed or integrated absolutely inside its oscillatory sum.

There are at most seven strong regular factors per selected residual vertex, costing at most `L^{7(47d+2)a}` using local output extensions from (17.2); using this bound also for ordinary factors overcounts their cost. The fine coefficient costs `L^{4r}`. All face and dichotomy choices have a base depending on P and fixed cutoffs only. Equations (20.4)–(20.5), followed by μ≥1, give the product occurrence gain on both bounds. Their interpolation therefore retains that entire product. ∎

Proposition 20.1 discharges **o75 Revision 1, row 13 and §11.6**, at skeleton/residual selected vertices: it supplies M₂^{−1/18} per occurrence on both bounds before interpolation. Its valid variant uses the total-frequency reciprocal on L_v and the Fourier moment on H_v; no ledger entry needs the additional raw-reciprocal factor (cδL^{2γ})^{−1}. Inside regular objects the raw reciprocals remain in the signed collection of (17.3), as in o82 Revision 1, Theorem 18.2.

This is an exact rearrangement of the original annular integrand. It does not claim that its Fourier-level faces equal the individual raw faces of S Lemma 9.1 term by term. The sum equals the same original integral. The raw individual-face assertions, which are needed independently for Addendum 4, are Proposition 19.2.

## 21. Sufficient restricted marked-object theorem

**Theorem 7.3′ (unexcised protected-object variant).** Use o63 Theorem 6.3′, o75 Revision 1, Theorem 7.5′, and the weighted ordinary-kernel inputs of o82 Revision 1, with the protected set Π of o75 and `b=|Π|≤26P`. Use profiles (16.1). Every regular object meeting an original stem has the geometry of Proposition 3.1. On these objects and on the corresponding residual garden the following assertions hold simultaneously.

1. Terminal pins have the actual consumed `X^η` estimates (17.2) and its sharper η version. Top and parent (upper) faces are estimated **after summing over their maximizer cells**; stem-child and side-child lower faces are estimated **per cell**, by Proposition 19.2. These bounds use neither a selected reciprocal nor an M₂ assumption; they do not assert bounds for individual upper-cell contributions. The original stem floor face is empty. The off-stem pinned child face F_ch in (19.6) is included. Pattern top and lower faces and F_ch also have the centered positive time-Fourier representations (P1)–(P8) of o104, with the explicit boundary phases.
2. After ordinary layered side kernels have been integrated, the protected single-layer chain has the original-coordinate representation (19.3), the pointwise-in-Λ spectral derivative estimates (19.4) and amplitude bound (19.4a), and at most two exceptional linked coordinates per pin/face incidence. The separate-object F_ch case (P8) instead uses the root-trace representation (19.1); no single-layer hypothesis is imposed on that object. The consumed time weight on that protected coefficient is one. Its phases are passed exactly to the residual coefficient or evaluated at fixed external times. Ordinary unmarked coherent coefficients retain all their source derivative orders and both source time/spectral weights; their principal approximations and cancellation identities are unchanged. No principal approximation is used on a protected coefficient.
3. Residual pins and individual endpoint faces satisfy the mixed **local-supremum** estimate (18.3), with their exceptional coordinates fixed. This includes the coincident pinned-vertex configurations dParent and dChild with the designated strict inequality removed. The same holds when an exceptional coordinate still has its time integration.
4. For M₂-selected occurrences in regular objects use the exact signed collection estimate (17.3); for those in the residual garden use Proposition 20.1. Together they give `M₂^{−1/18}` per occurrence, hence `M₂^{−P/9}` for the 2P selections. Occurrences are counted separately if linked frequencies repeat. No gain is inferred for an isolated raw face without its reciprocal.
5. Beyond the exceptional-support costs already in o75 row 12, the total additional cost of these analytic replacements is bounded by
\[
 C_{P,\chi}^{n+1}C_{P,\delta}L^{400d b}
 \le C_{P,\chi}^{n+1}C_{P,\delta}L^{10400dP}.
 \tag{21.1}
\]
The exponential base is independent of δ. The exponent supplied to Addendum 3 is explicitly
\[
 \boxed{c=10400d\le19000d^3.}
 \tag{21.2}
\]
In o75's *per-incidence* notation this is `c_{7.3}=400d`, not 10400d.
6. **Gain retention.** All incoherency units of every protected regular object are retained in the final estimates. In the intermediate coefficient construction at most two units per pin/face incidence are removed into exceptional links, and their restoration is paid by `L^e` in (19.8). In particular this is stronger than the permitted loss of ten units per protected incidence. Every unmarked bad-vine, ordinary incoherency and retained ladder gain is the one used in o75; no entire protected regular object is estimated trivially in its order.

**Proof of sufficiency and the cost.** The exact kernel identities in §§13 and 19 justify the changed regular reduction. Their ordinary components have arbitrary layer assignments; only the remaining stem chain has been translated to a single unit layer. This is where the restricted geometry is used. The division of labour with o82 is now noncircular: its ordinary filtered-kernel and independent-box theorems are inputs, and §19 supplies the protected coefficient to which its discrete theorem applies. Its conditional marked-interface Theorem 13.1 is not used to infer an unproved interface.

In the reduction T1956–1974 insert these regular-kernel Fourier representations. Protected factors lie outside unmarked spliced-vine interiors. The ordinary source weighted bounds are kept there. The protected phase translations are legitimate by §16 and Proposition 18.1; the selected residual moments are accounted for by (20.2). Apply o75's retained-ladder estimate to the crude bound and its counting estimate with Proposition 18.1 to the fine bound. Proposition 20.1 gives the same residual occurrence gain on both bounds. Selected regular kernels already carry their occurrence gains. Thus all the factors multiply before the final interpolation, which does not reduce the occurrence powers. The rest of o75's aggregate argument is unchanged. Finally apply o63's exact common-profile extrapolation to supply the external decay and M₁ gain, at zero L cost.

Here is an explicit allocation of (21.1). Let `r_reg` count pins and selections internal to regular objects, and let `r_res=b_res+a_res` count residual pins and selections. They obey `r_reg+r_res≤b`. Any extra individual pattern face is counted as its additional protected incidence. The regular occurrence bound and the individual-face bound cost at most `L^{(47d+6)r_reg}`; this covers (17.3), (19.7), and any finite-output conversion once per nonempty object. The extra strong factors adjacent to residual selections number at most `7a_res` and cost at most `L^{7(47d+2)a_res}`. The residual coefficient costs `L^{4r_res}`. Even allowing all these costs together,
\[
 (47d+6)r_{\rm reg}
 +7(47d+2)a_{\rm res}+4r_{\rm res}
 \le(329d+18)b\le347db<400db.
 \tag{21.3}
\]
The unused margin covers using the weaker of the displayed endpoint bounds when an object has overlapping marks; it is not a reserve for an unproved estimate. Exceptional pairs in (19.8) have already been summed as spatial tuples and are included in its `6r` charge. No additional spectral-volume factor for those pairs is necessary. Keeping the original o75 row 12 for them as well only overcounts. For residual atoms, row 12 is used exactly as stated.

Factors polynomial in the order, including `(n+1)^{4r}` in (18.5), are bounded by `C_P^{n+1}` with P fixed before δ. Fixed numbers of marked endpoint choices are treated in the same way. All ordinary components contribute their `(C₁δ)^{m_i}` factors. An exceptional pair has two branching normalizations and contributes an extra δ rather than an inverse power of δ, as shown in (19.8). The profile constants in (16.1), the cutoffs and C_κ are chosen before δ. Therefore no `C₂^n`, `C_δ^n`, or `L^{Cn}` is hidden in (21.1). ∎

**Derivative patterns and †.** Theorem 7.3′ includes the individual R1 faces requested in Addendum 4. For dRoot, dParent and dChild use the exact cuts (P1)–(P8), (19.1), and the residual statement (18.3); an extra pattern pin adds at most one exceptional link, and the local output extension is charged only once per object. Boundary phases in (P2), (P7), (P8) involve only the fixed external times, so they are evaluated after fixing the exceptional spatial tuples. The † operation fixes the sibling momenta and removes that explicitly recorded external phase, as o104 Lemma 3.3 and §8 specify. Restricting the exceptional tuple sum cannot increase the absolute bound used here. One need not obtain M₂ occurrence gains for the nonplain derivative patterns. Their ordinary upper filters are still admitted. With the enlarged protected count `b≤30P`, the analytic cost here is at most `L^{12000dP}`, and o104's separate pattern overhead is included in the doubled-budget check below.

## 22. Numerical ledger and verification

This ledger supersedes the conditional rows in §§8–10. It records the consumed norm, not merely the norm before a boundary phase is restored.

| Item | Proved estimate or numerical charge | Proof/input |
|---|---:|---|
| Ordinary incoherent/coherent components; upper filters | no new positive L power in the ordinary `X^η` bound | o82 Prop. 15.1 |
| Strong ordinary time norm at a selected residual boundary | `L^{4d}` at fixed output; safely `L^{47d+2}` locally | (17.1)–(17.2) |
| Terminal pin | `L²` fixed output, `L^{31d+2}` locally in `X^η` | §13; o82 Cor. 15.2 |
| Strong terminal-pin norm | `L^{16d+2}` fixed output; `L^{47d+2}` locally | (17.2) |
| Reunited upper face or per-cell lower face, no selected reciprocal | `L^{(31d+6)r}` locally in the consumed norm | Prop. 19.2 |
| F_ch, including coincident pin | included in the preceding row, one additional exception | (19.1), (19.6); Prop. 18.1 |
| General regular selected-occurrence collection | `L^{(47d+5)r}M₂^{−a/18}` | (17.3) |
| Residual mixed box suprema, including faces | `L^{4r}` | (18.3) |
| Selected residual vertices, including frequency cancellation | `L^{7(47d+2)a+4r}M₂^{−a/18}` | Prop. 20.1 |
| Exception sum for a regular linked pair | `L²` per pair, plus at most `L` to restore its incoherency | (19.8) |
| Restoring residual exceptional spectral supports | o75 row 12: `L^{(24d+0.01)P}` | S Lemma 7.1; no local-supremum shortcut |
| Entire o73 analytic charge | `L^{400db}≤L^{10400dP}` | (21.3) |
| Incoherency units lost finally on protected regular objects | **0**; at most two intermediate units per incidence, already repaid | Prop. 19.2; Theorem 7.3′(6) |
| Section-6 marks/frontier differentiation | **0**, absent in this variant | o63 Thm. 6.3′ |

With o75's notation, its aggregate coefficient becomes
\[
 B=9384d+416.01+26(400d+c_{8.2})
   =19784d+416.01+26c_{8.2}.
 \tag{22.1}
\]
Even at that packet's generous per-incidence ceiling `c_{8.2}=19000d³`,
\[
 B+80d+1/9+3
 \le494000d^3+19864d+419.122\ldots<10^6d^3
 \quad(d\ge1).
 \tag{22.2}
\]
The actual setting has d≥3. In the doubled allowance, substituting `c_{7.3}=400d` into o75's derivative ledger gives at most
\[
 570000d^3+22936d+483.2.
\]
Adding even an additional `300d` for o104's stated pattern overhead, plus the same harmless end reserves, remains strictly below `2·10^6d³` for d≥1. Thus both the user's total-P contract and the receiving packet's per-incidence ledger are satisfied; the two conventions have not been conflated.

**Proof-check boundaries.** The original continuation checked source formulas and quantifier order and included a self-review. It did not itself provide an independent referee audit or a Lean verification. The subsequent independent REFEREE-73 report and the fixes applied in response are recorded in §23; no Lean verification is claimed. No source file outside this packet was edited, and no build or mutating git command was run. The stronger, unused raw layered coefficient theorem with every original spectral variable and every source positive weight is not claimed. The theorem proved here is the explicit sufficient variant: ordinary sides are integrated first, protected coefficients have the consumed weight one, individual faces are included, and selected-occurrence gains use the specified collections or the residual dichotomy. The reduction in §21 is the reason that weaker protected norm suffices.


### Final checks and current dependency status

The latest o82 report at the hash recorded in §16 now ends `CLOSED WITH VARIANT`, with its actual per-incidence charge `c_{8.2}=47d+5`. Substitution in (22.1) gives the sharper aggregate
\[
 B=21006d+546.01,
 \qquad B+80d+1/9+3<10^6d^3.
 \tag{22.3}
\]
The doubled derivative calculation, including an extra `300d` from o104, gives `24646d+633.2` before the harmless end reserves, also strictly below its allowance. The ceiling calculation (22.2) remains valid independently of this improvement.

The explicit proof dependencies are:

| New conclusion | Inputs actually used |
|---|---|
| Protected terminal and selected regular kernels, §17 | proved §§12–13; o82 §§14–18 |
| Residual mixed box supremum, §18 | T2003–2037, with the changed X/Y sets and the dephased box inequality explicitly retained |
| Root trace and F_ch, §19.1 | o104 Prop. 7.4 and (P1)–(P8), with the port lower-bound and explicit-phase conventions stated here |
| Punctured chain coefficient, §19.2 | D21 955–1152; ordinary side-kernel norms; the reduced-chain version of T995–1017 |
| Face kernels, §19.3 | Lemma 19.1 and o82 Revision 1, Theorem 10.1, at fixed (E,Λ) and weight one; (P8) uses (19.1) directly |
| Residual selection, §20 | strong adjacent-factor norms, Prop. 18.1, and o75's protected ladder split/counting estimates |
| Sufficient assembly, §21 | the preceding estimates, o75 Theorem 7.5′, and o63 Theorem 6.3′ |

The original self-review specifically checked the cases of a top-face pure phase, a linked root/terminal double pin, an off-stem child trace with an incoherent root link, and a residual selected frequency canceled by a large adjacent Fourier frequency. The first two phases are evaluated only at fixed external times or passed through a weight-one consumer; the third loses at most one intermediate gain unit and repays it; the last uses (20.4), never the invalid lower bound on the total frequency. The paired-tree port restriction in §19.1 prevents integration of an extension outside its defining triangle. All available-frequency suprema use the dephased box inequality before integration.

Mechanical checks found equal numbers of opening and closing display brackets, no accidental control bytes, and exactly one final STATUS line. The exponent inequalities were checked with rational arithmetic at d=1,3,10; for every d≥1 they follow directly from `d³≥d` and the displayed positive margins. These checks validate bookkeeping, not an independent certification of the proof.

The initial OPEN descriptions and “Not established” rows in §§1–15 are retained as the requested history. They are superseded for the unexcised flower geometry by Theorem 7.3′ and the numerical ledger above. The stronger unused raw-layered formulation is not asserted. There is no remaining OPEN sub-item in this packet's sufficient variant; other packets' separately stated hypotheses, such as their ladder inputs, are not re-proved here.


## 23. Revision 1 following REFEREE-73

This revision applies all nine o73 fixes requested in REVISE.md. The independent [REFEREE-73 report](../ref/REFEREE-73.md) records **0 FAIL** and Theorem 7.3′ **PASS AFTER FIX**; none of its fixes changes an exponent. The refereed o73 version had SHA-256 `683351431762e5dd0ebff1b84daeb5d623b0ab45ca39807bb7fc90d39a58f7bf`. The report used for this revision has SHA-256 `6b4b64eb1d8467859ba5c21d2312eb45363241a1bfc2459836cd5d8a6c37fd2d`. This section records application of that report, not a claim of a second independent review of the revised text.

| Fix | In-place revision |
|---|---|
| **73-F2** | Proposition 13.2, (17.1), the proof of (17.2), and §20 now retain side-couple output decay or trivial-side profile decay when summing exceptional and adjacent unit-box centres. Equation (17.1) cites o82 Revision 1, Lemma 16.1, as `X^{1/4,30d,30d}` for couples and `X^{1/4,30d,0}` for trees. The previous, larger L charges remain valid overestimates. |
| **73-REC** | The crude-bound proof of Proposition 20.1 no longer puts every residual parent recipient in the protected split set. It uses o75 Revision 1's kernel core: the absolute value is inside the time integral, and the added phase and indicators are independent of the ladder summation variables. |
| **73-UF** | Proposition 19.2 and Theorem 7.3′(1) take top/parent upper faces summed over their maximizer cells; lower faces remain per cell. The proof reunites the upper-cell indicators before evaluating side couples. No individual upper-cell bound is claimed. |
| **73-P8** | The separate-object F_ch case uses the root-trace representation (19.1) directly, not the single-layer-chain representation (19.3). Its one exceptional link has the same already charged normalization and gain-restoration costs. |
| **73-L19** | Equation (19.4) is pointwise in Λ, with derivative-independent coefficient factor B_κ(Λ); (19.4a) bounds the weighted spatial amplitude mass D_E(Λ). The discrete theorem is applied at fixed (E,Λ), then Λ is integrated. A fixed smooth Gevrey output cutoff turns the possible line measure into a Fourier density. |
| **73-RT** | The traced root in (19.1) is explicitly in layer p; R_B may depend on a third boundary time, included in its Fourier norm. The corrected port lower bound and explicit boundary phase remain in force. |
| **73-E1** | Proposition 18.1 explicitly allows a bounded number of pins per tree, including two coincident pins, as well as at most one selected endpoint substitution per tree. All pins are counted in r. |
| **73-PIN** | Section 16 now pins and cites o75 Revision 1 and o82 Revision 1. Section 20 explicitly identifies Proposition 20.1 as the consumer satisfying o75 Revision 1's row 13/§11.6 obligation at skeleton/residual selected vertices. |
| **73-C** | Section 19 contains the complete 64-digit o104 hash; the pole-restoration citation is D21 1142–1146. |

The receiving contract is explicit: inside regular objects, (17.3) keeps the raw reciprocals in the signed collection; at skeleton/residual selected vertices, Proposition 20.1 supplies `M₂^{−1/18}` per occurrence on both bounds using the total-frequency reciprocal or the Fourier moment. The referee's corresponding wording fixes in o75/o82 (73-W) belong to those packets; this revision edits only o73.

**Concurrent dependency revisions.** During final verification, the three live dependency files changed. The §16 and §19 hashes deliberately identify the versions read for the proofs and referee fixes, rather than silently relabeling them as the later versions. The later revisions were read and record compatible corrections:

| Later version observed | SHA-256 | Relevant change |
|---|---|---|
| o75 Revision 2, §12 | `47513e351d6a3e0b2dc2bef465e9278e880812f4ab3fa9ad69a6a3528587c96d` | Applies 73-W and confirms the kernel-core argument for a parent recipient inside a ladder. |
| o82 Revision 1 addendum, §22.1 | `3c39999c44a733980f99782a72ec593e5e4d61aa197ab2441af1dc956a099eff` | Applies 73-W and cites Proposition 20.1 for skeleton/residual selections. |
| o104 Revision 1, §13 | `2d711cbdd4c38275cbc1a6b3659eab9183b414e428bd6bdc561cbd2a05b2c5f2` | Adopts the port-domain and explicit-phase conventions and closes its pattern-specific item using Theorem 7.3′. |

The later o104 budget distinguishes its `300d` local pin overhead from the full pattern increment, which also includes the additional protected-incidence costs. Those incidence costs are already present in our doubled ledger with `b≤30P`; the additional `300d` in §22 remains an overcount, not an assertion that the full increment is only `300d`. Thus neither doubled-budget calculation changes.


The theorem's constants and final ledger are unchanged: `c_{7.3}=400d` per protected incidence, total `10400dP`, zero final lost incoherency units, and the same doubled derivative allowance. Verification checked all nine requested entries against the in-place statements, the revised dependency hashes, the unique final STATUS line, display delimiters, equation labels, and the absence of control bytes. No Lean build, source mutation outside this packet, or mutating git operation was performed.

STATUS: CLOSED WITH VARIANT (Revision 1, §23, applies all REFEREE-73 fixes; Theorem 7.3′, §21, uses reunited top/parent faces and per-cell lower faces, includes dChild F_ch, and supplies the residual selected-vertex gain via Proposition 20.1; c_{7.3}=400d per protected incidence, total c=10400d≤19000d³, zero final lost incoherency units; all exponents and both budgets unchanged).
