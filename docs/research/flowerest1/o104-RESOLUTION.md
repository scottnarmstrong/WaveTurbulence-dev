# o104 — OPEN 10.4: the derivative patterns and the † variant of the frozen flower statement

Packet o104 (FLOWER-OPEN), for wt-orch, 2026-11-07. Binding: COMMON.md, o104/BRIEF.md.

## 0. Result

> **Revision 1 (§13, after REFEREE-73).** Fixes Prop. 7.4(a) with the port convention and makes (7.2) state the centred bound, with phases recorded and consumed. Sub-item 10.4.C is absorbed by o73 Theorem 7.3′. The doubled budget is checked against the receiving ledger. **STATUS is now CLOSED.** Where §13 conflicts with the text below, §13 governs.

**What the patterns are (§3, exact, from the frozen definitions).**

- Each non-plain pattern adds **one** time pin per tree: the root at `t` (`dRoot`), the flower's grandparent `π_j` at
  `s` (`dParent`), or a branching layer-`p` sibling `m_{j,i}` of the flower at `s` (`dChild i`).
- The last two pins coincide with the existing pin of the flower parent at `s`. The order constraint between the two
  designated vertices is dropped.
- No pattern adds a momentum Dirac factor, changes a profile, a pairing, or a cutoff weight.
- By Lemma 3.2 these are exactly the boundary terms of `∂_t` and `∂_s` (T2312, T2331).
- `†` adds no pin. It fixes the momenta on the two edges from `φ_j` to the flower's siblings (both endpoints basic
  protected vertices) and removes the phase of `φ_j`. On the support that phase is a unimodular constant on each of
  `≤ 3^{2P}` flower-position classes (Lemma 3.3).

**What is proved.**

- **`M₁` and external decay.** o63 Theorem 6.3′ applies to every pattern and to `†` verbatim, at zero `L`-cost (§4.1).
- **Remainders.** Covered by o102 §8.4 (§4.2).
- **`†`.** It costs no power of `L` (Prop. 8.1) and keeps the `M₂` gain on all-plain vectors (§4.3).
- **dRoot and dParent.** By Lemmas 6.1–6.2, these are, exactly, individual faces of S-L 9.1 (the top face at the
  root; the lower face at the grandparent, on the piece where the flower parent is the maximizing child). Their time
  structure is therefore among the faces for which OPEN 7.3 requires its estimate.
- **dChild.** By Lemma 6.3, `dChild` is a face at an **off-stem** vertex whose upper endpoint is the **pinned**
  time `s` (the pinned child face `F_ch`). It is not on OPEN 7.3's list.
- **§7.** Every pattern pin, in every geometry, is handled by the mechanism of the terminal flower-parent pin: exact
  cut at the linked partner, consumed modulation, or a pinned residual atom. The new ingredients are proved here: the
  mirror operator `T'_A`, the diagonal and fixed-interval operators (Lemma 7.1), and a **root-trace proposition** for
  ordinary regular objects (Prop. 7.4, which also answers o73 §15's norm-only obstruction for actual side couples,
  Remark 7.5).
  - Each pattern pin adds at most one exceptional linked coordinate, loses no power of any resonance, and creates
    boundary phases only in `t, s`.
  - At the time-Fourier level (the level of o73 Prop. 13.2) all patterns, including `F_ch`, are proved here (Prop. 7.6).
- **Budget.** The patterns cost at most `L^{300dP}`, within the extra `L^{(100d)^3P}` of the doubled allowance. `†`
  and all-plain vectors cost `L^0` (§10).

**The exact statement proved: Theorem 10.4 (§9).** Assume:

- (H1) the plain machinery that gives o63 (5.1) with S(10.4);
- (H2) OPEN 7.3 for the pin set `Π_pat = {φ_j} ∪ {pattern pins}`, pin by pin;
- (H3) OPEN 7.5 with `π_j` added to the protected list for `dParent` trees, in boundary form.

Then, for every `pat : Fin(2P) → FixPat`, every `dagger`, and every `cut1, cut2` allowed by the frozen side condition,

`‖flowerSumP‖ ≤ ⟨k−ζk'⟩^{−4ΛP} L^{c(pat)(100d)^3P} δ^{2νN} · M₁^{−80dP}[cut1] · M₂^{−P/9}[cut2, all plain]`,

with `c(pat) = 1` for all-plain vectors (with or without `†`) and `2` otherwise, and with all unmarked gains retained.
This covers the three inputs of `layergardenFlower_v3_of_three`. For vectors without `dChild`, (H2) is OPEN 7.3 as
stated, with its S-L 9.1 faces read individually.

**Pattern-specific OPEN sub-item (§12).** OPEN 10.4.C: the pinned child face `F_ch` of `dChild` must be added to
OPEN 7.3's pin/face list.

- It is proved here at the time-Fourier level.
- At the coefficient level and in the residual molecule, its obligations are verbatim those of the flower-parent pin.
- Three statement-level readings are recorded as (R1)–(R3); they add no new mathematics.

---

## 1. Pinned inputs

SHA-256 checked at first read; drafts of other packets were copied at first read and are cited by hash.

| Abbrev. | File | SHA-256 |
|---|---|---|
| S | <scratch>/flower-open/SUPPLEMENT-v1.md | `ddd81fe1238e7c51379a69981b4d10aa68690ced46d0fc1b115200fc0c3774d7` |
| T | <sources>/paper/source/WKE-Longer_times_Final_arXiv.tex | `493eef6b7dec448bc5f9f1c3974c0cad7a85eca9bc428f5b35e968aad76727cb` |
| D21 | <sources>/references/src-2104.11204/Inventiones-Final_Version.tex | `50d0e236a2df0cfd2b98bace6f0256043ee88fc05079ee44c3524ca9482fe402` |
| D23 | <sources>/references/src-2301.07063/Revision_Submit.tex | `c7e47dfabf5a4cca6e3ad0399fc377f2809c12f58e1563640407fe0992335475` |
| COMMON | flower-open/COMMON.md | `a165bad5bed0600d51c0495d1db27cc8d15dcedfeba0de53d7bafb22ce38a5ac` |
| BRIEF | flower-open/o104/BRIEF.md | `a9d4847ab4ddfd022dff2ccf132e83f05ba021e4e9cce98d8230dce3f9301948` |
| REF | flower-open/ref/REFEREE.md (item M4, lines 175–181) | `c31ee38a03ddace8d565828f7f467008ee16c64cb6803ba0e70fd539e4d88d6d` |
| o63 | flower-open/o63/RESOLUTION.md (Theorem 6.3′, Prop. 10.3′) | `c28aad09eb865b13645a1e88bbf74cc6c33efeebd2baa18a5893b887b2ee7ad9` |
| o102 | flower-open/o102/RESOLUTION.md (Theorem R, §8.4) | `772bac47097eb4c307b0df4993007857df23c5594a9949e5e03d6cfce4a555ab` |
| o73 | flower-open/o73/RESOLUTION.md (live; read at this hash; §§3, 4, 12–15) | `eb26e89a5ace5c4ad4f9a7391e94aee0604bd59b2f38ea909f3976d48370b928` |
| HANDOFF | <scratch>/port-ft1/HANDOFF.md ("The three inputs, exact text") | `e6b9987af7e85244aed68ae4c5013bb14f2dde26f23ee0acab2946a50eaf663a` |

Frozen Lean definitions: main checkout <repo> at `89e2e136` (the frozen tree is identical to
`7e34a835`; `git diff --stat` on `WaveTurbulence/Frozen` is empty). "F:File:n" means
`WaveTurbulence/Frozen/Defs/File.lean`, line n. The three inputs are read in the port worktree
<worktrees>/port-ft1 at `e2ec222b` (text-identical to HANDOFF).

"T n" is a line of T, "S n" a line of S, "S-L x.y" a lemma of S, "S(x.y)" a display of S. o73 is still OPEN; I use
only results it states as proved (its Prop. 3.1, Prop. 4.1, Lemma 12.1, Lemma 12.2, Prop. 13.1, Prop. 13.2,
Prop. 14.1), and I say so at each use.

No Lean build, no git write, no edit outside this file.

---

## 2. The exact target

### 2.1 Frozen objects

- `FixPat` (F:FixPat:30–34): `plain | dRoot | dParent | dChild (i : Fin 3)`.
- `fixPat pat t s` (F:LayeredGardenFixPat:41–50): flower parents ↦ `s`; in tree `j`, according to `pat j`: nothing;
  the root ↦ `t`; the parent of `𝔣^pr` ↦ `s`; the `i`-th child of `𝔣^pr` (a branching node) ↦ `s`.
- `PatValid p j` (F:LayeredGardenPatValid:43–48): `dRoot` needs root ≠ `𝔣^pr`; `dParent` needs `𝔣^pr` ≠ root;
  `dChild i` needs the `i`-th child of `𝔣^pr` to be a branching node of layer `p`.
- `kDomainFix` (F:KDomainFix:40–44): free nodes keep `𝔏<τ<𝔏+1`, `0<τ<up`; a parent–child order constraint is kept
  iff at least one of the two is free (constraints between two designated nodes are dropped).
- `kernelKgen` (F:KernelKgen:54–66): `(coupling)^n ζ(𝒢) Σ_κ ε_κ·wt(k)·∫_{free τ} 1_{kDomainFix}·phaseProdOff·∏ F`.
- `phaseProdOff` (F:PhaseProdOff:39–43): the phase `exp(iπσ_bδL^{2γ}Ω_b τ_b)` omitted for `b ∈ off`.
- `sibWeight c` (F:LayeredGardenSibWeight:44–48): `∏_{b=𝔣^pr} ∏_{i: child i not the flower} 1[k(child i) = c_{j(b),i}]`.
- `flowerSumP` (F:FlowerSumP:68–82): `kernelKgen` with `fix = fixPat pat t s`, `off = {𝔣^pr}` iff `dagger.isSome`,
  `wt = cutWeight1P^{cut1}·cutWeight2P^{cut2}·sibWeight^{dagger}`, `up ≡ t`, `k₀ = 0`, roots `n`, flowers `n'`; the
  garden sum carries `∀ j, PatValid p j (pat j)`.
- Decorations: `κ_𝔫 = κ_{𝔫₁}−κ_{𝔫₂}+κ_{𝔫₃}` (F:IsDecoration), `Ω = |k₁|²−|k₂|²+|k₃|²−|k|²` (F:ResFactor; T647).

### 2.2 The frozen bound and the three inputs

`layergardenFlower_v3` (Frozen/Theorems/LayergardenFlowerV3.lean:93–106) requires, for every pattern vector `pat`,
every `dagger`, and `cut1, cut2` with `cut2 ≠ none ⇒ cut1 = some j₁, (2^{j₁}L)^{10} ≤ |k|`:

$$
\|\mathrm{flowerSumP}\|\le\langle k-\zeta k'\rangle^{-4\Lambda P}L^{c(\mathrm{pat})(100d)^3P}\delta^{2\nu N}
\cdot M_1^{-80dP}[\text{if }cut1]\cdot M_2^{-P/9}[\text{if }cut2\text{ and all plain}],
\tag{2.1}
$$

with `c(pat) = 1` if every `pat j = plain` and `c(pat) = 2` otherwise. The `M₂` factor is required for all-plain
vectors **with or without** `†`, and then with the single allowance. The three inputs of
`layergardenFlower_v3_of_three` (HANDOFF 99–174) quantify over the same `pat`, `dagger`:

1. `FC23UniformCut1At`: the profile-family bound with budget
   `⟨k−ζk'⟩^{−4ΛP}·L^{c(pat)(100d)³P − 80dP − 2P}·δ^{8νN}`, uniformly over the FC23 endpoint-profile family;
2. `PositiveCut2At (1/9)`: (2.1) with `cut2 = some j₂`, `j₂ > 0`;
3. `FlowerCaseAt CaseCut2Zero`: (2.1) with `cut2 = some 0`.

The couple clause of the frozen gate (including the root-pinned `∂_t a^tr` of T2312) is not among the three inputs: it
is discharged on main by `coupleHalf_of_spine` (port-ft1 FlowerTop/FinalFamily.lean:23, 39). It is therefore outside
this packet. The `dRoot` analysis of §§6–7 applies to it verbatim (it is a single tree with the root pinned at `t`).

### 2.3 The statement of OPEN 10.4

**OPEN 10.4 (derivative patterns and †).** Under the hypotheses that prove S(1.1) for plain kernels (S Prop. 10.3 as
modified by o63 Prop. 10.3′ and o102 Theorem R), prove, for every `pat : Fin(2P) → FixPat` and every `dagger`:

- the order-`n` gain-free family bound o63 (5.1) for the pattern integrand `Θ_pat`, with exponent
  `B + β_pat`, where `B + 80d + 1/9 + 3 ≤ (100d)^3` is the plain exponent of S(10.4) and
  `β_pat ≤ (100d)^3` if some `pat j ≠ plain`, `β_pat = 0` if all `pat j = plain`;
- the factor `G₂ = M₂^{−P/9}` in (5.1) whenever all `pat j = plain` (with or without `†`);
- with all the gains of unmarked objects retained.

Then o63 Theorem 6.3′ and S Prop. 10.3 give (2.1); o102 Theorem R (§8.4) gives the remainders.

---

## 3. What each pattern adds

Fix a garden `LG` in the sum and a tree `j`. Write `r_j` for its root, `𝔣_j` for the flower, `φ_j := 𝔣_j^{pr}`,
`π_j` for the parent of `φ_j` (if `φ_j ≠ r_j`), and `m_{j,i}` (`i ∈ Fin 3`, `i ≠ ι_j`) for the children of `φ_j`
other than the flower; `ι_j ∈ {0,1,2}` is the position of the flower under `φ_j`. Put
`ω_𝔫 = πσ_𝔫δL^{2γ}Ω_𝔫`.

### Lemma 3.1 (anatomy of a pattern)

For each tree `j`, relative to the plain kernel, the pattern `pat j` changes the integrand of `kernelKgen` exactly as
follows, and in no other way.

| `pat j` | valid iff | designated node `v_j` | pinned time | removed integration | order constraints after the drop | phase at `v_j` |
|---|---|---|---|---|---|---|
| `plain` | always | — | — | — | — | — |
| `dRoot` | `r_j ≠ φ_j` | `r_j` | `t` | `τ_{r_j}` | free children of `r_j` below `t` | `e^{iω_{r_j}t}` |
| `dParent` | `φ_j ≠ r_j` | `π_j` | `s` | `τ_{π_j}` | other children of `π_j` below `s`; parent of `π_j` above `s`; `φ_j<π_j` dropped | `e^{iω_{π_j}s}` |
| `dChild i` | `m_{j,i}` branching, layer `p` | `m_{j,i}` | `s` | `τ_{m_{j,i}}` | children of `m_{j,i}` below `s`; `m_{j,i}<φ_j` dropped | `e^{iω_{m_{j,i}}s}` |

In particular: no pattern adds a momentum Dirac factor, changes an input profile `F_q`, changes a leaf pairing, or
changes the weights `cutWeight1P`, `cutWeight2P`; each non-plain pattern adds **exactly one** time Dirac factor
`δ(t_{v_j}−t)` or `δ(t_{v_j}−s)` per tree, at a node adjacent to the existing pin `φ_j` (`π_j`, `m_{j,i}`) or at the
root; and the pinned time of `π_j` or `m_{j,i}` coincides with the existing pinned time `s` of `φ_j`.

**Proof.** By F:LayeredGardenFixPat:41–50 the designated set is `{φ_j}_j ∪ {v_j : pat j ≠ plain}`, with the stated
values. For `dParent` the node `b` with `∃ c = 𝔣^pr, c.IsChildOf b` is `π_j` (one flower per tree). For `dChild i` the
node with path `c.path ++ [i]` is the `i`-th child of `φ_j`; it is a `GBranch` only if branching, and PatValid adds
layer `p` (F:LayeredGardenPatValid:47–48). By F:KDomainFix:40–44, removing `v_j` from the free set deletes its
integration, drops the constraint between `v_j` and the other designated node `φ_j` (for `dParent`, `dChild`) or `φ_j`
when `φ_j` is a child of `r_j` (for `dRoot`; then `s<t` holds anyway), and keeps every constraint between `v_j` and a
free node, with `τ_{v_j}` replaced by its value.

The designated node's own constraints `𝔏<τ<𝔏+1`, `0<τ<up` are dropped.

- For `π_j` and `m_{j,i}` they hold anyway: both are in layer `p` (stem vertices by `IsCanonH`; PatValid), and
  `s ∈ (p,p+1)`, `s < t`.
- For `r_j` the pinned value is the endpoint `t` of `τ_{r_j} < up = t`; this is the top face of Lemma 6.1.

`phaseProdOff` evaluates the phase of `v_j` at its value (F:KernelKgen:62–64, `extendFix`). The weight, `inputLeaves`
and the decoration set do not involve `fix`. ∎

Without the drop, `dParent` and `dChild` would carry the empty constraint `s<s`; the drop is what makes them the
boundary terms of Lemma 3.2.

### Lemma 3.2 (why these are the right objects: the `t,s` derivatives)

For a single tree `𝒯` (or any garden, one tree at a time), let `𝒥^{off}(t,s)` be the plain kernel with phases
removed at `off ⊂ {φ}`. Then, for `p<s<t<p+1`,

$$
\partial_t\mathcal J^{\varnothing}=\mathcal J^{\varnothing}_{\mathrm{dRoot}},\qquad
\partial_s\mathcal J^{\{\varphi\}}=-\mathcal J^{\{\varphi\}}_{\mathrm{dParent}}+\sum_{i}\mathcal J^{\{\varphi\}}_{\mathrm{dChild}\,i},
\tag{3.1}
$$

the sum over the positions `i` of branching layer-`p` children of `φ`, and each term is `0` when its pattern is not
valid. Without `†`, `∂_s` has the extra term `iω_φ 𝒥^∅`, which is not a `FixPat` object.

**Proof.** In the plain integrand `t` occurs only in `τ_b<t`; for a free `b ≠ r` this is implied by `τ_b<τ_r`. If
`r = φ` all free times are below `s<t` and `∂_t = 0`, matching PatValid. Otherwise differentiating the polytope
integral in the facet `τ_r = t` gives the integrand there, i.e. `dRoot` (the layer ceiling `p+1>t` is not active).
After the pin, `s` occurs in `τ_π>s`, in `τ_c<s` for free branching children `c` of `φ`, and in the phase of `φ`.
For `c` of layer `q<p`, `τ_c<q+1≤p<s` is not active. Differentiating the two kinds of facets gives `−dParent` and
`+dChild i`; with `φ ∈ off` the phase term is absent. ∎

This is T2312 ("an extra `δ(t_𝔯−t)` factor") and T2331 ("`δ(t_𝔫−s)` with `𝔫` the parent or a non-flower child of
`𝔣^pr`"), and it shows that PatValid's layer-`p` restriction for `dChild` is exact.

### Lemma 3.3 (the † variant: fixed sibling momenta and a constant phase)

Fix `c : Fin(2P) → Fin 3 → Mom d`. For `ι ∈ {0,1,2}^{2P}` let `flowerSumP^ι` be the garden sum restricted to the
gardens whose flower positions are `ι`. Then

$$
\mathrm{flowerSumP}(\mathrm{pat},\mathrm{some}\,c,\dots)=\sum_{\iota\in\{0,1,2\}^{2P}}u_\iota\;
\mathrm{flowerSumP}^{\iota}_{\mathrm{sib}}(\mathrm{pat},\dots),\qquad |u_\iota|=1,
\tag{3.2}
$$

where `flowerSumP^ι_sib` is the **non-†** kernel (`off = ∅`, all phases kept) with the extra weight `sibWeight c`, and
`u_ι = ∏_j exp(−iπσ_j(ι_j)δL^{2γ}Ω_j^♯(ι_j;c_j,n')s)` depends only on `(ι,c,n',ζ,s)`. If some `c_{j,i}` with
`i ≠ ι_j` is not a lattice point `L^{−1}ℤ^d`, the corresponding term is `0`.

**Proof.** On the support of `sibWeight c`, the children of `φ_j` carry the momenta `c_{j,i}` (`i ≠ ι_j`) and
`L^{−1}n'` (`i = ι_j`), so `k_{φ_j} = k_{φ_j,0} − k_{φ_j,1} + k_{φ_j,2}` (F:IsDecoration) and
`Ω_{φ_j} = resFactor(…)` are functions `Ω_j^♯(ι_j; c_j, n')`. The sign of `φ_j` is that of the flower
(`ζ·σ_{r_j}`, fixed by the garden condition in F:FlowerSumP:74) if `ι_j ∈ {0,2}` and its opposite if `ι_j = 1`. The
removed phase is `exp(iπσ_{φ_j}δL^{2γ}Ω_{φ_j}s)` because `τ_{φ_j} = s`. Hence, on the support,
`phaseProdOff_{\{φ\}} = u_ι · phaseProd`, garden by garden, with `u_ι` constant on the class `ι`. Decorations are
lattice-valued (`k₀ = 0`, F:CosetDecoration), so a non-lattice `c_{j,i}` gives `sibWeight = 0`. ∎

So `†` adds no pin and no time structure. It adds the indicators `1[k_e = c_e]` on the **edges `e = (φ_j, m_{j,i})`,
both of whose endpoints are basic protected vertices** (S 68: the flower parent and the two siblings), and it splits
the garden sum into `≤ 3^{2P}` flower-position classes, each multiplied by a unimodular constant.

### Summary: pins, Dirac factors, modified kernels

| Object | pins added (per tree) | Dirac factors | momentum constraints | modified kernels/profiles | phases |
|---|---|---|---|---|---|
| `plain` | 0 (only `φ_j ↦ s`, as in S-L 2.2) | `δ(t_φ−s)` | flower `= k'` | none | all |
| `dRoot` | 1: `r_j ↦ t` | `+δ(t_r−t)` | none new | none | root phase at `t` |
| `dParent` | 1: `π_j ↦ s` (coincident with `φ_j`) | `+δ(t_π−s)` | none new | none | `π_j` phase at `s` |
| `dChild i` | 1: `m_{j,i} ↦ s` (coincident with `φ_j`) | `+δ(t_m−s)` | none new | none | `m_{j,i}` phase at `s` |
| `†` | 0 | none | `k_{m_{j,i}} = c_{j,i}` at protected edges | none | `φ_j` phase removed = constant `u_ι` |

---

## 4. The gains that do not see the pattern

### 4.1 First cutoff and external decay: o63 Theorem 6.3′ verbatim

Let `Θ_pat` be the integrand of `flowerSumP(pat, dagger, cut1, cut2)` with the input profiles removed (o63 §1.1): the
normalization, `ζ(𝒢)`, `ε_κ`, the weight `W = cutWeight1P^{cut1}·cutWeight2P^{cut2}·sibWeight^{dagger}`, and the
integral over the free times of `1_{kDomainFix}·phaseProdOff`.

- `Θ_pat` is a bounded, profile-independent function of the decoration: `|W| ≤ 1`, and the free times range over a
  subset of a product of unit layer intervals, so the time integral has modulus `≤ 1` (Lemma 3.1 only removes
  integrations).
- If `cut1 = some j₁`, `j₁ ≥ 1`, then `Θ_pat = 0` unless every tree has a top leaf with `2^{j₁}L/4 < |k_a| < 2^{j₁}L`
  (support of `prodDyadicCut`, F:ProdDyadicCut:21–28; the top leaves of F:LayeredGardenIsTopLeaf are S's original
  frontier `B_j`). This is o63's (Hb′) with `c₋ = 1/4`, `c₊ = 1` (o63 Remark 2.1).

Hence o63 Theorem 6.3′ applies to `Θ_pat` with no change: the termwise identity o63 (2.1) holds for every pattern
vector and every `dagger`, and

$$
|S_{\Theta_{\rm pat}}[F]|\le(16c_\chi)^nC_{P,\delta}(1+n)^{(8\Lambda+80d)P}\,M_1^{-80dP}[cut1]\,
\langle k-\zeta k'\rangle^{-4\Lambda P}\,\mathcal B_{\Theta_{\rm pat}}(C_1).
\tag{4.1}
$$

Zero `L`-loss; the `M₁` factor is retained for every pattern, as (2.1) requires. o63 §7 states this; the two facts
above are what it uses. What remains is the gain-free, profile-uniform bound `𝓑_{Θ_pat}(C₁)` (o63 (5.1)).

### 4.2 Remainders: o102 §8.4

The frozen gate is the deterministic core (its deviation (D1)); the moment-expansion remainders belong to the consumer.
For the consumer, o102 §8.4 proves (R.1) for every pattern vector, with or without `†`, with `G ∈ {1, M₁^{−80dP}}` and
with the `M₂` factor whenever no vertex of `𝒮_j` is substituted. By Lemma 3.1 this includes all plain vectors (with
or without `†`) and also `dChild` (its designated vertex is off the stem). No part of the `L` budget is used.

### 4.3 The second cutoff for all-plain vectors, with or without †

For all-plain vectors (2.1) needs `M₂^{−P/9}` and only `L^{(100d)^3P}`. Without `†` this is the plain case. With `†`,
Lemma 3.3 writes the kernel as `Σ_ι u_ι·flowerSumP^ι_sib(plain)`. In each term:

- S-L 9.1 applies verbatim. Its proof (S585–594) uses only that the raw amplitude is time-independent apart from the
  phases, the order constraints and the fixed pins, and that a selected vertex is not a flower parent. `sibWeight` is
  time-independent; the selected `v_j ∈ 𝒮_j` are untouched; `φ_j ∉ 𝒮_j`.
- The selected reciprocals S(9.1), the faces (OPEN 7.3), the filters (OPEN 8.2, S-L 9.3, OPEN 8.3) and the gain (8.6)
  are produced exactly as without `†`. The only new factor is `sibWeight`, which acts on protected edges (§8).

So the `M₂` gain is retained for all-plain vectors with `†`, and `†` costs no power of `L` (§8): `β = 0`.

---

## 5. Protection and twist invariance

### Lemma 5.1

(a) The designated vertices `r_j` (dRoot) and `m_{j,i}` (dChild) are basic protected vertices (S68: the root and the
two flower siblings). `π_j` (dParent) is not (REF 177). Add `π_j` to the protected list for every tree with
`pat j = dParent`. This adds at most `2P` protected vertices and, by S-L 7.4, at most `4` crossing bonds each.

(b) Every LF twist used in the proof acts at a vine whose realization contains no protected vertex (T2297, and S68:
"an object containing a protected vertex remains protected when collapsed"). Such a twist leaves unchanged: the
designated vertices of Lemma 3.1, their parents and children, and the momenta on their incident bonds; the flower
positions `ι_j`; the momenta `k_{m_{j,i}}`; the validity `PatValid p j (pat j)`. Consequently `Θ_pat`, `sibWeight` and
each flower-position class of Lemma 3.3 are unions of the LF families that the plain proof sums over.

(c) The number of vines containing a protected vertex is less than `20P + 2P = 22P` (T2297 for the basic list, one
more per added `π_j`).

**Proof.** (a) is the definition of the S68 list together with S-L 7.4 (`q ≤ 4b`). For (b): an LF twist changes
the garden only inside the realization of the twisted vine, and the decoration only on bonds internal to it. A unit
twist exchanges `k_{𝔲₂}` and `k_{𝔲₂₃}` (T1447–1454, T1458; REF 132). The LF replacement families preserve layers and
orders (T1463–1487). Designated vertices, `φ_j` and the flower are protected, so they are outside every twisted vine.
Their positions, children and incident momenta are therefore unchanged, and so are `ι_j` and `k_{m_{j,i}}`.
`PatValid` refers only to these vertices and their layers. (c) is T2297's count plus one vine per added vertex. ∎

When `cut2 ≠ none`, the frozen side condition gives `|k| ≥ M₁^{10}`, and T2300 / S-L 9.2 show that the twists used do
not change the stem or its `Ω`. This is the same as in the plain case and does not depend on the pattern.

---

## 6. The pattern pins as faces of S-L 9.1

S-L 9.1 (S572–594) selects `v_j ∈ 𝒮_j` (the stem branching set without `φ_j`). It integrates `τ_{v_j}` over
`(A_{v_j}, B_{v_j})`, where:

- `B_v` is the parent time, or the external top time `t` at the root;
- `A_v` is the maximum of the layer floor and the times of the branching children of `v`;
- the domain is partitioned according to the maximizer.

Each face is the expression obtained by substituting `τ_{v_j}` by an endpoint, retaining the remaining inequalities,
and adding `ω_{v_j}` to the phase at that endpoint. It is multiplied by `±(iω_{v_j})^{−1}`. Below, "face expression"
means the expression **before** that factor. It is defined for every decoration, whether or not `|Ω_{v_j}| ≥ cM₂`.

### Lemma 6.1 (dRoot is the top face at the root)

Let `pat j = dRoot`, so `r_j ≠ φ_j` and `r_j ∈ 𝒮_j`. The top-face expression of S-L 9.1 at `v_j = r_j` equals the
`dRoot` expression of Lemma 3.1, pointwise in the decoration and in the remaining times. This holds summed over the
`≤ 4` pieces of the partition, and also piece by piece.

**Proof.** At the root `B_r = t`; the layer ceiling is redundant on the layer-`p` stem (S585). The top face sets
`τ_r = t`, gives the phase `e^{iω_r t}`, and retains `A_r < t`. The constraint `A_r < t` says that the branching
children of `r` lie below `t` and that `p < t`. This is exactly the dRoot row of Lemma 3.1. On each piece the top-face
formula is the same, and the pieces cover the domain up to ties of measure zero. ∎

### Lemma 6.2 (dParent is a lower face at the flower's grandparent)

Let `pat j = dParent`, so `π_j ∈ 𝒮_j`. Take the piece of the partition at `v_j = π_j` on which the maximizer of
`A_{π_j}` is the child `φ_j`, whose time is `s`. On that piece, the lower-face expression equals the `dParent`
expression of Lemma 3.1.

**Proof.** The child `φ_j` constrains `π_j` with time `s` (S585). The piece is `{other branching children of π_j < s}`;
note `p < s`. The lower face sets `τ_{π_j} = s`, gives the phase `e^{iω_{π_j}s}`, and retains
`s < B_{π_j}`, that is, the parent of `π_j` above `s` (or `s < t` at the root). This is the dParent row. The order
constraint `φ_j < π_j` has become `s < s`, of measure zero. Lemma 9.1 removes it in its substitution, and
`kDomainFix` drops it. ∎

REF 150 already records that OPEN 7.3 "covers the Lemma 9.1 faces, including the face where the pinned child time `s`
is the lower endpoint (`v_j` = grandparent of `f_j`)". By Lemmas 6.1–6.2, **dRoot and dParent are individual faces of
S-L 9.1**: the time structure of each is literally one of the faces for which OPEN 7.3 requires its estimate (S454).

### Lemma 6.3 (dChild is a face at an off-stem vertex: the pinned child face `F_ch`)

Let `pat j = dChild i` and `m = m_{j,i}`. In the plain expression, integrate `τ_m` over `(A_m, s)`. The proof of
S-L 9.1 applies, since it uses only that `m` is not a flower parent. The top face `τ_m := s` is the `dChild`
expression. This configuration is **not** a face of S-L 9.1:

- `m ∉ 𝒮_j`, because it is off the stem;
- its upper endpoint is the **pinned** time of `φ_j`;
- in S-L 9.1 every selected vertex has a free parent, because `φ_j` is the lowest stem branching vertex and is never
  the parent of a selected vertex.

Call it the **pinned child face** `F_ch`.

**Remark 6.4 (the super-atom).** In `dParent` (`U = π_j`, `D = φ_j`) and in `dChild` (`U = φ_j`, `D = m_{j,i}`), the
two coincident pinned vertices satisfy

$$
\sigma_U\Omega_U+\sigma_D\Omega_D=\sum_{e\ \text{external child}}\sigma_e|k_e|^2-\sigma_U|k_U|^2 ,
$$

where the external children are the 5 children of `{U, D}` other than `D` itself. The edge `UD` enters `σ_UΩ_U` as
`+σ_D|k_D|²` (child) and `σ_DΩ_D` as `−σ_D|k_D|²` (parent). The internal momentum is fixed by conservation. The time
constraints are the same in both cases: the parent of `U` is above `s`, and the 5 children are below `s`.

So at the level of the time-pinned molecule, `F_ch` and the `dParent` face are isomorphic: each contracts a bond at
`φ_j` into a degree-6 atom pinned at `s`. They differ only in how the five external edges attach to the
regular-object decomposition. §7 shows that this difference is handled by the same mechanism as the terminal pin.

---

## 7. The pattern pins at the level o73 has reached

OPEN 7.3 is not closed: o73 at `eb26e89a` is OPEN. This section shows that every pattern pin is handled by the
**same** mechanism by which o73 handles the terminal flower-parent pin:

- the exact cut at the linked partner (o73 Prop. 13.1);
- the consumed-modulation operator (o73 Lemma 12.1);
- in the residual molecule, a pinned atom with one exceptional spectral variable (D21 2692).

Each pattern pin adds at most one new exceptional linked coordinate. It carries no resonance-dependent loss, and its
new boundary phases depend only on the external times `t, s`. The only new ingredients are the elementary operators
of Lemma 7.1 and the root-trace cut of Proposition 7.4.

### 7.1 Elementary operators

`A^θ(ℝ^k)`, `0 ≤ θ ≤ 1`, is the space of finite complex measures `μ` with
`‖μ‖ = ∫ max_i⟨λ_i⟩^θ d|μ|(λ)`. Each `μ` is identified with `g(x) = ∫ e^{πiλ·x}dμ(λ)`; on a bounded time domain the
norm is the infimum over extensions (o73 §12; T588–591). Spectator time variables are written `y ∈ ℝ^k`.

**Lemma 7.1.** Let `H` be in `A^θ` in the variables `(t,u,s,y)`, and let `A ∈ ℝ`.

1. (o73 Lemma 12.1, with spectators.) `T_AH(t,s,y) := ∫_s^t e^{πiA(u−s)}H(t,u,s,y)du` satisfies
   `‖T_AH‖ ≤ C_θ‖H‖`, uniformly in `A`.
2. (Mirror.) `T'_AH(t,s,y) := ∫_s^t e^{πiA(t−u)}H(t,u,s,y)du` satisfies `‖T'_AH‖ ≤ 2C_θ‖H‖`, uniformly in `A`.
3. (Fixed endpoint.) For fixed `a ∈ ℝ`, the map `g ↦ g|_{s=a}` is bounded `A^θ(t,s,y) → A^θ(t,y)`, with norm `≤ 1`.
4. (Diagonal.) The map `g ↦ g(s,s,y)` is bounded `A^θ(u,s,y) → A^θ(s,y)`, with norm `≤ 2`.
5. (Fixed interval.) For a unit interval `I`, the map `H ↦ ∫_I e^{πiAu}H(u,y)du` is bounded
   `A^θ(u,y) → A^θ(y)`, with norm `≤ 1`, uniformly in `A`.
6. (Algebra.) A product of at most four `A^θ` functions of subsets of the variables has norm at most `4` times the
   product of their norms.

**Proof.**

1. Use o73 (12.3) atom by atom. The atom `e^{πi(ξt+λu+νs+μ·y)}` goes to
   `e^{πi(ξt+(λ+ν)s+μ·y)}h_{A+λ}(t−s)`. Multiply by one fixed cutoff `Φ(t,s)` equal to `1` on the unit square.
   - o73 Prop. 5.1 gives `‖Φh_z(t−s)‖_{A^θ} ≤ C_θ`, uniformly in `z`.
   - Translating by `(ξ, λ+ν, μ)` multiplies the weight by at most `2max(⟨ξ⟩,⟨λ⟩,⟨ν⟩,⟨μ_i⟩)^θ`, since
     `⟨a+b⟩ ≤ 2max(⟨a⟩,⟨b⟩)`.
   - Integrate against `|Ĥ|`.
2. Let `R(t,u,s,y) = (t, t+s−u, s, y)`. It maps `{s<u<t}` onto itself, and
   `e^{πiA(t−u)} = e^{πiA(u'−s)}` for `u' = t+s−u`. Hence `T'_AH = T_A(H∘R)`. The frequency map of `H∘R` is
   `Rᵀ(ξ,λ,ν,μ) = (ξ+λ, −λ, λ+ν, μ)`, whose weight is at most `2max(…)`. So `‖H∘R‖ ≤ 2‖H‖`.
3. This is the pushforward of `e^{πiλ_s a}dμ` under the forgetful map; it does not increase any weight.
4. This is the pushforward under `(λ_u,λ_s,λ_y) ↦ (λ_u+λ_s, λ_y)`, and `⟨λ_u+λ_s⟩ ≤ 2max(⟨λ_u⟩,⟨λ_s⟩)`.
5. Atom by atom the factor is `∫_I e^{πi(A+λ_u)u}du`, of modulus `≤ 1`.
6. Pull back each factor along the coordinate inclusion and convolve. Peetre's inequality gives
   `⟨a+b⟩^θ ≤ 2^{θ/2}⟨a⟩^θ⟨b⟩^θ`, and three convolutions cost at most `2^{3/2} < 4`. ∎

### 7.2 Where a pattern vertex can sit

**Proposition 7.2.** Let `v` be the designated vertex of a non-plain pattern of tree `j` (Lemma 3.1). Exactly one of
(G1) and (G2) holds.

**(G1)** `v` is a branching vertex of a nontrivial embedded regular object `𝒪` (T846). Then:

- **dRoot:** `𝒪` is stem-rooted with root `r_j = n_1`, the first node of its layer-`p` chain.
- **dParent:** either (i) `φ_j ∈ 𝒪`, and then `(π_j, φ_j) = (n_{2h−1}, n_{2h})`; or (ii) `φ_j ∉ 𝒪`, and then
  `π_j = n_{2h}` is terminal and the lone port of `𝒪` is `φ_j`.
- **dChild:** `m = m_{j,i}` is the root of one tree of a regular couple `𝒬`, or of a nontrivial regular paired tree.
  More precisely, one of the following holds:
  - (i) `φ_j = n_{2h}` of a stem-rooted `𝒪`, and `𝒬` is one of the side couples `𝒬_{·,0,ι}` of the link
    `{a, 2h}` containing `φ_j`;
  - (ii) `φ_j` is a skeleton vertex, and `𝒬` replaces the skeleton leaf pair at `m`, or a regular tree rooted at `m`
    replaces the skeleton vertex `m`.

**(G2)** `v` is a skeleton branching vertex (a trivial regular tree in T870), i.e. an atom of `𝕄(𝒢_sk)`.

**Proof.** We use three facts:

- o73 Prop. 3.1: an embedded object containing a stem vertex is a stem-rooted paired tree, or a (subtree, cap)
  couple. Its chain is in layer `p`, every linked partner of a chain vertex is a chain vertex, and `φ_j`, if
  contained, is terminal.
- T849: consecutive chain vertices are parent and child.
- T870: the decomposition into the skeleton and regular objects.

Now the cases:

- **`r_j`.** It has no ancestor, so an object containing it is rooted at it.
- **`π_j` with `φ_j ∈ 𝒪`.** Since `φ_j = n_{2h}`, its chain parent `π_j` is `n_{2h−1}`.
- **`π_j` with `φ_j ∉ 𝒪`.** The stem leaves `𝒪` at `π_j`. Since chain vertices are consecutive, `π_j` is the last
  one, and the port is its stem child `φ_j`.
- **`m`.** The vertex `φ_j` is never a non-chain vertex of an object: such an object would contain the flower, which
  is paired to the cap outside it (the argument of o73 Prop. 3.1). So either `φ_j = n_{2h}` of a stem-rooted object,
  or `φ_j` is a skeleton vertex.
  - In the first case, T857 attaches the two non-chain children of `n_{2h}` to the side couples `𝒬_{j',0,1}` and
    `𝒬_{j',0,2}` of its link. These have no siblings paired (T849), so `m` is the root of one tree of one of them.
  - In the second case, T870 gives the alternatives listed.
  - `m` cannot be a non-root vertex of an object unless its parent `φ_j` belongs to that object, which is the first
    case. ∎

### 7.3 Case (G1): exact cuts

By Lemma 3.3 it suffices to treat kernels with all phases kept (`off = ∅`). The `†` indicators act only on the
summed boundary data (§8), and the constant `u_ι` is harmless. Throughout, fix the lattice output and the lattice
variables of the exceptional links (T1002–1017), and hence all boundary momenta. `A` and `B` are the signed linked frequencies of the pinned vertices. `τ_top` is the upper time
bound of the root of `𝒪`: it is `t` if the root of `𝒪` is `r_j`, and otherwise a spectator, namely the free time of
its stem parent. Each `K_•` and `Q_•` below is an **ordinary** (unmarked) embedded regular paired tree or couple of
the original garden, with its original layer data, evaluated at the displayed boundary times.

**Proposition 7.3 (pattern-pinned objects).** In case (G1), the object `𝒪^{pat}` (with the pattern pin and, when
`φ_j ∈ 𝒪`, the flower-parent pin) equals one of the following expressions.

| | Configuration | Expression |
|---|---|---|
| (P1) | dRoot, `φ_j ∉ 𝒪`, port time `τ_w`, `r ↔ n_a` | `T'_A[K_int(t,u)Q₁Q₂(t,u)K_suf(u,τ_w)](t,τ_w)` |
| (P2) | dRoot, `φ_j ∈ 𝒪`, `r ↔ φ_j` | `e^{πiA(t−s)}K_int(t,s)Q₁(t,s)Q₂(t,s)` |
| (P3) | dRoot, `φ_j ∈ 𝒪`, `r ↔ n_a`, `φ_j ↔ n_b`, `1<a<b<2h` | `T'_A[K₁(t,u)Q₁Q₂(t,u)·(T_BG)(u,s)](t,s)`, `G = K_mid(u,u')K₂(u',s)Q₃Q₄(u',s)` |
| (P4) | dParent (i), `π_j ↔ φ_j` | `K_pre(τ_top,s)·Q₁(s,s)Q₂(s,s)` |
| (P5) | dParent (i), `π_j ↔ n_b`, `φ_j ↔ n_a`, `a<b` | `T_A[K_pre(τ_top,u)Q₁Q₂(u,s)·(T_BG)(u,s)](τ_top,s)`, `G = K_mid(u,u')K_int(u',s)Q₃Q₄(u',s)` |
| (P6) | dParent (ii), `π_j = n_{2h}` pinned | o73 (13.1) verbatim: `T_A[K_pre(τ_top,u)K_in(u,s)Q₁Q₂(u,s)](τ_top,s)` |
| (P7) | dChild (i), `m` a root in `𝒬 = Q₁` at the link `{a,2h}` of `φ_j` | o73 (13.1) with `Q₁(u,s)` replaced by `Q₁^m(u,s)` of Prop. 7.4: `e^{πiεB(s−q)}·T_A[K_pre K_in R Q₂](τ_top,s)` |
| (P8) | dChild (ii) | the root trace `𝒪^m` of Prop. 7.4 |

In (P1)–(P8) the subscripts index the components of each case separately.

**Proof.** For each case, the legality of the partition (T849: no `a<b<c<d` with `{a,c},{b,d}` linked) splits the
chain at the partners of the pinned vertices into complete legal sub-chains. T857 assigns every side couple to
exactly one link. Conditional on the partner times, the chain inequalities are those of the displayed ordinary pieces,
each side couple keeps its two upper times, and the internal times of different pieces are independent. This is the
argument of o73 Prop. 13.1.

- **(P1).** The links are `{1,a}`, interior `2..a−1`, suffix `a+1..2h` with port-side time `τ_w`. The phases are
  `e^{πiA(t−u)}` with `u = τ_{n_a} ∈ (τ_w, t)`, and the definition of `T'_A` applies. All chain vertices are in layer
  `p` (o73 Prop. 3.1), so the layer constraint on `u` is implied by `τ_w < u < t`.
- **(P2).** Interior `2..2h−1`. The only explicit phase left is `e^{πiA(t−s)}`.
- **(P3).** Interiors `2..a−1`, `a+1..b−1`, `b+1..2h−1`, with `t > u > u' > s`. Integrate `u'` first, which gives
  `T_B`, then `u`, which gives `T'_A`.
- **(P4).** Prefix `1..2h−2`. The two times of the link are both `s`, so its phases cancel, and its side couples are
  evaluated at `(s,s)`.
- **(P5).** Legality forces `{b,2h−1}` to be nested inside `{a,2h}`. The prefix is `1..a−1`, the middle `a+1..b−1`,
  the interior `b+1..2h−2`, with `τ_top > u > u' > s`. Integrate `u'` (`T_B`), then `u` (`T_A`).
- **(P6).** o73 Prop. 13.1 is stated for a stem-rooted regular paired tree whose terminal vertex is pinned at `s`. The
  port child `φ_j` has time `s`, and the constraint between the two designated vertices is dropped (Lemma 3.1).
- **(P7)–(P8).** Proposition 7.4 below. In (P7) the factor `e^{πiεB(s−q)}` depends on `s` only, so it comes out of
  the `u`-integral of (13.1). ∎

**Proposition 7.4 (root trace of an ordinary regular object; case (a) revised in §13.1).** Let `𝒪` be an ordinary embedded regular couple or
regular paired tree, and `ρ` the root of one of its trees. Assume `ρ` has layer `p`, upper time bound `σ`, and
linked frequency `B`. Let `𝒪^ρ` denote `𝒪` with `τ_ρ` pinned at `σ` (the root trace). Then

$$
\mathcal O^\rho=e^{\pi i\varepsilon B(\sigma-q)}\,R,\qquad \varepsilon\in\{0,1\},\qquad
\|R\|_{A^\theta}\le 8C_\theta\prod_{i\le 4}\|P_i\|_{A^\theta},
\tag{7.1}
$$

uniformly in `B`. Here `q` is a fixed layer index, and `P_1,…,P_4` are ordinary embedded regular objects (some
possibly trivial) of total half-order `m−1`. Their incoherency indices add up to `g` or `g−1`; it is `g−1` exactly
when the link of `ρ` is incoherent. The phase depends on the pinned time `σ` only.

**Proof.** Write `ρ'` for the linked partner of `ρ` (T877) and `u = τ_{ρ'}`. There are three cases.

**(a) `𝒪` a type-2 couple or a regular tree, and `ρ = n^ε_1` (T854, T857).** Then `ρ' = n^ε_b` lies in the same
chain. Legality gives the interior `2..b−1` and the suffix `b+1..2m_ε`, both complete. The pieces are:

- `P_1 = K_int(σ,u)`, a regular paired tree with boundary times `(σ,u)`;
- `P_2, P_3 = 𝒬_{j,ε,1}(σ,u), 𝒬_{j,ε,2}(σ,u)`, the side couples of the link `{1,b}`;
- `P_4 = K_rest(u,·)`. For a regular tree this is the suffix paired tree. For a couple it is the couple formed by the
  suffix chain, its side couples, `𝒬_lp` and the other chain `X^{−ε}`. That couple is a type-2 regular couple by the
  construction of T854: removing the complete legal top segment `1..b` leaves complete legal chains.

The constraints of `u` with its chain neighbours lie inside `P_1` and `P_4`. The explicit range of `u` is therefore
`(𝔏_{ρ'}, min(σ, 𝔏_{ρ'}+1))`, and the phase is `e^{πiB(σ−u)}`.

- If `𝔏_{ρ'} = p`, then `𝒪^ρ = (T'_B ∏P_i)(σ, p)`: Lemma 7.1, items 2, 3 and 6. Here `ε = 0`.
- If `𝔏_{ρ'} = q < p`, then `u < σ` holds automatically, and
  `𝒪^ρ = e^{πiB(σ−q)}∫_q^{q+1}e^{−πiB(u−q)}∏P_i du`: items 5 and 6. Here `ε = 1`.

**(b) `𝒪` of type 1 (T853).** Then `ρ'` is the other root (T877). No siblings are paired in the mini-couple (T826),
so each of the three couples `𝒬₁, 𝒬₂, 𝒬₃` replacing its leaf pairs has tops `(σ,u)`. Let `σ⁻` be the upper bound of
`ρ'`, a spectator. The pinned expression is `e^{πiBσ}∫e^{−πiBu}𝒬₁𝒬₂𝒬₃(σ,u)du`, with
`u ∈ (𝔏_{ρ'}, min(σ⁻, 𝔏_{ρ'}+1))`.

- If the parent of `ρ'` has the layer of `ρ'`, this is `e^{πiB(σ−𝔏_{ρ'})}·T_{−B}[∏𝒬_i](σ⁻, 𝔏_{ρ'})`: items 1, 3, 6.
- Otherwise the range is the unit interval, and item 5 applies.

In both sub-cases `ε = 1`.

**(c) `ρ` the root of the `ε`-tree of a type-2 couple with `m_ε = 0`.** Then that tree is the `ε`-tree of the type-1
couple `𝒬_lp` (T854). Apply (b) to `𝒬_lp`. The upper bound of `ρ'` is the time of `n^{−ε}_{2m_{−ε}}`, and the factor
`K_{X^{−ε}}(·,u)` (the other chain, as a paired tree with port-side time `u`) joins `∏𝒬_i` as `P_4`.

In every case:

- the pieces account for all vertices other than `ρ` and `ρ'`, which gives the half-order `m−1`;
- incoherencies sit in the pieces, except possibly that of the link `{ρ,ρ'}` itself;
- the constant `8C_θ` is the product of the constants of items 1–6. ∎

**Remark 7.5 (for o73, not used as a claim about 7.3).** By (7.1), a root trace of an actual side couple has the form
`e^{πiεBσ}R`, with `R` bounded uniformly in `B`. The child-face terms of o73 (15.2) are root traces at the
integrated time `σ = u`. For them,

$$
T_A[e^{\pi i\varepsilon Bu}RQ_2](t,s)=e^{\pi i\varepsilon Bs}\,T_{A+\varepsilon B}[RQ_2](t,s),
$$

which is bounded uniformly in `A` and `B` by Lemma 7.1. So the norm-only obstruction (15.3)–(15.4) does not occur for
actual ordinary side couples with arbitrary descendants, at the time-Fourier level. This is the "linked structure"
that o73 §15 asks for. o73 Prop. 14.1 is the special case of a type-1 mini-couple with trivial descendants.

**Proposition 7.6 (time-Fourier bound; restated in §13.2 for the centred expression).** In case (G1), let `e ∈ {1, 2}` be the number of exceptional links of
`𝒪^{pat}`, that is, links containing a pinned vertex. Then, for each fixed lattice output,

$$
\|\mathcal O^{\rm pat}\|_{X^\eta}\le (C\delta)^m L^{(2\gamma+1)e}L^{-(\gamma_1-\sqrt\eta)g}\le(C\delta)^mL^{3e}L^{-(\gamma_1-\sqrt\eta)g},
\tag{7.2}
$$

uniformly in the output, in the boundary momenta, in the layer assignments and in the linked frequencies. The pattern
pin adds at most one exceptional link to the flower-parent pin's object, so it costs at most `L^3` relative to the
plain pinned object of o73 (13.2). The boundary phases are `e^{πiA(t−s)}` in (P2) and `e^{πiεB(s−q)}` in (P7)–(P8).
They involve only the external times and fixed exceptional frequencies.

**Proof.** This is the argument of o73 Prop. 13.2.

- The components are ordinary objects, with the time-Fourier bounds T953–955 (incoherent) and T1097–1110,
  T1145–1164 (coherent), uniform in boundary momenta.
- Lemma 7.1 combines them, at the cost of the absolute constants of its items.
- Each exceptional link: sum its at most `(CL)^{2d}` lattice tuples and restore its two branching normalizations,
  giving at most `(δ/(2L^{d−γ}))²(CL)^{2d} ≤ Cδ²L^{2γ}`. An unpinned link contributes `Cδ` instead.
- Each incoherent exceptional link loses at most `L^{γ₁−√η} ≤ L`.
- Then `C^mδ^{m+e}L^{2γe}L^{e}L^{−(γ₁−√η)g} ≤ (Cδ)^mL^{3e}L^{−(γ₁−√η)g}`. ∎

To pass to the localized `X^{η,30d,0}` norm, use o73 (13.3)–(13.4): the conversion costs `C_dL^{31d}` per pinned
object, once per object. A pattern pin lies in the flower-parent pin's object in (P2)–(P5) and (P7). It lies in a
separate object in (P1), (P6) and (P8), which costs one more conversion.

**Coefficient level.** o73 Lemma 12.2 converts (12.1) into a coefficient decomposition with one new exception,
provided the inputs have coefficient representations. Lemma 7.1, item 2, writes `T'_A = T_A∘R*` with `R*` acting
only on time frequencies. Items 3–5 act only on `λ` and commute with `∂_α`. So Lemma 12.2 applies verbatim to every
expression in Proposition 7.3 and to (7.1): **each pattern pin adds exactly one exceptional linked coordinate**, under
the same hypothesis under which o73 obtains the terminal pin ("whenever the four factors have the spectral coefficient
representation required by o82", o73 §13). The boundary phases are recorded as `B_F(α_E)·τ` in o73 (10.2), with
`τ ∈ {t, s}` external.

### 7.4 Case (G2): skeleton atoms

**(α) The vertex lies in a vine containing a protected vertex.** T2297 treats such a vine by `ladderl1new` on its
ladders, and by trivial summation and integration over the at most `20` other atoms. Ladders are split at protected
atoms (REF 7.5(iv)), so a pattern vertex is never inside a ladder. A pinned atom contributes a factor of modulus `≤ 1`
in place of a trivial time integral of modulus `≤ 1`. The bound is unchanged.

**(β) The vertex lies in the residual molecule.** It is then estimated by T1994–2013. For a pinned atom `v`,
`𝔅(α) = e^{πiα_vτ_v^{fix}}𝔅'(α_{−v})`. In the sum over `σ` of T1998, the `σ_v`-sum has at most `L^{20d}` terms (T2013:
`Γ_v` takes at most `L^{20d}` values). `𝔅'` is the molecule time integral with `τ_v` fixed, with one denominator
missing. That is exactly the object that OPEN 7.3 must estimate for `φ_j` in this geometry: D21 2692, and o73 §8
("extend T1998 to the residual pieces").

Coincident pins (`dParent`, `dChild` with both vertices in the residual molecule) give two pinned atoms with the same
fixed time and no order constraint between them, hence two exceptional `α`'s.

So in case (G2) the pattern pins add pinned atoms of the kind OPEN 7.3 must already handle, and nothing else.

**Summary of §7.** Every pattern pin, in every geometry, is handled by the mechanism that handles the flower-parent
pin. It adds at most one exceptional linked coordinate, or one exceptional `α` in the residual molecule. It loses no
power of any resonance, and creates boundary phases only in `t, s`. What is pattern-specific is purely a
**statement-level** matter: OPEN 7.3 lists pins at flower parents and the faces of S-L 9.1. By Lemmas 6.1–6.2 the
dRoot and dParent pins are such faces (read individually). The dChild pin `F_ch` is not; §7 proves it at the
time-Fourier level and reduces it at the coefficient and residual levels to exactly the obligations of the
flower-parent pin.

---

## 8. The † variant in full

**Proposition 8.1.** Fix `c` and a pattern vector. For each flower-position class `ι`, the gain-free bound proved for
`flowerSumP^ι(pat, none)` also holds for `flowerSumP^ι_sib(pat)`, with the same constants. Consequently

$$
|\mathrm{flowerSumP}(\mathrm{pat},\mathrm{some}\,c,\dots)|\le 3^{2P}\cdot\big[\text{the bound for }\mathrm{flowerSumP}(\mathrm{pat},\mathrm{none},\dots)\big],
\tag{8.1}
$$

with no power of `L`. The `M₂` factor is kept for all-plain vectors (§4.3).

**Proof.** By Lemma 3.3 the only change is the weight `sibWeight_c = ∏_e 1[k_e = c_e]`, over the edges
`e = (φ_j, m_{j,i})`. Both endpoints of each such edge are protected (S68). In each geometry of Proposition 7.2,
`k_e` is a variable that the existing estimates sum in absolute value:

- **(G1), `φ_j = n_{2h}` of a stem-rooted object.** `k_e` is the root momentum of a tree of a side couple of the link
  `{a, 2h}`. In the coordinates of T981–1017 it is `k` plus an integer combination of that link's two lattice
  variables. The chain momentum is `k` (T1235–1244; S-L 4.1 proof). This link is exceptional (it contains the pinned
  `φ_j`), and its at most `(CL)^{2d}` lattice tuples are summed in absolute value (o73 Prop. 4.1 proof, Prop. 13.2
  proof). The indicator restricts that sum.
- **`φ_j` a skeleton vertex.** `k_e` is a bond momentum at the protected atom `φ_j`. It is summed trivially (in
  absolute value) in a vine containing a protected vertex (T2297), or it enters the absolute counting of the residual
  molecule (T2090–2097). In either case it is a boundary momentum of the excised protected atoms in OPEN 7.5
  (clause 3: "with the fixed boundary momenta included among the allowed fixed values").

Restricting a sum of nonnegative terms does not increase it; this is the monotonicity behind S-L 9.4, used here only
after absolute values have been taken. Each class `ι` is a union of the LF families of the plain proof
(Lemma 5.1(b)). The order-`n` bound is obtained by summing family bounds in absolute value (T2237–2255, S-Prop. 10.3),
so it holds for each class. Sum the at most `3^{2P}` classes in (3.2). ∎

**Alternative, when an indicator must sit inside an amplitude.** Take `ψ` smooth, supported in `|z|<1`, with
`ψ(0) = 1`. On lattice values, `1[k_e = c_e] = ψ(L(k_e−c_e))` (o73 §4, "cap constraint"). Its Fourier-measure total
variation is `‖𝓕ψ‖₁`, uniformly in `L` and `c_e`, because `k_e` is affine in the link variables. So it is an
admissible amplitude for S-L 4.2 (zero spatial derivatives), at a constant cost of at most `‖𝓕ψ‖₁^{4P}`.

**Interface (not a new claim).** OPEN 7.5 is used in **boundary form**: its exceptional-piece estimate is uniform in
the momenta on the bonds incident to protected atoms, and these momenta are then summed in absolute value. This is
how T2297 and S-L 7.4 count, and how o73 Prop. 4.1 and 13.2 treat exceptional links.

---

## 9. Assembly

### Theorem 10.4 (derivative patterns and †)

Fix `Pm = P ≥ 1` and frozen data `(p, R, t, s, n, n', ζ, N, kind)`. Fix any `pat : Fin(2P) → FixPat`, any `dagger`,
and `cut1, cut2` satisfying the frozen side condition. Put `c(pat) = 1` if every `pat j = plain` and `c(pat) = 2`
otherwise. Assume:

- **(H1) Plain machinery.** The hypotheses of o63 Prop. 10.3′ hold: OPEN 7.3, 7.5 and 8.2, and the referee's OPEN 8.3
  and OPEN 10.3 as being restated. They deliver o63 (5.1) for plain integrands, with an exponent `B` satisfying S(10.4):
  `B + 80d + 1/9 + 3 ≤ (100d)^3`.
- **(H2) Pins.** The estimates of OPEN 7.3 hold for the pin set
  `Π_pat = {φ_j}_j ∪ {v_j : pat j ≠ plain}`, pin by pin, with coincident pins allowed. Concretely: the flower-parent
  pins; the individual faces of S-L 9.1 identified in Lemmas 6.1–6.2; and the pinned child face `F_ch` of Lemma 6.3.
- **(H3) Protection.** OPEN 7.5 holds with the protected list `S68 ∪ {π_j : pat j = dParent}`, in the boundary form of
  §8.

Then, with `β_pat := 0` if all `pat j = plain` and `β_pat := 300d` otherwise (corrected in §13.5 to `76000d³+3372d+65 ≤ (100d)^3`):

**(a)** o63 (5.1) holds for `Θ_pat` with exponent `B + β_pat`. In it, `G₂ = M₂^{−P/9}` whenever `cut2` is nonbottom,
`|k| ≥ M₁^{10}` and all `pat j = plain` (with or without `†`); otherwise `G₂ = 1`.

**(b)** For `L ≥ L₀(P, δ, 𝔇, φ_in)`, the bound (2.1) holds:

$$
\|\mathrm{flowerSumP}\|\le\langle k-\zeta k'\rangle^{-4\Lambda P}L^{c(\mathrm{pat})(100d)^3P}\delta^{2\nu N}
M_1^{-80dP}[cut1]\;M_2^{-P/9}[cut2,\ \text{all plain}].
$$

**(c)** All gains of unmarked incoherent objects, bad vines and ladders are retained.

When `pat` has no `dChild` entry, (H2) is OPEN 7.3 as stated (S440–456), with its S-L 9.1 faces read individually.
§7 proves those individual faces directly at the time-Fourier level.

**Proof.**

(a) The plain bound (5.1) is the reduction of S §§4–9, completed by the OPEN items in (H1). By Lemmas 3.1 and 3.3,
`Θ_pat` differs from the plain integrand only at the vertices `v_j` and on the edges `(φ_j, m_{j,i})`. All of these
are protected (Lemma 5.1). The reduction therefore applies with these vertices in the exceptional set, and the
difference enters at exactly three places:

- (i) the estimates of the pinned objects and atoms, by (H2) and §7;
- (ii) the boundary sums of the excision, by (H3) and §8;
- (iii) the count of protected incidences, which grows by at most `4·2P` crossing bonds (S-L 7.4).

Proceed one tree at a time.

- **Anatomy.** By Lemma 3.1, a non-plain pattern adds exactly one pinned vertex `v_j ∈ Π_pat`. By Lemma 3.3, `†` adds
  only indicators on protected edges and a constant phase per class.
- **Protection.** By (H3) and Lemma 5.1, every designated vertex is protected. The twists used preserve `Θ_pat`, the
  classes `ι`, and `sibWeight`.
- **Pins.** By (H2), each pin is estimated by OPEN 7.3's machinery. §7 shows that this uses at most one new
  exceptional coordinate per pattern pin and no resonance-dependent loss. The numerical costs are in §10: at most
  `150d` powers of `L` per tree, so at most `β_pat·P = 300dP` in total.
- **†.** It costs `L^0` (Proposition 8.1).
- **Unmarked gains.** The pattern pins touch only exceptional links (Proposition 7.6) or exceptional atoms (§7.4).
  Every untouched link keeps its incoherency gain: o73 Prop. 4.1 with `g_J`, and (7.1). No unmarked object, vine or
  ladder is changed (Lemma 5.1(b)). This also proves (c).
- **`M₂`.** For all-plain vectors, the `M₂` argument is unchanged (§4.3).
- **The base `D_P`.** There are at most `2P` added pins, a number independent of `n`. Any factor `δ^{−C}` per pin goes
  into `E_{P,δ}`, so `D_P` is unchanged.

(b) o63 Theorem 6.3′ applies to `Θ_pat` (§4.1) and extracts `⟨k−ζk'⟩^{−4ΛP}` and `M₁^{−80dP}` at zero cost. o63
Prop. 10.3′ and S Prop. 10.3 then give the bound with exponent

`B + β_pat + 80d + 1/9 + 3 ≤ (100d)^3 + β_pat ≤ c(pat)(100d)^3`,

since `β_pat = 0` when `c = 1`, and `β_pat = 300d ≤ (100d)^3` when `c = 2`. The gate is stated per order (its
deviation D2). S-L 10.1 turns `E(1+n)^A D_P^{n+1}δ^{8νn}` into `L^{P}δ^{2νn}` order by order, within the margin. ∎

### Mapping onto the three inputs (HANDOFF 99–174)

- **`FC23UniformCut1At`.** The family weight `flowerFamilyWeight` (port FC23/FlowerFamily.lean:44–52) depends only on
  the momenta of the top leaves and attached roots, and on `M, A, z, tail, small`. `pat` and `dagger` enter
  `flowerWeighted` (FlowerFamily.lean:13–24) only through `fixPat`, `off` and `sibWeight`, exactly as in `flowerSumP`.
  So the pattern data are disjoint from the profile family, and every step above holds uniformly over that family.
  The pattern exponent `β_pat ≤ 300d` sits inside the extra `(100d)^3P` of the budget
  `L^{c(pat)(100d)³P−80dP−2P}`. Whatever proof FC23 gives for plain vectors therefore extends to all `(pat, dagger)`,
  at cost `L^{300dP}` and no other change.
- **`PositiveCut2At (1/9)` and `FlowerCaseAt CaseCut2Zero`.** These are (2.1) with `cut2 = some j₂`, `j₂ > 0`, and with
  `cut2 = some 0`: Theorem 10.4(b). For non-plain vectors the `M₂` factor is `1`, and the filter is carried without its
  gain. This is OPEN 8.2's case "any subset of stem vertices, no selected occurrence", together with S-L 9.3 and
  OPEN 8.3, with the pattern pins counted among 8.2's "protected pins … of OPEN 7.3".

---

## 10. Loss accounting

Costs are per tree with a non-plain pattern; at most `2P` trees. All are upper bounds, and different levels are added
rather than compared.

| Operation | Extra factor | Source | `L`-exponent |
|---|---|---|---:|
| New exceptional link, time-Fourier level | `CδL^{2γ}·L^{γ₁−√η} ≤ L^3` | Prop. 7.6; o73 Prop. 13.2, (4.2) | `3` |
| Local output extension for a separately pinned object, (P1)/(P6)/(P8) | `C_dL^{31d}` | o73 (13.3) | `31d` |
| Spectral-fiber conversion, at most 2 new coordinates (7.3's rule) | `(C_dL)^{8d}` | S-L 7.1; o73 Prop. 6.1 | `8d` |
| Residual-molecule pinned atom | `≤ L^{20d}` intervals | T2013; §7.4(β) | `20d` |
| Added protected vertex `π_j` (dParent): at most one more special vine | `L^{20d}` trivial part + 3 ladders at `L^{20d}` | T2297; S485 | `80d` |
| Faces / partition pieces | `1` (Lemmas 6.1–6.3 use one face, no partition sum) | §6 | `0` |
| **Total per tree** | | | `≤ 139d+3 ≤ 150d` |
| **Total, `2P` trees** (`β_pat·P`) | | | `≤ 300dP` |
| `†`: phase classes, indicator | `3^{2P}` (and `‖𝓕ψ‖₁^{4P}` if the amplitude form is used) | Lemma 3.3; Prop. 8.1 | `0` |
| `M₁`, external decay, all patterns | `(16c_χ)^nC_{P,δ}(1+n)^{(8Λ+80d)P}` | o63 Thm 6.3′ | `0` |
| Remainders, all patterns and `†` | absolute, with margin `L^{−P}e^{−100N}` | o102 §8.4 | `0` |

**Budget check.** (Superseded by §13.5, which adds the per-incidence filter charge `c_{8.2}`; the conclusions are unchanged.)

- **All-plain vectors, with or without `†`.** `β = 0`, so S(10.4), `B + 80d + 1/9 + 3 ≤ (100d)^3`, is unchanged, and
  the `M₂` gain is kept.
- **Non-plain vectors.** `B + β_pat + 80d + 1/9 + 3 ≤ (100d)^3 + 300d ≤ 2(100d)^3`, because `300d ≤ 10^6d^3`. For
  example, at `d = 3`: `900 ≤ 2.7·10^7`. The doubling is therefore more than three thousand times what the patterns
  use.
- **FC23 budget.** `c(pat)(100d)^3 − 80d − 2` exceeds the plain budget by `(100d)^3 ≥ 300d` for non-plain vectors.

**Quantifier order.** The order is C₀, η, C₁, ν, then P, then δ, then C₂, then L.

- The pattern costs are powers `L^{O(d)}` per tree times constants depending on `(d, P)`.
- No factor `L^{Cn}` or `C₂^n` appears: the number of added pins is at most `2P`, independent of the order.
- The exponential base `D_P` is unchanged.
- `3^{2P}` and `‖𝓕ψ‖₁^{4P}` are absorbed by the threshold on `L`.

---

## 11. Dependencies

| Source and lines | Content | Use |
|---|---|---|
| F:FixPat:30–34; F:LayeredGardenFixPat:41–50; F:LayeredGardenPatValid:43–48 | patterns, designated nodes, validity | Lemma 3.1 |
| F:KDomainFix:40–44; F:KernelKgen:54–66; F:PhaseProdOff:39–43 | free-time domain with dropped designated constraints; general kernel; removed phases | Lemmas 3.1–3.3 |
| F:LayeredGardenSibWeight:44–48; F:FlowerSumP:68–81; F:IsDecoration; F:ResFactor; F:CosetDecoration | `†` weight, flower sum, conservation, resonance, lattice decorations | Lemma 3.3 |
| F:ProdDyadicCut:21–28; F:LayeredGardenCutWeight1P/2P; F:LayeredGardenIsTopLeaf | product-form cutoffs and their supports | §4.1 ((Hb′)); §9 |
| Frozen/Theorems/LayergardenFlowerV3.lean:93–106 | the frozen bound, `c(pat)`, `M₂` iff all plain | §2.2, Theorem 10.4 |
| HANDOFF 99–174; port FC23/FlowerFamily.lean:13–24, 44–56; FlowerTop/FinalFamily.lean:23, 39 | the three inputs; the profile family; couple clause discharged on main | §2.2; §9 mapping |
| T640–647 | decorations, `Ω` | Lemma 3.3; Remark 6.4 |
| T673–674, T712–714 | time domains | Lemmas 3.1–3.2 |
| T826–828, T846, T849, T851–857, T870, T877 | regular objects, embedded objects, legal chains, structure theorem, skeleton, linkage | Props. 7.2–7.4 |
| T953–955, T1097–1110, T1145–1164 | ordinary time-Fourier bounds of regular objects | Prop. 7.6 (components) |
| T981–1017, T1002–1017 | coordinates `(k, x, y)`; localization of link variables | Props. 7.6, 8.1 |
| T1235–1244 | chain momentum `k` | Prop. 8.1 |
| T1447–1487, T1458 | LF twists preserve outside data; unit twist | Lemma 5.1 |
| T1994–2013 (T1998, T2013) | residual time-integral estimate; at most `L^{20d}` values of `Γ_v` | §7.4(β); §10 |
| T2090–2097; T2237–2255 | absolute counting; summation of family bounds | Prop. 8.1 |
| T2259–2265, T2283–2285 | flower trees and kernels; cutoffs | §§2–3 |
| T2294–2300 | decay and `M₁`; special nodes and special vines (T2297); `M₂` (T2299); stem invariance (T2300) | §§4–5 |
| T2312, T2321, T2327, T2330–2331 | `∂_t a^tr`; `𝒥†`; Sobolev in `(t,s)`; `∂_{t,s}` pins | Lemma 3.2; context |
| D21 2684–2694 (2689–2690, 2692) | terminal pin, odd chain, residual denominator | §7 (mechanism), §7.4(β) |
| S68; S-L 4.2; S-L 7.1; S-L 7.4; OPEN 7.3 (S440–456); OPEN 7.5 (S472–487, S485); OPEN 8.2 (S535–551); S-L 9.1 (S572–594); S-L 9.3, 9.4; S-L 10.1; S-Prop. 10.3; S(10.4) | protected list; amplitudes; fiber count; excision counts; pin/face target; exceptional pieces; filters; faces; polynomial absorption; assembly; budget | throughout |
| REF 132, 150, 175–181; REF 7.5(iv) | unit twist; 7.3 covers Lemma 9.1 faces; item M4; ladders split at B | §§5–7 |
| o63 §§1–5, Remark 2.1, §7 | Theorem 6.3′, (5.1), Prop. 10.3′ | §4.1, Theorem 10.4 |
| o102 §8.4 | remainders for patterns and `†` | §4.2 |
| o73 Prop. 3.1, Prop. 4.1, §4 (cap constraint), Prop. 5.1, Prop. 6.1, Lemmas 12.1–12.2, Props. 13.1–13.2, (13.3)–(13.4), Prop. 14.1, §15 | stem geometry; scalar pin estimate; lattice-equality amplitude; one-link Fourier bound; fiber conversion; consumed modulation; terminal pin; output extension; mini-couple child face; root-trace obstruction | §§7–8 (only results o73 states as proved) |

---

## 12. Remaining OPEN sub-items

**Pattern-specific: one item.**

- **OPEN 10.4.C (the pinned child face `F_ch`, pattern `dChild`). Closed in Revision 1 (§13.4) by o73 Theorem 7.3′.** OPEN 7.3 lists pins at flower parents and the
  faces of S-L 9.1. The `dChild` configuration — the branching non-flower child `m` of `φ_j` pinned at `s`,
  coincident with `φ_j` (Lemma 6.3) — is not on that list. It must be added to OPEN 7.3's pin/face list,
  equivalently to o73's "explicitly enumerated parent/child/floor/top faces". Its status at each level:
  - *Time-Fourier level, regular-object geometry:* **proved here**. `F_ch` is the root trace (7.1) of the ordinary
    object hanging off `φ_j`, inserted into o73 (13.1), or standing alone. See Props. 7.3 (P7)/(P8), 7.4 and 7.6. Its
    cost is one new exceptional link (`L^3`) and a boundary phase in `s` only.
  - *Coefficient level:* o73 Lemma 12.2 applies verbatim (§7.3). It needs the same component representation that o73
    needs for the terminal pin.
  - *Residual molecule:* one more pinned atom (§7.4(β)), i.e. the same extension of T1998 that OPEN 7.3 needs for
    `φ_j`.
  - *Vines containing a protected vertex:* nothing to do (§7.4(α)).

  So `F_ch` closes together with OPEN 7.3 once it is added to 7.3's list. The time-Fourier work is done in §7; nothing
  beyond the flower-parent pin's obligations remains.

**Statement-level readings: not new mathematics, but they must be recorded in the restated items.**

- **(R1)** OPEN 7.3's S-L 9.1 faces are read **individually** and **without** the selection restriction
  `|Ω_{v_j}| ≥ cM₂` or the reciprocal, with the face frequency exceptional and the estimate uniform in it. This is what
  dRoot and dParent use (Lemmas 6.1–6.2). §7 proves these two configurations directly at the time-Fourier level
  ((P1)–(P6)). If 7.3 is closed only for signed face collections (as S-8.2 permits), dRoot and dParent fall under
  10.4.C as well; the proofs of §7 still apply.
- **(R2)** OPEN 7.5 in boundary form (§8). This is used for `†` only.
- **(R3)** For trees with `pat j = dParent`, `π_j` is added to the protected list (Lemma 5.1(a)): at most `2P` more
  protected vertices, at most `4` crossing bonds each, and at most `L^{80d}` each, inside `β_pat`.

**Inherited, not pattern-specific.** OPEN 7.3, 7.5 and 8.2 as for plain kernels, and the referee's OPEN 8.3 (filtered
LG ladders) and OPEN 10.3 (aggregate count). Theorem 10.4 assumes exactly these, as o63 Prop. 10.3′ does for plain
kernels.

**Not needed.** No new `M₂` argument: the frozen gate asks for `M₂` only on all-plain vectors, where `†` is harmless
(§4.3). No new remainder estimate (o102 §8.4). No new `M₁` or external-decay argument (o63).

---

## 13. Revision 1 (after REFEREE-73)

New pinned inputs, copied and hashed at first read:

| Abbrev. | File | SHA-256 |
|---|---|---|
| REF-73 | flower-open/ref/REFEREE-73.md | `6b4b64eb1d8467859ba5c21d2312eb45363241a1bfc2459836cd5d8a6c37fd2d` |
| o73′ | flower-open/o73/RESOLUTION.md (Theorem 7.3′ §21, §19, §22), as refereed | `683351431762e5dd0ebff1b84daeb5d623b0ab45ca39807bb7fc90d39a58f7bf` |
| o73″ | the same file, live at the end of this revision: o73's Revision 1 (§23), which applies all REFEREE-73 fixes | `a38115ed3971e35e140dc939c2b2ce39913b7c968d2bfd7c74fc2fcd538a4206` |

Citations below are to o73′, the refereed text. I checked that o73″ keeps everything cited:

- Theorem 7.3′ and `F_ch`;
- the port convention of §19.1;
- (19.2);
- the derivative-pattern paragraph after Theorem 7.3′.

o73″ also adds Fix 73-RT (traced root in layer `p`; `R_B` may depend on the port time) and corrects its printed hash
of this file.

REF-73 read this file at `21e48492…ac273af` (REF-73 §0, 379). The two fixes it requests (REF-73 §3, "o104") are
13.1–13.2. 13.3–13.5 record consequences. **No result of §§3–9 changes.** Sections 7.3, 7.6, 10 and 12 above are
superseded where they conflict with this section.

### 13.1 Fix 1: Prop. 7.4(a) uses the port convention (REF-73 §2.7, 192–196; o73′ §19.1)

**The defect.** In case (a) with the mate `ρ' = n_b` in layer `p`, Prop. 7.4 integrated `u = τ_{ρ'}` from the layer
floor `p`. Suppose `𝒪` is a regular **paired tree** whose lone port has the mate's layer, with port time `τ_w > p`.
Then the true range is `u > τ_w`. If the suffix is empty, no `P_i` carries this constraint, and integrating an
`A^θ` extension over `(p, τ_w)` integrates outside the tree's defining triangle. Statement (7.1) is unaffected; only
the choice of endpoints in its proof changes.

**Corrected case (a).** All ordinary functions are evaluated only in their defining time domains (o73′ §19.1). Every
lower constraint on the mate other than its own layer floor and the port is carried inside `P_1` or `P_4`. Let

- `lo := τ_w` if `𝒪` is a paired tree whose port has the mate's layer `𝔏_{ρ'}`; otherwise `lo := 𝔏_{ρ'}`, the floor.
  For a couple there is no port. For a paired tree whose port has a lower layer, `τ_w < 𝔏_{ρ'}` holds automatically.
- `hi := σ` if `𝔏_{ρ'} = p`; otherwise `hi := 𝔏_{ρ'} + 1`, a fixed layer endpoint, and then `u < σ` is automatic.

Then `u` ranges over `(lo, hi)` and the phase is `e^{πiB(σ−u)}`. Two cases:

- **`hi = σ`.** Then `𝒪^ρ = (T'_B∏P_i)(σ, lo)`, with `ε = 0`. If `lo = τ_w`, use Lemma 7.1, items 2 and 6, with `τ_w`
  a boundary variable. If `lo = p`, add item 3.
- **`hi = q+1` with `q = 𝔏_{ρ'} < p`.** Write `e^{πiB(σ−u)} = e^{πiB(σ−(q+1))}·e^{πiB((q+1)−u)}`. Then
  `𝒪^ρ = e^{πiB(σ−(q+1))}·(T'_B∏P_i)(q+1, lo)`, with `ε = 1`. Use items 2, 3 and 6, with item 3 applied to the fixed
  first slot `q+1` (the same pushforward argument). When `lo = q` this is the old fixed-interval formula (item 5).

In both cases `‖R‖_{A^θ} ≤ 8C_θ∏‖P_i‖`, uniformly in `B`. In (7.1), `q` now denotes a fixed layer endpoint (here
`𝔏_{ρ'}+1`), as in o73′ (19.1). `R` may depend on the boundary time `τ_w` (REF-73 Fix 73-RT).

**Cases (b) and (c)** are unchanged. There the mate is a root of a couple's tree: its lower constraints lie inside the
`𝒬_i`, or inside `K_{X^{−ε}}(·,u)`, and it has no port. **Prop. 7.3** is unchanged: (P1) already integrates from the
port time (`T'_A(t,τ_w)`), and (P3)–(P6) integrate from `s` or between chain times.

### 13.2 Fix 2: boundary phases in (7.2) are recorded and consumed (REF-73 §2.7, 204–206; o73′ §19.1, (19.2))

Read literally, (7.2) put `e^{πiA(t−s)}` (P2) and `e^{πiεB(s−q)}` (P7)/(P8) inside an **uncentred** `X^η` norm
"uniformly in the linked frequencies". That is false: such a norm grows like `⟨A⟩^η` (o73 §5). Replace the statement
of Prop. 7.6 by the following.

**Prop. 7.6 (revised).** Write `𝒪^{pat} = e^{πiℓ·τ}·𝒪^{pat}_c`, where:

- `e^{πiℓ·τ}` is the displayed boundary phase: `e^{πiA(t−s)}` in (P2), `e^{πiεB(s−q)}` in (P7)/(P8), and `1` in
  (P1) and (P3)–(P6), whose modulations are already consumed by `T_A`, `T'_A`, `T_B`;
- `𝒪^{pat}_c` is the **centred** expression.

Then (7.2) holds for `𝒪^{pat}_c`, uniformly in the output, the boundary momenta, the layers and the linked
frequencies. The phase is not bounded in any positive-weight norm. It is **recorded** (as `ℓ_E` in o73′ (19.3), or
`B_F(α_E)·τ` in o73 (10.2)) and **consumed**:

- at the fixed external times `t, s` it is a unimodular constant, once the exceptional spatial tuples are fixed;
- where `s` is a boundary variable integrated later, it is absorbed into the adjacent integral by the
  consumed-modulation operator, o73 Lemma 12.1: exactly as in o73′ (19.2),
  `T_A[e^{πiεBu}RQ₂] = e^{πiεBs}T_{A+εB}[RQ₂]`;
- in the residual coefficient it translates that atom's `ξ`, where o73′ Prop. 18.1 is uniform.

The same reading applies to Remark 7.5 and to the "Coefficient level" paragraph of §7.3. o73′ §19 adopts it
explicitly.

### 13.3 Consistency with REF-73 Fix 73-UF (faces individually)

REF-73 asks that upper faces be estimated **summed over the maximizer cells**, and lower faces per cell
(Prop. 19.2, Thm 7.3′(1)). Lemma 6.1 identifies `dRoot` with the top face **summed over the pieces**: that is the
identity used, and it is what Theorem 7.3′ estimates. The words "and also piece by piece" in Lemma 6.1 mean only that
each cell's top-face term is the restriction of the dRoot integrand to that cell; no per-cell upper-face estimate is
used anywhere. Lemma 6.2 identifies `dParent` with a single lower-face cell, which 73-UF allows. `F_ch` is a root trace
(o73′ (19.6), (19.1); REF-73 Fix 73-P8 for (P8)).

### 13.4 The pattern-specific sub-item 10.4.C is absorbed by o73 Theorem 7.3′

o73′ Theorem 7.3′ (§21), refereed **PASS AFTER FIX** with 0 FAIL (REF-73 §1, rows 7–9 and 12; fixes 73-UF, 73-P8,
73-L19, 73-RT, none changing an exponent), supplies hypothesis (H2) of Theorem 10.4 in full:

- **Individual faces.** Item (1) estimates the individual top, parent, stem-child and side-child faces of S-L 9.1
  without a selected reciprocal or an `M₂` assumption (Prop. 19.2). This is reading (R1) of §12, hence `dRoot` and
  `dParent` (Lemmas 6.1–6.2).
- **`F_ch`.** Item (1) includes the off-stem pinned child face `F_ch` (o73′ (19.6)), which is the `dChild`
  configuration of Lemma 6.3.
- **Coefficient level.** Item (2) gives the coefficient representation (19.3)–(19.4) with at most two exceptional
  coordinates per incidence.
- **Residual molecule.** Item (3) gives the residual mixed estimate (18.3), "including the coincident pinned-vertex
  configurations dParent and dChild".

The paragraph "Derivative patterns and †" after Theorem 7.3′ (o73′ 900) consumes Lemmas 3.1 and 3.3, §8 and
(P1)–(P8) of this file, with the enlarged protected count `b ≤ 30P`. It confirms the restriction argument of
Prop. 8.1: "restricting the exceptional tuple sum cannot increase the absolute bound". So:

- **OPEN 10.4.C is closed** by o73′ Theorem 7.3′(1)–(3), and readings (R1)–(R3) are met there.
- (H3) is met in o73′'s unexcised setting, with o75 Theorem 7.5′ (Rev. 1) and protected count `b ≤ 30P`.

The remaining hypothesis (H1) is the plain assembly itself: o63 Prop. 10.3′, o75 Rev. 1, o73′ Thm 7.3′, o82, o83.
This is exactly what the brief allows Theorem 10.4 to assume.

### 13.5 Budget: the binding check is the receiving ledger (correction to §§9–10)

§10's `β_pat ≤ 300d` (per `P`) counts the pattern-pin costs at the level of §7: exceptional link, output extension,
fiber conversion, residual atom, protection. It does **not** charge the per-incidence filter constant `c_{8.2}`
(OPEN 8.2) for the added protected incidences, which o75's derivative rows do charge. The binding numerical check is
therefore o73′ (22) as verified in REF-73 §2.12, with `b ≤ 30P` and `c_{7.3} = 400d` per incidence:

- At o75's ceiling `c_{8.2} = 19000d³`: doubled total `≤ 570000d³ + 22936d + 483.2`. Adding o104's `300d`, which
  REF-73 notes is an overcount, gives `< 2·10⁶d³`. The increment over the plain total `494000d³ + 19864d + 419.12` is
  at most `76000d³ + 3372d + 65 ≤ (100d)^3`.
- At `c_{8.2} = 47d + 5`: doubled total `24646d + 633.2` (including the `300d`), against plain `21006d + 546.01`. The
  increment is `3640d + 88`.

So `β_pat ≤ (100d)^3` holds in either convention, and (2.1) holds with `c(pat) = 2`. In Theorem 10.4, read
`β_pat := 76000d³ + 3372d + 65`, at most `(100d)^3`, in place of `300d`. All-plain vectors (with or without `†`) add no
incidence and keep `β = 0`.

### 13.6 Status after revision

Theorem 10.4 (§9) holds as stated, with:

- (H2) discharged by o73′ Theorem 7.3′;
- (H3) as in o73′ §21;
- `β_pat` as in 13.5;
- Props. 7.4 and 7.6 as revised in 13.1–13.2.

No pattern-specific OPEN sub-item remains.

STATUS: CLOSED (Theorem 10.4, §9 with Revision 1, §13: the dChild sub-item 10.4.C is absorbed by o73 Theorem 7.3′, REFEREE-73 PASS AFTER FIX; Prop. 7.4(a) now uses o73's port convention; boundary phases are recorded and consumed via o73 Lemma 12.1; the doubled budget is checked against o73 (22) and REFEREE-73 §2.12; the remaining hypotheses are the plain assembly's).
