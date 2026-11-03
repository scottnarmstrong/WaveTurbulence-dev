# Figure-only definitions: textual versions, checked against the PNGs (Task 3b) and F14 (Task 3c)

Auditor: `wt-orch`. Date: 2026-11-03.

**Sources.**

- **TARGET:** `paper/source/WKE-Longer_times_Final_arXiv.tex` (sha256 `493eef6b…727cb`), with figures in
  `references/src-2311.10082/`.
- **DH23:** `references/src-2301.07063/Revision_Submit.tex`, with figures in that directory.
- **DH21:** `references/src-2104.11204/Inventiones-Final_Version.tex`.
- **Maps compared:** `maps/T-part2.md`, `maps/DH23.md` and `maps/DH21.md`, as of today.

**How I read the figures.** I viewed every figure named below myself. Where detail mattered I cropped it at full
resolution with ImageMagick into the session scratchpad.

**Purpose.** This document says what each figure-defined object *is*, in graph terms, so that a Lean definition can
be drafted in Wave B. Each section has four parts: (a) the precise definition; (b) discrepancies with the maps;
(c) ambiguities, with the reading I recommend; (d) Lean shape.

**Summary of substantive findings.** These change or constrain definitions; cosmetic transcription slips are only
listed in the sections.

- **V1 (§1).** Ladder insertion has an off-by-one gap. TARGET requires every ladder to have ≥ 2 rungs (L1384), while
  DH23 defines length = #rungs − 1 with no lower bound (DH23 L790). With the figure's insertion rule, TARGET's
  literal family therefore *misses every vine in which some dashed pair carries exactly one extra rung*. DH23's
  family includes them. **Recommendation:** define the vine family by "each dashed pair carries k ≥ 0 extra rungs",
  which is DH23's family, and keep "length ≥ 1" only for standalone ladders.
- **V2 (§1).** The two direction rules, "the two bonds at each joint have opposite directions" and "parallel ladder
  rails have opposite directions", both follow from the block axioms inside a vine (2-cut lemma, §0). A vine
  predicate therefore needs only *block + undirected template isomorphism*. This removes the map's Q1 worry about
  the directions of the dashed bonds.

---

## §0. Conventions used throughout

### 0.1 Molecules (TARGET L1295)

A **molecule** is a finite directed multigraph (loops allowed) with:

- every atom having out-degree ≤ 2 and in-degree ≤ 2;
- no connected component consisting only of degree-4 atoms.

An **atomic group** is a set of atoms together with *all* bonds between them, i.e. an induced sub-multigraph.

### 0.2 Blocks (TARGET L1324)

An atomic group 𝔹 is a **block** if two atoms `v₁ ≠ v₂` (the **joints**) have in-degree 1 and out-degree 1 within
𝔹, and every other atom of 𝔹 has degree 4 within 𝔹.

Because a molecule allows at most 2 in and at most 2 out, every interior atom of a block is exactly 2-in/2-out
inside 𝔹. It also has **no** bond leaving 𝔹, since its total degree is ≤ 4.

### 0.3 Lemma "2-cut" (mine; elementary)

> Let 𝔹 be a block and let S ⊂ 𝔹 be such that exactly two bonds of 𝔹 join S to 𝔹∖S. Then those two bonds have
> opposite directions relative to S (one leaves S, one enters S).

*Proof.* Inside 𝔹 every atom has out-degree = in-degree: 1/1 for joints, 2/2 for interior atoms. Summing
`out − in` over S, bonds inside S cancel. The two crossing bonds must therefore contribute `+1` and `−1`. ∎

**Consequence (V2).**

- In every vine template below, every pair of parallel dashed bonds, and every pair of parallel ladder rails, is a
  2-cut of the vine, with the joint(s) on one side. So "parallel single bonds have opposite directions" holds
  **automatically** for blocks.
- Likewise "the two bonds at a joint have opposite directions" is exactly the joint axiom of a block.
- **Recommendation:** define "𝕍 is a vine of type X" as "𝕍 is a block, and 𝕍 as an *undirected* multigraph is
  isomorphic to a template `T_X(k⃗)` by an isomorphism sending joints to joints". Then prove the direction facts as
  lemmas.
- The explicit direction requirement is needed only for **standalone ladders** in an arbitrary molecule
  (`layerlad`, DH23 §9), where the ladder's end atoms have bonds outside the ladder.

---

## §1. Vines (I)–(VIII) and ladders

**Sources.** TARGET Def `defvine` L1384–L1390 and Fig. `Vines.png` (L1391). DH23 Def 5.1 (L790) and Remark 5.2
(L801–L807), whose `Vines.png` is the same figure. The vine (II) annotation is in `vineAnnotated.png` (TARGET L1775,
L1779).

### 1(a) Definition

**Notation.** Templates are **undirected** multigraphs, written as follows:

- `x=y`: a double bond, i.e. two parallel bonds `x—y`;
- `x—y`: a single bond;
- `x⋯y`: a single bond that is a **slot member**.

**Slots.** A **slot** is an ordered pair of slot members `(x⋯y, x'⋯y')`, drawn as two parallel dashed bonds of one
colour.

**Expansion of a slot with k ≥ 0 extra rungs.**

- `k = 0`: keep `x—y` and `x'—y'`.
- `k ≥ 1`: add new atoms `u₁…u_k`, `v₁…v_k` and replace the two slot bonds by:
  - the rail `x—u₁—u₂—…—u_k—y`;
  - the rail `x'—v₁—…—v_k—y'`;
  - the rungs `u_i=v_i` (1 ≤ i ≤ k).

  This is "inserting a ladder with k double bonds", i.e. a TARGET ladder of length k−1, as in the ladder panel of
  `Vines.png`. There, black dashed stubs on both sides of the ladder are the two halves of the cut slot bonds.
- **Crossing is immaterial.** Every slot below has at least one end pair that is swapped by a template automorphism
  fixing everything else. So the crossed rail matching (`x…y'`, `x'…y`) gives an isomorphic graph. Expansions can
  therefore be defined with the parallel matching only.

**Template `T_X(k⃗)`.** This is the template X with slot `s` expanded by `k_s` extra rungs, for each slot s.

**The predicate.** An atomic group 𝕍 of a molecule is a **vine of type X** iff:

- 𝕍 is a block with joints `{v₁, v₂}`; and
- some `k⃗` gives an isomorphism of undirected multigraphs `𝕍 ≅ T_X(k⃗)` that maps `{v₁, v₂}` onto `{J₁, J₂}` (in
  either order).

The joints are unordered in the template. Their order in a garden comes from `block_clcn`, where `𝔲₂` is a
descendant of `𝔲₁`.

**Templates.** I read these from `Vines.png` (and the (VII) crop). The labels are mine; where they differ, the map's
labels are given in brackets. "Bonds" counts parallel bonds.

| Type | Atoms | Bonds (undirected) | Slots | #atoms / #bonds | σ (bonds J₁–J₂) |
|---|---|---|---|---|---|
| (I) | J₁, J₂ | `J₁=J₂` | none | 2 / 2 | 2 |
| (II) | J₁, J₂, a, b, c, d | `J₁—a, J₁—b, a=b, c=d, J₂—c, J₂—d` | red `(a⋯c, b⋯d)` | 6 / 10 | 0 |
| (III) | J₁, J₂, a, b, c, g, h, e, f | `J₁—a, J₁—b, a=b, c—g, c—h, g=h, e=f, J₂—e, J₂—f` | red `(a⋯c, b⋯g)`; green `(c⋯e, h⋯f)` | 9 / 16 | 0 |
| (IV) | J₁, J₂, a, b, c, m, e, f, g | `J₁—a, J₁—b, a=b, c=m, m=e, f=g, J₂—f, J₂—g` | red `(a⋯c, b⋯e)`; green `(c⋯f, e⋯g)` | 9 / 16 | 0 |
| (V) | J₁, J₂, a, b, c, d, e, f, g | `J₁—J₂, J₁—a, J₂—b, a=b, c=d, c—e, d—f, e—f, e=g, f=g` | cyan `(a⋯c, b⋯d)` | 9 / 16 | 1 |
| (VI) | J₁, J₂, a, b, c, d, e, f, x, y, p, q, r, g₁, g₂ [map: h,i = x,y; j,k,m = p,q,r] | `J₁—a, J₁—b, a=b, c=d, c—e, d—x, e=f, f—y, x=y, p—q, p=r, q=r, g₁=g₂, J₂—g₁, J₂—g₂` | red `(a⋯c, b⋯d)`; cyan `(x⋯p, y⋯q)`; green `(e⋯g₁, f⋯g₂)` | 15 / 28 | 0 |
| (VII) | J₁, J₂, a, b, p, q, r, c, d, e, f | `J₁—a, J₁—b, a=b, p=q, p=r, q—r, c—d, e=f, J₂—e, J₂—f` | red `(a⋯c, b⋯d)`; cyan `(q⋯c, r⋯d)`; green `(c⋯e, d⋯f)` | 11 / 20 | 0 |
| (VIII) | J₁, J₂, a, b, p, q, e, f, g, h, i | `J₁—a, J₁—e, a=b, p=q, J₂—p, J₂—q, b—f, e=f, g—h, g=i, h=i` | red `(a⋯p, b⋯q)`; cyan `(e⋯g, f⋯h)` | 11 / 20 | 0 |

**Consistency checks on the templates.**

- **Degrees.** In every template, J₁ and J₂ have degree 2 and every other atom has degree 4. I checked this atom
  by atom. The bond counts follow (`#bonds = (4·#interior + 4)/2`).
- **Atom counts** match TARGET L1515 and L1803: `2m+2` atoms for bad vines and `2m+5` for normal vines, where:
  - for (II), m is the number of rungs (2 in the template);
  - for (III)–(VIII), m is the number of "ladder" pairs. In the templates these are: (III) `a=b, e=f`;
    (IV) `a=b, f=g`; (V) `a=b, c=d`; (VI) `a=b, c=d, e=f, x=y, g₁=g₂`; (VII) `a=b, e=f` plus the
    three-slot pair `(c,d)` (L1803); (VIII) `a=b, p=q, e=f`. The **three remaining atoms** are: (III) `c,g,h`;
    (IV) `c,m,e`; (V) `e,f,g`; (VI), (VII) `p,q,r`; (VIII) `g,h,i`.
  - Each extra rung adds 1 to m.

**Ladder (standalone; TARGET L1384, DH23 L790; used in `layerlad`, DH23 §9).** A ladder of length `m ≥ 1` is an
atomic group:

- atoms `u₀…u_m`, `v₀…v_m`;
- rungs `u_j=v_j`;
- rails `u_j—u_{j+1}` and `v_j—v_{j+1}`;
- **directed** so that for each `j` the two rails `u_j—u_{j+1}` and `v_j—v_{j+1}` have opposite directions.

The rung directions are unconstrained. The end atoms `u₀, v₀, u_m, v_m` may have bonds outside the ladder.

### 1(b) Discrepancies with `maps/T-part2.md` (T-defvine)

- **(VII), cosmetic.** The map has "red dashed (crossed) `a⋯d, b⋯c`". In the figure the red bonds are
  **parallel**: `a⋯c, b⋯d`, where a is the rung atom directly below J₁. The crossing in the picture is between the
  red pair and the **cyan** pair (`b⋯d` crosses `q⋯c`). Swapping `a↔b` maps one to the other, so the graphs are
  isomorphic. Only the transcription is wrong.
- **(I)–(VI) and (VIII):** they agree with the map, up to atom labels.
- **Map's "Atom counts match … (`n_i = 2m_i+1` bad, `2m_i+4` normal, excluding J1)":** correct.
- **Map's Q1 ("the direction of the dashed bonds themselves is unconstrained in the figure"):** resolved by the
  2-cut lemma (§0.3). Inside a vine those directions are forced to be opposite.
- **Map's ladder-insertion reading** ("replacing the two bonds by `x—u₀, x'—v₀`, ladder, `u_m—y, v_m—y'`"): agrees
  with mine. With a ladder of length m this gives `k = m+1` extra rungs. Its consequence (V1) is not noted in the map.

### 1(c) Ambiguities and recommended readings

- **V1. Which numbers of extra rungs per slot are allowed?** Allow k ≥ 0, i.e. DH23's family.
  - TARGET requires ladders to have `m+1 ≥ 2` double bonds (L1384). With insertion as drawn, that gives
    `k ∈ {0} ∪ {2, 3, …}`, and repeated insertion into the same slot gives the same set.
  - DH23 Def 5.1 defines length = (#double bonds) − 1 with **no** lower bound (L790), so it gives k ∈ {0, 1, 2, …}.
    DH23 also speaks of "ladders of length at least one" (L1849), so length-0 ladders are meaningful there.
  - Reasons for k ≥ 0:
    1. TARGET says it *recalls* DH23's definition (L1384, "[DH23]").
    2. TARGET uses DH23's rigidity and counting theorem (`lgmolect` = DH23 Prop 9.6) as a black box, and that
       theorem's exceptional structures are DH23's family.
    3. TARGET's own parametrizations assume no gap. Vine (II) has rungs `(v_{2j+1}, v_{2j+2})` for every
       `1 ≤ j ≤ m_i` (L1775, `vineAnnotated.png` A), and normal vines have "`m_i` pairs" with any `m_i` (L1803).
    4. Nothing in the vine proofs needs k ≠ 1. In `layervine` an inserted single rung is two extra atoms, which go
       into the "< 20 extra atoms" budget, or a single-rung ladder can be handled directly.

    Keep `m ≥ 1` for standalone ladders, as in `layerlad`'s proof (`1 ≤ j ≤ m−1`). **To confirm with the author.**
- **V2. Directions.** Only the block axioms are needed (§0.3). Freeze no extra direction clause in the vine predicate.
- **V3. Template minimality.** The drawn template (all `k_s = 0`) is itself a vine. For (II) it is the smallest
  case, with 2 rungs. The structure "two joints both bonded to the two ends of one double bond" (4 atoms) is **not**
  a vine (II): it is not in the figure, and vine (II) has `m_i ≥ 2` rungs in TARGET L1775 with the template m = 2.
- **V4. Joint order.** Unordered in the definition. (V) and (VIII) are not symmetric under `J₁ ↔ J₂`, so the
  isomorphism decides which joint is which template joint. Statements that need `𝔲₂` to be a descendant of `𝔲₁`
  take that from the garden, not from the template.
- **V5. Groups (`cohmol`, L1489).** These should be part of the template data, as a partition of the non-joint atoms:
  - (II), and all inserted rungs: each rung is a group;
  - (III), (V), (VI), (VII), (VIII): the three remaining atoms listed above form one group;
  - (IV): `{c, m, e}`;
  - (VII): also `{c, d}`.

  The map's reading ("unique triangle containing no joint") agrees.

### 1(d) Lean shape

- An inductive `VineType` with eight constructors.
- For each type, a fixed `Fin n` template (adjacency multiset), its joint pair, its slots, and its groups.
- `expand : template → (slot → ℕ) → multigraph`.
- `IsVine (𝕍 : AtomicGroup M) (X : VineType) : Prop :=`
  `IsBlock 𝕍 ∧ ∃ k, Nonempty (UndirIso 𝕍 (expand X k))` with joints preserved as a set.
- Prove the 2-cut and direction facts as lemmas. Use `decide` on the templates for the degree and count facts.

---
