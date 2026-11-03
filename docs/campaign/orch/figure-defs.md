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
## §2. Blocks and vines inside gardens: (CL)/(CN), splicing, (I-a,b), (II-a…e), free children

**Sources.** TARGET `block_clcn` (L1342), `Couples_CL.png` (L1356), `Couples_CN.png` (L1361), `molecpl` (L1396–L1418),
`Block_Mole.png` (L1417). DH23 Prop 4.12 and Prop 5.3.

### 2(a) Definition

These objects are **defined in the text**. The figures illustrate them, and I checked that each figure is consistent
with the text.

**Sign rule (TARGET L627).** A node of sign ζ has children of signs `(ζ, −ζ, ζ)` in positions (L, M, R). Paired leaves
have opposite signs. Bond directions in 𝕄(𝒢) follow L1297: a PC bond points towards the child iff the child has sign
−; an LP bond points from the node whose paired child has sign − to the node whose paired child has sign +.

**(CL) and (CN) blocks.** Exactly as in `block_clcn` (1)(a) and (1)(b). `Couples_CL.png` and `Couples_CN.png` agree.

**Splicing (`block_clcn` (2)) is well defined.**

- 𝔲₁₁ has the sign of 𝔲₁, so it sits at L or R.
- After the realization is removed, 𝔲₁ has one free same-sign slot (the other of L/R) and the M slot.
- 𝔲₂₁ (sign +) and 𝔲₂₂ (sign −) go to the slot of their own sign, which is a unique placement.
- `Couples_CL.png` shows exactly this: 𝔲₁ of sign + gets 𝔲₂₁ at L, 𝔲₂₂ at M, and 𝔲₁₁ at R.

**Vine (I) in a garden** (from `Block_Mole.png` and the text). 𝔲₂ is a child of 𝔲₁. 𝔲₂₃ is the child of 𝔲₂ with
sign ζ(𝔲₂), at L or R. 𝔲₀ is a child of 𝔲₁ and is paired with 𝔲₂₃. 𝔲₁₁ is the third child of 𝔲₁ (free, with subtree
𝒯₃).

- **(I-a):** 𝔲₂ is at the L/R slot not taken by 𝔲₁₁, and 𝔲₀ is at M.
- **(I-b):** 𝔲₂ is at M, and 𝔲₀ is at the free L/R slot.
- The molecule is `v₁ = v₂`, with one LP bond and one PC bond (P at v₁, C at v₂), matching the figure.

**Vine (II) at the joint v₂** (from the text, with the figure as one instance; the caption says "positions may vary").
v₂ is bonded to v₃ and v₄, which are joined by a double bond. Write 𝔲ⱼ = 𝔫(vⱼ).

- **(II-a):** 𝔲₂ is a child of 𝔲₄; 𝔲₀ is a child of 𝔲₃ paired with 𝔲₂₃; the other two children of 𝔲₄ are paired
  with the other two children of 𝔲₃; 𝔲₃ and 𝔲₄ are incomparable.
- **(II-b):** the same with 𝔲₃ and 𝔲₄ exchanged.
- **(II-c):** 𝔲₄ is a child of 𝔲₃ and 𝔲₂ is a child of 𝔲₄; one remaining child of 𝔲₃ is paired with a remaining child
  of 𝔲₄; 𝔲₀ is the last child of 𝔲₃, paired with 𝔲₂₃.
- **(II-d):** 𝔲₂ and 𝔲₄ are both children of 𝔲₃; 𝔲₀ is a child of 𝔲₄, paired with 𝔲₂₃; the remaining child of 𝔲₃
  is paired with a remaining child of 𝔲₄.
- **(II-e):** 𝔲₂ is a child of 𝔲₃; 𝔲₄ = 𝔲₂₃ (in the figure at L of 𝔲₂); the other two children of 𝔲₃ are paired with
  two children of 𝔲₄.

**Free children** (the white nodes of the figure):

- 𝔲₂₁ and 𝔲₂₂ in every core case;
- also 𝔲₁₁ (𝒯₃) in (I-a) and (I-b);
- also the child of 𝔲₄ that is neither 𝔲₂/𝔲₀ nor paired with 𝔲₃, in (II-c) and (II-d);
- none in (II-e).

**Core** means bad and not (II-e).

I checked every panel of `Block_Mole.png` against the sign rule: every pairing joins opposite signs, and 𝔲₂₃ is
always an L/R child of 𝔲₂. The P/C/LP labels on the molecule triangles match L1297.

### 2(b) Discrepancies

- **Map T-molecpl:** consistent with the TeX and the figure, including the free-children list and "(I) bonds = one LP
  and one PC (P at v₁, C at v₂)".
- **Notation clash, cosmetic.** `Couples_CL.png` names the subtrees 𝒯₁ at 𝔲₁₁, 𝒯₂ at 𝔲₂₁ and 𝒯₃ at 𝔲₂₂.
  `Block_Mole.png` and Def `twist` use 𝒯₁ at 𝔲₂₁, 𝒯₂ at 𝔲₂₂, and 𝒯₃ for the third free child. Lean names should
  not reuse the 𝒯ⱼ indices.
- **Not compared:** DH23's own `Block_Mole.png` and `twist_dec.png`, which have different files (hashes), drawn for
  couples. TARGET's versions are the ones used.

### 2(c) Ambiguities and recommended readings

- **G1. (II-a) versus (II-b) is a labelling convention.** "Up to symmetry" (L1402) leaves v₃ and v₄ unlabelled.
  - In (II-c), (II-d) and (II-e) the labels are intrinsic: 𝔲₃ is the parent of 𝔲₄, or the parent of 𝔲₂.
  - In (II-a) and (II-b), swapping the names v₃ ↔ v₄ turns (II-a) into (II-b).
  - The unit twist preserves the directed molecule (`twistexplain` (a)), so a meaningful a/b distinction needs a
    labelling fixed on the **directed molecule**. For example, v₃ is the neighbour of v₂ whose bond to v₂ points
    into v₂. With such a labelling the twist swaps (II-a) ↔ (II-b).
  - **Recommendation:** in Lean use a single class "(II-ab): 𝔲₃ and 𝔲₄ incomparable". Nothing in TARGET uses a/b
    except as twist partners (`explaintwist`, `lftwistprop`).
- **G2. "Exactly one of the five" (DH23 Prop 5.3).** This is a theorem, to be proved. It is not part of the
  definition.

### 2(d) Lean shape

- Ordered ternary trees with `Fin 3` child slots and the sign rule.
- `IsCLBlock` and `IsCNBlock` as predicates on (garden, block, joint assignment).
- `splice` as a function, together with the lemma that placement by sign is well defined.
- An inductive `BadConfig := Ia | Ib | IIab | IIc | IId | IIe`, characterised by parent and pairing relations among
  `𝔲₁…𝔲₄, 𝔲₀, 𝔲₂₃`.

---

## §3. Unit twists, twists, LF twists, congruence (F20)

**Sources.** TARGET Def `twist` (L1429–L1434), Remarks `explaintwist` and `twistexplain` (L1436–L1455),
`twist_dec.png` (L1457), Def `lftwist` (L1466–L1480), Prop `lftwistprop` (L1481–L1488), Def `defcong` (L1934–L1936).

### 3(a) Definition: the case table that F20 asks for

**Slots.** For a core (CL) vine, let:

- A be the slot (parent `P_A`, position) occupied by 𝔲₂;
- B be the slot (parent `P_B`, position) occupied by the leaf 𝔲₀ paired with 𝔲₂₃.

Then:

| Type | `P_A` | `P_B` | Unit twist gives |
|---|---|---|---|
| (I-a) | 𝔲₁, position = the L/R slot not occupied by 𝔲₁₁ | 𝔲₁, position M | (I-b) |
| (I-b) | 𝔲₁, M | 𝔲₁, the free L/R slot | (I-a) |
| (II-a) | 𝔲₄ | 𝔲₃ | (II-b) |
| (II-b) | 𝔲₃ | 𝔲₄ | (II-a) |
| (II-c) | 𝔲₄ | 𝔲₃ | (II-d) |
| (II-d) | 𝔲₃ | 𝔲₄ | (II-c) |

**The unit twist τ_𝕍(𝒢)**, uniform for all six cases:

1. Move the subtree rooted at 𝔲₂ to slot B, and put a leaf at slot A. That leaf becomes the new 𝔲₀.
2. Inside the moved subtree:
   - 𝔲₂₃ keeps its position (L or R);
   - 𝒯₁ is placed at the remaining slot of sign +, and 𝒯₂ at the remaining slot of sign −. So 𝒯₁ and 𝒯₂ keep their
     root signs and their internal structure, and they swap positions.
3. 𝔲₂₃ is paired with the new leaf at A.
4. Every other node, position and pairing is unchanged.

**Lemmas** (elementary; to be proved, not assumed):

- **(i)** `sign(A) = −sign(B)`. This holds because 𝔲₂₃ (sign = sign(A)) is paired with 𝔲₀ (sign = sign(B)). Hence
  ζ(𝔲₂) flips, which is `twistexplain` (b).
- **(ii)** τ_𝕍(𝒢) is a garden whose molecule is the same directed graph, with labels changed only at v₂
  (`twistexplain` (a)).
- **(iii)** Under Def `twist`'s constraints, (1) "relations between 𝔲₃ and 𝔲₄ kept", (2) "outside the subtrees at
  𝔲₃, 𝔲₄ (or at 𝔲₁) kept" and (4) "𝒯₃ kept", the slots available for 𝔲₂ and the leaf are exactly {A, B}. This is
  L1431's "exactly two options".
- **(iv)** τ_𝕍 is an involution and exchanges the types as in the table, which is the last line of `explaintwist`.

**Figure check (`twist_dec.png`).** In (II-c), `k_{𝔲₂} = x` and `k_{𝔲₂₃} = y`. In (II-d), `k_{𝔲₂} = y` and
`k_{𝔲₂₃} = x`. The children of 𝔲₂ appear in the order `(e, f)` in (II-c) and `(f, e)` in (II-d). This is exactly
`twistexplain` (d), and agrees with the rule above: the new leaf at A carries the old `k_{𝔲₂}`.

**Recommendation:** freeze the unit twist as this explicit slot swap. Def `twist`'s indirect description, "the other of
two options", then becomes lemma (iii).

### 3(b) Discrepancies with the maps

- **T-twist: the case table is missing (Q2).** It is supplied above.
- **T-lftwist issue (1)** ("LF twist must include 'or none'; implicit"). This is **already explicit** in TARGET: L1473
  says "To form 𝒢′, starting from **either 𝒢_sk or 𝒢_sk′**". Starting from 𝒢_sk, with 𝒯′ = 𝒯 and 𝒬′ = 𝒬, gives the
  identity, and those choices satisfy the three bullets because 𝒢 is canonical and they are coherent.
- **T-lftwistprop (Q3; F20 "only (II-a)→(II-b) checked").** With the uniform slot swap, the canonicity check is the
  same for every case:
  - *Parent–child monotonicity.* The only changed edge is `P_A–𝔲₂` versus `P_B–𝔲₂`. For (I) both parents are 𝔲₁.
    For (II), `𝔏_{𝔲₂} ≤ min(𝔏_{𝔲₃}, 𝔏_{𝔲₄})` covers both.
  - *`canonequiv` for completely paired pairs (𝔫, 𝔫′).* Only pairs involving 𝔲₂, 𝔲₀, 𝔲₂₃ or a common ancestor of
    `P_A` and `P_B` change. The (II-a) argument at L1488 transfers verbatim.

  So F20's case gap reduces to writing that argument once for a generic (`P_A`, `P_B`).

### 3(c) Ambiguities and recommended readings

- **T1. Twists at a family `{𝕍ⱼ}`.** Def `twist` says "unit twists at a subset of these blocks, which only contains
  core vines", and claims the number of twists is "a power of two, at most 2^q". This silently needs three facts:
  1. unit twists at distinct vines commute;
  2. a unit twist at 𝕍ᵢ preserves the core (CL) status of every other 𝕍ⱼ;
  3. distinct subsets give distinct gardens, which is needed only for "power of two".

  I checked (2) for a vine chain sharing the joint `v₂ⁱ = v₁ʲ`. The realization of 𝕍ⱼ lies in 𝒯₁ ∪ 𝒯₂ of 𝕍ᵢ, and
  `𝔲₁₁ʲ = 𝔲₂₃ⁱ`, which keeps the sign of 𝔲₂ⁱ. So 𝕍ⱼ stays (CL) and core. If 𝕍ⱼ is a vine (I) whose 𝔲₂ʲ is 𝔲₂₁ⁱ or
  𝔲₂₂ⁱ, then its (I-a)/(I-b) type flips.

  **Recommendation:** define the twist class as `{τ_S(𝒢) : S ⊆ core vines of 𝒢}`, with core-ness evaluated in 𝒢, and
  state (1)–(3) as lemmas. The proofs only sum over the class as a set, so (3) is not needed.
- **T2. LF assumption for vine (I).** "`𝔏_{𝔲₂} ≤ min(𝔏_{𝔲₃}, 𝔏_{𝔲₄})`" is required, but (𝔲₃, 𝔲₄) are absent for
  (I) (L1470). **Recommendation:** vacuous for (I). The relevant inequality `𝔏_{𝔲₂} ≤ 𝔏_{𝔲₁}` already holds, since
  𝔲₂ is a child of 𝔲₁ in both (I-a) and (I-b).
- **T3. Family LF twists and congruence (`defcong`).**
  - *Applicability.* Evaluate the conditions (core; `𝔏_{𝔲₂} ≤ min(…)`; 𝒯_(𝔲₂) and 𝒬_(𝔲₂₃,𝔲₀) coherent) in 𝒢.
    Different vines own disjoint replaceable data (𝒯_(𝔲₂ʲ), 𝒬_(𝔲₂₃ʲ,𝔲₀ʲ)).
  - *Equivalence relation.* "Clearly … congruence is an equivalence relation" (L1936) needs:
    - **(a)** 𝒱 depends only on `𝕄(𝒢_sk)` plus data that LF twists preserve. This includes the "top" vine
      (ancestry of 𝔲₁ nodes) and (CL)/(CN) status. That is plausible because only 𝔲₂-subtrees move, between two
      children of nodes inside the same vine, but it is not stated.
    - **(b)** *Symmetry.* The conditions hold again in 𝒢′: layers are unchanged, 𝒯′ and 𝒬′ are coherent by bullet 2,
      and core-ness is preserved.
    - **(c)** *Transitivity.* Two unit LF twists at the same vine compose to one. The skeleton twist is an involution,
      and the order-sum and layer-p-count constraints compose.

    These are three lemmas for the Wave B prover packet (F20).

### 3(d) Lean shape

- `unitTwist (𝒢) (𝕍) (h : IsCoreCL 𝕍) : Garden`, defined by the slot swap.
- `IsLFTwist 𝒢 𝒢' : Prop`, existential over the choices (start from 𝒢_sk or 𝒢_sk′; 𝒯′, 𝒬′).
- Lemmas (i)–(iv), T1 (1)–(2), T3 (a)–(c).

---

## §4. Cuts

**Sources.** TARGET Def `defcut` (L2117–L2123), the following Remark (degree-2 cuts), and `Cut.png`. DH23's
`Cut.png` is byte-identical (same md5).

### 4(a)–(b) Definition and discrepancies

The cut is defined in the text. The figure is a degree-4 instance: ℓ₁ in and ℓ₂ out go to v₁; ℓ₃ out and ℓ₄ in go to
v₂. The map's transcription agrees.

### 4(c) Ambiguity

**C1. Self-loops.** Molecules from gardens have a loop at 𝔫 whenever two children of 𝔫 are paired (L1297 (ii) with
𝔫₁ = 𝔫₂), and prime skeletons can contain such loops (F21). "The endpoint v of ℓ₁ is moved to v₁" is ambiguous when ℓ₁
is a loop.

**Recommendation:** represent molecules with **half-edges (darts)**. A cut along (ℓ₁, ℓ₂) moves the dart of ℓ₁ that is
incoming at v and the dart of ℓ₂ that is outgoing at v (or vice versa) to v₁. This is well defined for loops and
agrees with the figure otherwise.

### 4(d) Lean shape

Molecules as dart structures, with `cut v d₁ d₂`, and α/β determined by the change in the number of components.

---

## §5. (1,1)-mini-couples, mini-trees, operations A and B, colour conventions (F12)

**Sources.** TARGET Def `defreg` (L826), `MiniCpl.png`, `MiniTree.png`, `OperAB.png`. DH21 Def 4.1 (`defmini`)
and Def 4.2. TARGET's and DH21's PNG files differ, but I compared them and their content is identical code by code.
The colours are used in `propstructure` (L855: red/green/blue ↦ 𝒬₁, 𝒬₂, 𝒬₃; red/green ↦ ι = 1, 2) and in the
code-dependent formula `regref3-4` (L1222–L1227).

### 5(a) Definition

**(1,1)-mini-couple.** Two order-1 trees T and T′ of opposite signs, with leaves `(L, M, R)` and `(L′, M′, R′)`, and
no siblings paired.

- Opposite signs force the pairing `M ↔ M′`.
- **Code 00:** `L ↔ L′, R ↔ R′`.
- **Code 01:** `L ↔ R′, R ↔ L′`.
- These are the only two possibilities: L can pair only with L′ or R′.
- **Colours:** red is the pair containing L, green is `{M, M′}`, blue is the pair containing R, where L and R are the
  leaves of the **first** tree T.

**Mini-tree.** A root ρ of sign ζ with a branching child ν at position `c ∈ {1, 2, 3}` (L, M, R). The two leaf children
of ρ are each paired with a child of ν. The remaining child of ν is the **lone leaf** (black in the figure). No siblings
are paired.

| Code | ν at | Pairs (ρ-child ↔ ν-child) | Lone leaf | red pair / green pair |
|---|---|---|---|---|
| 10 | L | `M↔R`, `R↔M` | ν-L | red = (ρ-M, ν-R), green = (ρ-R, ν-M) |
| 11 | L | `M↔L`, `R↔M` | ν-R | red = (ρ-M, ν-L), green = (ρ-R, ν-M) |
| 20 | M | `L↔L`, `R↔R` | ν-M | red = (ρ-L, ν-L), green = (ρ-R, ν-R) |
| 21 | M | `L↔R`, `R↔L` | ν-M | red = (ρ-L, ν-R), green = (ρ-R, ν-L) |
| 30 | R | `L↔M`, `M↔L` | ν-R | red = (ρ-L, ν-M), green = (ρ-M, ν-L) |
| 31 | R | `L↔M`, `M↔R` | ν-L | red = (ρ-L, ν-M), green = (ρ-M, ν-R) |

**Properties of the table.**

- **It is exhaustive.** I enumerated every sign-legal choice; for each position of ν there are exactly 2. The lone leaf
  always has sign ζ.
- **Colour rule:** red is the pair containing ρ's **leftmost leaf child**, green the other pair. This is confirmed
  independently by `regref3-4`: for c = 1 the red class sits at k₂ and the green at k₃; for c = 2 at (k₁, k₃); for
  c = 3 at (k₁, k₂). These are exactly ρ's leaf positions in left-to-right order.
- Only the first digit `𝚌` enters the formulas. The second digit only distinguishes shapes.

**Operation A.** A leaf pair is replaced by a (1,1)-mini-couple: each leaf becomes the root of one of the two order-1
trees, which forces their signs.

**Operation B.** **Any** node 𝔫, leaf or branching, is replaced by a mini-tree. The mini-tree root takes 𝔫's place
(same sign, hence a legal tree), and the lone leaf *is* 𝔫, keeping 𝔫's subtree if 𝔫 is branching, or 𝔫's pairing if 𝔫
is a leaf.

- `OperAB.png` shows (Y) below the node, and DH21 Def 4.2(2) says "replacing a node".
- B at a leaf is needed: the (2,0)-mini-couple (mini-tree, •) arises from × by B at a leaf.

### 5(b) Discrepancies

- **T-part1 map** (`T-defreg` note and Q9) reads the first digit as the position of the inner node and the second as
  "which of the two pairings". That is correct, and the table above makes it precise.
- **DH21 map** (`DH21-defmini`) says "this reading is inferred". It is now verified against both papers' figures.
- No discrepancies with the figures.

### 5(c) Ambiguity

**M1. Which tree is "first" in a (1,1)-mini-couple?** This matters only for the red/blue labels of code 01, where
swapping the trees swaps red and blue. Codes and green do not depend on it. The figures put the first tree on the
left; `RegChain.png` puts 𝒳⁺ on the left.

**Recommendation:** first = the tree of sign + (`𝒬 = (𝒯⁺, 𝒯⁻)`). For operation A at a pair (𝔩, 𝔩′), the first tree
replaces the leaf of sign +.

The type-1 formula `∫∏ⱼ 𝓜*_{𝒳ⱼ}(kⱼ) δ(k₁−k₂+k₃−k) δ(Ω)` is symmetric under (𝒳₁, k₁) ↔ (𝒳₃, k₃), so values do not
depend on this choice. Uniqueness statements and equivalence-class tuples do, so it must be fixed.

### 5(d) Lean shape

- `MiniCode : Fin 2` and `MiniTreeCode : Fin 3 × Fin 2` as explicit finite data (the table above).
- `opA` and `opB` as garden operations.
- `IsRegular` as an inductive predicate.
- Colour projections `red`, `green`, `blue` as functions of the code.

---

## §6. Regular chains (and their mini-tree rearrangement)

**Sources.** TARGET Def `defregchain` (L848–L850), `propstructure` (L852–L863), `RegChain.png` (L863),
`layerreg1` (L899), `LayerRegChain.png` (L905).

### 6(a) Definition

This is textual (`defregchain`). Write 𝔫_{2m+1} for the lone leaf, and let `s_j` be the slot of 𝔫_{j+1} under 𝔫ⱼ.

For a pair `{a, b}` of the legal partition, the "rearrangement into a mini-tree" is the mini-tree consisting of:

- root 𝔫ₐ;
- 𝔫_b placed at slot `s_a` (the slot of 𝔫ₐ's chain child);
- lone leaf at slot `s_b`;
- 𝔫ₐ's two other children and 𝔫_b's two other children, with their chain pairings.

Its code, read from the §5 table, defines `𝚌_{j,ε}` and the red/green labelling of `𝒬_{j,ε,ι}`.

**Figure check.** In `RegChain.png`, the dominant chains are 𝒳⁺ = codes 10, 10 and 𝒳⁻ = codes 30, 30, with
`𝒬_{j,ε,1}` on the red-role pair and `𝒬_{j,ε,2}` on the green-role pair. Both are consistent with §5.
`LayerRegChain.png` illustrates `layerreg1` and is consistent with its text.

### 6(b)–(c) Discrepancies and ambiguities

- None beyond §5's M1.
- "Some specified child of 𝔫_{2m} is the lone leaf" is part of the data.

---

## §7. Flower trees and flower gardens (F26)

**Sources.** TARGET Def `defflower` (L2259–L2262), the (Y)/(W) conditions (L2272), `Flowertree.png` (L2275). DH23's
`Flowertree.png` is byte-identical.

### 7(a) Definition

This is textual: a flower tree is a ternary tree with a marked leaf 𝔣, and the stem is the path from the root to 𝔣.
The figure only illustrates the order conditions.

I checked the caption against the text:

- (Y-2) for the stem child of 𝔯 is `m − 1 − n₁′ − n₂′ ≤ N`, i.e. `m ≤ N + n₁′ + n₂′ + 1`.
- (W-3) is `m − 1 − n₁ − n₂ ≤ N`.
- Both agree with the caption and give `m ∈ [N+1, 3N+1]`.

The map's transcription (T-defflower) agrees.

### 7(c) Ambiguity (outside figure scope, flagged for the F26 analytic audit)

The kernel `jtflower` contains `δ(t_{𝔣^pr} − s)`, so every flower tree in `𝒳` has order ≥ 1, and `𝒳` contains no
identity term. The identities `(1−ℒ₁)𝒳 = 1+𝒴` and `𝒳(1−ℒ₁) = 1+𝒲` (L2271) then need checking: the "1" must come from
somewhere. Possibly the intended parametrix is `1 + 𝒳`. Compare DH21 §11 and DH23 §11.1.1 before freezing.

---

## §8. Layered gardens and canonical layered gardens

**Sources.** TARGET Def `deflayer` (L645–L653), `defcanon` (L657–L667), `LayerGarden.png`, `CanonGarden.png`.

Both definitions are textual, and the figures are a worked example. I verified the example:

- The tree signs `(+, −, +, −)` and all seven pairings respect the sign rule.
- Layers are monotone along every parent–child edge, and paired leaves share a layer.
- The decomposition `𝒢 ∈ 𝒢₃ → 𝒢′ ∈ 𝒢₂ → 𝒢″ ∈ 𝒢₁` follows `defcanon`. At depth 3 the leaf subsets are
  {red pair}, {magenta pair} and one six-element subset replaced by 𝒢′. At depth 2 they are {green}, {blue} and one
  four-element subset replaced by 𝒢″. At depth 1 everything is pairs, consistent with 𝒢₀ = ∅.

No discrepancies and no figure-dependent content.

---
## §9. F14 — DH21-2 Prop 6.3 (`basemol`: χ ≤ m − R/2 for mixed gardens)

**Sources.** DH21-2 `WKE_Hierarchy-Revised.tex`: Def `defgarden` (L606–L609, "multi-couple", "mixed"), Def
`gardenmol` (L809–L817), Prop `basemol` (L818–L823), Prop `reconstruction` (L824). DH21 map E5.

### Verdict: the counterexample is invalid; Prop 6.3 is true; TARGET does not depend on it

**1. The map's counterexample is not a mixed garden.** The example is:

- T₁(+) with leaves (a, b, c), pairs `a–b` and `c–(root of the trivial tree T₂(−))`;
- T₄(−) with leaves (d, e, f), pairs `e–f` and `d–(root of the trivial tree T₃(+))`.

The leaf set of T₁ ∪ T₂, namely `{a, b, c, r₂}`, is closed under the pairing. So (T₁, T₂) is a **couple** (a width-2
garden; couples may pair siblings), and likewise (T₄, T₃). The garden is therefore a **multi-couple**, and DH21-2
L609 defines mixed as "no two trees `𝒯_j`, `𝒯_{j′}` have all their leaves paired with each other". The computation
χ = 2 > 1 is correct, but the hypothesis "mixed" fails.

**2. Prop 6.3 is true as stated**, including when trivial trees are present. The proof's sentence "any connected
component must be the union of at least four `S_j`" is loose, because `S_j = ∅` for trivial trees, but it repairs
directly:

- For a component C, let `A_C` contain:
  - the non-trivial trees whose atoms lie in C (each `S_j ≠ ∅` is connected, so it lies in one component);
  - the trivial trees whose root is paired with a leaf of one of those trees.
- Mixedness forbids two trivial roots from being paired with each other, so every tree belongs to exactly one `A_C`.
- The leaves of `A_C` are closed under pairing. An LP partner of an atom-leaf is either in an atom of C or a trivial
  root assigned to C.
- So `|A_C|` is even, since each tree has an odd number of leaves. It is not 2, since that would be two trees "with all
  their leaves paired with each other", contradicting mixedness. Hence `|A_C| ≥ 4`, and `F ≤ 2R/4 = R/2`.
- I also re-derived `E = 2m − R` with trivial trees. There are `m − R_nt` non-root branching nodes and
  `(m + R) − R_t` LP bonds with both leaves non-root, where `R_t = 2R − R_nt`. Hence `χ ≤ m − R/2`. ∎

**3. TARGET does not use Prop 6.3.** I checked every `[DH21-2]` citation (L268–L669 introduction and set-up, L848,
L872, L1294–L1308, L2630 bibliography):

- **Substantive uses:**
  - L872 `propstructure2` (skeleton decomposition of gardens) uses DH21-2 Props 4.4–4.6;
  - L1306 `propcplmol` (number of gardens with a given molecule ≤ `(C₀R)!C₀^n`) uses DH21-2 Prop 6.4
    (`reconstruction`), whose proof (an encoding by position codes 0–3) does not use 6.3.
- **Definitions only:** L1294–L1308 (molecules, decorations; TARGET gives self-contained definitions).
- **Introduction only:** L370 ("it follows from the proof in [DH21-2] that |(introcm)| ≤ L^{−cr}") is motivation,
  and the next sentence calls it "too weak". TARGET proves its own cumulant bounds (`propansatz`).
- **Not part of Theorem 1.1:** L327 (Remark `suppresult`: higher statistics "using the same arguments in [DH21-2]").
- TARGET's own χ statement for irreducible gardens (`propcplmol`: `χ = n − R + 1`, connected) is proved in TARGET
  (L1304–L1306). TARGET's irreducible gardens of width ≥ 4 are mixed anyway.

**Consequences.**

- F14 can be closed as **not a defect** of DH21-2 Prop 6.3 and **not a dependency** of TARGET.
- The other half of E5, about DH21-2's (contribution1) summation range, concerns DH21-2's own proof of its Theorem
  1.3 and is likewise outside TARGET's dependency graph.
- E10 (mixed versus irreducible) is moot for TARGET for the same reason: L370 is motivational.
