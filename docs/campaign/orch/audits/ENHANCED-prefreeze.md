# Pre-freeze statement audit: ENHANCED (packet C5, wt-torus)

Auditor: `wt-orch`, refute-first, findings only. Date: 2026-11-04 (Task 24a).

**Scope.**
- The exported statements of `/home/scott/wt-scratch/enhanced` against:
  - DH21 Defs 4.17–4.22 and Props 4.20 and 4.23 (`defstd`, `equivcpl`, `encodedtree`/`codechain`, `structure+`,
    `equcodetree`, `cpl-tree`, `bijection`; L854–L898) and the summary §4.4.5 (L899–L911);
  - TARGET Defs 6.4–6.5 (`defencpl`, `defentree`; L1126–L1143).
- The packet's readings R1–R8.
- Whether the statements are about the current B2 definitions.

## Verdict

**PASS.** No BLOCKER and no REQUIRED finding. Two OPTIONAL observations (E-1, E-2) and one consumer item
(E-3, the `ζ*` bridge, already open in the packet).

- **Statements.** Every audited statement matches its source, in places in a stronger form.
- **Readings.** R1–R8 are all acceptable.
- **Currency.** The statements' closure over B1, B2 and Wave A is identical to the current definitions (§3).

## 1. Inputs and pins

**Pin.** `/home/scott/wt-scratch/enhanced`: 18 files hashed at 03:13:47 UTC (digest `6299505351218423…`).
Re-verified unchanged at 03:26 UTC.

**Packet build.** The packet's `build-final/` sits on LINKS' `build-final/` (both read-only on `LEAN_PATH`). Its B2
input is LINKS' copy of Regular (`ad72ce4b…`). The current definitions are those of the LINKS audit §1.

## 2. Statements against the sources

**DH21 Def 4.17 (dominant).**
- `dominant_iff_source : Q.dominant = true ↔ DominantSrc Q`. `DominantSrc` is Def 4.17 written as a recursion:
  - type 1: all `𝒬_j` dominant;
  - type 2: both chains dominant and all sub-couples dominant.
- `partition_dominant_iff`: a chain is dominant iff its legal partition is `{{1,2}, …, {2m−1, 2m}}`.
- `chain_dominant_iff_source`: the same for chains.
- **Faithful.** This validates B2's freeze candidates `RegCpl.dominant` and `RegChain.dominant`.

**Special subsets.**
- `isSpecialSet_iff` / `mem_specialSets_iff`: B2's `IsSpecialSet` / `specialSets` (TARGET `defencpl`: "the node
  linked with `𝔫` is a child of `𝔫`") ⇔ every `z ∈ Z` is one of DH21's recursive candidates `cplSpecial` (the
  (unionz) description).
- `root_not_mem_specialList`: a type-1 root is never special.
- TARGET's definition and DH21's coincide. **Faithful.**

**Equivalence (DH21 Def 4.18; TARGET Def 6.4).**
- `EnhCpl` is a code with `wf`, `dominant` and `Z ∈ specialSets`. Its setoid is `Shape.Equiv` of the shapes.
- `Shape.Equiv` has three constructors:
  - `triv` only with `triv`, and the types never mix;
  - `type1`: the three sub-shapes equivalent, in order;
  - `type2`: a bijection `e` of tuple positions with equal `𝙸`, equal `𝚌` and equivalent sub-objects, plus
    equivalent tails. That is "(ii) a permutation of the tuples (iii) `𝒴 = 𝒴'`", with (i) `m₊ + m₋ = m₊' + m₋'`
    implied by `e`.
- The inversion lemmas `cplShape_type1_equiv_iff` / `cplShape_type2_equiv_iff` state these clauses on codes:
  - type 1 places `𝒬₂` with its `+` tree at `b·[1]`, the middle child of the `−` root, which has sign `+`;
  - the order red, green, blue follows the `+` tree (DH21 Def 4.11 Case 1).
- The invariants `size_eq_of_equiv` and `card_eq_of_equiv` are the definition's closing claims.
- **Faithful.**

**TARGET Def 6.4 (layered).** `LayEnhCpl.setoid`: same layer ∧ DH21 equivalence. When all nodes are in one layer,
TARGET's recursion compares sub-objects in that same layer, so this is the literal definition. See R4.

**TARGET Def 6.5 (trees).**
- `LayEnhTree.equiv_iff`: same layer ∧ a bijection of the chain tuples with equal `𝙸`, equal `𝚌` and equivalent
  sub-couples.
- This is TARGET's "same layer, and the tuples form a permutation" (there is no tail for trees).
- **Faithful.** See E-1 on the root sign.

**DH21 Defs 4.19–4.21 (encoded trees).**
- `EncTree` is a ternary tree with codes `c0…c3` at branching nodes.
- `canonPath` / `IsChain` follow L874 and Def 4.19 (`codechain`).
- `EncTree.setoid` is `Shape.Equiv` of `EncTree.shape`. Per `shape_node_c0` and `shape_type2`:
  - code 0 gives type 1 with its three subtrees;
  - a canonical-path chain gives type 2 with triples `(𝚌, 𝒵₁, 𝒵₂)` and the tail.

  This is Def 4.21 (`equcodetree`).

**DH21 Prop 4.20 (`structure+`).**
- `EncTree.structure_plus T`, for `T` of type 2:
  - the spine is non-empty;
  - its tail is `•` or of type 1;
  - `build spine.1 spine.2 = T`;
  - every `(L, t)` with `t` a tail and `build L t = T` equals the spine.
- This is existence plus uniqueness of `𝒯₀` (with its replacements), in the rebuild form of R6. The uniqueness is
  stronger than the source's, which concerns `𝒯₀` only.
- **Faithful.**

**DH21 Def 4.22 (`cpl-tree`).** `cplEnc`:
- `triv ↦ •`;
- type 1 ↦ a code-0 node over `𝒬₁, 𝒬₂, 𝒬₃`;
- type 2 ↦ the `+` chain, then the `−` chain (`chainEnc Xp (chainEnc Xm (cplEnc Qlp))`), with the red and green
  trees off the path and `𝒬_lp`'s tree at the tail.

This is the source's ordering ("`ε = +` triples before `ε = −`, increasing `j`"). **Faithful.**

**DH21 Prop 4.23 (`bijection`).**
- `cplEnc_surjective : ∀ T, ∃ q : DomCpl, cplEnc q = T`, where `DomCpl = {Q // wf ∧ dominant}`.
- `domCpl_equiv_iff_enc : q ≈ q' ↔ cplEnc q ≈ cplEnc q'`.
- `domClassEquiv : Quotient DomCpl.setoid ≃ Quotient EncTree.setoid`.
- **Faithful** for well-formed dominant codes. With REG-STRUCT (codes ↔ carriers) this is DH21's statement for
  couples.

**DH21 §4.4.5 (2) (net signs).**
- `EncTree.netSign` is (defzetat) `∏_𝔫 (−1)^{𝚌_𝔫}`, with `codeSign`: `𝚌 = 1, 2, 3 ↦ −1, +1, −1` and code 0 ↦ 1.
- `zeta_eq_netSign` / `zeta_eq_netSign_cplEnc`: B1's `Garden.zeta` (DH21 (defzetaq) `∏(iζ_𝔫)`) of the decoded
  carrier equals the shape's or encoded tree's net sign.
- `Shape.Equiv.netSign_eq` and `EncTree.netSign_eq_of_equiv`: the sign is invariant under equivalence.
- **Faithful.**

**PL1, tree version of incohproof1** (`tree_incoh_unimodular`, …). Outside the source list. Axioms only (§4).

## 3. Are the statements about the current B2 definitions?

I ran the same closure comparison as in `LINKS-prefreeze.md` §3, from the 43 principal statements of
`check/Check.lean`. Result: 100 B1, B2 and Wave A constants, **100 identical, 0 different, 0 missing**. The
statements are therefore about the current B2 (`dominant`, `links`/`linksAt`, `IsSpecialSet`, `specialSets`,
`wf`, `Decodes`, …).

## 4. Checks

- **Axioms.** I re-ran the packet's `check/Check.lean`: 43 declarations, all within
  `[propext, Classical.choice, Quot.sound]`. No `sorryAx`.
- **Exports.** All statements printed for this audit elaborated in the packet environment.

## 5. Readings R1–R8

| Reading | Verdict | Reason |
|---|---|---|
| R1 (sub-objects read the global `Z`) | ACCEPT | `cplShape_inter`: the shape depends on `Z` only through the special candidates at the object's own nodes, so `Z` and DH21's `Z_j = Z ∩ 𝒩_j^ch` give the same shape. |
| R2 (`𝚌` stored as `𝚌 − 1`) | ACCEPT | A pure encoding; `codeSign` and the codes `c1…c3` use it consistently. |
| R3 (only the chain spine is read) | ACCEPT | Enhanced objects are dominant, and B2's `RegChain.dominant` requires `inner.isNil` at every pair. So nested pairs never occur. |
| R4 (layer as a number) | ACCEPT | TARGET's "all nodes in layer `r`" is a property of the embedded object, not of its class. The class data (a number `r` plus the DH21 class) is what the source compares. Consumers obtain the single-layer property from LAYERREG (`layerreg1`). |
| R5 (enhanced objects are codes) | ACCEPT | B2 convention. REG-STRUCT gives codes of regular carriers. |
| R6 (Prop 4.20 in rebuild form) | ACCEPT | See §2; stronger uniqueness. |
| R7 (`encCode` as one preimage) | ACCEPT | Surjectivity is existential. DH21 leaves the choice free. |
| R8 (`ζ*` is B1's `Garden.zeta`, not B2's `zetaOfTrees`) | ACCEPT, with consumer item E-3 | The net-sign results are stated with DH21's own `ζ*` (defzetaq). The bridge to B2's `zetaOfTrees` (used by `RegCpl.app`) is a separate fact. |

## 6. Findings

**E-1 (OPTIONAL). Tree equivalence ignores the root sign.**
- `EnhTree` carries `sign : ℤˣ`, but `LayEnhTree` equivalence compares only the layer and the tuples. This is
  TARGET Def 6.5 literally, which mentions no sign.
- Classes therefore contain trees of both root signs. TARGET's tree sums (regref2-3) are at fixed `ζ`.
- A consumer summing over a class at fixed root sign must add `sign = ζ` itself. No change to the definition is
  needed.

**E-2 (OPTIONAL). DH21 §4.4.5 (1)'s half-scale is not stated.** The fact "`n(𝒯(𝒬)) = n(𝒬)/2`" is unformalized. The
handoff notes it reduces to a count on shapes. No consumer needs it now.

**E-3 (consumer item, not a defect of this packet). Bridge `zetaOfTrees` = `Garden.zeta`.**
- B2's `RegCpl.app` uses `zetaOfTrees` (its `ζ(𝒬)`), while ENHANCED's and LAYERREG's sign results use B1's
  `Garden.zeta`.
- The B2.1 provider (packets L3/L4 or the J series) needs `zetaOfTrees Q.trees = G.zeta` for `Q.Decodes G`.
- It is open in both handoffs and should be scheduled with the B2.1 provider work.

**Note (no action).** The F61 remarks in the handoff are consistent with the confirmed F61 and B2-CL-11:
- `|Z|` is a class invariant (`card_eq_of_equiv`);
- the weight is not;
- so the class sums are unaffected.
