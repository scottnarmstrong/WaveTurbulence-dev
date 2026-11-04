# Pre-freeze statement audit: LAYERREG (packet C4, wt-torus)

Auditor: `wt-orch`, refute-first, findings only. Date: 2026-11-04 (Task 24a).

**Scope.**
- The exported statements of `/home/scott/wt-scratch/layerreg` against TARGET Prop 4.9 `layerreg1`
  (L899–L929, with `canonequiv` L889 and `deflayer` L650) and Prop 4.10 `layerreg2` (L932–L948).
- The packet's readings R1–R8.
- Whether the statements are about the current B2 definitions.

## Verdict

**PASS.** No BLOCKER and no REQUIRED finding. One OPTIONAL observation (LR-1). The consumer item `ζ*` is shared with
ENHANCED E-3.

- **Statements.** Parts (1) and (2) and the count match the source. They are stronger in places: criterion-form
  hypotheses, no WLOG, and no `binom(m, g)` factor.
- **Readings.** R1–R8 are all acceptable.
- **Currency.** The statements' closure is identical to the current definitions (§3).

## 1. Inputs and pins

**Pin.** `/home/scott/wt-scratch/layerreg`: 74 files hashed at 03:13:47 UTC (digest `ace52078dbf6cbc9…`).
Re-verified unchanged at 03:26 UTC.

**Packet build.** The packet's own `build-final/`, read-only.

**B2 copy.**
- The packet's copy of Regular is `c0216a90…`: the live waveb2 file taken during my Task 23 edits, after CL-13 and
  before CL-16.
- It differs from current (`ce8f0a16…`) only by the ten CL-16 instance renames. These are the same names and bodies
  (`instance …` → `@[instance_reducible, instance] def inst… …`).
- B1 Core, System and Lemmas are byte-identical to snapshot 6.

## 2. Statements against the sources

**Hypotheses.**
- The packet uses `LG.CanonCriterion p ∧ LG.garden.IsPlain` (R2) in place of `𝒢 ∈ 𝒢_{p+1}`.
- B1 defines `IsCanonG (p+1) LG := 4 ≤ w ∧ IsPlain ∧ Irreducible ∧ CanonCriterion p` and
  `IsCanonC (p+1) LG := IsCouple ∧ CanonCriterion p`, with `IsCouple → IsPlain`. So both of TARGET's settings
  (`𝒢_{p+1}`, `𝒞_{p+1}`) supply these hypotheses.
- `q` and `q'` are `parAt LG p a` and `parAt LG p b`: the parent layer, with a root read as `p`, as in TARGET (ii).

**Prop 4.9 (1), couples, trivial or type 1.**
- `layerreg1_type1`: with `wf`, `Embeds`, coherence `CohOn LG (Q.linksAt a b)` and `isType2 = false`, every node
  of `𝒬` has layer `min(q, q')`.
- `cpl_coherent` adds the induction's by-product: if `q = q'`, the whole couple is in layer `q`.
- TARGET: "all nodes in layer `q'`" (with `q ≥ q'`). **Faithful.**

**Prop 4.9 (1), couples, type 2.**
- `layerreg1_type2`:
  - `𝒬_lp` is in layer `min(q, q')`;
  - `ChainPairLayers` on both chains: `𝔏_{𝔫_a} = 𝔏_{𝔫_b}` for each pair, and the pair's sub-couples are in that
    layer;
  - chain nodes lie in `[min(q, q'), parent layer of their chain root]`.
- `layerreg1_type2_minus` (`q' ≤ q`): the `−` chain and `𝒬_lp` are in layer `q'`.
- TARGET's monotone sequence `q ≥ 𝔏_{𝔫_1^+} ≥ ⋯ ≥ q'` is not a separate conclusion. It follows from `deflayer`
  (`𝔏_{child} ≤ 𝔏_{parent}`, built into `LayeredGarden`), since `𝔫_{a+1}` descends from `𝔫_a` (R6). It is also
  proved as `chain_monotone`.
- **Faithful.**

**Prop 4.9 (1), trees.**
- `layerreg1_tree`:
  - `ChainPairLayers`;
  - chain nodes in `[𝔏(lone position), q]`;
  - `List.Pairwise (≥)` along `chainNodeList`, which is the explicit monotone sequence.
- Here `q'` is the layer of the lone-leaf position, as in TARGET. **Faithful.**

**`layerreg1_canonCouple`.** A whole coherent couple in `𝒞_{p+1}` is in layer `p`: the case `𝔫^± =` roots. **Faithful.**

**Prop 4.9 (2), replacement.**
- `layerreg1_replace_canonG`, given:
  - `IsCanonG (p+1) LG`;
  - `𝒬` well-formed, embedded and coherent;
  - `OutAgree LG LG' a b`: the same nodes, leaves, layers and outside partners off the region;
  - `𝒬'` embedded in `LG'` at the same `(a, b)`;
  - `LayerPattern LG' p 𝒬' a b`: coherence plus the part-(1) layer structure.

  Conclusion: `IsCanonG (p+1) LG'`.
- `layerreg1_replace_canonC` is the `𝒞` version. It adds `LG'.sig = LG.sig`; plainness and irreducibility of `LG'`
  are proved.
- The tree versions use `OutAgreeT`, the same agreement modulo moving the lone-position subtree.
- TARGET: "fix `(q, q')` and the structure and layering of the rest of the garden, but replace `𝒬` by any other
  regular couple with layering satisfying all the above assumptions".
  - `(q, q')` agree automatically under `OutAgree`.
  - "All the above assumptions" includes the part-(1) structure, which the source's proof uses (the collapsed `𝒢̃`
    needs single-layer sub-objects). See R6.
- **Faithful.**

**Prop 4.10 (`layerreg2`).**
- `layerreg2 Q hwf a b p q q' g : (inducedLayerings p Q a b q q' g).ncard ≤ (2^{9p})^g · 2^{n(𝒬)} · 2^{|q−q'|}`.
- `inducedLayerings` is the set of functions on the code's node addresses (`cplNodes`, branching nodes and leaves)
  induced by some plain layered garden satisfying `CanonCriterion p`, with:
  - `𝒬` embedded at `(a, b)`;
  - parent layers `q` and `q'`;
  - incoherency index `g` (`incohCount`, the number of links with different `layerAt`: Def 4.7).
- Against TARGET's `C₂^g C₀^{m+|q−q'|}` with `2m = n(𝒬)`:
  - `2^{n(𝒬)}·2^{|q−q'|} ≤ 4^{m+|q−q'|}`, so `C₀ = 4`;
  - `2^{9p} ≤ 2^{9𝔇}` (`p ≤ 𝔇`) gives an admissible `C₂(𝔇)`.
- The set ranges over a superset of TARGET's gardens, so the bound is stronger.
- `g ≤ m` is not needed.
- `layerreg2_tree` is the same with `2^{q−q'}`.
- **Faithful.**

## 3. Are the statements about the current B2 definitions?

I ran the closure comparison of `LINKS-prefreeze.md` §3 from the 24 principal statements (`check/Check.lean`).
Result: 105 B1, B2 and Wave A constants, **105 identical, 0 different, 0 missing**. As expected, the CL-16 renames
change no constant.

## 4. Checks

- **Axioms.** I re-ran `check/Check.lean`: 24 declarations, all `[propext, Classical.choice, Quot.sound]`. No
  `sorryAx`.
- **Exports.** All printed statements elaborated in the packet environment.

## 5. Readings R1–R8

| Reading | Verdict | Reason |
|---|---|---|
| R1 (embedding as `Embeds` / `ChainEmb`) | ACCEPT | TARGET's "embedded with roots at `𝔫^±`": the subtrees are the code's trees and the code's pairs are pairs of `𝒢`. Carriers ↔ codes by REG-STRUCT. |
| R2 (criterion form, weaker hypotheses) | ACCEPT | Stronger statements. B1's `IsCanonG`, `IsCanonGC` and `IsCanonC` all unfold to them (§2). |
| R3 (no WLOG `q ≥ q'`) | ACCEPT | `min(q, q')` covers both orders; `layerreg1_type2_minus` is the normalized form. |
| R4 (`wf`) | ACCEPT | B2 well-formedness is part of every code of a regular couple (REG-STRUCT). |
| R5 (count for a fixed code; `C₀ = 4`, `C₂ = 2^{9p}`; no `binom(m, g)`) | ACCEPT | TARGET's statement counts "the layerings it induces on `𝒬`" for a given `𝒬`. Its proof's extra `C₀^m` (structure) and `binom(m, g)` (positions) factors are proof slack that this bound does not need. A consumer that sums over structures multiplies by `regular_count_le`'s `C₀^m`, as in Q10. |
| R6 (replacement: `OutAgree`, `LayerPattern`) | ACCEPT | See §2. A coherent `𝒬'` without the part-(1) structure could not give a canonical garden, so the source must mean the structured layering. |
| R7 (direct characterization instead of iterated attachments) | ACCEPT | A different proof of the same statement. |
| R8 (tree layerings counted off the lone position) | ACCEPT | The lone position's layer is the fixed `q'`. |

## 6. Findings

**LR-1 (OPTIONAL). The couple conclusions are stated over code addresses.**
- The conclusions use `cplNodes`, `chainNodesSet` and `layerAt`, not over the carrier's `GNode`s. Consumers reading
  layers through `LG.layer` need `layerAt_node` (LINKS) and REG-STRUCT's address correspondence.
- This is the B2 code convention and not a fidelity issue. A carrier-level corollary would ease the RA2/PL1
  consumers.

**Consumer item (ENHANCED E-3).** `ζ*` = `zetaOfTrees` bridge, open; LAYERREG does not use net signs.
