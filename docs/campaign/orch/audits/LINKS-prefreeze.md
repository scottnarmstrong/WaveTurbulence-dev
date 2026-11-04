# Pre-freeze statement audit: LINKS (packet C2, wt-torus)

Auditor: `wt-orch`, refute-first, findings only. Date: 2026-11-04 (Task 24a).

**Scope.**
- The exported statements of `/home/scott/wt-scratch/links` against TARGET Prop 4.6 `deflink` (L875–L884),
  DH21 Prop 4.3 `branchpair` (L729) and TARGET Def 4.7 `defcoh` (L886–L887).
- Whether they are stated about the **current** B2 definitions.
- A refute-first check of the packet's errata E1–E4 (FINDINGS F62–F65).

## Verdict

**PASS.** No BLOCKER and no REQUIRED finding. Two OPTIONAL items: L-1 and L-2.

- **Statements.** The statements for Prop 4.6, DH21 Prop 4.3 and Def 4.7 match the sources. Some are stronger,
  never weaker.
- **Currency.** The packet compiled against an older copy of `WaveB2-Regular.lean` (`ad72ce4b…`), but every B1, B2
  and Wave A constant its 43 principal statements depend on is identical to the current definitions (§3). The
  statements are therefore about the current B2.
- **Errata.** E1–E4 (F62–F65) are confirmed on the source text.

## 1. Inputs and pins

**Pin.** `/home/scott/wt-scratch/links`: 52 files (sources, scripts, HANDOFF) copied and hashed at 03:13:47 UTC.
- Digest of the hash list: `ec4717394ea4efce…`.
- The live tree re-verified at 03:26 UTC: unchanged.

**Packet build.** I used the packet's own `build-final/`, loaded read-only through `LEAN_PATH`, for all probes.

**Current definitions.**
- `/home/scott/wt-scratch/waveb2` after B2-CL-13 to CL-17 (`WaveB2-Regular.lean` `ce8f0a1652ba…`, built
  2026-11-04 03:02 UTC);
- `/home/scott/wt-scratch/waveb/build` (B1; Core and System byte-identical to snapshot 6);
- the dev build.

**Packet inputs.** B1 Core and System are byte-identical to snapshot 6, and so to snapshot 5. B2 Regular is
`ad72ce4b…`. It differs from current only by:
- CL-8 (an added obligation theorem);
- CL-11 (`specialWeight` body);
- CL-13 (`RegChain.JBtree` body);
- CL-16 (named instances, same names).

## 2. Statements against the sources

Each statement below was printed with `#check @…` in the packet environment.

**DH21 Prop 4.3 (`branchpair`).**
- Source: "a unique way to pair branching nodes … such that for any pair {𝔫,𝔫'} and any decoration
  `ζ_{𝔫'}Ω_{𝔫'} = −ζ_𝔫Ω_𝔫`."
- Lean `branchpair`, for `1 ≤ d`, `L ≠ 0`, `Q.Decodes G`, `IsCouple G`:
  `∃! P : GBranch → GBranch, P ∘ P = id ∧ (∀ b, P b ≠ b) ∧ ∀ κ` (lattice decoration `κ/L`,
  `IsDecoration`) `∀ b, ζ_{P b}Ω_{P b} = −ζ_bΩ_b`.
- A fixed-point-free involution is a pairing.
- Uniqueness is asserted against lattice decorations only. That is the stronger form (D4).
- Existence holds for all vector decorations (`linkPartner_antisymm`, any `Mom d`).
- "Regular couple" is the decoded carrier. Every regular couple has a code by REG-STRUCT
  (`existsUnique_regCpl_decodes`, a B2 §4 obligation proved by REG-STRUCT).
- **Faithful.**

**TARGET Prop 4.6 (`deflink`), partition.**
- `exists_unique_link`: every branching node lies in exactly one link of `Q.links`.
- `link_branching`: the two endpoints of a link are branching and distinct.
- Together these say that the links partition the branching nodes into two-element sets.
- The tree versions (`tree_*`) do the same for `X.treeLinks (G.sig 0)`.

**TARGET Prop 4.6, antisymmetry.**
- `zeta_omega_link` / `tree_zeta_omega_link`: `ζ_{𝔫'}Ω_{𝔫'} = −ζ_𝔫Ω_𝔫`.
- They hold for every vector decoration in `Mom d`, which covers TARGET's `ℤ_L^d` decorations (stronger).

**TARGET Prop 4.6, `(x, y)`.**
- Definitions: `xNode κ b = κ(b.child 0) − κ b`, `yNode κ b = κ b − κ(b.child 2)`; that is,
  `(x_𝔫, y_𝔫) = (k_{𝔫1} − k_𝔫, k_𝔫 − k_{𝔫3})` as in TARGET.
- `xy_link`: `∃ s₁ s₂, (x' = s₁x ∧ y' = s₂y) ∨ (x' = s₁y ∧ y' = s₂x)`, plus `ζ' = −s₁s₂ζ` (F16). This is
  TARGET's set equality `{x', y'} = {ζ₁x, ζ₂y}` in ordered form, with an extra sign conclusion. It holds for
  decorations in any additive group.
- **Faithful.**

**TARGET Prop 4.6, `𝒩^ch`.**
- B2's `chosenSet` is the set of first components of the links.
- `chosenSet_link` (the first node of each link is chosen, the second is not), `chosen_xor` (exactly one per link)
  and `card_chosenSet` (`|𝒩^ch|·2 = size`).
- The rule "type 1: the `+` root; type 2 / trees: `𝔫_a` with `a < b`" is fixed by B2's `linksAt` (audited at
  stage 1).
- **Faithful.** The tree analogue of `chosenSet_link` is not stated (L-2).

**TARGET Def 4.7 (`defcoh`).**
- B2's `LayeredGarden.incoherency` counts pairs `(b, b')` of the carrier's branching nodes with `(b, b') ∈ links`
  and different layers.
- `incoherency_eq_count` / `tree_incoherency_eq_count` show it equals the number of links whose endpoints have
  different layers, using `layerAt`.
  - `layerAt` reads a node's layer; its junk value 0 off nodes is never used, since link endpoints are nodes.
  - Duplicate links cannot inflate the count, because the endpoint list has no duplicates.
- `coherent_iff`: index 0 ⇔ `𝔏_𝔫 = 𝔏_{𝔫'}` on every link.
- `incoherency_le`: `2·index ≤ size`.
- **Faithful.**

**Other exports** (auxlem, explem, treelemma, incohproof1) are outside this audit's source list. I re-ran their
axioms (§4) but did not audit them against DH21 L1659, DH23 A.4 or TARGET L2422 beyond E2/E3.

## 3. Are the statements about the current B2 definitions?

**Method.**
1. In the packet environment, I computed the transitive closure of the 43 principal statements (`check/Check.lean`).
   The closure follows types, definition bodies, constructors and recursors.
2. I kept the constants from B1 (`WaveBDraft.*`), B2 (`WaveB2Draft.*`) and Wave A (`Frozen.Defs`).
3. Each kept constant was dumped with matchers and auxiliary constants delta-expanded and proofs erased, and
   compared with the same name in the current build.

**Result.** 100 constants (49 B2 Regular, 49 B1 Core, `Mom`, `latticePoint`): **100 identical, 0 different,
0 missing.**

**Control.** The same tool, run on `RegCpl.app` and `RegChain.app` in the packet environment, reports exactly
`specialWeight` and `RegChain.JBtree` as different (CL-11, CL-13). So it does detect stale definitions.

**Consequence.** The packet's statements mean the same over the current B2. The stale copy of Regular in `src/`
affects only declarations outside every statement's closure. When the modules are ported, they should be rebuilt
against the frozen B2 rather than the copy.

## 4. Checks

- **Axioms.** I re-ran the packet's `check/Check.lean` against `build-final/`: 43 declarations, all
  `[propext, Classical.choice, Quot.sound]` (one is `[propext, Quot.sound]`). No `sorryAx`.
- **Exports.** All printed statements elaborated in the packet environment.
- **Not re-run:** the packet's clean rebuild (`fullbuild.sh`, run by wt-torus).

## 5. Errata E1–E4 (FINDINGS F62–F65), refute-first

| Item | Claim | Check | Verdict |
|---|---|---|---|
| E1 / F62 | TARGET (incohproof10) (L1023–L1025) uses a per-link factor `ε_𝔫 ∈ {1, 0, −1}`. The true factor is `ε_𝔫²`. | (incohproof8)'s `ε` is `ε_ℐ = ∏_{𝔫∈𝒩} ε_{k_{𝔫1}k_{𝔫2}k_{𝔫3}}` over **all** branching nodes (defepscoef, L646). With `k = k₁ − k₂ + k₃` we have `x = k₂ − k₃` and `y = k₁ − k₂`. So `ε_{k₁k₂k₃}` is `1`, `0`, `−1` as `0`, `1`, `2` of `x, y` vanish (`epsCoef_eq_epsXY`), and `{x', y'} = {±x, ±y}` preserves which of `x, y` vanish, so `ε_{𝔫'} = ε_𝔫`. Hence `ε_ℐ = ∏_{𝒩^ch} ε_𝔫²`. TARGET's factor gives `−1` where the truth is `+1` (both vectors zero). | **Confirmed.** Estimates unaffected ((incohproof12) bounds the factor by 1). |
| E2 / F63 | TARGET `treelemma` (1) (L2422–L2425): "−" should be "±", and `j = 1` has no `j' < j`. | Read at L2422–L2425. DH23 Lemma A.4's proof (L2123) writes `k_𝔫 ± k_{𝔫'}` (a middle child carries sign `−`). For `j = 1` "∃ `j' < j`" is empty. | **Confirmed** (typo / precision). |
| E3 / F64 | DH23 Lemma A.4 (2): "not on `r`" cannot hold literally. | As `r` ranges over `|r| ≤ 1`, `r·k_𝔫` sweeps `[−|k_𝔫|, |k_𝔫|]`, which no fixed unit interval contains once `|k_𝔫| > 1/2`. The proof counts floors as `r` varies. | **Confirmed** (imprecision). The packet's formalization (centres chosen per decoration and `r` from a family independent of `r`) is the meaningful reading. |
| E4 / F65 | DH21 Def 4.11: "if `𝒬 = ×` then `𝒩^ch` contains the root of `+` sign" is a slip. | `𝒩^ch ⊂ 𝒩*` contains branching nodes only (L798), and the trivial couple's roots are leaves. | **Confirmed** (typo). B2's `chosenSet` is `∅` for `triv`. |

## 6. Findings

**L-1 (OPTIONAL). Uniqueness of tree links is not stated.**
- TARGET Prop 4.6 asserts "a unique way" for regular trees too. The packet proves uniqueness only for couples
  (`branchpair`; DH21 Prop 4.3 is about couples).
- For trees, the links are B2's code-defined `treeLinks`, and the partition and antisymmetry are proved.
- No consumer in the current graph needs tree-link uniqueness, so this is not required.

**L-2 (OPTIONAL). `chosenSet_link` and `chosen_xor` exist for couples only.**
- The tree analogues are one-line consequences of `tree_exists_unique_link` and B2's `chosenSet`.
- They are needed only if a tree consumer uses `𝒩^ch` membership. ENHANCED's tree special sets use `treeLinks`
  directly.

**Notes (no action).**
- D1 (the explem (2) constant `7·147^n`) affects only downstream constants.
- The `Incoh.linkEpsilon` QUESTION in the handoff is the F62 consequence for wt-l2s.
- `decEquiv`'s unused `IsCouple` hypothesis (D5) is harmless.
