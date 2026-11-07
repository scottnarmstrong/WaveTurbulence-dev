# HANDOFF M8 LAYERCNT (scratch /home/scott/wt-scratch/layercnt, namespace `WaveTurbulence.LayerCnt`)

Status: `layerlad` PROVED. `layervine`: the first bound (sumofexp0) PROVED; the improved bound C_0^{m+|q-q'|} is
PROVED ONLY CONDITIONALLY on a layer-range claim (upper half proved, lower half NOT proved). So the packet is not
complete: `CHECKPOINT layercnt` (see "Not done" below).

## Files (all in `src/LayerCnt/`, 19 files, 2290 lines, every file < 250 lines; sha256 in `LAYERCNT-SHA256SUMS`)
Universe: the lftwist scratch closure (`src/`, `build/`; 899 sources pinned in `COPIED-SHA256SUMS`, copied at first read).
Build: `./build.sh LayerCnt.<Mod>`; fresh rebuild: `./fullbuild.sh` (new dir `build-final/`, exit codes `build-final/log/exit-codes.txt`).

| module | content |
|---|---|
| `TVCount` | at most `(h+1)3^{k+T}` lists in `{0..h}` of length `k+1` with total variation `≤ T` (`card_tv_all`) |
| `Peak` | `NoPeak` (no strict up-step followed by a strict down-step inside a coherent stretch of rungs); `tvab_le`: rail variation `≤ 8𝔇(g+1)` for a peak-free configuration with `g` incoherent rungs |
| `ParentChain` | TARGET L1507 parent-chain argument: `noPeak_of_parents` (abstract `HasParents`) |
| `LadderIncidences` | `IsLadder` interior atoms have four incidences (`ladder_upper/lower_incidences`); adapters `ladder_rails/inj/rung/pos` |
| `BondExp` | `bondsIn`, `bondExp` (= exponent of the bond product), `two_mul_bondExp_le` (dart-sum bound) |
| `Interior`, `Ladder` | interior dart sum of a `FullRungSequence`; `interior_dartSum_bound`; `dartExp_le_split` |
| `GardenParents` | degree-4 atoms of `𝕄(𝒢)` have a parent (adjacent, smaller depth, `f x ≤ f parent`): `garden_parent_step`, `garden_parent_step_le` |
| `Count` | counting of families by rung configurations: `card_configs_le'`, `multi_card_le` |
| `LadderMain`, `LadderSum` | `IsLadder` ⇒ `FullRungSequence`; `incoherencyIndex_ladderGroups`; `ladder_bondExp_le`; `ladder_sum_le` (molecule level) |
| **`Layerlad`** | **`layerlad`** (garden level) |
| `Multi` | several rung sequences + `r` extra atoms: `multi_sum_le` |
| `VineSlots`, `VineGroups` | inserted-rung ladders of a `VineRealization` (slots, labels, disjointness, `|S \ interior| = T.n ≤ 15`); `incCnt_slot_le` (incoherent inserted rungs ≤ `realizedIncoherencyIndex`) |
| **`Layervine`** | `vine_sum_le` (core) and **`layervine_bound`** (first bound) |
| `Improved` | `layervine_improved_of_range` (improved bound, conditional on the layer range; clamp to `[q',q]`, core with `𝔇 = q-q'`) |
| `LayerRange` | `prelayer_le_of_isDesc`; **`layer_le_upper`**: `f x ≤ f a` for every atom of a (CL) block (upper joint `a`) |
| `Check` | `#print axioms` of the main results |

## Statements (no Lean spine statement existed in lg-spine; stated literally from TARGET over the skeleton carriers)
Carriers: a plain/any garden `G : Garden w` (for LG-SPINE: the skeleton `S`), molecule `G.molecule` (B2 `Garden.molecule`),
a pre-layering is `f : GBranch G.tree → ℕ` with `LFTwist.IsBranchPrelayering G f` (T.L1463: monotone along children), atoms of
`𝕄` are `GBranch G.tree`. `Vine.incoherencyIndex`/`ladderGroups`/`realizedIncoherencyIndex` (M4, TARGET cohmol) give `g`.
`bondsIn M S` = the bonds joining atoms of `S`.

```lean
theorem layerlad (B : ℝ) (hB : 1 ≤ B) :
  ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ (G : Garden w) {m} (u v : Fin (m+1) → GBranch G.tree), G.molecule.IsLadder u v →
    ∀ (𝔇 : ℕ) (C₂ : ℝ), C₀ ^ (𝔇+1) ≤ C₂ → ∀ g, g ≤ m+1 → ∀ 𝓕 : Finset (GBranch G.tree → ℕ),
    (∀ f ∈ 𝓕, IsBranchPrelayering G f ∧ ∀ x, f x ≤ 𝔇) →
    (∀ f ∈ 𝓕, ∀ f' ∈ 𝓕, (∀ x ∈ Molecule.ladderAtoms u v, f x = f' x) → f = f') →
    ∑ f ∈ 𝓕.filter (fun f => incoherencyIndex f (ladderGroups u v) = g),
        ∏ x ∈ bondsIn G.molecule (Molecule.ladderAtoms u v), B ^ dst (f (atom x)) (f (atom (mate x))) ≤ C₀ ^ m * C₂ ^ (g+1)

theorem layervine_bound (B : ℝ) (hB : 1 ≤ B) :
  ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ (G : Garden w) (X : VineType) (S) (a b), G.molecule.IsVine X S a b →
    ∀ (R : VineRealization G.molecule X S a b) (m : ℕ), (X.IsBad = true → S.card = 2*m+2) → (X.IsBad = false → S.card = 2*m+5) →
    ∀ 𝔇 C₂, C₀ ^ (𝔇+1) ≤ C₂ → ∀ g, (X.IsBad = true → g ≤ m) → (X.IsBad = false → g ≤ m+1) → ∀ 𝓕,
    (∀ f ∈ 𝓕, IsBranchPrelayering G f ∧ ∀ x, f x ≤ 𝔇) → (distinct on S) →
    ∑ f ∈ 𝓕.filter (fun f => realizedIncoherencyIndex R f = g), ∏ x ∈ bondsIn G.molecule S, B ^ dst (..) ≤ C₀ ^ m * C₂ ^ (g+1)

theorem layervine_improved_of_range (B : ℝ) (hB : 1 ≤ B) :   -- CONDITIONAL
  ∃ C₀, 1 ≤ C₀ ∧ ∀ G X S a b R m (counts as above) (q q' : ℕ), q' ≤ q → ∀ 𝓕,
    (∀ f ∈ 𝓕, IsBranchPrelayering G f) → (∀ f ∈ 𝓕, realizedIncoherencyIndex R f = 0) →
    (∀ f ∈ 𝓕, ∀ x ∈ S, q' ≤ f x ∧ f x ≤ q) → (distinct on S) →
    ∑ f ∈ 𝓕, ∏ x ∈ bondsIn G.molecule S, B ^ dst (..) ≤ C₀ ^ (m + (q - q'))

theorem layer_le_upper (G) (hB : G.molecule.IsBlock S a b) (hCL : Mole.CLParentPattern G S a b) (hf : IsBranchPrelayering G f) :
    ∀ x ∈ S, f x ≤ f a
```
Source readings (TARGET line numbers):
- L1501–1512 (layerlad). "summation over all possible layerings of atoms in `𝕃` with fixed `g`" is read as: every finite
  family `𝓕` of pre-layerings (layers `≤ 𝔇`) that are pairwise distinct on the atoms of the ladder (the sum over the set of all
  distinct restrictions is the supremum over such families). The product is over the bonds joining atoms of `𝕃`
  (`bondsIn`), its base `B ≥ 1` is TARGET's "absolute `C_0`" in the product; the `C_0` on the right is "possibly different" and
  depends only on `B`; `C_2` is any constant `≥ C_0^{𝔇+1}` ("depends only on 𝔇"). Hypothesis `g ≤ m+1` is carried but unused.
- L1513–1521 (layervine, first bound). The statement is proved for every vine in every garden molecule (neither (CL) nor
  canonicity nor the skeleton structure is used): with `G` = skeleton, `f` = `LFTwist.inducedPrelayer` (an `IsBranchPrelayering`
  by `inducedPrelayer_isBranchPrelayering`) it is the source statement. Joint layers `q, q'` are not fixed (a larger sum).
  The vine incoherency index is `realizedIncoherencyIndex R f` for the realization `R` (independent of `R` by M4).
- L1522–1532 (improved bound): see "Not done".

## Approach
`layerlad`: (i) interior atoms of the ladder have four incidences (degree-4 atoms are non-roots, `root_degree_le_three`), each
has a parent among its four neighbours; (ii) the parent-chain argument gives `NoPeak` (TARGET: unimodal; here only the
consequence used: no up-step followed by a down-step in a coherent stretch); (iii) `NoPeak` gives total rail variation `≤
8𝔇(g+1)` (induction on the number of incoherent rungs, splitting at the first incoherent rung); (iv) sequences of
bounded variation are counted by `(𝔇+1)3^{n+T}` (recursion on lists; replaces TARGET's `2^{m+𝔇+1}` monotone count and its
"two monotone pieces" bookkeeping, the factor `(m+2)` dropped there is harmless); (v) the bond exponent is bounded via a
dart sum (`2·bondExp ≤ dartExp`) by `𝔇(10g+18)`; (vi) assemble: `≤ 9^m ((2^6 3^16 B^28)^𝔇)^{g+1}`.
`layervine_bound`: the realization (`VineRealization.has_rungSequence`) gives a `FullRungSequence` for each of the `≤ 3` slots;
different slots have disjoint label ranges; the other atoms are the `T.n ≤ 15` template atoms (`card_rest`); each incoherent
inserted rung is an incoherent group (`incCnt_slot_le`, groups nodup). The same per-ladder estimates with a *uniform*
bound `g` per ladder give `9^m ((2^21 3^48 B^60)^𝔇)^{g+1}` (explicit exponential constants absorb the product of the three ladders'
`C_2^{g_i+1}`, which TARGET's "possibly different `C_2`" glosses over).

## Checks run (exact)
- Fresh rebuild: `./fullbuild.sh` → `build-final/log/exit-codes.txt`: all 19 LayerCnt modules exit 0 (TVCount … LayerRange, Check),
  new build dir, dependency oleans = the copied lftwist build (not rebuilt; sources pinned in `COPIED-SHA256SUMS`).
- `build-final/log/Check.log`: `#print axioms` of `layerlad`, `layervine_bound`, `vine_sum_le`, `layervine_improved_of_range`,
  `layer_le_upper`, `prelayer_le_of_isDesc`: each exactly `[propext, Classical.choice, Quot.sound]`.
- Hygiene grep over `src/LayerCnt`: no `sorry/admit/axiom/opaque/unsafe/maxHeartbeats/maxRecDepth` (only `#print axioms` lines in Check.lean).
  Linter warnings only (unused variables/simp args) in some modules; no `declaration uses sorry`.
- Exact-type check: NOT run (no pinned Lean statement exists: lg-spine has only the SPINE.md row, grep found none).

## How LG-SPINE should consume
Take `G := ` the skeleton garden `S`, `𝓕 :=` the finite set of induced pre-layerings `inducedPrelayer LG D hS hd` (as functions
`GBranch S.tree → ℕ`) of the canonical layered objects in the class counted, chosen pairwise distinct on the atoms of the ladder/vine under
consideration (distinct restrictions = distinct "layerings of atoms"); layers `≤ p ≤ 𝔇`. Then
the weighted sum over layerings with fixed `g` of the ladder/vine is `≤ C₀^m C₂^{g+1}`. For the improved vine bound
(VC chains, `q_sk`), use `layervine_improved_of_range` once the range hypothesis is available.

## Deviations / errata
- Statement shape: families of pre-layerings instead of "all layerings"; `C₂ ≥ C₀^{𝔇+1}`; `g` as `Vine.incoherencyIndex`.
- `IsLadder` in this scratch universe (`MoleculeDefs`, lftwist copy) has an extra clause "`4m+2` bonds in the atomic group";
  the B2 final-candidate `IsLadder` does not. Only `LayerCnt.ladder_rails` (`hL.2.2.2.2.1`) depends on this; on porting to the
  B2 final form change it to `hL.2.2.2.2`.
- Suspected erratum-lite (TARGET L1519): applying `layerlad` to each of the three ladders gives `C_2^{g_1+1}C_2^{g_2+1}C_2^{g_3+1}`, i.e. up to
  `C_2^{g+3}`, not `C_2^{g+1}`; harmless once `C_2` constants are allowed to differ (done here with explicit constants).
- `layerlad` source proof miscounts only harmlessly (omits the `m+2` split points).

## Session 2 (lower half of the layer range): DONE except the bridge for the canonical pair criterion

New modules (all in `src/LayerCnt/`, fresh `./build.sh` per module, exit 0, no sorry; axioms of the main results exactly
`[propext, Classical.choice, Quot.sound]`, see `Check2.lean`; hygiene grep over `src/LayerCnt` empty; sha in `LAYERCNT-SHA256SUMS`):

* Cut certificates for expanded templates: `CutCert` (Crosses/CutOn/Sides2, `ext_insert`), `CutRung` (`rung_cert`), `CutFold`, `CutBase`
  (bfs-computed labellings, `CutG`/`CutS`), `CutExpand` (`CertAt`, `fold_ext`), `CutMain` (`expand_certG`, `expand_certS`).
* Chain: `ChainLower` (`exists_level1`, `lower_of_cert`), `ChainGarden` (`chain_exists`: parent chain b -> a in a (CL) block),
  `GoodGroups` (`expand_groups_cases`, `GoodGroup`, **`lower_of_good`**: atoms of base cut groups and of rungs of base cut slots have f >= f b).
* The group `H` of vines (V)-(VIII) (non-cut groups): tree argument `TreeFacts`, `Deg4`, `HExit`..`HExit5` (**`exit_lemma`**: a set K of degree-4 atoms whose
  only exit darts are d1 != d2 with f(atom d1) = f(atom d2) satisfies min(f(atom(mate d1)), f(atom(mate d2))) <= f(atom d1); uses the canonical pair
  criterion `CanonPairs G f p Reg`); template-to-molecule translation `ExitTranslate`, `ExitKCut` (**`exit_of_kcut`**), cut families `KCutExt`
  (**`kcut_ext`**), `PosCut`/`PosSingle`/`PosDefs`/`PosMain` (**`expand_kcutPos`**, rail-position cuts of inserted ladders), peeling `HChain`, `PosChain`,
  `HLower` (`lower_cover`), `HLowerV`, `HLowerVI` (VI, VII, VIII), **`LowerHalf.lower_half_aux`**.
* `Unconditional`: `layer_range` and **`layervine_improved`** (improved bound `C_0^{m+(q-q')}`, unconditional modulo the hypothesis `CanonPairs G f p (RegS G S)`).

Source reading (TARGET L1522-L1532, proof of the improved bound): the (V)-(VIII) argument "move from v to v+ ... eventually reach v1 or v3 ... by canonequiv" is formalized as `exit_lemma`
(three cases: both exits parent darts -> canonequiv on (m2,m4); parent dart + child dart -> trivial; parent dart + leaf-pair dart -> canonequiv on (m2, paired leaf), using that the
minimum-parent leaf layer is <= f(v4)). The inductive removal of the pair (v2,v4) is formalized by peeling cuts (ext cut, rail-position cuts j = 0..k of the H slot, end cut for (V)).
Deviation: the criterion is used in the form `CanonPairs` for the minimum-parent extension `extendBranchLayers G f p` of the skeleton pre-layering f; nodes restricted to `RegS G S`.

* `CanonBridge` (compiled): `canonPairs_of_criterion` and **`canonPairs_of_coherent`**: for a canonical object LG with `AllAttachmentsCoherent`, the induced skeleton pre-layering
  satisfies `CanonPairs S (inducedPrelayer LG D hS hd) p Reg` for every `Reg` (from lftwist `coherent_inducedSkeleton_canonical`). With `layervine_improved` this gives the improved bound
  in the all-coherent case (hypotheses of layervine_improved discharged by it).

## Session 3 (region-only bridge): DONE

New modules (all in `src/LayerCnt/`, each built with `./build.sh`, exit 0, no sorry; every file < 500 lines):

| module | content |
|---|---|
| `RegionErase` | `CohT`/`CohQ` (per-slot coherence), `canonObj_eraseTree/Couple` (per-slot), `cohT_eraseTree`, `cohQ_eraseTree`, `eraseTrees_set` (set-indexed copy of lftwist `eraseTrees_list`) |
| `RegionErase2` | `couple_links_outside` (couple erasure with ARBITRARY tree codes; replaces lftwist's `nilTrees_couple_links_outside`), `cohQ_eraseCouple`, `eraseCouples_set`, **`erase_region`** (erase trees of `T`, couples of `Q`; only their own coherence; same induced pre-layering; trivial attachments on `T`,`Q`) |
| `PosTransfer` | `decodedNode_parent` (parent of the node at an inflated position = retained core branch of the skeleton parent), `parentLayer_decodedNode`, `decodedNode_branch_nil`, `decodedNode_incomp`, `below_of_pos_below` |
| `PairTransfer` | `partner_below`: every pair of the decoded garden is an attachment pair (couple pair with endpoints under the two source-leaf roots, or chain pair with endpoints under the chain position and off the hole); with the skeleton's complete pairing this gives the decoded complete pairing |
| `RegionBridge` | `RegErased`, `decoded_completelyPaired`, `layer_decodedNode_le`, `canonPairs_of_erased`, **`canonPairs_of_region`**: `CanonPairs S (inducedPrelayer LG D hS hd) p (RegErased hS T Q)` from `CohT` on `T`, `CohQ` on `Q` |
| `Source` | `SourceRegion`, `CanonPairs.mono`, **`layervine_improved_source`**, **`layervine_source`** (both parts of TARGET's proposition with literal hypotheses) |
| `Check3` | `#print axioms` of `canonPairs_of_region`, `layervine_improved_source`, `layervine_source`, `layerlad`, `layervine_bound`, `layervine_improved` |

Changes to existing modules (Session 2 files): the region predicate now excludes the top joint `a` (= u1).  `HExit5` (`exit_with_up`,
`exit_lemma`) takes `hRegK : ∀ x ∈ K, Reg x.toNode` and `hRegLeafK : parent ℓ ∈ K → Reg (G.pair ℓ).toNode`; `HChain.cut_step`,
`PosChain.PeelCtx`, `LowerHalf.lower_half_aux` take `hRegS : ∀ x ∈ S, x ≠ a → Reg x.toNode` and
`hRegLeaf : parent ℓ ∈ S → parent ℓ ≠ a → Reg (G.pair ℓ).toNode`; `cut_step` derives the `K`-versions because `K (R.f x)` forces `2 ≤ R.f x`
(IsKCut) while `R.f a ∈ {0,1}` (`joints_eq`).  `Unconditional`: `RegS` replaced by `RegV G S a`; `layer_range`, `layervine_improved` use `RegV G S a`.

### Statement (final)
```lean
def SourceRegion (G : Garden w) (hG : G.IsPlain) (p) (S) (a) (f : GBranch G.tree → ℕ) : Prop :=
  ∃ kind LG (D : ReconstructionData G) (hd : D.Decodes hG LG.garden), CanonicalObject p kind LG ∧ f = inducedPrelayer LG D hG hd ∧
    (∀ x ∈ S, x ≠ a → CohT LG D x) ∧
    (∀ q : SourcePair G, (∃ ℓ hr, pairOfLeaf G hG ℓ = q ∧ parent ℓ ∈ S ∧ parent ℓ ≠ a) → CohQ LG D hG q)

theorem layervine_improved_source (B : ℝ) (hB : 1 ≤ B) : ∃ C₀, 1 ≤ C₀ ∧ ∀ G (hG : G.IsPlain) X S a b (hV : IsVine X S a b) (hCL : CLParentPattern G S a b)
    (R : VineRealization ..) m, (counts) → ∀ p q q' 𝓕, (∀ f ∈ 𝓕, SourceRegion G hG p S a f) → (∀ f ∈ 𝓕, realizedIncoherencyIndex R f = 0) →
    (∀ f ∈ 𝓕, f a = q ∧ f b = q') → (distinct on S) → ∑ f ∈ 𝓕, ∏ x ∈ bondsIn .., B ^ dst .. ≤ C₀ ^ (m + (q - q'))
theorem layervine_source : both the first bound (any vine, any pre-layering family) and layervine_improved_source with one constant C₀ (max of the two).
```
`CohT LG D x` = `CohOn LG ((D.tree x).linksAt (nodeSign S.sig x.1) (inflatedPosition S D.tree x.toNode))`, `CohQ` the same for the couple at the leaf pair (lftwist
`AllAttachmentsCoherent` components).  `G` is the skeleton `𝒢_sk`; `a` = joint with `𝔫(a) = u₁`; `S` = the vine atoms.

### Source readings (TARGET line numbers)
- L1521 "coherent for all branching nodes 𝔪 and leaf pairs (ℓ,ℓ') that belong to 𝒢_sk[𝕍]∖{u₁}": branching nodes = `S∖{a}`; a leaf pair "belongs" when at least ONE of its leaves is a child of a node of `S∖{a}`
  (weakest reading that the proof of L1531 needs: it applies `canonequiv` to a leaf `𝔪₆` whose pair `𝔪₅` is a child of `𝔪₃`, possibly `𝔪₃ = u₁`).  Mathematically the proof needs the couple at `(𝔪₅,𝔪₆)` erased.
- L1521 "Using Remark sublayer, replace each such 𝒯 by a single node and 𝒬 by a leaf pair, without affecting canonicity": `erase_region` (per-slot lftwist erasure lemmas `eraseCoherentTree_canonG`/`eraseCoherentCouple_canonG` + set-indexed coherence bookkeeping; trees first, then couples; couple erasure proved for arbitrary tree codes).
- L1531 `canonequiv` is applied to the erased object `ℋ` (canonical, same skeleton, same induced pre-layering) at nodes of the region; `canonPairs_of_erased` transfers `ℋ.CanonCriterion` to the skeleton nodes.  The parent of an erased branch is the retained core branch of its skeleton parent EVEN when that parent (e.g. `u₁`) is not erased, so `u₁` needs no coherence for being a PARENT; it only needs to be unerased as a node (excluded from the region by `RegV`).
- g = 0 and "q ≥ q'" as in the source; `f a = q`, `f b = q'` for `a`, `b` the two joints (`u₁ = 𝔫(a)` ancestor of `u₂ = 𝔫(b)`).

### Checks run (exact)
- Per-module `./build.sh LayerCnt.<M>`: exit 0 for all modules listed above and for every Session-2 module touched (`HExit5 HChain PosChain HLower HLowerV HLowerVI LowerHalf Unconditional`).
- `Check3.log`: `#print axioms` of `canonPairs_of_region`, `layervine_improved_source`, `layervine_source`, `layerlad`, `layervine_bound`, `layervine_improved`: each exactly `[propext, Classical.choice, Quot.sound]`.
- Hygiene grep `\b(sorry|admit|axiom|opaque|unsafe|maxHeartbeats|maxRecDepth)\b` over `src/LayerCnt/*.lean` except `Check*.lean`: no hits.
- Fresh rebuild: `./fullbuild.sh` (new dir `build-final2`, 59 modules in topological order, exit codes `build-final2/log/exit-codes.txt`).
- Exact-type check: not applicable (no pinned Lean statement exists for `layerlad`/`layervine`; the statements above are the literal TARGET readings).

### Universe-specific notes for the UNIVERSE port (R8)
The bridge uses these lftwist/SkeletonDraft declarations (names must exist in the canonical universe after the port): `ReconstructionData.{decodedNode, decodedCoreBranch, core_child_position, pairList, pairList_mem_cases, forest_pairList_cover, couple_pair_mem, chain_pair_mem, eraseTree, eraseCouple, eraseTree_at, eraseCouple_at, eraseTree_other, eraseCouple_other, eraseCouple_collapse_decodes}`,
`eraseTree_collapse_decodes`, `eraseTree_chain_links`, `eraseTree_couple_links`, `eraseTree_native_layerAt`, `eraseTree_inducedPrelayer_eq`, `eraseCouple_inducedPrelayer_eq`, `collapseCouple_outAgree`, `cohOn_map_iff`,
`decodedTrivLeaf`, `decodedTrivLeaf_pair`, `inflatedPosition_{below,incomp,injective,nonroot}`, `chain_endpoints_region`, `cpl_endpoints_under`, `canonical_leaf_layer`, `parentLayer_nonroot`, `parent_eq_of_child` (namespace `Twist`), `pairOfLeaf_sides_pos`, `sourcePair_first_sign`, `leaf_not_above_branch`, `below_child_of_desc_ne`.  The `IsLadder` extra-clause note above (`LayerCnt.ladder_rails`) still applies.
