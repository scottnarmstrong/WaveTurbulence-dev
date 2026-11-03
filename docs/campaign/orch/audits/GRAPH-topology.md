# Topology review of `docs/blueprint/GRAPH.md` (refute-first), with WAVE-B §3 reconciliation (Task 4a)

Auditor: `wt-orch`. Date: 2026-11-03. Blueprint as merged on `w/orch` from main (`GRAPH.md`, 704 lines; `WAVE-B.md`,
730 lines). Source: TARGET TeX (sha256 `493eef6b…727cb`); DH21, DH23 and DH21-2 as pinned in the maps. Scope:
topology only (nodes, edges, routes, packets, gates), not proofs.

## Verdict

**SOUND IN OUTLINE, NOT READY TO SCHEDULE FROM AS IS.**

What holds up:

- The root and the three gates have adequate dependency sets.
- The route table chooses single alternatives, with one exception (R14).
- I found no cycles.

What needs fixing before §D–§E are used to assign work:

- **(1) The Stage-2 counting chain is falsely serialized behind the Stage-1 analytic chain.** Four edges cause this
  (I1–I4). They put `T.subpro → T.ops → DH23.excessprop1 → DH23.finalmole → … → T.lgmolect` behind
  `T.vineest`/`T.regref1`, so the published critical path (§D.1) and the zero-slack packet list are wrong.
- **(2) Seven omitted edges and two missing definition nodes** (I5–I11). The most consequential is that the counting
  quantities 𝔄/𝔇𝔢𝔳 are defined only deep in packet F1, yet five G-packets state results in terms of them.
- **(3) One route is stale (R1 versus F3 revised) and one is undecided on the critical path (R14).**
- **(4) The flower pipeline is a "same proof" re-run whose listed dependencies cannot suffice** (I14, I15), and it
  is the longest edge of the critical path.

For the gates, I recommend generalizing the Wave B garden definitions to cover flower gardens now (G-1), and making
`canonicalCharacterization` mandatory (G-2).

## 1. What I checked

**The root and gates, against their source lines and every cross-reference inside their proofs:**

- `T.main` and `T.proofmain` (L817–L823);
- `T.propansatz` and `T.step.S1`–`S7` (L689–L816);
- `T.layergarden` and `T.proofLayergarden` (L761–L779, L2229–L2256);
- `T.fixedpoint`, `T.fp.part1`–`part3` (L780–L794, L2306–L2338).

**All 43 nodes of the critical path (§D.1).** The DH21 and DH23 nodes were checked against the cross-references in
DH21 L752–L797, L913–L944, L1097–L1154, L1748–L1765 and DH23 L945–L1175, L1786–L1818.

**About 20 further nodes across §A.5–§A.13:**

- `T.lemlayer1`, `T.layerreg2`, `T.layervine`, `T.sumint.S2`, `T.regred`, `T.ladderl1old`, `T.ladderl1new`;
- `T.l1reduction`, `T.finalcount1`, `T.proplayer4`, `T.pl1.S3`, `T.redcount0`, `T.vineest.S3`;
- `T.excessprop1`, `DH23.excessprop1`, `DH23.finalmole`, `T.finalmol`, `T.subpro`, `DH23.subpro`;
- `T.cnblock`, `T.lftwistprop`, `T.defcong`, `T.fp.part2`.

**Method.** For each node I extracted every `\ref` and `\cite` in its source range and compared them with its
`deps`. Where a reference could be load-bearing, I read the surrounding text.

**Nodes with no issue:** `T.main`, `T.propansatz`, `T.step.S1`–`S7`, `T.layergarden`, `T.fixedpoint`, `T.fp.part2`,
`T.fp.part3`, `T.proofLayergarden`, `T.plg.ab`, `T.finalproof`, `T.finalcount1`, `T.finalmol`, `T.ops`, `T.vineest`,
`T.vineest.S3`, `T.proplayer2`, `T.regref1`, `GAP.regrefNorm`, `DH23.regcpltreeasymp`, `DH21.maincoef`,
`T.propstructure`, `GAP.structUniq`, `DH21.structure15`, `DH21.structure1`, `DH21.prop34`, `DH21.legalpair`,
`T.defregchain`, `T.defreg`, `T.subobject`, `T.defgarden`, `T.deftree`, `T.layerreg2`, `T.layervine`, `T.sumint.S2`,
`T.regred`, `T.ladderl1old`, `T.l1reduction`, `T.pl1.S3`, `T.redcount0`, `T.cnblock`, `T.lftwistprop`, `T.defcong`,
`T.lemlayer1`.

`T.lemlayer1`'s proof is "an easier version of DH23 Lemma 6.5" (L966). The graph chooses to re-prove it from
`AN.statPhase`/`AN.nonStat` rather than depend on `DH23.NTSP`. That is a legitimate choice, since both are in NT5.

**`T.proofmain` (L817–L823)** cites `layergarden` and `fixedpoint` for non-integer times. It correctly reaches them
only through the time-parametrized `T.propansatz` (route R13, B1.1 item 2′).

## 2. Issues

The nodes affected are named in the first column.

| # | node(s) | problem | evidence | fix |
|---|---|---|---|---|
| I1 | `T.subpro` → `T.redsplice` | **False serialization.** `subpro` needs only the *construction* of 𝒢_sb/𝕄_sb (congruence classes, 𝒱_0, splicing, hinge atoms). It does not need the analytic Stage-1 bound, which brings in `T.vineest` and the whole regref chain. | T L2040–L2053: the proof uses the merging of the VCs in 𝒱_0, `blockchainprop`, `propcplmol`, and "the proof of DH23 Prop 9.1". No estimate appears. | Split `T.redsplice` into `T.redsplice.def` (row P1) and `T.redsplice` (analytic: redvine2, factorization; deps `T.redsplice.def`, `T.vineest`, `T.treelemma`, `T.proplayer1`, `T.proplayer2`). Then `T.subpro` → `T.redsplice.def`. |
| I2 | `GAP.degenerate` | **Conflates two different gaps.** (a) The L^{−0.1γ₀} gain for degenerate decorations in vineest Step 3 is analytic and needs the vine parametrization. (b) subpro(3), "non-hinge ZG atoms are tame", is combinatorial, from DH23 Prop 9.1's proof. Through (a), `T.subpro` inherits `T.vineest.S2`. | T L1855 versus L2044–L2045, L2053. | Split into `GAP.degenerate.vine` (→ `T.vineest.S3`) and `GAP.degenerate.tame` (→ `T.subpro`) (rows P2, P3). |
| I3 | `DH23.excessprop1` → `T.vineest.S2` | **Wrong edge.** DH23 Prop 9.4 uses DH23's *molecule-level* reparametrization ("the reparametrization introduced in the proof of Props estbadvine–estnormalvine", DH23 L1788–L1802). It does not use TARGET's garden-level Step 2, which drags in `T.vineest.S1 ← T.regred ← C3/D2/M2/M3`. | DH23 L1788–L1802; also T L2172 (`excessprop1`(2)), "invoke the re-parametrization … (we are dealing with a single vine now)". | `DH23.excessprop1` → `GAP.vineParam`; `T.excessprop1` → `GAP.vineParam` (new edge); `GAP.vineParam` deps → `GAP.vineDef`, `T.defdecmol`, `T.cohmol` (drop `T.vineest.S1`); move `GAP.vineParam` out of V4 into M4 or its own early packet. `T.vineest.S2` keeps `GAP.vineParam` and `T.vineest.S1`. |
| I4 | `DH23.finalmole` → `DH23.excessprop1` | **Spurious edge.** DH23 Prop 9.5 is structural. Its proof uses odd-degree parity, the operations' definitions and Prop `subpro`, not the deviation bounds. It only *recalls the notation* κ_v from 9.4. | DH23 L1806–L1817 (statement and full proof). | `DH23.finalmole` deps: `T.ops`, `DH23.subpro`. |
| I5 | `T.fp.part1` | **Omitted input.** (fixedest1–2) need the time derivatives ∂_t a^tr and ∂_t ℒ_0 (Sobolev in t). TARGET bounds them "using the same arguments in the proof of Proposition flowerest1" (Dirac time node at the root). | T L2310. | New node `T.fp.dtBound` (row P4), a dep of `T.fp.part1`. |
| I6 | `T.vineest.S4` | **Omitted edge to `T.layerreg2`**, which counts the choices of (𝒬, 𝒯) in the twist difference terms. | T L1890s: "the number of choices for (𝒬,𝒯) is at most C₂·C₀^{n(𝒬)+n(𝒯)} by Proposition layerreg2". | Add `T.vineest.S4` → `T.layerreg2`. |
| I7 | `T.ladderl1new` | **Omitted edge**: the ladder L^∞ bound re-uses vineest Step 2's reparametrization. | T L1984–L1986: "argue as in Step 2 of the proof of Proposition vineest to re-parametrize … the ladder component of Vine (II)". | Add `T.ladderl1new` → `GAP.vineParam`. |
| I8 | `T.proplayer4` | **Omitted edge to `T.proplayer2`.** | T L1250s: "by Proposition proplayer2 we may restrict 𝒬 and 𝒯 to be dominant". | Add `T.proplayer4` → `T.proplayer2`. |
| I9 | `T.lgmolect`, `DH23.lgmolect`, `DH23.moleprop1–4`, `DH23.excessprop1`, `DH23.appB.ops` | **Missing definition node.** All are stated with 𝔈/𝔄/𝔇𝔢𝔳 (`defcounta`, `defcounta2`), but the only defining node is `T.L2129`, which hangs off `T.l1reduction` (packet F1, depth 129). `T.lgmolect`'s statement cites `defcounta2` directly, yet it has no edge to `T.L2129`. B2.3 `rigidity` must freeze this definition. | T L2108–L2112, L2129–L2137, L2192–L2200. | New def node `MOL.countq` (row P5) in M1 or G0. All the listed nodes and `T.L2129` depend on it; `T.L2129` keeps `T.l1reduction` only for 𝔄_sb. |
| I10 | `DH21.Bcstruct` → `T.deflink` | **Over-strong edge.** DH21 §5.1 uses Prop 4.3 (`branchpair`), Def 4.11 (`defchoice`, the choice set 𝒩^ch) and the structure theorem. It does not use the (x,y) relation (`GAP.linkXY`, F16), which only TARGET Prop 5.1's change of variables needs. Today this edge puts `T.deflink` and `GAP.linkXY` on the critical path. | DH21 L913–L944: references `branchpair`, `defchoice`, `structure1` only. | New def node `DH21.defchoice` (row P6). `DH21.Bcstruct` deps → `DH21.branchpair`, `DH21.defchoice`, `DH21.structure1`; `T.deflink` → `DH21.defchoice`. |
| I11 | `DH21.maincancel` | **Omitted edge to `DH21.defstd`.** The statement is "for non-dominant Q". It is harmless at packet level, since J4 already depends on C5. | DH21 L1748–L1765 references `defstd`. | Add the edge. |
| I12 | Route R1; `NT.circle23`, `NT.annulus`, `GAP.circle23`, `DH23.basiccount0`; WAVE-B B1.7 | **Stale route.** R1 chooses exponent 2/3. F3 (revised) shows that `basiccount0`(2) (γ > 4/5) needs an exponent e < 2/3 strictly, via van der Corput (packet NT-EXPSUM; e = 27/41 from the pair (11/30, 16/30)). B1.7's constant remark ("if the 2/3-exponent proof …") is stale too. | FINDINGS F3 (revised 2026-11-03, `ExponentAudit.lean`). | Restate `NT.circle23` as "discrepancy ≤ C·Q^e for a fixed e < 2/3" and `NT.annulus` with e. Add rows P7 and P8. Update R1, GAP.circle23's text and B1.7. |
| I13 | Route R14; `GAP.largeOrder` (F33) → `DH23.regcpltreeasymp` | **Undecided route on the critical path** (RA1). Option (b), a crude bound absorbed by δⁿ, is not available as stated: the trivial bound on K_Q loses about L^{γ} per order, which is not L^{O(1)}. | GRAPH §B R14; T L949; DH23 L1168. | Decide before RA1 starts. I recommend (a): re-check DH23 Props 6.1 and 6.4 for n ≤ (log L)^{C(𝔇)}, i.e. track the (λ)^C and C^n losses against L^{−γ₁+η}. |
| I14 | `GAP.flowerPipeline` (critical path) | **"Same proof" whose deps cannot suffice.** TARGET L2283–L2305 re-runs §5–§11 for flower gardens with seven adjustments. The node depends on `T.proofLayergarden`, but the garden-level theorems do not apply to flower gardens. 𝕄(𝒢) has unpaired-leaf degree deficits and Dirac time nodes (`t_{𝔣^pr} = s`); stems must lie in layer p; there is no flower version of `block_clcn`, `cnblock`, `propcplmol`, `canonequiv` (for ℋ_{p+1}, "same proof") or `excessprop1`(3). | T L2259–L2305; map T-part2 (T-defflower issue). | Gate change G-1 (§4). If that is not adopted, list the flower variants as explicit nodes. |
| I15 | `GAP.flowerPipeline` | **Flower gardens are not irreducible** ("we will make no irreducibility assumption about flower gardens", L2283). The garden pipeline uses irreducibility at several points: connectivity and χ = n−R+1 in `propcplmol`, the 2R-component count in `cnblock`/`excessprop1`(3), and imperfect components in `finalmol`. So the flower case is not a re-run: it needs a decomposition into irreducible components (moments rather than cumulants). | T L2283; L1303–L1307, L1367–L1376, L2154–L2190. | Add the statement to G-1. The generalized gate must allow reducible gardens, or factor over irreducible components. |
| I16 | `T.excessprop1` | **Garden adaptation not represented.** (1) is "exactly DH23 Prop 9.4 … same proof", but DH23's proof "relies on" no Operation 1 creating a component (L2165). `GAP.rigidityGardens` covers the "9.4–9.6 for gardens" adaptation but lies only upstream of `T.lgmolect`. | T L2165–L2166. | Either state `DH23.excessprop1` at molecule level (no couple structure) and say so in its row, or add `T.excessprop1` → `GAP.rigidityGardens`. |
| I17 | packets NT3, NT4, NT11 | **False parallelism.** All three need the same "standard reductions" of DH23 Lemma 6.6: multi-d quadratic exponential sums with χ₀ cutoffs reduced to products of 1-D Weyl sums, plus the compactly supported replacement of χ̂₀. Only NT11 (`GAP.lemcubicRed`) has a node, so NT3 and NT4 would each re-derive it. | DH23 L1076–L1136; T L1560 ("standard reductions as in … Lemma 6.6 of DH23"). | Hoist into `NT.weylReduction` (row P9) in NT1, consumed by `DH23.minorarcs1`, `DH23.minorarcs2` and `T.lemcubic` (`GAP.lemcubicRed` then becomes only the lemcubic-specific part). |
| I18 | packets G2, G5, G6, G7, G8 | **False parallelism.** They are scheduled independently of F1 but share the definition of 𝔄/𝔇𝔢𝔳, which only F1 provides (I9). | as I9 | Fixed by I9. |
| I19 | packets V4, G2 | After I3, both need the vine parametrization. V4 currently sits behind V3 (`T.regred`). | as I3 | Put `GAP.vineParam` in M4, or in a molecule-level packet after M4, before V4 and G2. |
| I20 | `GAP.timeParam` | **Design node with no deps, but listed as a dep of `T.cmattr`, `T.proofLayergarden` and `T.proofmain`.** Its content ("every ingredient holds at t ∈ [p,p+1]") is distributed over the ingredients. This is harmless for acyclicity, but its 500 lines are counted twice. | GRAPH §A.1 | Keep it as a design note with zero weight, or attach it to the frozen time-parametrized statements (B1.1 item 2′, B1.2 (D2)). |

**Effect of I1–I4 and I10 on §D.** The longest chain no longer runs
`lgmolect ← rigidityGardens ← finalmol ← finalmole ← excessprop1 ← ops ← subpro ← redsplice ← vineest`. The Stage-2
counting chain (G1–G3, G8, F3) becomes parallel to the vine and regref chain, whose prefix now ends at `T.redsplice`
(analytic), which feeds `T.l1reduction`/`T.ladderl1old` → `T.finalproof`. `GAP.linkXY` and `T.deflink` also leave the
path. My rough estimate is that 20–30 of the 123 weight units of serialization disappear and packets G1–G3, G8 and
F3 gain large slack. **Re-run the §F.4 script after applying the edge changes in §3**; the zero-slack list in §D.2
will change.

## 3. Proposed new rows (GRAPH format) and edge changes

| ID | kind | source | statement | deps | consumer | d | lines | pkt |
|---|---|---|---|---|---|---|---|---|
| P1 `T.redsplice.def` | step | T L1927–L1946 | congruence classes; SG/LG/ZG prescriptions (≤3^n); 𝒱_0; merging each VC of 𝒱_0 into one atom (splicing) ⇒ 𝒢_sb, 𝕄_sb, hinge atoms; invariance of 𝒱_0 under LF twists | T.defcong, GAP.congEquiv, T.defdiff, T.lftwistprop, T.block_clcn, T.blockchainprop, T.twistexplain | T.subpro | M | 800 | S2a (new, before S2 and S4) |
| P2 `GAP.degenerate.tame` | gap | GAP (F21; T L2044–L2045; DH23 Prop 9.1 proof) | subpro(3): for decorations with ε̃·𝒵 ≠ 0, every degenerate (ZG) atom of 𝕄_sb that is not a hinge atom is tame | DH23.extradegen, DH23.subpro, T.redsplice.def | T.subpro | M | 600 | S4 |
| P3 `GAP.degenerate.vine` | gap | GAP (F21; T L1855) | the L^{−0.1γ₀} gain in vineest Step 3 for ε = −1 / self-loop / degree-2 decorations (the vine half of the old `GAP.degenerate`) | T.vineest.S2, DH23.extradegen | T.vineest.S3 | H | 900 | V5 |
| P4 `T.fp.dtBound` | step | T L2310 | E_p∣∂_t a^tr_k(t)∣², E_p∣∂_t(ℒ_0)_k(t)∣² satisfy (trterm1) with an extra L^{100d} (Dirac time node at the root, by the flower-pipeline arguments) | GAP.flowerPipeline, T.defjt, T.defbk, T.taylorbound | T.fp.part1 | M | 600 | X2 |
| P5 `MOL.countq` | def | T L2108–L2112, L2129–L2137; DH23 (defcounta) | for a molecule with a restricted (c_v, β_v, k^0_ℓ)-decoration problem and α/β/ε labels (Q_v, ι_v, κ_v): the counts 𝔈 and 𝔄, and the deviation 𝔇𝔢𝔳 of an operation; generic in the molecule (no garden) | T.defdecmol, T.defcut | DH23.excessprop1 | M | 500 | M1 (or G0) |
| P6 `DH21.defchoice` | def | DH21 L798–L812 (Def 4.11); T L874–L882 | the choice set 𝒩^ch: one node from each linked pair, fixed through the structure theorem | DH21.branchpair, T.propstructure | DH21.Bcstruct | L | 300 | C2 |
| P7 `NT.expPair` | infra | F3 (revised); packet NT-EXPSUM | van der Corput A- and B-processes in 1-D; the exponent pair (11/30, 16/30) | AN.poisson, AN.statPhase | NT.circleE | VH | 3000 | NT-EXPSUM |
| P8 `NT.circleE` | infra | F3 (revised) | #{n∈ℤ²: ∣n−c∣≤Q} = πQ² + O(Q^{27/41}) uniformly in c (any fixed e < 2/3 suffices) | NT.expPair | NT.annulus | H | 1500 | NT-EXPSUM (replaces NT.circle23 on the route) |
| P9 `NT.weylReduction` | infra | DH23 L1076–L1136; T L1560 | reduction of Σ_{x,y(,z)∈ℤ_L^d}∏χ₀(·−a)·e(quadratic phase) to products of 1-D Weyl sums with compactly supported replacements of χ̂₀ | NT.gaussSum, AN.poisson, AN.gevrey | DH23.minorarcs2 | M | 800 | NT1 |

**Edge changes** (old → new):

- `T.subpro`: `T.redsplice` → `T.redsplice.def`; `GAP.degenerate` → `GAP.degenerate.tame`.
- `T.vineest.S3`: `GAP.degenerate` → `GAP.degenerate.vine`.
- `T.redsplice`: add `T.redsplice.def`.
- `DH23.excessprop1`: `T.vineest.S2` → `GAP.vineParam`; add `MOL.countq`.
- `T.excessprop1`: add `GAP.vineParam`, and either `GAP.rigidityGardens` or a molecule-level restatement (I16).
- `GAP.vineParam`: `T.vineest.S1` → `T.defdecmol`, `T.cohmol`.
- `DH23.finalmole`: `DH23.excessprop1` → `DH23.subpro`.
- `T.fp.part1`: add `T.fp.dtBound`.
- `T.vineest.S4`: add `T.layerreg2`.
- `T.ladderl1new`: add `GAP.vineParam`.
- `T.proplayer4`: add `T.proplayer2`.
- `T.lgmolect`, `DH23.lgmolect`, `DH23.moleprop1–4`, `DH23.appB.ops`, `T.L2129`: add `MOL.countq`.
- `DH21.Bcstruct`: `T.deflink` → `DH21.branchpair`, `DH21.defchoice`, `DH21.structure1`.
- `T.deflink`: add `DH21.defchoice`.
- `DH21.maincancel`: add `DH21.defstd`.
- `DH23.minorarcs1`, `DH23.minorarcs2`, `T.lemcubic`: add `NT.weylReduction`.
- `NT.annulus`: `NT.circle23` → `NT.circleE`.

All of these keep the graph acyclic: no new node depends on any of its consumers.

## 4. Are the tier-B1 statements (WAVE-B §4.1–§4.10) the right gates?

**What is right.** `layergarden` is deterministic (F36). `layergarden` and the two-point part of `propansatz` carry a
time parameter (F7, F27). `nlsAkBridge` isolates the PDE content, and the five analytic/NT interfaces need no
combinatorial definitions. These are good choices. The following changes would make the cut safer:

- **G-1 (most important): generalize the garden definitions to cover flower gardens now.**
  - **The problem.** Freezing B1.2 for gardens only leaves `fixedpoint` (B1.3) to be reached through an unfrozen
    VH re-run (`GAP.flowerPipeline`, ~5000 lines, critical path; I14, I15).
  - **The proposal.** Make the §2.2/§2.4 carriers "gardens with a set of marked unpaired leaves (flowers) and, per
    marked leaf, a fixed time node", and drop irreducibility from the carrier.
  - **The gates.** State the B1.2 estimate either for this general class, with irreducibility as a hypothesis for
    the cumulant part and a component factorization for moments, or add a companion gate `layergardenFlower`
    (`flowerest1`'s moment bound) now.
  - **Cost.** Small at definition time. If done later, the whole M/V/S/G/F pipeline has to be re-stated.
- **G-2: make B2.4 `canonicalCharacterization` mandatory, frozen together with B1.**
  - B1.1 item 3 and B1.2 quantify over `IsCanonG`, which per route R12 is the *criterion* form (`canonequiv` (i)+(ii),
    with the F35 reading for incomparable nodes), not TARGET's Def 3.7.
  - The faithfulness of the two main gates to the source therefore depends on that characterization, together with
    the construction bijection (`GAP.cmattrBij`). Without it, the B1 statement audits cannot certify B1.1(3) and B1.2.
- **G-3: consider a frozen `cumulantExpansion` interface (`T.cmattr`).** It is the hinge between the probabilistic
  gate (B1.1) and the deterministic one (B1.2): 𝕂_p of a^tr equals Σ_{𝒢^tr_{p+1}} K_G plus errors. It is the place
  where the meaning of 𝒦^tr_{p+1,N} (inputs F_q, time domain, truncation) must match exactly across the two gates. It
  is also H + H work (2500 + 2000 lines, F12). Freezing it, or at least fixing 𝒦^tr as one shared definition used
  verbatim by B1.1 and B1.2, prevents a mismatch that would otherwise surface only at assembly (I2).
- **G-4: `sumint` (B1.6).** Add the size hypothesis `M ≤ N_{p+1}^4` (or `M ≤ (log L)^{C(𝔇)}`) now. WAVE-B leaves "whether
  the proof needs M ≤ (log L)^C" open, and every consumer satisfies it. A weaker frozen statement is safer than
  discovering that the proof needs it.
- **G-5: `countLemma` (B1.7).** Update the constant remark for F3: exponent e < 2/3, possibly with η-dependence.
- **G-6 (no change).** B1.3 `fixedpoint`'s hypothesis `AnsatzAt q` for all q ≤ p, and B1.4–B1.5, are adequate as
  cut points.

## 5. Reconciliation of WAVE-B §3 with `figure-defs.md`

"Agree" means the same mathematical object, up to atom labels.

| WAVE-B | figure-defs | Status | Recommended reading |
|---|---|---|---|
| §3.1 mini-couples | §5 | **Agree.** WAVE-B cites DH21 L798 ("counted from left to right in the tree whose root has + sign"), which settles my open point M1. | WAVE-B's: red/green/blue = pairs of the + tree's L/M/R leaves. M1 is closed by the source. |
| §3.2 mini-trees | §5 | **Agree** on all six rows and on the colour rule. | — |
| §3.3 operations A, B | §5 | **Agree.** This includes B at a leaf, where the lone leaf is that leaf. WAVE-B's open check is answered by my §5 (needed for the (2,0)-mini-couple). | — |
| §3.4 regular chains | §6 | **Agree.** | — |
| §3.5 links (x,y) | not covered | I checked the three computed cases algebraically: code 00 gives (x′,y′) = (x,y); 01 gives (−y,−x); 10 gives (−x,y), using a−b+c = k. All correct. | The other codes stay with packet C2, as WAVE-B says. |
| §3.6 vines | §1 | **Agree** on all eight templates. WAVE-B's (VI) h, i, j, k, m are my x, y, p, q, r. Two differences: (i) WAVE-B check (ii) says "(VII) red slot drawn crossed". At full resolution the red pair is **parallel** (`a⋯c, b⋯d`), and the crossing is between red and cyan. This is immaterial, as WAVE-B notes. (ii) Check (iv), "is the opposite-direction condition implied?": **yes**, by the 2-cut lemma (figure-defs §0.3). | Use the block axioms plus undirected isomorphism. Add no slot-direction clause. |
| §3.7 ladders and insertion | §1 (V1, V2) | **Same family** (k ≥ 0 extra rungs per slot, k = 1 included). **Difference:** WAVE-B does not disclose that k = 1 contradicts TARGET's literal "m+1 ≥ 2 double bonds" (L1384; F37). It also writes "each pair of parallel single bonds … opposite directions" into the definition, which is redundant. | Keep k ≥ 0. Disclose it as a deviation from L1384 (DH23 L790 family) for author approval. State the rail-direction fact as a lemma (2-cut), not a clause. |
| §3.8 groups | §1 (V5) | **Agree** for all types, including (VII) `{c,d}`. | — |
| §3.9 positions (I-a…II-e) | §2 | **Agree** on the conditions, the bond labels (including (II-e)) and the free children. **Difference:** WAVE-B leaves (II-a) versus (II-b) as a labelling of v₃, v₄; my G1 notes that it is meaningful only with a labelling fixed on the directed molecule. | A single class "(II-ab)", or v₃ := the neighbour whose bond points into v₂. |
| §3.10 unit twist | §3 | **Agree:** the same slot-swap rule (F38). WAVE-B check (i) (𝔲₂₃ not the right child) is resolved: 𝔲₂₃ keeps its position, and signs place 𝒯₁/𝒯₂. Check (ii) is my lemma (iii). **Not in WAVE-B:** the family-level lemmas (T1: commutation and preservation of core status), T2 (the LF assumption is vacuous for vine (I)) and T3 (congruence is an equivalence relation; GRAPH has `GAP.congEquiv`). | Freeze the slot-swap definition. Add T1–T3 as named lemmas in M6/M7/S1. |
| §3.11 cutting | §4 (C1) | **Differs.** WAVE-B says "No further check needed", but a cut at an atom with a self-loop is ambiguous (F40; loops arise from paired siblings). | Half-edge (dart) encoding of molecules; a cut moves darts. |
| §3.12 flowers | §7 | **Agree** (F25 prefactor). **Not in WAVE-B:** F39 (𝒳 has no identity term, so `(1−ℒ₁)𝒳 = 1+𝒴` needs one); this belongs to `GAP.operatorIdent`. | Add F39 to `GAP.operatorIdent`'s statement; see also G-1. |
| §3.13 | — | **Agree.** | — |
