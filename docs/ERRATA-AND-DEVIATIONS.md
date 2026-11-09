# Errata and deviations

This file lists the defects we found in the published arguments while formalizing them in Lean, and every way in
which the formal (Lean) statements differ from the printed ones. It is written for a mathematician who has the papers
at hand but not the history of this project.

**What an entry claims.** Each entry concerns an argument or a statement as printed. **No counterexample to the main
theorem of TARGET or of DH23 has been found.** The only entry that breaks the printed proof of a main theorem without
a local repair is E1: DH23 Prop 9.6 and the statements built on it are false for 0 < γ ≤ 1/2. That breaks the printed
proof of TARGET's main theorem in that range; it does not refute the theorem. Several other entries show that an
intermediate statement or identity is false as printed (class ERROR), but each has a repair that keeps what the proof
needs. The remaining entries are omitted or invalid steps whose conclusions survive, usually with a repair that we give.

## Summary of findings

In order of importance. An *error* is a statement false as printed; a *gap* is a step whose written justification is
missing or does not work, while the conclusion survives. Evidence, status and repairs are in the entries. TARGET,
DH21, DH23 and GIT20 are the papers listed under "Pinned sources" below, and L-numbers are lines of their TeX files.

1. **The range 0 < γ ≤ 1/2 (E1, error, CONFIRMED).** DH23 Prop 9.6, case (4), is false for 0 < γ ≤ 1/2: an explicit
   family of "necklace" molecules violates it, and with it DH23 `kqmainest2`, TARGET `lgmolect` and (finalcount1); the
   per-class analytic bound `kqmainest1` also fails there for γ < 1/2 (F73, CANDIDATE). For 1/2 < γ < 1 case (4) is
   closed by a new, refereed argument, and the main theorem is now formally proved in Lean for 1/2 < γ < 1 (`main_v2`,
   sealed and two-key audited, 2026-11-09). For γ ≤ 1/2 a repair route (splicing the neutral T-type blocks as an
   enlarged vine family) has passed three independent referee rounds but is not formalized. One step of the counting
   run (E20) was open there; it is now resolved for all 0 < γ < 1 and refereed (2026-11-09). Plain-language
   overview and plan: [GAMMA-LE-HALF.md](GAMMA-LE-HALF.md).
2. **The flower estimate (TARGET Prop `flowerest1`, L2279–L2305).** Its printed proof is a list of seven
   adjustments to the proof of `layergarden`. A complete proof also needs: a layered fixed-time estimate in place of
   "fix the value of Ω" (E30; DH21 L2684–L2694 has the unlayered mechanism); a restated `subpro` for the vines left
   unspliced (E31); an extraction of the M₁ gain that keeps the twist-class cancellation (E33); face estimates for the
   M₂ time integration, whose per-tree gain goes beyond the cited DH21 corollary (E35); arguments for the upper M₂
   filters that L2299 says "play no role", inside regular stem objects and on large-gap ladder rungs (E39, E44); and
   the corrected Stage 1 clock identity (E26). The internal cutoffs themselves are absorbed by the paper's own
   Fourier-L¹ and |r| mechanisms (E36–E38, exposition). A written completion for 1/2 < γ < 1 supplies all of these;
   each piece of the estimate passed an independent referee with no failure, except the weighted clock identity
   (E26), whose referee is pending. No counterexample to `flowerest1` is known, and an independent assessment found
   that the missing arguments build on mechanisms already in DH21 and DH23 without establishing that any needs a new
   idea. The statement needs the normalization fix E41 and the order-zero reading E42; the dagger and derivative
   variants used for `fixedpoint` add one more gap (E45, partly refereed).
   *Update 2026-11-09:* the flower estimate is now formally proved in Lean for 1/2 < γ < 1 (`layergardenFlower_v3`,
   sealed and two-key audited).
3. **Other errors.** Each has a repair, and none breaks a main theorem.
   - DH21 Lemma 5.8 and Prop 7.5: the sign of the χ_∞ term is wrong, so the per-couple weight in TARGET (regref1-3)
     needs a factor (−1)^{|Z|} (E2a, CONFIRMED).
   - TARGET L2264–L2265 and DH23 L1995–L1996 keep the γ = 1 prefactor (δ/(2L^{d−1}))ⁿ; it should be
     (δ/(2L^{d−γ}))ⁿ, and the difference L^{(1−γ)n} is not absorbable (E41, CONFIRMED).
   - TARGET (redvine), L1954–L1957, is false as an identity; an exact replacement gives the same conclusion (E26).
   - TARGET L2152: a zero-gap atom v₃ in Operation 2 need not be tame when it is a hinge (E16).
   - DH23 Lemma `ylem1` misses several molecules (E2b); DH23's operation count in Prop 10.2 (E2c); the relative sign
     of the core in `vineest` for vines (V)–(VIII) (E2d); TARGET L1918 for trivial couples and trees (E18).
   - Smaller slips and readings, harmless in context: E3, E6, E9, E19, E25, E27, E43, and minor items m1–m51.
4. **Gaps that needed a new argument, outside the flower section.** "Replace ε by 1 … sum trivially" fails for long
   vine chains (E4, CONFIRMED); moving weights and derivatives onto decoration-dependent leaves breaks the twist
   cancellation of `vineest` (E24); "cut at v and proceed normally" can feed Prop 9.6 a component on which it fails,
   and single-atom erasure leaves components with no usable bound (E11, E17); triangles through already-cut atoms
   (E20); atoms of degree 0–2 and self-loops in the stage-1 molecule (E23); the d-dimensional trilinear estimate of
   GIT20 that TARGET Prop 3.2 cites (E2g). All are repaired, E20 only for γ > 1/2.
5. **Exposition gaps** (omitted, routinely fillable):
   - the counting run of DH23 §§9–10 as reused by TARGET: E5, E7, E8, E10, E12, E13, E21, E22, E28;
   - regular objects and the vine and ladder estimates: E2e (order ranges), E14, E15, E40 (the `ladderl1new` sketch);
   - the flower section: E29, E32, E36–E38, E46;
   - the proof of Theorem 1.1: E2f.

**Deviations.** The Lean statements restrict TARGET's results to 1/2 < γ < 1, read the order-zero flower as the
identity, use d − γ in the flower normalization, and use DH21's product form of the dyadic cutoffs (Deviations, A
and C).

**Pinned sources** (sha256 of the TeX; line numbers below are physical lines of these files):
- TARGET: Y. Deng, Z. Hani, *Long time justification of wave turbulence theory*, arXiv:2311.10082v2,
  `WKE-Longer_times_Final_arXiv.tex`, `493eef6b7dec448b…`.
- DH23: Y. Deng, Z. Hani, *Derivation of the wave kinetic equation: Full range of scaling laws*, arXiv:2301.07063,
  `Revision_Submit.tex`, `c7e47dfabf5a4cca…`.
- DH21: Y. Deng, Z. Hani, *Full derivation of the wave kinetic equation*, arXiv:2104.11204,
  `Inventiones-Final_Version.tex`, `50d0e236a2df0cfd…`.
- DH21-2: Y. Deng, Z. Hani, *Propagation of chaos and higher order statistics in wave kinetic theory*,
  arXiv:2110.04565, `WKE_Hierarchy-Revised.tex`, `cc36fc22e96fe129…` (minor items and E2e only).
- GIT20: P. Germain, A. D. Ionescu, M.-B. Tran, *Optimal local well-posedness theory for the kinetic wave
  equation*, arXiv:1711.05587, `Kin8.tex`, `c02ccada9ba423c9…` (E2g only).

**Lean citations.** A declaration name in `code` refers to a declaration in this repository. A few declarations cited
in E2d, E26 and E32 were added on the main branch after the commit on which this file was first drafted (`5c6d256c`);
the entries say "on main" for those. Lean checks that exist
only in the project's working directories are marked "(working note, not included)"; they are reported as evidence
but are not claimed as proved here. Research notes, referee reports and scripts that support an entry are in
[`docs/research/`](research/INDEX.md). Ruling (R…), decision (D…) and ledger (F…) numbers refer to the project's
internal records (`docs/campaign/orch/RULINGS.md`, `docs/DECISIONS.md`, `docs/FINDINGS.md`) and are given only as
references.

## How to read the entries

**Status** (as recorded; never upgraded without an independent check):
- **CONFIRMED** — established by an explicit counterexample or proof, and checked by an independent refute-first
  verifier.
- **CANDIDATE** — written up, with the evidence cited; an independent check is pending.
- **SUSPECTED** — plausible from our analysis, but not established as an issue in the source.

**Class:**
- **ERROR** — a claim that is false as printed.
- **GAP** — a step whose justification is missing and whose repair is not routine.
- **EXPOSITION** — a step that is omitted but can be filled routinely; we describe the fill.
- **DEVIATION** — a formal statement of ours that differs from the source.
- **MINOR** — a typo, a small slip or a reading choice, harmless in context.

**Main theorem** (last column of the summary): the theorem itself is not refuted by any entry. The column says what the
entry does to the printed *proof*: "none" (harmless as it stands); "repaired" (a repair is given), with "in Lean" if
the repair is checked in Lean in this repository or on its main branch, "on paper (refereed)" if a written proof was
checked by an independent refute-first referee, and "on paper" alone otherwise; or "breaks for γ ≤ 1/2".

**Referees named in the entries.** "Independent" means not involved in writing the claim or the repair checked. The
flower entries (E29–E46) cite: the referee of the first integrated flower supplement (`REFEREE.md`); the referees of
the resolution packets (`REFEREE-2.md` for o63, o102 and o75; `REFEREE-73.md`, `REFEREE-82.md`, `REFEREE-83.md`), all
in [`docs/research/flowerest1/`](research/flowerest1/); an earlier referee of the flower design
(`flower-design-referee.md`); and an independent assessment of the printed proof of `flowerest1`
(`astra-flowerest1-report.md`), a single-assessor source audit that fixed its verdict before reading our claims.

## Summary table

| Id | Source, lines | Claim | Class | Status | Main theorem |
|---|---|---|---|---|---|
| E1 | DH23 Prop 9.6, L1818–L1822, L1885; DH23 L1681–L1690; TARGET L2192–L2197, L2114 | DH23 Prop 9.6 case (4), and the statements built on it, are false for 0 < γ ≤ 1/2 (necklace counterexample) | ERROR | CONFIRMED | breaks for γ ≤ 1/2; γ > 1/2 closed by a new refereed argument |
| E2a | DH21 L1070, L1079, L1737, L1767; TARGET L1154 | sign of the χ_∞ term in DH21 Lemmas 5.8/7.3: 𝒥B̃_{𝒬,Z} = (−1)^{\|Z\|}𝒥B̃_𝒬, so the per-couple weight in TARGET (regref1-3) needs (−1)^{\|Z\|} | ERROR | CONFIRMED | none (main sums unaffected); per-couple bound corrected in Lean |
| E2b | DH23 Lemma `ylem1`, L1937–L1948 | the lemma misses several molecules (Q, T, a 5-atom molecule, two infinite families) | ERROR | CANDIDATE | none directly; it underlies E1 |
| E2c | DH23 L1911–L1912 | in the proof of Prop 10.2, "the total number of operations is ≤ C(r₁+r₂)" is false | ERROR | CANDIDATE | none (short repair) |
| E2d | TARGET L1814, L1817 | for vines (V)–(VIII) the same-direction core has the opposite relative sign; `sumint` must be used in a signed form | ERROR | CANDIDATE | repaired (signed `sumint`, proved in Lean on main) |
| E2e | DH23 L1002, L1168; TARGET L951; DH21-2 L587, L602 | regular-couple asymptotics are used at orders beyond the range in which they are stated | EXPOSITION | CANDIDATE | repaired (range extension of DH23 Prop 6.4 in Lean) |
| E2f | TARGET L752–L758, L314–L316, L817–L821 | three steps of the proof of Theorem 1.1 are asserted without proof | EXPOSITION | CANDIDATE | none |
| E2g | GIT20 Remark 2.6 (L593); TARGET L2515 | the d-dimensional L²_s trilinear estimate is asserted without proof; GIT20's d = 3 argument fails for d ≥ 4 at one step | GAP | CANDIDATE | none (only the blow-up criterion of Prop 3.2 uses it); repaired on paper |
| E2-m | see the table in E2 | minor items m1–m51 (m28 moved to E41) | MINOR | CANDIDATE | none |
| E3 | DH23 Def 5.1, L1421, L1481 | vine (II) must include the one-double-bond case m = 1 | MINOR | CANDIDATE | none with this reading |
| E4 | TARGET L1846 | "replace ε by 1 … sum trivially" fails for vine chains longer than d/γ | GAP | CONFIRMED | repaired (reduction in Lean; one input proved only in a working note) |
| E5 | TARGET L2079 | (finalsbest1) does not follow from Prop `ladderl1new` as stated: ladders are coupled by the time order | EXPOSITION | CONFIRMED | repaired in Lean |
| E6 | TARGET L2189, L2142 | the invariant 4V − 2E − 2(V_α+V_β) is not preserved by the blanket Operation 2 cut | MINOR | CANDIDATE | none (DH23's formulation avoids it) |
| E7 | DH23 L1793–L1794 | the pair count in the triangle step with ΔF = 1 assumes a nonzero fixed difference | EXPOSITION | CANDIDATE | none |
| E8 | DH23 L1876 | Prop 9.6 proof, "only remove ε-atoms": degree-1 α/β atoms must also be deleted | EXPOSITION | CANDIDATE | none |
| E9 | TARGET L2185, L2189 | "at most R imperfect components" fails after tame-atom removals (R + 2t) | MINOR | CANDIDATE | none |
| E10 | DH23 L1815 | "the vine is not changed" although its joints are cut | EXPOSITION | CANDIDATE | none |
| E11 | TARGET L2152, L2218 | Remark `remtame` (i), "cut at v and proceed normally", is not trivial; Prop 9.6 fails on a resulting component | GAP | CANDIDATE (part (a) CONFIRMED) | repaired in Lean |
| E12 | DH23 L1876 | the odd-component argument is written for a degree-1 odd atom | EXPOSITION | CANDIDATE | none |
| E13 | TARGET L2101 | the DV selection rule leaves a case unspecified | EXPOSITION | CANDIDATE | none |
| E14 | TARGET L1747 | the time domain 𝔅 is not the kernel's domain when a lower child is a leaf | EXPOSITION | CANDIDATE | none |
| E15 | various | further exposition points | EXPOSITION | CANDIDATE | none |
| E16 | TARGET L2152 | "a ZG v₃ in Operation 2 must be tame by `subpro` (3)" is false when v₃ is a hinge atom | ERROR | CANDIDATE | repaired in Lean |
| E17 | TARGET L2152, L2218, L2189, L2193–L2197 | single-atom erasure leaves components with no usable bound; "imperfect = odd" contradicts L2218 | GAP | CANDIDATE | repaired in Lean |
| E18 | TARGET L1918 | "J̃_𝒬(t,s) equals 0 if t = L_r" is false for trivial couples and trees | ERROR | CANDIDATE | none after repair (in Lean) |
| E19 | TARGET L2213 | "p_sb ≤ p_op" should be "p_sb ≤ 2p_op" | MINOR | CANDIDATE | none |
| E20 | DH23 L1777, L1791–L1795; TARGET L2126, L2142, L2189 | triangles containing an already-cut atom ("ghosts"): the per-step bound fails | GAP | CANDIDATE | repaired in Lean for γ > 1/2; open for γ ≤ 1/2 |
| E21 | DH23 L1803; TARGET L2131 | the ι ball when the hitting cut has been deleted | EXPOSITION | CANDIDATE | none |
| E22 | TARGET L2140 | a triple bond need not lie in a collected object | EXPOSITION | CANDIDATE | none |
| E23 | TARGET L2122, L1306 | the stage-1 molecule can have atoms of degree 0, 1, 2 and self-loops, which DH23's proof does not cover | GAP | CANDIDATE | repaired in Lean |
| E24 | TARGET L2065, L2067 | moving weights and derivatives onto decoration-dependent leaves breaks the twist-class cancellation of `vineest` | GAP | CANDIDATE | repaired (key identity in Lean) |
| E25 | TARGET L1909 | the class count consumes part of the bad-vine gain | MINOR | CANDIDATE | repaired (half the gain suffices; in Lean) |
| E26 | TARGET L1954–L1957 | the printed (redvine) factorization is false as an identity: lower-child slots keep the lower joint's clock | ERROR | CANDIDATE (independent referee pending) | repaired: exact replacement identity; unweighted case in Lean (sealed `layergarden_v2`), weighted flower case on paper |
| E27 | TARGET L1944 | "at most 2ⁿ" refined classes can fail | MINOR | CANDIDATE | none (the final count survives) |
| E28 | TARGET L2126, L2138, L2156–L2161 | degree-2 cuts need explicit bookkeeping of the isolated half | EXPOSITION | CANDIDATE | none |
| E29 | TARGET L2259, L2261, L2287 | reusing the skeleton and twist machinery for flower gardens needs marked bookkeeping (caps, components) that is not written; the skeleton theorem itself holds for any garden | EXPOSITION | CONFIRMED | repaired on paper (refereed) |
| E30 | TARGET L2265, L2295 | fixing the flower-parent resonance does not remove the Dirac time trace; DH21 L2684–L2694 has the (unlayered) mechanism | GAP | CONFIRMED | repaired on paper (refereed: o73 Thm 7.3′) |
| E31 | TARGET L2297, L2045 | leaving special-node SG vines unspliced invalidates the use of `subpro` (4) | GAP | CONFIRMED | repaired on paper (refereed: o75 Thm 7.5′) |
| E32 | TARGET L2312 | the root-time derivative needs root excision; width-four components remain | EXPOSITION | CONFIRMED | repaired: couple clause in Lean on main; flower trees on paper (E45) |
| E33 | TARGET L2283–L2285, L2294, L2299 | the cutoffs need DH21's product partition, and the M₁ gain must be extracted without breaking twist-class cancellation | GAP | CONFIRMED | repaired on paper (refereed: o63 Thm 6.3′) |
| E34 | our `layergardenFlower_v2` | its max-form cutoffs are not the source's product partition | DEVIATION | — | n/a (our statement; replaced by `layergardenFlower_v3`) |
| E35 | TARGET L2299 | the time integration needs face estimates; the per-tree M₂^{−P/9} goes beyond DH21 Cor 11.3 | GAP | CONFIRMED | repaired on paper (refereed: supplement Lemma 9.1, o73, o82) |
| E36 | TARGET L2294, L2297; L1452, L1902 | the cutoff weights are not checked to agree across twist classes (exactly, or up to \|r\|-terms) | EXPOSITION | CONFIRMED | repaired on paper (refereed) |
| E37 | TARGET L2294; `vineest` L1742–L1752; `sumint` L1595–L1625 | a cutoff inside a spliced vine must enter the vine estimate's weight | EXPOSITION | CONFIRMED | repaired on paper (refereed) |
| E38 | TARGET L2294, L2297; `proplayer1` L953–L956, L1007–L1013 | a cutoff inside an incoherent regular object needs `proplayer1` with that factor | EXPOSITION | CONFIRMED | repaired on paper (refereed) |
| E39 | TARGET L2299 | "these cutoffs play no role" fails for upper M₂ cutoffs inside coherent regular trees on the stem | GAP | CANDIDATE | repaired on paper (refereed: o82 Thm 8.2′) |
| E40 | TARGET L1981, L1989–L1991 | the sketch of `ladderl1new` does not handle the gap indicators (G2) or the conservation law coupling the last rung sum (G3) | EXPOSITION | CANDIDATE | none (filled on paper, refereed, and in Lean) |
| E41 | TARGET L2264–L2265; DH23 L1995–L1996 | the flower prefactor (δ/(2L^{d−1}))ⁿ should be (δ/(2L^{d−γ}))ⁿ; the difference L^{(1−γ)n} is not absorbable | ERROR | CONFIRMED | none once corrected |
| E42 | TARGET L2264, L2270–L2273 | the order-zero flower tree must be read as the identity: 𝒳 = I + 𝒳_reg, and (flowerest2) bounds 𝒳_reg | DEVIATION (reading) | — | none |
| E43 | TARGET L2295, L2297, L2299 | the intermediate loss figures (L^{20d} per vine, L^{200dP}, L^{100dP}) are not established; larger L^{O(dP)} losses fit | MINOR | CANDIDATE | none |
| E44 | TARGET L2299, L2081 | "these cutoffs play no role" fails for upper M₂ filters on large-gap ladder rungs | GAP | CONFIRMED | repaired on paper (refereed: o83 Thm 8.3) |
| E45 | TARGET L2327–L2331 | the dagger and derivative variants used for `fixedpoint` add an unprotected grandparent pin and coincident faces | GAP | CANDIDATE | repaired on paper (o104 Thm 10.4), partly refereed |
| E46 | TARGET L2290 | the expansion remainders are not shown to carry the cutoff gains | EXPOSITION | CANDIDATE | repaired on paper (refereed) |

---

## Deviations of the frozen Lean statements from the papers

The formal development states the results it targets as *frozen* Lean statements in `WaveTurbulence/Frozen/`
(theorems with `sorry` bodies awaiting proof, and sealed definitions). Their approval is recorded in
`docs/DECISIONS.md` (D6–D10, D13, D16) and on the approval pages in `docs/review/`. This section lists every recorded
way in which they differ from the printed text. "Weaker?" says whether the Lean statement claims less than the source.

### A. The main theorem (TARGET Theorem 1.1, L314–L318)

Lean: `WaveTurbulence.main` (0 < γ < 1) and its restricted successor `WaveTurbulence.main_v2` (1/2 < γ < 1). Both are
frozen and unproved.

| Source text | Lean reading | Reason | Weaker? |
|---|---|---|---|
| "Fix d ≥ 3 and γ ∈ (0,1) (or assume γ = 1 but replace 𝕋_L^d by a rectangular torus …)" (L314) | `main`: 0 < γ < 1 on the square torus. `main_v2`: 1/2 < γ < 1. | The γ = 1 generic-torus case is out of scope (D2). The range γ ≤ 1/2 is removed in `main_v2` because the printed proof fails there (E1; D9, D10). | Yes, for `main_v2`. `main` keeps the full range and remains open. |
| "the expectation 𝔼 is taken assuming (NLS) has a smooth solution on [0,T]" (L318) | ∫ 1_F ‖û(t,n)‖² dP, where F is the solvability event: an expectation restricted to F, not conditioned on it. | This is the quantity the proof computes (L818–L819); D6. | No. Since P(F) ≥ 1 − e^{−(log L)^{40d}} and the expectation is bounded, the two readings differ by far less than L^{−θ}. |
| "(NLS) has a smooth solution u(t,x) up to time T" (L316); "smooth" is not defined | `IsSmoothNLSSolution` (a C^∞ solution on [0,T]); the bound is asserted for every family U of such solutions on F. | Makes the notion precise; D6 (ledger F8). | No (smooth solutions are unique). |
| — | `MeasurableSet F` is an extra conclusion. | So that P(F) is defined; D6. | No (adds a conclusion). |
| the Dirac deltas in (COL), L307 | the hyperplane integral (2\|ℓ₁\|)⁻¹∫_{ℓ₁^⊥} | The standard meaning; D6. | No. |
| "τ_* ∈ (0, τ_max)" with φ the solution of (WKE) (L314) | every τ_* > 0 and every Schwartz-class solution φ of (WKE) on the closed interval [0, τ_*] (`IsWKESolution`) | Equivalent by Prop 3.2 (frozen `wkelwp`); D6. | No. |
| random data (data); probability ≥ 1 − e^{−(log L)^{40d}}; ⟨k⟩ | data through Fourier coefficients (`initialCoeff`) with independent standard circular complex Gaussians; (log L)^{40d} as printed; ⟨k⟩ = (1+\|k\|²)^{1/2} | Conventions fixed explicitly; D6. | No. |

### B. Proposition 3.2 (`wkelwp`, TARGET L598–L601)

Frozen as printed; no deviation is recorded. For d ≥ 4 its blow-up criterion rests on GIT20 Remark 2.6, which is
unproved as written there (E2g).

### C. The intermediate statements used by the proof of Theorem 1.1

**The γ restriction.** `propansatz_v2`, `layergarden_v2`, `fixedpoint_v2`, `layergardenFlower_v2` and
`layergardenFlower_v3` are their originals verbatim with the hypothesis `1 / 2 < γ` added (D10; for v3 also D13). The
originals stay frozen and open. Weaker: yes, in γ. The reason is E1: the printed proof fails for γ ≤ 1/2 at DH23
Prop 9.6. The written completion of the flower estimate (E29–E46) is likewise proved only for 1/2 < γ < 1: it uses the
counting inputs repaired for that range (E1's γ > 1/2 argument, and E20, whose two-ghost case needs 8η ≤ 2γ − 1), and
it chooses η small depending on γ with 8η ≤ 2γ − 1. `layergardenFlower_v4` (D16) is `layergardenFlower_v3` without
the restriction, so it covers the full range 0 < γ < 1; it is frozen and open.

**Recorded deviations of each statement** (from the statements' docstrings; the approval pages
`docs/review/WAVE-B-B1.md` and `docs/review/WAVE-B-B2.md` give the reasons in full):

| Statement (source) | Deviation | Effect |
|---|---|---|
| `propansatz` (TARGET Prop `propansatz`, L689–L707) | a new item for intermediate times t ∈ (p, p+1], with constant 2 | adds a conclusion; Theorem 1.1's sup over t needs it (E2f (a)) |
| | the correction R_p is a real C^{Λ_p} function on ℝ^d, measured in the ℝ^d norm | reading of the source's lattice-or-ℝ^d object |
| | the cumulant in (ansatz1) is written as the moment; the sums in items (3)–(4) are a shared truncated sum, equal to the untruncated ones (`truncSum_untruncated`) | equivalent forms |
| | uniqueness in a stated solution class; measurability and integrability conjuncts; symmetric events as preimages of invariant sets of data | added precision; adds conclusions |
| `layergarden` (TARGET Prop `layergarden`, L761–L779) | deterministic: the induction hypothesis is replaced by the explicit hypothesis `RemainderBound` on the corrections | the proof uses the induction hypothesis only through these bounds (L949–L951); not weaker in use |
| | every t ∈ (p, p+1] instead of t = p+1 | stronger; needed at L821 and L2309 |
| | (estcouple) and (estcouple2) merged; shared sums; general carriers | equivalent forms |
| `fixedpoint` (TARGET Prop `fixedpoint`, L780–L794) | contraction constant ½; continuity in Z; (1−ℒ₁)⁻¹ expressed by unique solvability; conjugates on negative leaves (minor item m5) | explicit constants and equivalent forms |
| `layergardenFlower` (TARGET Prop `flowerest1`, L2279–L2305) | only the deterministic per-order core is frozen; the moment expansion is left to the proof | the frozen statement is an intermediate form of the proposition |
| | per-order bounds with δ^{2νN} (flowers) and δ^{νN} (couples); order range N ≤ N_{p+1}⁴ (L2290) | explicit form of the source's bounds |
| | prefactor (δ/(2L^{d−γ}))ⁿ instead of the printed (δ/(2L^{d−1}))ⁿ | corrects an erratum (E41); not weaker |
| | the kind 𝒳 excludes the trivial flower tree; 𝒴 and 𝒲 replace the top bound | the order-zero reading 𝒳 = I + 𝒳_reg, with (flowerest2) bounding 𝒳_reg on p < s < t < p+1 (E42); the only meaningful pointwise reading, not weaker |
| | explicit dyadic cutoffs: in v2 a cutoff of a maximum (E34); in v3 DH21's product form (D13) | TARGET says only "smooth cutoff function" of a maximum (L2283, L2285); v3 reads it as DH21's per-variable partition grouped by the largest scale (DH21 L2731, L2735; E33). v2 differs from that reading (E34) |
| | derivative patterns and † as designated nodes, removed phases and weights; L^{2(100d)³P} for derivative patterns; a couple clause for ℒ₀; per-tree choices of patterns | explicit form; more general than the consumer needs |
| `nlsAkBridge` (TARGET L540–L566, L817–L819) | precise correspondence between smooth NLS solutions and the Fourier-side system; measurability of the observables at t ∈ [0,T]; rapidly decreasing data; 1 ≤ 𝔇 | makes the paper's implicit step precise (E2f (b)) |
| `wkeTaylor` (TARGET L752–L758) | the expansion at every t ∈ [p,p+1]; interval integrability of the integrands added | stronger; adds conclusions (E2f (c)) |
| `sumint` (TARGET Prop `sumint`, L1595–L1640) | weights on ℝ^d; an explicit constant in place of C₀^M; unit intervals inside [0, 𝔇]; two typo fixes (minor item m19); a size hypothesis M ≤ N₁⁴; shifts are integer combinations with coefficient sum 1; every Λ_v ≥ 1 | faithful to the printed (unsigned) statement; the proof chain uses a signed form (E2d) at phase 2δ (minor item m18) |
| `countLemma` (TARGET L2459–L2466; DH23 Lemma A.2 (1), (3)) | \|r\| ∼ P with an explicit constant c₀, and \|r\| ≤ c₀ when P = 1; constants uniform in δ for L ≥ L₀(δ) | explicit form; DH23's bound needs δ⁻¹L^{−10η} ≤ (log L)^{−2} |
| `atomCountLemma` (TARGET L2467–L2478) | k ≠ 0 in the first bound for signs (+,−); "\|r\| ≥ L^{−γ+η}" read as \|k\| ≥ L^{−γ+η}; (atomcountbd3) omitted (unused); signs (+,−,+) for r = 3 | the printed first bound is false at k = 0 (minor item m33) |
| `canonicalCharacterization` (TARGET L657–L668, L888–L897, L2262) | uniqueness of the decomposition of a given garden, in place of a construction from data | equivalent (the construction is a bijection onto its image) |
| `regularAsymptotics` (TARGET L1145–L1232) | (K*)_app defined by explicit recursions; regular objects as (code, carrier) pairs; inputs with finite 𝔖^{40d,40d} norm instead of C^∞; order range n ≤ N_{p+1}⁴ (E2e); item 4 stated for (K*)_app (minor item m7); special-subset weight ∏_{𝔫∈Z}(−ζ_𝔫πi)⁻¹ (E2a) | more general inputs; corrects two source slips |
| `incoherentDecay` (TARGET L953–L956) | arbitrary layerings; inputs as in `regularAsymptotics` | more general |

**Readings fixed in sealed definitions.**
- `SNorm`: classical derivatives for Λ₁ ≥ 1. A function with bounded but discontinuous top-order derivatives has a
  finite source norm but infinite `SNorm`. Every consumer supplies C^{Λ₁} functions.
- `XNorm`: an integrability guard and almost-everywhere C^{Λ₁} regularity of the time Fourier transform (ledger F80).
  The unrestricted norm is infinite for some functions with finite source norm (for example sinc); the restricted
  norms over bounded sets, the only ones used, agree with TARGET's up to an absolute factor.
- `chi0` = `Real.smoothTransition (2 − 2|x|)`: a C^∞ cutoff, with TARGET's Gevrey condition read as in minor item m4.
- `SumintDatum`: in hypothesis (ii) of `sumint`, an index with no predecessor is read as "ℓ_v itself is a signed sum".
- `RegCpl.app`, `RegChain.app`: the special-subset weight is `specialWeight` = ∏_{𝔫∈Z}(−ζ_𝔫πi)⁻¹, correcting the
  sign of E2a.

### D. Formalization issues (not errata)

These concern our own statements, encodings or interfaces, not the papers:
- Draft-statement defects found and fixed before the freeze: the flower clause `PatValid`/`dChild` (F68), the ∂ₜ
  clause of `coupleSum` (F78), the 𝔛 norms at derivative order ≥ 1 (F80), and earlier F53, F56, F59, F66.
- Our v2 max-form flower cutoffs (E34), replaced by v3 (D13).
- R57 F-KIND (a statement of ours hard-wired one kind; TARGET's Def `lftwist` covers couples), R68
  TraceCounterexample (a norm-only trace lemma is false for arbitrary functions; the paper's kernels are continuous),
  FINDING-ANCH (profile 1 at anchored leaves has infinite Sobolev norm in our encoding; TARGET treats 1_{k_𝔣=k′}
  explicitly at L2295), FINDING-TIVINE (our Stage-1 interfaces could not carry weights).
- Shapes defined only by figures (vines, ladders, mini couples and trees, cuts: ledger F12, F19). Textual definitions
  had to be written and checked (`docs/campaign/orch/figure-defs.md`); this is not a defect of the papers.

---

## E1 — DH23 Prop 9.6 (`lgmolect`), case (4), is false for 0 < γ ≤ 1/2

**Status:** CONFIRMED. **Class:** ERROR. **Main theorem:** the printed proof breaks for 0 < γ ≤ 1/2; the theorem is
not refuted. For 1/2 < γ < 1 the failing case is closed by a new argument (F75 below).
- Ledger: F69b.
- Research note: [`docs/research/dh23-prop96-case4.md`](research/dh23-prop96-case4.md); scripts and outputs:
  [`docs/research/dh23-prop96-case4-scripts/`](research/dh23-prop96-case4-scripts/).
- Independent adversarial referee report: [`docs/research/dh23-prop96-referee.txt`](research/dh23-prop96-referee.txt).

**Statements affected.** All are false for 0 < γ ≤ 1/2.
- **DH23 Prop 9.6 `lgmolect`, estimate (finalcount), L1818–L1822.** Its proof, case (4), is at L1883–L1886.
- **DH23 Prop `kqmainest2`, L1681–L1690.** It is proved from Prop 9.6 (L1823–L1826) and fails on molecules of bounded
  size.
- **TARGET Prop `lgmolect`, L2192–L2197.** Its proof (L2197) says that for perfect components it "is exactly the same
  as Proposition 9.6 of [DH23]".
- **TARGET (finalcount1), L2114,** at R = 1.

TARGET claims its main theorem for all γ ∈ (0, 1) (L314). The physically distinguished value γ = 1/2 (L325) lies in the
failing range.

### The source text

DH23 Prop 9.6 (L1819–L1821) asserts, for each component 𝕄₀ of the final molecule 𝕄_fin:

> 𝔄₀ ≲ ∏_v^{(α)} L^{−(γ+3η)/2+κ_vη} R_v^{−1} · L^{(γ₀+2η²)V_β − (2γ₀+5η²)G} · L^{−η⁵ρ₀}.

For a component with V_α = 0 and V_β = 2 (an even component, G = 1), the right side is at most a negative power of L.
The required estimate is 𝔄₀ ≲ L^{−η²−η⁵ρ₀}.

Case (4) of the proof (L1883–L1886) reads:

> (4) If V_α=0 and V_β=2, then choose all the chains of β-atoms and perform operation (d) to them. The resulting
> molecule 𝕄₁ is 4-regular and has at most two triple bonds. Therefore, by Proposition [moleprop4] (2), we know that
> either 𝔄₁ ≲ L^{−η/5} or 𝕄₁ is formed by removing the two joints of a vine and adding one new bond between the pair
> of atoms connected to each joint. […] In the latter case, **an enumeration shows that 𝕄₀ must be a vine and is thus
> LG** due to Proposition [finalmole], so we may now perform operation (c) to the chains of β-atoms in 𝕄₀. […] we get
> that 𝔄₀ ≲ L^{−η/2}, so (finalcount) again follows by interpolation.

### What is wrong

The enumeration claim at L1885 is false: 𝕄₀ need not be a vine. The smallest non-vine case-(4) components are:
- the 4-atom Q-block;
- three 5-atom T-blocks;
- five 7-atom T₁-blocks;
- a 9-atom block.

The source argument (vine ⇒ large gap ⇒ operation (c) gains) uses only the large gap, not the vine shape. So it covers
every 𝕄₀ whose β-gap is large, but not a non-vine component whose two β-atoms come from small-gap cuts.

For γ ≤ 1/2 a small gap makes the β-constraints void, and the count of such a component is of order 1, not
L^{−η²}. The Q-block is repaired by reading vine (II) as including m = 1 (E3 below). The T-blocks give the
counterexample.

### The counterexample: the necklace N_m

**Molecule.** Take joints w₀, …, w_m.
- **T-bead B_i, for 1 ≤ i ≤ m.** It lies between a = w_{i−1} and b = w_i, with interior atoms e_i, g_i, f_i and bonds
  - a→e, b→e,
  - e→g (twice),
  - g→f (twice),
  - f→a, f→b.

  It is a triangle of double bonds with both copies of one double bond subdivided by the two joints.
- **Odd bead B₀.** It lies between w_m and w₀, with interior atoms o₁, o₂ and bonds
  - w_m→o₁, w₀→o₁,
  - o₁→o₂,
  - o₂→w_m, o₂→w₀.

N_m has n = 4m + 3 atoms and 8m + 5 = 2n − 1 bonds, and no triple bond. Two atoms have degree 3: o₁ with
(in, out) = (2, 1) and o₂ with (1, 2). Every other atom has (2, 2).

**Facts** (proofs in the research note, §3, each checked by a script in `docs/research/dh23-prop96-case4-scripts/`):
1. **Prime couple (Lemma 3.2).** N_m is the molecule 𝕄(𝒬) of an explicit prime, non-degenerate couple 𝒬, directions
   included.
   - **Construction:** a spanning forest of two trees rooted at o₁, o₂ gives the PC bonds. The other bonds become LP
     bonds with a leaf at each end. Set ζ_v = + iff the parent bond points v → parent.
   - **Primality:** there is no triple bond.
   - **Mechanical check** (`necklace.py`, m ≤ 20): 𝕄(𝒬) is rebuilt from 𝒬 bond by bond, and non-degeneracy is checked.
   - **Referee check:** the referee re-derived this with randomized couple constructions up to m = 20. In TARGET,
     putting all nodes in layer 0 gives a canonical layered couple in 𝒞₁ satisfying (a)–(f) of L2096–L2109.
2. **No vine-like objects (Lemma 3.3).**
   - The blocks of N_m are exactly the runs B_i ∪ … ∪ B_j with joints w_{i−1}, w_j.
   - There are no hyper-blocks, and no block is isomorphic, even undirected, to any vine (I)–(VIII) with any number of
     rungs, or to the Q-block. One bead has 5 atoms and no vine has 5 atoms; a longer run has an interior cut atom,
     and no vine template has one.
   - Hence the vine collection 𝒞 is empty (DH23 Lemma 8.1), 𝒬_sub = 𝒬_sk = 𝒬, 𝕄(𝒬_sub) = N_m, Δ_sub = 0, and there
     are no hinge atoms.
   - **Mechanical check:** `vinefree.py` enumerates all atomic groups for m ≤ 4.
3. **Stage 2 (Lemma 3.4).** Take the decorations where every joint w_i is small-gap, with its designated pair the two
   bonds in the next bead and gap ±r, and every other atom large-gap. Then, for **every** order of Step 3:
   - Steps 1, 2 and 4 do nothing;
   - the first Step-3 cut is an α-cut and every later one is a β-cut;
   - the final components are the beads;
   - for m ≥ 3, some T-bead component has V_α = 0 and V_β = 2, so it falls in case (4).

   **Mechanical check** (`cuts.py`): all 24 orders for m = 3 and all 120 for m = 4. For m = 2 the conclusion fails, as
   expected.

**Count of one T-bead component (Lemma 4.1).** Fix d ≥ 3, 0 < γ ≤ 1/2, δ ∈ (0, 1/2], and the β-gap r = e₁/L. The
small-gap label is R = L^{−1}, which is allowed (DH23 L1752).

Let 𝕋 be the T-bead with:
- ε-atoms e, g, f and β-atoms b, b′;
- bonds b→e (x), b′→e (x′), e→g (p, p′), g→f (q, q′), f→b (y), f→b′ (y′);
- c_e = c_g = c_f = 0, c_b = r, c_{b′} = −r.

Then y = x − r, y′ = x′ + r, p′ = x + x′ − p and q′ = x + x′ − q. The vectors x, x′, p, q are free, so χ(𝕋) = 4.

The resonance factors are:
- Γ_e = 2(p − x)·(p − x′);
- Γ_e + Γ_g = 2(q − x)·(q − x′);
- Γ_b = 2x·r − |r|²;
- Γ_{b′} = −2x′·r − |r|²;
- ΣΓ = 0.

These identities are checked by `count_check.py`.

Draw x, x′, p, q from the balls of radius 1/4 around 0, 10e₁, 10e₂ and 10e₃.
- **Large-gap constraints hold.** Every opposite pair at e, g, f differs by at least 8.
- **The β-constraints hold automatically.** We have |Γ_b − β_b| = 2|(x − x⁰)·r| ≤ |r|/2, and likewise for b′.
  Moreover |r| = L^{−1} ≤ λ := δ^{−1}L^{−2γ} **exactly because γ ≤ 1/2**. So the width-λ β-constraints are void for
  the whole family.
- **Pigeonhole.** The family has at least cL^{4d} members, and (Γ_e, Γ_g) ranges over [−2000, 2000]². So some λ-cell
  contains at least c′δ^{−2}L^{4d−4γ} members. One more halving fixes β_f, since Γ_f = −ΣΓ_rest.

Hence 𝔠(𝕋) ≥ (c′/2)δ^{−2}L^{4(d−γ)} and

> **𝔄(𝕋) ≥ c_d (C⁺)^{−4},** a constant independent of L.

**Inheritance (Lemma 4.2).** Every member of this family is the restriction to 𝕋 = B₂ of a decoration of N₃ in the
class above, satisfying DH23 Remark `subcondition` and `kqmainest2` (i)–(ii):
- the other beads use the same construction shifted by 100·i·e₁;
- the odd bead uses, for example, s = 300e₁, s′ = 400e₁, t = s − r, t′ = s′ + r, u = s + s′ + 10e₂;
- non-resonance holds because every opposite pair has a nonzero gap.

**Contradiction with DH23 Prop 9.6 (Prop 4.3).** The T-bead component of N₃ is a case-(4) component of 𝕄_fin in every
Step-3 order, with 𝔄₀ ≥ c_d(C⁺)^{−4}. Prop 9.6 demands 𝔄₀ ≲ L^{−η²−η⁵ρ₀} with ρ₀ ≤ 5. This is impossible for L large.
The same component is a perfect component in TARGET, so TARGET `lgmolect` (L2193) fails too.

**Contradiction with `kqmainest2` (Prop 4.4).** Let m ≥ (3d+1)η^{−6}. Given r the beads are independent, so

> 𝔠(N_m) ≥ [(c′/2)δ^{−2}L^{4(d−γ)}]^m.

The right side of `kqmainest2` is (C⁺δ^{−1/2})^{4m+3} L^{(d−γ)(4m+3)} L^{−η⁶ρ}, with Δ_sub = 0, ∏𝔛 = 1 (there is no
ladder) and ρ ≥ m + 3. The ratio of left to right is at least

> [(c′/2)(C⁺)^{−4}]^m (C⁺)^{−3} δ^{3/2} L^{η⁶(m+3) − 3(d−γ)} ≥ c(m)·L → ∞.

TARGET (finalcount1) at R = 1 fails the same way. It also asks for L^{−4η⁶p_sb} with p_sb ≥ m + 1, so it fails once
4η⁶(5m+4) > 3(d−γ).

### Scope

- **Not refuted:** TARGET's main theorem, DH23's main theorem, and TARGET `layergarden` as a statement.
- **Why the necklaces do not refute them:** these couples are few (C^n of them), and their contribution per couple,
  hence per congruence class, is heuristically about (Cδ^{1/2})^n L^{−γ(2d−1)}. That is a fixed negative power of L.
  (The research note's earlier O(L^{γ−d}) is right only at γ = 1/2; it is corrected in
  [`docs/research/gamma-le-half-repair-1-notes.md`](research/gamma-le-half-repair-1-notes.md), Q1.)
- **What is broken:** the proof chain, at the intermediate statements listed above.
- **Why no repair inside stage 2 works:** the only slack in a necklace is that of the first α-cut, of size
  R^{d−2}L^{−3η}, and a necklace with ≫ η^{−6} beads exhausts it.

### Related findings

- **F73: the analytic per-class bounds fail too.** DH23 `kqmainest1` (L1632–L1640) and TARGET (finalsbest2) (L2078)
  also fail on the necklace couples for 0 < γ < 1/2, and for γ = 1/2 with δ small.
  - On these couples K_𝒬(t,t,k) = ζ(𝒬) 2^{−n} δ^{2m+2−d} L^{−γ(2d−1)} [A_m + o(1)], with n = 4m + 3 and A_m ≠ 0 for
    explicit data. There is no gain per bead.
  - TARGET (finalsbest2) fails once η⁶(4m+3) > γ(2d−1).
  - So no counting-only repair suffices.
  - Note: [`docs/research/kqmainest1-necklace.txt`](research/kqmainest1-necklace.txt). Status: CANDIDATE (derived; error
    terms not fully explicit).
- **F75: the range γ ∈ (1/2, 1) is closed by a new argument,** confirmed by an independent referee
  ([`docs/research/case4-gamma-above-half.txt`](research/case4-gamma-above-half.txt) and
  [`…-referee.txt`](research/case4-gamma-above-half-referee.txt)).
  - Operation (c) on the first β-chain, using DH23 Lemma A.3(1).
  - Operation (d) on the second β-chain.
  - At most two (Y)-sequences.
  - The γ > 1/2 branch of DH23 Lemma A.2(3).

  Together these give 𝔄₀ ≲ δ^{−1}(log L)^C L^{−10η}, for η ≪ γ − 1/2.
- **E2b: DH23 Lemma `ylem1`**, on which L1885 rests, is itself false.
- **E3 (F72): the Q-block.** DH23 Def 5.1 / vine (II) (L1421) must include the one-double-bond case m = 1. Without it,
  Q-bead necklaces break the same four statements for all γ < 2/3.

### Consequence for the formalization

The project owner decided (2026-11-04; `docs/DECISIONS.md` D9, D10):
- **Restrict the endpoint.** The formal endpoint is restricted to γ ∈ (1/2, 1) by versioned successors of the frozen
  statements: `main_v2` and the affected intermediate statements (see Deviations, A and C).
- **Research the repair** for γ ≤ 1/2 separately.
- **Write to the authors.** A letter was drafted (`docs/review/LETTER-DENG-HANI-DRAFT.md`).

**Repair route for γ ≤ 1/2 (research; refereed three times; not formalized).** A first research note
([`docs/research/gamma-le-half-repair-1-notes.md`](research/gamma-le-half-repair-1-notes.md)) proposes that the chain
can be repaired without a new analytic estimate:
- T-type blocks are exactly neutral and fit the hypotheses of the existing DH23 Cor `sumintest3` / TARGET Prop
  `sumint` (Theorem N; checked on all 4446 directed T-type classes up to 15 atoms).
- So they can be spliced in stage 1 as an enlarged vine family, after the combinatorial extensions of Lemma 8.1,
  `subsetvc`, Props 9.1, 9.5 and 9.6.

**First independent referee (2026-11-04,
[`docs/research/gamma-le-half-repair-1-referee.md`](research/gamma-le-half-repair-1-referee.md)): the route is sound.**
No counterexample was found.
- **Analytic core: confirmed.** T-vines meet the hypotheses of `sumintest2`/`sumintest3`/`sumint` literally:
  8892/8892 cases up to 15 atoms and 14928/14928 at 17 atoms; 800/800 mixed chains.
- **Combinatorial extensions:** confirmed on all data up to 19 atoms, heuristic beyond. A written rung-locality proof
  was still needed.
- **Still open at that point:** TARGET with R ≥ 2 gardens, the flower/parametrix sections, and Prop 10.4(1) for T∖ℓ.
- **The note's own errors (E1–E5 of the referee report)** do not affect the route.

**Second research pass and second referee (2026-11-05).** Notes:
[`docs/research/gamma-le-half-repair-2-notes.md`](research/gamma-le-half-repair-2-notes.md). Report:
[`docs/research/gamma-le-half-repair-2-referee.md`](research/gamma-le-half-repair-2-referee.md).
- **Confirmed:** the R ≥ 2 gardens, the flower and parametrix sections, Prop 9.6 case (5), the ylem1′ list, and a
  Lean-ready predicate `IsTVine` for the enlarged γ ≤ 1/2 vine family.
- **Rung-locality:** proved for all sizes after two repairs the referee supplied (a patch to Lemma 1.14(c), and a
  parity argument for hyper-member removal).
- **Still open for all sizes:** one structural fact used by `layervine`, checked up to 21 atoms.
- **Not yet in Lean:** the base cases need a verified enumeration of T-vines with at most 13 atoms.

**Third research pass and third referee (2026-11-05).** Notes:
[`docs/research/gamma-le-half-repair-3-notes.txt`](research/gamma-le-half-repair-3-notes.txt). Report:
[`docs/research/gamma-le-half-repair-3-referee.md`](research/gamma-le-half-repair-3-referee.md).
- **Proved for every size, and confirmed by the referee:** the `layervine` structure, i.e. spine, pendants and at most 3
  ladders. Each vine's pieces form a cactus with at most one triangle. Checked independently on all shapes with at
  most 41 atoms (3060 labelled cases).
- **Corrected statements written out in full:** Lemma 1.14(c′) and Cor 1.16′ (the sources keep the adjoint bond:
  TARGET L2140, DH23 L1775).
- **Referee verdict:** the γ-dependent vine family (`IsTVine` for γ ≤ 1/2) was ready for the owner's approval, which
  was given on 2026-11-05 (D11; text on `docs/review/GAMMA-LE-HALF-VINES.md`; the Lean text is a working note, not
  included). Remaining caveats:
  - the base enumerations (classification up to 13 atoms; 57 base pairs up to symmetry) are Python checks, not yet
    kernel certificates;
  - confluence (note 2 Lemma 1.4) is still a Lean obligation.
- **DH23 `subsetvc` (L2128) is incomplete.** Its list of sub-objects omits two blocks:
  - the block VC:I+I, which occurs in drawn vine (IV) (second referee);
  - the block vine (V), which occurs in drawn vine (VII) on atoms {4,…,8} (third referee).
  The corrected list is Cor 1.16′.

In the Lean development, the γ-sensitive input `FinalCountGate` (TARGET finalcount1) is a separate hypothesis of
`layergarden_of_spine`. Its restriction to 1/2 < γ, `FinalCountGateHalf`, is proved (`finalCount_half`).

---

## E2 — further errata and gaps (E2a–E2g), and minor items

This section collects findings that were recorded in the project ledger but not yet written up: seven full entries,
then a table of minor items.

## E2a — DH21 Lemma 5.8 and the proof of Lemma 7.3: the sign of the χ_∞ term; DH21 Prop 7.5 and TARGET (regref1-3) inherit it

**Status:** CONFIRMED. **Class:** ERROR. **Main theorem:** no effect on the summed asymptotics; the per-couple
statement (regref1-1) as printed is false, and its corrected form is what the Lean statements use.
- Found while auditing the Lean form of DH21's operator lemmas (ledger F61); traced independently by a second worker
  and checked by hand by the project's orchestrator.
- Evidence: [`docs/research/dh21-lemma73-sign-trace.md`](research/dh21-lemma73-sign-trace.md). Lean: the composition
  kernel identity `iker_comp_decompP` and the decomposition `lemma510` (`WaveTurbulence/Foundations/ClassJR/`).

**Source text.** DH21 Lemma 5.8 (L1070):

> I_{εα₁} I_{μ₁−εα₁} = (χ_∞(α₁)/(επiα₁)) 𝒥_{α[ ],μ₁} + 𝒥_{α₁,μ₁} + ℛ_{α₁,μ₁}.

Its proof defines the second term with a minus sign (L1076), "II := −(χ_∞(εα₁)/(επiα₁)) J_{0;0,μ₁}", and then states
(L1079) "likewise II = (χ_∞(α₁)/(επiα₁))·𝒥_{α[ ],μ₁}". The proof of Lemma 7.3 (L1737) uses the same "+" sign:

> I_{ε_jα_j} I_{μ_j−ε_jα_j} = (χ_∞(α_j)/(ε_jπiα_j)) I_{μ_j} + 𝒥_{α_j,μ_j} + ℛ_{α_j,μ_j}.

**What is wrong.** With I_β f(t) = ∫₀ᵗ e^{πiβs} f(s) ds, the composition has kernel

> e^{πiμs} (e^{πiεα(t−s)} − 1)/(πiεα) = e^{πiμs}e^{πiεα(t−s)}/(πiεα) − (1/(επiα)) e^{πiμs},

so its χ_∞ part contains **−(χ_∞(α)/(επiα)) I_μ**, as term II of the proof of Lemma 5.8 says. Carried through:
- the correct (regchaincalref) of Lemma 7.3 has an extra factor (−1)^{|Z|};
- DH21 Prop 7.5 (L1767), "𝒥B̃_{𝒬,Z} … is independent of Z", is false: 𝒥B̃_{𝒬,Z} = (−1)^{|Z|} 𝒥B̃_𝒬;
- the weight in DH21 (reducedom) (L1810) and in TARGET (regref1-3) (L1154), ∏_{𝔫∈Z} 1/(ζ_𝔫πi), should be
  ∏_{𝔫∈Z} (−1)/(ζ_𝔫πi).

The resonance convention does not compensate: the same Ω_𝔫 = 2⟨x_𝔫, y_𝔫⟩ appears in (newsum1) and in α_𝔫.

**What survives.** |Z| is constant on each equivalence class, so DH21 Props 7.8–7.10, TARGET (regref2-3) and
(regref1-5), and both main theorems are unaffected (the Z ≠ ∅ classes cancel either way). What fails as printed is the
per-couple bound (regref1-1) for R*_𝒬 = K*_𝒬 − (K*_𝒬)_app, for dominant 𝒬 with odd-|Z| terms.

**In the Lean statements.** The frozen definitions `RegCpl.app` and `RegChain.app` use `specialWeight`
= ∏_{𝔫∈Z}(−ζ_𝔫πi)⁻¹ (see Deviations, C).

---

## E2b — DH23 Lemma `ylem1` (L1937–L1948) misses several molecules

**Status:** CANDIDATE. **Class:** ERROR. **Main theorem:** no direct effect; DH23 L1885 (E1) rests on this lemma.
- Found while formalizing DH23 Prop 10.4 (ledger F69): a kernel-checked 5-atom counterexample (working note, not
  included).
- An independent investigation confirmed the counterexample and found further omissions by exhaustive enumeration:
  [`docs/research/ylem1-investigation.md`](research/ylem1-investigation.md). The ledger records the finding as a DH23
  erratum; no separate refute-first verdict is recorded, so the status is left as CANDIDATE.

**Source text.** DH23 L1937:

> Suppose 𝕄 is 4-regular with at most two triple bonds and 𝕄′ is formed from 𝕄 by (Y) sequences. If 𝕄′ is either a
> quadruple bond or a triangle formed by 3 double bonds, then 𝕄 is formed by removing the two joints of a vine and
> adding one new bond between the pair of atoms connected to each joint.

The proof (L1939) begins: "The proof is an enumeration of all possibilities. Clearly going from 𝕄 to 𝕄′ involves at
most two (Y) sequences with last operation (Y2)."

**What is wrong.**
- **A counterexample.** The 5-atom molecule with bonds 1→0, 1→2, 2→1, 2→0, 0→2, 0→3, 3→4, 3→4, 4→3, 4→1 is 4-regular,
  loop-free and has one triple bundle. One (Y2) step at atoms 3, 4 gives the triangle of double bonds. The conclusion
  would make it a vine minus its two joints, that is, a vine with 7 atoms; no vine (I)–(VIII) has 7 atoms (vine (I)
  has 2, vine (II) an even number ≥ 6, the others ≥ 9).
- **The full list of omissions** (exhaustive inverse enumeration, against all vine closures):
  - Q and T themselves, reached by zero (Y) sequences;
  - the 5-atom T₁ above, reached by one sequence of length 1;
  - two infinite families with two triple bonds, both from the "(VI)" bullet (L1946); the smallest has 7 atoms, with
    two triple bonds in series.
- **Where the proof slips.** It never treats zero or one (Y) sequence, and the claims at L1941 and L1946 are too
  strong. No reading of the figures saves the lemma: the most generous one, which allows a length-0 dashed pair
  between two double bonds, recovers Q, T₁ and one family, but still misses T and the other family.
- **Checks:** brute force to 15 atoms, parametrised families to 27 atoms, 288 configurations, no mismatch with the
  corrected list.

**Repair.** A corrected lemma `ylem1′` lists the exceptions explicitly. DH23 Prop 10.4(2) then takes the hypothesis
"not Y-exceptional" (some complete (Y)-reduction of 𝕄 ends in Q or T), and its proof (L1963–L1977) no longer uses
`ylem1` (Lean: `WaveTurbulence.MoleProp4.YReachesQT`). DH23 Prop 10.4(1) (L1959) has the same length-1 omission; with
vine (II) read to include m = 1 (E3), that omission is exactly the m = 1 vine, and `ylem1`'s quadruple-bond branch
becomes "vine (II), m ≥ 1".

---

## E2c — DH23 proof of Prop 10.2, "Conclusion" (L1912): "the total number of operations is ≤ C(r₁+r₂)" is false

**Status:** CANDIDATE. **Class:** ERROR (in a proof). **Main theorem:** none (a short repair).
- Found while formalizing the algorithm of DH23 §10 and Appendix B (ruling R4).
- Evidence: [`docs/research/dh23-prop102-proof-errata.md`](research/dh23-prop102-proof-errata.md).

**Source text.** DH23 L1911:

> Now we see that the number of steps different from (3D3-1N) is at most C(r₁+r₂). […] As for the sequences of
> (3D3-1N) or (3D3-2G) occurring in (3-b), each sequence corresponds to a ladder, and each chain can be as long as Cn,
> but the number of chains must be at most C(r₁+r₂) for the same reason.

DH23 L1912:

> here note that, for operation (3D3-1N), which is the only operation whose number is not controlled by C(r₁+r₂), we
> do not have any logarithmic loss […]. In the same way, if E=2V−2>0, then the total number of operations is
> ≤ C(r₁+r₂) as shown above, and this total number must be positive if E>0, so we know r₁+r₂ ≥ 1 and hence
> 𝔄 ≲ L^{−η/3}.

**What is wrong.** The total number of operations includes the (3D3-1N) steps, which L1911 and the first sentence of
L1912 say are not controlled by C(r₁+r₂). Long double-rung ladders have arbitrarily many such steps. So the bound on the
total, and with it the deduction of r₁ + r₂ ≥ 1, does not follow as written.

**Repair.** The conclusion needs only r₁ + r₂ ≥ 1 when E = 2V − 2 > 0. A nonempty terminating run contains a step
other than a normal (3D3-1N): such a step leaves degree-3 atoms on the boundary, so it cannot be the last step. Hence
the number of non-(3D3-1N) steps is positive, and these are counted by C(r₁+r₂). No new premise is needed.

---

## E2d — TARGET `vineest` Step 2, case (C-ii) (L1817): "the same results will hold" fails for the same-direction core of vines (V)–(VIII)

**Status:** CANDIDATE. **Class:** ERROR. **Main theorem:** none, provided `sumint` is used in a signed form (its proof
goes through with the sign). That signed form is now proved in Lean on main, as a special case of a signed, weighted
`sumint` (`WaveTurbulence.SumintPar.signed_of_sumintPar`, from `SumintPar.sumint`; on main after commit `5c6d256c`).
- Found while formalizing the vine parametrization (ledger F79). The computation is kernel-checked in a working note
  (not included), including a determinant obstruction; an independent audit of the signed reading is pending.
- Evidence: [`docs/research/target-vine-core-sign-check.md`](research/target-vine-core-sign-check.md).

**Source text.** TARGET L1814, case (C-i) (vine (III)): "Then we have ω₁ = 2u₁·u₂, while ω₂ equals 2u₁·u₃ in the first
case, and equals 2u₃·(u₁+u₂−u₃) in the second case." TARGET L1817, case (C-ii):

> For Vines (V)–(VIII), the argument is again similar, and in fact much easier. […] Then we argue as above, with
> (u₁,u₂,u₃) = (a−e, b−e, a−c) if bonds decorated by a and b have the same direction, and (u₁,u₂,u₃) = (e−g_*, b−g_*,
> d−g_*) if they have opposite directions, then the same results will hold.

**What is wrong.** In the same-direction core of Figure (D), with g_* = 0 and conservation e = a + b, d = a + b − c, the
three resonance factors of the triangle are

> 2ab, −2(c−a)(c−b), 2c(c−a−b).

Each is a quadratic form of rank 2, and they sum to 0. The printed pair 2⟨u₁,u₂⟩, 2⟨u₃, u₁+u₂−u₃⟩ has a third form
(minus their sum) of rank 3. No real linear change of variables, and no change of sign of individual factors, maps the
actual triple to the printed one (the symmetric coefficient determinant of the printed third form is −4, while all
actual ones vanish). In suitable coordinates the actual pair is 2⟨u₁,u₂⟩ and −2⟨u₃, u₁+u₂−u₃⟩: the relative sign is
reversed. A scalar check: at a = b = 1, c = g_* = 0 the actual −Γ(w₁) is −2, while the displayed 2(a−e)(b−e) is +2.
For the linear alternative the printed forms have a common factor that the actual triple lacks.

**Consequence.** TARGET Prop `sumint` (L1595–L1640), as printed, takes two positive core forms. For vines (V)–(VIII)
its input has a signed nonlinear core. The proof of `sumint` does not use the sign, so a signed version holds by the
same proof. The frozen `sumint` is faithful to the printed statement; the proof chain uses the signed version
(`SumintSigned`, `WaveTurbulence/Foundations/VineEst/VineEstS2/SumintSigned.lean`).

---

## E2e — Regular-couple asymptotics are used beyond the order range in which they are stated

**Status:** CANDIDATE. **Class:** EXPOSITION. **Main theorem:** repaired: the number-theoretic input is extended in Lean
to every fixed power of log L.
- Ledger: F33, F15, and the addendum to F54.

**Source text.**
- DH23 Prop 6.4 (`approxnt`), L1002: "Assume n ≤ (log L)³." DH23 applies it at L1168: "if 𝒬 be a regular couple of
  order 2n where n ≤ N³", with N = ⌊(log L)⁴⌋ (L480), that is, for n up to about (log L)¹².
- TARGET L951 fixes "a layered regular couple 𝒬 and a layered regular tree 𝒯 of order 2n … where n ≤ N_{p+1}⁴", with
  N_{p+1}⁴ = (log L)^{C(𝔇)}. Its regular-couple asymptotics (L1145–L1232) cite DH21 Props 6.7, 6.10, 7.5, 7.11 and
  DH23 Prop 6.1 (L1171), which are proved for n ≤ N³.
- DH21-2 Prop 3.8 (L587) states the asymptotics for n ≤ (log L)⁵⁰ and its proof (L602) reads: "This follows from
  Propositions 6.7 and 6.10 of [DH21]. Whether the upper bound for n is (log L)⁶ or (log L)⁵⁰ does not affect the
  proof (again, as long as n ≪ L^{δ²})."

**What is missing.** The stated ranges are smaller than the ranges used. A crude bound absorbed by δⁿ is not available
for the excess orders (the trivial bound on K_𝒬 loses about L^γ per order), so the asymptotics must genuinely be
extended. The remark in DH21-2 indicates why the same proof should extend; it is not a proof.

**Repair.** DH23 Prop 6.4 holds for n ≤ (log L)^A for every fixed A, with constants depending on A
(`approxnt_conclusion1`, `approxnt_conclusion2` in `WaveTurbulence/Foundations/ApproxNT/`). The frozen
`regularAsymptotics` carries the range n ≤ N_{p+1}⁴ (Deviations, C).

---

## E2f — TARGET proof of Theorem 1.1: three steps are asserted without proof

**Status:** CANDIDATE. **Class:** EXPOSITION. **Main theorem:** none; each step became an explicit statement of the
formalization.
- Ledger: F7 and F27, F8, F10. Noted while mapping the paper.

**(a) Intermediate times.** TARGET L821:

> In general, suppose t′ ∈ [p,p+1]. We use Proposition [propansatz] for p, then, assuming 𝔉_{p+1}, we repeat the
> arguments applied in the inductive step […], but apply them to rescaled time t′ instead of p+1. It is clear from the
> proof that none of the ingredients is affected by this change, and the result follows in the same way.

The theorem's supremum over t ∈ [0,T] needs Prop `layergarden`, the WKE Taylor expansion and the whole inductive step
at every t′ ∈ (p, p+1], uniformly. Prop `layergarden` is stated at time p+1 (L761) but used at every t ∈ [p, p+1]
(L821, L2309). The frozen statements carry this time parameter (Deviations, C).

**(b) Smooth solutions.** Theorem 1.1 (L316) asserts that (NLS) "has a smooth solution", a notion not defined; the
proof produces a solution of the Fourier-side system (akeqn) with decay ⟨k⟩^{−50d}. Passing to a C^∞ solution of (NLS)
needs the inverse gauge transform, persistence of regularity, uniqueness, and measurability of the solvability event.
This is standard but not written (frozen statement `nlsAkBridge`).

**(c) The Taylor expansion of (WKE).** TARGET L756–L758: "It is easy to see that
sup_{t∈[p,p+1]} ‖𝒰_n(t,·)‖_{𝔖^{4Λ_{p+1},4Λ_{p+1}}} ≤ C₂·(C₁δ)ⁿ for any n ≥ 0." A proof needs a tame estimate for the
collision operator in the 𝔖^{4Λ,4Λ} norms whose base C₁ does not depend on Λ (C₁ is chosen before δ and 𝔇).
Appendix C works in L²-based norms only (frozen statement `wkeTaylor`).

We claim no counterexample and no difficulty beyond careful standard analysis for (a)–(c).

---

## E2g — GIT20 Remark 2.6 (L592–L594), used by TARGET Prop 3.2: the d-dimensional L²_s theory is asserted without proof

This entry concerns GIT20 (Germain, Ionescu and Tran), not a paper of Deng and Hani; it is listed because TARGET relies
on it.

**Status:** CANDIDATE. **Class:** GAP (in GIT20, as used by TARGET). **Main theorem:** none. Theorem 1.1 does not use
the blow-up criterion of Prop 3.2; the estimate is proved for all d ≥ 3 in a research note.
- Ledger: F18, F32. The failing step was located during the formalization of TARGET Appendix C.
- Research note with a proof for all d ≥ 3: [`docs/research/git20-general-d.md`](research/git20-general-d.md).
  Independent audit (finds the proof correct): `docs/campaign/orch/audits/GIT20-general-d.md`.

**Source text.** GIT20, `Kin8.tex` L593 (Remark 2.6):

> We are working in dimension d=3 mostly for the sake of concreteness. Similar theorems hold in any dimension d≥2, with
> the corresponding ranges of exponents s>d−1 for the L^∞_s local well-posedness theory, and s>(d−2)/2 for the L²_s
> local well-posedness theory.

TARGET L2515: "It is proved in [GIT20], see Lemmas 4.1–4.3 of [GIT20] (also Remark 2.6 of [GIT20]), that each 𝒦_j
satisfies the trilinear estimate" (schappend8) in Z_s, which TARGET uses for all d ≥ 3 and s > d/2 − 1 to obtain the
blow-up criterion of Prop 3.2 (L598–L601).

**What is missing.** GIT20 proves the trilinear estimates only for d = 3. For d ≥ 4 the d = 3 argument does not
transfer at one step: in GIT20 Lemma 4.2, before inequality (bil7), a radial Cauchy–Schwarz step leads to
sup_p ∫₀^∞ ⟨rθ+p⟩^{−2s} r^{d−3} dr, which grows like R^{d−3} at p = −Rθ when d ≥ 4. Lemma 4.1 would need a
d-dimensional dispersive bound that is not proved.

**Repair (on paper, audited).** The research note proves (schappend8) for every d ≥ 3, s > d/2 − 1 (its Theorem 7:
polar coordinates, one linear change of variables, Hölder, a weighted Schur step that moves the radial weight onto the
integrated variable, and a symmetry of the resonant measure). GIT20's (bil7) itself is true in all d ≥ 3; only the
preceding step must be replaced. The blow-up criterion then follows through TARGET Appendix C. The note also shows that
for d = 2 the individual loss-operator bound fails for every s (its §8.3); it does not settle the full d = 2 statement,
which Deng–Hani do not use.

---

## E2 minor items

Typo-level slips, local imprecisions and reading choices. All are CANDIDATE and harmless in context; none affects a
main theorem. "Ledger" is the entry in `docs/FINDINGS.md` or the evidence file.

| # | Source, lines | Printed | Correction or comment | Kind | Ledger / evidence |
|---|---|---|---|---|---|
| m1 | TARGET L314, L818 | probability ≥ 1 − e^{−(log L)^{40d}} in the theorem; (log L)^{20d} in the proof | Prop `propansatz` (1) gives 1 − e^{−N_𝔇} with N_𝔇 = R_𝔇^{40d}, which implies the stated bound | typo | F1 |
| m2 | TARGET L818–L819 | "𝔉 ⊃ 𝔉_p"; "≤ 2Σφ_in·P(𝔉∖𝔉_p)^{1/2} ≤ C₀L^d·P(𝔉_p^c)" | 𝔉 ⊃ 𝔉_p is false for p < 𝔇 (𝔉_p gives a solution only up to rescaled time p); argue with 𝔉_𝔇. The square root is dropped in the last step. Easy fixes. | slip | F6 |
| m3 | TARGET L688 | constant hierarchy C₀ ≪ η⁻¹ ≪ C₁ ≪ δ⁻¹ ≪ C₂ | the order used is C₀, η, ℭ, C₁, ν, δ (with 𝔇 = τ_*/δ an integer), C₂, L, with δ^ν ≪ 1; ν is not displayed | exposition | F5 |
| m4 | TARGET L623 | "Gevrey class 2 (i.e. the m-th order derivatives are bounded by (2m)!)" | impossible literally for a cutoff equal to 1 on [−1/2,1/2] and 0 off (−1,1): at m = 1, \|χ₀′\| ≤ 2 forces slope −2 on all of (1/2,1), contradicting smoothness at 1/2. Read as \|χ₀^{(m)}\| ≤ C·A^m·(2m)! | wording | F41 |
| m5 | TARGET L712 (defjt); also L2264 (jtflower) | leaf factor a_{k_ℓ}(p) | a_{k_ℓ}(p)^{ζ_ℓ} (conjugate on negative leaves), as in DH23 and as shown at TARGET L737 | typo | F9; `docs/research/flowerest1/o102-RESOLUTION.md` §2.1 (L2264) |
| m6 | TARGET L879–L881 | {x_𝔫′, y_𝔫′} = {ζ₁x_𝔫, ζ₂y_𝔫}, "See Proposition 4.3 of [DH21]" | DH21 Prop 4.3 states only ζ_𝔫′Ω_𝔫′ = −ζ_𝔫Ω_𝔫; the uniqueness step of DH21 Prop 4.14 ("case-by-case") is not written | omitted argument | F16 |
| m7 | TARGET L1168 (regref1-5) | Σ_{n(𝒬)=2n} K*_𝒬(t,t,k) = 𝒰_n(t,k) | should be Σ (K*_𝒬)_app(t,t,k), as in DH23 Prop 6.2 | typo | F11 |
| m8 | TARGET L957 | "the strategy of Section 7 of [DH23]" | Section 6 (the lemmas used are DH23 Lemmas 6.5, 6.6) | typo | F11 |
| m9 | TARGET L1024–L1025 | per-link factor ε_𝔫 ∈ {1, 0, −1} | the two nodes of a link carry the same ε, so the per-link factor is ε_𝔫² ∈ {1, 0, 1}; estimates unaffected | slip | F62 |
| m10 | TARGET L1101, L1107 | "(K*_𝒬)_app can be written as the sum of at most 2ⁿ terms" | 2^{2n+1} − 1 terms; still ≤ C₁ⁿ | slip | F80 |
| m11 | TARGET L1304 | "If 𝒢 is an irreducible garden of width 2R and order n, then 𝕄 has n atoms and 2n−R bonds" | needs "nontrivial", as in the couple sentence: two paired trivial trees give n = E = 0, against E = 2n − R at R = 1 | missing hypothesis | F58 |
| m12 | TARGET L1319 | the correspondence "gives a bijection between (k₁,…,k₂R)-decorations of 𝒢 and … of 𝕄(𝒢)" | fails when trivial roots are paired directly: four trivial trees with signs (+,−,+,−) and root values (0,1,1,0) satisfy conservation but admit no garden decoration, while the empty molecule admits one. Correct under root-pair compatibility (directly paired roots carry equal values), the indicator the garden sums carry. Lean counterexample in a working note. | missing hypothesis | F52 |
| m13 | TARGET L1330 (Def `defblock`); L1337–L1340 (Lemma `disjointlem` = DH23 Lemma 4.11) | the concatenation of two blocks sharing one joint "is either a block or a hyper-block" | false for blocks defined by degrees only, in TARGET's molecules (which allow self-loops, L1295): loops at atoms 0, 2, 4 and opposite double bonds 1–2, 3–4; A = {0,1,2}, B = {0,3,4} are blocks meeting the premises (i)–(iii) of `disjointlem`, but A ∪ B has three atoms of degree 2. Fix: require blocks to be connected. DH23 forbids self-loops (L633), so this example does not apply to DH23 as written. Lean counterexample in a working note. | missing hypothesis | F57; `docs/campaign/orch/audits/MOLE-prefreeze.md` |
| m14 | TARGET L1384 | "We require each ladder to have m+1 ≥ 2 double bonds" | DH23 L790 sets length = (number of double bonds) − 1 with no lower bound; with the figures' insertion rule TARGET's literal vine family misses every vine in which a dashed pair carries exactly one extra rung. Reading adopted: DH23's family | reading | F37 |
| m15 | TARGET L1431, L1481 | "it is easy to see that there are exactly two options to insert 𝔲₂" | needs a case table; Prop `lftwistprop` (L1481) checks only (II-a)→(II-b); that congruence is an equivalence relation is asserted. The unit twist is one uniform operation in all six core cases (ledger F38) | omitted argument | F20, F38 |
| m16 | TARGET L1519 | "(sumofexp0) follows from Proposition [layerlad], because 𝕍 consists of at most three ladders" | applying Prop `layerlad` to three ladders gives up to C₂^{g+3}, not C₂^{g+1}; harmless since C₂ may change | slip | `docs/research/layervine-count-handoff.md` |
| m17 | TARGET L1523 | "all the groups other than 𝔾_i form exactly the shape which is Vine (V) minus two joints" | false for vine (VII); the argument survives | slip | F28 |
| m18 | TARGET L1601 (sumintI1), L1831 (tildeK2) | phases e^{πiδL^{2γ}(t−s)⟨x,y⟩}, e^{πiδL^{2γ}(t−t′)⟨r,ζ⟩}, … | since ζ_𝔫Ω_𝔫 = 2x·y and 2r·ζ (L1792), each exponent lacks a factor 2. Equivalent to replacing δ by 2δ; the Lean chain applies `sumint` at 2δ (`sumintSignedDoubled_of_sumintSigned`) | typo | `docs/research/vineest-early-sessions-handoff.md` |
| m19 | TARGET L1615, L1687 | "i ∈ A"; "\|t_j^i − q_j^i\| ≤ 2L^{−β} + \|t_1^i − s_1^i\|" | A should be Nor; an index slip at L1687 (fixed in the frozen `sumint`) | typo | F23 |
| m20 | TARGET L1541–L1542 | (lemlin3) | omits the factor L^d of the Poisson identity at L1541, needed to recover (lemlin2) | typo | F47 |
| m21 | TARGET L1567 | "since \|t′\| ≥ L⁻¹, we must have a ≠ 0" | at t′ = L⁻¹, a = 0 and q = 1 satisfy the Dirichlet bound; a null endpoint | slip | F45 |
| m22 | TARGET L1807, L1823 | "Ω_{𝔲₂} = 2r·x₀"; variables (w₁ⁱ, w₂ⁱ, w₃ⁱ) | ζΩ, not Ω; u₁ⁱ, u₂ⁱ, u₃ⁱ, as defined at L1814 | typo | F28 |
| m23 | TARGET L1814, L1817 | "The argument for Vine (IV) is similar"; "the argument is again similar" | the parametrizations of vines (IV)–(VIII) are not written (see also E2d) | omitted argument | F22 |
| m24 | TARGET L2009 (used in (localize1), L2013) | "any atoms v and w connected by a double bond, we have Γ_v+Γ_w = 2r_j·y_w" | holds only at interior rungs; the end atoms of a ladder carry extra bonds. Pair only interior rungs and put the end rungs in 𝕐, at a cost absorbed by the slack | slip | `docs/research/ladderl1-handoff.md` |
| m25 | TARGET L2034, L2037 | 𝔇^{z_j}/(z_j−d)! | the monotone-volume bound gives (2𝔇)^K/K! with K ≥ z_j − d − 1; the final inequality at L2037 is unaffected up to constants | slip | `docs/research/ladderl1-handoff.md` |
| m26 | TARGET L2082 | L^{−(γ₁−√δ)g′} | √η, as elsewhere | typo | F28 |
| m27 | TARGET L2197 | "Lemma 10.2 of [DH23]" | Proposition 10.2 (`moleprop2`); see also m37 | typo | F24 |
| m28 | TARGET L2264–L2265 (jtflower, kqflower); DH23 L1995–L1996 | prefactor (δ/(2L^{d−1}))ⁿ | **moved to E41** (upgraded to ERROR, CONFIRMED: the discrepancy L^{(1−γ)n} is not absorbable) | — | F25 |
| m29 | TARGET L2345 (Lemma `propertycm`) | "there is no proper subset A ⊂ {1,…,r} such that ∪_{i∈A}S_i equals the union of some of the sets B ∈ 𝒫" | literally A = ∅ always qualifies; read "no nonempty proper subset". The S_i must be nonempty when the expectation is taken over an event (mass ≠ 1); all uses have nonempty S_i | wording | F30 |
| m30 | TARGET L2386–L2388 (Lemma `timeintlem2`) | "for complex valued F we have ‖𝒰_χF‖_{𝔛^{1/4,0,0}} ≲₀ ‖∂_{t₁}∂_{s₁}F‖_{L^∞_kL¹}" | false for F ≡ 1 (the right side vanishes, 𝒰_χF does not). The proof assumes F compactly supported (L2391), the class used at the call site | missing hypothesis | F42 |
| m31 | TARGET L2370, L2391–L2393, L2417 | Appendix A proofs | (i) the convolution step at L2370 suppresses a logarithm; (ii) the decay (weakdecay), "a simple calculation yields", is false before localization; (iii) "bounded in Schwartz class … uniformly in ξ and k" is false globally (at Γ₁(k) = ξ the tail integral of χ² is nonzero). Repaired without changing the lemma statements | slips in proofs | F49 |
| m32 | TARGET L2425 (Lemma `treelemma` (1)) | "k_{𝔫_{j′}} − k_{𝔫_j} is an algebraic sum …" | the signs should be ±; for j = 1 there is no earlier node (see also E15) | slip | F63 |
| m33 | TARGET L2472 (atomcountbd) | 𝔈₂ ≲₁ δ⁻¹min(L^d, L^{d+1−2γ}) | false at k = 0 with signs (+,−) and γ > 1/2: k₁ = k₂ gives about L^d solutions. DH23 Lemma A.3(1) has \|k₁−k₂\| ∼ R ≥ L⁻¹, i.e. k ≠ 0. Also "if \|r\| ≥ L^{−γ+η}": r is undefined, read as \|k\|. The frozen `atomCountLemma` carries k ≠ 0 | missing hypothesis | F43 (found independently by a statement auditor and by the referee of F75) |
| m34 | DH23 L1003, L1005 (Prop 6.4) | ⟨x_j, y_j⟩_β | carried over from DH21; DH23 has no β (square torus): ⟨·,·⟩ | typo | F54 |
| m35 | DH23 L1099 | phase p·ξ + y·ζ | p·ξ + q·ζ | typo | F45 |
| m36 | DH23 L1148, L1154–L1155 (Lemma 6.7) | μ⁻¹∫ψ(μΩ)…; error μ^{1−2η} | μ∫ψ(μΩ)… in (1) and (2); μ^{−(1−2η)} (cf. DH21 Lemma 6.5); the bound is bilinear in the Φ- and ψ-norms | typo | F50 |
| m37 | DH23 L1834 (Prop 10.2), L1900, L1913 | no size bound on 𝕄; "the w SG atoms" | the proof's log losses and its C^n choices need a size bound n ≤ (log L)^C, true in every application but not stated (Lean: `GraphOk`). SG-ness depends on the decoration, so "the w SG atoms" is handled by a union bound over at most (w+1)nʷ sets, which again uses the size bound. The step from L^{−η²ρ+C(w+1)} needs η ≤ 1/(4C₀), part of "η small" | missing hypothesis | R4; `docs/research/dh23-prop102-proof-errata.md` |
| m38 | DH23 L1904 (increv3) | ≤ −V₃₀ − Cr₂ | ≤ −V₃₀ + Cr₂ (the good operations contribute O(r₂) in absolute value); the subtraction at L1905 uses this sign | typo | `docs/research/dh23-prop102-proof-errata.md` |
| m39 | DH23 L1924 | "v₄ and v₅ are not bridges" | the bonds ℓ₄, ℓ₅ | typo | F67 |
| m40 | DH23 L2040 | #(A ∩ ℤ^d) | #(A ∩ ℤ²) | typo | F51 |
| m41 | DH23 L2077, L2082 | "(with ρ ∼ L^{2−2γ})"; min(L^{2/5}+Q^{7/11}, L^{1/5}+L^{8/5}Q⁻¹, L^{6/5}Q^{−1/3}) | Qρ ∼ L^{2−2γ}; the comma before the last term should be "+" (from the two-branch (disclattice)). The argument still works | typos | F31 |
| m42 | DH23 L2183, L2185 (Prop `brprop`); Appendix B | "Δν = 2" | the proof computes Δν = −2. Further slips in Appendix B: an opposite/same internal direction in the 3D3-3G proof, the sign of a quadratic defect in `basiccount` (4), a missing constant factor in the 3D3-3G raw count, and small typos. Statements otherwise unchanged | typos | F81; `docs/research/dh23-appendix-b-errata.md` |
| m43 | DH21 L380 (table) | 1 ≤ κ < L^{d/2} | κ < d/2 (since T_kin ∼ L^{2κ} ≪ L^d) | typo | F17 |
| m44 | DH21 Cor 4.9 (L776), proof | count of choices for double chains | miscounted; the corollary (at most C₀^m regular couples of order 2m) still holds | slip in a proof | F55; `docs/campaign/orch/audits/REG-STRUCT-prefreeze.md` |
| m45 | DH21 L798 (Def 4.11) | "if 𝒬 = × then 𝒩^{ch} contains the single root of + sign" | the trivial couple has no branching nodes | slip | F65 |
| m46 | DH21 L851 (proof of Cor 4.16) | Σ_{n₁+⋯+n_m≤n} C₀^{n₁}⋯C₀^{n_m} ≤ (2C₀)ⁿ | fails as written (for m = n = 8 with even scales there are 330 terms of total scale 8, against (2C₀)⁸ = 256·C₀⁸); the exponential count is true with larger constants | slip in a proof | F77 |
| m47 | DH21 L1788–L1790 (integralK) | weight e^{−πθα²} | e^{−πθ²α²}, consistent with the next line θ⁻¹e^{−π(t₁−s₁)²/(4θ²)} | typo | F70 |
| m48 | DH21-2 L830 | "this does affect the result" | "does not" | typo | F60 |
| m49 | TARGET L2295–L2296 | the loss "may come from taking the 𝔖^{40d,40d} norm of the input function 1_{k_𝔣=k′}"; "all the proofs … are translation invariant" | the 𝔖^{40d,40d} norm (T585) carries the weight ⟨k⟩^{40d}, so that norm of the cap indicator is at least ⟨k′⟩^{40d}, not uniformly bounded by a power of L for arbitrary k′. Treat k′ as a fixed external momentum and use the estimates that are uniform in localization centres (T958–T976, T1617, T1985), as the footnote to L2296 intends | slip | `docs/research/astra-flowerest1-report.md` §2 (3) |
| m50 | TARGET L2065 | "Λ_p = 40Λ_{p+1}" | Λ_p = 40dΛ_{p+1}, from the definition Λ_p := (40d)^{𝔇−p+1} at L611 | typo | flower scan (this pass) |
| m51 | TARGET L2297 | "if the realization of a vine 𝕍 in 𝒢_sk does not contain any of the 'special nodes'" | a special node can lie inside a regular object collapsed onto a skeleton node, so the test must count the regular objects attached at skeleton nodes; DH23 L2012 states this convention for the flower ("or a leaf in 𝒬_sk such that the regular couple in 𝒬 attached at it contains 𝔣"), TARGET does not. Reading adopted in the completion (o75 Def 2.3; checked in REFEREE-2 §3.1) | reading | `docs/research/flowerest1/o75-RESOLUTION.md` §2.2; assessment §2 (4) |

---

## E3 — DH23 Def 5.1, vine (II) (L1421): the one-double-bond case m = 1 must be included

**Status:** CANDIDATE. **Class:** MINOR (a definition read too narrowly from the figure; DH23's own text supports the
wider reading). **Main theorem:** none with the wider reading; under the literal reading the four statements of E1
fail for all γ < 2/3.
- Ledger: F72. Research check: [`docs/research/vine2-m1.txt`](research/vine2-m1.txt) (no Lean).

**Source text.** DH23 L1421 parametrizes vine (II): "we denote by v₁, v₂, v_{2j+1}, v_{2j+2} (1 ≤ j ≤ m) the 2m+2 atoms
forming the vine with joints at v₁, v₂, such that v_{2j+1} is connected by a double bond to v_{2j+2}". The figure of
Def 5.1 draws vine (II) with two double bonds. DH23 L1481 adds "noticing that m ≥ 1 for vines (II)", and Lemma
`sumintest1` (L1280) is stated "for m ≥ 1".

**What is at stake.** The 4-atom Q-block (vine (II) with one double bond) occurs as a case-(4) component in E1. If it
is not a vine, Q-bead necklaces break DH23 Prop 9.6, `kqmainest2`, TARGET `lgmolect` and (finalcount1) for all
γ < 2/3 (research note on E1, Lemma 4.6).

**The check.** Every vine-level argument of DH23 and TARGET goes through verbatim for m = 1:
- no step uses m ≥ 2; the cancellation is local to the rung next to the lower joint, which exists at m = 1;
- TARGET treats vine (I) as the m = 0 case of the same parametrization (L1800);
- mechanical checks: all 1152 placements of a Q-block fall into the scenarios (II-a)–(II-e); every unit twist is a
  valid involution; the Q-block is never a proper sub-object of a vine.

With m = 1 included, the Q-bead necklaces are repaired for all γ ∈ (0, 1), and E1 remains only for T-beads and
γ ≤ 1/2. Two small slips found in the same check: DH23 L1481 cites Lemma A.2(2) outside its range (A.2(1) closes the
step), and the δ-bookkeeping in (twoestbadv1) is off but absorbed by L^{−5η}.

---

## E4 — TARGET `vineest` Step 3, L1846: replacing ε by 1 "by trivial summation" fails for long vine chains

**Status:** CONFIRMED (as a gap in the argument). **Class:** GAP. **Main theorem:** repaired; the statement survives
with a corrected argument.
- Found while formalizing Step 3 of Prop `vineest`, and confirmed by a second formalization of degenerate vines
  (ledger F21).
- Evidence: [`docs/research/vineest-step3-epsilon-handoff.md`](research/vineest-step3-epsilon-handoff.md), §6. Lean:
  namespace `WaveTurbulence.DegenVine` (`WaveTurbulence/Foundations/Vine/DegenVine/`).

**Location.** TARGET L1846, in Step 3 of the proof of Prop `vineest`, just after (tildeK2). DH23 L1448 and
`extradegen` (DH23 L1979–L1989) make the same kind of claim: "treat the rest of the variables using the same arguments".

**Source text (TARGET L1846):**

> Here note that once we specify r = k_{u21} − k_{u22} = k_{u1} − k_{u11} ≠ 0, we may replace ε_x in (tildeK2) by 1,
> since if any ε factor is not 1, this would imply some restrictions on the relevant variables (such as x_j^i = 0 or
> y_j^i = 0, or u_1^i + u_2^i − u_3^i = 0 etc.), which allows us to sum over these variables trivially and gain an
> extra power L^{−0.1γ₀}.

**Why the stated argument fails.** Consider a vine chain with M vines, where some ε-factor equals 0 because one affine
constraint holds.
- Summing trivially (absolutely) over the remaining variables of the restricted subspace costs L^{(M−1)d}.
- The budget of (vineest2) for these variables is L^{M(d−γ)}.
- The trivial sum therefore exceeds the budget by L^{Mγ−d}, which grows once **M > d/γ**. For example, at d = 3 this
  is M ≥ 7 for γ = 1/2 and M ≥ 4 for γ = 0.9.
- Chains of this length do occur, since the vine-chain length M is up to order N_{p+1}⁴.
- The loss comes from summing absolutely: that gives up the oscillatory gain L^{−γ} per variable, which the `sumint`
  bound needs.

**The gap cannot be closed by quoting `sumint`.**
- The indicator 1[x_v = 0] is not an admissible `sumint` weight: its S^{30d,30d} norm is about L^{31d}.
- Deleting the restricted rung breaks the invertibility of T₁ and `Admissible` (ii)/(iii).

**Correct argument.**
1. Write ε = 1 − 1[k₂ = k₁] − 1[k₂ = k₃].
2. Each indicator of an affine constraint on the lattice ℤ_L^d is an average of characters (Fourier inversion on the
   finite group), so it is a mixture of linear input phases with total mass 1. Over n nodes, ε is a mixture of mass at
   most 3ⁿ (`exists_eps_mix`).
3. The `sumint` kernel bound is uniform in the linear input phases: `exists_source_static_power_bound` holds for all
   p, ν, r. The norm `XNorm00` is a supremum over the output. So the recombination step of the `sumint` proof
   applies, multiplied by the mixture mass.
4. Conclusion (`clockedBoundEps_of_restr`): the Step 3 bound holds with ε, at a cost of a factor 3^{|I|} ≤ C^M. That
   factor is absorbed into C₁.

In this repository `clockedBoundEps_of_restr` takes the mixture form of `sumint` as a hypothesis
(`SumintMixDoubledAt`); the unconditional proof of that hypothesis is a working note, not included.

No L^{−0.1γ₀} gain is proved, and none is needed for (vineest2).

**Suggested rewording of L1846.** "ε_x is a combination of at most 3ⁿ indicators of affine constraints. Each indicator
is an average of linear input phases, to which the proof of Proposition `sumint` applies verbatim, since its kernel
bound is uniform in the linear phases. So ε may be replaced by 1 at the cost of the constant 3ⁿ ≤ C^M."

**Effect on the formalization.** None on any frozen statement. The Step 3 endpoint is stated with ε, in the literal
form, and uses the corrected argument.

---

## E5 — TARGET (finalsbest1), L2075–L2079: "very easy with Proposition `ladderl1new`" does not follow from that proposition as stated

**Status:** CONFIRMED (as a gap in the argument). **Class:** EXPOSITION. **Main theorem:** repaired in Lean; the
estimate itself is true.
- Found while formalizing (finalsbest1).
- Evidence: [`docs/research/finalsbest1-ladder-coupling-handoff.md`](research/finalsbest1-ladder-coupling-handoff.md).
  Lean: `coarseSplicedGatePinned : CoarseSplicedGate`, and the intermediate bound `ladderL1Gate` described below.

**Location.** TARGET L2075–L2079. Estimate (finalsbest1) is
|K_{G_sb}| ≲₂ (C₁√δ)^{n_sb} L^{−η·g_sb + 80d(ρ_sb + q_sk)}.

**Source text (L2079):**

> The proof of (finalsbest1) is very easy with Proposition [ladderl1new], which we describe below.

**What is wrong.**
- Prop `ladderl1new` (redladder2, L1978–L1992) bounds a single ladder's local kernel. It holds with all outside times
  and boundary data fixed, over the time-ordered domain, uniformly in the outside times.
- Two ladders adjacent in the tree and lying in the same layer are coupled by the time-ordering indicator. So the
  integrand of K_{G_sb} does not factor over the maximal ladders.
- Hence a product of `ladderl1new` bounds, used as black boxes, does not bound K_{G_sb}. Fixing the outside times of
  one ladder fixes times inside the other's ordering constraint, and the uniform bound gives no way to integrate them
  out.

**Correct argument (proved in Lean).**
1. Use the intermediate quantity from inside the proof of `ladderl1new`: the integral over the unit time box, with the
   ordering dropped, of the modulus of the finite lattice sum (`kernel_core`).
2. Bound that quantity by the same right-hand side (`ladderL1Gate : WTPrefix LadderL1At`). It is multiplicative over
   disjoint ladders, since dropping the ordering decouples them.
3. Glue over disjoint, hinge-free maximal ladders (`splicedKernel_le_classes`), and count the classes.
4. Select the ladders combinatorially (`selection_claim`). This uses the pairwise disjointness of distinct maximal
   ladders.

**Effect on the formalization.** None on any frozen statement. The corresponding input of the `layergarden` assembly
is proved.

**The translated-box form (E5′).** The flower estimate needs the same kernel-core bound for every product of unit time
intervals, not only the layer box, because an upper resonance filter acts on a rung as a time translation (E44). The
Lean gate `ladderL1Gate` is stated for the layer box only. o83 Theorem K proves the translated form on paper (refereed;
[`docs/research/flowerest1/o83-RESOLUTION.md`](research/flowerest1/o83-RESOLUTION.md)); see also E40 for two
exposition gaps in the printed sketch of `ladderl1new` that the same theorem fills.

---

## E6 — TARGET L2189 ("easy to check … preserved"): the invariant fails under the blanket Operation 2 cut

**Status:** CANDIDATE. **Class:** MINOR. **Main theorem:** none.
- Found while formalizing the stage-2 cutting run; the computation is explicit.
- Evidence: [`docs/research/finalcount-stage2-handoff.md`](research/finalcount-stage2-handoff.md).

**Location.** TARGET L2189, in the proof of Prop `finalmol` (L2187–L2190): the invariant 4V − 2E − 2(V_α + V_β) is
"easy to check" to be preserved in each Operation 1–4. Operation 2, the triangle cut, is stated as a blanket cut at
L2142.

**Configuration.**
- Take a triangle (v₁, v₂, v₃) whose atom v₃ is a degree-2 β-atom created by an earlier cut.
- The blanket Operation 2 cuts all three triangle atoms. At v₃ this leaves v₃ intact and creates a fresh isolated
  β-atom of degree 0.
- Then ΔV = 0, ΔE = −3 and Δ(V_α + V_β) = −1 + 3 = +2.
- So Δ(4V − 2E − 2(V_α + V_β)) = 0 + 6 − 4 = **+2**, and an extra imperfect component appears.

**Repair.** DH23's own formulation (L1777, "If deg v_j ≥ 3, then we cut") avoids this. The Lean model follows DH23
and deletes the degree-0 remainder (the class `Cls.ghost`).

**Effect on the formalization.** None on any frozen statement.

---

## E7 — DH23 L1793–L1794 (Prop 9.4, triangle with ΔF = 1): the pair count assumes a nonzero fixed difference

**Status:** CANDIDATE. **Class:** EXPOSITION. **Main theorem:** none; the final bound is unaffected.
- Found while formalizing the triangle step; the construction is analytic and has not been checked in Lean.
- Evidence: [`docs/research/finalcount-prop94-handoff.md`](research/finalcount-prop94-handoff.md).

**Location.** DH23 L1793: "If ΔF = 1, then (triangle1) still holds for *some* j", followed by the count at L1794.

**Configuration.**
- The v₃ triple need not be SG; L1777 requires SG only for j ∈ {1, 2}.
- Take v₃ with k_{ℓ₁} = k_{ℓ₂} = k free in the unit ball.
- Then there are about L^d pairs. This exceeds the source's δ⁻¹L^{d+1−2γ} for γ > 1/2 and L large.
- For d ≥ 3 and R ≤ L^{−γ+η}, the final ΔF = 1 bound still holds, by exponent arithmetic alone.

The Lean proof assumes nonzero gaps at all three triangle atoms, a reading wider than the source's.

---

## E8 — DH23 L1876 (proof of Prop 9.6, case (1)): "only remove ε-atoms" is incomplete

**Status:** CANDIDATE. **Class:** EXPOSITION; the statement is not false. **Main theorem:** none.
- Found while formalizing Prop 9.6.
- Evidence: [`docs/research/finalcount-prop96-handoff.md`](research/finalcount-prop96-handoff.md).

**Location.** DH23 L1876: "we perform the same operations (a) and (b) as in the proof of Proposition [moleprop1]
above, but we only remove ε-atoms"; cases (2)–(3) follow at L1878–L1880.

**Problem.** The argument also needs degree-1 α- and β-atoms to be deleted at no cost. That is possible, since fixed
charges determine their bond, but the text does not say so.

**Effect on the formalization.** The Lean proof adds this free deletion.

---

## E9 — TARGET `finalmol` (L2185, L2189) fails as stated once tame-atom removals occur (Remark `remtame`, case (ii))

**Status:** CANDIDATE. **Class:** MINOR. **Main theorem:** none.
- Found while formalizing the stage-2 cutting run; the computation is explicit.
- Evidence: [`docs/research/finalcount-stage2-handoff.md`](research/finalcount-stage2-handoff.md), Session 4, which
  contains the exact configuration.

**Location.** TARGET L2185 (`finalmol`): the final molecule has "at most R imperfect components", and "no α- or
β-atom is ZG". Its proof at L2189 says the invariant 4V − 2E − 2(V_α + V_β) is preserved.

**What goes wrong.**
- **The invariant rises by 4.** A degree-4 ZG tame atom removed under Remark `remtame` case (ii) changes the invariant
  by **+4**: V − 1 and E − 4.
- **The imperfect-component bound fails.** With t such removals it becomes **R + 2t**, not R. TARGET's later remark
  `remtame2` (L2218) adds 2 imperfect components per removal, which is consistent with +4. So the source's own later
  bookkeeping contradicts L2185/L2189 as stated.
- **Degree invariant.** The "ε-atoms have degree ≥ 3" invariant fails for a neighbour joined to the removed atom by two
  bonds.
- **ZG α/β atoms.** `remtame` case (i) creates ZG α/β atoms, contradicting L2185's "no α- or β-atom is ZG".

**Assessment.** The final estimates survive, because `remtame2` accounts for the extra components. But `finalmol` as
stated is false in TARGET's setting with tame atoms.

**Effect on the formalization.** The counting chain models TARGET's setting with an explicit removal step and the
bound R + 2t. DH23's setting has no non-hinge ZG tame atoms (`DegenSG`), so `remtame` never fires there.

---

## E10 — DH23 L1815 (proof of Prop 9.5, vine components are LG): "the vine is not changed" although its joints are cut

**Status:** CANDIDATE. **Class:** EXPOSITION. **Main theorem:** none.
- Found while formalizing the stage-2 cutting run.
- Evidence: [`docs/research/finalcount-stage2-handoff.md`](research/finalcount-stage2-handoff.md).

**The problem.** The proof says a final vine component is the vine from stage 1, "not changed in the process". But its
joints are cut atoms. Identifying the component with an object of 𝕄₀ needs two arguments:
- **An identification argument.** The component's non-ε atoms are its two joints, and the cut halves map injectively
  to distinct ancestor atoms. The two joints cannot be the halves of one cut atom: the component would then be closed
  under adjacency, hence all of 𝕄_sub, which contradicts the two odd atoms.
- **The case of a hyper object.** When the joints' other halves are joined by a bond, the component is a hyper object
  (HV), not a VC.

The Lean proof adds both arguments.

---

## E11 — TARGET Remark `remtame` case (i) (L2152, L2218): "cut at v and proceed normally" / "modified trivially" is not trivial

**Status:** CANDIDATE overall; part (a) is CONFIRMED (ledger F48, independently checked:
`docs/campaign/orch/audits/F48-check.md`). **Class:** GAP. **Main theorem:** repaired in Lean; (finalcount1) is
unaffected.
- Research with mechanical checks: [`docs/research/remtame-case-i-notes.txt`](research/remtame-case-i-notes.txt). Part
  (a) is also written up in [`docs/research/erratum-remtame.md`](research/erratum-remtame.md). Ruling R27.

**Location.** TARGET L2152, case (i) applies "if d(v) < 4, or if some component contains exactly one atom adjacent to
v". The text says: "the values of k_ℓ for ℓ↔v must all be fixed in the given decoration, so we always have enough gain
whether the resulting α- or β-atoms have zero gap. We then cut at v and proceed normally." TARGET L2218 adds: "In case
(i) the proof is modified trivially."

**What goes wrong.**
- **(a) "Values fixed" is false in one configuration.** A component of M − v can meet v only through an
  opposite-direction double bond to a single atom u. Conservation then puts no constraint on the shared value (in an
  explicit prime garden the label varies over ≳ L choices).
  - This is harmless. In that configuration M − v has c ≤ 2 components, so Δχ ≤ −2 and case (ii)'s gain applies.
  - The correct split is "pinned, or c ≤ 2", i.e. "exactly one bond connecting the component to v". This is DH23
    §10.5(4)'s "bridge, or Δχ ≤ −2" and the bridge criterion of DH21 Lemmas 9.13–9.14.
- **(b) The pin does not survive the cut.** Where the values are pinned, they are pinned by the charges of the
  molecule before the cut. After the β-cut, the zero-gap half of v can lie in a component whose own charges do not pin
  them. TARGET's product over components (L2203) cannot use the pin.
- **(c) Prop 9.6 (`lgmolect`) is false for a component with an unpinned zero-gap β-atom.**
  - **Counterexample.** X = {a, b, c, v₁} with bonds c→a ×2, a→b, a→v₁, v₁→b, b→c ×2. It is perfect, with V_α = 0 and
    V_β = 1, and conservation forces gap(v₁) = 0.
  - A pigeonhole count gives 𝔄(X) ≥ c·C₁⁻⁴. But (finalcount) requires L^{−γ₀−3η²−η⁵ρ}.
  - So "cut and proceed normally" can feed Prop 9.6 a component it does not cover.

**Repair (used in Lean).** Erase v instead of cutting it, exactly as DH23 §10.5 does (L1985: "we shall not make any
cut at non-hinge degenerate atoms"). Then:
- the nonzero-gap property of β-atoms (N1) and the ι property (N2) hold as stated;
- the count of imperfect components becomes R + Σ(deg v_e − 2);
- an erasure-deviation lemma gives the gain: pinned, factor 1; unpinned, deg 4 and c ≤ 2.

---

## E12 — DH23 Prop 9.6 proof, case (1) (L1876): the odd-component argument is written for a degree-1 odd atom

**Status:** CANDIDATE. **Class:** EXPOSITION. **Main theorem:** none.
- Found while formalizing Prop 9.6.
- Evidence: [`docs/research/finalcount-prop96-handoff.md`](research/finalcount-prop96-handoff.md).

**Location.** DH23 L1876, case (1) of the proof of `lgmolect`.

**Configuration.**
- Take an odd component whose two odd atoms both have degree 3, with all other atoms of degree 2 or 4, and no α- or
  β-atom. So w = 0 and E = 2V − 1.
- Such components occur, because DH23 `subpro` (b) (L1734) has two degree-3 atoms that need not be cut.
- Here 𝔄 ≲ 1 (Prop 10.1) does not give (finalcount): its right side carries L^{−η⁵ρ₀}.

**Repair (used in Lean).** Use the first statement of Prop 10.2 (no triple bond and E = 2V − 1 give
𝔄 ≲ L^{−3γ₀/5}).

---

## E13 — TARGET L2101 (selection of 𝒞₂): a DV whose two vines are both SG

**Status:** CANDIDATE. **Class:** EXPOSITION. **Main theorem:** none.
- Found while formalizing the stage-2 cutting run.
- Evidence: [`docs/research/finalcount-stage2-handoff.md`](research/finalcount-stage2-handoff.md), Session 6.

**Quote.** "if both vines (V) forming this DV are SG, then we select only one of them, plus all the maximal SG
vine-like proper subsets of the other."

**The gap.** The text does not say what happens if the selected vine is contained in a larger SG object. For example,
U could be an HV whose added bond is the shared joint bond. The unselected vine could then survive as an SG vine
component, contrary to the claim that vine components are LG (TARGET `finalmol`, L2185; DH23 L1815).

**Reading used in Lean.** The DV rule is applied among the maximal objects (`UnselOK`): the partner of an unselected
vine is a VC member of 𝒞₂. No concrete counterexample is known.

---

## E14 — TARGET Prop `vineest` (L1742–L1752) and `sumint`: the time domain when a lower child is a leaf

**Status:** CANDIDATE. **Class:** EXPOSITION. **Main theorem:** none.
- Found while formalizing Prop `vineest`.

**The issue.** The domain 𝔅 (L1747) is "the intersection of the set {t_{u₁} > max(t_{u₂₁}, t_{u₂₂})} with the product of
three unit intervals". That is not the actual domain of the kernel when u₂₁ or u₂₂ is a leaf, because a leaf carries
no time variable of its own.

**Repair (used in Lean).** Evaluate at the lower end of the unit interval, then take an order-0 time trace
(`XNorm00Restr_trace`). This costs a constant depending only on η, which is absorbed into C₁.

---

## E15 — further exposition points (recorded for completeness)

**Status:** CANDIDATE. **Class:** EXPOSITION (two items are small slips). **Main theorem:** none.

- **TARGET L1959 (redvine → redvine2, L1962).** The text records "a loss of at most C₀ⁿ" for node centres, then omits it
  in (redvine2), whose prefactor is (C₁√δ)^{n−n_sb}. When n = n_sb the exponent is 0, so the loss cannot be absorbed
  there. The Lean interface carries C₁^{n_sb} explicitly (ruling R24).
- **TARGET L1846–L1847 (vineest Step 3, layer failure).** The time order t_{u4} < t_{u2} comes from layers, not from a
  parent–child relation. It holds up to a null set (ruling R20).
- **DH23 L790 (closed ladder cells).** The text does not say which of the two parametrizations of a closed cell
  defines its gap (ruling R26). This is harmless: DH23's Prop 10.4(2) proof (L1961–L1977) treats such a post under
  case (I).
- **DH23 L1803 (Prop 9.4, κ = 50).** The text does not say whether the ι ball is fixed. For a "sibling" hit (the first
  cut of the same triangle) it is centred at a variable. The relative-ball count still gives the same bound (checked
  in the formalization).
- **DH23 L1862 (operc).** "𝔇 ≲ 1 + δ⁻¹R⁻¹L^{−γ}" is really L^{γ−1} + δ⁻¹R⁻¹L^{−γ}. This is an over-estimate, not an
  error.
- **TARGET L2425 (`treelemma` (1)).** "for each j there exists j′ < j" fails for j = 1. This is a trivial slip in a part
  that is not used (see also minor item m32).
- **TARGET Operation 3, after a tame-atom erasure.** A neighbour of the erased atom can become an SG ε-atom of degree 2,
  which Operation 3 (degree ≥ 3) never cuts. The text is silent on this. It was tracked as an open item of the
  formalization; the separate bound for damaged components in E16's repair addresses it.
- **TARGET Operations 2/4, ι property ("dead hit").** If both halves of the earlier cut that gives κ_v = 50 are later
  deleted by triangle operations, the ι ball centre is no longer a parameter of the current molecule. The Lean step
  lemmas require the hitting cut to be carried by a present atom (see E21).

---

## E16 — TARGET L2152: "a ZG v₃ in Operation 2 must be tame by `subpro` (3)" is false when v₃ is a hinge atom

**Status:** CANDIDATE (written by the finder and re-derived by an independent refute-first referee; ruling R29).
**Class:** ERROR. **Main theorem:** repaired in Lean; (finalcount1) holds with TARGET's exponents for 1/2 < γ < 1.
- Research: [`docs/research/remtame-hinge-notes.txt`](research/remtame-hinge-notes.txt) §3.2.
- Referee scripts and outputs: [`docs/research/remtame-hinge-referee/`](research/remtame-hinge-referee/)
  (`ref_hinge.py`, `ref_cluster.py`).

**Location.** TARGET Remark `remtame`, L2152: "We will also assume that no atom v₃ in Operation 2 … is ZG; in fact, if
any such atom v is ZG, then it must be tame by Proposition subpro (3)".

**Counterexample.** Take a couple of order 6, with its skeleton molecule M(Q_sk) as follows:
- 6 atoms and 11 bonds;
- degrees (3, 3, 4, 4, 4, 4);
- no loop and no triple bond;
- prime, with no mini couple, mini tree or sibling pair.

**Why it is a counterexample.**
- **The vine.** The only block is {u1, u2}. It is a (CL) vine (I-a), non-root (joint degree sum 8 > 6), and SG under
  the decoration, so stage 1 merges it into a hinge h.
- **The decoration.** Take decorations with D = E. Then M(Q_sk) has no zero gap, so no atom is degenerate and h is not
  tame. The referee found this in 300 of 300 random decorations.
- **The triangle.** In M_sb the unique Operation-2-eligible triangle is (P, u21 | v₃ = h). Its pair at h is a crossing
  pair with gap ±(D − E) = 0.
- So v₃ is ZG but not tame.

**Consequence.**
- **The literal cut breaks a needed property.** Cutting h along that pair leaves a degree-2 β-atom with zero gap. At a
  charge-0 degree-4 atom, complementary pairs have opposite gaps, so this breaks the nonzero-gap property of β-atoms
  that DH23 Prop 9.6 needs.
- **DH23 has the same gap.** It appears in DH23 L1777 against L1985, under DH23's reading that "SG triples are fixed".
- **A related gap.** With 0 < |D − E| SG, Operation 2 cuts h along a crossing (non-designated) pair. DH23 L1815's
  argument that vines are LG assumes hinges are cut along designated pairs. This is a CANDIDATE exposition gap at DH23
  L1815 / TARGET L2187.

**Repair (ruling R29, used in Lean).**
- A triangle is eligible only if its v₁ and v₂ triples are SG, its v₃ pair has nonzero gap, and at each hinge the
  triangle pair is a designated pair. Other triangles are skipped, and their v₁, v₂ are cut in Operation 3.
- Tame atoms are never cut. A final operation erases each maximal connected tame cluster.
- Components that still contain tame atoms, or were damaged by an erasure, get a separate bound (`prop96_damaged`).

---

## E17 — TARGET L2152/L2218 (`remtame`) and L2193/L2197 (`finalmol`, R = 1): single-atom erasure and "imperfect = odd"

**Status:** CANDIDATE (refereed together with E16; ruling R29). **Class:** GAP. **Main theorem:** repaired in Lean.
- Evidence: as for E16.

**(a) Single-atom erasure leaves components with no usable bound.** Two graph-level examples:
- **C1.** The chain R1–e⇄u⇄v⇄f–R2, with all of e, u, v, f tame. Erasing e and f leaves an isolated tame double bond
  {u, v} whose shared value is unpinned. Then 𝔄 ~ L^γ.
- **C0.** A similar chain isolates a degree-0 tame atom, so 𝔄 = 1, while TARGET's R = 1 bound requires L^{−η⁵}.

The repair is cluster erasure at the end of the run (E16).

**(b) TARGET L2193/L2197.** For R = 1 these lines set Z = 0 and call the imperfect components "odd". That
identification is false by TARGET's own text: L2189 says "exactly R if R=1", but L2218 says a case-(ii) removal
"increases the number of imperfect components by 2". The Z = 0 failure is shown at graph level only. Harmless.

---

## E18 — TARGET L1918 (ii): "J̃_𝒬(t,s) equals 0 if t = L_r" fails for trivial couples and trees

**Status:** CANDIDATE. **Class:** ERROR. **Main theorem:** none after the repair below, which is in Lean.
- Found while formalizing Step 4 of `vineest`; the trivial-couple case is checked in Lean in a working note (not
  included). Ruling R35.

**Location.** TARGET `vineest` Step 4, L1918 (ii): "if q = L_r then J̃_𝒬(t,s) equals 0 if t = L_r".

**Counterexample.** For the trivial couple the coherent approximant is the input itself: `RegCpl.app δ r F triv t s k
= F(k)` for all t and s, so J̃ ≡ 1 on [q, q+1] and does not vanish at t = L_r. The trivial tree behaves the same way.
The true kernel K*_triv = F(k)·1_{t>q} does vanish there. There are also two other configurations where the
approximant is nonzero:
- type 1 with q′ < q, where the approximant does not depend on t;
- type 1 with q = q′ and s < q.

**Consequence.** The constant-in-t extension of the approximants, used for the case L_{u3} > L_{u4}, gives F where the
true kernel gives 0.

**Repair (ruling R35, used in Lean).**
- For trivial 𝒬 and 𝒯, the exact kernel F·1_{t>q} replaces the approximant (no remainder arises).
- The vanishing is proved for the nontrivial approximants, where it holds.
- The cancellation (`replSum_decomp_ext`) is re-proved with the mixed family. Realness (layerregest10) transfers off a
  null set.

---

## E19 — TARGET L2213 (final count): "p_sb ≤ p_op" should be "p_sb ≤ 2 p_op"

**Status:** CANDIDATE. **Class:** MINOR. **Main theorem:** none.
- Found in the assembly of the final counting argument.

**Location.** TARGET L2213: "then we must be cutting at v in one of the Operations 1–4, so we have p_sb ≤ p_op",
used in (together3), L2214–L2216.

**Issue.** Operation 2 cuts two critical SG atoms, so the number of critical SG atoms consumed can be up to twice the
number of operations.

**Why it is harmless.** The margin absorbs it, since η³/2 ≥ 8η⁶.

---

## E20 — DH23 Prop 9.4 (L1777, L1791–L1795) and TARGET Operation 2 (L2142, L2165): triangles containing an already-cut atom ("ghost")

**Status:** CANDIDATE. **Class:** GAP. **Main theorem:** repaired in Lean for γ > 1/2; open for γ ≤ 1/2.
- Found while formalizing the triangle step, and independently re-derived by a research check with a lattice count up
  to L ≤ 400: [`docs/research/ghost-triangle-notes.txt`](research/ghost-triangle-notes.txt). Ruling R38.

**The gap.**
- DH23 L1777 cuts only triangle atoms of degree ≥ 3, so an already-cut degree-2 atom (a "ghost", for example the
  α-atom left at a joint of a vine removed in Step 1) is not cut again.
- DH23's per-step proof (L1791–L1795) only covers triangles with no ghosts: there ΔF ∈ {0, 1, 2} and Δχ = ΔF − 3.
- With an α-ghost, the per-step bound (excesseqn2), written with the true ΔF and ΔV_β, FAILS. In the explicit
  configuration v₁, v₂ have degree 4, v₃ is an α-ghost, and the outer bonds form private double bonds. The count then
  exceeds the allowed bound by ≈ L^{γ₀}. This happens in every one of the 21 patterns that contain an α-ghost.
- (together2) drops the ghost's own label factor T_g ≤ 1, which was paid when the ghost was created and is never used
  again.

**Under TARGET's cut-all reading.** The Remark at L2126 together with L2142 also cuts degree-2 atoms. Each step's
bound then holds, but the invariant claimed at L2189 ("at most R imperfect components") fails. This part is an
erratum (CANDIDATE).

**Repair (ruling R38, used in Lean).**
- Charge the ghost's label factor at the triangle step: 𝔇 ≤ C · excessRHS(true Δ's) · ∏_{α-ghosts} T(Q_g, κ_g)⁻¹.
- Each α label factor is paid once, at creation, and refunded at most once: at the final molecule, or at its deletion
  as a ghost.
- The two-α-ghost case needs 8η ≤ 2γ − 1. That is harmless for γ > 1/2, because η is chosen after γ. For γ ≤ 1/2 the
  case is OPEN.

---

## E21 — DH23 L1803 / TARGET L2131: the ι ball when the hitting cut has been deleted ("dead hit")

**Status:** CANDIDATE (ruling R38). **Class:** EXPOSITION. **Main theorem:** none.

**The gap.**
- The counting problem is a supremum over the parameters of the CURRENT molecule (DH23 L1766, TARGET L2131).
- The "fixed ball" claim for κ_v = 50 (DH23 L1803) therefore needs the earlier cut that hits v to be still carried by
  a present atom.
- If both halves of that cut were deleted by later triangle operations, the ball's centre is no longer a parameter of
  the current problem.

**Repair (used in Lean).** ι_v is defined only through cuts that are still alive when v is cut. κ_v is fixed at
creation and used consistently: in the creation-step bound, in Prop 9.6's product, and in any ghost refund. The ι
property (N2) still holds.

---

## E22 — TARGET Operation 1 (L2140): "these also include any possible triple bonds in M_sb (see Proposition subpro (2))"

**Status:** CANDIDATE. **Class:** EXPOSITION. **Main theorem:** none.
- Found while formalizing `subpro`. The configuration is constructed at molecule level; it is NOT yet verified that it
  occurs in a prime garden. Ruling R37.

**The gap.**
- Proposition `subpro` (2) only says every triple bond has a hinge endpoint. It does not place the triple bond in the
  collected objects 𝒞₁ ∪ 𝒞₂.
- **Configuration.** Merge two whole-group SG vine chains, with joints j₁, j₂ and b₁, b₂, carrying the external bonds
  j₁→b₁, b₂→j₁ and b₁→j₂. This creates a hinge–hinge triple bond that lies in no collected object.
- DH23 L1775 does cut triple bonds in Step 1, at a joint and along two of their bonds.

**Repair (ruling R37, used in Lean).**
- **Pigeonhole.** A triple bond at a hinge uses both external bonds at one joint of the hinge's unit, and that pair is
  small-gap.
- **Choice of pair.** That pair is chosen as the hinge's designated pair.
- **Step 1.** Step 1 cuts the hinge along it, which destroys the triple bond.

---

## E23 — TARGET L2122 ("essentially the same as in Sections 9–10 of [DH23]") and the proof of `propcplmol`: the stage-1 molecule can have atoms of degree 0, 1 or 2, and self-loops

**Status:** CANDIDATE; no counterexample to (finalcount1) itself is known. **Class:** GAP. **Main theorem:** repaired
in Lean (a low-degree extension of the cutting run).
- Found in the assembly of the final counting argument and settled by a research study of the counting geometry. The
  examples are Lean-checked in a working note (not included). Ruling R48.
- Evidence for the repair: [`docs/research/low-degree-cuts-handoff.md`](research/low-degree-cuts-handoff.md).

**Location.**
- TARGET L2122: "The proof is essentially the same as in Sections 9–10 of [DH23], with only minor differences due to
  the fact that here we are dealing with general gardens instead of couples."
- The proof of Prop `propcplmol` (L1306) adds that "some discussion is needed when some trees of 𝒢 is trivial".

**Why DH23's proof does not cover M_sb.**
- DH23 Props 9.4–9.6 assume every atom has degree 3 or 4 and that there are no self-loops (Remark `moleremark`, DH23
  L682).
- DH23 §10.5(2) removes only a degenerate degree-2 atom, and that for couples.

**Where M_sb violates this.** In a plain garden every branching node v has four legs, and
deg v = 4 − f(v), with f(v) = [v is a root] + #{children of v that are leaves paired with the root of a trivial tree}.
So gardens with trivial trees produce low-degree atoms, and sibling leaf pairings produce loops. The three examples
below are prime, irreducible, plain and balanced, and satisfy the full counting geometry.

**Example A, an atom of degree 0.**
- R = 2. T₁ is a single branching node v whose three leaves have signs +, −, +. T₂, T₃ and T₄ are trivial, with root
  signs +, −, −.
- Each leaf of v is paired with one trivial root. Pairs involving a root leaf produce no bond.
- So M is one atom with no bonds: connected, with bonds + R = 2 = 2n. This configuration is the only one of degree 0,
  up to signs (n = 1, R = 2).
- (finalcount1) holds, since 𝔄 ≤ 1 ≤ L^{(d−γ−1/4−1/40) − 4η⁶}.

**Example B, a self-loop.**
- Two sibling leaves are paired with each other. The prime skeleton condition excludes only mini couples and mini
  trees, not sibling pairs, so this is allowed.
- The resulting loop atom is not excluded by the ε-factor: ε(k,k,k₃) ≠ 0 exactly when k₃ = k. So on the ε-support
  the atom is degenerate, with all four legs equal.
- (finalcount1) holds, since the ε-support forces the loop momentum, giving 𝔄 ≤ L^{−(d−γ)}·C₁⁻¹δ^{1/2}.

**Example C, a non-cut degree-2 atom with a gap pair.**
- A root whose left and right children are leaves paired with two trivial roots gives an atom of degree 2 with two
  bonds of opposite direction.
- Its fixed offset is c_v = k_j − k_{j′}, a difference of two root momenta, so whether it is ZG, SG or LG depends only
  on the roots.
- Its two neighbours share a double bond, so it is not a cut atom.
- (finalcount1) holds (𝔄 ≲ L^{2γ₀+η³}).
- Variant: replace the double bond by a large irreducible block, with |k_{T₀} − k_{T₁}| ~ L⁻¹. Here (finalcount1)
  holds by TARGET's degree-2 β-cut accounting, but it cannot be proved by erasing the atom when γ is in about
  (1/2, 0.59). Erasing costs up to L^{γ₀}, against a margin of about 0.072 per unit of R.

**What TARGET supplies, and only in passing.**
- The Remark after Def `defcut` allows cuts at degree-2 atoms.
- `excessprop1` (3) covers an isolated β-atom.
- `lgmolect` allows imperfect components with ε-atoms of degree other than 4 when R ≥ 2.
- `remtame` and DH23 §10.5 cover degenerate atoms.

**Repair (ruling R48, used in Lean).**
- `FinalCountAt` gains `G.Irreducible`, matching TARGET `subpro` (1).
- The counting geometry gains two facts, proved by the stage-1 construction: the hinge triple-bond designation (E22)
  and "no loop at a hinge".
- The final count is split into a REG case (every atom of degree ≥ 3, no loop), where DH23's run applies, and a LOW
  case.
- The LOW case is handled by a generalization of the cutting run:
  - degree-2 β-cuts;
  - removal of isolated atoms;
  - exact smoothing of degenerate loops;
  - R carried as a run variable.
- No degree or no-loop premise is added to the statement. Examples A–C are valid outputs of the stage-1 construction.

---

## E24 — TARGET §redcount0, L2065 and L2067: moving the weights and the k-derivatives onto individual leaves breaks the twist-class cancellation of `vineest`

**Status:** CANDIDATE (the diagnosis was confirmed by an independent referee). **Class:** GAP. **Main theorem:**
repaired; the key extraction identity is in Lean.
- Found independently by three formalization packets (the Stage 1 reduction, the leaf map of LF twists, and
  `vineest`). Diagnosed in [`docs/research/twist-profiles-notes.md`](research/twist-profiles-notes.md); referee report
  [`docs/research/twist-profiles-referee.md`](research/twist-profiles-referee.md). Rulings R44, R45, R47.

**Quotes.**
- L2065: "⟨k_j⟩^{4Λ_{p+1}} ≤ (3n_j)^{4Λ_{p+1}}·⟨k_{𝔩_j}⟩^{4Λ_{p+1}} for some leaf 𝔩_j ∈ 𝒯_j … if we include the extra
  factor ⟨k_{𝔩_j}⟩^{4Λ_{p+1}} to the input function F_{𝔏_{𝔩_j}}(k_{𝔩_j}) …"
- L2067: "taking any ∂_k derivative is equivalent to taking exactly one ∂_{k_𝔩} derivative for some leaf 𝔩 ∈ 𝒢 …"
  followed by "these stronger bounds will follow from same arguments below".

**The gap.**
- **(i) The weights.** The leaf 𝔩_j depends on the decoration, so L2065 is a pointwise inequality inside oscillatory
  sums: the decoration sum and the twist-class sum of `vineest`. It is not a change of input function. Any rigorous
  replacement is a decoration-independent identity, such as a polynomial expansion of ⟨k_j⟩^{4Λ} over leaves or a
  Leibniz distribution of ∂_k over leaves. Those produce terms whose modified leaf lies inside the regular tree T_(u₂)
  or the regular couple Q_(u₂₃,u₀) of a vine.
- **(ii) Why such terms break the cancellation.**
  - Under a layered full twist (Def `lftwist`, L1466–L1480), T_(u₂) and Q_(u₂₃,u₀) are replaced by free coherent
    objects T′ and Q′. These are constrained only by (q, q′), their total order and their number of layer-p nodes, so
    their leaf sets differ, and so do the leaf-layer multisets.
  - A term with a modified leaf inside them therefore has no counterpart in the twisted garden.
  - Prop `vineest` is a sum over the LF-twist class with IDENTICAL inputs, and it uses the realness (layerregest10) of
    a common real input. It cannot be applied term by term.
- **(iii) Supporting facts.**
  - The leaf correspondence of an LF twist exists only on ordinary leaves (checked in Lean).
  - The realness statement holds only for symmetric (common) profile assignments.
  - With layer-dependent bounds, the region leaf-cost product is not twist-invariant (ruling R46).

**Why the result survives.** The sums TARGET forms are symmetric in the leaves they range over, and they can be
rewritten exactly as real combinations of kernels with inputs that depend only on the leaf-pair TYPE: the layer, the
root tree of the + leaf and the root tree of the − leaf.
- **Types are twist-invariant.** An LF twist acts inside the subtree of u₁, and every pair of the vine realization has
  type (q, j₁, j₁). Only (CN) vines can span two trees, and those are never twisted.
- **(a) Derivatives.** ∂_{k^i} K = Σ_𝔩 K[∂_i F at 𝔩] = d/dε|₀ K[F + ε∂_iF].
- **(b) Root linear forms.** σ_j k_j^i K = d/dε|₀ K[F·(1 + ε c_j k^i)], where c_j = [+ leaf in T_j] − [− leaf in T_j].
  This vanishes on pairs inside one tree, hence on every vine region. Then (1+|k_j|²)^{2Λ} is expanded into products of
  such forms, with the derivatives applied first.
- **(c) Exact extraction by real central differences.** For a polynomial p of degree ≤ 2M, where 2M ≥ n + R:
  - p′(0) = Σ_{k≤2M, k≠M} w_k·p(λ(k−M))/λ;
  - w_k = (−1)^{k+M+1}·C(2M,k)/((k−M)·C(2M,M)), with |w_k| ≤ 1/|k−M| and Σ|w_k| = H_M.
  - This is Lean-checked (`first_coeff_extraction`).
- **The bound.** Every term is then a kernel with real, type-uniform inputs, bounded at every layer by the one constant
  C₁ + 2/(n+R) (taking λ with max(1, V)). The Stage 1 reduction and `vineest` apply to it verbatim.
- **The loss** is (C(n+R))^{O(RΛ_{p+1})}. It is absorbed by the L-power margins, because n and R are polylogarithmic in
  L (parameters2), and not "as in L2065".
- **Side corrections to L2065.**
  - (3n_j) fails for trivial trees; use 2n_j + 1.
  - "at most R input factors" should read "at most 2R".
  - For couples the weight is ⟨k⟩^{4Λ}.
- **The flower case.** Adjustment (1) of the flower proof (L2294) obtains the external decay "by the same arguments as
  in Section redcount0", that is, by this leaf device. For the flower estimate the decay is instead extracted by one
  real Lagrange extrapolation in a common profile parameter, with no marked leaf (o63 Theorem 6.3′, refereed; see
  E33).

---

## E25 — TARGET `vineest`, L1749/L1909: the class count consumes part of the bad-vine gain

**Status:** CANDIDATE. **Class:** MINOR (an error in the proof's bookkeeping; the corrected estimate keeps half the
gain). **Main theorem:** repaired; the halved gain suffices downstream.
- Found while formalizing `vineest`. Rulings R54 and R55.
- Evidence: [`docs/research/vineest-handoff.md`](research/vineest-handoff.md) (the class-count finding and the count
  bookkeeping).

**Location.** TARGET L1909, against (vineest2), L1748–L1750 (the bound is on L1749).

**Quoted text (L1909).**

> Here note that, in cases (a)–(c) above, the number of choices for (𝒬,𝒯) is at most C₂·C₀^{n(𝒬)+n(𝒯)} by Proposition
> [layerreg2], which is acceptable because this only occurs once for 𝕌^p and can be covered by the L^{−η²} gain for
> this bad vine obtained below.

**The configuration and the missing loss.** Fix one operative bad vine and the orders of its exceptional regular couple
and tree. Their allowed layer interval has length Δ = q − q′, with Δ ≤ p ≤ 𝔇 = τ_*/δ. A coherent chain pair can be
re-layered at each of the Δ+1 intermediate layers while keeping its order fixed. Thus the count is not uniform in 𝔇.
The estimate used in the formal proof is

    #choices ≤ 16(N+1)(4·12⁹)^N 4^p.

The exponential-in-order part can be assigned to C₁. The remaining 𝔇-dependent factor cannot: C₁ is chosen before δ
and 𝔇. The upper bound 4^p is not asserted to be sharp; the actual re-layering family already shows that there is no
count uniform in 𝔇 at fixed order.

The argument supplies the full gain L^{−η²b} appearing in (vineest2), with no additional η² margin in general. Applying
the triangle inequality over the choices and absorbing their count by this gain cannot then leave that same full gain
on the right. This diagnoses a missing prefactor or margin in the proof; it is not a lower-bound counterexample to the
kernel estimate itself.

**Repair (rulings R54/R55, used in Lean).** Keep the factor C₂^b explicitly (`VineEstCanonLayerC2`), where C₂ is
chosen after δ and 𝔇. Every operative member is bad, so the number of such factors is at most b. For L ≥ L₀(C₂,η),

    C₂^b L^{−η²b} ≤ L^{−(η²/2)b}.

Use the halved-gain corollary (`VineEstCanonLayerHalf`; `vineEstCanonLayerHalf_of_C2`) and amend the mass exponent of
`Stage1Piece.RepresentsInt` to −η²b_sk/2. Ruling R55 checks that the downstream arithmetic uses only nonnegativity of
this exponent, so this amendment does not remove a needed downstream saving. The remaining exponents are unchanged.

The implication `vineEstCanonLayerHalf_of_C2` is proved; it does not by itself discharge every input of the full
`vineest` bound.

---

## E26 — TARGET (redvine), L1954–L1957: lower-child slots retain an integrated lower-joint clock, so the printed factorization is false as an identity

**Status:** CANDIDATE. The mismatch was re-derived independently by the integrated flower supplement (§12.3) and by the
U-clock resolution (§0); an independent refute-first referee of that resolution is pending, so the status is not
upgraded. **Class:** ERROR (in an intermediate identity; the estimate (redvine2) that it is used to prove survives).
**Main theorem:** repaired. The unweighted case is proved in Lean (the sealed `layergarden_v2`); the weighted flower
case is proved on paper, referee pending.
- Found while formalizing the Stage 1 splicing identity (ruling R58).
- Evidence: [`docs/research/redvine-lower-clock-handoff.md`](research/redvine-lower-clock-handoff.md);
  [`docs/research/flowerest1/uclock-RESOLUTION.md`](research/flowerest1/uclock-RESOLUTION.md) (the weighted repair,
  and §2 for the Lean declarations); [`docs/research/flowerest1/SUPPLEMENT-v2.md`](research/flowerest1/SUPPLEMENT-v2.md)
  §12.3.

**Location.** TARGET (redkg), L1725–L1726; the definition of K^𝕌, L1737–L1738; and (redvine), L1954–L1957, especially
the outer tree/couple slots on L1956.

**Quoted text.**

> we only integrate over the variables t_𝔫 for all branching nodes 𝔫 ∈ 𝒢_sk[𝕌]∖{𝔲₁}, and treat the other t_𝔫
> variables as fixed. (L1737)

> ∏_{𝔪∈𝒩_sb} 𝒦*_{𝒯_(𝔪)}(t_{𝔪^pr}, t_𝔪, k_𝔪) (L1956)

**Configuration (p = 0).** Take an eligible non-root (CL) unit U with upper joint a = u₁ and lower joint b = u₂. All
nodes have layer 0 and clocks in (0,1). Let the lower external child c = u₂₁ be a branch, and reconstruct there a
nontrivial order-2 regular paired tree, with one chain pair n₁→n₂, also in layer 0. The native factor has the time
ordering

    τ_c < t_n₂ < t_n₁ < τ_b < t_a < 1.

It is a function K*_{T_(c)}(τ_b, τ_c, k_c). The integral defining K^U integrates τ_b, because b lies inside U; it does
not include this external-child slot, because c lies outside U. After splicing, c has parent a, so the outer slot
written in (redvine) instead reads K*_{T_(c)}(t_a, τ_c, k_c). These two upper integration limits differ. Layer
separation does not make the slot constant when all layers are zero.

For a lower external child which is a leaf, the couple slot similarly reads (τ_b, τ_{c′ᵖʳ}); if its partner is a lower
child of another unit, it couples the two units' interior clocks. Twist invariance of the slot does not make its
lower-joint clock an exterior variable.

This is a structural p = 0 configuration. The cited evidence does not enumerate a complete prime skeleton or evaluate a
numerical instance, and this entry does not claim such a check.

**Repair: an exact replacement identity (redvine♯).** Keep the lower-child slots at their native clock τ_b inside the
clocked expression, and Fourier-expand those slots in that clock before separating the unit factors. The frequency λ is
routed into the unit as a modulation e^{πiλτ_b}; `vineest` holds with this modulation at a loss ⟨λ⟩^{6η⁶} (the case
λ = 0 is the unmodulated statement), by TARGET's modulation tolerance of `sumint` (FourierboundI), L1618; and the slots'
time-Fourier moments, of weight η, pay for the loss. The end product is exactly the printed conclusion (redvine2), with
no new power of L. Changing the outer clock to τ_b without changing the interface would not repair the identity: τ_b
is not a coordinate of the spliced garden.
- **In Lean (unweighted).** This is the repair used in the proof of `layergarden_v2`, which was sealed as proved on
  main for 1/2 < γ < 1 (commit `cd80ff86`; independent seal audit
  [`docs/research/seal-layergarden_v2-audit.md`](research/seal-layergarden_v2-audit.md)). On main: the summed identity
  is `WaveTurbulence.Represents.class_sum_modes`; the modulated vine estimate is the statement
  `VineEstS5C.VineEstCanonLayerHalfMK`, proved by `VineEst.vineEstCanonLayerHalfMK`; the corrected (redvine2) is
  `Represents.VineCaseRepresents`, closed by `Represents.vineCase_prefix`, which feeds the Stage 1 gate of the sealed
  proof. (`VineEst.vineEstCanonLayerHalfMK` and the sealed proof were added on main after commit `5c6d256c`, on which
  this file was first drafted; the other declarations are already there.)
- **On paper (weighted, with pins).** For the flower estimate, Theorem U-clock of
  [`docs/research/flowerest1/uclock-RESOLUTION.md`](research/flowerest1/uclock-RESOLUTION.md) proves the same
  replacement with frontier cutoffs, stem filters, the retained marked vines and the pinned lower slots (the cap couple
  of an original tree and two derivative-pattern cases). The explicit boundary phases of the pinned slots depend only on
  the fixed flower time s, not on τ_b, so the slots keep a positive time weight and no new power of L appears
  (resolution §6.3–§6.4, §15). An independent referee of this resolution is pending.

---

## E27 — TARGET L1944: the LF-twist refinement need not have at most 2ⁿ classes

**Status:** CANDIDATE. **Class:** MINOR (an error in an intermediate count). **Main theorem:** none; the final garden
count survives.
- Found while formalizing the Stage 1 class decomposition. Ruling R56.
- Evidence: [`docs/research/lftwist-class-count-handoff.md`](research/lftwist-class-count-handoff.md).

**Location.** TARGET L1944 in Stage 1, and the garden count L2250–L2251.

**Quoted text.**

> then we can further divide the sum into at most 2ⁿ terms, each of which is a sum over a new equivalence class.

**Configuration.** Fix the unlayered garden and its order n. Inside the coherent tree T_(u₂), take one coherent chain
pair whose common layer may be any integer r ∈ [q′, q]. Keeping every other datum fixed gives Δ+1 distinct layered
gardens in one LF-twist class, where Δ = q − q′. At fixed n, Δ can grow with p < 𝔇 as δ decreases. Under the
prescription in which every vine is LG there are no SG vines at which the finer relation is allowed to twist; these
members therefore give distinct singleton pieces. Choosing Δ+1 > 2ⁿ violates the asserted uniform refinement count. The
same obstruction defeats any fixed exponential-in-size bound on pieces per coarse class.

This is an LF-twist issue: the relation changes coherent objects and their layerings, not only the finite plain-twist
choices. Merging the singleton pieces would put their Δ+1 multiplicity into the represented mass, whose constant C₁ is
chosen before δ and 𝔇.

**Why the final count is still usable.** L2250–L2251 counts canonical layered gardens, not merely coarse classes. It can
count all the re-layerings; no false final estimate is asserted here.

**Repair used in the Lean interfaces (ruling R56).** Replace the per-class piece cap by a direct count at fixed (g, r):

    #{π : ḡ(π)=g, ρ̄(π)=r} ≤ 3ᴺ C₀ᴺ (C₀r)! (C₀R)! C₂^{g+r}.

Here N is the Stage-1 size budget. Map pieces to representative layered gardens, with fibres of size at most 3ᴺ, and
use the garden count including all free coherent layerings. The needed layer dependence is covered uniformly by the
late constant C₂ (in particular K^{𝔇+1} ≤ C₂). Keep the class/partition data, but do not infer a uniform number of
faithful pieces from the old class count. The same correction applies on the flower side.

---

## E28 — TARGET `excessprop1`, L2156–L2162: degree-2 cuts need explicit isolated-half bookkeeping

**Status:** CANDIDATE; harmless with the corrected ledger. **Class:** EXPOSITION. **Main theorem:** none.
- Found while extending the cutting run to low-degree atoms (ruling R48); no false TARGET statement is claimed.
- Evidence: [`docs/research/low-degree-cuts-handoff.md`](research/low-degree-cuts-handoff.md), "Errata"; the example is
  Lean-checked in a working note (not included).

**Location.** TARGET's degree-2-cut remark L2126, increment convention L2138, and excess bounds L2156–L2161.

**Quoted text.**

> This case is in fact trivial: after the cut v₂ becomes an isolated atom (without any bond) which forms a single
> connected component by itself. (L2126)

> use Δ to denote increments (such as ΔF = F_pos − F_pre). (L2138)

**Example C (E23), with a complete garden configuration.** Take four trees with root signs (+,−,+,−): trees 0, 2, 3 are
ternary corollas, tree 1 is trivial. Number the children 0, 1, 2. Pair leaves as

    (0,[0]) ↔ (1,[]),   (0,[1]) ↔ (2,[0]),   (0,[2]) ↔ (3,[0]),
    (2,[1]) ↔ (3,[1]),  (2,[2]) ↔ (3,[2]).

The molecule has n = 3 atoms a, b, c (the three corolla roots), four bonds, R = 2, degrees (2,3,3), one bond a–b, one
a–c and two b–c. The two bonds at a have opposite directions. Choose the difference of the two prescribed root momenta
so that their pair gap c_a is nonzero, of size about L⁻¹. This is the plain, prime, irreducible Example C of E23; the
Lean check also verifies that the degree-2 cut applies and that the index drops to R − 1.

**The bookkeeping ambiguity.** Cutting a along both bonds creates one non-isolated β-half and one isolated β-half.
Before deleting that isolated half the literal increments are ΔF = 1 and ΔV_β = 2. If it is immediately discarded, the
true remaining-graph increments are instead ΔF = 0 and ΔV_β = 1. In the factor

    L^{(2γ₀+5η²)ΔF − (γ₀+2η²)ΔV_β}

the two conventions give L^{η²} and L^{−γ₀−2η²}, respectively: a missing factor L^{γ₀+3η²}. Thus one cannot use the
compressed graph's increments in the unamended per-step estimate. The displayed formula is not refuted when the
isolated half is counted as TARGET literally describes.

**Repair used in Lean.** `UStepD3.excess` and `UStepD1.excess_new` keep the isolated β-half in the excess ledger. When
it is deleted, `InvL.stepD3` and `UCtx.stepD3`/`UCtx.stepD1` decrease the run index R by one. The resulting L^X margin,
X = d − γ − 1/4 − 1/40, pays the missing L^{γ₀+3η²} under the standing small-η conditions. State both conventions and
the index drop explicitly; do not silently discard a half while treating Δ as the true graph increments with unchanged
R.

---

## E29 — TARGET L2259–L2261/L2287: reusing the skeleton and twist machinery for flower gardens needs marked-garden bookkeeping that is not written

**Status:** CONFIRMED, as an omitted routine construction. The earlier flower-design referee
([`docs/research/flower-design-referee.md`](research/flower-design-referee.md), §8) and the independent assessment
([`docs/research/astra-flowerest1-report.md`](research/astra-flowerest1-report.md), §2 "Preliminary completion" and
§4.2) both checked it; the construction that fills it passed the independent referee of the supplement
([`docs/research/flowerest1/REFEREE.md`](research/flowerest1/REFEREE.md), Lemma 2.1: PASS, one wording fix).
**Class:** EXPOSITION (revised from GAP). **Main theorem:** repaired on paper (refereed).
- Found by the first formalization of flower skeletons and by the flower design study.
- Evidence: [`docs/research/flower-skeleton-handoff.md`](research/flower-skeleton-handoff.md),
  [`docs/research/flower-design-notes.md`](research/flower-design-notes.md); the fill:
  [`docs/research/flowerest1/SUPPLEMENT-v2.md`](research/flowerest1/SUPPLEMENT-v2.md), Lemmas 2.1–2.2.

**Revision.** An earlier version of this entry said that the skeleton construction requires a plain, irreducible
garden, so that no skeleton is defined for flower gardens. That was too broad. The skeleton theorem is stated "for
any garden" (T870, Prop `propstructure2`). Irreducibility enters only later: in the connected count of `propcplmol`
(T1304) and in the domain of the canonical layered full twists (T1466). What is missing is only the bookkeeping of the
marked flowers.

**Location.** TARGET's optional pairing footnote L2259, flower canonicity L2261, and the moment expansion L2287–L2288;
compare the skeleton theorem at L870.

**Quoted text.**

> We may also pair the flowers (for example pair the flower of the first tree with the second, the third with the
> fourth, etc.) to make 𝒢 a genuine garden, as was done in [DH23], but this is not necessary in the proof below.
> (L2259)

> so we will make no irreducibility assumption about flower gardens. (L2287)

> for any garden 𝒢 there is a unique prime garden 𝒢_sk, called the skeleton of 𝒢, such that 𝒢 is obtained from 𝒢_sk
> by replacing each leaf pair with a regular couple and each branching node with a regular tree. (L870)

**What is missing.** The flowers are marked, unpaired leaves, and each flower parent carries a fixed-time constraint.
Reusing the proof of `layergarden` needs: an encoding of the flowers that keeps them marked; a decomposition into
components to which T1304 and T1466 apply; and the rule that a mark absorbed into a regular object stays with that
object. The paper gives none of these. The footnote's flower-to-flower pairing does give a genuine garden, but it can
change which objects are regular and does not carry the marks.

**Two-corolla configuration (Lean-checked in a working note, not included).** Take two ternary corollas, root signs
(+,−), with the left child of each marked as its flower. Pair the middle children across the trees, and likewise the
right children; put every node in layer 0. Pairing the two flowers with each other produces the regular (1,1)
mini-couple, whose regular reduction has a zero-order skeleton: the marked fixed-parent-time kernel is not preserved by
that pairing. Disjoint unions of such pairs give allowed flower inputs of any width 2P with reducible completions. This
is not a counterexample to (flowerest2).

**The fill (routine).** Attach to each flower f_j an additional trivial tree of sign −ζ_{f_j} (a "cap"), paired with
f_j and carrying the fixed momentum k′ in place of an input profile. This is an exact encoding of the decoration sum and
adds no bond between branching nodes. Apply the skeleton theorem T870 to the capped garden, decompose it into at most
2P components (T637), each a canonical garden or couple, and carry the marks through all collapsings. The supplement
proves the needed identities (Lemma 2.1, capped encoding; Lemma 2.2, decoration-sum and moment identities), and both
passed the independent referee. The heavier formal design adopted earlier (garden-level excision with anchor trees,
ruling R61) is one implementation of the same idea; the refereed completion does not use excision.

---

## E30 — TARGET L2295 (2): fixing the flower-parent resonance does not remove the Dirac trace

**Status:** CONFIRMED, that the printed shortcut is invalid: checked by the earlier flower-design referee
([`docs/research/flower-design-referee.md`](research/flower-design-referee.md), items 1, 2 and 8) and by the
independent assessment ([`docs/research/astra-flowerest1-report.md`](research/astra-flowerest1-report.md), §2 (2) and
§3.6). **Class:** GAP. The printed justification does not work; the mechanism that replaces it is in DH21 for the
unlayered setting, and its layered version is a new estimate. **Main theorem:** repaired on paper: Theorem 7.3′ of the
o73 resolution, refereed (REFEREE-73: no FAIL; PASS AFTER FIX, no exponent changed).
- Evidence: [`docs/research/flower-skeleton-obstruction.md`](research/flower-skeleton-obstruction.md); the repair
  [`docs/research/flowerest1/o73-RESOLUTION.md`](research/flowerest1/o73-RESOLUTION.md) (Theorem 7.3′, §21) and its
  referee report [`docs/research/flowerest1/REFEREE-73.md`](research/flowerest1/REFEREE-73.md).

**Location.** TARGET (kqflower), L2265, and adjustment (2) of the proof of Prop `flowerest1`, L2295. Compare DH21
L2684–L2694 (the same Dirac factors in DH21's flower section) and DH21 Corollary 11.3 (L2699–L2704).

**Quoted text (L2295).**

> They may also come from the δ(t_{𝔣ᵖʳ}−s) factor which removes the integration in the t_{𝔣ᵖʳ} variable, but Ω_{𝔣ᵖʳ}
> has at most L^{10d} possible values once we fix each k_ℓ to a unit ball, so we may fix the value of Ω_{𝔣ᵖʳ} and
> safely get rid of the factor e^{ζ_𝔫πi·δL^{2γ}Ω_𝔫t_𝔫} for 𝔫 = 𝔣ᵖʳ at a loss of at most L^{10d}.

**What is valid.** With k′ fixed and the sibling momenta localized to unit balls, the flower-parent resonance takes
polynomially many values, uniformly in k′. No defect in that count is alleged.

**What is missing.** Fixing Ω_{𝔣ᵖʳ} makes its phase a constant; it does not restore the removed time integration. The
pinned node imposes caps τ_child < s on its free children and a floor τ_parent > s on its parent. If 𝔣ᵖʳ lies on a
regular chain, the object is a trace of an ordered chain integral, not the all-times-integrated regular-object factor,
and the linked partner's phase is still inside an integral and must be consumed. The estimates for incoherent objects
(T1084–T1089) and for the residual molecule (T1998) must be re-proved for the altered domain.

**Concrete time-dimension test (Lean-checked identities in a working note, not included).** In the two-corolla garden
of E29, with all layers 0, root momenta 0, flower labels 1, other child labels (2,1) and 0 < s < t < 1, both roots are
flower parents. The two Dirac factors remove all branch-time integrations and the remaining time integral is exactly 1,
while a positive-order plain kernel with bounded amplitudes is O(t^{order}). This refutes an unchanged
positive-time-volume representation of the pinned kernel; it is not a counterexample to the flower estimate.

**DH21's mechanism.** DH21 treats the same factors (L2684): "this difference will cause at most another L^{20d} loss
… only one node (and one time variable) is affected". Its argument is a mixed norm: the pinned chain expression
"satisfies the same bound as the one with t_𝔪 integration, but in the *weaker norm* L^∞_{α_𝔪} L¹_{α[𝒩*∖{𝔪}]}"
(L2688); in the residual molecule the pin loses "only *one* denominator" (L2692); and L^∞ in α_𝔪 is converted back
to L¹ at a loss L^{5d} by restricting α_𝔪 to unit intervals (L2694). TARGET's L2295 does not cite this argument and
replaces it by "fix the value of Ω". DH21 itself omits cases ("Case 1 is much easier … we can directly calculate it",
L2688; "for simplicity we will omit this case", L2689), and its operators act on a single unit interval (L953), with
no layers.

**Repair (refereed).** Theorem 7.3′ of the o73 resolution proves the layered pinned and face estimate in the actual
flower geometry, with the protected objects kept whole (no excision). The flower parent is the last node of a layer-p
chain of a regular object (o73 Prop 3.1, the layered analogue of DH21's t_𝔪 = t_{2m} at L2689). Terminal pins and time
faces get consumed time-Fourier and coefficient estimates (the pin phase is consumed exactly, o73 Lemma 12.1); residual
pins and faces satisfy the local-supremum ladder estimate (Prop 18.1). The cost is L^{400d} per protected incidence,
at most L^{10400dP} in total (at most 26P incidences), with an exponential base independent of δ and no incoherency
gain lost in the end. This replaces the earlier formal design of ruling R61 (a pendant stub after excision).

---

## E31 — TARGET L2297 (4): leaving special-node SG vines unspliced does not preserve `subpro` (4)

**Status:** CONFIRMED. The independent referee of the o75 resolution checked the configuration against the source
([`docs/research/flowerest1/REFEREE-2.md`](research/flowerest1/REFEREE-2.md), §3.1: "E31's configuration refutes the
verbatim T2045"); so did the independent assessment
([`docs/research/astra-flowerest1-report.md`](research/astra-flowerest1-report.md), §2 (4) and §3.6: "Invocation
invalid") and the earlier flower-design referee
([`docs/research/flower-design-referee.md`](research/flower-design-referee.md), §8). **Class:** GAP. This concerns the
reuse of Stage 1 and Stage 2 with a modified splicing rule, not a refutation of `subpro` itself. **Main theorem:**
repaired on paper: Theorem 7.5′ of the o75 resolution, refereed (REFEREE-2: PASS AFTER FIX; the fixes are editorial or
bookkeeping and change no statement or number).
- Evidence: [`docs/research/flower-design-notes.md`](research/flower-design-notes.md); the repair
  [`docs/research/flowerest1/o75-RESOLUTION.md`](research/flowerest1/o75-RESOLUTION.md) (Theorem 7.5′, §3; count and
  budget §§7–8).

**Location.** Adjustment (4) of the proof of Prop `flowerest1`, L2297, against Proposition `subpro` (4), L2045.

**Quoted text.**

> Clearly there are less than 20P vines containing one of these special nodes; for each of them we can use
> Proposition [ladderl1new] to treat its ladder parts, and sum and integrate trivially over the k_ℓ and t_v variables
> for ℓ and v outside of the ladders (there are at most 20 such variables per vine). (L2297)

> Any SG vine-like object which is not a subset of an SG vine-like object in 𝒞₁, and also *does not contain* a hinge
> atom, must be a subset of a DV or an LG or ZG vine-like object (L2045)

**Configuration exposing the conflict.** Consider a maximal non-root SG (CL) vine disjoint from other collected
objects, for example a two-joint vine (I) with degree-four joints a, b, whose upper joint a is a child of an original
flower-tree root (one of L2297's special nodes). Suppose there is no containing DV or larger LG/ZG object, and no other
collected object meeting this vine. If the exceptional-vine rule leaves it unspliced, it is an SG object outside 𝒞₁ with
no hinge and no containing DV/LG/ZG object: exactly the alternative that `subpro` (4) excludes for the ordinary
splicing. Paying a polynomial L-loss for fewer than 20P exceptional vines does not restore that structural premise, and
"sum and integrate trivially" over their remaining variables is valid inside the oscillatory sum only after the
boundary data are pinned (Fubini), not as an absolute bound on one piece of a cancelling sum.

**Repair (refereed).** Theorem 7.5′ of the o75 resolution. A vine is *marked* if its twist-active set meets the
protected set Π of at most 26P vertices (the special nodes, with the regular objects that contain them); marked vines
are neither twisted nor spliced, so the twist classes leave the truncation data of L2297 (i)–(iii) unchanged. The
unspliced members of affected chains (the survivors, at most 2b of them) stay in the molecule 𝕄_sb, which remains
connected, and are removed by an added Stage 2 operation. `subpro` then holds with 𝒞₁ replaced by 𝒞₁ together with the
survivors, plus one added clause for objects meeting the survivors' joints; ladders are split at those joints and at
the protected atoms. The extra cost is L^{(360d+16)b} ≤ L^{(9360d+416)P}, within the L^{(100d)³P} allowance (see also
E43). The integrated supplement and the planned Lean work follow this non-excision route rather than the excision
design of ruling R61.

---

## E32 — TARGET L2312: the root-time derivative is handled by decapitation, with width-four components retained

**Status:** CONFIRMED, as an exposition gap: the earlier flower-design referee found the width-four configuration
below ([`docs/research/flower-design-referee.md`](research/flower-design-referee.md), item 6), and the independent
assessment agrees that this is an exposition and assembly issue
([`docs/research/astra-flowerest1-report.md`](research/astra-flowerest1-report.md), §4.2). **Class:** EXPOSITION.
**Main theorem:** repaired. The couple clause (ℒ₀ and the root-pinned ∂ₜa^tr) is proved in Lean on main; the
flower-tree root pin (the dRoot pattern) is covered on paper by Theorem 10.4 of the o104 resolution (see E45).
- Found by the flower design study; its initial "no Stage 1" claim was corrected by the referee. Ruling R61.

**Location.** TARGET L2312, the use of the flower argument for ∂ₜaᵗʳ and ∂ₜℒ₀.

**Quoted text.**

> In addition, we can treat the time derivative ∂ₜa_k^{tr} (which simply contains an extra δ(t_𝔯−t) factor in 𝒥_𝒯
> similar to the one in (jtflower)) using the same arguments in the proof of Proposition [flowerest1], to get the same
> bound (trterm1) with an additional L^{100d} loss.

**The required identity.** Differentiating a nontrivial tree's upper endpoint pins its root at t. Excise that root
once: its three child subtrees become trees with cap t, and its coupling, ε, phase and local label sums move outside.
For a differentiated couple, excising both roots gives a width-six garden. Ordinary Stage 1 alone integrates the root
time and does not implement this identity; a separate root-Dirac estimate for regular objects is unnecessary after the
excision.

**A width-four configuration.** Let r₁ have children a₁, a₂, a₃, with a₁ and a₂ leaves paired to each other. Let a₃
and the other root r₂ be the corolla roots of a (1,1) mini-couple, their three child pairs matched across. The couple 𝒬
is regular: remove the top mini-tree and then that mini-couple. After deleting r₁, r₂, the detached a₁, a₂ form a
trivial couple, while {T_a₃, T_b₁, T_b₂, T_b₃} (b₁, b₂, b₃ the children of r₂) is one irreducible width-four component:
the a₃ corolla and three trivial trees, each corolla leaf paired to one trivial root. It has no vine but is not a
couple. So "only regular couples remain" is not a valid shortcut, and recursive decapitation through depth O(N) would
lose too much.

**Repair.** Use the single root-excision identity, then componentwise bounds: regular and trivial couples use their
pointwise kernels; nonregular components, including the width-four components above, go through the Stage 1 bound of
`layergarden` (with the low-degree geometry of E23 where needed). The local label loss is at most δ²L^{2d+2γ}, within
the permitted L^{100d}.
- **In Lean.** The couple clause of the frozen flower statement, which covers ℒ₀ and ∂ₜa^tr, is proved on main
  (`WaveTurbulence.FlowerTop.coupleHalf_of_spine`, applied in `WaveTurbulence.Flower.Cases` to the proved Stage 1 gate
  and the proved final count `finalCount_half`). The first two were added on main after commit `5c6d256c`.
- **On paper.** For flower trees the root pin is the top face of the exact time-integration identity (supplement
  Lemma 9.1); Theorem 10.4 of [`docs/research/flowerest1/o104-RESOLUTION.md`](research/flowerest1/o104-RESOLUTION.md)
  treats it together with the other derivative patterns (E45).

---

## E33 — TARGET L2294/L2299: the cutoffs need DH21's product partition, and the M₁ gain must be extracted without breaking the twist-class grouping

**Status:** CONFIRMED. The independent assessment
([`docs/research/astra-flowerest1-report.md`](research/astra-flowerest1-report.md), §2 (1), §3.4 and §4.2) finds that
"maintaining the grouped estimate while extracting that decay is the real obligation"; the earlier flower-design
referee confirmed the cutoff point ([`docs/research/flower-design-referee.md`](research/flower-design-referee.md),
items 7–8). **Class:** GAP. The non-routine piece is the extraction of the M₁ gain inside the cancelling twist-class
sums; the power counting itself and the absorption of internal cutoffs are routine. **Main theorem:** repaired on
paper: Theorem 6.3′ of the o63 resolution, refereed (REFEREE-2: PASS).
- Found by the flower design study and the cutoff study (rulings R61–R63). The defect of our own first frozen cutoff is
  separated in E34.
- Evidence: [`docs/research/flower-cutoff-notes.md`](research/flower-cutoff-notes.md); the repair
  [`docs/research/flowerest1/o63-RESOLUTION.md`](research/flowerest1/o63-RESOLUTION.md) and its referee report
  [`docs/research/flowerest1/REFEREE-2.md`](research/flowerest1/REFEREE-2.md), §1.

**Location.** TARGET L2283–L2285, adjustment (1) L2294 and adjustment (6) L2299; DH21 Corollary 11.3 L2699–L2704 and
the per-variable partitions L2731/L2735.

**Quoted text.**

> The extra factor M₁^{−80dP} when assuming max{|k_ℓ| : 𝔣_j ≠ ℓ ∈ ℒ_j} ∼₀ M₁ comes in the same way (note that if we
> insert some cutoff to the tree 𝒯 associated to 𝒳, then the same cutoff will appear in each tree 𝒯_j occurring in the
> garden 𝒢 associated with the expansion (flowerexp2)). (TARGET L2294)

> and we insert suitable cutoff functions supported in |k_ℓ| ≤ M₀ for each 𝔣 ≠ ℓ ∈ ℒ*; moreover, suppose we insert one
> (or more) cutoff function supported in |Ω_{𝔫_j}| ≥ M₁ for some 1 ≤ j ≤ n−1, where 𝔫_j is the j-th node in the stem
> from top to bottom (in particular 𝔫_n = 𝔣ᵖ), (DH21 L2699)

**The intended smooth partition.** DH21 L2731 decomposes each non-flower leaf separately and then groups the dyadic
indices by their maximum; L2735 does the same for stem resonances. For a finite family of nonnegative magnitudes y_a,
this gives

    Ψ₀(y) = ∏ₐ χ₀(y_a/L),
    Ψⱼ(y) = ∏ₐ χ₀(y_a/(2ʲL)) − ∏ₐ χ₀(y_a/(2ʲ⁻¹L)),  j ≥ 1.

This is a difference of smooth products, not a scalar cutoff evaluated on a pointwise maximum (TARGET's "smooth cutoff
function" of a maximum, L2283/L2285, is read in this product form; see E34 and the Deviations). DH21 Corollary 11.3
states the gain M₁^{−1/9}M₀^{5d}, with M₀ its leaf scale and M₁ its stem scale; TARGET calls these scales M₁ and M₂.

**What is missing.** After the layered expansion (L2261) an original non-flower leaf can be the root of an attached
lower-layer garden, so a cutoff slot can be an internal node whose momentum is a signed sum of descendant input
momenta. Two things are then needed.
- *Routine:* the power counting. Momentum conservation (T641) gives ⟨k − ζk′⟩ ≲ m·max⟨k_ℓ⟩ over non-flower leaves and
  |k_v| ≤ |D(v)| max |k_ℓ| over the descendants of a frontier vertex, with m a polynomial in the order; this places the
  powers M₁^{−80dP} and ⟨k − ζk′⟩^{−4Λ_{p+1}P} on final leaves within the regularity budget Λ_p = 40dΛ_{p+1}
  (assessment §2 (1)). Cutoffs at internal momenta are smooth functions of linear forms and fit the Fourier-measure
  amplitude steps of `proplayer1` and `sumint` (E37, E38).
- *Not routine:* keeping the twist-class cancellation while extracting the decay. A decoration-dependent choice of a
  large leaf, as in the leaf device of L2065 that L2294 invokes ("the same arguments as in Section redcount0"), is a
  pointwise inequality inside oscillatory sums and breaks the LF-twist grouping (E24). Bounded weights cannot simply
  be dropped from a cancelling sum either: 1 + (−1) = 0 becomes 1 after weighting its two terms by (1, 0).

**Repair (refereed).** Theorem 6.3′ of the o63 resolution. Replace each input profile F by F·w_{ρ,z}, with
w_{ρ,z} = χ(·/ρ) + z(1 − χ(·/ρ)). On the support of the cutoffs at least P leaf pairs have momentum at least 2ρ, and on
such a pair w_{ρ,z} = z exactly; so each decoration's profile product is a polynomial of degree at most n in z,
divisible by z^P. One real Lagrange
extrapolation from n+1 nodes in [0, Z] to z = 1, taken before any absolute value, gives an exact identity with
coefficients of total size at most 8ⁿZ^{−P}. Every evaluated family keeps a common real profile, so the twist-class
cancellation is untouched; there is no L-loss and no marked leaf. The same extraction gives the external decay
⟨k − ζk′⟩^{−4Λ_{p+1}P} of adjustment (1), which is the flower case of E24. The M₂ half of the cutoffs is E35, E39 and
E44. The earlier formal design (a Markov-type identity with marked decaying inputs) is superseded.

---

## E34 — frozen `layergardenFlower_v2`: max-form cutoffs differ from the source's product partition

**Status:** a DEVIATION of our frozen statement, not a TARGET erratum (ruling R62). **Class:** DEVIATION. **Main
theorem:** not applicable; the successor `layergardenFlower_v3` uses the product form (D13). No falsity of the
max-form estimate is established.
- Evidence: [`docs/research/flower-cutoff-notes.md`](research/flower-cutoff-notes.md); the probe is a working note (not
  included).

**Location.** TARGET L2283/L2285, read with DH21 L2731/L2735. On the Lean side, the frozen definitions
`LayeredGarden.cutWeight1`/`cutWeight2` feed `flowerSum`, which `layergardenFlower_v2` uses
(`WaveTurbulence/Frozen/Theorems/LayergardenFlowerV2.lean`).

**Quoted text.**

> by a smooth cutoff function for the tree 𝒯, where 𝔣 is the flower of 𝒯 and ℒ the set of leaves, then (flowerest2)
> holds with an extra factor M₁^{−80dP} on the right hand side (TARGET L2283)

> 1 = Σ_{R≥L} χ_R(k_ℓ), where χ_R(z) is supported in |z| ≲ R if R = L and in |z| ∼ R if R > L, for each 𝔣 ≠ ℓ ∈ ℒ*.
> (DH21 L2731)

**The exact mismatch.** The frozen `cutWeight1` applies `dyadicCut` to a `Finset.sup` of leaf magnitudes in each
original tree; `cutWeight2` does so to stem-resonance magnitudes. Thus for j = 0 its factor is χ₀(maxₐ y_a/L), and for
j ≥ 1 it is the difference of the two scalar max cutoffs. The DH21 per-variable partition, grouped by its largest dyadic
scale, instead gives the product differences Ψⱼ of E33. These have the same intended dyadic role but are different
functions. The words "smooth cutoff" in TARGET do not prescribe our nonsmooth scalar-of-max implementation.

**Lean-checked two-leaf example (working note).** Let L > 0 and take two magnitudes y₁ = y₂ = 3L/4 in one tree at
j = 0. Put c = χ₀(3/4). For the frozen χ₀(x) = smoothTransition(2 − 2|x|), the probe proves 0 < c < 1. Then

    frozen factor = χ₀(max(y₁,y₂)/L) = c,
    product factor = χ₀(y₁/L)χ₀(y₂/L) = c²,
    c − c² = c(1 − c) > 0.

The check uses only the standard axioms. It proves that the weight functions differ, not a counterexample to the full
frozen estimate or a nonzero lower bound for an admissible kernel.

**Repair of the formalization (ruling R62; decision D13).** `layergardenFlower_v2` is not edited. The successor
`layergardenFlower_v3` uses `prodDyadicCut`, `cutWeight1P`, `cutWeight2P` and `flowerSumP`, and keeps the other
clauses (`flowerSumP_none`: the uncut expressions agree by `rfl`). It passed an independent statement audit before it
was frozen. Both v2 and v3 remain frozen and open in Lean. The refereed written completion of the flower estimate
(E29–E46) targets v3, with the frozen product cutoffs kept exactly (supplement §12.2).

---

## E35 — TARGET L2299: the time integration needs face bounds, and the per-tree gain M₂^{−P/9} goes beyond the cited DH21 corollary

**Status:** CONFIRMED. The independent assessment
([`docs/research/astra-flowerest1-report.md`](research/astra-flowerest1-report.md), §2 (6)) separates the elementary
time integration from the missing estimates, and the independent referee of the supplement checked the citation
([`docs/research/flowerest1/REFEREE.md`](research/flowerest1/REFEREE.md), §3: "T's per-tree product M₂^{−P/9}
therefore goes beyond what Cor 11.3 states"). **Class:** GAP. No falsity of the stated bound is claimed. **Main
theorem:** repaired on paper, refereed: the exact face identity (supplement Lemma 9.1), Theorem 7.3′ of the o73
resolution with its Proposition 20.1, and Theorem 8.2′ of the o82 resolution.
- Found by the study of the M₂ cutoff ([`docs/research/flower-cut2-notes.md`](research/flower-cut2-notes.md), §9),
  with an independent review ([`docs/research/flower-cut2-review.md`](research/flower-cut2-review.md)).
- Repair: [`docs/research/flowerest1/o73-RESOLUTION.md`](research/flowerest1/o73-RESOLUTION.md) (Prop 18.1, Prop 20.1,
  Theorem 7.3′), [`docs/research/flowerest1/o82-RESOLUTION.md`](research/flowerest1/o82-RESOLUTION.md) (Theorem 18.2,
  Theorem 8.2′); referee reports [`REFEREE-73.md`](research/flowerest1/REFEREE-73.md) and
  [`REFEREE-82.md`](research/flowerest1/REFEREE-82.md) (no FAIL).

**Location.** TARGET adjustment (6), L2299; related stem invariance L2300. DH21 Corollary 11.3, L2699–L2704, is a
comparison, not a ready-made layered 2P-mark theorem.

**Quoted text.**

> By integrating in t_j before manipulating everything else, and arguing similarly as in the proof of Corollary 11.3
> in [DH21], we gain a factor M₂^{−P/9} from this integration.

**(a) Time faces.** Mark a free stem branch b other than 𝔣ᵖʳ, with free parent u and off-stem children at times σ₁,
σ₂; its stem child may be the fixed flower parent at s. The b-clock ranges over

    max(s, σ₁, σ₂) < τ_b < τ_u.

Integrating e^{iωτ_b} first, ω = πζ_bδL^{2γ}Ω_b, produces upper and lower endpoint terms, (e^{iωτ_u} −
e^{iω max(s,σ₁,σ₂)})/(iω) with coefficient 1, which need not vanish. With the remaining kernels present these are cap
and floor faces: the parent or one child is pinned at the marked clock. Faces have their own lower-dimensional
integration measure, and the child faces do not follow from the side kernels' time-Fourier norms (o73 §15 gives a
family bounded in that norm whose child face grows). At a residual vertex the frequency is shifted, α_v = β_v + ξ_v,
and ξ_v can cancel β_v, so the raw reciprocal 1/β_v cannot be used there.

**(b) The other cutoffs still matter.** The product partition (E33) marks one annular resonance per original tree but
leaves smooth upper cutoffs at the other stem nodes. They cannot be dropped from an oscillatory sum; see E39 (inside
regular objects on the stem) and E44 (on ladder rungs).

**(c) The citation.** DH21's high-resonance gain is a single factor M₁^{−1/9}M₀^{5d}, even with several cutoffs, and it
comes from coefficient weights and denominators, not from integrating the selected time first. TARGET's product over
the 2P trees is therefore a new requirement, not a consequence of Corollary 11.3.

**Repair (refereed).** Integrate the selected stem time exactly and keep the raw face identity (supplement Lemma 9.1,
PASS). Inside regular objects, the faces are estimated with the reciprocal retained (o82 Theorem 18.2). At skeleton and
residual selected vertices, o73 Proposition 20.1 replaces the raw reciprocal by a dichotomy (either the reciprocal is
usable, or a large adjacent frequency pays through a moment). Each selected occurrence gains M₂^{−1/18}, and the 2P
trees give M₂^{−P/9}. In this completion the marked vines are neither twisted nor spliced, and the filters at atoms of
the spliced molecule are common to each twist class (o75 Lemma 2(d)), so the separate cut-label carrier of the earlier
formal route (rulings R63–R64; [`docs/research/flower-cut2-fiber.md`](research/flower-cut2-fiber.md), refereed in
[`docs/research/flower-cut2-fiber-referee.md`](research/flower-cut2-fiber-referee.md)) is not needed.

---

## E36 — TARGET L2294/L2297: the cutoff weights are not checked to agree across twist classes

**Status:** CONFIRMED, as an omitted check whose fill is routine: the independent assessment checked both the |r| route
and the exact common factor for the coherent frontier weights
([`docs/research/astra-flowerest1-report.md`](research/astra-flowerest1-report.md), §3.3 and §4.3), and the fill passed
the independent referee of the supplement ([`docs/research/flowerest1/REFEREE.md`](research/flowerest1/REFEREE.md),
Lemmas 3.2, 5.1–5.3). **Class:** EXPOSITION. **Main theorem:** repaired on paper (refereed).

**Location.**
- Adjustments (1) and (4) of the proof of `flowerest1` (L2294, L2297).
- Definition `lftwist` (L1466–L1480) and Remark `twistexplain` (d) (L1452).
- The vine cancellation (L1907) and its |r|-error case (b) (L1902).

**Quoted text (L2294).**

> (note that if we insert some cutoff to the tree $\Tc$ associated to $\Xs$, then the same cutoff will appear in each
> tree $\Tc_j$ occurring in the garden $\Gc$ associated with the expansion (\ref{flowerexp2})).

**What is missing.**
- **Where the cutoff sits.** After the layered expansion (Definition `defflower`, L2261), the M₁ cutoff can sit at an
  internal node: an original non-flower leaf that is not paired in layer p becomes the root of a tree of an attached
  garden (E33).
- **What the vine estimate needs.** Its leading term cancels exactly after summing over the layered full twists of a
  vine (L1907). The paper does not say how the inserted weight behaves across a twist class.

**What does hold.**
- **The twist moves the cutoff only slightly.** A unit LF twist switches the values of k_{𝔲₂} and k_{𝔲₂₃}
  (Remark `twistexplain` (d), L1452). These differ by the vine's gap r, with |r| ≤ L^{−γ+η} for spliced (SG) vines.
  - A cutoff at scale M ≥ L that reads one of them therefore changes by O(|r|/M) across the twist.
  - The vine proof already turns differences of this kind into a factor |r| (case (b), L1902, giving assumption (b)
    of `sumint`, L1611).
- **The skeleton reading is exact.** If the cutoff is read with layers taken from the skeleton, the weight on a vine
  region is a product over the vine's bonds of functions of atom layers, bond momenta and M. Every LF twist preserves
  these, so the weight is exactly common to the class.

**The fill.** Show that the cutoff weight is class-common up to such |r|-terms, or exactly in the skeleton reading,
and route the error through case (b). The paper does neither. For the actual frontier cutoffs the leading cancellation
is in fact exact: in a coherent regular object the frontier weight reduces to a real profile replacement F_p ↦
F_pχ(·/M)² in each layer-p side object and, if q = p > q′, one trunk factor χ(k/M) at the external momentum, so the
equal-upper-layer pair (𝒬, 𝒯) of the cancellation at L1883–L1907 carries a common real scalar (assessment §4.3). The
supplement proves this and the commutator bounds: Lemma 3.2 (shell expansion and commutators), Lemma 5.1 (coherent
trunk factorization; PASS after a scope fix), Lemma 5.2 (weighted tuple identity, with multiplicities) and Lemma 5.3
(local weighted `vineest`), all passed by the independent referee
([`docs/research/flowerest1/SUPPLEMENT-v2.md`](research/flowerest1/SUPPLEMENT-v2.md), §§3–5).

**Formalization note (not an issue in the paper).** Our first exact Lean formula for the class-common weight was
wrong. It read the layer of each skeleton child at the root of the regular object inserted there, and in a
Vine (II-a) one class member then carries the factor at k_{𝔲₂₃} and another at k_{𝔲₂}. The corrected skeleton-layer
form passed an independent mathematical review, in a build that failed our consistency check (rulings R135 and R143
in `docs/campaign/orch/RULINGS.md`). Our need for exact equality came from our formal interfaces, not from the
paper.

---

## E37 — TARGET L2294: a cutoff inside a spliced vine must enter the vine estimate's weight

**Status:** CONFIRMED, as an omitted routine extension: the independent assessment shows that such internal cutoffs fit
the Fourier-measure amplitude step of `sumint`
([`docs/research/astra-flowerest1-report.md`](research/astra-flowerest1-report.md), §3.2 and §4.2), and the fill passed
the independent referee of the supplement ([`docs/research/flowerest1/REFEREE.md`](research/flowerest1/REFEREE.md),
Lemmas 4.2 and 5.3: PASS). **Class:** EXPOSITION. **Main theorem:** repaired on paper (refereed). Found by the Lean work
(ruling R133).

**Location.**
- Adjustment (1) of the proof of `flowerest1` (L2294).
- Proposition `vineest` (L1742–L1752), which reduces to Proposition `sumint` (L1753; L1595–L1625).
- The Stage-1 reduction (Section 10).

**What is missing.**
- **How Stage 1 works.** It replaces each spliced vine by the bound of `vineest` for the sum over its twist class.
  The vine's internal momenta are summed inside that bound.
- **The problem.** A cutoff at a node strictly inside the vine is not a function of the data that survive. So it
  cannot be applied after Stage 1: it has to be part of the class sum.

**Configuration.**
- Take a Vine (II-a) with small nonzero gap 0 < |k_{𝔲₂₁} − k_{𝔲₂₂}| ≤ L^{−γ+η}, so that it is spliced.
- Decorations with k_{𝔲₂} near 0 and with |k_{𝔲₂}| ≥ 2M can have the same image in the spliced skeleton.
- A cutoff χ₀(|k_{𝔲₂}|/M) gives them weights 1 and 0.

**The fill.**
- **The mechanism exists.** Proposition `sumint` already bounds class sums carrying product weights in "alternative
  variables", linear forms in the summed variables, through their Fourier mass (L1623–L1625), after localizing with
  the decay of the inputs (L1621). The cutoff is a bounded smooth function of such a linear form.
- **What to do.** Include it in W at the cutoff's Fourier mass, which is independent of M, with moments that improve
  as M grows. Check that the vine's internal momenta are admissible variables there.
- **The paper's part.** It states `vineest` without such a weight and does not make this check.
- **Refereed fill.** Supplement Lemma 3.1 (Fourier-measure algebra: a product of O(n) cutoffs of linear forms has mass
  at most Cⁿ, independent of positions and coefficients), Lemma 4.2 (`sumint` with Fourier-measure weights in the
  alternative variables) and Lemma 5.3 (local weighted `vineest`), all PASS.

**Formalization note.** In our setting several cheaper routes did not work, for example moving per-frequency
characters to the leaves. The weighted class bound our architecture needed was scoped but not built.

---

## E38 — TARGET L2294/L2297 with `proplayer1`: a cutoff inside an incoherent regular object

**Status:** CONFIRMED, as an omitted routine extension: checked by the independent assessment
([`docs/research/astra-flowerest1-report.md`](research/astra-flowerest1-report.md), §3.2 and §4.2); the fill passed
the independent referee of the supplement after a proof-level fix
([`docs/research/flowerest1/REFEREE.md`](research/flowerest1/REFEREE.md), Lemma 4.1). **Class:** EXPOSITION. **Main
theorem:** repaired on paper (refereed). Found by the Lean work and a research pass (rulings R139, R142). The research
note is [`docs/research/internal-weights-notes.md`](research/internal-weights-notes.md); it uses the campaign's
internal vocabulary.

**Location.**
- Adjustments (1) and (4) of the proof of `flowerest1` (L2294, L2297).
- Proposition `proplayer1` (L953–L956) and its proof (L991–L1013).
- Definition `lftwist`, L1472 (every non-exceptional regular object is "the *same* regular tree … with the same
  layerings").

**What is missing.**
- **Which objects matter.** Only an *incoherent* regular object whose root's parent lies in layer p can carry the
  M₁ cutoff at an internal node. On a coherent object the cutoff reduces to a single factor at the object's external
  momentum (Proposition `layerreg1`). Below layer p there is no cutoff node.
- **What is needed.** Inside such an object, the cutoff reads the object's root momentum plus internal momenta, so
  Proposition `proplayer1` is needed with that factor.

**Configuration.**
- In a core Vine (II-a), let the interior branch 𝔲₄ carry a chain 𝔫₁ → 𝔫₂, with 𝔫₁ in layer p and 𝔫₂ in layer
  p − 1. The children 𝔠₁, 𝔠₂ of 𝔫₁ are lower-layer leaves, paired with children of 𝔫₂.
- The cutoff nodes 𝔫₂, 𝔠₁, 𝔠₂ carry k_{𝔲₄} plus internal link variables.
- Such rows lie inside twist classes (L1472), and can also occur outside every vine.

**The fill.**
- **The proof already has the mechanism.** The proof of `proplayer1` uses its weight W in (k, x, y) through its
  Fourier mass (L1007–L1013), after localizing with the decay of the inputs (L1002). The cutoff is a bounded smooth
  function of a linear form in the same variables, so the weighted estimate should follow at the cutoff's Fourier
  mass.
- **Plus a cost for root dependence.** That costs moments of the Fourier measure, because k-derivatives fall on the
  cutoff, as at L995. These must be tracked through E37's class sum.
- **The paper's part.** It does not state this.
- **Refereed fill.** Supplement Lemma 4.1 (frontier-weighted `proplayer1`). The referee required one proof-level fix
  for the tree half: the output supremum must stay inside the time-Fourier integral (norm (1.2) of the supplement), so
  the step uses TARGET's uniform-in-k argument at L1062–L1092 rather than a spatial Sobolev bound; the statement
  stands.

**State of our Lean attempt.** The weighted incoherent estimate was in progress and unfinished when Lean work stopped.
The weighted vine class bound that would consume it was only scoped.

---

## E39 — TARGET L2299: "otherwise these cutoffs play no role": the upper M₂ cutoffs can sit inside coherent regular trees on the stem

**Status:** CANDIDATE (upgraded from SUSPECTED; held at CANDIDATE because the gap claim rests on a single
independent assessment, not a refute-first referee check of this specific claim). The independent assessment
([`docs/research/astra-flowerest1-report.md`](research/astra-flowerest1-report.md), §2 (6), §3.5 and §3.6) finds that
the upper cutoffs left at the unselected stem nodes "cannot be deleted inside an oscillatory decoration sum merely
because their absolute values are at most one" and that inside regular stem chains they need a spectral argument.
**Class:** GAP. **Main theorem:** repaired on paper: Theorem 8.2′ of the o82 resolution, refereed (REFEREE-82: no FAIL;
Theorem 8.2′ PASS; its sufficiency PASS after a scope fix).
- Found by research and supported by the Lean analysis (rulings R142, R145).
- Repair: [`docs/research/flowerest1/o82-RESOLUTION.md`](research/flowerest1/o82-RESOLUTION.md) (§§10–11, 15, 18–19);
  referee report [`docs/research/flowerest1/REFEREE-82.md`](research/flowerest1/REFEREE-82.md).

**Location.** Adjustment (6) of the proof of `flowerest1` (L2299); see E35. Compare DH21 Corollary 11.3, case (a)
(DH21 L2703), and the partition at DH21 L2735.

**Quoted text (L2299).**

> if we insert the M₂ cutoff, then for each j we fix a branching node 𝔫_j ∈ 𝒮_j and insert the cutoff such that
> |Ω_{𝔫_j}| ∼₀ M₂ (otherwise these cutoffs play no role in the proof).

**What is missing.**
- **The leftover cutoffs.** The product partition for the M₂ cutoff (DH21 L2735) marks one stem node per tree and
  leaves smooth upper cutoffs χ₀(|Ω_𝔟|/2ʲL) at the other stem nodes.
- **Where one can sit.** A stem node can be a chain node of a coherent regular tree on the stem, whose resonance
  Ω_𝔟 = 2⟨x, y⟩ reads that tree's internal link variables.
- **Why Stage 1 cannot ignore it.** Stage 1 replaces coherent regular trees by their asymptotics (Propositions
  `proplayer2`–`proplayer4`), and here the weight sits inside the collapsed object, in one of its spectral variables.

**Where the other unselected filters sit** (for completeness; each needs its own short argument):
- inside regular objects on the stem: this entry;
- on the rungs of large-gap ladders of the spliced molecule: E44;
- at the top of a small-gap vine: there the resonance is affine, Ω_{𝔲₁} = 2r·(a − f) with r and f fixed by the vine
  estimate, so the filter is a smooth function of a linear form and enters `sumint` through its Fourier mass
  (assessment §4.3; supplement Lemma 9.3, PASS after a wording fix and one added sentence on twist invariance);
- in the residual molecule: only after the reduction to the absolute count (L2090–L2097), where a filter merely
  restricts a positive sum (supplement Lemma 9.4, PASS).

**Repair (refereed).** Theorem 8.2′ of the o82 resolution carries the filters in the spectral coordinates of the
regular object (DH23 L955–L1009), with a truncated principal value for an extracted denominator. Unprotected objects
keep their coherent leading term and lose no power of L; objects that carry a pin or a selected occurrence are kept
whole, at a cost L^{(47d+5)} per such incidence, with M₂^{−1/18} per selected occurrence and no incoherency gain lost.

**Fairness.** DH21 faces the same partition in its short-time setting (DH21 L2735). It treats the marked stem node when
it lies inside a regular couple or tree (case (a), DH21 L2703), and, like TARGET, it does not discuss the upper cutoffs
left at the other stem nodes. So this point is shared with DH21's argument.

**State of our Lean attempt.** A weighted coherent approximation was proved in a scratch build; it failed its first
independent review and passed a second after repair, in a build that had not passed our consistent-rebuild check. It is
not on main.

---

## E40 — TARGET `ladderl1new`, proof sketch L1989–L1991: the gap indicators and the last rung sum are not handled (G2, G3)

**Status:** CANDIDATE, as the independent referee recommends. Both items were checked by the referee of the o83
resolution and found to be genuine gaps in the printed sketch
([`docs/research/flowerest1/REFEREE-83.md`](research/flowerest1/REFEREE-83.md), §12), and the premise of G3 was also
checked by the referee of the o75 resolution
([`docs/research/flowerest1/REFEREE-2.md`](research/flowerest1/REFEREE-2.md), §3.2). The status stays CANDIDATE because
the indicator half of G2 is not shown to occur in TARGET's construction. **Class:** EXPOSITION. **Main theorem:** none;
`ladderl1new` is true as stated. Filled on paper (o83 Lemma R and Theorem K, refereed: PASS) and in Lean in the ladder
proof in this repository (`WaveTurbulence/Foundations/Spine/`: `RungTotal.lean`, `Kinds.lean`, `FibreSum.lean`).
- Found by the o83 resolution ([`docs/research/flowerest1/o83-RESOLUTION.md`](research/flowerest1/o83-RESOLUTION.md),
  §§4.2–4.4). Related: E4 (the same indicator issue in `vineest`) and E5 (the ladder kernel core).

**Location.** Prop `ladderl1new` (T1978–T1988) and its proof sketch (T1989–T1991).

**Quoted text.**

> We also replace ε̃_{𝒪_sb} and 𝒵_{𝒪_sb} by the product of ε_v and 𝒵_v (defined above) over all v ∈ 𝕃. (T1981)

> Recall that in Step 2 of the proof of Proposition [sumint] we estimated each quantity ℳ_j^i pointwise, leading to the
> final L^∞ bound of ℐ. Here we can do exactly the same thing, […] In the end we are left with the last remaining sum,
> which is taken over the decoration of the last double bond in the ladder, and can be bounded trivially by L^{2d}.
> (T1991)

**G2: the indicators ε_v and 𝒵_v.** The ladder kernel carries ∏_{v∈𝕃} ε_v𝒵_v (T1981). The sketch says to do "exactly the
same thing" as Step 2 of `sumint`, whose weights are smooth with 𝔖^{30d,30d} bounds; ε_v and the gap indicators 𝒵_v are
sharp indicators, not such weights, and the sketch does not mention them.
- The ε half is routine: the mass-one character mixture of E4, or a per-rung count once the rungs factor.
- The 𝒵 half needs a real argument if a ball indicator constrains an internal opposite pair of an incoherent interior
  rung: the trivial count then fails, for example for d = 3 and 1/2 < γ < 4/5 (o83 Lemma R, Step 2(a)). In TARGET, 𝒵
  records the SG/LG/ZG type of collected objects at a joint (T1938–T1944, T1970), and the referee does not see a joint
  occurring as an interior ladder atom. So this half is needed for the general weight class, but its occurrence in
  TARGET's construction is not established.

**G3: the last rung sum.** The sketch introduces (x_j, y_j)_{1≤j≤m} plus the last double bond, 2m+2 vector variables,
but a ladder with its four boundary momenta fixed has only 2m+1 free vectors. One d-dimensional conservation law
couples the rungs, so the rung-by-rung factorization of `sumint` Step 2 does not apply literally, and the last sum is
not independent of the others. Fixing only one end double bond does not cure this: the far end rung then depends on
Σλ_j.
- **Fill:** fix both end double bonds (cost L^{4d}, within the L^{20d} of (redladder2)) and resolve the single remaining
  constraint by a mass-one character average (o83 Theorem K, step 4). The Lean proof uses the same chart, with the flux
  identity `flux_eq` in `Spine/FibreSum.lean`.
- **Sub-item.** T1989's formula Γ_w = −2x_j·y_j + 2r·ζ_j is claimed for every rung; at an end rung containing a
  degree-3 atom it can fail (compare minor item m24). This is harmless once the end rungs are only counted.

**Also proved there (E5′).** o83 Theorem K proves the unordered kernel-core bound of E5 for every product of unit time
intervals, not only the layer box; this translated-box form is what the upper-filter argument of E44 needs.

---

## E41 — TARGET (jtflower), (kqflower), L2264–L2265 (and DH23 L1995–L1996): the prefactor (δ/(2L^{d−1}))ⁿ should be (δ/(2L^{d−γ}))ⁿ

**Status:** CONFIRMED: by the independent referee of the supplement
([`docs/research/flowerest1/REFEREE.md`](research/flowerest1/REFEREE.md), §1: "Accept as an erratum") and,
independently, by the independent assessment
([`docs/research/astra-flowerest1-report.md`](research/astra-flowerest1-report.md), §1). **Class:** ERROR (a
normalization typo, but not a harmless one: read literally it changes the kernels by a factor that the estimate cannot
absorb). Formerly minor item m28. **Main theorem:** none once corrected; the frozen flower statement and the refereed
completion use d − γ.
- Ledger: F25. Supplement: [`docs/research/flowerest1/SUPPLEMENT-v2.md`](research/flowerest1/SUPPLEMENT-v2.md), §1
  ("Normalization convention") and §12.

**Quoted text.**

> 𝒥̃_𝒯(t,s,k,k′) = (δ/(2L^{d−1}))ⁿ ζ(𝒯) Σ_𝒟 ε_𝒟 ∫_𝒟 ∏_{𝔫∈𝒩} e^{ζ_𝔫πi·δL^{2γ}Ω_𝔫t_𝔫} dt_𝔫 · δ(t_{𝔣ᵖʳ} − s) ∏_{𝔣≠𝔩∈ℒ} a_{k_𝔩}(p)
> (T2264; (kqflower) at T2265 has the same prefactor)

> (𝒥_𝒯)_k(t) = (δ/(2L^{d−γ}))ⁿ ζ(𝒯) Σ_𝒟 ε_𝒟 ∫_𝒟 ∏_{𝔫∈𝒩} e^{πiζ_𝔫·δL^{2γ}Ω_𝔫t_𝔫} dt_𝔫 · ∏_{𝔩∈ℒ} a_{k_𝔩}(p)  (T712)

**What is wrong.** Everywhere else TARGET uses δ/(2L^{d−γ}) per branching node (T671, T712 and 23 further displays,
for example the ladder normalization T1980). The operator ℒ₁ (T725) is built from the trees of T712, and the proof of
`flowerest1` says to "follow the arguments in Section [secduhamel]" (T2287). For order n the printed prefactor exceeds
the intended one by L^{(1−γ)n}, which is not an L^{O(P)} factor uniformly in the allowed orders n ≤ N_{p+1}⁴; so the
printed kernels do not satisfy the estimate the proof gives. With lower-layer insertions, the moment expansion
(flowerexp2) at T2288 would even mix the two normalizations, d − 1 at top-layer nodes and d − γ at inserted ones, if
both definitions were read literally (assessment §1).

**Origin and fix.** The flower formulas are copied from DH21 (11.2)–(11.3) (DH21 L2663, L2671), where γ = 1 and d − 1,
δL²Ω are correct. DH23 L1995–L1996 copies them with both the prefactor d − 1 and the phase δL²Ω, while DH23 elsewhere
uses d − γ and δL^{2γ}Ω (for example (defjt), DH23 L468). Read d − γ, and in DH23 also L^{2γ} in the phase.

---

## E42 — TARGET (operatorxker), L2270–L2273, with (jtflower), L2264: the order-zero flower tree must be read as the identity operator

**Status:** a reading, not a claim that a printed statement is false. The independent referee of the supplement
checked that it is necessary ([`docs/research/flowerest1/REFEREE.md`](research/flowerest1/REFEREE.md), §1: "the only
meaningful pointwise reading … a statement-level reinterpretation"); the independent assessment makes the same
observation ([`docs/research/astra-flowerest1-report.md`](research/astra-flowerest1-report.md), §1). **Class:**
DEVIATION (a reading of the statement; see the Deviations, C). **Main theorem:** none.
- Ledger: F39. Supplement: [`docs/research/flowerest1/SUPPLEMENT-v2.md`](research/flowerest1/SUPPLEMENT-v2.md), §1
  ("Order-zero convention").

**Quoted text.**

> where the summation is taken over all flower trees 𝒯 of order ≤ N_{p+1} such that ζ_𝔯 = + and ζ_𝔣 = ζ for the root 𝔯
> and flower 𝔣. (T2271)

> Let 𝒴 = (1 − ℒ₁)𝒳 − 1 and 𝒲 = 𝒳(1 − ℒ₁) − 1. (T2273)

> By adding up all n ≥ 0 for 𝒳 (T2304)

**The issue.** The sum includes the trivial flower tree (root = flower, order 0). For it, (jtflower) contains
δ(t_{𝔣ᵖʳ} − s), but there is no flower parent. For 𝒴 = (1 − ℒ₁)𝒳 − 1 to have the stated tree expansion, its
contribution must be the identity: 𝒳 = I + 𝒳_reg, with formal kernel 1_{k=k′}δ(t − s), in the channel ζ = + only (for
a trivial tree ζ_𝔣 = ζ_𝔯 = +). A pointwise bound on the 2P-th moment, (flowerest2), cannot apply to that distribution.

**Reading adopted.** (flowerest2) and its cutoff variants bound the regular kernel 𝒳_reg on p < s < t < p+1; 𝒴 and 𝒲 are
defined with the operator 𝒳 = I + 𝒳_reg. The parametrix identities (1 − ℒ₁)𝒳 = 1 + 𝒴 and 𝒳(1 − ℒ₁) = 1 + 𝒲 hold in this
reading, and the identity part of 𝒳 is bounded trivially. The frozen statement reads it so (its kind 𝒳 excludes the
trivial flower tree), the derivation of `fixedpoint_v2` from the flower estimate and `layergarden_v2`, built on that
reading, is checked in Lean (`V2Chain.fixedpoint_v2_of_closed_gates_v3`), and the supplement states its target this way.

---

## E43 — TARGET L2295, L2297, L2299: the intermediate L-loss figures of the flower adjustments are not established by the arguments given

**Status:** CANDIDATE. The point about L2297 was made by the supplement's statement of its open item 7.5
([`docs/research/flowerest1/SUPPLEMENT-v1.md`](research/flowerest1/SUPPLEMENT-v1.md)) and independently by the
independent assessment ([`docs/research/astra-flowerest1-report.md`](research/astra-flowerest1-report.md), §2 (4));
no referee has given a verdict on the printed figures, and the L2297 point depends on a reading (below). **Class:**
MINOR. Any fixed power L^{O(dP)} suffices, and the completion pays larger fixed powers, all within the final allowance
L^{(100d)³P}. **Main theorem:** none.

**Quoted text.**

> In any case the total loss is ≤ L^{200dP} for the total of 2P trees. (L2295)

> (there are at most 20 such variables per vine). This leads to a loss of at most L^{20d} per vine, and at most
> L^{400dP} in total. (L2297)

> All the possible loss (such as those described in (2)) that may come along the way again add up to at most L^{100dP}
> which is acceptable. (L2299)

**What is wrong.**
- **L2297.** The ladder bound that L2297 invokes already carries L^{20d} per ladder (redladder2, T1986), and a vine has
  up to three ladders plus fewer than 20 extra atoms (T1519); the trivial estimate of (finalsbest1) charges L^{20d} per
  atom outside ladders (T2082). So "L^{20d} per vine" is not the sum of the quoted bounds. *Reading caveat:* if the
  vine's ladders are counted among the maximal ladders of the spliced molecule, already charged in (finalsbest1), the
  figure may be meant for the at most 20 extra variables only; under that reading it is plausible.
- **L2295, L2299.** The completed arguments do not give these totals: the pin and face estimate (E30, E35) costs
  L^{400d} per protected incidence, up to L^{10400dP}, and the exceptional pieces (E31) cost L^{(360d+16)b} ≤
  L^{(9360d+416)P}.

**Why it is harmless.** There are fewer than 20P exceptional vines and O(P) pins, and the statement allows L^{(100d)³P}.
The supplement's total budget fits this allowance (its §10).

---

## E44 — TARGET L2299 with (finalsbest1), L2081: the upper M₂ filters on the rungs of large-gap ladders do not "play no role"

**Status:** CONFIRMED. Found by the independent referee of the supplement
([`docs/research/flowerest1/REFEREE.md`](research/flowerest1/REFEREE.md), §4.2, item M2: "a genuine gap, not covered
by any listed item"); independently, the assessment shows that the unselected upper filters cannot be dropped inside
oscillatory sums ([`docs/research/astra-flowerest1-report.md`](research/astra-flowerest1-report.md), §2 (6)). The
repair and the case analysis of where filters sit were refereed
([`docs/research/flowerest1/REFEREE-83.md`](research/flowerest1/REFEREE-83.md), §§8–10, 13; REFEREE-2 §3.2).
**Class:** GAP. **Main theorem:** repaired on paper: Theorem 8.3 of the o83 resolution, refereed (PASS).
- Repair: [`docs/research/flowerest1/o83-RESOLUTION.md`](research/flowerest1/o83-RESOLUTION.md) (Theorem 8.3,
  Theorem K, Corollary 8.3.A). The o75 resolution's Lemma F covers the same ground, conditional on Theorem K.

**Quoted text.**

> (otherwise these cutoffs play no role in the proof). (L2299)

> For each new ladder 𝕃, we apply Proposition [ladderl1new], noting that the function 𝒦†(k[𝕎]) does not depend on any
> of the k_ℓ variables for ℓ ∈ 𝕃 (L2081)

**Configuration.** If the stem leaves a block adjacent to a small-gap vine through 𝔲₂₁ or 𝔲₂₂, the separation
|k_𝔫 − k_{𝔫′}| ≥ |k|/2 between stem and off-stem nodes (L2300) forces the block's gap to be large: the block is LG and
its interior is on the stem, the parent chain passing through every rung group (T1519). Only SG chains are spliced, so
these LG ladders survive among the maximal ladders of the spliced molecule and carry upper filters χ(Γ_v/M₂) at stem
atoms. A filter of Γ_v = 2x_j·y_j or −2x_j·y_j + 2r·ζ_j (T1989) is a genuinely quadratic amplitude on two bonds, which
violates the hypothesis used at L2081, and `ladderl1new` is an oscillatory rung-sum estimate. The stem can cross
unboundedly many LG ladders, so a loss per filter is not affordable, and (finalsbest1) cannot be skipped: its
interpolation with (finalsbest2) supplies the δ- and g-gains (T2079, T2220–T2225).

**Repair (refereed).** Fourier-invert each filter. For a filter at dyadic scale R it becomes a translation of the rung
time variable by O(ξ/(δL^{2γ}R)) inside the rung phase, plus a linear modulation; in the unordered kernel core of E5
only the unit time box moves. Theorem K (E40) bounds that core for every product of unit intervals, so each filter costs
a constant 𝔟(ψ), independent of L and δ, with no loss of incoherency gains and no use of the L-power budget.

---

## E45 — TARGET L2327–L2331 (proof of `fixedpoint`): the dagger and derivative variants of the flower estimate are not covered by "the same way"

**Status:** CANDIDATE. Found by the independent referee of the supplement
([`docs/research/flowerest1/REFEREE.md`](research/flowerest1/REFEREE.md), §4.2, item M4); the face estimates the repair
uses passed the referee of the o73 resolution
([`docs/research/flowerest1/REFEREE-73.md`](research/flowerest1/REFEREE-73.md), rows 7–9: PASS AFTER FIX), but no
referee has given a verdict on the assembling theorem (o104 Theorem 10.4) or on its revision. **Class:** GAP: it
inherits E30 and E31, and adds a pinned node that L2297 does not protect. **Main theorem:** repaired on paper (o104
Theorem 10.4), partly refereed.
- Repair: [`docs/research/flowerest1/o104-RESOLUTION.md`](research/flowerest1/o104-RESOLUTION.md) (Theorem 10.4,
  Lemmas 3.1–3.3, 6.1–6.3, Props 7.2–7.4).

**Quoted text.**

> here the ∂_t derivative introduces an extra δ(t_𝔯−t) factor, while the ∂_s derivative introduces an extra δ(t_𝔫−s)
> factor with 𝔫 being the parent or a non-flower child of 𝔣ᵖʳ, and all these factors can be treated just as the one in
> (jtflower) (L2331)

> the root 𝔯_j, any of the children nodes of 𝔯_j, the flower 𝔣_j, the parent and any sibling node of 𝔣_j (L2297, the
> "special nodes")

**What is missing.**
- **An unprotected pinned node.** For the ∂_s term with 𝔫 the parent of 𝔣ᵖʳ, the new pin sits at the flower's
  grandparent, which is not among L2297's special nodes; so the paper's protection of the truncation data against LF
  twists does not cover it.
- **Coincident pins.** The new pin and the flower-parent pin both sit at time s. This creates a lower face at the
  grandparent and an off-stem pinned child face, which neither adjustment (2) nor adjustment (6) treats, and both
  inherit E30's problem with the time trace.
- (A harmless overcount: only branching children in layer p contribute to "non-flower child".)

**Repair (on paper).** Theorem 10.4 of the o104 resolution: each derivative pattern adds exactly one time pin per tree;
the root pin is the top face of the exact time-integration identity (supplement Lemma 9.1), the grandparent pin a lower
face, and the child pin an individual child face, all estimated by o73 Theorem 7.3′ (its Proposition 19.2); the
grandparent is added to the protected set (at most 30P vertices). The dagger kernel 𝒥† of L2327 fixes the sibling
momenta and leaves a unimodular phase on at most 3^{2P} classes, at no L-cost. The cost fits the extra L^{(100d)³P}
that L2331 allows, and the M₂ gain is kept when all patterns are plain.

---

## E46 — TARGET L2290: the expansion remainders are not shown to carry the cutoff gains

**Status:** CANDIDATE. Found by the independent referee of the supplement
([`docs/research/flowerest1/REFEREE.md`](research/flowerest1/REFEREE.md), §4.1, OPEN 10.2: "a weighted argument
really is required"); the fill passed the referee of the o102 resolution
([`docs/research/flowerest1/REFEREE-2.md`](research/flowerest1/REFEREE-2.md), §2: Theorem R PASS). **Class:**
EXPOSITION. **Main theorem:** repaired on paper (refereed).
- Fill: [`docs/research/flowerest1/o102-RESOLUTION.md`](research/flowerest1/o102-RESOLUTION.md) (Theorem R).

**Quoted text (L2290).**

> We may treat ℰ^{(1)} just as in the proof of Proposition [propansatz] in Section [proofmain]; moreover, if the order
> of 𝒢 is n(𝒢) > N_{p+1}⁴, then the resulting term ℰ^{(2)} can also be treated just as in the proof of Proposition
> [propansatz].

**What is missing.** The bounds that L2290 points to (T803–T807) carry no factor M₂^{−P/9}, and M₂ is not bounded by
any power of L; nor do they show the factors M₁^{−80dP} and ⟨k − ζk′⟩^{−4Λ_{p+1}P}. So the cutoff variants of
(flowerest2) need a weighted bound on the remainders.

**Fill (routine).** Absolute bounds suffice: M₁ and the external decay are extracted pointwise from the inductive decay
of the inputs; M₂ comes from integrating one stem time exactly at each fixed decoration, |∫e^{iωu}du| ≤ 2/|ω|; the
e^{O(N²)} losses are paid by e^{−N_p} or by 2^{−N⁴/2} (o102 Theorem R; no use of the L-power budget).

---
