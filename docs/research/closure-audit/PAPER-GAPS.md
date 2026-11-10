> **Note for readers.** This is the verbatim working report of an independent, read-only audit run on 2026-11-07, when development stopped. It uses the campaign's internal work-package names (FC23, C2-E-B, S2-ST, V5, …) and ruling numbers (R…). Paths under `<scratch>/`, `<repo>/` and `<worktrees>/` refer to working directories that are not included. The formalization report it was prepared for has not been published (decisions D14, D15).

# PAPER-GAPS — where the formal proof could not follow Deng–Hani, arXiv:2311.10082v2

Auditor: O-CLOSURE-MAP (Opus), 2026-11-07, read-only. Status: **draft 2 (complete)**.

- TARGET = `<sources>/paper/source/WKE-Longer_times_Final_arXiv.tex`, sha256 `493eef6b…727cb`
  (re-hashed in this audit; it matches the manifest pin). All line numbers are TARGET lines unless prefixed DH21/DH23.
- Every quotation below of TARGET was re-read in the TeX in this audit (L1464–L1484, L1903–L1909, L2063–L2067,
  L2240–L2338).
- Campaign sources (snapshotted with sha256 in `closure-map/snap/`): `docs/ERRATA-AND-DEVIATIONS.md` (E1–E35, on
  origin/main), `docs/FINDINGS.md` (F1–F82), `RULINGS.md` R1–R145, the packet handoffs, `research-internal/NOTES.md`.

## Classification used

- **(a) mathematical error**: a claim false as printed; a counterexample or configuration is given.
- **(b) gap**: a step whose justification is not given and whose repair is not obvious.
- **(c) exposition gap**: a step omitted but routinely fillable; the fill is described.
- **(d) formalization difficulty**: not a defect of the paper.

Evidence levels: **LEAN** (a Lean theorem or Lean-checked configuration exists), **WORKED** (an explicit
configuration or computation written out and independently re-derived by a second agent), **CAMPAIGN** (written by
one agent, not independently checked), **SUSPECTED** (an argument that something is missing, with no configuration
checked end to end). I did not re-run any campaign script or Lean check; where I say LEAN I am relying on the cited
artifact's own recorded check, and I say so.

---

## 0. Verdict on the paper, in one paragraph

**No counterexample has been found to any result that TARGET's main theorem needs for 1/2 < γ < 1, and none to the
main theorem for any γ.** The one confirmed mathematical error with real consequences is in a cited paper: DH23
Prop 9.6 (`lgmolect`) case (4) is false for 0 < γ ≤ 1/2 (E1; explicit "necklace" counterexample, mechanically checked
and independently refereed), and TARGET reuses it at L2192–L2197. That breaks TARGET's *proof* for γ ≤ 1/2 at an
intermediate proposition; it does not refute TARGET's theorem, and a repair route has been refereed three times but
not formalized. Separately, the **flower estimate (Prop `flowerest1`, L2279–L2305) is not proved at the level of
detail a formal proof needs.** Its printed proof is a list of seven "minor adjustments" to the ~1000-line proof of
`layergarden` (L2292: "most of the proof is completely analogous"). The formalization found that at least six of those
adjustments need constructions or estimates the paper does not give: a skeleton for flower gardens, a fixed-time trace,
a modified splicing rule, a product partition of the cutoffs, an extraction of the M₁ gain from cutoffs at internal
nodes, and — the item the campaign was working on when it was stopped — **the cutoff functions survive as smooth weights at momenta internal
to vine twist classes, to incoherent regular objects, and to regular objects on the stem, where TARGET's vine
estimate (`vineest`) and incoherent-decay estimate (`proplayer1`) are stated and proved only without weights.** We
classify these as **gaps (b)**, not errors: in each case a repair route has been designed and refute-checked, and
several have independent referee reports, but no complete formal proof of `flowerest1` exists, so none of the
repairs is verified end to end. A list of smaller local errors (a) and exposition gaps (c) elsewhere in the counting
chain is in §2; all of them were repaired in Lean or are harmless.

---

## 1. The flower estimate (Prop `flowerest1`, L2279–L2305, and its uses L2312, L2320–L2331)

### 1.0 What the paper prints

L2279–L2285 state (flowerest2) for 2P-th moments of the parametrix kernel 𝒳, plus two cutoff variants: an extra
`M₁^{−80dP}` under a smooth cutoff `max{|k_ℓ| : ℓ ≠ 𝔣} ∼₀ M₁` over the non-flower leaves of the flower tree (L2283),
and an extra `M₂^{−P/9}` under `max_{𝔫 ∈ 𝒮} |Ω_𝔫| ∼₀ M₂` over the stem nodes other than 𝔣ᵖʳ (L2285).

The whole proof is L2287–L2305. After the moment expansion (L2288) it says:

> L2292: "Now, to estimate (flowerexp2), we simply repeat the arguments in Sections layerobject1–redcount devoted to
> the proof of Proposition layergarden. Below we only discuss the necessary (minor) adjustments needed in the flower
> garden case here, as most of the proof is completely analogous."

It then lists adjustments (1)–(7), L2294–L2300. Those sections (layerobject1–redcount) are the regular-object
asymptotics, the incoherent decay `proplayer1`, the vine estimate `vineest`, the Stage-1 reduction and the final
counting: essentially L845–L2255.

**Our position.** For an expert reader this is a reasonable sketch of a known pattern (DH21 §11–12 and DH23 §11 do the
same for shorter times). It is not a proof at the level we formalize. Below are the places where the "analogous"
argument does not go through as written, in order of the paper's items.

### 1.1 Flower gardens are not plain gardens: no skeleton or LF twist is defined for them — (b)

- **Printed.** L2259 footnote: "We may also pair the flowers … to make 𝒢 a genuine garden, as was done in [DH23], but
  this is not necessary in the proof below." L2261: canonical layered flower gardens are defined "in the same way as in
  Definition defcanon (but without any assumption about irreducibility of 𝒢)". L2287: "so we will make no
  irreducibility assumption about flower gardens."
- **What is missing.** The skeleton (Prop `propstructure2`), the molecule, vines and LF twists (Def `lftwist`, L1466)
  are defined for plain, irreducible gardens. Flower gardens have unpaired, marked leaves and may be reducible. The
  paper never says how the Stage-1 machinery is applied to them. The footnote's pairing does not help: pairing two
  flowers can produce a regular (1,1) mini-couple whose regular reduction has a zero-order skeleton, and it does not
  carry the fixed-time Dirac mark (E29, two-corolla configuration).
- **Why a formal proof needs it.** Every later step (vines, twist classes, `vineest`) is a statement about skeletons of
  plain canonical objects.
- **Status.** E29, CANDIDATE; the configuration's elementary identities are LEAN (FLOWER-S1), and an independent
  flower referee reviewed it (research-flower-referee, items 1–5, 8). **Repair (R61 "design C"):** excise the flower
  parents as pendant fixed-time stubs, replace the detached slots by leaves paired to fresh trivial "anchor" trees with
  fixed labels, decompose into irreducible plain anchored components, and use their ordinary skeletons and LF twists.
  The excision identity is proved in Lean (FLOWER-P1 `flowerSum_eq_excision`; FC23/C2-E-B component formulas). The
  full transport through Stage 1 is not complete.
- **Classification: (b).** The repair is a new construction, not a routine fill; the paper's own suggestion (the
  footnote) is not it.

### 1.2 The Dirac factor δ(t_{𝔣ᵖʳ} − s) changes the time domain, not only a phase — (b), leaning (c)

- **Printed.** L2295: "They may also come from the δ(t_{𝔣ᵖʳ}−s) factor which removes the integration in the t_{𝔣ᵖʳ}
  variable, but Ω_{𝔣ᵖʳ} has at most L^{10d} possible values once we fix each k_ℓ to a unit ball, so we may fix the value
  of Ω_{𝔣ᵖʳ} and safely get rid of the factor e^{…Ω_𝔫 t_𝔫} for 𝔫 = 𝔣ᵖʳ at a loss of at most L^{10d}."
- **What is missing.** The counting claim is fine. But fixing Ω_{𝔣ᵖʳ} removes a phase; it does not restore the
  integration over t_{𝔣ᵖʳ}. A fixed node imposes caps τ_child < s and a floor τ_parent > s on its neighbours, and if
  𝔣ᵖʳ sits inside a regular tree the factor is a trace of an ordered chain integral, not the ordinary
  all-times-integrated regular-object kernel. The Stage-2 bounds must be proved on that altered domain.
- **Why a formal proof needs it.** The vine and regular-object estimates are norms of time-integrated kernels; a
  pointwise-in-one-time trace of such a norm is a separate statement. (A norm-only trace is false for arbitrary
  functions — R68's Lean `TraceCounterexample` — so the trace must use continuity of the actual kernels; that part is
  category (d).)
- **Status.** E30, CANDIDATE; time identities LEAN (`corolla_plain_timeIntegral`), referee-checked. Repair: the
  excised 𝔣ᵖʳ is a pendant stub (degree ≤ 1), so it lies in no vine or ladder; use a trace of the V5 norm for
  continuous kernels (X7, proved for continuous functions). Done in scratch, not on main.
- **Classification: (b)**, though close to (c): the fill (fixed-node trace) is the natural one, but the paper's stated
  reason ("fix Ω") does not address it.

### 1.3 Leaving special-node vines unspliced invalidates `subpro` (4) — (b)

- **Printed.** L2297 (4): "Clearly there are less than 20P vines containing one of these special nodes; for each of
  them we can use Proposition ladderl1new to treat its ladder parts, and sum and integrate trivially … This leads to a
  loss of at most L^{20d} per vine."
- **What is missing.** Prop `subpro` (4) (L2045) is a conclusion about the *ordinary* splicing selection ("any SG
  vine-like object … not contain[ing] a hinge atom must be a subset of a DV or an LG or ZG vine-like object"). Leaving
  some SG vines unspliced produces exactly the excluded alternative, so the modified algorithm cannot quote `subpro`
  (4) unchanged; paying L^{20d} per vine does not restore the structural premise the counting needs.
- **Status.** E31, CANDIDATE; configuration written (a maximal non-root SG CL vine whose upper joint is a child of a
  flower-tree root), referee item 8 confirms the gap; no full prime flower garden enumerated. Repair: design C's
  excision makes the special nodes pendant stubs, so no vine needs an exception.
- **Classification: (b).**

### 1.4 The root-time derivative ∂ₜa^tr (L2312) — (c), repair VERIFIED in Lean (conditionally)

- **Printed.** L2312: "we can treat the time derivative ∂ₜa_k^tr (which simply contains an extra δ(t_𝔯−t) factor …)
  using the same arguments in the proof of Proposition flowerest1, to get the same bound (trterm1) with an additional
  L^{100d} loss."
- **What is missing.** Pinning the root time is a root excision: the three child subtrees become trees capped at t
  (a width-six garden for a differentiated couple). The decapitated pieces include irreducible width-four components
  that are not couples (referee's configuration, E32), so "only regular couples remain" is false and Stage 1 is still
  needed. A structure lemma the campaign first proposed for this (R61 X6) was itself false (R69); not a paper issue.
- **Status.** E32, CANDIDATE, referee-corrected. **The repair is carried out in Lean:** the exact decapitation identity
  `kernelKgen_cap` and the total couple clause `FlowerP7.coupleSum_total_bound`, consumed by flower-top as the couple
  half of `layergardenFlower_v3` (proved, conditional only on the same Stage-1 gate that `layergarden` needs).
- **Classification: (c)** — routine once the root excision is written down; the fill is described and done.

### 1.5 The cutoffs: "smooth cutoff of a maximum" needs DH21's product partition — (c) for the partition; our max-form was (d)

- **Printed.** L2283, L2285: "Suppose we restrict to max{|k_ℓ|} ∼₀ M₁ … by a smooth cutoff function"; L2299: "for each
  j we fix a branching node 𝔫_j ∈ 𝒮_j and insert the cutoff such that |Ω_{𝔫_j}| ∼₀ M₂ (otherwise these cutoffs play
  no role in the proof)."
- **What is missing.** A smooth function of a maximum is not smooth; the intended object is DH21's per-variable dyadic
  partition grouped by the largest scale (DH21 L2731/L2735): Ψⱼ = ∏ₐ χ₀(yₐ/2ʲL) − ∏ₐ χ₀(yₐ/2ʲ⁻¹L). Telescoping marks
  one annular factor and leaves *upper cutoffs at all the other slots*.
- **Status.** E33 (CANDIDATE, referee item 8). Our first frozen statement used a scalar cutoff of the maximum; that was
  our transcription error, not the paper's (E34, DEVIATION; LEAN `frozen_ne_product` shows the two weights differ) and
  was fixed by the versioned successor `layergardenFlower_v3` (ruling D13).
- **Classification: (c)** for the partition itself (DH21 already has it). **(d)** for E34. But the consequence — the
  other cutoffs are still present as weights — is not "no role", see 1.7–1.8.

### 1.6 The M₁ gain "comes in the same way" — the cut leaves can be internal nodes — (b)

- **Printed.** L2294 (1): "The extra factor M₁^{−80dP} when assuming max{|k_ℓ| : 𝔣_j ≠ ℓ ∈ ℒ_j} ∼₀ M₁ comes in the
  same way (note that if we insert some cutoff to the tree 𝒯 associated to 𝒳, then the same cutoff will appear in each
  tree 𝒯_j occurring in the garden 𝒢 associated with the expansion (flowerexp2))." "The same way" refers to the decay
  factor, obtained "by the same arguments as in Section redcount0", i.e. L2065.
- **What is missing.** In the layered setting the leaves of the initial layer-p flower tree are replaced, in groups
  of ≥ 4, by lower-layer gardens (L2261). A leaf carrying the cutoff can therefore be the *root of an attached garden*,
  an internal node whose momentum is a signed sum of descendant input momenta. The M₁ gain must come from the input
  decay at some actual input leaf, and which leaf depends on the decoration. L2065's device ("for some leaf ℓ_j …
  include the extra factor … to the input function") is a pointwise choice inside oscillatory sums, which is exactly
  what E24 shows is not legitimate (it breaks the twist-class cancellation of `vineest`).
- **Why a formal proof needs it.** A cutoff at an internal node is a weight on a bond, not a modified input function.
  An unweighted bound on a smaller oscillatory sum does not bound a weighted one: 1 + (−1) = 0, but weighting the two
  terms by (1, 0) gives 1 (E33).
- **Status.** E33 (cut1 part), CANDIDATE, WORKED. Repair (FC2/FC3): extract a marked decaying input by an exact
  uniform-family/Markov identity with per-bond weights, preserving real, twist-compatible families. The plain clause
  is then the M → ∞ limit of that family (proved in Lean, flower-top `plain_of_family`). The family estimate itself
  (`FC23UniformCut1At`) is **not proved**: it is the largest open leaf of the campaign.
- **Classification: (b).** No counterexample; the statement is very plausibly true; but the argument is genuinely
  absent, and it is specific to the layered (long-time) setting — in DH21 the cutoff leaves are input leaves.

### 1.7 The cutoffs remain as weights inside vine twist classes and inside incoherent regular objects — (b)

This is what the campaign was working on when it was stopped (rulings R130–R145, 2026-11-07).

- **Printed.** L2294 (above); L2297 (4) "if the realization of a vine 𝕍 in 𝒢_sk does not contain any of the 'special
  nodes' … then any LF twist at this vine will not affect the property of belonging to ℋ^tr_{p+1}"; L2300 (7) for the
  stem only. Nothing is said about the M₁ cutoff weights inside vines away from the stem, or inside regular objects.
- **What is missing, part 1 — vine classes.** `vineest`'s gain is a cancellation over an LF-twist class with
  *identical inputs*: L1907 "Thanks to (layerregest10), this is exactly zero after summing over all (𝒬,𝒯) ∈ 𝔅". If a
  smooth cutoff multiplies the integrand at a momentum inside the vine region, the cancellation survives only if the
  weight is the same function for every member of the class. The paper never states this, nor that `vineest` holds
  with such a weight.
  - Configuration (R132, CAMPAIGN, from FC23 session 9): a core Vine (II-a) under an off-stem layer-p node u₁, with u₃,
    u₄ in layer p and the bottom joint u₂ rooting a layer-(p−1) tree; the cutoffs χ₀(‖k_{u₂}‖/M_T) at u₄ and
    χ₀(‖k_{u₀}‖/M_T) at u₃ read an internal loop momentum.
  - It is true that the weight is class-common **when read at skeleton (core) layers** (R132, R135, from Def `lftwist`
    L1472 and Remark `sublayer` L1464). It is **false** when read at the layers of the actual nodes: R135 gives a
    configuration (Vine II-a; member 1 has a coherent two-node chain T(u₂) in layer p, giving χ₀ at k_{u₂₃}; member 2
    puts the factor at k_{u₂}) where the naive node-level reading differs between members. research-internal §3 A-1
    adds that weights must be lower-layer-blind (`topPsi p g`), else the exact zero at L1907 breaks. **The paper's
    actual cutoff is blind and skeleton-common**, so this is not an error in the paper — but it shows the omitted
    argument is not a triviality.
- **What is missing, part 2 — incoherent regular objects.** Def `lftwist` L1472 keeps every non-exceptional regular
  object "the *same* … with the same layerings", so incoherent regular objects sit inside V5 classes and elsewhere in
  𝒢_sb. A top cutoff can sit at a node inside such an object (research-internal §2: a dominant chain n₁ (layer p) →
  n₂ (layer p−1) inside T(u₄), with lower-layer leaf children c₁, c₂ of n₁; the top nodes n₂, c₁, c₂ carry momenta
  k_{u₄} plus internal link variables). Then the incoherent-decay estimate `proplayer1` is needed *with that weight*.
  TARGET proves `proplayer1` with a weight W (L991–L1012) whose Fourier step only needs a finite Fourier L¹ norm, which
  strongly suggests the weighted version holds (research-internal §3 A-2) — but the paper never says the M₁ cutoff
  enters there, and `vineest`'s proof uses only unweighted row bounds.
- **Why a formal proof needs it.** Without it, either the weight is dropped (not allowed in a signed sum, see 1.6) or
  `vineest` and `proplayer1` must be re-proved with weights. The campaign tried five cheaper routes and refuted each
  (research-internal §3 B–D: per-character expansion is not class-common; the configurations do occur; trivial
  treatment of affected vines loses O(N) vines' gains; Taylor splitting needs the weighted estimate anyway; moving the
  cutoff changes the statement).
- **Status.** WORKED configurations (two independent Opus passes: FC23 sessions 9–11 and research-internal, plus
  V5-SPACE-EXT's refutation in R135); probe *statements* compile against main (`TopRowStatements.lean`,
  `V5TopStatement.lean`), but **none of the three needed weighted estimates is proved** (`TopIncoherentDecayGate`,
  `V5TopClassBound`, `Stage1ReductionAtSTBLDψTop`; estimated 9–15k further Lean lines).
- **Refinement after re-reading L989–L1000.** TARGET's W (L992: W = ∏⁽⁺⁾ F(k + z_ℓ), z_ℓ an integer linear
  combination of the link variables) already has the shape of a top cutoff g(k_a), k_a = k + (linear in x, y). So for
  `proplayer1` alone the weighted version is close to routine (c): one more bounded smooth factor of the same form,
  derivatives absorbed as at L995. The non-routine part is the vine class (part 1) and threading the weight through
  `vineest`'s rows and the Stage-1 reduction.
- **Classification: (b)** overall (part 1 is (b); part 2 alone would be (c)). Not an error: no configuration makes the
  printed bound false, and a refute-checked repair route exists. But the paper's "comes in the same way" hides two weighted versions of the paper's two deepest
  estimates and a twist-invariance argument whose correct form (skeleton layers, lower-layer-blind weights) is
  delicate. We do not claim the repair works; we claim the argument is missing.

### 1.8 The M₂ cutoff: time faces, and upper cutoffs at the other stem nodes — (b)

- **Printed.** L2299 (6): "By integrating in t_j before manipulating everything else, and arguing similarly as in the
  proof of Corollary 11.3 in [DH21], we gain a factor M₂^{−P/9} from this integration … (otherwise these cutoffs play
  no role in the proof)."
- **What is missing, (i) time faces.** Integrating e^{iωτ_b} over max(s,σ₁,σ₂) < τ_b < τ_u produces endpoint terms;
  with the other kernels present these are cap/floor faces with their own lower-dimensional measure and carriers, not
  the original garden (E35(a), WORKED; the mixed face/BV identity is LEAN, packet C2-D). DH21 Cor 11.3 is not a layered
  2P-mark theorem.
- **What is missing, (ii) the other cutoffs.** After the product partition (1.5) every unmarked stem node keeps an
  upper cutoff χ₀(|Ω_b|/M). They cannot be dropped from a signed kernel (E35(b)). Inside vines they are class-common
  by L2300 (7) on the support of the M₁ cutoffs. But a stem node can be a chain node of a regular tree inserted on the
  stem, where Ω_b = 2⟨x,y⟩ reads internal link variables: **FINDING-STEMROW** (R142, R145; C2-E-B session 18 confirms
  that the formal weight `markedPhi` places such factors and that no premise excludes the configuration). Then the
  coherent regular-object approximation (`regref`, TARGET L1145–L1232) is needed with a weight at internal momenta.
- **Status.** (i) E35 CANDIDATE with LEAN identity; cut-label fibre theorem PROVED-WITH-REPAIR on paper (R64), referee
  pending at the time. (ii) FINDING-STEMROW is confirmed only at the level of *our* weight definitions and an
  admissible configuration (CAMPAIGN). Whether the paper's intended argument even needs the upper cutoffs inside
  regular objects is not settled; I classify it as **SUSPECTED gap**.
- **What is missing, (iii) stem cutoffs at vine tops.** L2300 puts the stem through a vine's top u₁ and its child u₁₁,
  so an upper stem cutoff χ₀(|Ω_{u₁}|/M) can sit at the top branch of a vine region. (7) makes it class-common, but
  `vineest` must then hold with that smooth resonance cutoff multiplying the class sum. The campaign's V5 scoping
  (uni-top SCOPE §6.2 item 1) found that χ₀(Ω/M) with Ω an indefinite quadratic form has a finite-mass Fourier
  presentation only after localization, which its engine cannot absorb. This is at least a formalization difficulty
  (d) with no owner at the stop; whether TARGET's own argument meets it is **SUSPECTED only**.
- **Classification: (b)** for (i) (the face terms are a real omitted argument); **(b), suspected** for (ii).

### 1.9 The decay factor ⟨k − ζk'⟩^{−4Λ P} inherits E24 — (b)

- L2294 (1) obtains it "by the same arguments as in Section redcount0", i.e. L2065, which is E24 (below, §2): moving
  weights onto decoration-dependent leaves breaks the twist-class cancellation. The repair (type-uniform real inputs by
  central differences, LEAN `first_coeff_extraction`) applies "verbatim to the flower Stage 1 reduction" according to
  E24; that transfer is not formalized.

### 1.10 Smaller flower items

- **F25 (typo, (a)-minor).** L2264–L2265: the prefactor (δ/(2L^{d−1}))ⁿ should be (δ/(2L^{d−γ}))ⁿ, as in DH23
  L1996–L1999 (same slip there). Harmless.
- **F39 (c).** L2271 sums 𝒳's kernel over all flower trees of order ≤ N_{p+1}, which includes the order-0 tree;
  for it (jtflower) has no 𝔣ᵖʳ, and it must be read as the identity operator for (1−ℒ₁)𝒳 = 1+𝒴 to hold. The frozen
  statement reads it so (D5: kind 𝒳 excludes the trivial flower tree); the fixed-point assembly built on that reading is
  proved on main.
- **F68, F78 (d).** Defects in *our* earlier frozen flower statements (designated children and roots not required to
  be top-layer branching nodes), fixed before the freeze.

### 1.11 What the Lean campaign proved about the flower estimate (for calibration)

- `fixedpoint_v2`, `propansatz_v2` and `main_v2` follow on main from `layergardenFlower_v3` + `layergarden_v2` +
  sealed results, with no other input (verified in this audit by a Lean composition and `#print axioms`; see
  CLOSURE.md). `layergarden_v2` itself is proved, axiom-clean and at the exact frozen type, in the unlanded batch-4b-3
  port (verified in this audit). So **the flower estimate is the only mathematics standing between the campaign and
  TARGET's main theorem for 1/2 < γ < 1.**
- Proved (scratch, frozen world, standard axioms; not on main): the exact reduction of `layergardenFlower_v3` to four
  inputs (flower-top `layergardenFlower_v3_of_owners'`), including the couple clause (1.4), the plain clause as a limit
  of the cut1 family (1.6), and both leafwise inputs.
- Not proved: the cut1 family estimate (1.6–1.7), the two cut2 clauses (1.8), and the weighted Stage-1 reduction they
  both need (1.7).

### 1.12 Flower verdict

The paper's proof of `flowerest1` is **not complete at the level we formalize.** Of its seven adjustments, (1), (2),
(4) and (6) omit arguments that are not routine (1.1–1.3, 1.6–1.8); (3) and (5) are fine as stated (translation
invariance; stem layers preserved under LF twists); (7) is fine for vines and is what makes the stem cutoffs
class-common there. **We have no evidence that `flowerest1` is false.** All the gaps we found are of the type "the
cited argument does not apply verbatim to the new object, and the needed variant is not stated": weighted and
fixed-time variants of `vineest`, `proplayer1` and `regref`, and a skeleton theory for flower gardens. The campaign's
judgment (R132, research-internal F5) that these are "exposition gaps, not false statements" is fair as far as
falsity goes; I would not call them *routine* exposition gaps, because the correct form of the twist-invariance
argument (skeleton layers, lower-layer-blind weights) was found only after two of the campaign's own natural readings
were refuted.

---

## 2. Other places where the formal proof could not follow the paper

[Draft 1: classifications assigned from the errata file E1–E35 plus my reading of each entry's evidence. Per-entry
detail is in `docs/ERRATA-AND-DEVIATIONS.md`; quotes there are machine-verified per R65.]

| Id | Location | Issue (short) | Class | Evidence | Effect |
|---|---|---|---|---|---|
| E1 | DH23 Prop 9.6 case (4), L1885; TARGET L2192–L2197 | "an enumeration shows 𝕄₀ must be a vine" is false; Prop 9.6 fails for 0<γ≤1/2 (necklace N_m) | **(a)** | WORKED + mechanical + independent referee | TARGET's proof fails for γ ≤ 1/2 at `lgmolect`; main theorem not refuted; γ>1/2 closed by a new argument (F75, refereed); campaign restricted to 1/2<γ<1 |
| E3/F72 | DH23 Def 5.1, vine (II), L1421 | must include m = 1 (Q-block) | (a)-minor (definition omission) | WORKED | repaired by reading |
| F73 | DH23 `kqmainest1` L1632; TARGET (finalsbest2) L2078 | per-class analytic bounds also fail on necklaces, γ<1/2 | (a), CANDIDATE | derived, error terms not fully explicit | same scope as E1 |
| E4 | TARGET `vineest` Step 3, L1846 | "replace ε by 1 … trivial summation" loses L^{Mγ−d} for M > d/γ | (b) | LEAN (corrected argument) | statement survives |
| E5 | TARGET (finalsbest1), L2079 | "very easy with ladderl1new": ladders in one layer are coupled by time order | (c) | LEAN (corrected proof) | statement survives |
| E6 | TARGET L2187 | invariant not preserved under blanket Op 2 cut | (a)-minor, CANDIDATE | explicit computation | DH23's formulation avoids it |
| E7 | DH23 L1794 | pair count assumes nonzero difference | (c), CANDIDATE | analytic | final bound unaffected |
| E8, E10, E12, E13, E21, E22, E28 | DH23 §9–10 / TARGET §redcount | omitted cases in the counting run | (c), CANDIDATE | worked; Lean uses the fills | harmless |
| E9 | TARGET `finalmol` L2185/L2187 | "at most R imperfect components" false after tame removals (R+2t); TARGET's own L2218 contradicts it | (a)-minor, CANDIDATE | explicit configuration | final estimate survives |
| E11 | TARGET `remtame` (i), L2152/L2218 | "cut at v and proceed normally": the pin does not survive the cut; Prop 9.6 false for the resulting component (X = {a,b,c,v₁}) | (b) with a false sub-claim | WORKED (research + mechanical) | repaired by erasure (DH23 §10.5) |
| E14 | TARGET `vineest` L1742–L1752 | domain wrong when a lower child is a leaf | (c) | — | trace repair |
| E16 | TARGET L2152 | "a ZG v₃ … must be tame by subpro (3)" false for hinge v₃ (order-6 couple) | **(a)** local | WORKED, referee re-derived (300/300) | repaired (R29) |
| E17 | TARGET L2152/L2218, L2193/L2197 | single-atom erasure leaves unbounded components; "imperfect = odd" contradicts L2189 vs L2218 | (a)-minor / (b) | graph-level | repaired by cluster erasure |
| E18 | TARGET L1913 (ii) | "J̃_𝒬(t,s) = 0 if t = L_r" false for trivial couples/trees | (a)-minor | LEAN (trivial couple) | harmless after repair |
| E19 | TARGET L2216 | p_sb ≤ p_op should be ≤ 2p_op | (a)-minor | — | absorbed by margin |
| E20 | DH23 L1777/L1791; TARGET L2142/L2165 | triangles with an already-cut atom ("ghost"): per-step bound fails | (b), CANDIDATE | lattice count to L ≤ 400 | repaired for γ>1/2; open for γ≤1/2 |
| E23 | TARGET L2122 | stage-1 molecule has degree 0/1/2 atoms and loops; DH23 assumes degree 3–4 | (b), CANDIDATE | LEAN examples (FcgeomCex) | new LOW-degree run needed and built |
| E24 | TARGET L2065, L2067 | moving weights/derivatives onto decoration-dependent leaves breaks `vineest`'s twist cancellation | **(b)** | three independent finders + referee; extraction identity LEAN | result survives with a new argument |
| E25 | TARGET L1909 vs (vineest2) | class count consumes part of the bad-vine gain; full η² gain not available | (a)-minor | CAMPAIGN | gain η²/2 suffices |
| E26 | TARGET (redvine), L1954–L1957 | lower-child slots keep the lower-joint clock τ_b, not t_a | (a) local identity, CANDIDATE | structural configuration, no numeric instance | repaired by modulation (R58) |
| E27 | TARGET L1944 | "at most 2ⁿ" refinement classes false (Δ+1 relayerings) | (a)-minor | worked | final count survives |
| E29–E33, E35 | flower section | see §1 | (b)/(c) | see §1 | flower estimate not closed |
| E34 | our frozen statement | max-form cutoff ≠ product partition | **(d)** | LEAN | fixed by v3 |

Also in `docs/FINDINGS.md`, not yet in the errata file (typo or missing-hypothesis level; harmless): F42 (TARGET Lemma
A.3 bound false for arbitrary F, needs smooth compactly supported F — (a)-minor), F43 (atomcountbd L2472 false at k = 0
— (a)-minor), F25, F28, F45, F50, F51, F55/F77 (DH21 count slips), F70, F79, F81.

## 3. Campaign "findings" that are really formalization difficulties (d)

These appear in RULINGS as FINDING-* or "false" statements, but concern our own statements or Lean architecture, not
the paper:

- **E34 / D13** max-form cutoff in our frozen v2 (1.5).
- **F68, F78** our flower statement defects.
- **R57 F-KIND** our V5 statement hard-wired kind = true; TARGET Def `lftwist` covers couples explicitly.
- **R68 TraceCounterexample** a norm-only trace is false for arbitrary functions; the paper's kernels are continuous.
- **R118/R122 FINDING-ANCH** profile 1 at anchored leaves has infinite Sobolev norm in our encoding; TARGET treats
  1_{k_𝔣=k'} explicitly (L2295).
- **R125 FINDING-TIVINE, R133, R139 FINDING-INTERNAL (architecture part)** our Stage-1 interfaces could not carry
  weights; the underlying paper issue is §1.7, counted once there.
- **R135** refutes *our* first weight formula (`regionTopWeight`), not the paper (§1.7).
- **R128, R136, R138, R143** vacuous quantifier orders and inconsistent build worlds in our scratch packets.
- **E2-level typos** that the formalization merely had to read correctly (F5, F9, F27, F35 …).

## 4. What is verified versus suspected (summary)

- **Verified false (a), with consequences:** E1 (DH23 Prop 9.6 for γ ≤ 1/2).
- **Verified false (a), local and harmless:** E16, E18 (Lean), E9, E19, E27, F42, F43; E6, E26 candidate.
- **Verified gaps (b) whose repairs are proved in Lean:** E4, E24 (core identity), E11, E23 (LOW run), E32 (flower
  couple clause).
- **Gaps (b) in the flower estimate, configurations worked, repairs designed but NOT proved:** §1.1, 1.2, 1.3, 1.6,
  1.7, 1.8(i).
- **Suspected only:** §1.8(ii) FINDING-STEMROW as a paper issue.
- **Not found:** any counterexample to TARGET's main theorem, to `layergarden`, or to `flowerest1`.
