# Audit: Wave B stage 1 (core definitions, `WaveB1-Core.lean`)

Auditor: `wt-orch` (Opus), refute-first. Date: 2026-11-03. Task 4b, stage 1.

## Inputs

**Snapshot.** I audited the frozen snapshot `/home/scott/wt-scratch/waveb-snap-1/`, not the live directory.
`sha256sum -c SHA256SUMS` passes. The files I audited:

| File | Lines | sha256 |
|---|---|---|
| `WaveB1-Core.lean` | 627 | `aff86f25…32daaa` |
| `WaveB1-Core-probes.lean` | 380 | `699aea84…c31a1d` |
| `DESIGN.md` (§1, §4, questions Q1, Q2 and Q4) | 400 | `625952e2…442f6b` |

**Source.** `paper/source/WKE-Longer_times_Final_arXiv.tex`, sha256 `493eef6b…727cb`. Line numbers below refer to
this file.

**Toolchain.** Lean v4.35.0, Mathlib v4.35.0.

**How I elaborated the drafts** (no `lake build`, one `lean` process at a time, `nice -n 5`, run from my worktree):
- I first compiled the imported landed Foundations modules into the worktree's `.lake/build`, one module at a time
  with `lake env lean -o … -i …`: `Torus/{Basic, Derivative, Inversion, Series, TimeDerivative, Product}`,
  `NLS/{FourierEquation, AkSystem}` and `Cumulant/Basic`.
- I then copied the snapshot files to a scratch source root as modules `WaveBDraft.{Core, CoreProbes, System,
  SystemProbes}` and compiled each with `LEAN_PATH` extended and `-R <root>`.
- Results:
  - Core: OK.
  - Core-probes: OK, sorry-free.
  - All imports resolve: Core imports only `Frozen/Defs/{Mom, LatticePoint, IsWKESolution}` and
    `Foundations/NLS/AkSystem`.
- `#print axioms` on the probes `figLG_canon3`, `figLG_trunc`, `finite_layeredGardens`, `wtPrefix_true`,
  `trivialCouple_canon` and `flowerGarden_canonH` gives `[propext, Classical.choice, Quot.sound]`.

## Verdict

**NOT APPROVED. One REQUIRED fix (R1).**

**R1.** `attachedOrder` generates its equivalence relation on **all** nodes. Chains can then pass through a common
ancestor and merge distinct attached gardens. As a result `IsTrunc`, and so 𝒢^tr, 𝒞^tr, ℋ^tr and every `truncSum*`,
excludes gardens that TARGET Def `defgtr` includes. A sorry-free probe proves this on an explicit garden of 𝒢₂.

**Everything else** is FAITHFUL or a disclosed reading that I accept. This covers:
- the parameter prefix (Π) and its binder order (F5);
- the derived parameters;
- trees, the flower-capable garden carrier (G-1), couples, paired trees and flower gardens;
- decorations, ε and Ω;
- layerings (Q1);
- the canonical criterion, against Def 3.7 / Prop 4.8 (`canonequiv`) and the F35 reading;
- `IsCanonC` (Q2) and `IsCanonH`;
- the top-tree order of the truncation;
- arbitrary width (Q4).

Earlier concern E2 (the name clash with the landed `epsCoef`) is fixed in the snapshot.

## 1. Verdict table

### 1a. Declarations

| Decl | Verdict | TeX | Reason |
|---|---|---|---|
| `WTParams` | FAITHFUL | L605–L615 | One field per parameter TARGET fixes. C₀ is not a field: it is absorbed into the choice of η₀(d,γ) ("η small depending only on C₀"), and the statements write their absolute constants explicitly. |
| `WTPrefix` | FAITHFUL (F5) | L605–L615, (defD) | See §1b. |
| `theta` | FAITHFUL | (parameters) L611 | `η^20(1+2^{-p})`. The probe `theta_chain` proves L611's chain. |
| `Lambda` | FAITHFUL on 0 ≤ p ≤ 𝔇+1 | (parameters) | `(40d)^{𝔇+1−p}` in ℕ, which equals `(40d)^{𝔇−p+1}` on that range; probe `Lambda_succ`. For p > 𝔇+1 the truncated subtraction gives 1, which is junk but never consumed. |
| `Rdown`, `R`, `N` | FAITHFUL on 0 ≤ p ≤ 𝔇 | (parameters2) L612 | R_𝔇 = ⌊(log L)^{40d}⌋₊ (`Real.log P.L ^ (40*d)` parses as (log L)^{40d}); N_p = R_p^{40d}; R_{p−1} = N_p^{40d}. Probes `R_top`, `R_pred`. For p > 𝔇, `R p = R_𝔇` (clamped), which is never consumed. |
| `gamma0`, `gamma1` | FAITHFUL | (defgamma1) L613 | — |
| `TTree`, `order`, `nodes`, `leaves`, `branching` | FAITHFUL | Def `deftree` L625–L631 | Gorn addresses. Probes `card_leaves` (\|ℒ\| = 2n+1) and `card_branching` (\|𝒩\| = n). |
| `pathSign`, `nodeSign`, `Garden.sign` | FAITHFUL | L629–L630 | Children of a node of sign ζ′ have signs (ζ′,−ζ′,ζ′), so ζ_𝔫 = ζ·(−1)^{#mid steps}. |
| `GNode`, `GLeaf`, `GBranch`, `toNode`, `child`, `root`, `IsDesc`, `Incomparable`, `leavesBelow`, `orderBelow` | FAITHFUL | L627 | `IsDesc` is reflexive (a node is its own descendant), as at L627. `leavesBelow a` is the leaf set of the subtree at `a`, and `orderBelow a` its order. |
| `MarkTag`, `Garden` | FAITHFUL (G-1 carrier) | Def `defgarden` L632–L638, L637, Def `defflower` L2259–L2263 | The involution `pair` has exactly the marked leaves as fixed points (`pair_eq_iff`), and paired leaves have opposite signs (`pair_sign`). A plain garden (no marks) is exactly TARGET's "partition of the leaves into opposite-sign pairs". The trees are ordered and labelled, as TARGET's sums need. No junk: `pair` is defined only on leaves. Equal data give equal `Garden` terms (the Prop fields are proof-irrelevant), so a `finsum` over `LayeredGarden w` counts each labelled layered garden exactly once. |
| `IsFlower`, `IsLone`, `IsPlain` | FAITHFUL | — | — |
| `IsBalanced` | FAITHFUL | L632 | "Exactly half +". It is automatic for plain gardens: each tree has one more leaf of its own sign than of the other, and pairs cancel. So plain width-w gardens have w even. |
| `IsFlowerGarden` | FAITHFUL (see O1) | Def `defflower` L2259 | One marked leaf per tree, marks are flowers, root signs (+,−,+,−,…), non-flower leaves completely paired with opposite signs (by the carrier). Flower signs are not fixed, as in TARGET. TARGET's width is 2R; the predicate does not force w even (O1). |
| `order`, `zeta` | FAITHFUL | L632, (defgarden) | ζ(𝒢) = ∏_{𝔫∈𝒩}(iζ_𝔫). |
| `CompletelyPaired`, `leavesOf`, `Irreducible` | FAITHFUL | L636 | No A with ∅ ≠ A ≠ univ whose leaves are paired among themselves. `CompletelyPaired` excludes marked leaves, which only matters for non-plain gardens and agrees with "completely paired" at L2259 and L889. |
| `IsCouple` | FAITHFUL | L634 | Width 2, plain, (+,−). Irreducibility is automatic: one tree alone has an odd excess of one sign. |
| `IsPairedTree` | FAITHFUL | L637 | Width 1, exactly one marked leaf, tagged `lower`. The lone leaf's sign equals the root's (forced by the opposite-sign pairing), so k_𝔯 = k_{ℓ_lo} holds automatically (L643). |
| `IsDecoration`, `IntDecoration` | FAITHFUL | Def `defdec` L641–L643 | k_𝔫 = k_{𝔫₁} − k_{𝔫₂} + k_{𝔫₃}; paired leaves equal; root values. Integer labels n with vectors n/L. |
| `GenDecoration` | FAITHFUL | L643, L2260 ((k,k′)-decorations) | Root values n_j and value n′ at every flower. The flower clause is void for plain gardens and paired trees. |
| `cosetDecoration` | FAITHFUL | L643 | For L ≠ 0, k + z/L over integer z with root value 0 runs bijectively over the k-decorations of couples and paired trees with k ∈ ℝ^d. |
| `epsDec` | FAITHFUL | (defepscoef), (defcoef0) | Landed `epsCoef` on integer labels. For L ≠ 0, k + z/L ↦ z preserves the equalities ε depends on. |
| `resFactor`, `omegaNode` | FAITHFUL | (res), (defomega) | Duplicates the landed `resonance` in vector form (O3). |
| `IsLayering`, `LayeredGarden` | FAITHFUL (reading Q1) | Def `deflayer` L650 | ℕ-valued; child ≤ parent; paired leaves equal. Q1 is accepted (§4). |
| `parentLayer` | FAITHFUL | L889 | A root's parent layer is read as `top` (= p), per "replaced by p". |
| `CanonCriterion` | FAITHFUL (F35 reading harmless) | Prop `canonequiv` L889 | (i) all layers ≤ p. (ii) For incomparable 𝔫, 𝔫′ whose subtree leaves are completely paired: min(parent layers) ≤ max(layers). Restricting to incomparable pairs (F35) loses nothing: if 𝔫 = 𝔫′ or one is below the other, the union of their leaf sets is the leaf set of one subtree, which is odd, so it is never completely paired. I re-read the proof (L890–L897) and agree with DESIGN §4 in both directions. |
| `OnStem` | FAITHFUL | L2259 ("stem … from the root to the flower") | Includes the flower itself (`IsDesc` is reflexive), as L2261 requires ("all the nodes on the stem … in layer p"). |
| `IsCanonG` | FAITHFUL (criterion form; the agreement with Def `defcanon` is obligation B1.11) | Def `defcanon` L657–L668, L889 | 𝒢₀ = ∅. 𝒢_{p+1} = width ≥ 4 (proper), plain, irreducible, and the criterion at p. Plain and width ≥ 4 give even width, so R ≥ 2. Probe `figLG_canon3` (the 19-node figure garden, by kernel `decide`) and its negative controls `figLG_not_canon2` and `figLGBad_not_canon3`. |
| `IsCanonC` | FAITHFUL (reading Q2) | Def `defcanon` last paragraph; L889 "Similarly … couple" | Couple plus criterion. It contains the trivial couple with both roots in layer p and no other layering: (ii) at the two roots forces max(layer) ≥ p. This matches Def `defcanon` with R = 1. Probes `trivialCouple_canon`, `miniCouple00_canon`, `miniCouple01_canon` (all at p = 0). |
| `IsCanonH` | FAITHFUL (criterion form; obligation B1.11(4)) | Def `defflower` L2261–L2262 | Flower garden, stem in layer p, criterion, no irreducibility. The criterion form relies on L2262's "Prop `canonequiv` also holds for ℋ_{p+1}". I checked the "if" direction: the 𝒰-forest contains no flower, because ancestors of flowers lie on the stem in layer p, so the garden proof applies verbatim. Probe `flowerGarden_canonH`. |
| `attachNodes` | FAITHFUL | proof of `canonequiv` (𝒰) | 𝔏_𝔫 < p and parent layer = p, with roots included. |
| `topOrder` | FAITHFUL | Def `defgtr` (i) | The number of layer-p branching nodes of 𝒯_j. These are exactly the branching nodes of the initial tree 𝒯_j^p, since layers are ≤ p and nondecreasing upwards. The flower variant at L2290 is the same. Probe `figLG_topOrder`. |
| `AttachLinked` | OK as a relation; docstring wrong | — | Defined on all nodes, whereas the docstring says "two attachment nodes". |
| `attachedOrder` | **WRONG (R1)** | Def `defgtr` (ii) L731–L732 | See §2. |
| `IsTrunc` | **WRONG via R1**; otherwise FAITHFUL | Def `defgtr`, L2288 | With R1 applied: (i) top orders ≤ N_top and (ii) every attached garden of order ≤ N_att. With `(Ntop, Natt) = (N_{p+1}, N_p)` this is TARGET's definition; the flower version ℋ^tr (L2288) is the same predicate. |

### 1b. Binders of `WTPrefix` (F5)

TARGET's order (L605–L615) is: fix τ★, φ; then "C₀ depends on (d,γ), η small depending only on C₀"; then
"C₁ = C₁(τ★, η, 𝔆)"; then ν small depending on C₁; then δ small depending on ν with 𝔇 = τ★/δ ∈ ℤ; then
"C₂ = C₂(𝔇, δ, φin)"; then L large depending on C₂. F5 records the resulting order C₀ → η → 𝔆 → C₁ → ν → δ (𝔇) → C₂
→ L.

| Binder | Verdict | Reason |
|---|---|---|
| `∀ d, 3 ≤ d`, `∀ γ ∈ (0,1)` | FAITHFUL | Rulings D2 and the frozen `main`. |
| `∃ η₀ > 0, ∀ η ∈ (0, η₀]` | FAITHFUL (F5) | η₀ comes before the data, so it depends only on (d, γ), as "depending only on C₀" says. Universal quantification over small η is the eventual reading of "η small enough". |
| `∀ φin` Schwartz with φin ≥ 0; `∀ τ★ > 0`; `∀ φ` with `IsWKESolution φin τ★ φ` | FAITHFUL | These are the data hypotheses of the frozen `main`. By Wave A §1b, `IsWKESolution` on `[0, τ★]` ⟺ τ★ < τ_max and φ is the solution. |
| `∃ C₁ ≥ 1` | FAITHFUL | It comes after η and the data, so it may depend on (τ★, η, 𝔆). The normalization `≥ 1` is harmless because the statements are monotone in C₁ (DESIGN Q3). |
| `∃ ν₀ > 0, ∀ ν ∈ (0, ν₀]` | FAITHFUL | Small depending on C₁. |
| `∃ δ₀ > 0, ∀ δ ∈ (0, δ₀]`, `∀ D ≥ 1, τ★ = D·δ` | FAITHFUL | Small depending on ν, with (defD). `1 ≤ D` is automatic from τ★, δ > 0. |
| `∃ C₂ ≥ 1` | FAITHFUL | It comes after (δ, 𝔇) and the data, as "C₂(𝔇, δ, φin)" requires. |
| `∃ L₀ ≥ 2, ∀ L ≥ L₀` | FAITHFUL | "L large depending on C₂". |

Non-vacuity: `wtPrefix_true`. The hypotheses are satisfiable as soon as (WKE) has a Schwartz solution, which is Wave
A's `wkelwp`.

## 2. REQUIRED fixes

### R1. `attachedOrder` merges distinct attached gardens

**The defect.** `attachedOrder p u` sums `orderBelow` over the attachment nodes u′ with
`Relation.EqvGen LG.AttachLinked u u'`. Because `AttachLinked` is a relation on **all** nodes, the generated
equivalence can pass through non-attachment nodes. The root w of a top tree is linked to u as soon as one leaf below
u is paired with any leaf of that tree, since every leaf of the tree lies below w. Two attached gardens hanging in
the same top tree therefore end up in one class, and `attachedOrder` returns the sum of their orders.

**What TARGET says.** Def `defgtr` (ii) bounds *each* garden of 𝒢_p that replaces a leaf subset B_i by N_p. The
proof of `canonequiv` (L897) identifies these gardens as the irreducible components of the garden formed by the trees
rooted at 𝒰. Those components are the classes of the relation *restricted to 𝒰*. DESIGN §4 describes this
correctly ("the equivalence relation generated by … on 𝒰"), but the code does not implement it.

**Consequence.**
- The draft's `IsTrunc` is strictly stronger than TARGET's, so 𝒢^tr_{p+1}, 𝒞^tr_{p+1} and ℋ^tr_{p+1} are too small.
- Hence `truncSum`, `truncSumC`, `truncSumH` and the statements' `truncSumHζ` all compute the wrong sums once
  attached orders can exceed N_p.
- B1.11(2) as drafted ("blocks equal to the `AttachLinked` classes") is false for the same garden.
- `truncSum_untruncated` (N ≤ N_q) is unaffected: every class order is at most the total order.

**Counterexample**, proved sorry-free in `scratch/WaveB-stage1-E1.lean` (§5):
- **The garden.** Width 4, signature (+,−,+,−). The trees are 𝒯₁ = node(node(•₃, •, •), •, •₃), where •₃ is the tree
  of order 1, and 𝒯₂ = 𝒯₃ = 𝒯₄ = •.
- **The layering.** The nodes [] and [0] of 𝒯₁ are in layer 1; every other node is in layer 0.
- **The attached gardens.** There are two, each in 𝒢₁, each of order 1:
  - G₁ is attached at {[0,0], [0,1], [0,2], [1]} of 𝒯₁;
  - G₂ is attached at {[2] of 𝒯₁, root of 𝒯₂, root of 𝒯₃, root of 𝒯₄}.
- **Canonicity.** The garden is in 𝒢₂: probe `e1_canon2` (`decide`). It also satisfies Def `defcanon` literally: the
  top trees are 𝒯₁ cut to layer 1 (order 2) and three trivial trees; B₁ and B₂ are as above; no proper union of B's
  is a top-tree leaf set.
- **TARGET's verdict.** With (N₂, N₁) = (2, 1), the garden is in 𝒢^tr₂: top orders (2,0,0,0) (`e1_topOrder`) and
  attached orders 1, 1.
- **The draft's verdict.** `EqvGen AttachLinked` links [0,0] to [2]:
  - `AttachLinked [0,0] root₁`, via leaf [0,0,0] ↔ [0,1];
  - `AttachLinked root₂ root₁`, via root₂ ↔ [2,0];
  - `AttachLinked [2] root₂`.

  This is `e1_merged`. Hence `2 ≤ attachedOrder 1 [0,0]` (`e1_attachedOrder_ge`) and `¬ IsTrunc 1 2 1`
  (`e1_not_trunc`).
- **With the fix.** Every class order is ≤ 1 (`e1_attachedOrder'_le`).

**Exact Lean change** (`WaveB1-Core.lean`, §7):

```lean
/-- Two attachment nodes are linked if some leaf below the first is paired with a leaf below the
second. The attached gardens are the classes of the equivalence relation on `attachNodes p`
generated by this (T Prop `canonequiv`, proof: the components of the garden rooted at `𝒰`). -/
def AttachLinked (u u' : GNode LG.garden.tree) : Prop :=
  ∃ ℓ ∈ u.leavesBelow, LG.garden.pair ℓ ∈ u'.leavesBelow

/-- `AttachLinked` restricted to the attachment nodes `𝒰 = attachNodes p`. -/
def AttachLinkedOn (p : ℕ) (u u' : GNode LG.garden.tree) : Prop :=
  u ∈ LG.attachNodes p ∧ u' ∈ LG.attachNodes p ∧ LG.AttachLinked u u'

noncomputable def attachedOrder (p : ℕ) (u : GNode LG.garden.tree) : ℕ := by
  classical
  exact ∑ u' ∈ (LG.attachNodes p).filter (fun u' => Relation.EqvGen (LG.AttachLinkedOn p) u u'),
    u'.orderBelow
```

**Why the fix is exactly right.** Take u in the block of an attached garden G_a. Every leaf below u is a leaf of G_a,
and G_a is completely paired. So the restricted relation never leaves G_a's block; it is connected on the block by
the irreducibility of G_a.

**After the fix:**
- the existing probes `attachedOrder_le_total` and `figLG_trunc` keep their proofs;
- add the E1 garden to `WaveB1-Core-probes.lean` as the second truncation unit test (`e1_canon2`, `e1_topOrder`,
  `IsTrunc 1 2 1`);
- change B1.11(2) to name `AttachLinkedOn`.

## 3. OPTIONAL suggestions

- **O1.** `IsFlowerGarden` allows odd w, whereas TARGET's flower gardens have width 2R. It is harmless because the
  consumers fix w = 2P. Either add `Even w` or state in the docstring that the width is fixed by the consumer.
- **O2.** Document the junk ranges of the parameters: `Lambda p = 1` for p > 𝔇+1, and `R p = R_𝔇` for p > 𝔇. No
  consumer reaches them, because statements quantify p ≤ 𝔇 and use q = p+1 ≤ 𝔇.
- **O3.** Add a bridge lemma:
  `omegaNode G (cosetDecoration G L 0 κ) b = resonance L (κ (b.child 0)) (κ (b.child 1)) (κ (b.child 2)) (κ b.toNode)`.
  `treeTerm` (stage 2) uses the landed `resonance`, while `kernelK` uses `omegaNode`. The cumulant expansion matches
  the two (T L733–L750), so a one-line bridge saves the provers a rediscovery.
- **O4.** Add a lemma that the lone leaf of a paired tree has the tree's sign. This is what makes k_𝔯 = k_{ℓ_lo}
  automatic (L643) and keeps `KTstar` from needing a lone-leaf value constraint.
- **O5.** In DESIGN §4 ("Truncation"), point to `AttachLinkedOn` after R1. Also add the E1 garden to the probe list
  there: the figure garden alone cannot detect merging, because it has only one attached garden.

## 4. DESIGN questions (definitional; my answers)

- **Q1 (layers in ℕ): ACCEPT.** Under T L650 a root that is a leaf of a trivial tree could take a negative layer,
  which would make F_{𝔏_ℓ} undefined. Every other node is ≥ 0, since it is ≥ its children, which are ≥ 0. TARGET
  never uses negative layers (every construction puts nodes in layers 0…p). Taking `ℕ` removes the junk without
  changing any sum.
- **Q2 (𝒞₀ = ∅): ACCEPT.** TARGET defines 𝒞_{p+1} only for p ≥ 0, and no statement uses 𝒞₀. `False` at 0 matches
  𝒢₀ = ∅.
- **Q4 (arbitrary width w): ACCEPT.** It is the only uniform carrier for gardens (2R), couples (2), paired trees (1)
  and flower gardens (2P). For plain gardens, evenness and balance are automatic. Consumers fix w through their
  binders (`Fin (2*m)` and `w := 2*Pm`).
- **Q3** (the prefix composition lemma) is not a definition. I agree with leaving it to the provers. Its
  precondition, monotonicity in C₁, C₂ and the thresholds, holds for every B1 statement I have read.
- **F37 / F40** are not exercised in stages 1–2. The snapshot defines no molecules, vines, ladders or cuts. They
  belong to carrier B (DESIGN §1.2, deferred to COMB-CORE). The F37 reading (k ≥ 0 rungs per slot) and the F40
  reading (half-edge darts) must be applied there, so this audit records nothing against them.

## 5. Non-vacuity probes

**Snapshot probes** (`WaveB1-Core-probes.lean`, elaborated, sorry-free):
- the trivial couple and the mini-couples (00 and 01) with their predicates decided;
- the figure garden: in 𝒢₃, not in 𝒢₂, plus a lowered-layer negative control;
- the figure's truncation data: top orders (2,1,0,0), six attachment nodes, `IsTrunc 2 2 2`, `¬ IsTrunc 2 1 _`;
- a flower garden in ℋ₁ that is not plain;
- a paired tree;
- the finiteness theorem `finite_layeredGardens` (order ≤ n *and* depth ≤ p).
  - Every sum over `IsCanonG/C/H q` is depth-bounded by q−1, through criterion (i).
  - So the finiteness theorem covers the stage-2 `finsum`s; System probes `finite_truncSum*_support`.
- the parameter lemmas;
- `wtPrefix_true`.

**My probe** `scratch/WaveB-stage1-E1.lean` (untracked; sha256 `b2e098a9…31ab1af`, 144 lines):
- It imports `WaveBDraft.CoreProbes`, i.e. the snapshot compiled as described in the Inputs section.
- It proves `e1_canon2`, `e1_topOrder`, `e1_merged`, `e1_attachedOrder_ge`, `e1_not_trunc` and, for the fixed
  definition, `e1_attachedOrder'_le`.
- Every proof is a kernel `decide`, plus a short `EqvGen` induction.
- Axioms: `[propext, Classical.choice, Quot.sound]`.

The core of the probe:

```lean
def e1T1 : TTree := .node (.node tree1 .leaf .leaf) .leaf tree1
def e1Pairs : List ((Fin 4 × Path) × (Fin 4 × Path)) :=
  [((0, [0, 0, 0]), (0, [0, 1])), ((0, [0, 0, 1]), (0, [0, 2])), ((0, [0, 0, 2]), (0, [1])),
   ((0, [2, 0]), (1, [])), ((0, [2, 1]), (2, [])), ((0, [2, 2]), (3, []))]
def e1Garden : Garden 4 :=
  mkGarden 4 ![1, -1, 1, -1] ![e1T1, .leaf, .leaf, .leaf] (swapList e1Pairs) (by decide)
def e1Layer : Fin 4 × Path → ℕ
  | (0, []) => 1 | (0, [0]) => 1 | _ => 0
def e1LG : LayeredGarden 4 := ⟨e1Garden, fun a => e1Layer a.1, e1_isLayering⟩
theorem e1_canon2 : IsCanonG 2 e1LG := by decide
theorem e1_topOrder : (List.ofFn fun j => e1LG.topOrder 1 j) = [2, 0, 0, 0] := by decide
theorem e1_not_trunc : ¬ e1LG.IsTrunc 1 2 1 := …   -- TARGET: in 𝒢^tr₂ for (N₂, N₁) = (2, 1)
theorem e1_attachedOrder'_le (u) (_ : u ∈ e1LG.attachNodes 1) : attachedOrder' e1LG 1 u ≤ 1 := …
```
