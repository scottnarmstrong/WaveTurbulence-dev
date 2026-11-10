# The T-vine blueprint: the T-vine combinatorics, Lean-oriented

## Reader's preface

**What this note proves.** It states exactly, in a form ready for Lean, the combinatorics of T-vines (the enlarged
vine family used for γ ≤ 1/2), and proves for all sizes what was still missing. Theorem C (§3) gives every T-vine an
explicit chart, so that the hypotheses (i)–(iii) of TARGET Prop `sumint` hold for chains of T-vines; §5 replaces
every use of confluence of the (Y)-reduction (N2 Lemma 1.4) by surgery on one given (Y2)-path. It also encodes
T-vines for the class count (§6), re-checks the `vineest` repairs for T-vines (§7) and lists the finite facts left to
a verified checker (§8).

**How it fits the repair.** It supports ingredient 1 of the repair,
[T-vines](../GAMMA-LE-HALF.md#3-ingredient-1-t-vines), which answers erratum E1 of
[ERRATA](../ERRATA-AND-DEVIATIONS.md), and re-checks for T-vines the repairs E2d, E4, E14 and E24–E26 of the vine
estimate.

**Where it is in Lean** (names relative to the namespace `WaveTurbulence`, files relative to the repository root).
- Definitions: `Molecule.IsTVine` and the γ-dependent family `Molecule.IsVineGamma`, in
  `WaveTurbulence/Foundations/TVine/Defs.lean` (the approved text, pinned by hash).
- Core lemmas and path surgery: `WaveTurbulence/Foundations/TVine/Core/` (for example `Lemma5.lean`, `Lemma19.lean`,
  `LemmaE.lean`, `Phi*.lean`), assembled in `TVine.Core.phiType_holds`
  (`WaveTurbulence/Foundations/TVine/Core/Final.lean`).
- In `WaveTurbulence/Foundations/TVine/Checker/`: generation without confluence (Lemma 1.7′),
  `TVine.Checker.generation`; the size bound |B| ≤ 11 + 2D(B), `TVine.Checker.sizeBound`; the base cases (at most
  13 atoms), decided by a checker proved sound and evaluated by the kernel, `TVine.Checker.pieceShapeBase`,
  `TVine.Checker.subObjBase`, `TVine.Checker.familiesBase`.
- In `WaveTurbulence/Foundations/TVine/Struct/Final.lean`: `TVine.Struct.pieceShape_holds` (Prop 1.17(b)),
  `TVine.Struct.layervine_holds` (N3 Theorem 6), `TVine.Struct.attach_holds` (Lemma A),
  `TVine.Struct.subObjects_holds` (Theorem 1.15), `TVine.Struct.cor116Single_holds` (Cor 1.16′). Drawn vines are
  T-vines (Lemma 5.2): `TVine.Struct.Drawn.drawnTVine`.
- Theorem C: `TVine.Chart.tvineChart_holds` (`WaveTurbulence/Foundations/TVine/Chart/Unconditional.lean`); Lemma D:
  `WaveTurbulence/Foundations/TVine/Chart/LemmaD.lean`.
- The vine estimate over the enlarged family, built on Theorem C: `GammaLow.Famb.vineEstGammaHalfMK`
  (`WaveTurbulence/Foundations/GammaLow/Famb/VineEstGamma.lean`).
- Names marked "proposed" (§2.1, §9) are this note's plan, made before the formalization; the names actually used
  are those above.

**Status.** Accepted with repairs by an independent refute-first referee
([report](gamma-le-half-tvine-blueprint-referee.md)). The referee's repairs are listed in the report; they were
applied in the Lean formalization and are not folded into this text.

*Provenance: written and independently refereed in November 2026.* The scripts named in the text are not included in
this repository. Lean names refer to the repository at the time of writing (this preface: commit `5c19b015`; the text:
the commit it cites, where it cites one); a later clean-up removed some unused helpers, which remain in the git history
at the commits cited.

**Abbreviations.**
- TARGET: Y. Deng, Z. Hani, *Long time justification of wave turbulence theory*, arXiv:2311.10082v2; line numbers
  are lines of its TeX source (sha256 `493eef6b…`).
- DH23: Y. Deng, Z. Hani, *Derivation of the wave kinetic equation: full range of scaling laws*, arXiv:2301.07063;
  line numbers as above.
- DH21: Y. Deng, Z. Hani, *Full derivation of the wave kinetic equation*, arXiv:2104.11204.
- N1, N2, N3: the three earlier research notes on T-vines,
  [`gamma-le-half-repair-1-notes.md`](gamma-le-half-repair-1-notes.md),
  [`gamma-le-half-repair-2-notes.md`](gamma-le-half-repair-2-notes.md),
  [`gamma-le-half-repair-3-notes.txt`](gamma-le-half-repair-3-notes.txt); REF1–REF3: their referee reports
  `gamma-le-half-repair-{1,2,3}-referee.md`.
- ERRATA: [`../ERRATA-AND-DEVIATIONS.md`](../ERRATA-AND-DEVIATIONS.md) (here E2d, E4, E14, E18, E24–E26, E37).
- TVineDefs: the T-vine definition as proposed for approval (`TVineDefs.lean`, the undirected API;
  [review](../review/GAMMA-LE-HALF-VINES.md)). Approved, it became `WaveTurbulence/Foundations/TVine/Defs.lean`.
- main: the main branch of this repository when the note was written (read only; Lean names as of that time), in
  particular `WaveTurbulenceVineParam/Contract.lean` (`FullVineChart`), `WaveTurbulence/Frozen/Defs/SumintDatum.lean`,
  `WaveTurbulence/Foundations/VineEst/VineEstS2/` (the `sumint` consumer) and
  `WaveTurbulence/Foundations/Stage1/ClassCount/` (the class count).
- The counting note: [`gamma-le-half-counting-notes.md`](gamma-le-half-counting-notes.md); the flower note:
  [`gamma-le-half-flower-notes.md`](gamma-le-half-flower-notes.md).
- The planning notes: the planning notes for the extension to γ ≤ 1/2 (not included).
- R39: a ruling of the formalization project that fixes a reading of the sources; described where it is used.

**Status words.**
- **PROVED**: a complete proof is written here, or in N1–N3 and confirmed by a referee (then the source is named and
  the status is written REFEREED).
- **CHECKED**: verified by a script of this note unless another source is named, over the stated finite range.
- **SKETCH**: argued, not written in full.
- **OPEN**: not established.

---

## 0. Verdict

**READY.** All seven items set for this note are done. There is no counterexample and no new erratum.

| # | Item | Result | Status |
|---|---|---|---|
| 1 | Exact statements: N2 1.4–1.14, Thm 1.15, Cor 1.16′, Prop 1.17, N3 Thm 6, Lemma 4.1, Lemma 5.2 | §2, in a U-layer extending TVineDefs; each statement carries its status and a Lean name | REFEREED (N1–N3), plus five new lemmas (E, 5′, 5″, 1.7′, A), PROVED |
| 2 | All-size proof of `sumint` (i)–(iii) for the piece chart | **Theorem C** (§3): every T-vine has a chart with unit decoding, local coordinates and exact sumint phases. Corollary C′: (i)–(iii) hold for every (CL) chain with T-vine ingredients | PROVED, given Theorem 6 (REFEREED) and 20 local core and junction facts (CHECKED exhaustively, tabulated). End-to-end check: 0 failures on all T-vines with ≤ 17 atoms |
| 3 | C3 decision | **Unit decoding.** T₁⁻¹ has entries in {0, ±1} by Lemma LPC (leaf-pair cancellation), which is already in Lean on main and family-free. No widening; the frozen `SumintDatum` is untouched. The ±2 of REF1 comes from same-direction differences, which the chart never uses | PROVED; CHECKED |
| 4 | A path-wise alternative to confluence | Confluence is used nowhere. Rung deletion and insertion become **path surgery**: delete or insert one named move of a (Y2)-path (Lemmas E, 5′, 5″). Generation (Lemma 1.7′) is proved by counting triple bonds along the reversed path | PROVED; CHECKED (21,078 surgeries, 0 failures) |
| 5 | T-vine class-count encoding | **Spine code** (Theorem S): Theorem 6's normal form as a finite word. Every T-vine with N atoms is decode(c) for one of at most 2^{4N} codes, orientations included. It reuses `IngCode`'s shape | PROVED (completeness); CHECKED exact (decoded = all shapes) to 19 atoms |
| 6 | `vineest` repairs E2d, E4, E14, E24, E25, E26 re-checked for T-vines | All six transfer. E2d sharpens: **every** core with parallel doubles (B, C or D) has the signed nonlinear form with coreSign = −1, and the printed unsigned form never occurs. The signed `sumint` on main covers it | PROVED (each reduction); E2d sign table CHECKED exhaustively |
| 7 | Exact list of finite facts for the compact checker | §8: seven fact families. The base set is 135 D = 0 instances and 378 D ≤ 1 instances (raw, by position, from Lemma 1.7′'s parameters), 20 local core and junction configurations, and 6 templates with 13 slot facts | CHECKED (sizes and coverage) |

The open remainder (§9) is Lean engineering, not mathematics:
- kernel certificates for the finite facts of §8;
- transport along isomorphisms in Lemma 1.7′;
- a γ-range check on main's E4 mixture lemma, which is proved there unconditionally and is not specific to
  T-vines.

---

## 1. Conventions

**Labels and flow.** These follow the Lean contract `VineParamContract.FullVineChart`, so that the blueprint plugs
into main's sumint consumer.
- B is a T-vine with **upper joint a** (excluded atom, node 𝔲₁) and **lower joint b** (node 𝔲₂).
  n := |B| − 1 and m := (|B| − 5)/2.
- Bond labels k ∈ E (an abelian group), on internal bonds only.
- flow(v) := Σ_out k − Σ_in k. It equals −r at a, +r at b, and 0 elsewhere: this is the fiber `FlowFiber M S a b E r`.
- The external labels at b are g (incoming) and h = g − r (outgoing).
- nodeResonance(v) := Σ_in |k|² − Σ_out |k|² over internal bonds, plus |g|² − |g − r|² at b.

**Directions.** Every combinatorial fact (pieces, cuts, rungs, sub-objects, types, gaps, the cactus) depends only on
the undirected joint-marked multigraph. This is N3 §3.2, PROVED, CONFIRMED by REF3 for the combinatorial facts. Only the
chart (§3) uses directions. So the combinatorics is stated in a **U-layer** of undirected multigraphs (§2.1) and
transported to molecules by the bridge B0.

---

## 2. The statement sheet (item 1)

### 2.1 The U-layer (proposed for the formalization, extending TVineDefs)

All objects live on `TVine.UMultigraph V` (TVineDefs), loopless. Write mult(u, v) for `G.mult s(u,v)`.

| Name (proposed) | Definition |
|---|---|
| `G.deg v` | Σ_{w ≠ v} mult(v, w) |
| `G.cut X` (X ⊆ verts) | Σ_{u ∈ X, w ∉ X} mult(u, w), the number of bond copies of δ(X) |
| `G.ConnOn X` | the induced multigraph on X is connected |
| `IsBlockU G j₁ j₂` | j₁ ≠ j₂ ∈ verts; deg j₁ = deg j₂ = 2; deg v = 4 for every other v; `ConnOn verts`. Interior I := verts ∖ {j₁, j₂}; σ := mult(j₁, j₂) |
| `IsClosureU G j₁ j₂ C` | TVineDefs' `IsClosure`, read in G instead of a molecule |
| `IsTVineU G j₁ j₂` | `IsBlockU` ∧ (∀ u ≠ v, mult(u,v) ≤ 2) ∧ ∃ C C′, `IsClosureU G j₁ j₂ C` ∧ `ReflTransGen Y2Step C C′` ∧ `IsDoubledTriangle C′` |
| `groupGraph M S` | the U-graph on S with mult e := count e (`M.groupBonds S`) |
| `TwoCutSide G X` | ∅ ≠ X ⊊ verts and cut X = 2. Every cut is even, since all degrees are 2 or 4 |
| `SamePieceU G u w` | ∀ X, `TwoCutSide G X` → (u ∈ X ↔ w ∈ X). This is an equivalence relation **by definition**: it is an intersection of "same side of X" relations. This settles point R10 of the [review of TVineDefs](../review/GAMMA-LE-HALF-VINES.md). The **pieces** are its classes, and joints are singleton pieces |
| Γ(B) | the piece quotient: one node per piece, one edge per bond between different pieces |
| `IsTwoCutRung G a b` | a, b ∈ I, a ≠ b, mult(a, b) = 2; G − {a, b} has exactly two components K⁻, K⁺; each of a, b has exactly one bond (a *rail*) into K⁻ and one into K⁺. Rail ends: x^± at a and y^± at b |
| `IsCap` | K⁻ ⊆ {j₁, j₂} or K⁺ ⊆ {j₁, j₂} |
| `Deletable` | `IsTwoCutRung` ∧ ¬`IsCap`; **D(B)** := the number of deletable rungs |
| `G /[μ] {a,b}` | delete a and b, then add x⁻–y⁺ and x⁺–y⁻ (μ = straight) or x⁻–x⁺ and y⁻–y⁺ (μ = crossed). In the molecule the *canonical* matching is the one that respects directions (N2 Def 1.3) |
| `insertRung G e f u v` | for bond copies e = p–q and f = p′–q′ and fresh u ≠ v ∉ verts: replace e by p–u–q and f by p′–v–q′, and add u = v (double) |
| sub-object U = (S_U, k₁, k₂, adj) | S_U ⊊ verts, E(U) = all bonds of G inside S_U. **Block type** (adj = none): deg_U k_i = 2, other degrees 4, `ConnOn`. **Hyper type**: adj = s(k₁,k₂) is a bond of E(U), deg_U k_i = 3, other degrees 4, and E(U) minus one copy of adj is block type. U° := U minus adj; I(U) := S_U ∖ {k₁, k₂} |
| vine-like types | **I**: S_U = {k₁, k₂}, mult 2 (block). **VC:I+I**: S_U = {k₁, c, k₂}, mult(k₁,c) = mult(c,k₂) = 2 (block or hyper). **T**: `IsTVineU` of G[S_U] at (k₁, k₂) (block or hyper). **II** (Q-type): B2's template `IsVine .II` |
| `GapFree G U` | ¬∃ X, δ(X) = {ℓ_in, ℓ_out}, where ℓ_in, ℓ_out are the two bonds of U° at k₁ |
| `rem G U` (removal, sources' semantics) | delete I(U) and the bonds of U°; **keep** k₁, k₂ and adj. This is TARGET L2140, L2104, DH23 L1775, and N3 §2.2 |

**B0 (bridge). PROVED, by unfolding.** `M.IsTVine S j₁ j₂ → IsTVineU (groupGraph M S) j₁ j₂`.
- `IsBlock`'s in-degree 1 and out-degree 1 at the joints give degree 2.
- S is an atomic group, so `groupBonds S` carries every bond.

Conversely, `M.IsBlock S j₁ j₂ ∧ IsTVineU (groupGraph M S) j₁ j₂ → M.IsTVine S j₁ j₂`. Every statement below is
stated in the U-layer and transported through B0.

### 2.2 The statements

Each entry gives the statement, its status and source, and what it is used for. "C →* T" abbreviates
`∃ T′, ReflTransGen Y2Step C T′ ∧ IsDoubledTriangle T′`.
- `X` = (G, j₁, j₂) is a T-vine (`IsTVineU`), with interior I.
- "4-regular" means every vertex has degree 4; closures of blocks are 4-regular.

**N2 Lemma 1.4 (confluence).** On finite loopless multigraphs of maximum degree ≤ 4, (Y)-rewriting has a unique
normal form up to isomorphism.
- *Status:* REFEREED (N2; REF2).
- *Use: none.* §5 replaces every use by path surgery. Lean need not prove it.

**Lemma E (early reduction; new).** Let H be loopless and Q = {a, b} a triple pair of H whose external neighbours
c ≠ d are distinct. Suppose H →* T along the moves P₁, …, P_N, where a move is named by its triple pair. Then
Q = P_k for exactly one k, and H/Q →* T along (P₁, …, P_N) with P_k removed.
- *Status:* PROVED (§5.2); CHECKED.

**Lemma 5′ (rung deletion, path-wise; new).** Let C be loopless and 4-regular, and R = {a, b} a 2-cut rung of C, with
the joints ignored. Suppose C →* T along (P_i). Then R = P_k for exactly one k, and for either matching μ,
C/[μ]R →* T along (P_i) with P_k removed.
- *Status:* PROVED (§5.3); CHECKED.

**Lemma 5″ (rung insertion, path-wise; new).** Same hypotheses, but suppose C/[μ]R →* T along (P_i). Then exactly one
P_j is a *collapse*: the pair of P_j has as its two external bonds the two current "cross bonds" descended from the
new bonds of the deletion. Moreover C →* T along (P₁, …, P_j, R, P_{j+1}, …, P_N).
- *Status:* PROVED (§5.3); CHECKED.

**N2 Lemma 1.5 (rung deletion keeps the class).** Let C be loopless and 4-regular.
- If R is a 2-cut rung of C, then C →* T ⟺ C/[μ]R →* T, for either μ.
- If R is a *cap*, a triple pair with distinct external neighbours, then C →* T ⟺ C/R →* T.
- *Status:* REFEREED (N2) via confluence; PROVED **path-wise** here from Lemmas E, 5′, 5″.
- The Q-class version (N2) is not needed in Lean, since vine (II) stays B2's template.

**N3 Lemma 6.2 (= N2 Lemma 1.6 for T-vines; pendant poles).** `IsTVineU G j₁ j₂ → ¬∃ K₁ K₂ ⊆ I` disjoint and nonempty
with cut K₁ = cut K₂ = 2.
- *Status:* REFEREED (N3 §1.4; REF3). It is already path-wise: it uses only the given (Y2)-path.

**N2 Lemma 1.7′ (generation; confluence-free form).** `IsTVineU G j₁ j₂` iff both of the following hold.
- The closure C is isomorphic to T, to Z_k(T, ℓ) (k ≥ 1), or to Z_{k′}(Z_k(T, ℓ), ℓ′) (k, k′ ≥ 1, ℓ′ a non-triple
  bond copy of Z_k(T, ℓ)). Here Z_k(H, ℓ) is k successive (Z1) moves: the first on ℓ, each later one on a copy of the
  triple bond just created.
- G is C with two bond copies each subdivided by a joint (σ = 0), or one copy subdivided twice (σ = 1), and every
  multiplicity of G is ≤ 2. This forces one joint on a copy of each triple bond.
- *Status:* N2's proof used Lemma 1.4; the confluence-free proof is PROVED in §5.4. N2 §4.2 lists ℓ′ in five position
  classes (ef, eg, conn, rail j, rung j); that list is REFEREED and not needed for the checker.

**N2 Lemma 1.8 (size bound).** `IsTVineU G j₁ j₂ → |verts| ≤ 11 + 2·D(G)`.
- *Status:* REFEREED (N2; REF2). It is tight, CHECKED to 25 atoms by N3.
- *Use:* D = 0 ⇒ ≤ 11 atoms; D ≤ 1 ⇒ ≤ 13 atoms.

**N2 Lemma 1.9 (deletion and insertion stay in the class).**
1. `IsTVineU G j₁ j₂ ∧ Deletable G a b → IsTVineU (G/[μ]{a,b}) j₁ j₂`, for either μ.
2. Suppose `IsTVineU G′ j₁ j₂`, {e, f} is a 2-edge-cut of G′, and both of its sides contain an interior vertex. Then
   G := `insertRung G′ e f u v` satisfies `IsTVineU G j₁ j₂`, {u, v} is deletable, and G/[μ₀]{u,v} = G′ for the
   matching μ₀ undoing the insertion.
- *Status:* REFEREED (N2; REF2), via Lemma 1.5, so now path-wise.
- REF2: (2) must be applied undirected.

**N2 Lemma 1.10 (parity).** Let U be a sub-object and X ⊆ verts. If U is block type, |E(U) ∩ δ(X)| is even. If U is
hyper type, it is odd iff exactly one joint of U lies in X.
- *Status:* REFEREED.

**N2 Lemma 1.11 (joints in rungs).** Let R = {a, b} be a 2-cut rung and U a sub-object with a joint in R. Then either
U = ({a, b}, a, b, none) is the double bond, or U = (K ∪ R, a, b, s(a,b)) for a side K of R with K ∩ {j₁, j₂} = ∅.
In both cases both joints of U lie in R.
- *Status:* REFEREED.

**N2 Lemma 1.12 (container joints).** Let (V, j₁, j₂) be a block with V ∖ {j₁, j₂} connected and no interior cut
vertex. Then no **proper** sub-object of V contains j₁ or j₂.
- *Status:* REFEREED.

**N2 Lemma 1.13 (gap criterion).** Fix the outer data. The gap of U, k(ℓ_out) − k(ℓ_in), is constant on the fiber
iff {ℓ_in, ℓ_out} is a 2-edge-cut. The constant is then 0 or ±r.
- *Status:* REFEREED.
- Lean: take `GapFree` as the definition and prove this lemma only where the analytic side needs it, in the Step-1
  count.

**N2 Lemma 1.14 (Φ).** Let R be a 2-cut rung and U a sub-object with no joint in R. Then:
- (a) R ⊆ I(U) and all four rails are in E(U), or R ∩ S_U = ∅ and no rail is in E(U).
- (b) Φ(U) := (S_U ∖ R, k₁, k₂, adj) is a sub-object of G/R of the same kind.
- (c′) *(N3 §2.1; REFEREED.)* If R is inside the ingredient V_i of U° and R ≠ I(V_i), the type is preserved. If
  R = I(V_i), then V_i is the 4-atom Q-block, Φ turns it into (I), and the gap of Φ(U) is constant. Inside a T-vine the
  second case contradicts (F4) for B/R.
- (d) GapFree Φ(U) in G/R ⇒ GapFree U in G.
- (e) For pairwise disjoint U_i, each all-in or all-out, connectivity of (G/R) ∖ ⋃Φ(U_i) implies connectivity of
  G ∖ ⋃U_i.
- *Status:* REFEREED (N2, N3; REF2, REF3).
- The cap subcase of (c′) uses Lemma E (path-wise) instead of confluence.

**N2 Theorem 1.15 (all sizes).** For every T-vine X:
- (F1) I is connected (DH23 `disjointlem` (i)), and X has no interior cut vertex ((ii)).
- (F2) No proper sub-object contains j₁ or j₂.
- (F3) Every proper vine-like sub-object is of type I, VC:I+I (block or hyper), or T (block or hyper). In particular no
  Q-type ingredient occurs.
- (F4) Every proper vine-like sub-object is GapFree.
- (F5) For every family of pairwise vertex-disjoint proper vine-like sub-objects, X ∖ ⋃U_i is connected.
- (F6) Two overlapping, non-nested proper vine-like sub-objects are double bonds sharing exactly one joint.
- *Status:* REFEREED (N2 with REF2's R1 patch, written in N3 §2.1). Bases CHECKED; §8 lists the minimal base.
- Note: (F5) in N2's stronger "delete adj" semantics also holds for single ingredients; the container statement uses
  the sources' semantics (Cor 1.16′).

**N3 Corollary 1.16′ (`subsetvc`′, sources' removal semantics).** Let Ctr be a container: a vine of 𝒱_enl, an HV, a
VC, an HVC or a DV′. A *member* is a vine-like U ⊊ Ctr with no common ingredient.
- (1) **Location.** Exactly one of:
  - (L-a) U lies in one ingredient V and avoids V's joints;
  - (L-b) Ctr = (V, e*) with σ(V) = 1, and U is the (I) formed by e* and V's joint bond;
  - (L-c) Ctr is a DV′ and U is one of its two vines.
- (2) **List.** In (L-a), U is of type I, VC:I+I (block or hyper) or T (block or hyper) if V is a T-vine, and a rung
  double bond if V is (II).
- (3) **Connectivity.** For every family of disjoint members, `rem` of all of them leaves Ctr connected.
- (4) **Disjointness.** Maximal SG members are pairwise disjoint, except the two vines of a DV′, of which the sources
  keep one.
- **Lemma P (parity).** Let V be a vine with σ(V) = 1 and joint bond f. Let G be V after `rem` of a family of pairwise
  disjoint sub-objects none of which contains j₁ or j₂. If G is connected, then G − f is connected.
- *Status:* REFEREED (N3 §2.2; REF3).

**N2 Proposition 1.17.**
- (a) For a deletable rung R: pieces(G/R) = pieces(G) ∖ {R}, and every surviving 2-cut keeps its gap label (0 or ±r).
- (b) **Piece-shape theorem.** The pieces of a T-vine are {j₁}, {j₂}, exactly one 3-atom **core** with induced bonds
  of shape (B) (triangle with one double bond), (C) (path w₁=w₂=w₃) or (D) (triangle with two double bonds), and m
  2-atom pieces with internal multiplicity 1 or 2, where |verts| = 2m + 5.
- *Status:* REFEREED (N2; REF2). The base, D = 0, is CHECKED (§8, F2).

**N3 Lemma 4.1 (cut-vertex clause redundant).** `IsTVineU G j₁ j₂ → ∀ v ∈ I, ConnOn (verts ∖ {v})`.
- *Status:* REFEREED (N3 §4.1; REF3). It is path-wise: (Z1) preserves 2-connectivity along the given path.

**N3 Lemma 6.1 (cactus).** Γ(B) is a connected loopless cactus: every edge lies on exactly one cycle, and every two
distinct nodes are separated by a 2-edge cut.
- *Status:* REFEREED.

**N3 Lemma 6.3 (attachment units).** Take the block-cut path C₁, A₁, …, A_{t−1}, C_t from b to a. Then Γ − {A₀, …, A_t}
has at most one component (unit).
- *Status:* REFEREED.

**N3 Theorem 6 (layervine structure).** For every T-vine and either joint labelling (v₁, v₂):
- (i) Γ is a cactus all of whose cycles are digons, except at most one triangle.
- (ii) **Spine.** The separating pieces G₁, …, G_r occur in order; consecutive members of (v₂, G₁, …, G_r, v₁) are
  joined by 2 bonds, except at most one pair joined by 1 bond; non-consecutive members are not joined; r = 0 iff
  σ = 1.
- (iii) **Pendant.** The remaining atoms H are empty iff the core is (B) or (C). Otherwise H = Y₁ ∪ … ∪ Y_s is "vine (V)
  minus its joints": Y₁, …, Y_{s−1} are rungs and Y_s is the (D) core. H is attached either (P-a) to the unique
  Γ-degree-6 spine piece (a 2-atom piece with a single internal bond), or (P-b) at the triangle on a single-bond
  consecutive pair.
- (iv) X has at most 3 maximal ladders and at most 13 atoms outside them.
- *Status:* REFEREED (N3 §1; REF3). CHECKED to 41 atoms.

**N2 Lemma 5.2 (𝒱_{>1/2} ⊂ 𝒱_{≤1/2}).** `M.IsVine X S j₁ j₂ → X ∉ {I, II} → M.IsTVine S j₁ j₂`, and `M.IsVine .II`
blocks are Q-type.
- *Status:* REFEREED (N2; REF2). The base (6 templates at k = 0 and 13 slot facts) is CHECKED. The k = 0 templates are
  already **Lean-proved** T-vines, in a check that accompanied TVineDefs (`TVineExamples.lean`, not included; in
  this repository they are `TVine.Struct.Drawn.base_III`, …, `base_VIII`, in
  `WaveTurbulence/Foundations/TVine/Struct/Drawn/Bases.lean`).

**Attachment lemma A (new).** Let P be a non-joint piece of a T-vine and C a cycle of Γ through P. Then the two
C-edges at P are incident to two **distinct** atoms of P.
- *Status:* PROVED here.
- *Proof.* Suppose both are at w ∈ P. Let K be the side of the 2-cut {those two edges} not containing P.
  - δ(K) consists of exactly these two edges, both at w. So w's other two bonds leave K ∪ {w}, and
    cut(K ∪ {w}) = 4 − 2 = 2.
  - K ∪ {w} meets P only in w, and P has ≥ 2 atoms. So this 2-edge cut separates w from another atom of P, which
    contradicts the definition of pieces. ∎
- **Consequences** (used in §3 and §6), by the degree count of each piece shape (Prop 1.17(b)):
  - a 2-atom piece of Γ-degree 4 has one bond of each of its two cycles at each atom;
  - the degree-6 piece (the *junction*) has one bond of each of its three cycles at each atom;
  - in a (B) core x=y, y–z, x–z, z carries one entry and one exit bond, and x and y one each;
  - in a (C) core w₁=w₂=w₃, each of w₁ and w₃ carries one entry and one exit bond;
  - in a (D) core p=r, r=q, p–q, p and q carry the two bonds of its only cycle.

---

## 3. The piece chart and the all-size proof of `sumint` (i)–(iii)

### 3.1 What has to be proved

TARGET Prop `sumint` (L1595–L1625; frozen as `SumintDatum`) is applied in `vineest` (L1742–L1925) to a (CL) vine chain
U = U¹ ∘ ⋯ ∘ U^I. Its variables and hypotheses are as follows.

**Input variables x.** For each unit i:
- a bad unit has x₀ⁱ and the pairs (x_jⁱ, y_jⁱ);
- a normal unit has x₀ⁱ, the pairs (x_jⁱ, y_jⁱ) for j ≤ m_i, and the core variables (u₁ⁱ, u₂ⁱ, u₃ⁱ); so n_i = 2m_i + 4.

**Alternative variables.** k (the leaf-pair bonds of the garden realization) and ℓ (the tree bonds).

**Hypotheses.**
- (i) k = T₁x + h₁ and ℓ = T₂x + h₂, where T₁, T₁⁻¹, T₂ have entries in {0, ±1} and h₁, h₂ depend only on (e,f,g,h).
- (ii) The ℓ's satisfy a predecessor chain with ∏Λ ≤ C₀^M.
- (iii) Every input variable is the difference of two of (k, ℓ, e, f, g, h).

**Phase normal form.**
- joint: ⟨r, x₀⟩;
- each pair: ⟨x_j, y_j⟩ at s_j and ⟨x_j, y_j⟩ + ⟨r, ζ_j⟩ at t_j, with ζ_j = a x_j + b y_j + c r and a, b, c ∈ {0, ±1};
- core: ⟨u₁, u₂⟩, Λ ∈ {⟨u₁,u₃⟩, ⟨u₃, u₁+u₂−u₃⟩} and ⟨r, ξ⟩, with ξ unit. These are read **signed** (E2d; main
  `SumintSigned`).

On main the molecule half of this is the contract `FullVineChart` (Contract.lean), and the garden half is the
consumer `VineEstS2`:
- unit decoding gives T₁ and T₂ (`free_unit`);
- `chart` being an equivalence over every abelian group gives T₁ ∈ GL(ℤ);
- `difference` gives (iii);
- the phase fields give the normal form;
- the garden supplies (ii) (`clOrderedPrev`, DH21 Lemma 6.6) and T₁⁻¹ (`exists_chainInverseRow`, from local
  differences; §4).

So the task is: **produce, for every T-vine and both joint labellings, a chart with exactly these fields.**

### 3.2 Theorem C (the piece chart; every T-vine, every size). PROVED

**Theorem C.** Let `M.IsTVine S a b`, with a the upper joint and b the lower joint, n = |S| − 1 and m = (|S| − 5)/2.
There is a chart with the fields of `FullVineChart`, de-indexed from `VineType`, as follows.

- **(C0) Indexing.**
  - Fin n ≃ S ∖ {a}, with the slot x₀ ↦ b.
  - The m pair slots are the 2-atom pieces: xSlot j ↦ t-atom and ySlot j ↦ s-atom.
  - The three core slots are the atoms (w_a, w_b, w_c) of the core.
  - `junction : Option (Fin m)` is the index of the Γ-degree-6 piece when the pendant is attached (P-a), and none
    otherwise.
  - bondsBetween is 2 on each pair, and 1 on the junction.
- **(C1)** For every abelian group E and g, r ∈ E, `chart g r : FlowFiber M S a b E r ≃ (Fin n → E)`.
- **(C2) Unit decoding.** k_e = g + Σ_i D_{e,i} x_i + c_e r, with D_{e,i} ∈ {0, ±1} and c_e ∈ ℤ.
- **(C3) Locality.** Every coordinate is origin(p) − origin(q) for two incidences p, q of **opposite direction at one
  atom** (`OriginAt p v out ∧ OriginAt q v (!out)`).
  - x₀ = h − k(in-bond at b);
  - the pair coordinates are local at the s-atom;
  - u₁ and u₂ are local at w_a, and u₃ at w_b.
- **(C4) Exact phases.**
  - joint: nodeResonance(b) = 2⟨r, x₀⟩;
  - pair: nodeResonance(s) = −2⟨x_j, y_j⟩ and nodeResonance(t) = 2⟨x_j, y_j⟩ + 2⟨r, ζ_j⟩, with ζ_j unit;
  - core: nodeResonance(w_a) = 2σ₁⟨u₁, u₂⟩, and nodeResonance(w_b) = 2σ₁⟨u₁, u₃⟩ (`coreLinear`) or
    2σ₁σ₂⟨u₃, u₁+u₂−u₃⟩; Σ_core = 2⟨r, ξ⟩ with ξ unit.
  - Moreover `coreLinear` holds iff the core's double bond(s) are anti-parallel, and σ₂ = −1 whenever it fails
    (§7, E2d).
- **(C5)** The number of internal bonds is 2n.

**Proof.**

*Step 0: structure.*
- Fix b as the root of the block-cut tree of Γ (N3 Lemma 6.1).
- Every non-joint piece P has a unique **entry cycle** C_P, the first cycle on the path from P to b.
- Its two C_P-edges at P are its **entry pair**; its other cycles are **exit** cycles. By the 2-cut relation (Lemma D
  of N1; REFEREED), across each cycle's 2-cut net flow ρ ∈ {0, ±r} passes toward a. It is ±r for a spine cut and 0
  for a pendant cut.
- By Theorem 6 and Lemma A, every non-joint piece is in exactly one of six **local configurations**:

| config | piece | cycles at P (gaps) | atoms carrying the cycle bonds |
|---|---|---|---|
| L1 | rung (2 atoms, double bond) on the spine | entry ρ, exit ρ | each atom one entry, one exit (Lemma A) |
| L2 | rung in the pendant | entry 0, exit 0 | same |
| L3 | junction (2 atoms, single bond, P-a) | entry ρ, exit ρ, pendant 0 | each atom one bond of each cycle |
| L4 | core (B) on the spine | entry ρ, exit ρ | z: entry and exit; x: entry; y: exit |
| L5 | core (C) on the spine | entry ρ, exit ρ | w₁ and w₃: each one entry and one exit |
| L6 | core (D), end of the pendant | entry 0 | p and q one each |

The triangle of (P-b) needs no configuration of its own: its three bonds are entry or exit pairs of the three pieces
on it. The (B) and (C) cores lie on the spine, and the (D) core ends the pendant (Thm 6(iii)).

*Step 1: local charts (Prop L).*
- Give the entry pair the labels κ + ρ (the bond into P) and κ (the bond out of P).
- Unknowns: P's internal bonds and its exit bonds. Equations: conservation at P's atoms and the 2-cut relation of each
  exit cycle.
- **Prop L.** For each configuration and each balanced orientation there are coordinates, 2 for a 2-atom piece and 3
  for a core, each a local opposite difference at an atom of P, such that:
  - the solution map E^{c_P} → (unknown labels) is an affine bijection over every E;
  - every label is κ + (a {0, ±1}-combination of P's coordinates) + (an integer)·ρ;
  - the local phases are exact and **free of κ**: for 2-atom pieces Γ_s = −2⟨x, y⟩ and Γ_s + Γ_t = 2⟨ρ, ζ⟩ with ζ unit
    in (x, y, ρ); for cores, the core forms above with ξ unit in (u, ρ).
- For L1 and L2 the proof is written out below. For L3–L6 Prop L is CHECKED exhaustively (`local_pieces.py`):
  - 6 + 6 + 4 + 4 = **20 configurations × orientations**, every coordinate choice tried, at least one good choice in
    each;
  - one explicit good chart per configuration is printed in `out_local_tables.txt`. These are the Lean `decide` cases
    of §8, F7.
  - For 2-atom pieces **both** choices of s work in every configuration.

*Rungs (L1, L2), by hand.* Let P = {p, q}. Name the entry bond into P e₁, at p (Lemma A), and the entry bond out of P
f₁, at q.
- **Straight** (d: q→p, d′: p→q). Balance forces p's exit bond to be outgoing (e₂) and q's to be incoming (f₂).
  - Take s = p, x := k_{d′} − k_{e₁}, y := k_{d′} − k_d.
  - Labels: k_{e₁} = κ+ρ, k_{d′} = κ+ρ+x, k_d = κ+ρ+x−y, k_{e₂} = κ+ρ−y, k_{f₂} = κ−y, k_{f₁} = κ.
  - Conservation at q holds: (κ+ρ+x−y) + κ = (κ+ρ+x) + (κ−y). The exit relation k_{e₂} − k_{f₂} = ρ holds.
  - Γ_p = −2(o₁−i₁)·(o₁−i₂) with (o₁, i₁, i₂) = (d′, e₁, d), that is, −2⟨x, y⟩.
  - Σ_P Γ = (|e₁|²−|f₁|²) + (|f₂|²−|e₂|²) = 2⟨ρ, y⟩, so ζ = y.
- **Turn** (d₁, d₂: p→q; the opposite turn is excluded, since e₁ enters p). Balance forces f₂ (incoming) at p and e₂
  (outgoing) at q.
  - Take x := k_{d₁} − k_{e₁}, y := k_{d₁} − k_{f₂}.
  - Labels: k_{e₁} = κ+ρ, k_{d₁} = κ+ρ+x, k_{f₂} = κ+ρ+x−y, k_{d₂} = κ+ρ−y, k_{e₂} = κ+2ρ+x−y, k_{f₁} = κ.
  - Γ_p = −2⟨x, y⟩ and Σ_P Γ = −2⟨ρ, ρ+x−y⟩, so ζ = −x + y − ρ.
- In both cases every label is unit in (x, y), and the map (x, y) ↦ labels is affine-bijective with inverse given by
  integer differences. ∎(L1, L2)

*Step 2: gluing.* Define the coordinates piece by piece in the block-cut order from b, and the labels recursively.
1. At b: k_in(b) := g − r − x₀ and k_out(b) := g − x₀. So flow(b) = r and x₀ = h − k_in(b).
2. When the root piece of a cycle C is labelled, its C-bonds are known. The remaining bond of a triangle gets its label
   from the 2-cut relation of that triangle: k_f = k_e − flow(X), with coefficient +1 on k_e because one of e, f
   leaves X and the other enters.
3. Every other piece P on C then has its entry pair labelled with the shape (κ_P + ρ, κ_P). Apply Prop L, and recurse
   on P's exit cycles.

The result has the following properties.
- **It lies in the fiber.** Conservation holds at every non-joint atom (Prop L) and at b (by 1). It holds at a because
  Σ_v flow(v) = 0. On the triangle, the three 2-cut relations are dependent: they sum to the flow balance of the
  middle side. So the relation imposed in 2 is consistent with the one used in Prop L at the far node.
- **It is a bijection over every E.**
  - Given the coordinates, the labels are forced step by step (uniqueness in Prop L).
  - A fiber element restricted to P satisfies P's local system, since conservation and the 2-cut relations hold in
    the fiber (Lemma D).
  - The coordinates are integer differences of labels.
  - So the inverse is integer-affine. This gives (C1).
- **(C2).** By induction along the order, every label in P's region is g + Σ_{Q ≼ P} U_Q + c·r. Here the sum runs over
  the pieces on the block-cut path from b to P, each U_Q is a unit combination of Q's own coordinates, and the
  coefficient of g is 1 because every step adds labels with coefficient +1. Distinct pieces have disjoint coordinates,
  so every coefficient lies in {0, ±1}.
- **(C3)** comes from Prop L, and x₀ is local at b.
- **(C4)** follows from the next identity.
  - For v ∈ P, write each label at v as κ_P + w_e. Then nodeResonance(v) = 2⟨κ_P, Σ_in w − Σ_out w⟩ + (Σ_in|w|² −
    Σ_out|w|²).
  - The first term vanishes by conservation at v, which has #in = #out = 2.
  - So nodeResonance(v) is exactly Prop L's local phase, with ρ = ±r on the spine and 0 in the pendant. The sign of ρ
    is absorbed into ζ and ξ, which stay unit.
  - At b, (C4) is the computation in 1.
- **(C5).** A block with |S| atoms has 2|S| − 2 = 2n internal bonds. ∎

*Dependencies.* Theorem 6, Prop 1.17(b) and Lemma D are REFEREED. Lemma A is PROVED in §2. Prop L is PROVED for L1 and
L2 and CHECKED exhaustively for L3–L6. No induction on rungs is needed beyond the one inside Prop 1.17(b).

**Corollary C′ (TARGET `sumint` (i)–(iii) for T-vine chains). PROVED.** Let U be a (CL) vine chain whose ingredients
are in 𝒱_{≤1/2}. Its bad ingredients (I) and (II) carry TARGET's charts (A) and (B), and its T-vine ingredients carry
Theorem C's chart. Then in any garden realization the assembled variables satisfy (i), (ii), (iii) and the phase
normal form (signed core), with n_i = 2m_i + 4 for every T-vine unit.
- **(i), T₁ and T₂.** Their rows are bond labels: unit by (C2) and TARGET (A-i). Chaining keeps them unit: the g of
  unit i is a label of unit i − 1, and coordinates of different units are disjoint. This is main's
  `chainDecodeFree_unit` argument, which is family-free.
- **(i), T₁ ∈ GL(ℤ),** by (C1).
- **(i), T₁⁻¹ unit,** by Lemma LPC (§4) applied to (C3).
- **(ii)** is garden-level (DH21 Lemma 6.6; main `clOrderedPrev`).
- **(iii)** by (C3). ∎

### 3.3 Checks

| script | what | result |
|---|---|---|
| `local_pieces.py` | Prop L on all 28 local configurations: L1 and L2, 4 orientations each; L3–L6, 20; every choice | every configuration has a good chart; both s-choices for every 2-atom piece; explicit tables in `out_local_tables.txt` |
| `chart_check.py 11 4 3` | the global construction of Step 2, every choice, all 526 directed T-vines with ≤ 11 atoms, both labellings (1,052 cases) | 0 failures. Checked: conservation, integrality, g-coefficient 1, unit decoding, encode∘decode = id, n coordinates, locality (asserted), exact joint, pair and core phases, ζ and ξ unit. T₁⁻¹ unit on 4,208 random garden trees |
| `chart_check.py 15 3 7 fast` | the same, first good chart per case, all 4,446 directed T-vines with ≤ 15 atoms (8,892 cases) | 0 failures; T₁⁻¹ unit on 26,676 random spanning trees |
| `chart_check.py 17 2 11 fast` | the same, all 11,910 directed T-vines with ≤ 17 atoms (23,820 cases) | 0 failures; T₁⁻¹ unit on 47,640 random spanning trees |

Any spanning tree of the vine rooted at a is the tree-bond set of some garden realization: give each atom the sign
read off its parent bond, and the child signs (ζ, −ζ, ζ) are then forced by balance. So random spanning trees test
Lemma LPC in its full generality.

---

## 4. The C3 decision: unit decoding

**Decision: keep the unit contract.** Keep `free_unit`, so bond labels are {0, ±1}-combinations of the coordinates,
and keep the frozen `SumintDatum.T_unit` (T₁, T₁⁻¹, T₂ unit) unchanged. Widening to entries ±2 is not needed and is not
recommended.

**Lemma LPC (leaf-pair cancellation). PROVED; in Lean on main, family-free.** Setting:
- a plain garden and a (CL) block or chain region with boundary nodes 𝔲₁, 𝔲₁₁, 𝔲₂₁, 𝔲₂₂ (DH23 Prop `block_clcn`);
- a decoration κ with κ_𝔫 = κ_{𝔫1} − κ_{𝔫2} + κ_{𝔫3} at branching nodes, child signs (ζ_𝔫, −ζ_𝔫, ζ_𝔫), and equal
  labels on internal leaf pairs.

For any two bonds p, q at one atom 𝔫 with **opposite** incidence, k_p − k_q is a {0, ±1}-combination of the internal
leaf-pair labels and the boundary labels.

*Proof.*
- Put s(𝔪) := ζ_𝔪 κ_𝔪. Then s(𝔫) = s(𝔫1) + s(𝔫2) + s(𝔫3), and s(ℓ) + s(ℓ′) = 0 for an internal leaf pair.
- Hence s(𝔪) is the sum of s(λ) over the internal leaves λ below 𝔪 whose partner is not below 𝔪, plus s of the
  boundary nodes (𝔲₂₁, 𝔲₂₂) below 𝔪. The internal pairs with both leaves below 𝔪 cancel.
- At the atom 𝔫, with ε = +1 for outgoing and −1 for incoming, the signed labels εk of its four bonds are −s(𝔫) for
  the parent bond and s(𝔫c) for the child bonds. Indeed, the parent bond is outgoing iff ζ_𝔫 = −1, and a child bond
  is outgoing iff ζ_𝔫c = +1.
- An opposite difference is k_p − k_q = ε_p k_p + ε_q k_q, the sum of two of these four signed labels. That is either
  s(𝔫c) + s(𝔫c′) or −s(𝔫) + s(𝔫c) = −(s(𝔫c′) + s(𝔫c″)). Either way it is ± the sum of s over the union of two child
  subtrees.
- So each internal leaf-pair label enters with coefficient ±1 if exactly one of its two leaves is in the union, and 0
  otherwise. ∎

A **same-direction** difference k_p − k_q = s(·) − s(·) doubles the pairs that straddle it, which produces ±2.
- In Lean this is `VineEstS2.clLocalOrigin_difference_coeffs`. Its hypotheses are `IsBlock`, `CLRegionData` and
  `IsPlain`; it mentions no `VineType`.
- Applied to the coordinates of `exists_chainInverseRow`, it gives T₁⁻¹ unit with **no inverse-unit premise**.

**Why the decision is safe.**
1. Theorem C gives unit decoding and locality (C3) for **every** T-vine. So T₁⁻¹ is unit by LPC, and every
   hypothesis of the frozen `SumintDatum` is met as stated.
2. REF1's C3 caveat ("T₁⁻¹ entries in {0, ±1, ±2}") is the crude bound for a difference of two bonds. A ±2 is
   attained only by a same-direction difference:
   - CHECKED: of 1,320,944 same-direction differences at atoms of T-vines with ≤ 17 atoms, on random garden trees,
     669,837 (51%) have a ±2;
   - of the chart coordinates, which are local and opposite, none do (47,640 trees, 0 failures).
   The chart never uses a same-direction difference. TARGET's core coordinates in (C-i) and (C-ii) are not required
   to be local. The chart uses local opposite differences instead, which exist for every core configuration
   (Prop L).
3. Widening would require a new `sumint` variant, since `SumintDatum` is frozen under D7, and a re-check of its sealed
   consumer. It buys nothing.

**Lean-facing consequence (for the formalization of the chart).** De-index `FullVineChart` from `VineType` and keep
every field, with two changes:
- `junction : Option (Fin m)` becomes "some iff the pendant is attached P-a";
- `junction_type` (now `isSome = decide (X = .VII)`) becomes that equivalence.

`coreLinear`, `coreFirstSign` and `coreSign` are kept. Main's
`clVineChart_hasLocalDifferences`, `clLocalOrigin_difference_coeffs`, `exists_chainInverseRow` and
`chainDecodeFree_unit` read only the contract fields, so they carry over once `X : VineType` is replaced by the
de-indexed chart.

---

## 5. A path-wise alternative to confluence

### 5.1 Where confluence was used, and what replaces it

TVineDefs defines T-vines through *some* (Y2)-path, `ReflTransGen Y2Step`, not through the normal form. Every use of
N2 Lemma 1.4 then turns into a statement about one given path.

| Statement | Use of Lemma 1.4 in N2/N3 | Confluence-free replacement |
|---|---|---|
| N2 Lemma 1.5 (rung deletion keeps the class) | "by Lemma 1.4 we may start with the (Y2) at R"; poles reduced "in parallel" | Lemmas 5′, 5″ (path surgery), and E for caps |
| N2 Lemma 1.7 (generation) | "by Lemma 1.4 the reduction consists of (Y2) moves only"; "at most two sequences" | Lemma 1.7′ (§5.4): the path is (Y2) by definition, and the triple count is read off the reversed path |
| N2 Lemma 1.9 (deletion and insertion) | via Lemma 1.5 | via Lemmas 5′, 5″ |
| N2/N3 Lemma 1.14(c′), cap subcase | "cl(V) → cl(V/R) by one (Y2), and Lemma 1.4 applies" | Lemma E (one direction) and prepending the move (the other) |
| N2 Lemma 4.2 (ylem1′ list; used in the counting note) | Lemma 1.4 plus the counting of 1.7 | Lemma 1.7′ |
| Thm 1.15, Prop 1.17, Cor 1.16′ | only through Lemma 1.9 | — |
| N3 Lemma 6.2, N3 Lemma 4.1 | none (already path-wise; REF3) | — |

So **Lean never needs Newman's lemma or uniqueness of normal forms.** What it needs is the path-surgery lemmas, over a
list-of-pairs representation of paths:
- `Y2At G {a,b} G′`: the move at the triple pair {a, b}, with its externals read off G;
- `Y2Path G (ps : List (Sym2 V)) G′`, defined inductively;
- the equivalence `ReflTransGen Y2Step G G′ ↔ ∃ ps, Y2Path G ps G′`.

The `runMoves` of TVineCert, the certificate checker that accompanied TVineDefs (now in
`WaveTurbulence/Foundations/TVine/Struct/Drawn/Cert.lean`), already implements such a path with explicit quadruples
(a, b, c, d). Surgery changes the externals of later moves, so the pair form is the right one.

### 5.2 Lemma E (early reduction of a triple bond). PROVED

**Statement.** Let H be a finite loopless multigraph and Q = {a, b} a (Y2) pair of H: mult(a,b) = 3, a has exactly
one further bond (to c), b has exactly one (to d), and c ≠ d. Suppose `Y2Path H (P₁,…,P_N) T′` with T′ a doubled
triangle. Then:
- Q = P_k for exactly one k;
- `Y2Path (H/Q) (P₁,…,P_N with P_k removed) T′`.

**Proof.**
- **(E0) Invariants.** A move deletes its pair and replaces the two external bonds p′–p, q′–q by p′–q′. So the degree
  of every surviving vertex is unchanged, and the multiplicity between two surviving vertices never decreases.
  - While a and b survive, mult(a,b) ≥ 3, and a and b keep degree 4.
  - If mult(a,b) ever became 4, then {a, b} would be a closed component on which no move acts (a move needs
    multiplicity exactly 3). It would survive to the end, which is not T′.
  - So on a path to T′, mult(a,b) = 3 while a and b survive, and each keeps exactly one further bond.
- **(E1) Q occurs exactly once.**
  - T′ has no triple bond, so a and b do not both survive to the end.
  - A move deleting a is at a triple pair containing a, and by (E0) that pair is {a, b}.
  - Hence exactly one P_k equals Q.
- **(E2) Surgery,** by induction on k. If k = 1, the claim is the tail of the path. Let k > 1 and P₁ = {p, q}, with
  externals p′, q′. P₁ is disjoint from Q, since a vertex lies in at most one triple pair. There are three cases.
  - (α) **No bond joins P₁ and Q.**
    - Then c, d ∉ P₁, so P₁ is a move of H/Q, and (H/Q)/P₁ = (H/P₁)/Q.
    - In H/P₁, Q is still a (Y2) pair with externals c, d.
    - By induction (H/P₁)/Q →* T′ along the rest of the path without Q.
  - (β) **Exactly one bond joins them,** say p–a. So p′ = a and c = p.
    - In H₁ := H/P₁ the pair Q has externals q′ and d.
    - If q′ = d, Q can never be reduced: d keeps one bond to a and one to b while Q survives, so it has at most 2 bonds
      to anything else and is never in a triple pair. Q then survives to the end, a contradiction. So q′ ≠ d.
    - By induction, H₁/Q →* T′.
    - In H/Q the pair P₁ is triple with externals d (through the new bond p–d) and q′, which are distinct.
    - (H/Q)/P₁ = H − Q − P₁ + d–q′ = H₁/Q.
  - (γ) **Two bonds join them.** Then {p, q, a, b} is a closed component. The move at P₁ makes a≣b quadruple, which
    survives forever, a contradiction. ∎

### 5.3 Lemmas 5′ and 5″ (rung deletion and insertion as path surgery). PROVED

**Setting.**
- C is loopless with deg a = deg b = 4.
- R = {a, b} is a 2-cut rung: mult(a,b) = 2, and C − R has exactly two components K⁻, K⁺.
- The rails are a–x^± and b–y^±, with x^±, y^± ∈ K^±.
- C/[μ]R is defined in §2.1.
- C ≠ T′, because δ(K⁻) = {a–x⁻, b–y⁻} is a 2-edge cut and T has edge-connectivity 4.

**Lemma 5′.** If `Y2Path C (P₁,…,P_N) T′`, then:
- R = P_k for exactly one k;
- for either μ, `Y2Path (C/[μ]R) (P_i)_{i≠k} T′`.

*Proof,* by induction on N.
- P₁ ∩ R = ∅, since a and b have multiplicity ≤ 2 with every vertex. So P₁ lies in one pole, say K⁻. Let its externals
  be p′, q′.
- **(i) p′, q′ ∉ R.** Then p′, q′ ∈ K⁻.
  - In C/P₁, R is still a 2-cut rung, with poles K⁻ ∖ P₁ (joined by the new bond p′q′) and K⁺, and with the same
    rails, since x⁻, y⁻ ∉ P₁.
  - P₁ is a move of C/R, and (C/R)/P₁ = (C/P₁)/R.
  - Induct.
- **(ii) Exactly one external is in R,** say p′ = a. So p = x⁻, and q′ ∈ K⁻ ∖ P₁.
  - In C/P₁, R is a 2-cut rung with a's K⁻-rail moved to q′. Its pole K⁻ ∖ P₁ still contains y⁻ and is connected:
    P₁ hung from it by the one bond q–q′.
  - In C/[μ]R the pair P₁ is triple with externals q′ and the far end of p's new bond, which lies in K⁺. They are
    distinct.
  - (C/R)/P₁ = (C/P₁)/R, with the same μ.
  - Induct.
- **(iii) Both externals are in R.** Then K⁻ = P₁ = {x⁻, y⁻} (the pole collapses).
  - C/P₁ has a≡b triple, with externals x⁺, y⁺.
  - If x⁺ = y⁺, the triple can never be reduced, as in E(β), a contradiction.
  - So {a, b} is a (Y2) pair of C/P₁. Lemma E gives (C/P₁)/R →* T′ along P₂, …, P_N with R removed, and R occurs
    there exactly once.
  - In C/[μ]R the pole K⁻ is a triple pair with externals {x⁺, y⁺}, for either μ, and
    (C/R)/K⁻ = C − R − K⁻ + x⁺y⁺ = (C/P₁)/R. ∎

**Lemma 5″.** If `Y2Path (C/[μ]R) (P₁,…,P_N) T′`, call the two bonds joining the poles *cross bonds*. A move inside a
pole with one external cross bond replaces that cross bond by the new bond it creates. Then:
- exactly one P_j has both of its external bonds equal to the current cross bonds (the *collapse*);
- `Y2Path C (P₁,…,P_j, R, P_{j+1},…,P_N) T′`.

*Proof.* Mirror the cases of 5′.
- (i) and (ii) are mirrored move for move, keeping R a 2-cut rung of the current C-graph.
- (iii), the collapse, becomes two moves in C: first P_j makes a≡b triple with externals x⁺ ≠ y⁺ (they are distinct
  because P_j is a valid move in C/R); then R produces (C/R)/P_j.
- Until the collapse the cross bonds form a 2-edge cut, so the path cannot end before it. ∎

**Consequences.**
- N2 Lemma 1.5: (⇒) is 5′, (⇐) is 5″, and the cap case is Lemma E together with prepending the move.
- N2 Lemma 1.9: (1) by 5′ applied to cl(B), since a non-cap 2-cut rung of B is a 2-cut rung of cl(B) with
  cl(B/R) = cl(B)/R (N2's argument); (2) by 5″.
- N3 Lemma 1.14(c′): the cap subcase uses E.

All of these are **constructive**: the new path is the old one with a single named move deleted or inserted.

### 5.4 Lemma 1.7′ (generation without confluence). PROVED

**Statement.** Let C be a finite loopless multigraph with at most two triple pairs and `Y2Path C ps T′`. Then
C ≅ T, or C ≅ Z_k(T, ℓ) with k ≥ 1, or C ≅ Z_{k′}(Z_k(T, ℓ), ℓ′) with k, k′ ≥ 1 and ℓ′ a non-triple bond copy of
Z_k(T, ℓ).

**Proof.**
- **Reverse the path.** Write G_N = T′ and G_{t−1} = Z1(G_t, β_t): a (Z1) move subdividing one copy of the bond
  β_t = c_t–d_t created by the t-th move, which turns c–d into c–a, a≡b, b–d with a, b fresh.
- **Count triples.** Let τ(G) be the number of triple pairs. Then τ(G_{t−1}) = τ(G_t) + 1 − [β_t is a copy of a
  triple bond of G_t]. A (Z1) creates exactly one triple pair, lowers exactly the multiplicity of β_t, and creates only
  single bonds to fresh vertices; no multiplicity ever exceeds 3.
- **Starts and extensions.** Since τ(T) = 0 and τ(C) ≤ 2, at most two reverse steps are *starts* (β_t not a triple
  copy). The first step from T′ is a start. Every other step is an *extension*: it acts on a copy of the triple bond
  of the **ladder** that triple belongs to. At any time there are at most two ladders, each with exactly one current
  triple pair.
- **Reorder.** Move every ladder-1 operation before ladder 2's start, keeping the relative order within each ladder.
  - Each swap exchanges a ladder-2 operation with a later ladder-1 operation that acts on a different bond occurrence.
    Ladder 1 acts only on copies of its own triple; ladder 2 acts on ℓ′ (a non-triple bond) or on copies of its own
    triple.
  - Ladder-2 operations never create or destroy a copy of ladder 1's triple, and ladder-1 operations never delete ℓ′
    or a ladder-2 triple copy.
  - So every swapped operation is still applicable, and (Z1) operations on distinct bond occurrences, with the same
    fresh names, commute exactly.
- **Conclusion.**
  - The reordered sequence builds Z_k(T, ℓ) and then Z_{k′}(·, ℓ′). The multiplicity of the pair ℓ′ is never raised
    by ladder-1 operations, which create only bonds to fresh vertices, so ℓ′ is a non-triple bond copy of Z_k(T, ℓ).
  - All bond copies of T are equivalent under Aut(T), so ℓ needs no parameter. ∎

N2's joint-placement clause and Lemma 1.8 then follow as in N2: they use only the ladder structure. In Lean the
isomorphism "≅" should be produced as an explicit `Equiv` onto a generated instance on `Fin N` (§8, F1); it never
needs canonical forms.

### 5.5 Checks

`pathwise_check.py 21 6 5` (`out_pathwise_21.txt`) ran on all 170 closures with ≤ 21 atoms, with 6 random (Y2)-paths
each (1,020 paths, every one ending at T). For every (Y2) pair, every 2-cut rung and both matchings, it
**implemented the surgery** and replayed the new path:

| surgery | cases | ok |
|---|---|---|
| Lemma E | 1,974 | 1,974 |
| Lemma 5′ (delete R) | 9,552 | 9,552 |
| Lemma 5″ (insert R after the collapse) | 9,552 | 9,552 |

---

## 6. The T-vine class-count encoding

### 6.1 What the class count needs

TARGET L2238–L2252 counts the canonical layered gardens. "By adding back at most C₀ρ̄ disjoint VC's in 𝒱₀ … we get at
most C₀ⁿ(C₀ρ̄)! choices for 𝕄(𝒢_sk)". This is `Stage1Counts` (iv), ruling R39 (the exact statement of the stage-1
class count). Lean (`WaveTurbulence/Foundations/Stage1/ClassCount/`) proves it by an injective code per VC ingredient:
- `IngCode = (X : VineType, k : slot rung counts, swap, o : orientation bits)`;
- the decoder `ingArcs` (the expanded template, relabelled);
- the bound `card_ingCodesAt_le' : #codes with w + 1 atoms ≤ (2⁴¹)^w`;
- the bookkeeping `vine_card_m` (|S| = 2m + 5 for normal vines) and a realization-independent incoherency index
  (`realizedIncoherencyIndex_any`).

For T-vines the template list is replaced by the **spine code**, which is Theorem 6's normal form written as a finite
word.

### 6.2 The spine code

The pieces are those of §2.1. Each piece type has named **entry atoms**, **exit atoms** and, for the junction,
**pendant atoms**. Lemma A fixes these.

| type | atoms, internal bonds | entry atoms | exit atoms |
|---|---|---|---|
| R (rung) | p=q | (p, q) | (p, q) |
| B (core) | x=y, y–z, x–z | (z, x) | (z, y) |
| C (core) | w₁=w₂, w₂=w₃ | (w₁, w₃) | (w₁, w₃) |
| J (junction) | p–q | (p, q) | (p, q); pendant atoms (p, q) |
| D (core, pendant end) | p=r, r=q, p–q | (p, q) | — |

**Code.** c = (w, s, att, β, o, swap):
- w ∈ {R, B, C, J}^r is the spine word;
- s ≥ 0 is the pendant length;
- att is the attachment: (P-a, the position of J in w) or (P-b, a step i ∈ {0, …, r}). Exactly one core occurs: a B or
  C in w with s = 0, or the D at the end of a pendant with s ≥ 1;
- β is one matching bit per digon, per triangle corner and per attachment;
- o is one orientation bit per bond;
- swap orders the joints.

**decode(c).** Place a = 0, b = 1, then the spine pieces, then the pendant chain Y₁ = ⋯ = Y_{s−1} = D.
- Join consecutive members by their exit and entry atoms, with the matching given by a bit.
- At the step att = (P-b, i), join members i and i+1 by one bond, and join each to the pendant top Y₁ by one bond
  (the triangle; 3 bits).
- At att = (P-a, j), join J's pendant atoms to Y₁.
- Orient the bonds by o.

The decoder is an explicit `List (ℕ × ℕ)` function, like `ingArcs`.

**Theorem S (spine code). PROVED (completeness); CHECKED (completeness and soundness, exact).**
1. **Completeness.** For every T-vine (S, a, b) with N atoms there is a code c of size N and a relabelling f : S → ℕ,
   injective on S, with f(a) = 0, f(b) = 1 and image range N, mapping the group bonds of S, with their directions, onto
   decode(c). This is the `IsVine`-style realization.
2. **Count.** #{codes of size N, before o and swap} ≤ 3(m+2)²·2^{m+2} ≤ N²·2^N, where N = 2m + 5. With the 2^{2N−2}
   orientation bits and the swap bit: **#codes ≤ 2^{4N}**, since N² ≤ 2^{N+1}.

*Proof of 1.*
- By Theorem 6 (labelling v₂ = b, v₁ = a) the quotient Γ is the spine (v₂, G₁, …, G_r, v₁), with digons and at most one
  triangle, plus at most one pendant chain ending in the (D) core, attached P-a or P-b.
- By Prop 1.17(b) every non-joint piece has one of the shapes R, B, C, J, D. A 2-atom piece of multiplicity 1 has
  Γ-degree 6, so it is J (Thm 6(iii)).
- By Lemma A, every cycle's two bonds at a piece sit on two distinct atoms. The degree count then forces the
  entry/exit/pendant assignments of the table, up to the symmetries p↔q of R and J and w₁↔w₃ of C.
- Each bond of S lies inside a piece or on a cycle of Γ.
- So f can be built piece by piece along the spine, then along the pendant. Whenever a symmetry of a piece is used,
  the next matching bit absorbs it. Directions are copied into o. ∎

*Proof of 2.* Count the configurations directly.
- No pendant: 2 core types × (m+1) positions × 2^{m+2} bits.
- (P-a): ≤ (m+1)² position pairs × 2^{m+2} bits.
- (P-b): ≤ (m+1)(m+2) positions × 2^{m+3} bits. ∎

*Checks* (`classcode_check.py 19`, `out_classcode_19.txt`). For every N ≤ 19:
- the decoded graphs, up to isomorphism fixing a and b, are **exactly** the joint-labelled undirected T-vine shapes:
  3, 8, 15, 24, 35, 48, 63, 80 for N = 5, 7, …, 19, with nothing missing and nothing extra;
- every decoded graph satisfies the defining predicate (block, multiplicity ≤ 2, closure (Y2)-reduces to T);
- codes before orientation number 16, 88, 336, 1088, 3200, 8832, 23296, 59392.

Soundness of decode, which is not needed for the count, therefore holds to 19 atoms. For all sizes it would follow
from Lemma 1.9(2) (rung insertion), but it is not proved here.

### 6.3 Plugging into Lean

- **`IngCode`.** Add a T branch, `IngCode.T (c : SpineCode) (swap : Bool) (o : List Bool)`, with `size := N` and
  `Wf := (o.length = 2N − 2)`. `ingCodesAt` gains a summand of size ≤ 2^{4N}, which is (2^k)^w with w = N − 1 for some
  fixed k. The bound `card_ingCodesAt_le'` survives with a larger constant.
- **`vine_card_m` analogue.** |S| = 2m + 5 with m = #2-atom pieces (Prop 1.17(b)).
- **Incoherency index.** The groups are the pieces (N3 §4.2), which are **intrinsic**: no realization is chosen, so the
  analogue of `realizedIncoherencyIndex_any` is definitional.
- **Unit decoding of VC codes (`UnitDecode*`).** These read only the arc lists of the ingredient codes, so they carry
  over once `ingArcs` dispatches on the T branch.
- **Bonds.** A block with N atoms has 2N − 2 bonds, so `expand_bonds_le`'s role (bonds ≤ 28 + 3n) is trivial.

---

## 7. The `vineest` repairs re-checked for T-vines

Each repair is a property either of `sumint` and its uniformity, or of the garden and twist bookkeeping. **None uses
the list (I)–(VIII).** For T-vine units the only inputs are Theorem C and Corollary C′ (§3), so each repair transfers.

| Erratum | The repair (ERRATA; main) | T-vines | Status |
|---|---|---|---|
| **E2d** (L1817, same-direction core of (V)–(VIII)) | the core pair has the **signed** form 2⟨u₁,u₂⟩ and −2⟨u₃, u₁+u₂−u₃⟩; `sumint` holds signed (`SumintPar.signed_of_sumintPar`, `SumintSigned`; contract fields `coreFirstSign` and `coreSign`) | **Sharpened** (CHECKED exhaustively on all 14 core configurations, §3, L4–L6). A core of shape (B), (C) or (D) has the linear form iff its double bond(s) are anti-parallel. If they are **parallel** it has the nonlinear form with **coreSign = −1, always**, and the printed unsigned nonlinear form never occurs. So every T-vine core is covered by the signed `sumint` already on main | PROVED (reduction) and CHECKED (sign table) |
| **E4** (L1846, ε → 1 for long chains) | ε = 1 − 1[k₂=k₁] − 1[k₂=k₃] is a mixture of linear input phases of mass ≤ 3ⁿ, and `sumint` is uniform in linear phases (`clockedBoundEps_of_restr`). The mixture hypothesis `SumintMixSignedDoubled` is proved unconditionally on main (namespace `DegenVine`, consumed by `vineestStep3`) | ε is per node, a garden datum; the mixture argument needs only that each unit satisfies `sumint`'s hypotheses uniformly in linear phases, which Corollary C′ gives. The cost 3^{|I|} ≤ C^M is unchanged | PROVED (verbatim). For the formalization of the vine estimate: confirm that `SumintMixSignedDoubled`'s γ-range includes γ ≤ 1/2. `SumintPar` is two-branch (planning notes), so this is expected |
| **E14** (L1747, a lower child that is a leaf) | evaluate at the lower end of the unit interval, then take an order-0 time trace (`XNorm00Restr_trace`) | garden-level (u₂₁, u₂₂ are external to the unit); family-free | PROVED (verbatim) |
| **E24** (L2065/L2067, weights and k-derivatives on leaves) | rewrite as real combinations of kernels with **type-uniform** inputs (leaf-pair type = layer, root tree of the + leaf, root tree of the − leaf), using real central differences (`first_coeff_extraction`) | the extraction acts on leaf weights. An LF twist acts only on core **bad** vines, and T-vines are normal, so never twisted. Every pair of a (CL) vine region has type (q, j₁, j₁) whatever the family. The resulting kernels are `vineest` kernels to which Corollary C′ applies | PROVED (verbatim) |
| **E25** (L1909, the class count eats the bad-vine gain) | keep C₂^b explicitly, with b = the number of bad vines, and halve the gain (`VineEstCanonLayerHalf`) | b counts (I) and (II), the same in 𝒱_{≤1/2}. T-vines are normal, hence never operative, and add nothing to b | PROVED (verbatim) |
| **E26** (L1954–L1957, lower-child slots keep the clock τ_b) | Fourier-expand the slots in τ_b and route e^{πiλτ_b} into the unit as a modulation, at a loss ⟨λ⟩^{6η⁶}, by `sumint`'s modulation tolerance (L1618; `VineEstCanonLayerHalfMK`) | for a T-vine unit, τ_b is the time t₀ⁱ of its lower joint, the x₀-atom of Theorem C (C0). `sumint` carries the parameter λ₀ⁱ on t₀ⁱ for every unit. The weighted flower variant (U-clock) is treated in the flower note and is equally family-free | PROVED (verbatim) |

**Two adjacent items, outside the scope of this note and noted for the formalization of the vine estimate and for
the flower note.**
- **E18** (trivial couples and trees at the top layer) is garden-level.
- **E37** (a cutoff inside a spliced vine enters the vine weight) concerns the weights 𝒦 and ℒ of `sumint`, which are
  family-free.

---

## 8. The finite facts for the compact checker

Everything above is PROVED for all sizes, **given** the finite facts below. They are the *complete* list: no other
statement of §2–§7 has a finite base.

**How completeness becomes a theorem, without canonical forms.**
- N2 Lemma 1.8 bounds the base: D = 0 ⇒ ≤ 11 atoms, and D ≤ 1 ⇒ ≤ 13.
- Lemma 1.7′ (§5.4) says every T-vine with ≤ 13 atoms is isomorphic to an instance produced by a Lean function from
  the parameters (k, k′, ℓ′ by position, joint placement).
- So the checker runs over generated instances, and the facts transfer along the explicit isomorphism.

| ID | Fact (a Bool check on each instance) | Instances | Consumed by |
|---|---|---|---|
| **F1** | *Generation.* `genClosure (k, k′, i)` = Z_{k′}(Z_k(T, ℓ₀), the i-th non-triple bond), for k + k′ ≤ 4 (≤ 11 atoms). `genTVine (closure, i, j)` subdivides the bond copies i ≤ j (j = i gives σ = 1) and is kept iff every multiplicity is ≤ 2. *Theorem (not a check):* every T-vine with ≤ 13 atoms is ≅ some `genTVine` (Lemma 1.7′ plus N2's joint rule) | 63 closure instances; **723** T-vine instances, covering all 53 undirected shapes (CHECKED, `gen_params.py 13`) | completeness of F2–F5 |
| **F2** | *Piece-shape base* (Prop 1.17(b)). If D = 0: the pieces are {j₁}, {j₂}, one 3-atom core of shape B, C or D, and 2-atom pieces of internal multiplicity 1 or 2 | the **135** instances with D = 0 (13 shapes; 94 directed classes) | Prop 1.17(b), hence Theorem 6, Theorem C, Theorem S, (U0) of `layervine` |
| **F3** | *(F1)(i) base.* If D = 0: I = verts ∖ {j₁, j₂} is connected | the same 135 | Thm 1.15 (F1) |
| **F4** | *Theorem 1.15 single-member base.* If D ≤ 1: for every proper vine-like sub-object U such that every deletable rung contains a joint of U, U has type I, VC:I+I or T (block or hyper), U is `GapFree`, and X minus U is connected | the **378** instances with D ≤ 1 (27 shapes). In N3's count, the pairs up to isomorphism are 57 (70 raw; 459 directed) | Thm 1.15 (F3), (F4), (F5) for single members |
| **F5** | *Family base is empty.* If D ≤ 1: every family of ≥ 2 pairwise disjoint proper vine-like sub-objects contains the double bond of a 2-cut rung (deletable or cap), or has a deletable rung containing no member's joint | the same 378 | Thm 1.15 (F5) for families (N3 (B5)) |
| **F6** | *Drawn templates* (N2 Lemma 5.2 base). The six templates III–VIII at k = 0 are T-vines (**already proved in Lean**: `TVineExamples.lean`, see Lemma 5.2 in §2.2). Each of their 13 slots is a 2-edge-cut with an interior atom on each side | 6 + 13 | Lemma 5.2 (𝒱_{>1/2} ⊂ 𝒱_{≤1/2}); the γ > 1/2 ⊂ γ ≤ 1/2 inclusion |
| **F7** | *Local charts* (Prop L, configurations L3–L6). For each configuration and orientation, the explicit chart of `out_local_tables.txt` has: labels solving the local system; coordinates that are local opposite differences; unit decoding; and the exact phase identities. These are polynomial identities, `ring`-level, with no enumeration. L1 and L2 (rungs) are proved by hand (§3.2) | **20** (core B 6, C 4, D 4; junction 6); optionally the 8 rung configurations | Theorem C (C2)–(C4); E2d sign table |

**Status of the facts.**
- F1 coverage and F2, F3 are CHECKED **here**, independently: `gen_params.py` finds 0 failures on all 135 D = 0
  instances.
- F4 and F5 are CHECKED by N3 (`base_sets.py`, `cor116_check.py`) and REF3 (`chk_base.py`), to 13 atoms and beyond.
- F6 is CHECKED by N2, N3 and REF3; its k = 0 part is Lean-proved.
- F7 is CHECKED here, exhaustively.

**Not needed** (despite earlier lists):
- the classification counts (53 shapes, 1586 directed classes): F1's generation theorem replaces them;
- N1's analytic unit data (★) on base cores: the analysis consumes only the forms (F7) through the sealed `sumint`;
- directed instances, except in F7: N3 §3.2;
- confluence: §5.

**Kernel guidance** (a risk noted in the planning notes). Encode an instance as `Fin N` with an edge list of ≤ 24 bonds.
- 2-edge-cuts: remove each of the ≤ 276 bond pairs and run a fuel-bounded BFS.
- Pieces: from the cuts, as the signature of each vertex over all cut sides.
- Sub-objects (F4, F5): enumerate (k₁, k₂) and subsets of the components of X − {k₁, k₂}. I(U) is a union of such
  components (N2 Def 1.1), so no powerset of vertices is ever formed.
- Use structural recursion on `Nat`/`List`, `decide`, no `native_decide`, one module per closure family.
- Benchmark first on the largest instance (13 atoms) and the largest F5 family.
- The whole base is ≤ 723 small instances.

---

## 9. Lean-facing summary, open remainder, risks

**Proposed Lean statements** (distinct names, stub-first, as for the flower):

| Name (proposed) | Statement | Proof source |
|---|---|---|
| `TVine.y2Path_early` | Lemma E | §5.2 |
| `TVine.y2Path_deleteRung`, `TVine.y2Path_insertRung` | Lemmas 5′, 5″ | §5.3 |
| `TVine.isTVine_deleteRung`, `TVine.isTVine_insertRung` | N2 Lemma 1.9 | N2 plus §5 |
| `TVine.generation` | Lemma 1.7′, with an explicit `Equiv` to `genTVine` | §5.4 |
| `TVine.card_le_of_D` | N2 Lemma 1.8 | N2 |
| `TVine.pieceShape` | Prop 1.17(a)(b) | N2 plus F2 |
| `TVine.thm6` | N3 Theorem 6 (i)–(iv) | N3 |
| `TVine.attach` | Lemma A | §2 |
| `TVine.subObjects` | Thm 1.15 (F1)–(F6) | N2/N3 plus F3–F5 |
| `TVine.subsetvc'` | Cor 1.16′ and Lemma P | N3 |
| `TVine.noCutVertex` | N3 Lemma 4.1 | N3 |
| `TVine.drawn_isTVine` | N2 Lemma 5.2 | N2 plus F6 |
| `TVine.chart` | Theorem C (de-indexed `FullVineChart`) | §3 plus F7 |
| `TVine.spineCode` | Theorem S | §6 |

**Remark: the bad vines need no catalogue either.** Vine (II) is the digon chain j₁ = R₁ = ⋯ = R_m = j₂ of spine rungs,
and (I) is the joint alone. So Step 2 of Theorem C, using only the rung charts L1, gives their charts:
- n = 2m + 1;
- ζ = y (straight) or −x + y − ρ (turn), so the contract's `ζ_bad_nonzero` holds.

Together with Theorem C for T-vines, which include the drawn (III)–(VIII) by Lemma 5.2, this replaces the whole
VineParam catalogue by the gluing proof plus F7. The planning notes anticipated this; it is now proved on paper.

**Open remainder.**
1. *Lean engineering:*
   - kernel certificates for F1–F7;
   - the `Equiv` transport in `TVine.generation`;
   - the bridge B0 and the U-layer API;
   - de-indexing the contract and its consumer from `VineType`;
   - the spine-code decoder.
2. *Check for the vine estimate:* the γ-range of main's `SumintMixSignedDoubled` (E4) must include γ ≤ 1/2. Expected,
   since `SumintPar` is two-branch.
3. *Not claimed:*
   - soundness of the spine code for all sizes (CHECKED to 19 atoms, not needed);
   - the Q-class version of Lemma 1.5 (not needed: (II) stays a template).

**Risks.**
- Lemma E, Lemmas 5′/5″, Lemma 1.7′, Lemma A, Theorem C, Lemma LPC (paper form) and Theorem S are **new written
  proofs**, and the refute-first referee should attack them first.
- The computations support them: 0 failures in 21,078 surgeries, 23,820 global charts and 47,640 garden trees, and
  exact spine-code coverage to 19 atoms.
- Theorem C inherits Theorem 6's dependence on the piece-shape base F2, which is CHECKED in Python but not yet
  kernel-verified.

---

## 10. Files (scripts, not included in this repository)

| file | content | output |
|---|---|---|
| `chartlib.py` | piece-chart construction (Step 2 of Theorem C), checks, random garden trees, cotree expression | — |
| `chart_check.py MAX NTREE SEED [fast]` | Theorem C and Corollary C′ end to end; the T₁⁻¹ control | `out_chart_check_11_all.txt`, `out_chart_check_15_fast.txt`, `out_chart_check_17_fast.txt` |
| `local_pieces.py` / `local_pieces.py tables` | Prop L, exhaustive over L1–L6; explicit charts for F7 | `out_local_pieces.txt`, `out_local_tables.txt` |
| `pathwise_check.py MAXC NPATH SEED` | Lemmas E, 5′, 5″ as surgery on random (Y2)-paths | `out_pathwise_21.txt` |
| `classcode_check.py MAX` | Theorem S: completeness, soundness and counts | `out_classcode_19.txt` |
| `gen_params.py MAX` | the F1 parametric instance family, coverage and D counts | `out_gen_params_13.txt` |
| `g3lib.py` | N3's library, used unchanged: T-vine shapes, orientations, canonical forms, 2-cuts, pieces | — |
