# Closing the remaining gaps of the γ ≤ 1/2 repair (research note 2)

Date: 2026-11-05. Author: research agent launched by wt-orch (packet "research-gamma-half-2"). No Lean. Nothing outside
`<scratch>/research-gamma-half-2/` was edited. Inputs read only; the files this note relies on are pinned
in `pinned/` with hashes in `pinned/PINNED_SHA256.txt`.

**Sources** (line numbers refer to these files):
- **TARGET** = `wave-turbulence/paper/source/WKE-Longer_times_Final_arXiv.tex`;
- **DH23** = `wave-turbulence/references/src-2301.07063/Revision_Submit.tex`;
- **N1** = the first research note, `<scratch>/research-gamma-half/NOTES.md` (pinned copy `pinned/NOTES.md`);
- **REF** = the referee report, `<scratch>/research-gamma-half-referee/REPORT.md` (pinned `pinned/REPORT.md`);
- **YLEM1**, **CASE4**, **F75** = `docs/research/ylem1-investigation.md`, `dh23-prop96-case4.md`,
  `case4-gamma-above-half.txt`.

**Labels.** PROVED = the proof is written here. CHECKED = verified by a script in this directory (§8; run as
`python3 -I <script> <args>` from this directory, outputs in `out_*.txt`). HEURISTIC = not proved.

---

## 0. Status of items 1–6

| # | Item | Status |
|---|---|---|
| 1 | Rung-locality for the combinatorial facts, all sizes | **CLOSED (PROVED).** Induction on rungs (Theorem 1.15). The inductive step is a written proof (rung deletion, §1.3–1.6). The base is every T-vine with at most 13 atoms, CHECKED; the checks actually cover all 30718 T-vines with ≤ 19 atoms. Covered: `disjointlem` (i)/(ii); the sub-object classification; gap freeness; no sub-object meets a container joint; connectivity after removing *any family* of pairwise disjoint sub-objects (not only pairs); overlap classification, so maximal SG sub-objects are disjoint (TARGET L2167 relies on this); sub-objects never straddle a VC joint. The analytic piece data (Theorem N of N1) are extended to all sizes by the same deletion (§1.7, PROVED); the `layervine` structure is CHECKED to 17 atoms (sketch for all sizes). |
| 2 | TARGET, R ≥ 2 gardens | **CLOSED.** `excessprop1` (2) needs a T-vine count; it holds with the same exponent (PROVED, §2.1). `excessprop1` (3), the imperfect components of `lgmolect` and (finalcount1) use nothing about the vine shapes beyond two constants, which T-vines satisfy (≤ 3 ladders, ≤ 13 atoms outside them; §2.2–2.4). |
| 3 | DH23 Sec 11 / TARGET Sec 12 | **CLOSED.** Neither uses (I)–(VIII) as an exhaustive list. Both re-run the main proof, so they need the same (γ-dependent) family; T-vines need no twists and no cancellation there. One shape constant changes: "at most 20 variables per vine" (TARGET L2297) becomes O(1), which is absorbed (§3). |
| 4 | Prop 9.6 case (5) via Prop 10.4(1); explicit ylem1′ list | **CLOSED.** The exceptions of Prop 10.4(1) are exactly the Q-type molecules Q′_m (PROVED; CHECKED by brute force), so case (5) does not depend on the vine family. T∖ℓ gains L^{−γ₀} directly from DH23 Lemma A.3(4) (PROVED). The explicit ylem1′ list is Lemma 4.2, with the drawn/new split of every family (PROVED; CHECKED against brute force and against the pinned enumeration). |
| 5 | The γ-dependent vine family | **DONE.** Definition 5.1 gives the predicate (§5.1). Every statement of TARGET and DH23 that mentions vines is mapped to the family it needs (§5.3). Secondary finding: for the TARGET chain alone, one family for all γ would also work (§5.2). |
| 6 | Errata E1–E5 to N1 | **DONE** (§6), plus three further corrections (N6–N8). |

**New obstructions: none.** Two side findings, neither of which breaks the route:
- **DH23 `subsetvc` is incomplete as stated.** Its list omits the block "VC of two double bonds", which already occurs in
  drawn vine (IV). TARGET's own `subsetvc` (L2431) includes it.
- **DH23 Step 1 (L1775) does not say how nested SG sub-objects are handled.** It should be read as TARGET L2101 reads
  it: select the maximal ones.
  - In the enlarged family, nested chains of T-type hyper-blocks are common, so this reading matters.
  - Corollary 1.16 shows that the maximal SG sub-objects are pairwise disjoint, as TARGET L2167 asserts.

**Proposed predicate** (§5.1):

> 𝒱_γ := {(I), (II)} ∪ {T-vines} if γ ≤ 1/2, and 𝒱_γ := (I)–(VIII) (B2's `IsVine`) if γ > 1/2.
>
> A **T-vine** is a block S with joints j₁, j₂ satisfying four conditions:
> - no two atoms are joined by three or more bonds;
> - S∖{v} is connected for every interior atom v;
> - the closure cl(S) is defined (contract each joint);
> - cl(S) rewrites to the doubled triangle T by finitely many undirected (Y2) steps.
>
> **(Y2) step:** delete a triple-bonded pair a, b whose two remaining bonds go to distinct atoms c ≠ d, and add a bond c–d.

The drawn (III)–(VIII) are T-vines (Lemma 5.2), so 𝒱_{≤1/2} ⊇ 𝒱_{>1/2}.

---

## 1. Item 1 — rung-locality, proved for all sizes

### 1.1 Setting and definitions

**Conventions** (DH23 Def 4.1, Def 4.10; TARGET Def `defblock`). A molecule is a finite directed multigraph without
loops, with in- and out-degree ≤ 2 at every atom. An *atomic group* carries every bond between its atoms.

**Definition 1.1 (block, hyper-block, sub-object).**
- **Block.** A block is an atomic group S, connected (B2 F57), with two *joints* j₁ ≠ j₂ that have in- and out-degree
  1 inside S. Every other (*interior*) atom has degree 4 inside S. I(S) denotes the interior.
- **Hyper-block** (F71 reading). A hyper-block is a pair (S, e*): an atomic group S and a bond e* joining j₁, j₂, such
  that S with e* removed is a block with joints j₁, j₂.
- **Sub-object.** A *sub-object* of a block B is a block or hyper-block U whose atom set S(U) is contained in B and is
  different from B. Its bond set E(U) is the set of bonds of B between atoms of S(U).
  - B carries all bonds of the molecule between its atoms, so "sub-object of B in the molecule" and "sub-object of the
    graph B" are the same notion.
  - Every interior atom of U has all four of its bonds in U. Hence I(U) is a union of components of B ∖ {j₁, j₂}.
    `sub_objects()` in `tv.py` enumerates them on this basis, completely.

**Definition 1.2 (closure, T-vine, the enlarged family).**
- **Closure.** cl(B) is obtained by replacing each joint and its two bonds by a single bond. For adjacent joints, the
  path u→j₁→j₂→v becomes u→v. The closure is undefined if a loop would arise.
- **T-vine.** A block B is a *T-vine* if:
  - it has no triple bond;
  - it has no interior cut atom (B ∖ {v} is connected for every interior v);
  - cl(B) (Y)-reduces to the doubled triangle T (DH23 L1929).

  This is N1 Def 2.6.
- **Q-type block.** A block is *Q-type* if its closure reduces to the quadruple bond Q and the same two conditions hold.
  Q-type blocks are exactly the vines (II) with m ≥ 1 double bonds (F72). This is CHECKED by `qcheck.py`, which also
  checks the vine-(II) shape, and it follows from Lemma 1.7 (Q admits a single (Z) move).
- **𝒱_enl.** The enlarged family consists of:
  - bad vines: (I) (a double bond with its two joints) and (II);
  - normal vines: the T-vines.
- **Vine-like.** HV, VC and HVC are defined as in DH23 Def 5.1, with ingredients in 𝒱_enl. The *type* of a VC is the
  multiset of its ingredient types; for example, VC:I+I is a chain of two double bonds.

**Definition 1.3 (rungs and their deletion).** Let B be a block.
- **2-cut rung.** A pair R = {a, b} of interior atoms joined by exactly two bonds is a *2-cut rung* if:
  - B − R has exactly two components K⁻ and K⁺;
  - each of a, b sends exactly one bond (a *rail*) into each of K⁻ and K⁺.

  Then C^± (the two rails into K^±) are 2-edge-cuts of B.
- **Cap; deletable rung.** R is a *cap* if K⁻ or K⁺ consists of joints of B only. Example: the first rung of a (Z)
  ladder, next to the joint that subdivides its triple bond. A rung is *deletable* if it is a 2-cut rung and not a cap.
  D(B) denotes the number of deletable rungs.
- **Deletion B/R.** Delete a and b, then add two bonds:
  - x⁻ → y⁺, where x⁻ is the tail of the bond K⁻ → R and y⁺ is the head of the bond R → K⁺;
  - x⁺ → y⁻, defined the same way.

  Every remaining atom keeps its in- and out-degree. Each cut C^± has one bond entering R and one leaving it, since the
  graph is balanced (N1 Lemma D).
- **Insertion.** Insertion is the inverse operation, at a 2-edge-cut. There are two orientation types:
  - "straight": the double bond is anti-parallel;
  - "turn": the double bond is parallel.

### 1.2 Three lemmas on (Y)-reduction

**Lemma 1.4 (confluence). PROVED.**
- **Statement.** On finite loopless multigraphs of maximum degree ≤ 4, the (Y) rewriting has a unique normal form up to
  isomorphism. The rewriting is DH23's: (Y2) at a triple bond whose two external bonds go to distinct atoms, and (Y1)
  otherwise. Moves never raise a degree, so the degree bound persists, and each atom of a triple pair has at most one
  external bond.
- **Consequence.** "Some complete (Y)-reduction ends at T" is the same as "every complete (Y)-reduction ends at T".

*Proof.* Each move removes two atoms, so the rewriting terminates. By Newman's lemma it suffices to check local
confluence. Two distinct triple bonds P = {v₁,v₂} and P′ = {w₁,w₂} are disjoint: an atom lies in at most one triple
bond, since its degree is ≤ 4.
1. **No bond between P and P′.** The two moves commute.
2. **One bond v₁–w₁.** Let v₄ be the other external neighbour of P and u₂ that of P′.
   - Doing P first adds w₁–v₄; then P′ adds v₄–u₂.
   - Doing P′ first adds v₁–u₂; then P adds u₂–v₄.

   If v₄ = u₂, both orders end with a (Y1) that removes the second pair, and the results coincide. Directions are
   forced by balance. The same comparison works when one of the pairs has fewer than two external bonds: its move is a
   (Y1), and both orders delete P ∪ P′ with the same remaining bonds.
3. **Two bonds v₁–w₁ and v₂–w₂.** Either order produces the same quadruple-bond component on the surviving pair.
   This is a terminal state, and the two results are isomorphic.

∎ CHECKED: on all 590 T-type closures with ≤ 13 atoms, the fixed-order reduction of `tv.y_class` agrees with the
order-searching reduction of the pinned `mg.reduces_to_T`/`reduces_to_Q` (`t_gen_check.py`, `out_gen15.txt`).

**Remarks.**
- On a balanced graph the direction rule of (Y2) is automatic. So directed and undirected (Y)-reduction agree, and
  only the undirected graph matters.
- Any complete reduction ending at T or Q consists of (Y2) moves only. A (Y1) leaves an atom of degree < 4, and (Y2)
  never raises a degree.

**Lemma 1.5 (rung deletion preserves the (Y)-class). PROVED.**
- **Statement.** Let G be a connected 4-regular loopless multigraph. Let R be either:
  - a 2-cut rung of G (Def 1.3, joints ignored), or
  - a *cap*: a triple bond with its two single bonds.

  Let G/R be the deletion. For a 2-cut rung, any perfect matching of {x⁻, y⁻} to {x⁺, y⁺} may be used. For a cap,
  join the two far ends. Then NF(G) ≅ T iff NF(G/R) ≅ T, and NF(G) ≅ Q iff NF(G/R) ≅ Q.

*Proof.*
- **Caps.** By Lemma 1.4 we may start with the (Y2) at R. It produces exactly G/R.
- **2-cut rungs: setup.** Write G = P⁻ ∘ R ∘ P⁺, where P^± are the 2-poles K^± with their two dangling bonds; then
  G/R = P⁻ ∘ P⁺.
- **Pole-internal moves.** Call a move *pole-internal* if its triple bond lies in a pole and not both of its external
  bonds are that pole's dangling bonds. Such a move changes the pole in the same way in G and in G/R.
  - A dangling end attached to an atom of R in G is attached to the paired atom of the other pole in G/R.
  - In both graphs the (Y2) moves that dangling end to the same new atom.
- **Run pole-internal moves in both graphs, in parallel.**
  - (A) Suppose a pole, say P⁻, *collapses*, that is, becomes a triple bond whose two external bonds are its dangling
    bonds. In G/R, its (Y2) joins the two attachment atoms of P⁺. In G, its (Y2) first makes R a triple bond, and the
    (Y2) at R then joins the same two atoms. (If the two atoms coincide, a (Y1) occurs in both graphs.) From then on
    the two graphs coincide.
  - (B) Otherwise no triple bond remains: there is none inside the poles, R is a double bond, and every crossing bond
    is single. G is then in normal form. It has the 2-edge-cut C⁻ and at least four atoms, so it is neither T nor Q.
    G/R has no triple bond either: the two joining bonds give at most a double bond. It has the 2-edge-cut formed by
    the joining bonds. T and Q have no 2-edge-cut (each has edge connectivity 4), so neither normal form is T or Q.

By Lemma 1.4 the normal forms do not depend on the order chosen. ∎

**Lemma 1.6 (two pendant poles). PROVED.**
- **Statement.** Let G be a connected 4-regular loopless multigraph. Let K₁, K₂ be disjoint nonempty atom sets, each
  joined to the rest of G by exactly two bonds, and each without an internal triple bond. Then NF(G) is neither T nor
  Q.

*Proof.* Assume NF(G) ∈ {T, Q}. Then every move is a (Y2) (Remark after Lemma 1.4), so connectivity is preserved.
- **First modification time.** Let t_i be the first time a move adds a bond inside K_i or removes an atom of K_i.
- **Before t_i, K_i is intact.** It keeps its internal bonds and exactly two crossing bonds. A move that reroutes a
  crossing bond does not count.
  - So K_i contains no triple bond: none inside, and only two bonds cross.
  - So the move at t_i is a (Y2) at a pair {v₁,v₂} outside K_i whose two external bonds both end in K_i. By
    connectivity, the whole graph at that moment is K₁ ∪ {v₁, v₂} (taking i = 1).
- **So t₂ < t₁.** K₂ is disjoint from K₁ and has at least two atoms (a single atom with two crossing bonds would have
  degree 2). At time t₁ it has either lost atoms or become {v₁,v₂} with an internal triple bond. Either way it was
  modified earlier.
- **Contradiction.** By symmetry t₁ < t₂.
- **If some t_i never occurs.** Then NF(G) contains the intact K_i together with its 2-edge-cut, so NF(G) is not T or
  Q. ∎

### 1.3 Generation, size bound, and closure of the class under rung deletion and insertion

**Lemma 1.7 (generation; YLEM1 R1; N1 §2.4(b)). PROVED.**

B is a T-vine if and only if both of the following hold:
- cl(B) ∈ 𝒵_T := {T} ∪ {Z_k(T,ℓ)} ∪ {Z_{k′}(Z_k(T,ℓ),ℓ′) : ℓ′ is not a copy of a triple bond}, where Z is DH23's (Z)
  (L1939) with k, k′ ≥ 1;
- the joints subdivide copies of bonds so that B has no triple bond and no interior cut atom.

In the 2-move case, each joint subdivides a copy of a different triple bond. In the 1-move case, one joint
subdivides a copy of the triple bond.

*Proof.*
- **At most two triple bonds.** cl(B) has at most two triple bonds, since each contracted joint raises one
  multiplicity by one. A quadruple bond would make cl(B) = Q.
- **Inverting the reduction.** By Lemma 1.4 the reduction to T consists of (Y2) moves only. Each (Y) sequence uses up
  one triple bond and leaves none behind, so there are at most two sequences. Inverting a sequence is a (Z) move.
- **The second (Z) move.** The second (Z) acts on the bond ℓ′ added by the last (Y2) of the first sequence. That bond
  is not part of a triple bond, or the sequence would have continued.
- **Joint placement** is forced by the absence of triple bonds in B. ∎

The generator in `tv.gen_T_vines` reproduces the pinned enumeration exactly: 4446 classes up to 15 atoms (CHECKED,
`out_gen15.txt`).

**Lemma 1.8 (size bound). PROVED; CHECKED to 19 atoms.** Every T-vine satisfies |B| ≤ 11 + 2·D(B).

*Proof.* Use Lemma 1.7, with ladders of lengths k₁ (and k₂). Ladder 1 has rungs R₁, …, R_{k₁}; R₁ is the rung whose
triple bond carries a joint.
- **Each R_j with j ≥ 2 is a deletable rung of B**, unless the second (Z) move or the free joint sits on a copy of its
  double bond:
  - its rails C_{j−1} and C_j are 2-edge-cuts of M₁;
  - replacing a bond inside a side by a path, or subdividing a cut bond, preserves this;
  - its two sides contain R_{j−1} and the triangle respectively, so it is not a cap.

  The same holds for R′_j, j ≥ 2, in ladder 2.
- **Two (Z) moves:** D ≥ (k₁ − 2) + (k₂ − 1), so |B| = 5 + 2(k₁+k₂) ≤ 11 + 2D.
- **One (Z) move:** D ≥ k₁ − 2, so |B| = 5 + 2k₁ ≤ 9 + 2D.
- **No (Z) move:** |B| = 5. ∎

CHECKED (`item1_check.py 19`): the maximum of |B| over T-vines with D(B) = d is 11, 13, 15, 17, 19 for d = 0, …, 4.

**Lemma 1.9 (deletion and insertion stay in the class). PROVED.**
1. If B is a T-vine and R a deletable rung, then B/R is a T-vine.
2. Conversely, let B′ be a T-vine and C′ a 2-edge-cut of B′ both of whose sides contain an interior atom. Inserting a
   rung of either type at C′ gives a T-vine B in which the new rung R is deletable, and B/R = B′.

*Proof of (1).*
- **Block.** Degrees are preserved and the joints are unchanged.
- **No triple bond.** The two new bonds join K⁻ to K⁺. No bond joined these before, so they give at most a double
  bond.
- **No interior cut atom.** Let v ∈ K⁻ be interior. Every component of K⁻ − v reaches the rest of B − v (which is
  connected) only through C⁻, so it contains x⁻ or y⁻. In B/R − v both of these are joined to the intact, connected
  K⁺.
- **Closure.** Since R is not a cap, each side keeps a non-joint atom after the joints are contracted. So R is a 2-cut
  rung of cl(B), and cl(B/R) = cl(B)/R. Lemma 1.5 finishes the proof.

*Proof of (2).* The same steps, run backwards. ∎

### 1.4 Parity, joints in rungs, container joints, gaps

**Lemma 1.10 (parity). PROVED.**
- **Statement.** Let U be a sub-object and C = δ(X) an edge cut. If U is a block, then |E(U) ∩ C| is even. If U is a
  hyper-block, then |E(U) ∩ C| is odd exactly when C contains the adjoint bond e*.
- **Proof.** Σ_{v∈S(U)∩X} deg_U(v) = 2·#(U-bonds inside X) + |E(U) ∩ C|. The U-degrees are 4 and 2 for a block, and
  4, 3, 3 for a hyper-block. ∎

CHECKED on every sub-object and every 2-cut of every T-vine with ≤ 19 atoms (`lemmas_check.py`; 0 failures).

**Lemma 1.11 (joints in rungs). PROVED.**
- **Statement.** Let R = {a,b} be a 2-cut rung of a block B, and U a sub-object with a joint in R. Then one of two
  things holds:
  - U = {a, b} is the double bond (a block; a vine (I) when anti-parallel);
  - U is the *side hyper-block* (K ∪ R, e*), where K is one side of R and e* is a copy of a=b. Its joints are a, b, and
    K contains no joint of B.

  In both cases both joints of U lie in R. So the joints of any sub-object occupy at most one rung.

*Proof.* Let a be a joint of U, with rails a–x^± and b–y^±.
- **U a block.** Its two bonds at a are induced, so either (α) b ∈ S and x^± ∉ S, or (β) b ∉ S and x^± ∈ S.
  - (β) puts exactly one bond of C⁻ in U, contradicting Lemma 1.10.
  - In case (α), Lemma 1.10 forces y^± ∉ S. So b has U-degree 2, and connectivity gives S = {a, b}.
- **U a hyper-block.** a has U-degree 3, so b ∈ S and exactly one of x^± is in S, say x⁻.
  - Both joints lie outside K⁺, so Lemma 1.10 on C⁺ forces b–y⁺ ∉ U. Hence S ∩ K⁺ = ∅, since K⁺ is reached only
    through C⁺.
  - If the second joint were x⁻, then b would be interior, which needs y⁺ ∈ S. So the second joint is b, and e* is a
    copy of a=b.
  - y⁻ ∈ S, and the atoms of K⁻ are interior. They are closed under adjacency, so S ⊇ K⁻.
  - An interior atom has U-degree 4 while a joint of B has degree 2, so K⁻ contains no joint of B. ∎

CHECKED: 141 832 joint-in-rung incidences, 0 exceptions (`lemmas_check.py 19`).

**Lemma 1.12 (no sub-object meets a container joint). PROVED.**
- **Statement.** Let V be a block satisfying `disjointlem` (i) and having no interior cut atom. Then no proper sub-object
  of V contains a joint of V.

*Proof.* Let J be a joint of V lying in S(U).
- **J interior to U, or a hyper-joint.** Impossible: deg_V(J) = 2, but interior atoms need U-degree 4 and hyper-joints
  need 3.
- **J a joint of the block U, with j′ its other joint.** All bonds at J and at I(U) stay inside S(U).
  - **If j′ is not a joint of V:** then j′ separates S(U) ∖ {j′} from V ∖ S(U), and the latter contains the other
    joint of V. So j′ is an interior cut atom of V, a contradiction.
  - **If j′ is the other joint of V:** then I(U) is a nonempty union of components of V ∖ {J, j′}. That set is connected
    by (i), so S(U) = V. ∎

**Lemma 1.13 (gap criterion). PROVED.**
- **Statement.** Fix the outer data of B; this fixes B's gap r. The gap of a sub-object U (k_out − k_in over the two
  VC-bonds ℓ_in, ℓ_out of U at its joint j₁) is independent of B's free parameters if and only if {ℓ_in, ℓ_out} is a
  2-edge-cut of B. Otherwise it is a non-constant affine function: "free".

*Proof.*
- **The free parameters** form the circulation space Z₁(B) ⊗ ℤ^d. The gap is constant iff f(ℓ_out) − f(ℓ_in) = 0 for
  every circulation f.
- **Duality.** That holds iff e_{ℓ_out} − e_{ℓ_in} lies in Z₁^⊥, the cut space.
- **Translation.** That holds iff it is the signed cut vector of some δ(X). Its support {ℓ_in, ℓ_out} is then a cut,
  with signs matching because ℓ_in enters j₁ ∈ X and ℓ_out leaves it.
- **The constant value** is then 0 or ±r (N1 Lemma D). ∎

CHECKED: the criterion agrees with exact linear algebra (sympy nullspace) on every vine-like sub-object of every T-vine
with ≤ 11 atoms (1621 cases, `lemmas_check.py`).

### 1.5 Deleting a rung from a sub-object

**Lemma 1.14 (Φ). PROVED.** Let R be a 2-cut rung of B and U a sub-object with no joint in R.

**(a) All-in or all-out.** Either:
- R ⊂ I(U) and all four rails lie in E(U) ("all-in"), or
- S(U) ∩ R = ∅ and no rail lies in E(U) ("all-out").

*Proof.* If a ∈ S(U), then a is interior, so b and x^± are in S(U). Then b is interior too, so y^± are in S(U). If
a ∉ S(U), then b ∉ S(U), since an interior b would force a ∈ S(U).

**(b) The image Φ(U).** Φ(U) := (S(U) ∖ R, same joints, same adjoint) is a sub-object of B/R of the same kind.
- **All-out.** U is unchanged as a graph. U is connected and avoids R, so it lies in one side, and no new bond is
  induced.
- **All-in.**
  - **Degrees.** Each of x^±, y^± loses a rail and gains a new bond, keeping its in- and out-degree.
  - **Connectivity.** If U ∩ K⁻ split into a piece containing x⁻ and a piece containing y⁻, each piece would contain a
    joint of U: a piece without joints is closed and equals K⁻. Then U ⊇ K⁺, and both pieces reconnect through K⁺.

**(c) Type.** If U is vine-like of type t, then Φ(U) is vine-like of type t.

*Proof.* Nothing changes when U is all-out. In the all-in case:
- **R lies inside one ingredient V of U.** Suppose a were an intermediate joint of the VC U. It sends exactly two bonds
  into each of its two ingredients. These must be the two copies of a=b on one side, and the rails to x⁻, x⁺ on the
  other.
  - At least one of U ∩ K⁻, U ∩ K⁺ joins its two attachment points inside U, avoiding R. Otherwise there would be four
    pieces, each needing its own joint of U, as in (b).
  - Then x^± is joined to y^±, hence to b, in U − a. So the two ingredients at a meet outside a, a contradiction.
  - The same holds for b.
- **R is a 2-cut rung of V.** Otherwise V ∩ K⁻ would split with a joint of V in each piece, and a would be a cut atom
  of V.
- **Each ingredient stays a vine of the same type.**
  - **When R is not a cap of cl(V):** cl(V/R) = cl(V)/R, so Lemma 1.5 applies.
  - **When R is a cap of cl(V):** V ∩ K⁻ consists of joints of V. Then cl(V) → cl(V/R) by one (Y2), and Lemma 1.4
    applies.
  - **Shape conditions.** V/R has no triple bond and no interior cut atom, by the proof of Lemma 1.9.
- **The ingredient structure** of U is unchanged otherwise.

**(d) Gap.** If the gap of Φ(U) is free in B/R, then the gap of U is free in B.

*Proof.*
- **The lifting map ψ.** Define ψ : Z₁(B/R) → Z₁(B). It routes the flow of each new bond through its two rails, and
  through one copy of a=b when the entry and exit atoms differ. The two new bonds use different copies, so ψ(g) is a
  circulation.
- **Compatibility.** ψ commutes with the gap functionals of U and Φ(U). In the all-in case, a VC-bond of U at j₁ may be
  a rail, and its lifted flow equals that of the corresponding new bond.
- **Conclusion.** A non-zero gap functional on Z₁(B/R) gives a non-zero one on Z₁(B).

**(e) Removal connectivity.** If (B/R) ∖ ∪Φ(Uᵢ) is connected, then B ∖ ∪Uᵢ is connected. Here the Uᵢ are pairwise
atom-disjoint, have no joint in R, and are each all-in or all-out. At most one can be all-in, since they are disjoint.
- **One all-in member.** The two graphs are literally equal: R's atoms are interior, and its rails and the new bonds
  are removed.
- **All members all-out.** Write H := B ∖ ∪Uᵢ. It contains R with its four rails, and H/R = (B/R) ∖ ∪Φ(Uᵢ). Any path
  in H/R lifts to H by replacing each new bond with rail–R–rail. ∎

CHECKED (`lemmas_check.py 19`, 0 failures, on all 30718 T-vines with ≤ 19 atoms):
- 139 820 deletions;
- 772 066 sub-object images;
- 1 261 414 disjoint-pair transfers.

In every case: B/R is a T-vine; all-in or all-out holds; the image exists with the same kind and type; and gap
status, single and pair removal-connectivity, and joint-avoidance are preserved.

### 1.6 The theorem

**Theorem 1.15 (all sizes). PROVED; base cases CHECKED.** For every T-vine B:

| | Fact |
|---|---|
| **(F1)** | DH23 `disjointlem` hypotheses (i) and (ii) hold for B. Consequently they hold for every HV, VC and HVC of 𝒱_enl, as DH23 asserts at L792 for its own family: removing an intermediate joint of a VC leaves exactly two components, one containing each end joint, and an adjoint bond joins only the two joints. |
| **(F2)** | No proper sub-object of B contains a joint of B (Lemma 1.12). |
| **(F3)** | Every proper vine-like sub-object of B is one of: a block (I); a block VC:I+I; a hyper VC:I+I; a block T-vine; a hyper T-vine (an HV of a T-vine). There is no Q-type ingredient and no other VC or HVC. |
| **(F4)** | Every proper vine-like sub-object has a free gap, so its gap is never identically 0 or ±r. |
| **(F5)** | For every family of pairwise atom-disjoint proper vine-like sub-objects, B stays connected after all of them are removed. |
| **(F6)** | Two proper vine-like sub-objects that overlap without either containing the other are two double bonds sharing exactly one joint. |

*Proof.*
- **(ii)** is part of the definition: no interior cut atom.
- **(F1)(i), by induction on |B|.**
  - If D(B) ≥ 1, delete a deletable rung R. By Lemma 1.9, B/R is a T-vine, and (B/R) ∖ J is connected by induction.
  - Lift paths from (B/R) ∖ J to B ∖ J. A new bond u–w with u, w ∉ J lifts to u–rail–R–rail–w, avoiding J.
  - R is internally connected by its double bond. Of its four rails at most two end at joints, since B has two joints,
    so R stays attached to a non-joint atom.
  - So B ∖ J is connected. This is the argument of Lemma 1.14(e), adapted to rails that may end at a joint.
  - Base: D(B) = 0, which by Lemma 1.8 means |B| ≤ 11. CHECKED.
- **(F2)** follows from (F1) and Lemma 1.12.

**(F3), (F4), and (F5) for a single member, by induction on |B|.** Fix B and a vine-like sub-object U.
- **Inductive step.** Suppose some deletable rung contains no joint of U. Apply Lemma 1.14: Φ(U) is a proper vine-like
  sub-object of B/R with the same type. By induction its gap is free and its removal keeps B/R connected, and by
  1.14(d) and (e) the same holds for U in B.
- **Base.** Otherwise every deletable rung contains a joint of U. By Lemma 1.11 these joints lie in one rung, so
  D(B) ≤ 1 and, by Lemma 1.8, |B| ≤ 13. CHECKED.

**(F5) for families, by induction on |B| + |family|.** Apply the first of the following steps that is available.
1. **A member is the double bond of a deletable rung R.**
   - Its anti-parallel double bond means each of a, b has one rail in and one rail out. So the canonical new bonds of
     B/R join exactly the two rail-ends at a, and the two at b.
   - Hence B ∖ ∪F is (B/R) ∖ ∪Φ(F ∖ {R}) with the two new bonds subdivided, and connectivity is equivalent.
   - The other members avoid R and its rails: a rail in a member would put a or b into it.
2. **A member is the double bond of a cap rung.** Drop it. Its atoms stay joined through the cap joint, which no member
   contains, by (F2).
3. **Some deletable rung contains no member's joint.** Apply Lemma 1.14(e).
4. **Otherwise every deletable rung contains a joint of a side hyper-block member** (Lemma 1.11). There is at most one
   such member in a disjoint family:
   - for two disjoint side hyper-blocks K₁ ∪ R₁ and K₂ ∪ R₂, the sides K₁, K₂ are disjoint and joint-free;
   - in cl(B) they are pendant 2-poles without triple bonds;
   - this contradicts Lemma 1.6.

   So D(B) ≤ 1 and |B| ≤ 13. CHECKED, exhaustively over all families.

**(F6).** Both sub-objects satisfy (i) and (ii): by (F1), and for types I and VC:I+I trivially. So DH23 Lemma
`disjointlem` applies: both are blocks, and we are in scenario (a), (b) or (c).
- **(a)** σ = 1 for both, and they share both joints and nothing else. Then I(U) and I(V) are disjoint, joint-free
  (F2), triple-free pendant 2-poles of cl(B). This contradicts Lemma 1.6.
- **(b)** The concatenation U ∪ V is a proper vine-like sub-object; it is not B, which has no interior cut atom. By
  (F3) it is VC:I+I, so U and V are double bonds.
- **(c)** U = C₀ + C₁ is a VC, so by (F3) C₀ and C₁ are double bonds; likewise C₂. Then C₀ ∪ C₁ ∪ C₂ would be a
  VC:I+I+I sub-object, contradicting (F3). ∎

**Base cases, CHECKED** (`item1_check.py 19 17` → `out_item1_19.txt`, 0 failures). The check covers all 30718 T-vines
with ≤ 19 atoms, well beyond the base (≤ 13):
- (i) and (ii): 0 failures;
- 189 049 sub-objects, all vine-like, of the five types in (F3):

  | type | count |
  |---|---|
  | block I | 122 765 |
  | block VC:I+I | 904 |
  | hyper VC:I+I | 11 758 |
  | block T | 5 630 |
  | hyper T | 47 992 |

- every gap free; no sub-object touches a joint of B;
- every single removal keeps B connected;
- every family of pairwise disjoint sub-objects removed: 236 681 families up to 17 atoms, of sizes 2–7; all 252 668
  disjoint pairs at 19 atoms;
- at most one side hyper-block in any disjoint family;
- every overlapping non-nested pair is two double bonds sharing one joint: 12 662 pairs.

These numbers agree with the referee's independent `subcheck.py` counts at 19 atoms (REF).

### 1.7 Consequences for containers, and the analytic piece data

**Corollary 1.16 (`subsetvc`′, and TARGET's disjointness claim). PROVED.**
1. **No straddling.** Let U₂ be a vine-like object of 𝒱_enl and U₁ ⊊ U₂ a vine-like object with no common ingredient.
   Then U₁ lies in a single ingredient V and avoids V's joints.
   - *Proof.* If I(U₁) avoids every intermediate joint, it lies in one ingredient (it is connected), and Lemma 1.12
     applies.
   - If I(U₁) contains an intermediate joint c, then on each side of c the intersection with the neighbouring
     ingredient either is the whole ingredient or contains a joint of U₁.
   - In the first case that ingredient is an ingredient of U₁, a contradiction: its joints are cut atoms or joints of
     U₁, and it has no interior cut atom.
   - In the second case U₁ ∩ V_i is a proper sub-block of V_i with V_i's joint c as a joint, contradicting Lemma 1.12.
     (U₁ cannot be a hyper-block here, because its two joints lie in different ingredients.)
   - **One exception: an HV of a σ = 1 vine.** Its adjoint bond and the vine's j₁j₂ bond can form a double bond
     {j₁, j₂}, which is a sub-object of type (I). Its removal keeps the container connected.
2. **The list.** Hence U₁ is one of:
   - a double bond, a block or hyper VC:I+I, a T-vine, or an HV of a T-vine, when the ingredient is a T-vine (Theorem
     1.15);
   - a double bond, when the ingredient is a vine (II).

   The (II) claim is CHECKED for every vine (II) with ≤ 18 atoms (`qcheck.py`), and proved for all sizes by the same
   induction: every rung of (II) other than its two caps is deletable.
3. **Connectivity.** The container stays connected after any family of disjoint SG sub-objects is removed, by (F5)
   applied inside each ingredient. The joints of each ingredient survive by (F2).
4. **DV′ containers.** A DV′ is the union of two σ = 1 vines sharing both joints (Lemma 8.1′; see N6). Its
   sub-objects lie in one of the two vines, since an interior joint would need degree 4 but has degree 3, and the
   other vine keeps j₁, j₂ connected.
5. **Maximal SG sub-objects are pairwise disjoint** (TARGET L2101, L2167). By (F6), two overlapping maximal ones would be
   double bonds sharing a joint. Their concatenation has the same gap, so it is SG, which contradicts maximality.

**Proposition 1.17 (pieces, Theorem N of N1, `layervine`, all sizes).**

*(a) Pieces under deletion. PROVED.* The *pieces* of B are the classes of atoms not separated by any 2-edge-cut. For a
deletable rung R, pieces(B/R) = pieces(B) ∖ {R}, and every surviving 2-cut keeps its gap label.

*Proof.* B and B/R have all degrees even, so every edge cut is even. Hence u, w lie in one piece iff λ(u,w) ≥ 4 (Menger).
- **λ_B ≥ λ_{B/R}.** Lift edge-disjoint paths: each new bond goes along its rails, the two using different copies of
  a=b.
- **Conversely, a 2-cut {e, f} of B/R separating u ∈ X from w ∉ X gives a 2-cut of B separating them.**
  - *Neither e nor f is new, and both new bonds lie on one side.* Put R on that side; the boundary in B is still
    {e, f}.
  - *Neither is new, and the new bonds lie on different sides.* Then X and its complement each contain one − and one +
    rail endpoint. K⁻ and K⁺ are connected, so e ∈ K⁻ and f ∈ K⁺, say. If u ∈ K⁻, then K⁻ ∩ X has boundary
    {e, rail} in B. If u ∈ K⁺, use {f, rail}.
  - *e new, f not.* The other new bond lies on one side; put R on that side. The boundary becomes {f, one rail}.
  - *e and f both new.* X contains the two − endpoints (the case "one − and one +" would leave no K⁻-edge crossing,
    contradicting connectivity of K⁻), so its boundary in B is C⁻.

  R itself is a piece of B (λ(a,b) ≥ 4: two copies, plus one path through each side).
- **Labels.** A 2-cut's gap label is 0 or ±r according to whether the two joints of B lie on the same side (N1
  Lemma D). The joints are not in R, so the corresponding cuts have the same labels.
- **New bonds** join K⁻ to K⁺, so they are never internal to a piece. ∎

*(b) Theorem N for all sizes. PROVED, given the base.*
- Delete rungs down to D = 0, where |B| ≤ 11 (Lemma 1.8). By (a), every piece of B that is not a deleted rung is a
  piece of that base T-vine, with the same internal bonds and labels, hence the same analytic unit data (N1 Lemma D).
- The base is covered by N1's `units.py` and `pieces.py`, which reach 15 atoms.
- Every deleted rung is a generic 2-cut rung piece. It is a rung unit: Γ_a = 2(o−i)·(o−i′) has rank 2, and Γ_a + Γ_b
  is r-linear (N1 §2.5).
- This turns REF item 4a ("confirmed as a sketch") into a proof.

*(c) `layervine` structure. CHECKED to 17; all sizes HEURISTIC (sketch).* TARGET Prop `layervine` defines the
spine/pendant structure through pieces, and deletion removes one rung piece of a ladder. The same reduction to D = 0
should apply, but the invariance of "the piece separates v₁ from v₂" under deletion is not written out.

CHECKED (`pieces_check.py 17`, 0 failures):
- pieces(B/R) = pieces(B) ∖ {R} for all 43 596 deletions;
- every T-vine has exactly 2 one-atom pieces (the joints), one 3-atom piece, and otherwise 2-atom pieces;
- spine/pendant structure, over all 23 820 cases (each T-vine with either joint as v₂): 17 608 "ladder + (D)
  pendant" and 6 212 "no pendant";
- maximal ladders (B2's `IsLadder`): at most 3 per T-vine, with at most 13 atoms outside them.

(The second case of (a), the "separating bridge", occurs in 9 456 deletions, typically with a joint next to R; it is
handled in (a).)

---

## 2. Item 2 — TARGET with R ≥ 2 gardens

For R ≥ 2, TARGET's stage 2 differs from DH23 in four places. None of them uses (I)–(VIII) as an exhaustive list. Two
of them use vine-shape constants or counts, and T-vines satisfy those.

### 2.1 `excessprop1` (2): an Operation 1 that creates a new component (TARGET L2165–L2177). PROVED

**Setting.** U is an SG (CN) vine or root (CL) vine in 𝒞₁, with m atoms. Removing it raises F by 1 and V_β by 2. Then

  (dev1): 𝔍 ≲ 𝔉 · L^{−(m−1)(d−γ)} (C₁⁻¹δ^{1/2})^{m−1} ∏_{𝕃_j⊂U} 𝔛_j^{z_j}.

TARGET bounds 𝔉 in three steps:
1. fix the two bonds at one joint: L^{d−γ+γ₀+η³} choices, by (atomcountbd);
2. parametrize the rest as in `vineest`;
3. use (basiccount01) for each rung and (basiccount02) for the core.

**For a T-vine U** (m = 2m̃ + 5) the same three steps apply, with these justifications.
- **Step 1 is generic.** It uses only that the removal creates a component, which forces k_{ℓ₁} ± k_{ℓ₂} to be fixed.
- **Steps 2–3: the piece parametrization.** By Proposition 1.17 (Theorem N at all sizes), the pieces of U are its two
  joints, one 3-atom core, and m̃ 2-atom pieces. Parametrize along the 2-cut structure, starting from the joint whose
  bonds are fixed (N1 Lemma D):
  - every 2-cut decouples;
  - each piece's boundary bonds are determined by the data fixed before it, by its own difference variables, and by a
    gap label in {0, ±r}.
- **The per-piece systems.**
  - Each 2-atom piece is a (basiccount01) system with r replaced by its label, giving
    ≲ δ⁻¹L^{2(d−γ)} 𝔛(P)⁻¹.
    For a rung of a maximal ladder 𝕃_j ⊂ U, the label is the ladder's gap, so P = P_j. This gives one 𝔛_j⁻¹ per rung,
    hence at least z_j of them.
    Maximal ladders of 𝕄_sb that meet I(U) have all their rungs in I(U). The rails at a rung in I(U) stay inside S(U).
    A rung containing a joint of U would give that joint U-degree 3 (two copies of the double bond plus a rail), but a
    block joint has U-degree 2.
  - The core is a (basiccount02) system with Λ ∈ {u₁·u₃, u₃·(u₁+u₂−u₃)}, i.e. ζ ∈ {x, x+y−z} with v = 0, giving
    ≲ δ⁻²L^{3(d−γ)−γ₀}. REF `refcheck.py` verified the core forms for all T-vines up to 17 atoms, and Proposition 1.17
    extends this to all sizes.
  - The other joint carries no free vector. The free vectors number m − 2 = 2m̃ + 3: two per 2-atom piece, three for
    the core.
- **Total.**

  𝔉 ≲ L^{d−γ+γ₀+η³} (δ⁻¹L^{2(d−γ)})^{m̃} δ⁻²L^{3(d−γ)−γ₀} ∏𝔛_j^{−z_j},

  hence 𝔍 ≲ L^{η³} (the δ powers cancel: δ^{−m̃−2}·δ^{(m−1)/2} = 1).
- **Comparison.** This is better than TARGET's L^{γ₀+2η³}. So (excesseqn2+) holds for T-vines with the same margin.

### 2.2 `excessprop1` (3): at most 2R − 1 new components (L2179). Generic

The argument has three parts:
- Prop `cnblock` (L1367) is a statement about arbitrary (CN) blocks and root (CL) blocks.
- Operations 1 on HVs do not split the molecule, since the adjoint bond keeps the two joints joined.
- Operations 1 on 𝒞₂ do not split it either: this is Corollary 1.16(3), which replaces "by Lemma `subsetvc`".

The ordering "𝒞₁ before 𝒞₂" and the disjointness of 𝒞₁ ∪ 𝒞₂ are Corollary 1.16(5) together with subpro (4).

### 2.3 `finalmol` and the imperfect components in `lgmolect`'s proof (L2182–L2200). Generic

**`finalmol`.**
- "At most R imperfect components" is a degree count, invariant under Operations 1–4.
- "A vine component must be LG" is DH23 Prop 9.5's proof. It needs subpro (6), which holds for 𝒱_enl because its
  inputs hold: Lemma 8.1′ (N6), Cor `blockchainprop`, and `subsetvc`′ (Corollary 1.16).

**Imperfect components with R ≥ 2.** TARGET bounds them in three steps:
1. 𝔄 ≲ 1, by the odd-component argument of DH23 Prop 9.6 case (1): operations (a) and (b) on ε-atoms only.
2. 𝔄 ≲ L^{−η²ρ + C₀W} with W = V_α + V_β + Z, by DH23 Lemma 10.2.
3. Interpolation: L^{−η⁴ρ + C₀η²W}. This is at most the right side of (finalcount), since C₀η² ≤ min(γ/4, γ₀, η).

W ≥ 1 because the component is imperfect: if V_α = V_β = 0, some ε-atom has degree < 4, so Z ≥ 1. None of the three
steps involves vines.

**Perfect components** go to DH23 Prop 9.6. Their cases are:
- (1)–(3) and (6): unaffected;
- (4): repaired for γ ≤ 1/2 (N1, REF), and closed by F75 for γ > 1/2;
- (5): family-independent (§4.1).

### 2.4 Shape constants (L2213, L1519)

**What TARGET uses.**
- (finalcount1) uses: "each vine contains at most 3 ladders and no more than 20 atoms apart from these ladders" (L2213).
- `layervine` uses: "at most three ladders plus less than 20 extra atoms" (L1519).
- The same constant appears in DH23 L1826 as "O(1)".

**For T-vines** the bounds are at most 3 maximal ladders and at most 13 atoms outside them.
- PROVED from Lemma 1.7. The rungs lie in at most three segments: ladder 1, cut at most once by the second (Z) move or
  by the free joint, and ladder 2.
- The atoms outside ladders are counted as: the triangle (3), the joints (2), the length-1 segments (2 atoms each, at
  most 3 of them), and at most one destroyed rung (2). That gives at most 13.
- CHECKED to 17 atoms (§1.7).

The sub-objects removed in Operation 1 are sub-objects of T-vines (Theorem 1.15(F3)), so the same bound holds for them.

---

## 3. Item 3 — DH23 Sec 11 and TARGET Sec 12 (flower trees, parametrix)

**Verdict: nothing in either section uses the list (I)–(VIII) as exhaustive.** Both sections say "repeat the arguments of
the main proof", so they automatically need the same (γ-dependent) family as the main proof, and they use nothing else.

Itemized below. "B" means the passage concerns bad vines only, which are the same in both families; "G" means it is
generic.

**DH23 §11.1.1 (L2012), flower couples and full twists. B.**
- The point of the passage is that a full twist does not change the order counts n_j, n_j′ of the flower tree. That
  concerns core (bad) vines only; T-vines are normal and are never twisted.
- "Since each vine without exploiting cancellation only leads to loss of at most L^{1/2}": T-vines lose at most L^{η⁴}
  (N1 Theorem N; REF).
- "The number of such vines does not exceed the number of special nodes": generic.

**DH23 §11.1.2, the extra ladder argument with the shift k′. G.**
- The ladders concerned are the maximal ladders of 𝕄(𝒬_sub), and the case analysis (LP–LP, or LP/PC) is DH21 §10.1.
- **Remaining point: the shift k′.** In a flower couple a stem node can carry k ≈ k′, which may be large. N1's
  lattice-to-continuum step for T-vines needs the variables in unit balls, but the shift does not reach the interior of a
  spliced vine:
  - only SG vines are spliced (𝒱₀ ⊂ 𝒱; DH23 L1646);
  - the flower is never in 𝒬[V], because the leaves of 𝒬[V] are paired inside 𝒬[V] and the flowers are paired with
    each other;
  - so the stem enters 𝒬[V] ∖ {𝔲₁} only through 𝔲₂₁ or 𝔲₂₂;
  - in that case |r| = |k_{𝔲₂₁} − k_{𝔲₂₂}| ≳ |k′|, so the vine is LG unless k′ = O(1).
- So the T-vine variables (differences inside pieces) are O(1), as for the drawn vines. This is the same observation as
  TARGET L2300, item (7).

**TARGET Prop `flowerest1`, proof items (1)–(8) (L2287–L2305).**
- (1), (2), (3), (6), (8): generic.
- (4), "less than 20P vines containing a special node … sum and integrate trivially over the k_ℓ and t_v variables
  outside of the ladders (there are at most 20 such variables per vine)": uses Prop `ladderl1new` on the ladder part
  and trivial summation on the rest.
  - For a T-vine the rest has at most 13 atoms (§2.4), hence O(1) bond variables. The loss is L^{O(d)} per vine and
    L^{O(dP)} in total, which is absorbed by the slack L^{(100d)³P} in (flowerest2).
  - The constant "20" must read "C".
- (5), (7): LF twisting, stem layers. B (the argument in (7) works for any SG (CL) vine).

**DH23 §11.2 and TARGET Prop `fixedpoint`:** no vines.

---

## 4. Item 4 — Prop 9.6 case (5) via Prop 10.4(1), and the explicit ylem1′ list

### 4.1 Case (5) (DH23 L1887–L1889) does not depend on the vine family. PROVED; CHECKED

**Setting.** In case (5), V_α = V_β = 1:
- operation (c) removes the chain containing the α-atom;
- operation (d) replaces the other chain, if any.

This gives 𝕄₁ with:
- two atoms of degree 3 and all others of degree 4, so E = 2V − 1;
- at most one triple bond;
- DH23's β-cut hypothesis.

Prop 10.4(1) then gives 𝔄₁ ≲ L^{−4γ₀/7}, unless 𝕄₁ is "vine (II) with its joints removed and a bond added at one
joint".

**Lemma 4.1 (exceptions of Prop 10.4(1)). PROVED.** Under the hypotheses of Prop 10.4(1), the case in which the proof
cannot reduce to Prop 10.2 occurs exactly for 𝕄 ≅ Q′_m (m ≥ 1). Here Q′_m is vine (II) with m double bonds, its joints
removed, and one bond added between the two neighbours of one joint; Q′₁ is a bare triple bond on two atoms.

*Proof.* There is at most one triple bond, so there is at most one (Y) sequence (DH23 L1959–L1962). Its end is one of
the following:
- no triple bond, so 𝕄′ = 𝕄;
- a (Y2);
- a (Y1) with one external bond;
- a (Y1) with two external bonds at one atom, which the β-cut hypothesis excludes;
- a (Y1) with no external bond.

In the first three cases 𝕄′ has E = 2V − 1 and no triple bond, and Prop 10.2 together with ylem2 gives
L^{−3γ₀/5}(log L)^C. In the last case the sequence has consumed a ladder from the triple bond up to an isolated triple
pair. Undoing it rebuilds exactly Q′_m. ∎

**Q′₁ and F72.** Q′₁ is the "length-1 omission" of YLEM1. With F72/E0 (vine (II) includes m = 1), Q′₁ is the m = 1
member of DH23's own exception.

**Case (5) with 𝕄₁ ≅ Q′_m.** Then 𝕄₀ is a vine (II):
- 𝕄₀ has no triple bond, since 𝕄_fin has none (Prop 9.5).
- So the β-atom subdivides a copy of 𝕄₁'s triple bond.
- If the β-atom lay in the α-chain, the triple bond of 𝕄₁ would already lie in 𝕄₀, a contradiction.
- So the α-chain is a single α-atom joining the two degree-3 atoms.

A vine (II) component is LG (Prop 9.5), which contradicts its α-joint (DH23's own conclusion). Vine (II) belongs to
both families, so nothing depends on the choice of family.

**T-type 𝕄₁ are never exceptional.** Suppose 𝕄₁ together with a bond between its degree-3 atoms is T-type. Then the
sequence ends in "none", "(Y2)" or "(Y1), one external bond", and 𝕄′ has no triple bond and E = 2V − 1. So Prop 10.2
applies.

**The smallest case 𝕄′ = T∖ℓ, directly** (the worry flagged in REF):
- Bonds: s (single, between the two degree-3 atoms A and C), p, p′ (A=B) and q, q′ (B=C).
- Tuples: the counting problem contains the tuples {(s,p,p′), (s,q,q′)}. s occurs in both, with opposite signs. Neither
  tuple has three equal signs, since the atoms are balanced.
- Count: DH23 Lemma A.3(4) applies (L2106), using the form (countc2-1), and gives 𝔠 ≲ δ⁻²L^{3d−4γ} for γ ≤ 1/2.
  The third resonance condition, at B, is not even used.
- Conclusion: with χ = 3,

  𝔄(T∖ℓ) ≲ δ⁻²L^{3d−4γ} · L^{−3(d−γ)} δ^{3/2} = δ^{−1/2} L^{−γ} = δ^{−1/2}L^{−γ₀}.

  For γ > 1/2 one gets δ^{−1/2}L^{−γ₀−10η}. Either way this beats L^{−4γ₀/7}.

CHECKED (`p104_check.py 7`, 0 failures). The check covers all 327 connected loopless multigraphs with two degree-3
atoms, all others of degree 4, at most one triple bond and ≤ 7 atoms. Results:
- "(Y1), no external bond" occurs exactly for Q′₁, Q′₂, Q′₃.
- The 14 T-type ones end in "none", "(Y2)" or "(Y1), one external", with triple-free end states and E = 2V − 1.
- Their 3-atom end states are T∖ℓ.

### 4.2 The explicit ylem1′ list. PROVED; CHECKED

**Notation.** T has atoms e, f, g, all pairs doubled. T_n := Z_n(T, e–f), with ladder atoms a_j, b_j (1 ≤ j ≤ n),
a₁ ≡ b₁, and connections e–a_n, b_n–f. Up to the reflection a ↔ b, e ↔ f, the non-triple bonds of T_n fall into five
classes:
- **ef**: the remaining copy of e–f;
- **eg**: a copy of e=g, equivalently of f=g;
- **conn**: e–a_n, equivalently b_n–f;
- **rail j**: a_j–a_{j+1}, for 1 ≤ j < n;
- **rung j**: a copy of a_j=b_j, for 2 ≤ j ≤ n.

**Lemma 4.2 (ylem1′, explicit).** A connected loopless 4-regular multigraph with at most two triple bonds (Y)-reduces
to Q or T iff it is isomorphic to one of the graphs in the table below. Every balanced orientation is allowed, since
(Y)-reduction ignores orientation (Remark after Lemma 1.4).

| Family | Closure of |
|---|---|
| Q | (II), m = 1 |
| Q_k := Z_k(Q), k ≥ 1 | (II), m = k + 1 |
| T | **new** (the three 5-atom T-beads) |
| T₁ | **new** (the five 7-atom T₁-blocks) |
| T_n, n ≥ 2 | (V); also (VIII) for n ≥ 3 |
| Z_m(T_n, ef) | (IV) |
| Z_m(T_n, eg) | (III) |
| Z_m(T_n, rung j) | (VII) |
| Z_m(T_n, rail j), min(j, m) ≥ 2 | (VI) |
| Z_m(T_n, rail j), min(j, m) = 1 | **new** |
| Z_m(T_n, conn) | **new** |

Here Z_m(T_n, rail j) ≅ Z_j(T_{n−j+m}, rail m), so only min(j, m) matters.

*Proof.*
- **⇐** Each listed graph reduces by construction, since (Y) inverts (Z).
- **⇒** By Lemma 1.4 and the counting in Lemma 1.7, there are at most two sequences, all (Y2).
  - The first undone (Z) acts on Q or T. All bond copies of Q are equivalent; all bond copies of T are equivalent up to
    orientation, which is irrelevant.
  - A second (Z) on Q would create a third triple bond. So the Q-branch is {Q, Q_k}.
  - On T_n the second (Z) acts on a non-triple bond, which lies in one of the five classes above. ∎

The drawn/new column is CHECKED, not proved. The (VI) condition agrees with YLEM1: "interior rail and second chain with
≥ 2 pairs".

**Checks.**
- `ylem1_list.py 7 13`, `out_ylem1_7_13.txt`: brute force over all 78 connected loopless 4-regular multigraphs with
  ≤ 7 atoms and ≤ 2 triple bonds. The Y-exceptional ones are exactly the list (9 graphs).
- Same file: the T-type part of the list up to 13 atoms equals the undirected projection of the pinned enumeration
  (38 = 38).
- `out_ylem1_tags17.txt`: the drawn/new column, up to 17 atoms.
- YLEM1's earlier brute force reached 15 atoms.

**Consequence for T-vines (Lemma 1.7).** The closures of T-vines are exactly the T-part of the list. The joints must
subdivide one copy of each triple bond (two triple bonds), or one copy of the triple bond plus any other copy (one
triple bond).

---

## 5. Item 5 — the γ-dependent vine family

### 5.1 Definition (for a Lean successor of B2 `VineType` / `IsVine`)

The definition uses B2's half-edge molecules and B2's undirected conventions (`IsBlock`, `bondsBetween`,
`GroupConnected`). B2's `IsVine` has no direction clause; the block axioms supply balance.

**Definition 5.1.** Fix an atomic group S ⊆ M.atoms and joints j₁ ≠ j₂.
1. **Closure** `cl S j₁ j₂`, an undirected loopless multigraph on S ∖ {j₁, j₂}. Keep the bonds of S not incident to a
   joint, and add the following.
   - If σ = 0: for each joint, one bond between its two S-neighbours.
   - If σ = 1: one bond between the S-neighbour of j₁ other than j₂ and the S-neighbour of j₂ other than j₁.

   It is undefined if a loop would arise, or if σ ≥ 2. The case σ = 2 is vine (I).
2. **(Y2) step** on finite undirected loopless multigraphs: G ⟶ G′ if all of the following hold:
   - G has atoms a ≠ b joined by exactly 3 bonds;
   - a has exactly one further bond, to c; b has exactly one further bond, to d;
   - c ≠ d;
   - G′ = G − {a, b} + one bond {c, d}.
3. **T-vine.**
   `IsTVine S j₁ j₂ :⟺ IsBlock S j₁ j₂`
   `∧ (∀ u v ∈ S, u ≠ v → bondsBetween u v ≤ 2)`
   `∧ (∀ v ∈ S, v ≠ j₁ → v ≠ j₂ → GroupConnected (S.erase v))`
   `∧ ∃ G′, ReflTransGen (⟶) (cl S j₁ j₂) G′ ∧ G′ ≅ T`,
   where T is the three-atom multigraph with every pair doubled.
4. **The family.**
   - `IsVineEnl S j₁ j₂ :⟺ IsVine .I S j₁ j₂ ∨ IsVine .II S j₁ j₂ ∨ IsTVine S j₁ j₂`.
     Bad vines are (I) and (II); normal vines are the T-vines.
   - `IsVineγ γ S j₁ j₂ :⟺ (γ ≤ 1/2 ∧ IsVineEnl S j₁ j₂) ∨ (1/2 < γ ∧ ∃ X, IsVine X S j₁ j₂)`.
   - HV, VC and HVC are defined from `IsVineγ` exactly as from `IsVine`.

**Why this form.**
- **The (Y2) target.** "∃ path of (Y2) steps to T" equals "the normal form is T" by Lemma 1.4. It needs no confluence
  lemma in Lean, and the definition does not mention (Y1).
- **(II) needs no new predicate.** "Q-type" with the same clauses and target Q coincides with B2's `IsVine .II`
  (Def 1.2). So (II) can stay a template.
- **Equivalent generation, for proofs** (Lemma 1.7). cl(S) ∈ {T, Z_k(T), Z_{k′}(Z_k(T), ℓ′)}, with ℓ′ in the five
  position classes of §4.2.
- **Equivalent rung-closure form.** The T-vines are the closure under rung insertion at 2-edge-cuts (Lemma 1.9(2)) of
  the finitely many T-vines with D = 0. There are 94 directed classes (8, 32, 40, 14 with 5, 7, 9, 11 atoms; `out_explore11.txt`, together with the bound
  |B| ≤ 11 when D = 0).
  This is a finite template list plus one operation. It is useful for decision procedures, but it is not the
  definition proposed here.

**Lemma 5.2 (𝒱_{>1/2} ⊂ 𝒱_{≤1/2}). PROVED; base CHECKED.** Every expansion T_X(k⃗) of the B2 templates X = III–VIII
is a T-vine. Every expansion of II is Q-type.

*Proof.*
- **Base.** For k⃗ = 0, and more generally k_s ≤ 2: the shape (block degrees, no triple bond, no interior cut atom) and
  the reduction of the closure to T (resp. Q) are CHECKED (`drawn_check.py 2 15`).
- **Slots.** Every slot of III–VIII is a 2-edge-cut whose two sides both contain an interior atom (CHECKED).
- **Induction.** Inserting k rungs at a slot is k successive rung insertions at 2-cuts of this kind, so Lemma 1.9(2)
  applies. ∎

The same script checks that the undirected T-vine shapes with ≤ 15 atoms number 3, 5, 10, 14, 21, 27 for
5, 7, …, 15 atoms. Of these, 3, 5, 7, 9, 12, 14 are not drawn. This matches N1 §4.

### 5.2 Why γ-dependent, and the uniform alternative

**For γ > 1/2, DH23's own normal-vine estimate is not checked for T-vines.** That estimate (Prop 7.6, Step 2, L1584–L1594)
is a counting argument with a single zero-gap ladder: "the ladder L¹ estimate … only to the zero-gap ladder". This has
not been checked for T-vines; doing so would mean redoing REF's "Step 2" item.
- HEURISTIC: it extends. Zero-gap rungs of a T-vine lie in ≤ 3 ladders; r-gap rungs gain L^{−10η} each; the core count
  (A.2(3), γ > 1/2) has the same form.
- Not needed: F75 closes case (4) for γ > 1/2 with the original family.

**So the minimal repair is γ-dependent (Definition 5.1).** It also leaves the frozen γ > 1/2 statements built on B2's
`IsVine` untouched.

**Uniform alternative, TARGET chain only.** TARGET never cites DH23 Prop 7.5/7.6. Its citations are DH23 4.11, 4.12,
4.13, 5.3, 6.1, 6.3, 6.5, 6.6, 8.1, 9.1, 9.4, 9.5, 9.6, 10.2, §10.5, A.2, A.3, A.4. TARGET proves its own normal-vine
bound, Prop `vineest`, from Prop `sumint`, which holds for **all** γ ∈ (0,1); T-vine units meet its hypotheses literally
(REF `refcheck.py`, up to 17 atoms; Prop 1.17 for all sizes). The remaining inputs are γ-independent:
- the combinatorics of §1 and §2;
- case (4) through the enlarged family (CASE4 Lemma 2.4 needs only γ ≤ 1 − 2η).

Hence, for the TARGET chain, 𝒱_enl could be used for **all** γ, and F75 would not be needed. This is HEURISTIC to the
extent that it relies on no other TARGET-internal use of DH23 Prop 7.6 Step 2; the citation list says there is none.
Recommendation: keep Definition 5.1 (γ-dependent) for the formal successor, and record this as an option.

### 5.3 Every statement that mentions vines, and the family it needs

The list comes from `vine_mentions.py` (`out_vine_mentions.txt`): every labelled environment and proof containing
"vine", plus the vine lines in running text.

**Legend.**
- **G**: generic; holds for 𝒱_γ given (F1)–(F6) and Corollary 1.16.
- **B**: concerns bad vines (I)/(II) only; identical in both families.
- **F≤**: needs the γ ≤ 1/2 family, with the stated replacement.
- **any**: holds for either family as written.

**DH23**

| Statement (lines) | Need | Note |
|---|---|---|
| Intro L379–L628 (incl. L586 "(Y)-reduce to Q or T … exactly vines (II)–(VIII)") | — | Expository. L586 is false for (I)–(VIII) and true for 𝒱_enl (YLEM1, Lemma 4.2). |
| Def `defmole0` L633, Rem L617 | B | Passing mention. |
| Def 4.10 `defblock`, Lemma 4.11 `disjointlem`, Prop 4.12, Cor 4.13 | G | (i)/(ii) for 𝒱_enl objects: (F1). |
| **Def 5.1 `defvine` L790** and Rem `remilia` L801 | **F≤** | Replace by 𝒱_γ (Definition 5.1). L792 "easy to verify (i)/(ii)": (F1). "σ(V) = 0 except (V) and (I)" fails for σ = 1 T-vines; harmless, see N6. |
| Prop 5.3 `molecpl` + Rem `molecplrem` | B | "Core" = bad and not (II-e); T-vines are non-core. |
| Def `twist`, Rems `explaintwist`, `twistexplain`, `dectwist`, Def `twistrep`, Def `twistgen`, Rem `fulltwistrep` | B | Codes of non-core (CL) vines have two elements, generically; this covers T-vines. |
| §7.2 L1385, Prop 7.5 `estbadvine` | B | — |
| **Prop 7.6 `estnormalvine`** | **F≤** for γ ≤ 1/2 (Step 3); original family for γ > 1/2 (Step 2) | γ ≤ 1/2: N1 Theorem N with Cor `sumintest3` (REF CONFIRMED); all sizes by Prop 1.17. γ > 1/2: §5.2. |
| Rem `extravar` | G | — |
| Lemma 8.1 `vinechainlem` | G | DV → DV′ (two σ = 1 members of 𝒱_γ sharing both joints); proof verbatim (N6). |
| Def `defcong`, Def `defdiff` | G | Ladder gaps in T-vines are in {0, ±r} (N1 Lemma D). |
| §8.2 L1643–L1652, Prop `red1step`, L1680 | G | Normal units are chains of T-vines (Prop 7.6′). |
| Proof of `kqmainest1` (L1692ff.), L1826 "O(1) ladders/atoms per vine" | G | §2.4 constants. |
| Prop 9.1 `subpro` + Rem `subcondition` | G | Uses Lemma 8.1′, Cor 4.13 and `subsetvc`′ (Cor 1.16). |
| Step 1 L1775, **Prop 9.4 `excessprop1`** | **F≤** (count) | Step-1 deviation for T-vines and T-type sub-objects: N1 §3.2 row, REF re-derived; all sizes by Prop 1.17. Read "all SG objects" as "maximal SG objects" (Cor 1.16(5)). |
| Prop 9.5 `finalmole` | G | Via subpro (f). |
| **Prop 9.6 `lgmolect`**, proof L1854–L1897 | **F≤** for case (4) at γ ≤ 1/2; **any** for case (4) at γ > 1/2 (F75); **any** for case (5) (§4.1) | Case (4)′: N1 + REF (ylem1′ + 9.5′ + CASE4 Lemma 2.4). |
| Prop 10.4 `moleprop4` + proof; Lemma `ylem1` + proof | **any** | Replace `ylem1` by Lemma 4.2. Replace (2)'s hypothesis by "not Y-exceptional" (YLEM1 R2). (1)'s exceptions are Q′_m (Lemma 4.1). |
| §10.5 L1981, L1985 | G | — |
| §11.1.1 L2012 | B | §3. |
| **Prop `subsetvc` L2128** | **F≤** | Replace by Cor 1.16(2): add block VC:I+I (missing even for the drawn family), block T-vines and their HVs. |
| Proof of `timeFourierlem` L2146 | G | — |

**TARGET**

| Statement (lines) | Need | Note |
|---|---|---|
| Intro L394, L520–L536 | — | Expository; L536 cites DH23 9.6. |
| **Def `defvine` L1384** | **F≤** | 𝒱_γ. "Ladder ≥ 2 double bonds": unchanged. |
| Prop `molecpl`, Rem L1425, Def `twist`, Rems `explaintwist`/`twistexplain`, Fig L1458, Def `lftwist`, Prop `lftwistprop` | B | — |
| **Def `cohmol` L1489** | **F≤** | Groups of a T-vine = its 2-cut pieces (rungs, non-rung 2-atom pieces, the core); N1 §3.2. |
| **Prop `layervine` L1513** + proof | **F≤** | Needs spine + at most one "ladder + (D)" pendant attached by a 2-cut (Prop 1.17, CHECKED to 17; all sizes by deletion), and the L1519 constant (§2.4). |
| Prop `layerlad`, `ladderl1new`, `ladderl1old` | G | Ladders only. |
| Prop `sumint` (proof mentions vines once) | G | — |
| §9.2 L1723–L1741, **Prop `vineest` L1742** + proof | **F≤** (T-vines as Nor units) | REF CONFIRMED the literal hypotheses; Prop 1.17 extends to all sizes. Erratum E4 (TARGET Step 3) unchanged. |
| §10 L1926–L1977 (stage 1), Lemma `vinechainlem`, Def `defcong`, Def `defdiff` | G | DV′. |
| Prop `subpro` L2040 | G | — |
| §11.1 L2072–L2117 (𝒞₂ = maximal SG sub-objects) | G | Needs Cor 1.16(5) (disjointness). |
| Rem `remtame`, Operation 1 text L2140/L2148 | G | — |
| **Prop `excessprop1` (1)–(3)** | (1) **F≤** (via DH23 9.4); (2) **F≤** (§2.1); (3) G | — |
| Prop `finalmol`, Prop `lgmolect` + proof | G (perfect components via DH23 9.6, as above) | §2.3. |
| Proof of (finalcount1) L2213, Rem `remtame2` | G given §2.4 | — |
| §12, Prop `flowerest1` (L2287–L2305) | G/B | §3; "20 variables" → C. |
| **Lemma `subsetvc` L2431** | **F≤** | List of Cor 1.16(2). TARGET's list already includes "two double bonds" and "vine (V)" blocks. |
| Table L2575–L2602 | — | Notation. |

### 5.4 What a formal successor needs, in dependency order

1. Definition 5.1, and Lemma 5.2 (drawn ⊂ T-vines). Lemma 5.2's base is the six templates III–VIII with k⃗ = 0, plus
   the 13 slot facts.
2. Lemmas 1.4–1.6 (confluence; rung deletion; pendant poles). These are statements about (Y2) on multigraphs and are
   γ-free.
3. Lemma 1.7 (generation) and Lemma 1.8 (size bound).
4. Lemmas 1.9–1.14, and Theorem 1.15 with a finite base.
   - The base, checked here in Python, consists of all T-vines with ≤ 13 atoms (1586 directed classes) and all
     families of disjoint sub-objects on them.
   - A Lean development needs either a verified enumeration of the base or hand proofs of the 13-atom cases.
5. Corollary 1.16, Proposition 1.17, then the statements marked F≤ in §5.3.

---

## 6. Item 6 — corrections to N1

**E1 (REF E1): overstated label.**
- N1 §0 item 2, §2.5 and §3.2 say the combinatorial finite facts "extend to all sizes by a rung-locality argument
  (PROVED, §2.5)". §2.5 covers only the analytic piece data, and as a sketch. The combinatorial facts were CHECKED to 13
  atoms in N1 and to 19 in REF.
- **Correction:** the facts are now PROVED for all sizes by Theorem 1.15 and Corollary 1.16 of this note. Their base is
  CHECKED (≤ 13 atoms needed; ≤ 19 run).
- N1 §2.5's analytic reduction is replaced by Prop 1.17.

**E2 (REF E2): false side claim.**
- In N1 §3.2, row "Lemma 8.1 / `vinechainlem`", delete "Such a union has its joints of degree 3, so it is the whole
  molecule, exactly as for DV". REF's counterexample: two 5-atom σ = 1 T-vines glued along 3→4, plus 3→ρ→4.
- **Replace it with DH23's own sentence (L1621):** a third maximal object meeting one of the two vines would produce a
  saturated component.
- The uniqueness proof is unchanged (N6).

**E3 (REF E3): invalid route.**
- N1 §7, item 2 says the integrality conditions "can be avoided by doing Poisson summation in the original bond
  variables (Lemma C is coordinate-free)". This does not factorize: Lemma D's splitting is not orthogonal, and its
  conditioning is not uniform along ladders.
- **Delete it.** The valid route is DH23 `sumintest1` Step 1 / TARGET `sumint` Step 1: piece variables and product
  cutoffs. Their conditions (i)–(iii) hold (REF `refcheck.py`), with C3 as an old caveat.

**E4 (REF E4): unnecessary generalization.**
- N1 §3.2, row "Prop 7.6′", and §6 step 5 propose a "cosmetic generalization" (r-linear phases involving all
  variables). It is not needed:
  - each rung's ζ_j and the core's ξ involve only the piece's own variables and r, with coefficients in {0, ±1};
  - only intermediate-joint coefficients involve other units, which Cor `sumintest3` (L1374) already allows.
- **Delete step 5 of §6.** Prop 7.6′ follows from Theorem N and Cor `sumintest3` / Prop `sumint` as stated.

**E5 (REF E5): Q1 headline.**
- **Per couple.** The per-couple size is 2^{−n} δ^{2m+2−d} L^{−γ(2d−1)} = (δ^{1/2}/2)^n δ^{1/2−d} L^{−γ(2d−1)}. The
  headline (Cδ^{1/2})^n L^{−γ(2d−1)} drops the fixed factor δ^{1/2−d}.
- **Range.** It is valid for m ≥ d/2, where larger gaps do not change the exponent (N1 §1.1).
- **Status.** It rests on F73 (a CANDIDATE), so it is HEURISTIC as asymptotics.
- **Correction:** read "≈ (Cδ^{1/2})ⁿ δ^{1/2−d} L^{−γ(2d−1)}, m ≥ d/2, HEURISTIC" in N1 §0 item 4 and §1.

**N6 (new; refines E2): Lemma 8.1′ and "σ(V)".**
- DV′ := the union of two σ = 1 members of 𝒱_γ sharing both joints. DH23's proof of Lemma 8.1 then holds verbatim.
  Scenario (a) of `disjointlem` forces σ = 1 for both. A third maximal object meeting one of them would raise both
  joints to degree 4, giving a saturated component; scenarios (b) and (c) contradict maximality.
- DH23 L790 "σ(V) = 0 for all vines except (V) and (I)" is false for σ = 1 T-vines: 62 directed classes up to 13 atoms.
  The only use of σ = 1 is Lemma 8.1, so the replacement "σ = 1 members" suffices.

**N7 (new): `subsetvc`′ list.**
- N1's list for `subsetvc`′ ("a double bond, two double bonds (or its adjoint), a T-vine, or the adjoint of a T-vine")
  is correct for T-vine ingredients.
- It must add one degenerate case: the joint double bond of an HV of a σ = 1 vine (Cor 1.16(1)).
- It must add the containment rule (no straddling) and the family version of connectivity, as Cor 1.16 states. N1 and
  REF checked only single removals and pairs.

**N8 (new): the "equivalent explicit list" of N1 §3.1.**
- N1 §3.1 says cl(B) is "T; T₁; Z_m(T_n, ℓ′); a closure of (III)–(VIII)". That is correct, but it leaves T_n (n ≥ 2)
  inside "closures of (V)/(VIII)" and the positions ℓ′ implicit.
- Replace it by Lemma 4.2.

---

## 7. Residual risks (refute-first summary)

**What I tried to break, and what happened.**
- **Lemma J** (joints in rungs): 141 832 incidences ≤ 19 atoms, 0 exceptions.
- **Deletion transfer** (type, gap, connectivity, pairs): 772 066 images and 1.26 M pairs ≤ 19 atoms, 0 changes.
- **The size bound:** tight at d = 0, …, 4.
- **The gap criterion vs. linear algebra:** 0 disagreements ≤ 11 atoms.
- **Families of disjoint sub-objects:** all families ≤ 17 atoms, 0 disconnections.
- **Overlap classification:** only double-bond pairs ≤ 19 atoms.
- **Pieces under deletion:** 43 596 deletions ≤ 17 atoms.
- **Prop 10.4(1) exceptions:** brute force ≤ 7 atoms.
- **ylem1′ list:** brute force ≤ 7 atoms (YLEM1 reached 15), and the pinned enumeration ≤ 15.
- **Drawn templates:** all expansions with k_s ≤ 2.
- **A false expectation caught.** My first `p104_check.py` asserted that T-type 𝕄₁ always end at T∖ℓ. It failed (5- and
  7-atom end states, and "(Y1), one external" endings). The correct statement, now checked, is that they always end in
  a case that Prop 10.2 covers (§4.1).

**Not closed, or closed only at sketch level.**
1. **The `layervine` spine/pendant structure is CHECKED to 17 atoms; the all-size argument is a sketch** (Prop
   1.17(c)). The piece invariance (Prop 1.17(a)) and Theorem N for all sizes (Prop 1.17(b)) are PROVED; TARGET
   `excessprop1` (2) and the Step-1 deviation use only those.
2. **The base cases are Python checks.** For Lean they are a finite enumeration of 1586 directed T-vines with ≤ 13 atoms,
   including families.
3. **The uniform family for TARGET (§5.2) is HEURISTIC/unverified.** So is DH23 Prop 7.6 Step 2 for T-vines at
   γ > 1/2. Neither is needed with Definition 5.1.
4. **Old caveats C1–C3 (REF) are unchanged:** the sign of the core normal form (F79), |r| ≲ L^{−γ−η} versus
   L^{−γ+η} in `sumintest1/2`, and T₁⁻¹ entries ±2. All are blind to the vine family.
5. **The drawn/new column of Lemma 4.2 is CHECKED to 17 atoms.** Families with min(j,m) ≥ 2 at rail j are identified
   with (VI) by YLEM1's parametrised check (to 27 atoms). The "⇔" of Lemma 4.2 itself is PROVED.

---

## 8. Files (run `python3 -I <script> <args>` in this directory)

| script | checks | output |
|---|---|---|
| `tv.py` | library: (Y)-reduction, blocks, closure, sub-object enumeration, rungs, deletion, (Z)-generation | — |
| `t_gen_check.py 15` | generator = pinned `zgen.py` (4446 classes); Definition-1.2 predicate; confluence (fixed order vs. order search) | `out_gen15.txt` |
| `lemmas_check.py 19 11` | Lemmas 1.10, 1.11, 1.13, 1.14 (deletion transfer), size bound | `out_lemmas19.txt`, `out_lemmas15.txt` |
| `item1_check.py 19 17` | Theorem 1.15 (F1)–(F6) on all T-vines ≤ 19; families exhaustive ≤ 17 | `out_item1_19.txt`, `out_item1_15.txt` |
| `pieces_check.py 17` | Prop 1.17: pieces under deletion, piece shapes, ladders, `layervine` structure | `out_pieces17.txt` |
| `qcheck.py 7` | Q-type blocks = vine (II); their sub-objects (Cor 1.16(2)) | `out_qcheck7.txt` |
| `drawn_check.py 2 15` | Lemma 5.2 (B2 templates are T-vines / Q-type; slots are 2-cuts); shape counts | `out_drawn_2_15.txt` |
| `ylem1_list.py 7 13` | Lemma 4.2 vs. brute force and vs. the pinned enumeration | `out_ylem1_7_13.txt` |
| `ylem1_tags.py 17` | drawn/new column of Lemma 4.2 | `out_ylem1_tags17.txt` |
| `p104_check.py 7` | Lemma 4.1 and the T-type endings (§4.1) | `out_p104_7.txt` |
| `vine_mentions.py` | the statement inventory of §5.3 | `out_vine_mentions.txt` |
| `explore.py` | exploration only (examples) | — |

Pinned inputs: `pinned/` (`mg.py` and `zgen.py` from N1; `subcheck.py`, `refcheck.py`, `straddle.py` from REF).
Their hashes are in `pinned/PINNED_SHA256.txt`; hashes of this directory are in `SHA256SUMS`.
