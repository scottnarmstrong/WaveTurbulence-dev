# Repairing the TARGET/DH23 proof chain for 0 < γ ≤ 1/2 (F69b / E1): research notes

Date: 2026-11-04. Author: research agent launched by wt-orch (packet "research-gamma-half"). No Lean. No repository
or other scratch directory was edited (the earlier enumeration `<scratch>/case4-gamma-half/classes.json` is read only
to cross-check my own, independent enumeration).

Sources, with line numbers:
- **DH23** = `wave-turbulence/references/src-2301.07063/Revision_Submit.tex`;
- **TARGET** = `wave-turbulence/paper/source/WKE-Longer_times_Final_arXiv.tex`.

Earlier campaign notes:
- **E1** = `docs/ERRATA-AND-DEVIATIONS.md` E1;
- **CASE4** = `docs/research/dh23-prop96-case4.md`;
- **F73** = `docs/research/kqmainest1-necklace.txt`;
- **F75** = `docs/research/case4-gamma-above-half.txt`;
- **VINE2** = `docs/research/vine2-m1.txt`;
- **YLEM1** = `docs/research/ylem1-investigation.md`.

Labels used for claims:
- **PROVED** — the proof is written here;
- **CHECKED** — verified by a script in this directory (§8);
- **HEURISTIC** — not proved.

---

## 0. Verdict

**Recommendation (i): the repair is feasible, and the plan is clear.** No new analytic estimate is needed.

1. **The analytic input already exists.** F73 asked for a "Prop 7.6-type estimate for T-type blocks". It is DH23's
   own Corollary `sumintest3` (L1374), and TARGET's own Prop `sumint` (L1595), applied unchanged.
   - A T-type block satisfies their hypotheses once it is parametrized along its **2-bond cuts** (§2).
   - Every T-type block decomposes as: its two joints, one "core" piece of 3 atoms, and 2-atom "rung" pieces. The core
     has exactly the shape of DH23's normal-vine cores, Fig. VineAnnotated (B), (C) or (D).
   - A T-type block is therefore literally a normal vine in the sense of the estimates. Only the drawn list in
     Def 5.1 / Fig. Vines misses it.
   - Each T-bead and each T-type block is **exactly neutral**: no gain, no loss. That is all that splicing needs.
   - So no cancellation and no new log-free time bound are required. The only loss is the usual L^{η⁴} (DH23) or
     L^{η⁷} (TARGET) per spliced chain. The stage-2 cut at the hinge atom pays for it, exactly as for the drawn
     normal vines.
   - Status: PROVED (Lemma D, Lemma C, Theorem N), with the finite part CHECKED on all 4446 directed T-type classes
     with ≤ 15 atoms, both choices of lower joint, 0 exceptions.
2. **Each combinatorial extension can be stated, and each is checked by computer with no failures.** They are needed
   when T-type blocks join the vine family:
   - DH23 Lemma 4.11 hypotheses;
   - Lemma 8.1 / TARGET `vinechainlem`;
   - `subsetvc` (new sub-object types appear);
   - Props 9.1, 9.5 / TARGET `subpro`, `finalmol`;
   - the Step-1 deviation;
   - TARGET Def `cohmol`, Prop `layervine`;
   - case (4) of Prop 9.6.

   Each is a generic DH23 proof plus a finite template fact. Each finite fact is CHECKED on all T-type blocks with
   ≤ 13 or ≤ 15 atoms (§3) and extends to all sizes by a rung-locality argument (PROVED, §2.5).
3. **No alternative route avoids T-blocks (§5).**
   - Reordering stage 2 is refuted.
   - Bookkeeping inside stage 2 is refuted.
   - Changing ρ needs the same analytic input as splicing and more restructuring.
   - The only other option is D9's restriction to γ > 1/2.
4. **Heuristics (Q1).**
   - The necklace couples are small: per couple, and hence per congruence class (the class is the couple itself),
     about (Cδ^{1/2})ⁿ L^{−γ(2d−1)}.
   - E1's "O(L^{γ−d})" is right at γ = 1/2. For γ < 1/2 it is optimistic by L^{d(1−2γ)}, but the size is still a fixed
     negative power of L.
   - With the repair, the main theorems follow for γ ≤ 1/2 by the papers' own argument. So "plausibly true" becomes
     "true modulo writing the combinatorial extensions".

Residual risks (§7) are combinatorial bookkeeping, not mathematics:
- the full write-up of the enlarged-family lemmas for the infinite T-vine families;
- TARGET's layering lemma;
- the flower-tree/parametrix sections.

The B2 Lean template API would need a predicate-based vine family.

---

## 1. Q1 — heuristic size of the necklace couples

**1.1 Per couple.** This is F73 (0.1), re-derived as a bookkeeping check. HEURISTIC; F73 has the asymptotics.
- **Setting.** N_m has n = 4m+3 atoms and λ := δL^{2γ}.
- **Per T-bead.** 4 atoms, 4 free vectors and 2 effective resonances give
  (δ/2L^{d−γ})⁴ L^{4d} λ^{−2} = δ²/16. This is exactly neutral.
- **The other three atoms** (o₁, o₂, w₀, with free vectors s, s′, r) give (δ/2L^{d−γ})³ L^{3d} λ^{−1−d}. The
  r-integral over |r| ≲ 1/λ contributes λ^{−d}.
- **Total:** |K_Q| ≈ 2^{−n} δ^{2m+2−d} L^{−γ(2d−1)}.
- **Comparison with E1's L^{γ−d}:**

  L^{−γ(2d−1)} / L^{γ−d} = L^{d(1−2γ)} ≥ 1.

  The two agree at γ = 1/2. For γ < 1/2, E1's "O(L^{γ−d}) per congruence class" is too optimistic (the referee
  noticed this already). The correct heuristic is **O((Cδ^{1/2})ⁿ L^{−γ(2d−1)})** per class. The class of a necklace
  couple is {Q}: no vines and no twists, and with the repair T-vines are normal, so they have no twists either.
- **Larger gaps.** Gaps with |r| ≫ 1/λ give a further factor (λ|r|)^{−(2m+1)} (F73 §2.5). They do not change the
  exponent for m ≥ d/2.

**1.2 Total.** HEURISTIC, and a consequence of the repair (§4).
- There are at most Cⁿ necklace couples of order n, each of size ≲ (Cδ^{1/2})ⁿ L^{−γ(2d−1)}.
- The sum over n ≤ N² is ≪ L^{−η⁸}, which is what `mainest1.5` (DH23 L505) needs. So the necklaces do not threaten
  the main theorems.
- The general danger would be (Cρ)!-many couples with only a bounded gain in L. The repair excludes it: after T-chains
  are spliced, every congruence class satisfies DH23 `kqmainest1` with ρ = ρ_sub. The necklace has ρ_sub = O(1), and
  its true size L^{−γ(2d−1)} is consistent with L^{−η⁷ρ_sub}.
- **Answer to Q1:** confirmed, with the corrected exponent. The contribution is small, and nothing suggests that the
  main theorems fail for γ ≤ 1/2.

---

## 2. Q2(a) — the estimate needed for T-type blocks, and its proof

### 2.1 What has to be estimated

Fix the setting of DH23 Section 7.2 (L1387ff.):
- **The block.** A (CL) block B ⊂ 𝕄(𝒬₀) with upper joint v₁ (node 𝔲₁, merged on splicing) and lower joint v₂.
- **Variables.** A := (interior atoms of B) ∪ {v₂}, which are exactly the branching nodes 𝒬₀[B]∖{𝔲₁}, and
  N := |A|.
- **Free vectors.** Once the outer vectors (k_{𝔲₁}, k_{𝔲₁₁}, k_{𝔲₂₁}, k_{𝔲₂₂}) are fixed, the bond vectors of B
  are affine in N free vectors z ∈ (ℤ_L^d)^N and in the gap r.
  - The count is E_B − (#interior + 1) = (2·#interior + 2) − #interior − 1 = N.
  - The conservation matrix of a directed graph is totally unimodular, so the free vectors can be taken to be bond
    vectors themselves.
- **The phase.** It is exp(−iπλ Σ_{w∈A} Γ_w (t_w − t_{𝔲₁})), where
  - Γ_w = Σ_{out}|k|² − Σ_{in}|k|²;
  - at v₂ only the two block bonds count; its outer part is a constant;
  - this is the identity used in DH23 L1409–L1419.
- **Neutral normalization:** the block contributes (C⁺δ^{1/2})^N, i.e. L^{(d−γ)N} δ^{−N/2} decorations against
  (δ/L^{d−γ})^N.

**Needed (the precise analogue of DH23 Prop 7.6, (vinebound3)).**

> **Prop 7.6′** (T-vine chains, 0 < γ ≤ 1/2). Let 𝐕𝐂 be a (CL) chain whose ingredients are T-vines (Def 2.6 below).
> T-vines include the drawn (III)–(VIII), and every gap satisfies |r| ≤ L^{−γ+η}. Fix (𝒬^sp, 𝔫, 𝒜^sp) and, for each
> ingredient, (cod, ind, ℬ) as in DH23 Prop 7.6. Then for θ ∈ {η⁵, 0},
>
>   ‖e^{−πiδL^{2γ}t_{𝔲₁}Γ} 𝒦^{(𝐕𝐂,Z,W)}_{(sgn,ind,ℬ)}‖_{Y^θ_loc} ≲ (C⁺δ^{1/4})^{n₂} L^{η⁴} ‖Z‖_{Y^θ_loc}.
>
> In TARGET this is Prop `vineest` (L1742) for vine chains containing T-vines, i.e. (vineest2) with b = number of bad
> ingredients. Each T-vine counts as a "Nor" unit of Prop `sumint` (L1595), with m_i = number of its 2-atom pieces.

This is word for word DH23's statement with the vine family enlarged. No cancellation is used, and none is available:
T-vines, like the drawn normal vines, have no twists (Def `twist` concerns core bad vines only).

### 2.2 Lemma D (2-cut decoupling). PROVED.

**Statement.** Let (ℓ, ℓ′) be two bonds of B whose removal disconnects B into two sides X and Y. Then:
- relative to Y, one of ℓ, ℓ′ enters and the other leaves;
- k_ℓ − k_{ℓ′} = g with g ∈ {0, ±r};
- the free vectors split as z = (z_X, z_Y), with the vectors of Y-bonds equal to k_ℓ + δ_e, where δ = δ(z_Y, r) is
  independent of z_X;
- for every w ∈ Y, the quadratic part of Γ_w depends on z_Y only, and for w ∈ X on z_X only.

**Proof.**
- **One in, one out.** Every atom of B has in-degree equal to out-degree (interior 2/2, joints 1/1). Summing over Y,
  the numbers of cut bonds entering and leaving Y are equal, hence 1 and 1.
- **The value of g.** Summing the conservation laws Σ_out k − Σ_in k = c_w over w ∈ Y gives ±(k_ℓ − k_{ℓ′}) = Σ_{w∈Y} c_w.
  Here c_w = 0 at interior atoms and c_{v₂} = r = −c_{v₁}, so g ∈ {0, ±r}.
- **The δ-system.** Put δ_e := k_e − k_ℓ for the bonds of Y (incident to Y). Each conservation law at an atom of Y is
  invariant under adding one vector to all bonds at that atom, since the atom is balanced. So the Y-system in terms of
  δ is the same linear system, with boundary data δ_ℓ = 0 and δ_{ℓ′} = −g.
  - Its solutions are affine in (z_Y, r) and independent of the X-system.
  - The full solution set is the product of the two.
- **The quadratic forms.** At a balanced degree-4 atom, with outgoing o₁, o₂ and incoming i₁, i₂,

  Γ_w = |o₁|² + |o₂|² − |i₁|² − |i₂|² = 2(o₁ − i₁)·(o₁ − i₂).

  This uses o₁ + o₂ = i₁ + i₂, and it depends only on differences of bonds at w, hence only on δ. At a joint,
  Γ = (k_out − k_in)·(k_out + k_in) = ±r·(…), which is r-linear.

∎

Iterating Lemma D over all 2-bond cuts decomposes B into **pieces**: classes of atoms not separated by any 2-bond cut.
- The quadratic part of Σ_w s_w Γ_w is block diagonal over pieces.
- Each piece's block depends only on the piece itself (its internal oriented bonds) and on the gap labels g of its
  boundary cuts.
- Every r-dependent term is linear in z (coefficient λ|r| ≤ δL^{γ+η} ≪ L) or is a constant.

### 2.3 Lemma C (chirp bound) and the per-piece time integrals. PROVED.

**Lemma C.** For a real symmetric N×N matrix H, acting on (ℝ^d)^N as H⊗I_d, for a ∈ (ℝ^d)^N and ξ ∈ (ℝ^d)^N:

  |∫ e^{−|z−a|²} e^{iλ zᵀHz + iξ·z} dz| ≤ π^{Nd/2} ∏_i (1 + λ²μ_i²)^{−d/4},

where μ_i are the eigenvalues of H.

*Proof.*
- Shift z = a + w. This leaves a unimodular factor e^{iλaᵀHa + iξ·a} and the complex Gaussian integral
  ∫ e^{−wᵀAw + ic·w} dw, where A = I − iλH and c = ξ + 2λHa is real.
- The integral equals π^{Nd/2} det(A)^{−d/2} e^{−cᵀA^{−1}c/4}.
- The modulus of det(A)^{−d/2} is ∏(1 + λ²μ²)^{−d/4}.
- Re(cᵀA^{−1}c) = cᵀ(I + λ²H²)^{−1}c ≥ 0, so the exponential factor has modulus ≤ 1.
- Smooth unit-ball cutoffs are reduced to this case by writing χ = e^{−|z−a|²}·(e^{|z−a|²}χ) and expanding the second
  factor in a Fourier integral, which costs an L¹ norm ≤ Cᴺ. This is the same reduction as DH23 L1309ff. and TARGET
  L1621ff.

∎

**Applying Lemma C (γ ≤ 1/2).**
- **Lattice to continuum.** Every phase gradient is ≲ λ·O(1) ≤ CδL. As in DH23 `sumintest2` (L1360: "|θ_j| ≲ L due to
  γ ≤ 1/2") and TARGET Lemma `lemcubic0` (L1544), only O(1) Poisson modes per unit survive. Each is a shifted
  continuum integral, which Lemma C bounds uniformly in the shift.
- **Factorization.** By Lemma D the integrand bound factorizes over pieces. Integrating the times over a box (enlarging
  the time domain is allowed once absolute values are taken, as DH23 does at L1317) gives a factor λ^{−e_U} for each
  piece U. Here e_U = D_U := dim span{H_w : w ∈ U}, provided

  (★) the r_min-th largest |eigenvalue| of H_U(θ) = Σ θ_w H_w is positive on the unit sphere of the span, and
      r_min·d/2 > D_U.

  Under (★), ∫_{ℝ^{D_U}} ∏(1+μ_i(θ)²)^{−d/4} dθ < ∞: by compactness the top r_min eigenvalues are ≥ c|θ|.
- **Neutrality** of B means Σ_U e_U ≥ N/2.

**Unit types.**

| piece | atoms | D_U | rank on the sphere | factor | needed for neutrality |
|---|---|---|---|---|---|
| joint v₂ | 1 | 0 | — | 1 | λ^{−1/2}: **loses** λ^{1/2} |
| rung: 2 atoms, Γ_w + Γ_{w′} r-linear, Γ_w rank-2 form 2x·y | 2 | 1 | 2 | λ^{−1} | λ^{−1}: neutral |
| core: 3 atoms, ΣΓ r-linear, pencil {u₁·u₂, Λ} | 3 | 2 | ≥ 2 | λ^{−2} | λ^{−3/2}: **gains** λ^{−1/2} |

- **Rung:** a rank-2 form gives ∫(1+λ²θ²)^{−d/2}dθ ≈ λ^{−1}.
- **Core, Λ = u₁·u₃:** the pencil has rank 2 everywhere.
- **Core, Λ = u₃·(u₁+u₂−u₃):** det = 2θ₁θ₂(θ₁+θ₂), and the rank is still 2 on the three degenerate lines.

These are exactly DH23 Lemma `sumintest1` Step 2 (M_j ≲ δ^{−1}L^{2(d−γ)}) and Lemma `sumintest2` (M_* ≲ δ^{−2}L^{3d−4γ}).
The joint is DH23's trivial x₀-sum, L^d, and TARGET Lemma `lemlin`, first bound.

### 2.4 Theorem N (neutrality of T-vines). PROVED, finite part CHECKED.

> **Theorem N.** Let B be a T-type block, with either joint as v₂. Then:
> (a) the pieces of B are the two joints, exactly one 3-atom core, and 2-atom pieces;
> (b) the core's induced bonds are DH23's (B) (triangle with one double bond), (C) (path w₁=w₂=w₃) or (D) (triangle
>     with two double bonds);
> (c) every 2-atom piece is a rung unit and the core is a core unit (table above);
> (d) hence Σ_U e_U = N/2 exactly. B is exactly neutral, and so is every chain of T-vines: shared joints are zero-form
>     pieces, and the units add up.
> Consequently, Prop 7.6′ holds, by DH23 Cor `sumintest3` and TARGET Prop `sumint`. Both are applied with
> parametrization variables x₀ (joint), (x_j, y_j) (2-atom pieces) and (u₁,u₂,u₃) (core), taken as differences of
> bonds inside each piece.

**Example: the T-bead chain, explicitly. PROVED** (identities CHECKED by `tbead_check.py`).
- Take the T-bead of E1 (bonds b→e (x), b′→e (x′), e⇉g (p, p′), g⇉f (q, q′), f→b, f→b′), with v₂ = b′, v₁ = b.
- Set x₀ := x′, u₁ := p − x, u₂ := p − x′, u₃ := p − q. Then:
  - Γ_e = 2u₁·u₂;
  - Γ_g = −2u₃·(u₁+u₂−u₃);
  - Γ_e + Γ_g + Γ_f = 2r·(u₁ − u₂) + 2|r|²;
  - Γ_{b′} = −2r·x₀ − |r|² + const.
- The vine phase is therefore

  Γ_e(t_e−t_f) + Γ_g(t_g−t_f) + (ΣΓ)t_f + Γ_{b′}t_{b′},

  which is DH23 Lemma `sumintest2`'s integrand with **m = 0**, Λ = u₃·(u₁+u₂−u₃) (up to sign) and ξ = u₁ − u₂ + r.
- **Single bead.** (FourierboundI2) gives (C⁺δ^{−1})² L^{4(d−γ)−d+η⁴}. With the x₀-sum (L^d) and the prefactor
  (δ/2L^{d−γ})⁴, this is ≲ (C⁺δ)² L^{η⁴}: exactly neutral, the bound of Prop 7.6.
- **Chain of Q beads.** Cor `sumintest3` with all m_q = 0 gives (C⁺δ^{−1})^{2Q} L^{4Q(d−γ)−d+η⁴}, i.e. a single L^{η⁴}
  for the whole chain.
- This is precisely the neutral per-bead factor δ²/16 that F73 computed asymptotically.

**Proof of (b). PROVED.**
- A T-type block is T with at most two (Z)-ladders, plus two joints. This holds because the closure has at most two
  triple bonds, each (Y) sequence is undone by one (Z), and every triple bond needs a joint on one of its copies.
- An "exit" of T is a copy of a T-bond replaced by a 2-cut path. That path is either a (Z)-attachment or a joint
  subdividing that copy.
- **Two (Z)-moves.** Both joints sit at the two triple ends, so the core has at most 2 exits. The second ladder may
  attach to the first ladder instead of to the core.
- **One (Z)-move.** One joint sits at the ladder end. Exits: the (Z)-attachment, plus possibly the other joint.
- **No (Z)-move.** The two joints themselves give 1 or 2 exits; 1 exit is the σ = 1 case.
- **The shapes.** Removing 1 exit from T leaves (D). Removing 2 exits from different double bonds leaves (B). Removing
  2 exits from the same double bond leaves (C).

**Proof of (a), (c), (d). CHECKED** by `units.py` and `pieces.py`:
- on all 4446 directed T-type classes with |M₀| ≤ 15, for both choices of v₂ (8892 cases);
- units = 2-cut pieces in all 8892 cases;
- unit profiles: only (rung, D=1, rank 2) and (core, D=2, rank_min 2);
- 2Σe − N = 0 in every case;
- exactly one zero-form atom (v₂);
- core shapes D: 6296, B: 1940, C: 656.

**Extension to all sizes: §2.5.**

**Chains. CHECKED** by `chains.py`: runs of m = 1..4 T-beads in all bead orientations (the necklace's
B₁∪…∪B_m) give 2Σe − N = 0, with m zero-form atoms and m cores.

**Controls. CHECKED** by `controls.py`.
- **Vines (II), m = 1..5, and all Q-type blocks** generated from Q by (Z): 2Σe − N = −1. That is a loss of
  λ^{1/2} = δ^{1/2}L^γ, which is exactly DH23's "bad vine loses L^γ" (L588) that the twist cancellation repairs.
- **Random non-exceptional blocks:** mostly gains, 2Σe − N > 0. In a few, the sufficient test (★) is inconclusive for
  a large unit. That is irrelevant here, since such blocks are not vine-like and are handled by stage-2 counting.

So the absolute-value analysis separates bad (−1), normal (0) and generic (> 0) exactly as DH23's picture predicts
(L579–L593).

### 2.5 From ≤ 15 atoms to all T-vines (locality). PROVED (sketch at the level of DH23's own arguments).

**Locality.**
- By Lemma D, the analytic data of a piece (its forms, D_U, rank) depend only on the piece and on the gap labels of its
  boundary cuts.
- A gap label is determined by which joints lie on each side of the cut.

**Reduction.**
- **Pure rung segments.** A ladder segment is pure if it carries no joint and no attachment of the other ladder. It can
  be deleted, reconnecting its two boundary cuts (if needed, swapping the two rails, which is again a ladder).
- **What is preserved.** The result is again a T-type block, with Z_n replaced by Z_{n−k}. Every other piece and every
  boundary label is unchanged.
- **The bound.** In a T-type block, the non-pure rungs are:
  - the triple-end rung of each ladder;
  - at most 2 rungs next to the second ladder's attachment;
  - at most 2 rungs next to a joint sitting in a ladder (only possible with ≤ 1 (Z)-move).

  So every non-rung piece, with its boundary labels, already occurs in a T-type block with at most 13 atoms:
  - with two (Z)-moves: T (3) + first ladder with ≤ 3 rungs (6) + second ladder's end rung (2) + joints (2) = 13;
  - with one (Z)-move: 3 + 6 + 2 = 11.
- **Conclusion.**
  - Rung pieces of a ladder of any length have the rung data. PROVED: Γ_w = 2(o₁−i₁)·(o₁−i₂) has rank 2 in the
    piece's two difference variables, and Γ_w + Γ_{w′} is a sum over four rail bonds paired with gaps in {0,±r}, hence
    r-linear.
  - All other pieces are covered by the CHECKED range ≤ 15.

### 2.6 What F73's obstruction becomes

F73 is correct that each T-bead is exactly neutral in the time integral, and that there is no gain per bead. That
rules out keeping the bead atoms in ρ. It does not obstruct splicing:
- Splicing needs neutrality only. The analytic statement, exactly neutral per bead and λ^{−D_U} per piece, is
  log-free, because each piece's time integral is done by stationary phase rather than by the L¹ bound (1stsumbound2).
- No cancellation across a chain exists or is needed. T-vines admit no twist (the molecular involution of DH23
  Def `twist` exists only for core bad vines). The "twist-type involution" question in the brief has a negative answer
  that does not matter.

---

## 3. Q2(b) — the combinatorial extensions when T-vines join the vine family

### 3.1 Definition 2.6 (T-vine)

A block B (DH23 Def `defblock`) is a **T-vine** if all of the following hold:
- it has no interior cut atom;
- it has no triple bond;
- its closure cl(B) (each joint together with its two block bonds replaced by a single bond; for adjacent joints,
  u→b→b′→v becomes u→v) admits a complete (Y)-reduction (DH23 L1929) ending at T, with zero sequences allowed.

**Vines of the enlarged family:**
- **bad:** (I), and (II) with m ≥ 1 rungs (VINE2, (E0));
- **normal:** the T-vines.

The drawn (III)–(VIII) are T-vines (CHECKED in the reference enumeration; also F75 §3.4).

**Equivalent explicit list.** By YLEM1 (R1), ylem1′, cl(B) is one of:
- T;
- T₁;
- Z_m(T_n, ℓ′);
- a closure of (III)–(VIII), with any number of rungs.

**Recommendation:** use the enlarged family only for γ ≤ 1/2. For γ > 1/2, F75's Theorem A closes case (4) with the
original family. The same family can be used for all γ if Prop 7.6 Step 2 (counting, γ > 1/2) is re-checked for
T-vines. The piece parametrization makes that check the same counting as for the drawn vines; this is not done here.

### 3.2 The list of extensions

| Statement | Change | Status |
|---|---|---|
| DH23 Lemma `disjointlem` (L726) hypotheses (i), (ii), asserted for vine-like objects at L792 | must hold for T-vines | CHECKED: all 1586 T-type classes, ≤ 13 atoms, 0 failures (`subobj.py`) |
| DH23 Lemma 8.1 / TARGET L1930 `vinechainlem` | same proof. "DV" becomes a union of two σ = 1 vines sharing both joints and the bond between them. σ = 1 T-vines exist: 62 classes ≤ 13 atoms. Such a union has its joints of degree 3, so it is the whole molecule, exactly as for DV. | PROVED, given the hypotheses above |
| DH23 Cor `blockchainprop` (L782), Prop `block_clcn`(2) splicing (L741), Def `twistrep` codes (L890), Remark `remkv` (L1399) | generic for any (CL) block | unchanged |
| **Prop 7.6′ / TARGET `vineest`** | Theorem N + Cor `sumintest3` / Prop `sumint`. One cosmetic generalization: allow the r-linear phase vectors ζ_j, ξ to be integer combinations of *all* input variables. DH23 already allows this for ζ₀^q in Cor `sumintest3` (L1374). The proof is unchanged, because linear phases factor variable by variable and the per-unit bounds are uniform in linear shifts of size ≤ δL^{γ+η} ≪ L. | PROVED (§2) |
| DH23 Prop `red1step` (L1653) | Δ_{j+1} − Δ_j = η⁴ for each normal unit, now including T-vines | unchanged |
| **`subsetvc`** (DH23 L2128, TARGET L2431) | New sub-object types. If U₁ ⊂ U₂ share no ingredient, U₁ is a double bond, two double bonds (or its adjoint), **a T-vine, or the adjoint of a T-vine**. U₂ stays connected after removing U₁, and also after removing any two disjoint such U's. Even the drawn (V), (VII), (VIII) contain T-type sub-objects (5–11 atoms) whose gap is independent of theirs. | CHECKED: T-type containers ≤ 13 atoms, 0 disconnections (`subobj.py`, `drawn_subobj.py`). All sub-object gaps are free (never ±r or 0). No Q-type sub-objects. |
| DH23 Prop 9.1 / TARGET `subpro` (a)–(f) | generic proofs, using Lemma 8.1, Cor `blockchainprop`, `subsetvc` | PROVED, given the above |
| **Step-1 deviation** (DH23 L1797–L1802; TARGET Prop `excessprop1`(2), (dev1), L2154–L2179) for removing an SG T-vine or T-type sub-object | Count piece by piece in the order of the 2-cut tree: joint pair L^d(RL)^d; each 2-atom piece ≲ δ^{−1}L^{2(d−γ)} (Lemma A.2(1), x·y window); core ≲ δ^{−2}L^{3d−4γ} (A.2(3), γ ≤ 1/2 branch; the core forms are DH23's). r-linear cross terms only shift windows. This gives D ≲ R^dL^{2γ}(log L)^C ≤ L^{−η³}R²L^{γ+3η}, as for the drawn vines. TARGET's Operation 1 with a new component: I ≲ L^{γ₀+2η³}. | PROVED (same computation as DH23) |
| DH23 Prop 9.5 / TARGET `finalmol` ("a component that is a vine must be LG") | same proof, via Prop 9.1(f) | PROVED |
| **DH23 Prop 9.6 case (4) / TARGET `lgmolect`, γ ≤ 1/2** | M₁ is Y-exceptional, so by ylem1′ (YLEM1 R1, F75 §3) M₀ is (II) or a T-vine (this uses CASE4 Lemma 2.3: M₀ is a block H of 𝕄(𝒬_sub) with joints replaced by β-atoms). By Prop 9.5′ it is LG, and CASE4 Lemma 2.4 then gives 𝔄₀ ≲ (log L)^C δ^{−1}L^{−η}. That lemma needs the sharp form of (operc) (L1862), read via Lemma A.3(1), and γ ≤ 1 − 2η. | PROVED, modulo the CASE4 / F75 inputs |
| DH23 Prop 9.6 cases (1)–(3), (5), (6) | Not affected, in our reading. Case (5)'s exceptions (Prop 10.4(1)) are Q-type only: T∖ℓ (two adjacent degree-3 atoms) gains L^{−γ₀} by Lemma A.3(4), γ ≤ 1/2 branch, against the required L^{−4γ₀/7}. | HEURISTIC (not re-verified) |
| `kqmainest1` class count, and "ρ changes by O(1) per vine" | T-vines with s atoms number ≤ Cˢ (directed: 8, 32, 120, 366, 1060, 2860 for s = 5..15). Each T-vine has ≤ 3 maximal ladders (two (Z) ladders, one possibly split by the other's attachment, as in (VII)) and O(1) further atoms. | CHECKED counts; PROVED structure (§2.4(b)) |
| TARGET Def `cohmol` (groups) | groups := pieces (2-atom pieces and the core). Some 2-atom pieces are joined by a single bond, like the (VII) pair. | CHECKED (`piece_types.py`) |
| **TARGET Prop `layervine`** (coherent-layering count C₀^{m+\|q−q′\|}) | Needs DH's structure: groups on the v₂–v₁ spine form a separating chain, and every other atom lies in at most one pendant of shape "(V) minus its joints" (ladder + (D)-core) attached by two single bonds. The proof at L1521–L1531 then applies verbatim. | CHECKED: 8892/8892 cases ≤ 15 atoms are "no pendant" (2596) or "one ladder + (D) pendant" (6296) (`pieces.py`) |
| TARGET LF twists, Prop `lftwistprop` | not affected: T-vines are normal | — |
| DH23 Sec 11 / TARGET Sec 12 (flower trees, parametrix) | They rerun the couple analysis, so the same enlarged family must be used there | not checked; expected generic |

---

## 4. Q2(c) — is the T-type family finite?

**No: it is infinite, but finitely generated.**
- Every T-vine is T with at most two (Z)-ladders of arbitrary lengths, plus two joints.
- **Counts by atom number s (CHECKED; my enumeration equals the reference set exactly):**

  | s | 5 | 7 | 9 | 11 | 13 | 15 |
  |---|---|---|---|---|---|---|
  | directed classes | 8 | 32 | 120 | 366 | 1060 | 2860 |
  | undirected shapes | 3 | 5 | 10 | 14 | 21 | 27 |
  | shapes that are not drawn vines | 3 | 5 | 7 | 9 | 12 | 14 |

  These are the two-parameter families of YLEM1's R1: Z_m(T_n, ℓ′), and the vine closures with misplaced joints.
- Modulo pure rung segments, every T-vine reduces to one with ≤ 13 atoms (§2.5). This finite skeleton list is what the
  formal definition can be built on.
- **F69b's named examples:**
  - the three 5-atom T-beads = cores (C), (B), (D) with the joints attached directly; these are "(IV), (III), (V) with
    empty end ladders";
  - the five 7-atom T₁-blocks;
  - the 9-atom block.

  All of them are covered by Theorem N.

---

## 5. Q3 — alternative routes for γ ≤ 1/2 that avoid T-blocks

1. **A different Step-3 order or designation side. Refuted.**
   - CASE4 Lemma 3.4 and the referee: every order and every side gives case-(4) T-bead components.
   - In any case `kqmainest2` fails on 𝕄(𝒬_sub) = N_m itself, before stage 2 (CASE4 Prop 4.4).
2. **Stage-2 bookkeeping. Refuted.** The only slack in a necklace is one α-cut, R^{d−2}L^{−3η} (E1, "Scope").
3. **Remove T-chains in stage-2 Step 1 without splicing. Refuted.**
   - Step 1 removes a whole SG VC in one operation, but a T-chain of m beads holds about 4m atoms counted in ρ.
   - The proof of `kqmainest2` needs |ρ_sub − ρ_fin| ≤ Cσ (DH23 L1826). So one operation must not remove
     unboundedly many ρ-atoms.
   - Only stage-1 splicing turns a chain into one hinge atom.
4. **Change ρ (count a T-chain as one unit, like a ladder) and keep it in 𝕄(𝒬_sub).**
   - This needs (a) a log-free time bound for T-chains in (1stsumbound2) (F73 §5.3(ii)), and (b) a new stage-2
     bookkeeping in which SG T-bead components no longer owe L^{−η²}.
   - (a) is exactly the piece analysis of §2, applied inside stage 2 instead of stage 1.
   - It is strictly more work than splicing for the same analytic content. Not recommended.
5. **Use the γ ≤ 1/2 number theory differently.**
   - For γ ≤ 1/2 the lattice sums are continuum integrals up to O(1) Poisson modes. That is what makes Lemma C and
     Theorem N easy, and it is why T-vines are neutral rather than gaining.
   - The β-constraints at tiny gaps are void, which is the root cause. No counting refinement can recover them: CASE4
     Lemma 4.1 gives a lower bound.
   - A continuum-diagrammatic proof that bypasses the molecule machinery (Lukkarinen–Spohn style) would be a new paper.
6. **Restrict to γ > 1/2** (D9, F75). Complete and refereed, but it drops γ = 1/2, which TARGET singles out at L325.

So **no route avoids T-blocks**, other than option 6.

---

## 6. Q4 — recommendation

**(i) Repair feasible with a clear plan.** The new statements to formalize, in dependency order:

1. **Def T-vine** (§3.1), and the enlarged vine family. Bad vines are (I) and (II) with m ≥ 1 (E0, VINE2); normal vines
   are the T-vines (γ ≤ 1/2 branch).
   - For Lean, the explicit form is better than (Y)-reduction: the ylem1′ list (YLEM1 R1) with arbitrary rung counts,
     plus joint placements.
   - Alternatively, use the local piece predicate of Theorem N(a)(b).
2. **Lemma D** (2-cut decoupling). PROVED §2.2. Finite linear algebra over the bond vectors.
3. **Lemma C** (Gaussian chirp bound) together with the O(1)-Poisson-mode continuum reduction for γ ≤ 1/2. PROVED §2.3.
   This is in DH23 L1352–L1373 (Lemma `sumintest2` proof) and TARGET Lemma `lemcubic0` (L1544).
4. **Theorem N** (piece structure and neutrality of T-vines). PROVED §2.4 (b), §2.5; finite part CHECKED.
5. **Cor `sumintest3`′ / Prop `sumint`′:** the cosmetic generalization that r-linear phases may involve all variables.
   Proof unchanged.
6. **Prop 7.6′ / TARGET `vineest`** for chains containing T-vines. This is 4 + 5, and it is the analytic input that F73
   asked for.
7. **`disjointlem` hypotheses for T-vines; Lemma 8.1′** with σ = 1 doubles. CHECKED / PROVED.
8. **`subsetvc`′** with the new sub-object types. CHECKED ≤ 13 atoms.
9. **Prop 9.1′, Step-1 deviation′, Prop 9.5′.** PROVED, as in DH23.
10. **Prop 9.6 case (4)′** for γ ≤ 1/2 (ylem1′ + 9.5′ + CASE4 Lemma 2.4 with the sharp (operc)). Together with (E0),
    `kqmainest2` (DH23) and (finalcount1) (TARGET) hold for γ ≤ 1/2 with the new 𝒬_sub.
11. **TARGET:** `cohmol`′ (groups = pieces), `layervine`′ (structure CHECKED), `subpro`′, Operation-1 deviation′,
    `finalmol`′, `lgmolect`′; then (finalsbest2) and `layergarden` for γ ≤ 1/2.

**Effort and risk.**
- The analysis is done: it is existing DH lemmas applied to a parametrization.
- The work is combinatorial. It parallels the campaign's VINES/MOLEPROP4/B2 template work, but for an infinite family
  described by a predicate rather than eight templates.
- The B2 `VineType.template` API (YLEM1: 78 of 382 scratch files use it) would need a predicate-based successor.
- The formal `main` could then be widened from (1/2, 1) back to (0, 1) by a further versioned successor.

**What to ask Deng and Hani.** Questions for contacting the authors about erratum E1:
1. Do you agree that DH23 Def 5.1 / Fig. Vines (and TARGET Def `defvine`) should list all blocks whose closure
   (Y)-reduces to Q or T, which is your L586 description? The list then includes the zero- and one-sequence cases:
   - the 5-atom T-beads (cores (C)/(B)/(D) with the joints attached directly);
   - the 7-atom T₁-blocks;
   - the Z_m(T_n, ℓ′) closures and the vine closures with misplaced joints;
   - and (II) with one double bond.

   In particular, is "an enumeration shows 𝕄₀ must be a vine" (L1885) meant for this family?
2. Do you confirm that Prop 7.6 Step 3 (Lemma `sumintest2` / Cor `sumintest3`) and TARGET Prop `sumint` apply to any
   block with the x₀ / rung / core parametrization? This includes m = 0, joints adjacent to the core, and 2-atom groups
   joined by a single bond. It also includes r-linear phases ζ_j, ξ that involve other units' variables.
3. Should `subsetvc` (DH23 L2128 / TARGET L2431) include T-type sub-objects? We find that, in the enlarged family, (V),
   (VII), (VIII) contain T-type blocks and hyper-blocks with an independent gap.
4. Is TARGET Prop `layervine`'s proof meant for the general "spine + one (V)-minus-joints pendant" structure, which is
   what every T-vine has?
5. Is there any other place where the list (I)–(VIII) is used as exhaustive? Two candidates: the flower-tree/parametrix
   sections, and Prop 10.4(1) (case (5)), where we believe only Q-type exceptions occur.
6. **Main theorems:** do you agree that the necklace couples are of size about L^{−γ(2d−1)} per couple, so that only
   the intermediate statements (Prop 9.6, `kqmainest2`, (finalcount1), and with the papers' ρ also `kqmainest1` /
   (finalsbest2)) need the repair?

---

## 7. Residual risks (refute-first summary)

What I tried to break, and what happened:
- **(a) A T-type block that loses in the absolute-value bound.** None in 8892 cases. The controls show the test does
  detect losses: vine (II) gives −1.
- **(b) A unit structure other than rung/core.** None, and units = 2-cut pieces always.
- **(c) A core shape other than DH's.** Impossible (§2.4(b) proof); none found.
- **(d) Failure of the `disjointlem` hypotheses.** None.
- **(e) A sub-object whose removal disconnects the container.** None, for single removals or disjoint pairs.
- **(f) A gap coincidence (sub-object gap ≡ ±r or 0).** None.
- **(g) Layering structure outside DH's layervine shape.** None.

**Still open (not mathematics, but not yet written):**
1. **The rung-locality argument (§2.5) is a sketch.** Full proofs for the infinite families of the finite facts in
   rows 7–8 of §6 are needed: sub-objects with long ladders, and disjoint pairs. They were CHECKED only up to 13 atoms,
   and extend HEURISTICally by the same locality.
2. **The integrality conditions (i)–(iii)** of DH23 Lemma `sumintest1` (L1280) / TARGET Prop `sumint` (L1595) for
   the piece parametrization.
   They are routine: piece coordinates are differences of bonds, and the change of variables is triangular with
   entries in {0, ±1}. They are not written out. For γ ≤ 1/2 they can be avoided by doing Poisson summation in the
   original bond variables (Lemma C is coordinate-free), at the cost of uniformity bookkeeping along long ladders.
3. **TARGET-specific:** ZG containers in `subsetvc` (TARGET allows gap 0 with tame joints), and gardens with R ≥ 2.
   Both are generic in DH's text, but not rechecked.
4. **F79** (the sign of the core normal form) applies to T-vine cores exactly as to the drawn vines. Whatever fix lands
   there (`SumintSigned`) applies here unchanged.
5. **γ = 1/2 exactly:** Lemma C and the O(1)-mode reduction need λ = δL ≪ L, i.e. δ small. This is allowed, and it is
   DH23's own convention at γ = 1/2.

---

## 8. Files (run as `python3 -I <script>` in this directory)

| script | checks | output |
|---|---|---|
| `mg.py` | directed multigraph utilities: canonical form, literal (Y2)/(Y) (DH23 L1929) | — |
| `zgen.py 15 --compare` | Independent generation of all T-type blocks (T plus ≤ 2 verified (Z) moves, plus joint placements; no triple bond, no cut atom). Equals the reference set exactly: 4446 classes, 80 shapes. | `out_zgen15.txt` |
| `units.py 15` (`units.py 7` quick) | Unit decomposition and neutrality of every T-type block, both joints as v₂ | `out_units15.txt`, `out_units7.txt` |
| `pieces.py 15` | units = 2-cut pieces; core shapes B/C/D; spine/pendant structure | `out_pieces15.txt` |
| `chains.py` | runs of T-beads (necklace chains) are exactly neutral | `out_chains.txt` |
| `controls.py` | vine (II) and Q-type: −1 (lossy); generic blocks: mostly gain | `out_controls.txt` |
| `subobj.py 13` (`subobj.py 11`) | `disjointlem` hypotheses; vine-like sub-objects, their gaps and connectivity after removal (single and disjoint pairs) | `out_subobj13.txt`, `out_subobj11.txt` |
| `drawn_subobj.py` | sub-objects of the drawn (III)–(VIII) in the enlarged family | `out_drawn_subobj.txt` |
| `piece_types.py 13` | types of 2-atom pieces (TARGET `cohmol` groups) | `out_piece_types13.txt` |
| `tbead_check.py` | exact identities of the explicit T-bead parametrization (§2.4 Example) | `out_tbead_check.txt` |

Checksums are in `SHA256SUMS`.
