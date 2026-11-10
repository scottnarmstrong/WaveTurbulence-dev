# Referee report on the counting note (DH23 Props 9.4–9.6 and 10.4(2) for 0 < γ ≤ 1/2)

## Reader's preface

This is the independent refute-first referee report on the counting note,
[`gamma-le-half-counting-notes.md`](gamma-le-half-counting-notes.md). Verdict: **ACCEPT WITH REPAIRS**, with no gap,
false step or counterexample; the repairs R1–R4 (§3) are textual and scope corrections. The referee re-ran all four of
the note's scripts and obtained byte-identical output, re-derived every exponent, and wrote two checks of their own
(exact-arithmetic margins and off-centre lattice counts, §0). The repairs were applied in the Lean formalization and are
not folded into the note. In [`../ERRATA-AND-DEVIATIONS.md`](../ERRATA-AND-DEVIATIONS.md), Finding 1 as restricted by
R2 is erratum E47 and Finding 2 with remark K2 is erratum E48; the ghost lemma G is proved in the ghost-step note
([`gamma-le-half-ghost-step-notes.md`](gamma-le-half-ghost-step-notes.md)).

*Provenance: independent refute-first referee report, November 2026. The referee did not write the note under
review.* The scripts named in the text are not included in this repository. Abbreviations are as in the note's
preface; "the note" is the counting note, and D9 is the project decision, taken when erratum E1 was found, to restrict
the formal target to 1/2 < γ < 1 while γ ≤ 1/2 was being repaired (see E1 in ERRATA). Lean names refer to the repository
at the time of writing (the commits the report cites); a later clean-up removed some unused helpers, which remain in the
git history at the commits cited.

---------------------------------------------------------------------------------------------------------------------

I did not write the work under review.

**Verdict: ACCEPT WITH REPAIRS.** I found no mathematical gap, no false step and no counterexample. Every claim marked
PROVED or CHECKED survives a refute-first reading, and every exponent was re-derived. The repairs (§3) are textual
and scope corrections: one overclaimed lemma scope, one over-broad erratum, one imprecise gap identification in a proof
that remains correct, and the wording of the ghost lemma G (an input proved elsewhere). None of them changes a
conclusion.

---------------------------------------------------------------------------------------------------------------------

## 0. Sources and re-runs

**Paper versions** (sha256 prefix of the TeX source, re-hashed by me; they match the note): TARGET `493eef6b7dec448b`;
DH23 `c7e47dfabf5a4cca`. All Lean checks below are against commit `29488c88`, as in the note.

**Author scripts re-run.** All four outputs are byte-identical to the author's: `arith_low`, `reparam_check`,
`ghost_low`, `count_low`.

**Referee's own checks** (new):

| script | output | what it does | result |
|---|---|---|---|
| `ref_margins.py` | `out_ref_margins.txt` | Every exponent inequality of §3–§5 and §8, re-derived from the counts by me (not from `arith_low.py`), in **exact rational arithmetic**. Grid: d ∈ {3,4,5,8,20}; γ ∈ [1/1000, 1/2]; η at the (H_η) extreme dη = γ/1000 and 100× smaller; labels q on a grid of [−1, −γ+η]. | 0 failures. The 4 expected-negative controls are negative: ghost group D, a two-α triangle, case (2) with the printed (operc), case (6) without (e). The 9 closed forms of the note agree with my minima **exactly** (difference 0). |
| `ref_counts.py` | `out_ref_counts.txt` | Lattice counts for Lemma 2.1(ii) and Lemma 2.2, which no author script tests. d = 3, L ≤ 12, **off-centre** unit balls, v ≠ 0, W ≪ \|r\|, all three ξ and all three ζ. | count / bound stays in [7.6, 23.3] with no growth in L (sanity only). |

A first float run of `ref_margins.py` flagged three margins of size η² ≈ 10⁻¹⁸ as ≤ 0. That was rounding; the exact
rerun shows them positive.

---------------------------------------------------------------------------------------------------------------------

## 1. Verdicts, claim by claim

C = CONFIRMED; CR = CONFIRMED WITH REPAIR (repair in §3); G = GAP; F = FALSE. No claim is G or F.

| item of the note | claim | verdict |
|---|---|---|
| §1 Lemma 1.1 | interpolation with (roughbd) | C |
| §2 Lemma 2.0 (a)(b)(c) | slab, shell and harmonic lattice counts | C |
| §2 Lemma 2.1 (i)(ii) | A.2(1) at γ ≤ 1/2, uncapped: L^{2d}W·min(1, W/P̄) | C (proof checked line by line; numerics) |
| §2 Lemma 2.2 | A.2(3) at γ ≤ 1/2: C L^{3d}W², all three ζ | C (as above) |
| §2 Lemma 2.3 (1), (2), (4) | A.3 at γ ≤ 1/2 | C; (R1)/(R2) reparametrizations re-checked |
| §2 Lemma 2.3 (3); §0 row 1 "A.3(1)–(4)" | A.3(3) | **CR (R1)**: proved only in the weak and fixed-difference forms |
| §3.2 | α-cut, β-cut margins | C (with remark K1 on κ = 50) |
| §3.3 | triangles without ghosts; E7 moot | C |
| §3.4 | groups A–C margins; group D closed form −4η − gη² − η³ | C (in GHOST's model; remark K3) |
| §3.5 | Step 1 / Op 1: bad vine 2η − η³, T-vine γ + 2η − η³, two double bonds 3η − η³, Op 1 new component | C |
| §3.6 | erasures, E28, E19, (together3) slack 0.225 | C |
| §3.7 | ι/κ, N1, N2 as γ-free inputs | C (citations; matches Lean `FinalDec.iota`/`betaGap`) |
| §4.1 Lemma 4.1 | operation (c), sharp form; non-disconnection | C |
| Finding 1 | printed (operc) insufficient at γ < 1/2 | **CR (R2)**: true for case (2); not an erratum for case (4) |
| §4.2 | operation (d) | C |
| §4.3 Lemma 4.3 | (d)+(e) at γ ≤ 1/2: 𝔇 ≲ min(1, δ⁻¹L^{−2γ}/P) | C; the exclusion argument needs **R3** |
| Finding 2 | (opere) needs the uncapped A.2(1); TARGET `countlem` is capped only | C (exposition point; remark K2) |
| §4.4 | cycle components | C |
| §4.5–§4.7 | cases (1), (2), (3) | C |
| §4.8 Lemma 4.8 | case (4)′ in 𝒱_γ terms, including (A2) with σ = 1 | C |
| §4.9 | case (5) | C |
| §4.10 | case (6), (6a)–(6d), with (e) and N2; (e) necessary | C |
| §4.11–§4.12 | damaged and imperfect components; η-table | C |
| §5.1–§5.3 | pair gain, small-gap pair, merge at γ ≤ 1/2 | C |
| §5.4 | Prop 10.4(2)′ at γ ≤ 1/2, small cell X | C (Lean structure claim verified) |
| §6 | repair table | C (spot-checked) |
| Finding 3 | group-D deficit at γ ≤ 1/2 is 4η + gη² + η³, not (1 − 2γ) + 4η | C |
| §7 | the ghost lemma G (input proved elsewhere, in the ghost-step note); "G ⟺ (G-D)" | **CR (R4)**: wording |
| §8 | (finalcount1), `kqmainest2` conditional on G | C (conditional on G and the cited items) |
| §9 | Lean-facing claims | C (spot-checked at 29488c88; §2.9) |

---------------------------------------------------------------------------------------------------------------------

## 2. What I checked, and how (the refutation attempts)

### 2.1 Appendix A in the volume regime (the note, §2)

**(V).** W = δ⁻¹L^{−2γ} ≥ L⁻¹ ⟺ δ ≤ L^{1−2γ}. This holds for γ ≤ 1/2 and δ ≤ 1. Lemma 2.0(b) with w = 4W also
needs 4W ≤ 1, i.e. L ≥ (4/δ)^{1/(2γ)}. This is implicit in L ≥ L₀(δ, γ); see remark K4.

**Lemma 2.0.**
- (a) Each of the d − 1 free coordinates of a point of B(z₀, 1) takes ≤ 2L+1 values. The constrained coordinate lies in
  an interval of length 2w/|a_i|, with |a_i| ≥ |a|/√d.
- (b) ρ₊² − ρ₋² ≤ 2w gives Δ ≤ 2w/ρ₊. The cubes of the points lie in the thickened shell ∩ B(z₀, 2). The shell area
  inside B(z₀, 2) is ≤ C·min(r, 4)^{d−1}. This gives C L^d(w + L⁻¹), and the case ρ₊ < L⁻¹ gives O(1) points.
- (c) Lattice shells give Σ_k k^{d−1}(L/k) ≤ C L^d and Σ_k k^{d−1}(L/k)² ≤ C L^d for d ≥ 3. Points with |x − v| ≥ 3
  contribute ≤ C L^d. The mixed sum follows by Cauchy–Schwarz. All bounds are uniform in z₀ and v.

**Lemma 2.1.**
- (i) The terms are L^{2d−1}, L^{2d}W and L^d, all ≤ L^{2d}W by (V).
- (ii) The dyadic bound #{x ∈ S : |x| ≤ 2^{−j}} ≤ C(L2^{−j})^{d−1}·LW/P̄ is correct: it uses LW ≥ 1 and P̄ ≤ 1. The term
  L^{2d−1}W/P̄ is absorbed into L^{2d}W²/P̄ because LW ≥ 1.
- The (s, t) = (x+y, x−y) argument is an injection, and s lies in a ball of radius 2. Constants only.
- The attack "uniform in ball position, both slab terms kept" fails: every step is uniform, and `ref_counts.py` (A) with
  off-centre balls and W/|r| = 2L^{−2γ} ≪ 1 shows bounded ratios.

**Lemma 2.2.**
- ζ = x − v: the x = 0 row uses |v|⁻¹ ≤ L. The x = v row contributes ≤ C L^{2d} ≤ C L^{3d}W², since L^dW² ≥ L^{d−2}.
- ζ = x + y − v: the dyadic slab sum around c = v − x is uniform in c.
- ζ = x + y − v − z: (x + y − v)·z − |z|² = |c|² − |z − c|² with c = (x + y − v)/2, so this is a shell count.
- All three are correct. `ref_counts.py` (B) is bounded in L for all three ζ.

**Lemma 2.3.**
- (1): the shell (same sign) and the slab (opposite sign) counts, plus the trivial bound L^d.
- (2): I re-derived the identity k₁ − k₂ + k₃ = k ⇒ |k₁|² − |k₂|² + |k₃|² − |k|² = −2(k₁ − k)·(k₃ − k) by hand. This
  is the corrected sign of L2110.
- (4): I read `reparam_check.py`. Each affine map writes x, y, z as ±k_j + const, so it is a bijection onto the solution
  set of the linear equations. Unit balls go to unit balls and v ∈ ±a ± b ∈ Λ. The script verifies, for all
  18 + 6 sign patterns:
  - both linear equations hold identically;
  - the energies are ±2x·y + c and ±2ζ·z + c, with ζ in the allowed list.
- For {(1,2,3),(1,2,4,5)}: adding the two tuples eliminates the double-bond pair. The derived triple keeps k_s's sign,
  and no derived tuple has three equal signs (the degree-4 atom has two signs of each kind). Correct.
- (3): see R1.

**Lean statements I checked** at commit 29488c88:
- `exists_low_pair_selector_bound` is the uncapped strip bound C τ²L^{2d}/P for τL ≥ 1, with no γ hypothesis;
- `coupledTriple_bound` holds for γ ∈ (0,1), with exponent 3(d − γ) − min(γ, 1 − γ).

### 2.2 Prop 9.4 (the note, §3)

I re-derived each count exponent from DH23 L1788–L1803 with γ₀ = γ and found the same closed forms as the note.
`ref_margins.py` minima equal them exactly at (d, γ, η) = (3, 0.3, γ/3000).
- α-cut, d = 3: margin η − η³ at q = −γ + η. Since −(d−2)q − max(0, q + 2γ) is decreasing in q, the top label is the
  worst. For d ≥ 4 the margin is ≥ γ − η³.
- Triangle steps:
  - ΔF = 0: γ − η − 2η² − η³;
  - ΔF = 1: γ/2 − η/2 + η² − η³;
  - ΔF = 2: 4η² − η³.
  At γ ≤ 1/2, DH23's δ⁻¹min(L^{d−2γ+1}, L^d) equals δ⁻¹L^d, the trivial count. So no nonzero-gap fact is used, and
  **E7 is indeed moot** in this range.
- Step 1 (bad vine; T-vine with the L^{−γ₀} core gain of Lemma 2.2; VC of two double bonds) and Op 1 with a new
  component: as in the note. For two double bonds the min term is indeed unnecessary.
- **Ghosts (§3.4).**
  - In GHOST's model (`ghost_low.py` copies `patterns.py` verbatim; re-run is identical), I re-derived group D by hand:
    margin = −η³ − γ₀ − 3η − 2η² − q₂ when q₁ ≥ −2γ.
  - At q₂ = −γ + η this is (γ − γ₀) − 4η − 2η² − η³.
  - So the figure (2γ − 1) − 4η of GHOST and of the planning list of open steps (not included) is the γ > 1/2
    specialization (γ − γ₀ = 2γ − 1). At γ ≤ 1/2, γ − γ₀ = 0.
  - **Finding 3 is correct.** The deficit is ≤ 4η + gη² + η³, and it occurs only when both α-ghost labels are within
    L^{3η + O(η²)} of the SG top.
  - The slab s(ρ) = min(0, max(−1, −2γ − ρ)) is exactly Lemma 2.0(a)'s exponent, and the −1 floor never binds at
    γ ≤ 1/2. So the model is an upper bound in this range (the author's attack point 5).

### 2.3 Prop 9.6, structure and cases (1)–(5) (the note, §4.0–§4.9)

**Case split.** It is complete for even non-cycle components: V_β ≥ 3; V_β = 2 (V_α = 0 or ≥ 1); V_β = 1
(V_α = 1, 2, ≥ 3); V_β = 1 with V_α = 0 is impossible, since the gap would be 0.

**Interpolation weights.** w = V_α + V_β for even components and ≤ V_α + V_β + 2 for the odd one. These match the
C₀η³(w+1) terms used in every case:
- case (6): 4C₀η³;
- cases (5) and (4)′: 3C₀η³;
- case (3): C₀η³(V_α+3) or C₀η³(V_α+2).

**Lemma 4.1 non-disconnection.** Chain atoms have degree 2. So a component of M₀∖K containing neither end would have
been disconnected in M₀. If the two ends were in different components, each component would have one odd-degree atom.
Both are impossible.

**Cases (1)–(5).** Every margin, re-derived:
- (1): τw − 4C₀η³w; and (3γ/5)(1 − η³) − 3C₀η³.
- (2): ≥ η²(1 − 4/30), with the sharp (c).
- (3): (γ − 3η)/2 − η² − …, and (γ − 13η)/2 − 3η² − ….
- (4)′: (η/128)(1 − η³) − η² − 3C₀η³ ≈ 0.0076η at the extreme. Positive but thin; it relies on η ≤ 1/6000.
- (5): γ/14 − 3η/2 − ….

**Constants.** C₀η³ ≤ η²/30 holds: (16d + 28)η ≤ 0.0127 < 1/30 under (H_η).

**Finding 1.**
- With V_α = 0 and V_β = 3, the right side of (finalcount) is L^{γ+η²}.
- The printed (operc) gives at best δ⁻¹R⁻¹L^{−γ} ≤ δ⁻¹L^{1−γ} when every gap is ~L⁻¹. This loses 1 − 2γ − η². My
  control `case2 printed` is negative, as expected.
- The sharp form L^{γ−1} + δ⁻¹min(R⁻¹L^{−γ}, L^{γ}) is exactly DH23 Lemma A.3(1) times L^{−(d−γ)} (the trivial branch
  is L^d·L^{−(d−γ)}).
- I also checked that the printed form **does** suffice in cases (3), (5) and (6) (margins (γ−3η)/2, γ/14 − 5η/2,
  ≥ 45η respectively).
- See R2 for case (4).

**Case (4)′, (A2) with σ = 1** (attack point 6). D11's `IsClosure`
([`../review/GAMMA-LE-HALF-VINES.md`](../review/GAMMA-LE-HALF-VINES.md), approved text) has an explicit σ = 1 clause:
"one bond between the S-neighbour of j₁ other than j₂ and that of j₂ other than j₁". This is exactly operation (d) on
the single chain u→b→b′→v.
- `IsBlock` (`WaveTurbulence/Foundations/WaveB/Molecules.lean` L131) holds: dir2 at the joints, classes + evenDeg
  with V_α = 0, conn.
- The ≤ 2-bonds clause is FinalShape.noTriple.
- Looplessness holds because chain ends are distinct.
- The identification is correct.
- CASE4 Lemma 2.4's only γ-hypothesis is γ ≤ 1 − 2η (CASE4 L158), which is automatic here.
- In branch (B), class 2 uses the sharp (c) on the second chain, which is the count DH23 L1883 itself uses.

### 2.4 Lemma 4.3, operation (d)+(e) (the note, §4.3; attack point 2)

- **Δχ = −2** in all three configurations: two externals plus s–t; one external; none (a whole component, ΔF = −1).
- **External values.**
  - In the two-external case, p and q have in = out = 2 in M′, because op (d) bonds keep direction, and chain atoms have
    in = out = 1 (dir2). So ∂S is crossed once in each direction, and k_{ℓ_p} − k_{ℓ_q} = ±Σ_S c_v is fixed.
  - The new bond's value then fixes both externals for each of ≤ 7 values of g.
  - In the one-external case, conservation over S fixes the external.
  - The post parameters at s and t are fixed: c changes by (g−1)·(fixed); the energy changes by 2(g−1)k_{ℓ_q}·D + const,
    with k_{ℓ_q}·D fixed up to |S|W by the energy sum over S.
- **Count.**
  - Given the externals, p's and q's linear equations differ by a constant, so only one is independent. That leaves two
    free vectors with p's and q's windows.
  - The difference of the energies is ε₁(2w·k₁ − |w|²) (`reparam_check.py` (R3), all 6 patterns, with k₁ ∈ {x, x+y}
    + const).
  - So Lemma 2.1(ii) gives L^{2d}W·min(1, W/|w|). With δL^{2γ}W = 1 this is 𝔇 ≲ min(1, W/P). Correct.
- **LG of the post molecule.** The choice of g works at s and t simultaneously. Each opposite bond at s (≤ 3) or t (≤ 3)
  excludes ≤ 1 value of g when |D| is not small, so 6 < 7. Otherwise LG is inherited, as in DH23 L1867. Prop 10.1 then
  applies to M₂, which keeps the degree-3 ends of the (c)-chain.
- The "both externals at one atom s" exclusion is correct, but its gap identification is imprecise: **R3**.

### 2.5 Case (6) (the note, §4.10; attack point 1)

**Sub-cases.**
- The split (6a) κ ≥ 50, (6c) R₂ ≤ L^{−γ−50η}, (6b) no triple bond, (6d) the rest, is exhaustive.
- Margins:

  | sub-case | margin |
  |---|---|
  | (6a) | 46η − 3η² |
  | (6b) | 3γ/5 − 4η − … |
  | (6c) | 47η − 3η² |
  | (6d) | γ − 104η − … |

  These were re-derived by hand and in exact arithmetic. My grid gives a larger (6c) value only because it is coarse;
  the note's figure is the true lower bound.
- The control "(6) without (e)" is −4η − 3η², confirming the `Case6_96.lean` docstring and that (e) is necessary at
  γ ≤ 1/2.

**(6d).**
- *A triple bond in M₁ needs a (d)-bond.* M_fin has no triple bond.
- *Exactly two p–q bonds in M′.* Three would make M₀ = {p, q, two chains}, with v₁'s chain among them. Then (c) leaves
  degree 3 at p and q: the zero-external case.
- *At most two chains besides v₁'s.* Only v₂ and β remain, so ℓ_a and ℓ_b cannot both be (d)-bonds.
- *The charge of C.* By conservation in M₀ (ε-atoms have c_v = 0; α/β atoms have c_v = ±gap):
  c_{v₁} + c_{v₂} + c_β = 0. So w ∈ {±r₂, ±r_β, ∓r₁}.
- *N2.* Read exactly as Lean `FinalDec.iota` (min of the labels, factor 1/2), it gives |r_β| ≥ L^{−50η}R₂/2 ≥
  L^{−γ−100η}/2.
- *The derivation of N2 from DH23's ι.* If |r₁ ± r₂| = |r_β| were < L^{−50η}R₂/2, the later of the two α-cuts would
  have ι = 1. Simultaneous creation (same Step-1 VC, same α-cut) gives r₂ = ±r₁, hence |r_β| = 2|r₁|. Triangle
  siblings are covered by `SibUnif` in the Lean formalization of the stage-2 run (cited, γ-free).
- *P is a parameter.* α/β gaps are ±c_v, so the condition P ≥ L^{−γ−100η}/2 is a property of the parameter class,
  not of individual decorations, as the counting requires.
- **No gap found.**

### 2.6 Prop 10.4(2)′ at γ ≤ 1/2 (the note, §5)

**5.1 pair gain.** The degree-3/degree-3 single-bond case and the degree-3/degree-4 double-bond case are the systems
{(1,2,3),(1,4,5)} and {(1,2,3),(1,2,4,5)}, with no tuple of three equal signs. Δχ = −3. Lemma 2.3(4) gives
δ^{−1/2}L^{−γ}.

The Lean docstring of `PairGainInput` says the (3,3) count "needs γ > 1/2, erratum E1". I read E1: it restricts the
*formal target* (decision D9); it does not assert that A.3(4) fails at γ ≤ 1/2. Lemma 2.2 proves the count, and my
numerics agree. So there is no conflict, but the docstring should be reworded when a low provider lands (remark K5).

**5.2 small-gap pair.** L^d·L^{d(1−γ+η)}·δ⁻¹L^{2(d−γ)}·L^{−4(d−γ)}δ² = δL^{−(d−2)γ+dη}. Then (d−2)γ ≥ γ₀ at γ ≤ 1/2.

**5.3 merge.**
- Opposite direction: L^{γ−1} + δ⁻¹L^{−η} by LG.
- Same direction: a shell count, δ⁻¹L^{−γ}.
- The merged atom has in = out = 2 in both direction patterns, and LG across the pairs is the negation of
  `SmallPairGap`.

**5.4.**
- Exponents re-checked: (I) −3: γ₀ + η/3; (I) −2: 6γ₀/5; (II): γ₀/5; (III): γ₀ − dη_s.
- Small cell X: for ℓ* a copy of a = b, the (3,3) single pair (a, b) is removed; for ℓ* single, the (3,4) double pair
  is removed. Either way c = d is left, with E = 2V − 2 > 0.
- **Lean structure claim verified:** in `G8R.CoreTheorem.core_split` (commit 29488c88), `hγ12` occurs only in `(i5 hγ12)`,
  `(i6 hγ12)` and `(i7 hγ12 …)` (lines 46, 48, 50). The providers `betaCutInput`, `bridgeSplitInput`,
  `bibridgeEqualInput` (no γ hypothesis), `biBridgeInput`, `prop102InputSz`, `prop102SecondInputSz`, `prop104_one`,
  `prop101At_of_G6`, `prop103At_of_G6` and `rough96` all take γ ∈ (0, 1).
- `xMinus_afree` uses its γ > 1/2 hypothesis only through `pairGainAt`.

### 2.7 Cycles, damaged/imperfect, assembly (the note, §4.4, §4.11, §8)

- **Cycles.** All margins re-derived. The worst is (γ − 13η)/2 − 3η² − 4η⁵ (s = 4, V_β = 1).
- **Damaged.** `prop96_damaged` takes γ ∈ (0, 1) with `hsm : dη ≤ γ₀/1000` and `hηs`. Verified.
- **(together3).**
  - d − γ − 1/4 − 1/40 − 4γ₀ − 4η − 5η² ≥ 0.225 − O(η), with equality only at (d, γ) = (3, 1/2).
  - d − 5γ ≥ 1/2 at γ ≤ 1/2.

### 2.8 The ghost lemma G (the note, §7)

G is an input proved elsewhere (in the ghost-step note). The statement is coherent. It isolates exactly what the note
does not prove:
- the group-D steps;
- FinalShape.cycle.

The note does supply every other per-step bound and every other component bound. See R4 for the wording.

### 2.9 Lean-facing claims (the note, §2 remarks and §9), spot-checked at commit 29488c88

- `chain_A_bound` has `hγ : γ ∈ Ioo (1/2) 1` and only the ρ⁻¹ term. Correct.
- `Case6_96.lean` says (e) and N2 are not needed for γ > 1/2. Correct.
- The `FinalDec` fields `noBetaCut` ("every nonzero-gap cut at deg ≥ 3 is an α-cut") and `iota` are exactly as used.
- The input signatures `PairGainInput`, `SmallGapPairInput` and `MergeInput` are each `1/2 < γ → …`.

---------------------------------------------------------------------------------------------------------------------

## 3. Required repairs (all textual; no conclusion changes)

**R1 (§0 row 1; §2 Lemma 2.3(3)): scope of "A.3(1)–(4) PROVED".**
- Lemma 2.3(3) proves A.3(3) only in two forms:
  - "any signs: ≤ Cδ⁻¹L^{2(d−γ)}";
  - the fixed-difference refinement ×min(1, W/|w|), which is DH23's second half.
- It does not prove DH23's first half:
  - the same-sign gain {(1,2,3⁺),(1,2,4⁺)} ≲ δ⁻²L^{2(d−γ)−γ₀};
  - the variants {(1,2,3),(3^±,4^±)};
  - A.3(5).
- None of these is used in the note's scope. Their uses (Prop 10.1 `laddersharp`, Prop 10.2, `ylem2`) are LEAN for all γ.
- **Repair:** restate row 1 as "A.3(1), (2), (4), and A.3(3) in the weak and fixed-difference forms".

**R2 (Finding 1): restrict to case (2).**
- At L1878, DH23 does derive 𝔄₀ ≲ δ⁻¹L^{γ₀} "using also (operc)". At γ < 1/2 that needs the sharp form, so the
  erratum is confirmed (exposition, CANDIDATE).
- In case (4), DH23 L1883 does **not** invoke (operc). It bounds the new bond directly by δ⁻¹L^{d−γ+γ₀}, the sharp
  count from Lemma A.3(1). So "does not imply … the non-exceptional branch of case (4)" is not an erratum of the source.
- **Repair:** drop the case-(4) clause, or say "case (4) at L1883 already uses the sharp count".

**R3 (§4.3, "Which configurations occur"): the gap of the excluding β-cut.**
- The note says the cut at s along (ℓ_p, ℓ_q) "has gap ±w ≠ 0". That holds only when S's α/β atoms in M₀ are those of C.
- If one of ℓ_a, ℓ_b is an earlier (d)-bond (chain C′), or ℓ_p, ℓ_q is a (d)-bond (chain C″ ending at s), then the cut
  in M₀ is taken along the corresponding chain bonds. Its gap is the total charge of all α/β atoms on the S-side.
- That set is a nonempty subset of {v₂, β}, because v₁'s chain was removed by (c). So the gap is ±r₂, ±r_β or ±r₁
  (by c_{v₁} + c_{v₂} + c_β = 0), nonzero in every case by `alphaGap`/`betaGap`. `noBetaCut` then excludes it.
- **Repair:** replace "gap ±w" by this sentence. The conclusion is unchanged.

**R4 (§0 verdict; §7): the status of G.**
- Change "G is equivalent to (G-D)" to "given the cited γ-free inputs, G reduces to (G-D)". The cited inputs are:
  - N1/`betaGap` (E11/R29);
  - N2/`iota` (`IotaUnif`/`SibUnif` in the Lean formalization of the stage-2 run);
  - `noBetaCut`;
  - `epsLG`;
  - `vineLG`_γ (Prop 9.5′, N2 §2.3);
  - the other FinalShape clauses (REFEREED).
- In §0, change "G as the only input proved elsewhere" to "G as the only **new** input proved elsewhere; the
  REFEREED/LEAN items of §10 are cited, not re-proved". (G1) as written bundles these non-ghost clauses, so the
  equivalence holds only modulo them.

---------------------------------------------------------------------------------------------------------------------

## 4. Remarks (non-blocking)

**K1 (κ = 50 counts, §3.2 and §3.5; DH23 L1803, all γ).**
- The gap ball of radius L^{−50η}Q contains at least one lattice point. So the count is max(1, (QL^{1−50η})^d), not
  (QL^{1−50η})^d, when Q < L^{−1+50η}.
- The stated "+(50d − 100)η" gain is then not literally available. But the margin at such small labels is
  ≥ d − 2 − 97η − η³, and the worst case over all labels is still 51η − η³ at the top label. I checked this with the
  floor in `ref_margins.py` ("alpha-cut k50").
- Worth one sentence in a write-up.

**K2 (DH23 (opere) hypothesis, L1871).**
- "max|r| ≳ L^{−γ−100η} for the gaps in this chain" is not the quantity the count uses. The count uses the chain's
  total charge |w|. Lemma 4.3 correctly uses |w|.
- In case (6) the two agree via the sum relation (C = {v₂, β} ⇒ |w| = |r₁|).
- This could be added to Finding 2 as an exposition point.

**K3 (§3.4 "attained").**
- The sharpness of group D is inherited from GHOST §3c's local example (collinear α-ghost gaps r_x = ±r_y). The note
  shows only the model margin at γ ≤ 1/2.
- The collinear example is γ-independent, and since group D is delegated to G, nothing in the note depends on attainment.

**K4 (thresholds).** L₀ must also satisfy L ≥ (4/δ)^{1/(2γ)}, so that 4W ≤ 1 in Lemma 2.0(b). This degenerates as
γ → 0, which is fine (γ is fixed).

**K5 (Lean wording).** The `PairGainInput` docstring ("needs γ > 1/2, erratum E1") should be reworded when a γ ≤ 1/2
provider lands. E1 restricts the target; A.3(4) holds at γ ≤ 1/2 (Lemma 2.2).

**K6 (consequence for the ghost step, not a finding).** With Finding 3, the γ ≤ 1/2 group-D deficit is only
4η + O(η²). This makes route 1 (creation-step slack) of the list of open steps drawn up when the extension was planned
(not included) look less hopeless than §1 of that list suggests. The note's §7 per-creation slack
table (α-cut η, bad vine 2η, T-vine γ + 2η, triangle ≥ γ/2) re-derives correctly.

---------------------------------------------------------------------------------------------------------------------

## 5. Files (not included in this repository)

| file | content |
|---|---|
| re-runs of the author's scripts | outputs byte-identical to the author's |
| `ref_margins.py`, `out_ref_margins.txt` | independent exact-arithmetic exponent check (§0, §2.2–§2.7) |
| `ref_counts.py`, `out_ref_counts.txt` | off-centre lattice counts for Lemmas 2.1(ii) and 2.2 |
| sources consulted | ERRATA and `Prop96Statement.lean` at commit `29488c88` |

---------------------------------------------------------------------------------------------------------------------

## Overall verdict: **ACCEPT WITH REPAIRS**

**Reasons.**
1. Every PROVED claim in the note's scope survives a refute-first check, with every exponent re-derived independently. This
   covers:
   - the volume-regime App. A lemmas;
   - Prop 9.4 except group D;
   - Prop 9.6, all cases, including (6d) with operation (e) and N2;
   - case (4)′ in 𝒱_γ terms;
   - Prop 10.4(2)′ with its three γ ≤ 1/2 inputs and the small cell.

   Every CHECKED claim reproduces byte for byte, and two new adversarial checks agree.
2. No gap or counterexample was found. The three new findings hold:
   - Finding 3 (the group-D deficit is 4η + O(η²), not (1 − 2γ) + 4η);
   - Finding 2 (the uncapped A.2(1) is needed);
   - Finding 1, for case (2).
3. The repairs R1–R4 are scope and wording corrections. One is an imprecise gap identification in an otherwise correct
   exclusion argument. None affects a conclusion.
4. The result is conditional, as the note itself states. (finalcount1) and `kqmainest2` at γ ≤ 1/2 hold **conditional
   on G** (the ghost step for γ ≤ 1/2; open when this report was written, and proved in the ghost-step note) and on the
   cited REFEREED/LEAN inputs. The note does not and cannot close the γ ≤ 1/2 half on its own.
