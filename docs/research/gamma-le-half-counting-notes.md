# DH23 Props 9.4–9.6 and 10.4(2) for 0 < γ ≤ 1/2: the counting note (research notes)

## Reader's preface

**What this note proves.** It re-proves DH23 Props 9.4, 9.6 and 10.4(2) for 0 < γ ≤ 1/2 over the enlarged vine
family 𝒱_γ (vines (I), (II) and T-vines; Prop 9.5 for this family is cited from N1–N3), with every exponent explicit,
including case (4)′ (§4.8) and case (6) with operation (e) (§4.10). In this range the energy window W = δ⁻¹L^{−2γ} is
at least the lattice spacing 1/L (the "volume regime"), so DH23's Appendix A counts are volume counts with elementary
proofs (§2). The one input proved elsewhere is the ghost lemma G (§7); the note also records three findings about the
printed text (§0).

**How it fits the repair.** This is ingredient 2 of the γ ≤ 1/2 repair: see
[§4 of the overview](../GAMMA-LE-HALF.md#4-ingredient-2-proposition-96-for-γ--12). It supports the repair of erratum
E1 in [`../ERRATA-AND-DEVIATIONS.md`](../ERRATA-AND-DEVIATIONS.md), and §6 re-checks at γ ≤ 1/2 the repairs of E7, E8,
E11, E12, E16, E17, E20, E21, E28 and the others listed there. Finding 1, as restricted to case (2) by the referee's
repair R2, is erratum E47; Finding 2, with the referee's remark K2, is erratum E48; Finding 3 corrects the planning
notes for the extension (not included), not the papers. The ghost lemma G is proved in the ghost-step note
([`gamma-le-half-ghost-step-notes.md`](gamma-le-half-ghost-step-notes.md), Theorems 6.1 and 7.1; see its §11a).

**Where it is in Lean** (names relative to the namespace `WaveTurbulence`).
- `GammaLow.FinalCount.prop96_low_closed` (`WaveTurbulence/Foundations/GammaLow/FinalCount/P96/Proved.lean`): DH23
  Prop 9.6 over the enlarged family for 0 < γ ≤ 1/2, all cases. The cases are in
  `WaveTurbulence/Foundations/GammaLow/FinalCount/P96/`: case (2) with the sharp count in `Case23.lean`, case (4)′ in
  `Case4.lean`, case (5) in `Case5.lean`.
- `GammaLow.FinalCount.Count.prop104_two_proved_low`, with its inputs `GammaLow.FinalCount.Count.pairGainInputLow`,
  `smallGapPairInputLow` and `mergeInputLow` (`WaveTurbulence/Foundations/GammaLow/FinalCount/Count/Prop104Low.lean`):
  Prop 10.4(2)′.
- Operation (e): `WaveTurbulence/Foundations/GammaLow/FinalCount/Count/OpE.lean`. The uncapped A.2(1) bound:
  `CountLemmas.exists_low_pair_selector_bound` (`WaveTurbulence/Foundations/CountLemmas/LowPairSelectors.lean`).
- The whole final count for γ ≤ 1/2: `GammaLow.FinalCount.finalCountGateLow_of_ghost`
  (`WaveTurbulence/Foundations/GammaLow/FinalCount/I/Final.lean`), whose one hypothesis is the formal ghost step; it is
  applied in `GammaLow.Close.finalCountGateLow_proved` (`WaveTurbulence/Foundations/GammaLow/Close/Halves.lean`), which
  supplies that hypothesis by `GammaLow.FinalCount.Ghost.chainCoverLowL'_holds`.

Lean names in the body are as of commit `29488c88`. The Lean-facing plan in §7 and §9 predates the formal proof; the
names it proposes (for example `GhostLowInput`) are not the final ones.

**Status.** Accepted with repairs by an independent refute-first referee
([report](gamma-le-half-counting-referee.md)). The referee's repairs are listed in the report; they were applied in the
Lean formalization and are not folded into this text.

*Provenance: written and independently refereed in November 2026.* The scripts named in the text are not included in
this repository. Lean names refer to the repository at the time of writing (this preface: commit `5c19b015`; the text:
the commit it cites, where it cites one); a later clean-up removed some unused helpers, which remain in the git history
at the commits cited.

**Abbreviations.**
- TARGET: Y. Deng, Z. Hani, *Long time justification of wave turbulence theory*, arXiv:2311.10082v2; line numbers are
  lines of its TeX source.
- DH23: Y. Deng, Z. Hani, *Derivation of the wave kinetic equation: full range of scaling laws*, arXiv:2301.07063;
  line numbers as above.
- N1, N2, N3: the three earlier research notes on T-vines,
  [`gamma-le-half-repair-1-notes.md`](gamma-le-half-repair-1-notes.md),
  [`gamma-le-half-repair-2-notes.md`](gamma-le-half-repair-2-notes.md),
  [`gamma-le-half-repair-3-notes.txt`](gamma-le-half-repair-3-notes.txt); REF1–REF3: their referee reports
  `gamma-le-half-repair-{1,2,3}-referee.md`. (N1 and N2 are also the names of two properties of final decorations:
  N1 = nonzero β-gaps, Lean `FinalDec.betaGap`; N2 = the ι/κ property, Lean `FinalDec.iota` (§3.7). A note is always
  cited with a section or item number, e.g. "N2 §2.1".)
- GHOST: [`ghost-triangle-notes.txt`](ghost-triangle-notes.txt) (the first analysis of the ghost step).
- CASE4: [`dh23-prop96-case4.md`](dh23-prop96-case4.md) (the necklace counterexample, erratum E1).
- APPB: [`dh23-appendix-b-errata.md`](dh23-appendix-b-errata.md) (errata to DH23's appendices).
- YLEM1: [`ylem1-investigation.md`](ylem1-investigation.md); its repair R2 is the reading "not Y-exceptional" of
  Prop 10.4(2)′.
- The ghost-step note: [`gamma-le-half-ghost-step-notes.md`](gamma-le-half-ghost-step-notes.md).
- R26, R29, R37, R38, R48: rulings of the formalization project that fix readings of the sources; each is described in
  ERRATA ([`../ERRATA-AND-DEVIATIONS.md`](../ERRATA-AND-DEVIATIONS.md)). R26: which parametrization of a closed ladder
  cell defines its gap. R29: which triangles are eligible in Operation 2, and the erasure of tame clusters (errata E11,
  E16, E17). R37: triple bonds at hinges (erratum E22). R38: the charged per-step bound for triangles with ghosts
  (erratum E20). R48: the bookkeeping of degree-2 cuts (erratum E28).
- D11: the decision fixing the T-vine definition (`WaveTurbulence/Foundations/TVine/Defs.lean`).

---------------------------------------------------------------------------------------------------------------------

**Status words**: PROVED = complete written proof here; CHECKED = by computation, script named;
REFEREED = proved and independently refereed earlier (cited, not redone); LEAN = proved in Lean for all
γ ∈ (0,1) (cited as an input); SKETCH; OPEN. **G** = the ghost lemma (the ghost step, two α-ghosts at a triangle,
erratum E20, for γ ≤ 1/2), stated exactly in §7; it is an input proved elsewhere, in the ghost-step note.

**Paper versions** (sha256 prefix of the TeX source): TARGET 493eef6b7dec448b; DH23 c7e47dfabf5a4cca. DH23 line
numbers below are file lines.

---------------------------------------------------------------------------------------------------------------------

## 0. Verdict

**Everything in this note's scope is PROVED for 0 < γ ≤ 1/2, with the ghost lemma G as the only input proved
elsewhere (in the ghost-step note).** Every exponent is explicit, γ₀ = γ, γ₁ = 2γ. No counterexample was found.
The η-condition is d·η ≤ γ/1000 and 4·1440061·η ≤ 1 (the Lean `hsm`, `hηs` with γ₀ = γ). The condition
`8η ≤ 2γ − 1` and `hsm2` disappear everywhere except inside G.

| # | Claim (γ ≤ 1/2) | Status | § |
|---|---|---|---|
| 1 | App. A in the "volume regime" W := δ⁻¹L^{−2γ} ≥ L⁻¹: Lemma A.2(1) (capped **and uncapped**), A.2(3), A.3(1)–(4), with elementary proofs | PROVED; reparametrizations CHECKED (`reparam_check.py`); counts sanity-CHECKED (`count_low.py`) | 2 |
| 2 | Prop 9.4 per-step bounds, repaired form (rulings R29, R37, R38, R48; errata E21, E28): cuts, triangles without ghosts, ghost groups A, B, C, Step 1 for 𝒱_γ, TARGET Op 1 with a new component, erasures | PROVED (closed forms); CHECKED (`ghost_low.py`, `arith_low.py`) | 3 |
| 3 | Ghost group D (two α-ghosts at a triangle) | **G** (proved in the ghost-step note). Its deficit at γ ≤ 1/2 is exactly 4η + gη² + η³, **not** (1 − 2γ) + 4η as §1 of the list of open steps drawn up when the extension was planned (not included) says | 3.4, 7 |
| 4 | Prop 9.6 (`lgmolect`), all components: cycles, cases (1)–(6), damaged, imperfect | PROVED given FinalShape/FinalDec_γ (§4.0) | 4 |
| 5 | Case (6) with operation (e) and the ι/κ property N2 (= Lean `FinalDec.iota`) | PROVED, including a written proof of (opere) at γ ≤ 1/2 (Lemma 4.3) | 4.3, 4.10 |
| 6 | Case (4)′ consolidated in 𝒱_γ terms | PROVED from REFEREED pieces | 4.8 |
| 7 | Prop 10.4(2)′ inputs at γ ≤ 1/2: pair gain (A.3(4)), small-gap pair, merge (A.3(1)) | PROVED | 5 |
| 8 | Prop 10.4(2)′ at γ ≤ 1/2 (including the X small cell) | PROVED (γ-free structure as in Lean `core_split`; the three inputs from #7) | 5.4 |
| 9 | Every repair made during the formalization in this region re-checked at γ ≤ 1/2 | done (table) | 6 |
| 10 | (finalcount1) / `kqmainest2` at γ ≤ 1/2 | PROVED **conditional on G** | 8 |

**New findings (exposition errata, CANDIDATE):**
- **(Finding 1) (operc), DH23 L1861–1862.** The printed bound 1 + δ⁻¹R⁻¹L^{−γ} does **not** imply case (2) (L1878) or the
  non-exceptional branch of case (4) (L1883–L1884) when γ < 1/2. Configuration: an even component with V_α = 0,
  V_β ≥ 3 and every β-gap ≈ L⁻¹. The printed bound gives δ⁻¹L^{1−γ}, while the case needs δ⁻¹L^{γ₀} = δ⁻¹L^{γ}. Lemma
  A.3(1) itself gives the sharp form L^{γ−1} + δ⁻¹min(R⁻¹L^{−γ}, L^{γ}), which suffices (§4.1). `arith_low.py`
  shows the printed form fails case (2) by 1 − 2γ in the exponent. CASE4 noted the sharp form for case (4) at γ > 1/2;
  the Lean `chain_A_bound` has only the R⁻¹ term.
- **(Finding 2) (opere), DH23 L1869–1871.** At γ ≤ 1/2 it needs the **uncapped** A.2(1) bound
  δ⁻¹L^{2(d−γ)}(1 + δL^{2γ}P)⁻¹. TARGET's restatement `countlem` (L2459–L2461) keeps only the capped form with
  𝔛 ≤ (log L)², which gives no power gain. DH23 A.2(1) does state the uncapped γ ≤ 1/2 branch (L2056), and Lean has it as
  `CountLemmas.exists_low_pair_selector_bound`.
- **(Finding 3) The planning list of open steps (not included), §1, on the ghost step.** At γ ≤ 1/2 the group-D
  margin is −4η − gη² − η³ (worst case), and it is negative only when **both** α-ghost labels are above
  L^{−γ−3η−O(η²)}. It is not "−(1 − 2γ) − 4η". The figure (2γ − 1) − 4η is the γ > 1/2 formula, where γ₀ = 1 − γ.
  See §3.4 and §7.

---------------------------------------------------------------------------------------------------------------------

## 1. Setting and standing conventions

- d ≥ 3, 0 < γ ≤ 1/2, γ₀ := min(γ, 1 − γ) = γ, γ₁ := min(2γ, 1, 2(d−1)(1−γ)) = 2γ. δ ∈ (0, 1] fixed, L ≥ L₀.
- **W := δ⁻¹L^{−2γ}** is the energy window. The one structural fact behind everything below is

  **(V) W ≥ L^{−2γ} ≥ L⁻¹** (and W ≤ 1 for L ≥ δ^{−1/(2γ)}).

  So every window is at least the lattice spacing, and all counts are volume counts. For γ > 1/2, W < L⁻¹, and the
  counts are number-theoretic (DH23 App. A, γ > 1/2 branches). None of those are used here.
- **Exponent bookkeeping** (DH23 Prop 9.4/9.6, TARGET (excesseqn2), (finalcount)):
  - h := (γ + 3η)/2, a := 2γ₀ + 5η² = 2γ + 5η², b := γ₀ + 2η² = γ + 2η², τ := (γ − 5η)/2;
  - an α-label R ∈ [L⁻¹, L^{−γ+η}] and its exponent q := log_L R ∈ [−1, −γ + η];
  - the α label factor T(R, κ) := L^{h−κη}R ≤ L^{−τ} (κ ∈ {0, 50}).
- **(finalcount)** for a component M₀ of M_fin is

  𝔄₀ ≲ ∏_{α} T(R_v, κ_v)⁻¹ · L^{bV_β − aG} · L^{−η⁵ρ₀}   (G = 0 odd, 1 even),

  and in exponent form RHS_exp := Σ_α(−h + κ_vη − q_v) + bV_β − aG.
- **"margin"** = RHS exponent − LHS exponent. A margin > 0 that depends only on (d, γ, η) absorbs every factor
  C(d, γ, η, δ)(log L)^{O(1)} (the `≲` of DH23, `≤` with constant 1 for L ≥ R₀ in Lean).
- **η-condition (H_η):** η > 0, d·η ≤ γ/1000, 4·1440061·η ≤ 1. Consequences used:
  - η ≤ γ/3000 ≤ 1/6000;
  - C₀η³ ≤ η²/30 with C₀ := 16d + 28 (the constant of (roughbd) in the Lean proof `rough96`), as in Lean
    `small_facts`.
- **(roughbd)** (DH23 L1858; Prop 10.2(3), LEAN all γ, `dh23_prop_10_2`): 𝔄₀ ≲ L^{−η²ρ₀ + C₀(w+1)}, where
  w = #atoms of M₀ not of degree 4 (w ≤ V_α + V_β + 2).

**Interpolation Lemma 1.1** (DH23 L1858–1880; CASE4 Lemma 1.1). If 𝔄₀ ≲ L^{X}, then

  𝔄₀ ≲ L^{(1−η³)X + η³C₀(w+1) − η⁵ρ₀}.

Hence (finalcount) holds as soon as (1−η³)X + η³C₀(w+1) < RHS_exp with a margin depending only on (d, γ, η). When X
contains a factor R⁻¹ (q < 0), (R⁻¹)^{1−η³} ≤ R⁻¹ is used.

*Proof.* min(A, B) ≤ A^{1−θ}B^{θ} with θ = η³. ∎ (PROVED)

---------------------------------------------------------------------------------------------------------------------

## 2. Appendix A at γ ≤ 1/2 (the counting half of Prop 10.4(2) and its inputs)

Λ := ℤ_L^d = L⁻¹ℤ^d. "Unit ball" means a closed ball B(z₀, 1) with arbitrary centre. C denotes constants depending on
d only.

**Lemma 2.0 (volume-regime lattice counts).** PROVED.
- (a) **Slab.** For a ∈ ℝ^d∖{0}, t ∈ ℝ, w > 0:

  #{y ∈ Λ ∩ B(z₀,1) : |a·y − t| ≤ w} ≤ (2L+3)^{d−1}(2√d·Lw/|a| + 1).

  The same holds with B(z₀,1) replaced by B(z₀,ρ) and (2L+3)^{d−1} by (2Lρ+3)^{d−1}.
- (b) **Shell.** For c ∈ ℝ^d, t ∈ ℝ, 0 < w ≤ 1:

  #{z ∈ Λ ∩ B(z₀,1) : ||z − c|² − t| ≤ w} ≤ C L^d (w + L⁻¹).
- (c) **Harmonic sums.** For d ≥ 3 and v ∈ Λ:

  Σ_{x∈Λ∩B(z₀,1), x≠v} |x − v|^{−1} ≤ C L^d, Σ_{x≠v} |x−v|^{−2} ≤ C L^d, Σ_{x∉{0,v}} |x|^{−1}|x − v|^{−1} ≤ C L^d.

*Proof.*
- (a) Choose i with |a_i| = |a|_∞ ≥ |a|/√d. The other d − 1 coordinates of y take at most (2L+3)^{d−1} values. For each
  choice, y_i ∈ L⁻¹ℤ lies in an interval of length 2w/|a_i|, which contains at most 2Lw/|a_i| + 1 points.
- (b) The set is {ρ₋ ≤ |z − c| ≤ ρ₊} ∩ B(z₀,1), with ρ_± := (max(t ± w, 0))^{1/2}.
  - The width satisfies Δ := ρ₊ − ρ₋ ≤ min(√(2w), 2w/ρ₊), since ρ₊² − ρ₋² ≤ 2w.
  - The cubes z + [0, L⁻¹)^d of the points are disjoint and lie in A′ = {ρ₋ − √d/L ≤ |z−c| ≤ ρ₊ + √d/L} ∩ B(z₀, 2).
  - A spherical shell {r₁ ≤ |z−c| ≤ r₂} meets B(z₀, 2) in volume ≤ C(r₂ − r₁)·min(r₂, 4)^{d−1}.
  - If ρ₊ ≥ L⁻¹: vol(A′) ≤ C(2w/ρ₊ + 2√d/L)(ρ₊ + 2√d/L)^{d−1}, capped at 4^{d−1}, which is ≤ C(w + L⁻¹).
  - If ρ₊ < L⁻¹: the set lies in a ball of radius 3√d/L and has ≤ C points.
  - So # ≤ L^d·vol(A′) ≤ C L^d(w + L⁻¹).
- (c) At most C k^{d−1} points of Λ satisfy k/L ≤ |x − v| < (k+1)/L (k ≥ 1). Points with |x − v| ≥ 3 number
  ≤ (2L+3)^d and contribute ≤ C L^d. Hence:
  - Σ|x−v|⁻¹ ≤ C L Σ_{k≤3L} k^{d−2} + C L^d ≤ C L^d;
  - Σ|x−v|⁻² ≤ C L² Σ_{k≤3L} k^{d−3} + C L^d ≤ C L^d (d ≥ 3);
  - the last sum follows by Cauchy–Schwarz. ∎

**Lemma 2.1 (A.2(1) at γ ≤ 1/2, uncapped).** PROVED. Let x ∈ Λ ∩ B₁ and y ∈ Λ ∩ B₂ (unit balls), α, β ∈ ℝ, r ∈ Λ,
ξ ∈ {x, y, x+y}. Then:
- (i) E := #{(x,y): |x·y − α| ≤ W} ≤ C L^{2d}W = C δ⁻¹L^{2(d−γ)};
- (ii) if r ≠ 0: #{(x,y): |x·y − α| ≤ W, |r·ξ − β| ≤ W} ≤ C L^{2d}W·min(1, W/P̄), where P̄ := min(|r|, 1).

In DH23's form (ii) reads ≤ C δ⁻¹L^{2(d−γ)}(1 + δL^{2γ}P̄)⁻¹. That is ≤ C δ⁻¹L^{2(d−γ)}𝔛⁻¹ for every
𝔛 ≤ 1 + δL^{2γ}P with |r| ∼ P, i.e. it implies (countc1-1) and TARGET (basiccount01).

*Proof.*
- (i) Fix x.
  - If x ≠ 0, Lemma 2.0(a) with a = x gives #{y} ≤ C L^{d−1}(1 + LW/|x|).
  - If x = 0, #{y} ≤ C L^d.
  - Sum over x with Lemma 2.0(c) (v = 0): E ≤ C L^{2d−1} + C L^dW·Σ_{x≠0}|x|⁻¹ + C L^d ≤ C(L^{2d−1} + L^{2d}W) ≤ C L^{2d}W,
    by (V).
- (ii), ξ = x.
  - The slab S := {x : |r·x − β| ≤ W} has #S ≤ C L^{d−1}(1 + LW/|r|) ≤ C L^dW/P̄, by (a) and (V) (LW ≥ 1).
  - For x ∈ S, #{y} ≤ C L^{d−1}(1 + LW/|x|).
  - Dyadic decomposition of S by |x| ~ 2^{−j} ≥ L⁻¹: by (a) in balls of radius 2^{−j},
    #{x ∈ S : |x| ≤ 2^{−j}} ≤ C(L2^{−j} + 1)^{d−1}(LW/|r| + 1) ≤ C(L2^{−j} + 1)^{d−1}LW/P̄. Hence
    Σ_{x∈S∖0}|x|⁻¹ ≤ C(LW/P̄)L^{d−1}Σ_j 2^{−j(d−2)} ≤ C L^dW/P̄. (Points with |x| ≥ 1 contribute ≤ #S.)
  - Total: ≤ C L^{d−1}#S + C L^dW·L^dW/P̄ + C L^d ≤ C L^{2d}W²/P̄, using L^{2d−1}W ≤ L^{2d}W² and
    L^d ≤ L^{2d}W² ≤ L^{2d}W²/P̄.
- (ii), ξ = y: symmetric.
- (ii), ξ = x + y. Put s = x + y and t = x − y. The map (x,y) ↦ (s,t) is injective, and x·y = (|s|² − |t|²)/4.
  - s lies in a slab: #{s} ≤ C L^dW/P̄.
  - For each s, t lies in the shell ||t|² − (|s|² − 4α)| ≤ 4W: by (b), #{t} ≤ C L^d(W + L⁻¹) ≤ C L^dW.
- Finally min(1, W/P̄) ≤ 2(1 + P̄/W)⁻¹ = 2(1 + δL^{2γ}P̄)⁻¹. In every use below |r| ≤ 2, so P̄ ≍ |r|. ∎

**Lemma 2.2 (A.2(3) at γ ≤ 1/2).** PROVED. Let x, y, z range over Λ ∩ (unit balls), v ∈ Λ, and
ζ ∈ {x − v, x + y − v, x + y − v − z}. Then

  #{(x,y,z): |x·y − α| ≤ W, |ζ·z − β| ≤ W} ≤ C L^{3d}W² = C δ⁻²L^{3d−4γ} = C δ⁻²L^{3(d−γ)−γ₀}.

*Proof.* Let E = {(x,y): |x·y − α| ≤ W}; #E ≤ C L^{2d}W by Lemma 2.1(i).
- **ζ = x − v.**
  - For (x,y) ∈ E with x ≠ v: #{z} ≤ C L^{d−1}(1 + LW/|x − v|). For x = v: #{z} ≤ C L^d.
  - Σ_{(x,y)∈E, x≠v}|x − v|⁻¹ ≤ Σ_{x≠v}|x−v|⁻¹·C L^{d−1}(1 + LW|x|⁻¹1_{x≠0}) + C L^{d+1}·1_{v≠0}. Here the last term
    is x = 0, where |v|⁻¹ ≤ L. By Lemma 2.0(c) this is ≤ C(L^{2d−1} + L^{2d}W + L^{d+1}) ≤ C L^{2d}W.
  - Total: ≤ C L^{d−1}·L^{2d}W + C L^dW·L^{2d}W + C L^d·L^d ≤ C L^{3d}W², using (V) and L^dW² ≥ L^{d−2} ≥ 1.
- **ζ = x + y − v.**
  - For x ≠ 0 the set S_x := {y : |x·y − α| ≤ W} is a slab with normal x. By Lemma 2.0(a) in balls of radius ρ around
    c := v − x ∈ Λ, and the dyadic sum of Lemma 2.1(ii):
    Σ_{y∈S_x, y≠c}|y − c|⁻¹ ≤ C L^{d−1}(1 + LW/|x|).
  - Summing over x ≠ 0 (Lemma 2.0(c)) gives ≤ C L^{2d}W. The term x = 0 contributes ≤ C L^d.
  - The pairs with x + y = v number ≤ C L^d.
  - So the count is ≤ C L^{d−1}#E + C L^dW·C L^{2d}W + C L^d·L^d ≤ C L^{3d}W².
- **ζ = x + y − v − z.** |ζ·z − β| ≤ W is equivalent to ||z − c|² − (|c|² − β)| ≤ W with c = (x + y − v)/2. By
  Lemma 2.0(b), #{z} ≤ C L^dW, so the count is ≤ #E·C L^dW ≤ C L^{3d}W². ∎

**Lemma 2.3 (A.3 at γ ≤ 1/2).** PROVED. These are the systems (counteqn), with windows of width W.
- (1) {(1⁺,2⁺)}: ≤ C L^dW = C δ⁻¹L^{d−2γ} = C δ⁻¹L^{d−γ−γ₀}.
  {(1⁺,2⁻)} with k₁ − k₂ = k, |k| ∼ R: ≤ C(L^{d−1} + δ⁻¹min(R⁻¹L^{d−2γ}, L^d)).
- (2) {(1,2,3)}: ≤ C δ⁻¹L^{2(d−γ)}.
- (3) {(1,2,3),(1,2,4)}, any signs: ≤ C δ⁻¹L^{2(d−γ)}. If k₃ − k₄ =: w is fixed (the opposite-sign case
  {(1,2,3⁺),(1,2,4⁻)}): ≤ C δ⁻¹L^{2(d−γ)}·min(1, W/|w|).
- (4) {(1,2,3),(1,4,5)} and {(1,2,3),(1,2,4,5)} (DH23 conventions: k₁ in both tuples with opposite signs, no tuple with
  three equal signs): ≤ C δ⁻²L^{3d−4γ} = C δ⁻²L^{3(d−γ)−γ₀}.

*Proof.*
- (1), first system: with s := k₁ + k₂ fixed, |k₁|² + |k₂|² = (|s|² + |k₁ − k₂|²)/2, so k₁ − k₂ lies in a shell; use
  Lemma 2.0(b).
- (1), second system: |k₁|² − |k₂|² = 2k₁·k − |k|², a slab (Lemma 2.0(a)); and trivially ≤ (2L+3)^d.
- (2): by the identity k₁ − k₂ + k₃ = k ⇒ |k₁|² − |k₂|² + |k₃|² − |k|² = −2(k₁ − k)·(k₃ − k) (corrected sign, APPB
  errata L2110), the system is |x·y − α′| ≤ W in two free vectors. Use Lemma 2.1(i).
- (3): count (1,2,3) by (2); k₄ is then fixed by the second linear equation. For fixed w, subtract the energies:
  w·k₃ ∈ window, which is a (basiccount01) system in the variables of (2) with r = w and ξ ∈ {x, y, x+y} (CHECKED,
  `reparam_check.py` (R3)). Use Lemma 2.1(ii).
- (4): there is an explicit affine bijection (k₁, …, k₅) ↔ (x, y, z) under which the two linear equations hold
  identically and the energies become ±2x·y + c and ±2ζ·z + c, with ζ ∈ {x − v, x + y − v, x + y − v − z}.
  - CHECKED symbolically for all 18 admissible sign patterns of {(1,2,3),(1,4,5)} (`reparam_check.py` (R1)).
  - The choice: the tuple in which k₁ is a sum (signs k₁ − k₂ − k₃) supplies the pair (x, y); otherwise tuple A does.
    The table in `out_reparam_check.txt` lists v.
  - For {(1,2,3),(1,2,4,5)}: eliminating ε_p k_p + ε_{p′}k_{p′} gives the triple (s, q, q′) with s of the **same**
    sign as in (s, p, p′). It never has three equal signs, because the degree-4 atom has two signs of each kind. All 6
    patterns reduce the same way (`reparam_check.py` (R2)).
  - Then use Lemma 2.2. ∎

**Remarks.**
- *Check against `dh23-appendix-b-errata.md`.* The only App. A erratum, the sign at L2110, is respected (all identities
  verified symbolically). The other APPB errata (L2183 brprop, L2238 3D3-3G, L1904 (increv3), L1912) concern App. B /
  Prop 10.2, which are not used here except through the Lean Prop 10.2 (all γ).
- *DH23's own γ ≤ 1/2 text.* A.2(1) at L2073 ("Cf₁ ≲ L^{2d−4γ}P⁻¹ when γ ≤ 1/2", via (4vecnew)) and A.2(3) at L2088
  ("easily seen to be L^{d−2γ}") agree with Lemmas 2.1 and 2.2. We supply complete proofs.
- *Lean.* `coupledPair_low_bound` (capped A.2(1), γ ≤ 1/2), `exists_low_pair_selector_bound` (the uncapped strip bound
  C·τ²L^{2d}/P for τL ≥ 1, i.e. Lemma 2.1(ii)), `coupledTriple_bound` (A.2(3), all γ, exponent 3(d−γ) − γ₀) and
  `atomCountLemma` (A.3(1)–(2) parts) already cover Lemmas 2.1–2.3, except the reparametrization (4) at γ ≤ 1/2. The
  existing `A23HalfReparam` is γ > 1/2 only.

---------------------------------------------------------------------------------------------------------------------

## 3. Prop 9.4 (`excessprop1`) at γ ≤ 1/2, repaired form

### 3.1 Statement

The statement is in the reading fixed during the formalization:
- the stage-2 run of TARGET §redlg with Op 1 for the 𝒱_γ objects of 𝒞₁ ∪ 𝒞₂ (Cor 1.16′);
- Op 2 only for R29-eligible triangles (v₁, v₂ SG along the triangle pairs, nonzero v₃ gap, designated pairs at hinges);
- ghosts not cut (DH23 L1777 reading, R38);
- Op 3; Op 4;
- tame clusters erased (R29, Op 5);
- degree-2 cuts with the isolated-half bookkeeping (E28 / R48);
- ι through alive cuts and siblings (E21);
- TRUE increments ΔF, ΔV_β.

For every operation except a group-D triangle step:

  𝔇 ≤ C(log L)^C · L^{−η³} · ∏_{new α} T(Q_v, κ_v) · ∏_{α-ghosts deleted} T(Q_g, κ_g)⁻¹ · L^{aΔF − bΔV_β} (·L^{γ₀} for a TARGET Op 1 creating a component).

**Status.** PROVED for γ ≤ 1/2 (§3.2–3.7). Group D is the ghost lemma G (§7), proved in the ghost-step note. The
minimal margins below are exponents at d = 3 and the worst label, q = −γ + η, unless stated otherwise. All are CHECKED
in `arith_low.py` / `ghost_low.py`.

### 3.2 Single cuts (Steps 3–4)

**α-cut** with label Q (exponent q).
- Count: the gap r ∈ B(r₀, 2Q) gives ≤ C(QL)^d choices. With κ = 50 the ball has radius L^{−50η}Q around a current
  parameter: the alive-ι reading of E21, or a sibling.
- The energy class 2k_{ℓ₁}·r − |r|² takes ≤ C(1 + δQL^{2γ}) windows (k_{ℓ₁} + k_{ℓ₂} lies in a unit ball). Δχ = −1.
- Margin: m_α = 3η − η³ − (d−2)q − max(0, q + 2γ) ≥ η − η³ (d = 3; ≥ γ − η³ for d ≥ 4). κ = 50 adds (50d − 100)η ≥ 50η.

**β-cut.** 𝔇 ≤ C(log L)^C (DH23 L1788) against L^{−η³ + a − 2b} = L^{η² − η³}. Margin η² − η³. γ-free.

### 3.3 Triangles without ghosts (DH23 L1791–L1795)

The exponent model is GHOST §0/§3d with γ₀ = γ:
- I_exp = Σ_{new α} d(q_j + 1) + d + s(ρ) + (d − γ)(m − 1 − |N|), where s(ρ) = min(0, −2γ − ρ) is the slab gain of
  one fixed block gap, and Lemma 2.0(a) counts the free momentum;
- RHS_exp = −η³ + Σ_{new}(h + q_j) − Σ_{α-ghosts}(h + q_g) + a(m − 1) − b(m − g_β).

| ΔF | new α | minimal margin (γ ≤ 1/2) |
|---|---|---|
| 0 (B = 1) | 2 | −η³ + 3η − 2η² − 3γ + 2(d−1)(γ − η) = γ − η − 2η² − η³ at d = 3 |
| 1 (B = 2) | 1 | ≥ −η³ + η² + h + (d−1)(γ−η) − 2γ = γ/2 − η/2 + η² − η³ at d = 3 |
| 2 (B = 3) | 0 | 4η² − η³ |

**E7 is moot at γ ≤ 1/2.** The pair count with a fixed difference (Lemma 2.3(1), second system) is used only through
its trivial branch C L^d, which needs no nonzero gap. So the reading `hnz` (nonzero gap at all three atoms) is not needed
in this range.

### 3.4 Triangles with ghosts (E20, R38): groups A–C PROVED, group D = G

Charged form (GHOST §3a). Closed forms, PROVED by the computation below and CHECKED against the grid model on
γ ∈ {0.02, …, 0.5}, η ∈ {γ/200, γ/1000, γ/3000}, d ∈ {3, 4, 6}: 36 patterns, 0 mismatches (`out_ghost_low.txt`).

| group | pattern | minimal margin, γ ≤ 1/2 |
|---|---|---|
| A | no ghost | as §3.3 |
| B | β-ghosts only, B = 2 (1 new α) | ≥ γ/2 − η/2 − η³ |
| B | β-ghosts only, B = 3 (g ghosts) | (4 − g)η² − η³ |
| C | one α-ghost, B = 2 (1 new α) | γ − 2η − 2η² − η³ |
| C | one α-ghost, B = 3 (g ghosts) | γ/2 − 3η/2 + (2 − g)η² − η³ |
| **D** | two α-ghosts (g = 2; or g = 3 with one β-ghost), B = 3 | **−4η − gη² − η³** (attained) |

**Computation for group D.**
- Let q₁ ≥ q₂ be the two α-ghost labels. With g = 2 (m = 1, |N| = 1):
  - I = γ + s(q₁);
  - R = −η³ − b − 2h − q₁ − q₂ = −η³ − 2γ − 3η − 2η² − q₁ − q₂.
- If q₁ ≥ −2γ, then s = −2γ − q₁ and the margin is −η³ − γ − 3η − 2η² − q₂ ≥ −4η − 2η² − η³. Equality holds at
  q₂ = −γ + η.
- If q₁ < −2γ, the margin is ≥ γ − 3η − 2η² − η³ > 0.
- g = 3 is the same with 3η² in place of 2η².

So **the group-D step fails exactly when q₂ > −γ − 3η − gη² − η³**, i.e. when both α-ghost labels lie in the top band
[L^{−γ−3η−O(η²)}, L^{−γ+η}], and then by at most 4η + gη² + η³. `out_ghost_low.txt` tabulates the margin as
(top − q₂)/η − 4.

GHOST's γ > 1/2 value (2γ − 1) − 4η uses b = (1 − γ) + 2η². With γ₀ = γ the 1 − 2γ term cancels. This corrects
§1 of the planning list of open steps (not included), which says "negative by about (1 − 2γ) + 4η": see §7.

### 3.5 Step 1 / Operation 1 (vine-like objects of 𝒱_γ)

**(i) A single vine of 𝒱_γ as the removed VC** (DH23 L1797–L1802; N1 §3.2, N2 §2.1, REFEREED).
- Count: the joint pair gives L^d(RL)^d. Each 2-atom piece is a (basiccount01) system; Lemma 2.1 gives
  ≤ C δ⁻¹L^{2(d−γ)}𝔛⁻¹, with P = the ladder gap for rungs of maximal ladders.
- For T-vines the core is (basiccount02) with ζ ∈ {x, x+y−z}; Lemma 2.2 gives ≤ C δ⁻²L^{3(d−γ)−γ}.
- This gives 𝔇 ≲ R^dL^{2γ} (bad vines (I), (II)) and 𝔇 ≲ R^dL^{γ} (T-vines: the core gains L^{−γ₀}).
- Margins: 2η − η³ (bad), γ + 2η − η³ (T-vine). The κ = 50 version is as in §3.2.

**(ii) VC of two double bonds.**
- 𝔇 ≲ L^{−3(d−γ)}L^d(RL)^d(L^{d−1} + δ⁻¹min(R⁻¹L^{d−2γ}, L^d)).
- Margin: −η³ + 3η − 2γ − (d−2)q − max(−1, min(−q − 2γ, 0)) ≥ 3η − η³. Without the min the margin is
  −η³ + 3η − (d−3)q, also ≥ 3η − η³: the min is not needed here.

**(iii) Other Cor 1.16′ sub-objects** (adjoint/HV of a T-vine, block VC:I+I, block vine (V) inside (VII)): the same
counts (REFEREED, REF2/REF3).

**(iv) TARGET `excessprop1`(2)** (Op 1 creating a component; N2 §2.1, REFEREED): 𝔍 ≲ L^{η³} against L^{γ₀−η³+a−2b}.
Margin γ + η² − 2η³.

### 3.6 Erasures and bookkeeping (γ-free; exponents re-checked)

- **R29 / E11 / E16 / E17.** Tame atoms are never cut; maximal tame clusters are erased.
  - Erasure deviation: factor 1 if pinned; if unpinned (deg 4, c ≤ 2), a gain L^{−(d−2γ−η)} ≤ L^{−(2−η)}.
  - TARGET remtame2 net exponent: −(d − 2γ − 2γ₀) + 2η + 5η² = −(d − 4γ) + 2η + 5η² ≤ −1 + 2η + 5η².
- **E28 / R48.** The margin X = d − γ − 1/4 − 1/40 ≥ 2.225 pays L^{γ₀+3η²}.
- **E19.** p_sb ≤ 2p_op, absorbed since η³/2 ≥ 8η⁶.
- **(together3) → (finalcount1).** Needs d − γ − 1/4 − 1/40 − (4γ₀ + 4η + 5η²) > 0, i.e. ≥ 0.225 − 4η − 5η² at
  d = 3, γ = 1/2. This is tight but positive: d − γ − 4γ₀ ≥ 1/2 with equality only at (d, γ) = (3, 1/2).

### 3.7 ι/κ (E21) and N1

ι_v is defined through cuts alive at the time of v's cut, including the sibling cuts of the same triangle (Lean
`IotaUnif` / `SibUnif`, in the formalization of the stage-2 run). κ_v is fixed at creation and used in the creation
bound, in Prop 9.6's product and in a ghost refund.

The property consumed by Prop 9.6 is exactly Lean's `FinalDec.iota` (N2): for α-atoms v₁ ≠ v₂ with κ₁ + κ₂ = 0, a
β-atom v₃, nonzero gaps and r₃ = s₁r₁ + s₂r₂, one has |r₃| ≥ L^{−50η}min(R₁, R₂)/2. γ-free (GHOST §5c; the Lean
formalization of the stage-2 run).

N1 (`FinalDec.betaGap`, nonzero β-gaps) holds by the R29 erasure rule (E11). γ-free.

---------------------------------------------------------------------------------------------------------------------

## 4. Prop 9.6 (`lgmolect`) at γ ≤ 1/2

### 4.0 Hypotheses

M₀ is a component of M_fin with |M₀| ≤ (1 + log L)^m, satisfying:
- **FinalShape** (Lean `WaveTurbulence/Foundations/FinalCount/Prop96Statement.lean`): caps, noLoop, conn, degPos,
  classes, dir2, oddDeg (weakened), evenDeg, noTriple, evenBeta, cycle, chains;
- **FinalDec_γ**: Lean `FinalDec` with `vineLG` read over **𝒱_γ**, i.e. a component that `IsVineGamma γ` (with
  degree-2 joints), or a double bond, is LG. The other fields are labRange, kapVals, epsLG, alphaGap, alphaSG,
  betaGap (N1), noBetaCut, iota (N2).

These are the conclusions of Prop 9.5′ for 𝒱_γ:
- the structural clauses and "vine components are LG" are REFEREED (N2 §2.3 via subpro′(6); E10, E13, E16 readings
  γ-free);
- the clause "a triangle component has at most one α-atom" (FinalShape.cycle) **requires G** (§7).

**Conclusion:** (finalcount), with constants as in `Prop96At` (C★ depends on d, γ, η; m enters only R₀).

### 4.1 Operation (c), sharp form (Finding 1)

**Lemma 4.1.** PROVED. Let a chain K of α/β-atoms join distinct ε-atoms, and suppose its removal does not disconnect
M₀. Let R be such that some atom of K has gap ∼ R (|r| ≥ R/2). Then

  𝔇_c ≤ C(log L)^C (L^{γ−1} + δ⁻¹min(R⁻¹L^{−γ}, L^{γ})) ≤ C(log L)^C δ⁻¹L^{γ₀}.

*Proof.*
- Δχ = −1. The chain bonds are determined by one of them, k, through the fixed charges.
- One energy window, at the chain atom with gap r, reads 2k·r − |r|² ∈ window. Lemma 2.3(1) (second system) gives
  ≤ C(L^{d−1} + δ⁻¹min(R⁻¹L^{d−2γ}, L^d)), and ≤ (2L+3)^d without any gap information.
- The post parameters of the two end atoms are fixed up to (log L)^C windows (sum of the chain's equations, as at DH23
  L1788). The ladder factor changes by (log L)^C. ∎

**Non-disconnection** in even perfect components (CASE4 Lemma 2.4(i)): removing one chain leaves two degree-3 atoms in
one component (parity).

**Erratum (Finding 1).** The printed (operc) at L1861 gives only δ⁻¹R⁻¹L^{−γ} ≤ δ⁻¹L^{1−γ}, and L^{1−γ} > L^{γ₀} when
γ < 1/2. Case (2) (§4.6) and the class-2 branch of case (4)′ (§4.8) need the min term. `arith_low.py` "expected
failures": the printed form loses 1 − 2γ in case (2).

### 4.2 Operation (d)

𝔇_d ≤ C(log L)^C (DH23 L1865–L1867). The new bond is k_{ℓ₂} + g(k_{ℓ₁} − k_{ℓ₂}) with |g| ≤ 3 chosen to keep LG up to a
constant. γ-free. The Lean decoration-level form is `OpDW.opDW`.

### 4.3 Operations (d) + (e): (opere) at γ ≤ 1/2 (Finding 2)

**Lemma 4.3.** PROVED.

*Setting.*
- M′ is a molecule with relaxed parameters (c_v, β_v).
- p ≠ q are joined by exactly two bonds ℓ_a, ℓ_b, and a chain C of degree-2 atoms runs from p to q, with end bonds ℓ₁
  at p and ℓ_k at q.
- Put S := C ∪ {p, q}. Every other bond at p, q is external. There is at most one per atom: ℓ_p to s, ℓ_q to t.
- If both externals exist, s ≠ t.
- w := the total charge of C, so k_{ℓ_k} = k_{ℓ₁} − w for every decoration; P := |w| > 0.
- M″ is M′ minus S, plus a bond s–t (direction matching) when both externals exist. Its value is
  k_{ℓ_q} + g(k_{ℓ_p} − k_{ℓ_q}), |g| ≤ 3, chosen to keep LG.

*Conclusion.* 𝔇_{de} ≤ C(log L)^C·min(1, δ⁻¹L^{−2γ}/P). In particular P ≥ c L^{−γ−100η} gives
𝔇_{de} ≤ C(log L)^C δ⁻¹L^{−γ₀+100η}, i.e. (opere) with 100η in place of 200η.

*Proof.*
- **Δχ = −2 in all three external configurations:**
  - two externals with s–t added: ΔV = −(|C|+2), ΔE = −(|C|+4), ΔF = 0;
  - one external: the same ΔV and ΔE, ΔF = 0;
  - none: ΔE = −(|C|+3), ΔF = −1.
- **The external values are determined.** All c_v of M′ are fixed parameters (the post parameters of the earlier
  operations).
  - Two externals: then p, q have degree 4 in M′, so in = out = 2; chain atoms have in = out = 1. So S is balanced,
    ℓ_p and ℓ_q cross ∂S in opposite directions, and k_{ℓ_p} − k_{ℓ_q} = ±Σ_{v∈S}c_v is fixed. With the new bond's value
    this fixes k_{ℓ_p}, k_{ℓ_q}, for each of ≤ 7 values of g.
  - One external: it is the only bond crossing ∂S, so conservation over S fixes its value.
  - None: nothing to fix.
- **Windows.** The energy sum over S fixes |k_{ℓ_p}|² − |k_{ℓ_q}|² up to |S|W ≤ (log L)^m W. Subdivide into
  (log L)^m windows; this fixes the post parameters at s, t.
- **The removed system.** The unknowns are k_a, k_b, k₁. At p: ε_ak_a + ε_bk_b + ε₁k₁ = fixed, with p's energy
  window. At q (negated): ε_ak_a + ε_bk_b + ε₁(k₁ − w) = fixed, with q's window.
  - By the identity of Lemma 2.3(2), p's window is |x·y − α′| ≤ W in free vectors (x, y).
  - The difference of the two energies is ε₁(2w·k₁ − |w|²) ∈ window of width 2W, and w·k₁ = w·ξ + const with
    ξ ∈ {x, x+y}. CHECKED for all 6 sign patterns (`reparam_check.py` (R3)).
  - Lemma 2.1(ii) gives ≤ C L^{2d}W·min(1, 2W/P).
- **Total.** 𝔇 ≤ C(log L)^C·L^{2d}W min(1, W/P)·L^{−2(d−γ)}(C⁺)^{−2}δ = C(log L)^C min(1, W/P), since δL^{2γ}W = 1. ∎

**Why the uncapped form.** With TARGET's capped (basiccount01), 𝔛 = (log L)² as soon as δL^{2γ}P ≥ (log L)². Then the
bound is only (log L)^{−2}, with no power gain.

**Which configurations occur.** Within case (6) (§4.10) the three configurations of the lemma are exactly those that
occur. The fourth, both externals at one atom s, is excluded:
- S ∪ {half of s} would be separated by a cut of s along (ℓ_p, ℓ_q);
- these bonds are opposite at s (S is balanced), and the cut has gap ±w ≠ 0;
- in M₀ this is a β-cut with nonzero gap at an atom of degree ≥ 3, which contradicts `noBetaCut`.

"At most one external bond" (DH23's first alternative) occurs when p or q is an end of the α-chain removed by (c). It is
covered by the lemma.

### 4.4 Cycle components (DH23 L1854–L1855)

χ = 1 and ρ₀ ≤ s, so no interpolation is needed: the requirement is LHS < RHS − η⁵s. All PROVED, CHECKED.

| component | bound | RHS_exp − η⁵s | margin |
|---|---|---|---|
| double bond (vine (I), LG by `vineLG`) | L^{γ−1} + δ⁻¹L^{−η} | −η² − 2η⁵ | η − η² − 2η⁵ |
| triangle, V_α = 0 | δ⁻¹L^{γ} (free vector: trivial L^d) | γ + η² − 3η⁵ | η² − 3η⁵ |
| triangle, V_α = 1 (label R) | L^{γ−1} + δ⁻¹R⁻¹L^{−γ} | −h − q − η² − 3η⁵ | (γ − 3η)/2 − η² − 3η⁵ |
| triangle, V_α ≥ 2 | excluded by FinalShape.cycle (**needs G**) | — | — |
| cycle s ≥ 4, V_α = 0 | δ⁻¹L^{γ} | sb − a − sη⁵ | (s−3)γ + (2s−5)η² − sη⁵ ≥ γ |
| cycle s ≥ 4, V_α ≥ 1, V_β ≥ 1 | L^{γ−1} + δ⁻¹R₁⁻¹L^{−γ} | (−h − q₁) + τ(V_α−1) + bV_β − a − sη⁵ | ≥ (γ − 13η)/2 − 3η² − 4η⁵ |

At γ ≤ 1/2 the triangle counts need no nonzero-gap information (N1 is not used here).

*Why a triangle with two α-atoms is excluded.* For such a triangle the same count gives margin ≈ −4η when R₂ is at the
SG top, so it cannot be left in M_fin. This is why FinalShape.cycle, and hence G, is needed.

### 4.5 Case (1): the odd component (DH23 L1874–L1877; E8, E12)

- **w := V_α + V_β ≥ 1.** Operations (a), (b) on ε-atoms, plus free deletion of degree-1 α/β-atoms (E8), give 𝔄₀ ≲ 1.
  This is Prop 10.1′, LEAN all γ: `P101.proposition_one_off_bound`.
  - RHS_exp ≥ τV_α + bV_β ≥ τw.
  - Margin ≥ τw − C₀η³(w + 3) ≥ (τ − 4C₀η³)w > 0.
- **w = 0, both odd atoms of degree 3** (E12). E = 2V − 1 and there is no triple bond, so Prop 10.2(1) (LEAN) gives
  𝔄₀ ≲ L^{−3γ/5}. Margin (3γ/5)(1 − η³) − 3C₀η³ > 0.

### 4.6 Case (2): V_β ≥ 3 (DH23 L1878)

Operation (c) on any chain (Lemma 4.1, **sharp**: δ⁻¹L^{γ}), then Prop 10.1′: 𝔄₀ ≲ δ⁻¹L^{γ}.
- RHS_exp ≥ τV_α + bV_β − a ≥ γ + η² + τV_α + b(V_β − 3).
- Margin ≥ η² + γη³ − 4C₀η³ + (τ − C₀η³)V_α + (b − C₀η³)(V_β − 3) ≥ η²(1 − 4/30) > 0.

### 4.7 Case (3): V_β = 2, V_α ≥ 1, or V_β = 1, V_α ≥ 3 (DH23 L1880–L1881)

Operation (c) on a chain containing an α-atom v₁ (label R₁), then Prop 10.1′: 𝔄₀ ≲ L^{γ−1} + δ⁻¹R₁⁻¹L^{−γ}. The
R₁⁻¹ branch is binding:
- V_β = 2: margin = (γ − 3η)/2 − η² − γη³ − 4C₀η³ + (τ − C₀η³)(V_α − 1) > 0.
- V_β = 1, V_α ≥ 3: margin = (γ − 13η)/2 − 3η² − γη³ − 5C₀η³ + (τ − C₀η³)(V_α − 3) > 0.

The L^{γ−1} branch has margin ≥ 1 − γ − O(η). The printed (operc) also suffices here.

### 4.8 Case (4)′: V_α = 0, V_β = 2 (consolidated in 𝒱_γ terms)

**Lemma 4.8 (case (4)′).** PROVED from REFEREED pieces. Under §4.0, with V_α = 0 and V_β = 2:

  𝔄₀ ≲ L^{−η/128}.

Hence (finalcount) holds: the required bound is L^{2b−a} = L^{−η²}, and the margin (η/128)(1 − η³) − η² − 3C₀η³ > 0
since η ≤ 1/6000.

*Proof.*
- **Setup.** Let b₁, b₂ be the β-atoms. Either they lie in two chains (σ = 0) or form one chain u→b→b′→v (σ = 1).
  σ ≥ 2 would make M₀ a double-bond cycle. Let M₁ := the closure: operation (d) on each β-chain.
- **M₁ is RegCore:** 4-regular, loopless, connected, no cut vertex, ≤ 2 triple bonds (Lean `regcore_closureTwo`,
  `trip_closureTwo`, `nocut_M0`; the last uses `noBetaCut`, `epsLG` and parity). γ-free.
- **(A) M₁ is Y-exceptional** (some complete (Y)-reduction ends in Q or T).
  - (A1) Q-type: M₀ is a vine (II), with m = k+1 rungs when M₁ ≅ Z_k(Q). This is Lean `yrouteQ_zq`,
    `halfClosure_of_zq`, `isVine_of_halfClosure` / `c4_two_vine` (γ-free; E3 reading m ≥ 1).
  - (A2) T-type: M₀ **is a T-vine by definition** (`TVine.IsTVine`, decision D11). Take S = atoms of M₀ and joints
    b₁, b₂:
    - `IsBlock S b₁ b₂` (`WaveTurbulence/Foundations/WaveB/Molecules.lean` L131: joints distinct with one in- and one
      out-bond in S, every other atom of in-S degree 4, S group-connected): by `dir2` at b₁, b₂; by `classes` +
      `evenDeg` with V_α = 0 (all other atoms are ε of degree 4); and by `conn`;
    - at most two bonds between any two atoms: `noTriple`;
    - `IsClosure S b₁ b₂ M₁`: σ = 0 gives one added bond per joint; σ = 1 gives the bond u–v; this is operation (d);
    - a Y2-path from M₁ to the doubled triangle.

    The clause "no interior cut atom" is not part of `IsTVine` (N3 Lemma 4.1), and the explicit ylem1′ list is not
    needed.
  - In both cases M₀ ∈ 𝒱_γ, so `vineLG`_γ gives |r| > L^{−γ+η}. CASE4 Lemma 2.4 (REFEREED; at γ ≤ 1/2 its condition
    γ ≤ 1 − 2η is automatic) gives 𝔄₀ ≲ (log L)^C(L^{γ−1} + δ⁻¹L^{−η}) ≤ L^{−η/2}.
  - Its step (ii) uses Lemma 4.1 with R > L^{−γ+η}. Its step (iii) uses Prop 10.1, with LG at every atom because the
    other β-chain has gap ±r (CASE4 Lemma 2.1).
- **(B) M₁ is not Y-exceptional.** Prop 10.4(2)′ (§5.4) applies to M₁ at the LG parameter weakened by the operations
  (d): η_s = η/4 in Lean, with the bond ℓ of the second chain. It gives a decoration split (Lean `SplitBound`).
  - Class 1: 𝔄(M₁; ¬Q) ≲ L^{−η_s/4}. Operation (d) twice gives 𝔄₀(class 1) ≲ (log L)^C L^{−η_s/4}.
  - Class 2: 𝔄(M₁∖ℓ; Q) ≲ L^{−γ₀−η_s/4}. Operation (d) on chain 1, then operation (c) on chain 2 by Lemma 4.1
    **sharp** (≤ δ⁻¹L^{γ₀}, whatever the β-gap), gives 𝔄₀(class 2) ≲ (log L)^C δ⁻¹L^{γ₀}L^{−γ₀−η_s/4}.
  - The decoration-level mechanics are Lean `class1_bound`, `class2_bound`, `opDW`, `opCFree` (γ-free).
  - Polylog absorption gives L^{−η/128} (Lean `split_arith`; deviation 9 of the handoff of the γ > 1/2
    formalization of Prop 9.6, [`finalcount-prop96-handoff.md`](finalcount-prop96-handoff.md)).
  - The small cell X (M₁ reaching X; the Lean `YReachesSmallCell` artifact) is part of Prop 10.4(2)′ at paper level
    (case (I), §5.4). ∎

**What the producer (stage-2 run with 𝒱_γ) must supply for (4)′:** `vineLG` over 𝒱_γ (Prop 9.5′), `noBetaCut`,
`epsLG`, `betaGap`, `noTriple`, `chains`. The splicing of 𝒱_γ-VCs in stage 1 enters only through Prop 9.5′ (REFEREED).

### 4.9 Case (5): V_α = V_β = 1 (DH23 L1887–L1889; N2 §4.1)

- Operation (c) on the α-chain (label R), operation (d) on the other chain if any. M₁ has two degree-3 atoms,
  E = 2V − 1, ≤ 1 triple bond, and the β-cut hypothesis (from `noBetaCut`).
- Prop 10.4(1) (LEAN all γ: `G8R.prop104_one`): 𝔄₁ ≲ L^{−4γ₀/7}, unless M₁ ≅ Q′_m. In that case M₀ is a vine (II),
  hence LG, which contradicts its α-joint (N2 Lemma 4.1, REFEREED; family-free).
- So 𝔄₀ ≲ (log L)^C(L^{γ−1} + δ⁻¹R⁻¹L^{−γ})L^{−4γ/7}. RHS_exp = −h − q + b − a.
  - R⁻¹ branch: margin = γ/14 − 3η/2 − 3η² − (11/7)γη³ − 3C₀η³ > 0.
  - L^{γ−1} branch: margin ≥ 1 − 13γ/14 − 5η/2 − O(η²) > 1/2.
  - With the printed "1" in place of L^{γ−1} one needs γ/14 > 5η/2 + …, also true under (H_η).

### 4.10 Case (6): V_α = 2, V_β = 1, with operation (e) and N2 (DH23 L1892–L1896)

The labels are R₁ ≥ R₂ (exponents q₁ ≥ q₂). Operation (c) on the chain through v₁ (Lemma 4.1:
L^{γ−1} + δ⁻¹R₁⁻¹L^{−γ}), operation (d) on the other chains, giving M₁. RHS_exp = −2γ − 3η − 3η² + (κ₁+κ₂)η − q₁ − q₂.
In the binding R₁⁻¹ branch, with 𝔄₁ ≲ L^{X₁}:

  margin = −γ − 3η − 3η² + (κ₁+κ₂)η − q₂ − γη³ − (1−η³)X₁ − 4C₀η³.

**(6a) κ₁ + κ₂ ≥ 50.** X₁ = 0 (Prop 10.1). Margin ≥ 46η − 3η² − O(η³).

**(6b) M₁ has no triple bond.** E = 2V − 1 and M₁ is connected (parity). Prop 10.2(1) gives X₁ = −3γ/5. Margin
≥ 3γ/5 − 4η − 3η² − O(η³).

**(6c) R₂ ≤ L^{−γ−50η}.** X₁ = 0. Margin ≥ 47η − 3η² − O(η³).

**(6d) Otherwise:** κ₁ = κ₂ = 0, M₁ has a triple bond, and R₁ ≥ R₂ ≥ L^{−γ−50η}.
- **The β-gap.** By conservation on M₀ (c_v = 0 at ε-atoms, c_v = ±gap at α/β-atoms), r_β = s₁r₁ + s₂r₂ with all three
  gaps nonzero (alphaGap, betaGap). N2 (`FinalDec.iota`) gives |r_β| ≥ L^{−50η}R₂/2 ≥ L^{−γ−100η}/2.
  - This covers v₁, v₂ created by one Step-1 removal (r₂ = ±r₁, so |r_β| = 2|r₁|) and by one triangle (siblings).
- **The chain for (e).** Order the operations (d) so that the one creating a triple bond is last; call its chain C.
  C ⊂ {v₂, β}, as a set of chain atoms. Its total charge w satisfies:
  - C = {v₂}: P = |r₂| ≥ R₂/2;
  - C = {β}: P = |r_β| ≥ L^{−γ−100η}/2;
  - C = {v₂, β}: P = |r₂ ± r_β| = |r₁| ≥ R₁/2, by the sum relation.

  So P ≥ L^{−γ−100η}/2 in every case.
- **The configuration** of Lemma 4.3 holds:
  - the triple bond p≡q consists of the bond from (d) on C plus a double bond of the intermediate molecule (an earlier
    (d)-bond may be one of its two copies; Lemma 4.3 applies to the intermediate molecule);
  - p, q have degree 4 in M₀, so each has at most one external bond;
  - "both externals at one atom" is excluded by `noBetaCut` (§4.3).
- **The bound.** Performing (e) instead of the last (d), Lemma 4.3 gives 𝔇_{de} ≲ δ⁻¹L^{−γ+100η}, and Prop 10.1 gives
  𝔄₂ ≲ 1. So X₁ = −γ + 100η, and the margin is ≥ γ − 104η − 3η² − O(η³) > 0. This is the binding constraint
  η < γ/104 at d = 3 (`arith_low.py`), satisfied by (H_η).
- **The L^{γ−1} branch** has margin ≥ 1 − γ − 5η − O(η²) in all sub-cases.

**Operation (e) is necessary at γ ≤ 1/2.** The γ > 1/2 route (Lean `case_six`: operation (c) and Prop 10.1′ only) has
margin −4η − 3η² − O(η³) at R₁ = R₂ = L^{−γ+η}, κ = 0 (`arith_low.py`). This confirms the `Case6_96.lean` docstring
and deviation 10 of [`finalcount-prop96-handoff.md`](finalcount-prop96-handoff.md).

### 4.11 Damaged and imperfect components

- **Damaged** components (R29 erasures): Lean `prop96_damaged` uses only `hsm`, `hηs` (its handoff,
  [`finalcount-prop96-handoff.md`](finalcount-prop96-handoff.md): "hsm2 and γ > 1/2 are NOT needed"). Valid at
  γ ≤ 1/2. LEAN.
- **TARGET imperfect components** with R ≥ 2: 𝔄 ≲ 1 and 𝔄 ≲ L^{−η²ρ+C₀W}, interpolated to L^{−η⁴ρ+C₀η²W}. This needs
  C₀η² ≤ min(γ/4, γ₀, η), true under (H_η). N2 §2.3, REFEREED; exponents re-checked.

### 4.12 The η-condition

Binding constraints at d = 3 over the γ-grid (`arith_low.py`):

| constraint | threshold |
|---|---|
| (6d) | η/γ < 1/104.0 |
| (3) with V_β = 1 | η/γ < 1/14.2 |
| (5) | η/γ < 1/23.4 |
| (6b) | η/γ < 1/8.7 |
| Prop 10.4(2)′ | dη + η/4 < γ₀ (Lean `hηd : dη ≤ γ₀/4`) and η ≤ γ₀/200 (Prop 10.3, Lean `hη200`) |
| interpolation | C₀η ≤ 1/30 |

(H_η) (dη ≤ γ/1000, 4·1440061η ≤ 1) implies all of them. No condition of the form η ≤ c(2γ − 1) is used.

---------------------------------------------------------------------------------------------------------------------

## 5. Prop 10.4 at γ ≤ 1/2 (the molecule half)

The Lean proof of Prop 10.4(2)′ (`G8R.CoreTheorem.core_split`) uses γ > 1/2 **only** to discharge three inputs:
`PairGainInput`, `SmallGapPairInput`, `MergeInput` (each `1/2 < γ → …`).
- Its other inputs hold for all γ: BetaCut, BridgeSplit, BiBridge, BiBridgeEqual, Prop 10.2 (both statements), and
  Prop 10.3 (`prop103At_of_G6`, η ≤ γ₀/200).
- Prop 10.1 holds for all γ (`prop101At_of_G6`).
- The case structure (DH23 L1961–L1977 with YLEM1 R2) is γ-free; its exponent comparisons are listed in §5.4.

So Prop 10.4(2)′ at γ ≤ 1/2 reduces to the three inputs below. The statements are those of
`WaveTurbulence/Foundations/FinalCount/G8R/CoreInputs.lean` (`PairGainAt`, `SmallGapPairAt`, `MergeAt`) with γ ≤ 1/2.

### 5.1 Pair gain (DH23 L1965–L1967, case (I); Lemma A.3(4)). PROVED

*Statement.* a has degree 3 and b ∈ M with either (b of degree 4 and a = b double) or (b of degree 3 and ab single),
and M∖{a,b} is connected. Then 𝔄(M) ≤ C(log L)^C δ^{−1/2}L^{−γ₀}·sup 𝔄(M∖{a,b}).

*Proof.*
- Δχ = −3 (V −2, E −5, F 0).
- The removed bond values solve the system at a and b. These are 5 vectors and two vector equations:
  {(1,2,3),(1,4,5)} for a single bond (shared bond = 1, opposite signs at a, b), or {(1,2,3),(1,2,4,5)} for a double
  bond. No tuple has three equal signs, since in- and out-degree are ≤ 2.
- Lemma 2.3(4): ≤ C δ⁻²L^{3d−4γ}. Post parameters: (log L)^C windows. Ladder factor: (log L)^C.
- So 𝔇 ≤ C(log L)^C δ⁻²L^{3d−4γ}·L^{−3(d−γ)}(C⁺)^{−3}δ^{3/2} = C(log L)^C δ^{−1/2}L^{−γ}. ∎

### 5.2 Small-gap pair (DH23 L1975, case (III)). PROVED

*Statement.*
- v₁ = v₂ is a double bond, both atoms of degree 4. v₁ has extra bonds ℓ₃, ℓ₄; v₂ has ℓ₅, ℓ₆.
- |k_i ± k_j| ≤ L^{−γ+η} for some i ∈ {3,4}, j ∈ {5,6} (`SmallPairGap`), on the admissible set.
- M∖{v₁,v₂} is connected.

Then 𝔄(M) ≤ C(log L)^C δ L^{−(d−2)γ+dη}·sup 𝔄(M∖{v₁,v₂}) ≤ C(log L)^C L^{−γ₀+dη}·sup 𝔄(…).

*Proof.*
- Δχ = −4.
- Count: k_i in a unit ball (≤ C L^d), then k_j in a ball of radius L^{−γ+η} (≤ C L^{d(1−γ+η)}).
- Then the triple (1,2,i′) at v₁ has ≤ C δ⁻¹L^{2(d−γ)} solutions (Lemma 2.3(2)), and k_{j′} is fixed by the linear
  equation at v₂.
- 𝔇 ≤ C(log L)^C L^{d+d(1−γ+η)}δ⁻¹L^{2(d−γ)}·L^{−4(d−γ)}δ² = C(log L)^C δ L^{−(d−2)γ+dη}.
- Since (d−2)γ ≥ γ = γ₀, this is ≤ L^{−γ₀+dη}. (The same proof works for γ > 1/2, since (d−2)γ > 1 − γ.)
- In Prop 10.4(2)′ the post molecule has 𝔄 ≲ 1 (Prop 10.1), so 𝔄(M′) ≲ L^{−γ₀+dη} ≤ L^{−η/4} under dη + η/4 < γ₀. ∎

### 5.3 Merge (DH23 L1977, case (IV); Lemma A.3(1)). PROVED

*Statement.* As in 5.2 but with no `SmallPairGap` on the admissible set, and M LG. Merging v₁, v₂ into one atom carrying
ℓ₃, …, ℓ₆ gives a LG pseudomolecule, and 𝔄(M) ≤ C(log L)^C δ⁻¹L^{−η}·sup 𝔄(merged).

*Proof.*
- Δχ = −1. Given the merged decoration, the pair (k₁, k₂) of the double bond satisfies ε₁k₁ + ε₂k₂ = fixed, with v₁'s
  window.
- If the double bond is opposite at v₁: k₁ − k₂ is fixed with |k₁ − k₂| > L^{−γ+η} (LG at v₁). Lemma 2.3(1), second
  system, gives ≤ C(L^{d−1} + δ⁻¹L^{d−γ−η}).
- If it is same-direction: Lemma 2.3(1), first system (the thin annulus of `MergeFiberBound`, here a volume count by
  Lemma 2.0(b)), gives ≤ C δ⁻¹L^{d−2γ}.
- So 𝔇 ≤ C(log L)^C(L^{γ−1} + δ⁻¹L^{−η} + δ⁻¹L^{−γ}) ≤ C(log L)^C δ⁻¹L^{−η}.
- LG of the merged atom on the new pairs (ℓ_i, ℓ_j), i ∈ {3,4}, j ∈ {5,6}, is the negation of `SmallPairGap`. The ladder
  cells of the merged molecule are handled as in Lean (`GoodCell` hypothesis), γ-free. ∎

### 5.4 Prop 10.4(2)′ at γ ≤ 1/2. PROVED

DH23 L1961–L1977 with YLEM1 R2 ("not Y-exceptional"), the inputs 5.1–5.3, and the LEAN all-γ inputs above. Exponents:
- (I), Δχ = −3: L^{−γ₀}·L^{−η/3} (Prop 10.2(2)).
- (I), Δχ = −2: (L^{−3γ₀/5})² = L^{−6γ₀/5} ≤ L^{−γ₀−η/4}, since γ₀/5 ≥ η/4.
- (II), k_{ℓ₁} ≠ k_{ℓ₂}: L^{γ₀}(L^{−3γ₀/5})² = L^{−γ₀/5} ≤ L^{−η/4}.
- (II), equal: (L^{−3γ₀/5})² ≤ L^{−γ₀−η/4} (with Prop 10.4(1)).
- (III): L^{−γ₀+dη} ≤ L^{−η/4}.
- (IV): L^{−η/2}, then repeat; the quadrilateral of double bonds uses Lemma 2.3(4), then (1) with LG.
- Single bonds only: Prop 10.3 (LEAN), L^{−γ₀−η/2}.

**The small cell X** = (a=b, c=d, ac, bd, ad, bc), reached after ≤ 2 (Y)-sequences, is case (I).
- For every bond ℓ* of X, X∖ℓ* contains an adjacent pair of degrees (3,3) (ℓ* a copy of a double bond) or (3,4)
  (ℓ* single).
- Removing that pair costs L^{−γ₀} (5.1). It leaves the double bond c=d with E = 2V − 2 > 0, which gains L^{−η/3}
  (Prop 10.2(2)). This is Lean `xMinus_afree`, whose only γ > 1/2 use is `PairGainAt`.
- So `Case4SmallCell` holds at γ ≤ 1/2 mathematically. Lean still needs the arithmetic of `theorem_A_X` re-checked at
  γ ≤ 1/2 (§9).

**Prop 10.4(1)** at γ ≤ 1/2: LEAN (`prop104_one`, all γ). Exceptions are exactly Q′_m (N2 Lemma 4.1, REFEREED).

---------------------------------------------------------------------------------------------------------------------

## 6. Every repair made during the formalization in this region, re-checked at γ ≤ 1/2

| repair | where | γ ≤ 1/2 status |
|---|---|---|
| E7 (ΔF = 1 pair count needs nonzero difference) | DH23 L1793–L1794 | moot: the trivial branch C L^d suffices (§3.3) |
| E8 (free deletion of degree-1 α/β) | L1876 | γ-free; Prop 10.1′ LEAN all γ (§4.5) |
| E10 (vine component identification; HV case) | L1815 | γ-free; Prop 9.5′ (REFEREED for 𝒱_γ) |
| E11 / R29 (tame atoms erased; N1) | TARGET L2152, L2218 | γ-free; erasure gain larger at γ ≤ 1/2 (§3.6) |
| E12 ((3,3) odd component) | L1876 | Prop 10.2(1): L^{−3γ/5} (§4.5) |
| E13 (DV with both vines SG) | TARGET L2101 | γ-free; DV′ for 𝒱_γ (N2 N6, REFEREED) |
| E16 / R29 (ZG hinge v₃; designated pairs at hinges) | TARGET L2152 | γ-free structure; damaged components by `prop96_damaged` (all γ) |
| E17 (cluster erasure; "imperfect = odd") | TARGET L2152, L2193 | γ-free |
| E19 (p_sb ≤ 2p_op) | TARGET L2213 | γ-free (η³/2 ≥ 8η⁶) |
| E20 / R38 (ghost charge and refund) | DH23 L1777, L1791–L1795 | groups A–C PROVED (§3.4); **group D = G** |
| E21 (ι through alive cuts) | DH23 L1803 | γ-free; N2 = `FinalDec.iota` (§3.7) |
| E22 / R37 (hinge triple bonds) | TARGET L2140 | γ-free |
| E28 / R48 (isolated-half ledger) | TARGET L2156–L2162 | X = d − γ − 0.275 ≥ γ₀ + 3η² (§3.6) |
| (operc) sharp form | L1861–L1862 | **needed at γ < 1/2** in cases (2), (4)′ (Finding 1) |
| (opere) | L1869–L1871 | PROVED with the uncapped A.2(1) (Finding 2; Lemma 4.3) |
| R26 X-route / small cell | Prop 10.4(2) L1961–L1977 | case (I) with 5.1 (§5.4) |
| E1 / F69b (case (4) false for (I)–(VIII)) | L1883–L1886 | replaced by case (4)′ with 𝒱_γ (§4.8) |
| E3 (vine (II) includes m = 1) | L1421 | used in (4)′ (A1) and case (5) |
| deviation 9 of the γ > 1/2 Prop 9.6 handoff (exponent η/128) | Lean `case4_finish` | margin (η/128)(1−η³) − η² − 3C₀η³ > 0 (§4.8) |
| APPB errata (L2110 sign) | App. A | respected (§2) |

---------------------------------------------------------------------------------------------------------------------

## 7. The ghost lemma G (the ghost step for γ ≤ 1/2): exactly what this note needs

G is an input proved elsewhere: it is proved in the ghost-step note
([`gamma-le-half-ghost-step-notes.md`](gamma-le-half-ghost-step-notes.md), Theorems 6.1 and 7.1; see its §11a), in the
form (G-D) below.

**G.** For 0 < γ ≤ 1/2 there is η₀(d, γ) > 0 such that for 0 < η ≤ η₀ satisfying (H_η) the following holds. The stage-2
run is that of §3.1. G may modify the treatment of the triangles that contain two α-ghosts, and only those. For every
decoration class:
- **(G1) Final shape.** Every component of M_fin satisfies FinalShape and FinalDec_γ of §4.0, or is damaged (Lean
  `DamagedShape`/`DamagedDec`), or is a TARGET imperfect component. In particular:
  - no perfect triangle component has two α-atoms (FinalShape.cycle);
  - N1 (`betaGap`), N2 (`iota`), `noBetaCut`, `epsLG` and `vineLG` over 𝒱_γ hold.
- **(G2) Telescoping.** The product of the per-operation deviations satisfies TARGET (together2) with the true
  increments:

  𝔄_sb ≤ C^{n}(log L)^{Cp} · L^{a(F_im − 1) + γ₀p⁺ + ηZ_tot − η³p_op/2} · ∏_{components M} [𝔄(M) · ∏_{α∈M} T(Q_v,κ_v) · L^{−bV_β(M) + aG(M)}],

  where each α label factor is paid at creation and refunded at most once (R38), plus the tame-erasure gains of
  Remark remtame2. The factor ∏T(Q_v, κ_v)·L^{−bV_β+aG} cancels against the right side of (finalcount).

Given G, §4 bounds each 𝔄(M) by the right side of (finalcount), and (together3) and (finalcount1) follow at γ ≤ 1/2
(§8).

**What this note already supplies towards G.**
- Every per-step bound in (G2) **except the group-D triangle steps** (§3.2–3.6).
- Every component bound **except** for a triangle with two α-atoms (§4.4).
- So G is equivalent to **(G-D)**: a treatment of the group-D configurations such that:
  - (i) the telescoped excess of all group-D steps, Σ over group-D steps of (4η + gη² + η³ − (top − q₂))₊ in exponent,
    is paid from slack elsewhere in the run, or removed by a different operation;
  - (ii) no triangle component with two α-atoms survives;
  - (iii) N1, N2, `noBetaCut` and `vineLG`_γ are preserved.

**Lean-facing form.** G replaces the hypothesis `8 * η ≤ 2 * γ - 1` of `GhostArith2/3`, `GhostMain2/4`, `G3Ex2G`,
`Flower.FinalMKStep.Pot.hmarg_of_h8` and `FinalMKChain`. Proposal: a hypothesis `GhostLowInput d γ η`, to be
discharged by the ghost-step note, delivering (G1)+(G2) at the level of the formalized stage-2 run (`UStep2.excess`
restated, plus the telescoping lemma of the assembly). Its exact shape depends on the repair of the ghost step. If that
repair keeps the per-step architecture, the minimal statement is the charged triangle
deviation with an extra factor L^{θ_s} on group-D steps, together with a global bank Σ_s θ_s ≤ Σ (banked creation
slack).

**Observations for the ghost step** (PROVED closed forms, CHECKED; not claims about a repair):
- The group-D deficit at γ ≤ 1/2 is ≤ 4η + 3η² + η³ per step. It occurs only when both α-ghost labels are within
  L^{3η+O(η²)} of the SG threshold L^{−γ+η}.
- Creation-step slack per α-pair at the top label (d = 3), from §3.2–3.5:

  | creation | slack per pair |
  |---|---|
  | α-cut (d = 3) | η − η³ (γ − η³ for d ≥ 4) |
  | Step-1 bad vine (I)/(II) | 2η − η³ |
  | Step-1 T-vine | γ + 2η − η³ |
  | triangle-created α (ΔF = 1) | ≥ γ/2 − η/2 |

  So route 1 of the planning list of open steps (creation-step slack) has a bank ≥ 4η when the ghosts come from
  T-vines, triangles, or d ≥ 4 α-cuts. It falls short by ≈ 2η–3η when both come from a d = 3 α-cut or a bad-vine removal.
- The planning list's illustrative "partial range γ > 2/5" rests on the (1 − 2γ) deficit, which does not exist at
  γ ≤ 1/2.

---------------------------------------------------------------------------------------------------------------------

## 8. Assembly at γ ≤ 1/2 (conditional on G)

With G, §4 and TARGET L2203–L2216:
- (together2) as printed;
- (together3): 𝔄_sb ≤ L^{(R−1)(4γ₀+4η+5η²)}·L^{−η⁵(ρ_sb − C₀p_op) − η³p_op/2} ≤ L^{−4η⁶(ρ_sb + p_sb)}·L^{(R−1)(d−γ−1/4−1/40)}.

This uses:
- d − γ − 1/4 − 1/40 − 4γ₀ − 4η − 5η² ≥ 0.225 − 4η − 5η² > 0 (equality case of d − γ − 4γ₀ ≥ 1/2 at d = 3, γ = 1/2);
- the shape constants for 𝒱_γ: ≤ 3 ladders and ≤ 13 atoms outside them per vine (N2 §2.4, REFEREED; TARGET L2213's
  "20" becomes 13);
- E19's factor 2.

DH23 `kqmainest2` (L1823–L1826) follows in the same way: Δ_sub ≤ Cη⁴σ, and ρ changes by O(1) per operation. So
**(finalcount1) and `kqmainest2` hold for 0 < γ ≤ 1/2, conditional on G**.

---------------------------------------------------------------------------------------------------------------------

## 9. Lean-facing hypotheses and statements (for the Lean formalization of the final count)

**Prop 9.6.**
- `FinalDecLow` := `FinalDec` with `vineLG` over `IsVineGamma γ` (`WaveTurbulence/Foundations/TVine/Defs.lean`, the
  text fixed by decision D11).
- `Prop96LowAt d γ η` := `Prop96At` with `hγ : γ ∈ Ioc 0 (1/2)` and `FinalDecLow`.
- Hypotheses: `hsm : d * η ≤ γ / 1000`, `hηs : 4 * 1440061 * η ≤ 1`. There is **no** `hsm2`.

**Arithmetic, γ ≤ 1/2 versions** (closed forms in §4; each margin ≥ c·η² or better):
- `small_facts_low`; `case2_arith_low` (X = γ, needs the sharp chain bound);
- `case3_arith_low` (margins of §4.7); `odd_arith_low` (w ≥ 1 and w = 0);
- `case5_arith_low` (γ/14 − 3η/2 − …);
- `case6_arith_low` with four sub-cases (6a)–(6d), (6d) using X₁ = −γ + 100η;
- `cycle_*_low` and `rest_ge_real_low` (§4.4, no 2γ − 1); `split_arith_low` (γ₀ = γ).

**Operation (c), sharp.** `chain_A_bound_low`: conclusion ≤ ofReal(C·(min(dδ⁻¹ρ⁻¹L^{−γ}, δ⁻¹L^{γ}) + L^{γ−1})(log L)^8).
- The L^{γ} branch needs no gap hypothesis: one free vector in a unit ball, or `atomCountLemma` Ef₂ ≤ δ⁻¹min(L^d, L^{d+1−2γ}).
- The existing `chain_A_bound` has `hγ : γ ∈ Ioo (1/2) 1`, which looks vestigial for the R⁻¹ term (the slab count is
  γ-free).

**Operation (d)+(e), new.** `opE_bound` (Lemma 4.3).
- Count: `exists_low_pair_selector_bound` (uncapped strip, needs τL ≥ 1, i.e. (V)).
- Transport: as `OpDW` (W-version of operation (d)) with the post molecule M′ ∖ S + {s–t}.
- Configuration lemma: three external cases; exclusion of "both at one atom" via `FinalDec.noBetaCut`.

**Case (6).** `case_six_low` uses `FinalDec.iota`, which is currently unused, and `betaGap`, `alphaGap`, `labRange`,
`kapVals`.

**Case (4)′.**
- `case_four_low`: the T-branch replaces `theorem_A` / `theorem_A_one` by `isTVine_of_closure` plus `vineLG`_γ plus
  `chain_A_bound` (Lemma 2.4).
- `isTVine_of_closure` is a bridge between `closureTwo` / `YRouteT k` (from the γ > 1/2 proof of case (4)) and
  `IsClosure` / `ReflTransGen Y2Step` / `IsDoubledTriangle` (from `WaveTurbulence/Foundations/TVine/Defs.lean`).
- The Q-branch is unchanged (`c4_two_vine`).

**Prop 10.4(2)′ inputs at γ ≤ 1/2.** The bodies `PairGainAt`, `SmallGapPairAt`, `MergeAt` are unchanged; new
providers for γ ≤ 1/2:
- pair gain: `coupledTriple_bound` (all γ) plus the A.3(4) reparametrization at γ ≤ 1/2 (`reparam_check.py` (R1)/(R2)
  table = the case split);
- small-gap pair: `atomCountLemma` Ef₃ plus two ball counts;
- merge: the shell count (Lemma 2.0(b)) for the same-direction case, replacing the γ > 1/2 `MergeFiberBound` annulus,
  plus Ef₂ with LG.

Then `core_split` / `prop104_two_proved` run with the low providers (the `hγ12` uses disappear).

**X-route.** `xMinus_afree_low` (PairGainAt at γ ≤ 1/2 plus Prop 10.2(2)). The arithmetic of `theorem_A_X` /
`theorem_A_X_one` must be re-checked at γ ≤ 1/2 (not done here). Mathematically the bound for X∖ℓ* is
L^{−γ₀−η/3} (§5.4).

**Ghost.** The hypothesis `GhostLowInput` (§7), an input proved elsewhere (the ghost-step note).

**Counts already in Lean** for all γ or for γ ≤ 1/2: `coupledPair_low_bound`, `exists_low_pair_selector_bound`,
`coupledTriple_bound`, `atomCountLemma`, `countLemma`, Props 10.1′, 10.2, 10.3, 10.4(1), `prop96_damaged`.

---------------------------------------------------------------------------------------------------------------------

## 10. Open remainder, risks, and what a referee should attack first

**Open.** Only G (the ghost step for γ ≤ 1/2, §7). Nothing else in this note's scope is open.

**Attack points (most fragile first):**
1. **§4.10 (6d).** The identification of P for the chain on which (e) is performed, the claim that every triple bond of
   M₁ fits Lemma 4.3's configuration, and the use of `FinalDec.iota` for simultaneously created α-atoms (Step 1,
   triangle siblings). The margin γ − 104η is the tightest Prop 9.6 margin.
2. **Lemma 4.3.** The determination of k_{ℓ_p}, k_{ℓ_q} from the post data. The window bookkeeping at s, t. The
   reduction to (basiccount01) with r = w (CHECKED symbolically only for the 6 sign patterns of a triple at p).
3. **Lemma 2.1(ii), 2.2.** The dyadic slab sums uniformly in the position of the unit balls (|x| may be large; both
   terms of the slab count are kept). Lemma 2.0(b) for far centres.
4. **Finding 1.** Whether some other route in DH23 avoids the sharp (operc) in case (2). The statement of case (2) is true
   with the sharp form either way.
5. **§3.4.** Whether GHOST's slab model (one fixed block gap; the free momentum counted by Lemma 2.0(a)) is still the
   right upper bound at γ ≤ 1/2. It is an upper bound; group D's attainment was shown by GHOST §3c for its local model.
6. **§4.8 (A2).** The identification of the T-type closure with D11's `IsClosure` in the σ = 1 case (one chain of two
   β-atoms). `IsBlock` was checked against its Lean definition
   (`WaveTurbulence/Foundations/WaveB/Molecules.lean`).

**Not re-done (cited):**
- N1–N3 and REF1–REF3 (T-vine combinatorics, Thm N, Prop 9.5′ for 𝒱_γ, Step-1 counts for T-vines);
- CASE4 Lemmas 2.1–2.4;
- GHOST §0–§5 model;
- Lean Props 10.1′, 10.2, 10.3, 10.4(1) and `prop96_damaged`.

---------------------------------------------------------------------------------------------------------------------

## 11. Files (scripts and outputs; not included in this repository)

| script | output | content |
|---|---|---|
| `ghost_low.py` | `out_ghost_low.txt` | GHOST's 36-pattern model (verbatim copy of the functions of GHOST's script `patterns.py`) on γ ∈ (0, 1/2]; closed forms of §3.4; group-D deficit vs label |
| `arith_low.py` | `out_arith_low.txt` | every exponent inequality of §3–§4 on grids of (γ, d, η, labels); expected failures (printed (operc) in case (2); case (6) without (e)); binding η/γ ratios |
| `reparam_check.py` | `out_reparam_check.txt` | sympy: A.3(4) reparametrization for all 18 + 6 sign patterns; (opere) reduction for all 6 |
| `count_low.py` | `out_count_low.txt` | brute-force lattice counts, d = 3, L ≤ 10: ratios to L^{2d}W and L^{2d}W·min(1, W/P) stay bounded (25–48 at every L). Sanity only |
