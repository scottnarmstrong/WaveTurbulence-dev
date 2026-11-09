# Referee report on the ghost-step note: the two-α-ghost triangle (E20, group D) for all 0 < γ < 1

## Reader's preface

- **What was reviewed:** the ghost-step note, [`gamma-le-half-ghost-step-notes.md`](gamma-le-half-ghost-step-notes.md),
  which repairs the ghost step of the stage-2 counting run (erratum E20) for every 0 < γ < 1. "The note" below means it.
- **Verdict:** ACCEPT WITH REPAIRS. Three minor repairs, R1–R3 (§5); none changes the result.
- **How it was checked:** the referee re-ran all of the note's scripts and obtained byte-identical output (§2), wrote
  independent checks (an exponent model of the whole scheme, exact-arithmetic conservation checks, lattice brute-force
  counts; §3), and checked every load-bearing step by hand (§4). The repairs were applied in the Lean formalization
  and are not folded into the note's text.
- *Provenance: independent refute-first referee report, November 2026. The referee did not write the note under
  review.* The scripts named in the text are not included in this repository.
- **Abbreviations:** as in the note's preface. In addition, ERRATA is
  [`../ERRATA-AND-DEVIATIONS.md`](../ERRATA-AND-DEVIATIONS.md), and "the planning notes" are the notes drawn up when
  the extension to γ ≤ 1/2 was planned, including a list of open steps (not included).

Refute-first. I did not write the work under review.

**Short answer.** The claimed closure survives. I attacked every load-bearing step of the chain Lemma 2.1 → Lemma 6.2 →
Theorem 6.1 → Theorem 7.1, and each one holds. I found no false load-bearing step and no counterexample. I found three
defects, all minor:
- **R1.** §8 cites Lemma 2.1 for a flower configuration that the lemma, as stated, does not cover. The conclusion still
  holds, by the same conservation argument.
- **R2.** The Lean repair in §10.1 is scoped too narrowly. It is needed wherever `hH` fails, not only at γ ≤ 1/2.
- **R3.** Two entries of the §9 table are wrong: one is false by η², the other is a grid artefact.

None of these changes the result. Verdict: **ACCEPT WITH REPAIRS**.

## 1. What was reviewed

- The work is the note with its scripts and their outputs.
- Context read:
  - The list of open steps drawn up when the extension was planned (not included).
  - GHOST.
  - TARGET L1308 (Def `defdecmol`) and L2095–2218 (requirements (a)–(f), cuts, Operations 1–4, `excessprop1`, `finalmol`,
    `lgmolect`, (together2)/(together3)).
  - DH23 L1764–1803 (Prop 9.4 and its proof).
  - ERRATA E16/E17 (R29), E20 (R38) and E21.
  - O75 RESOLUTION §4.6 (Lemma 5), §4.7, §10 note B and §11.1–11.3.
  - SUPP v2 (L29, L732, L734).
  - N1 §3.2 (the T-vine Step-1 count).
  - The counting note, §0 and §3.4 (its Findings 1–3).
  - The Lean ghost step for γ > 1/2 (`GhostArith2/3.lean`, `GhostMain2/4.lean`), and `TriReal`
    (`WaveTurbulence/Foundations/FinalCount/TriDev3.lean`).

## 2. Re-runs (all by me)

| Script | Result |
|---|---|
| `grid_low.py` | output **byte-identical** to the author's `grid_low.out` |
| `scheme_check.py` | **byte-identical** |
| `lattice_check.py` | **byte-identical** |
| `sourceA_check.py` | **byte-identical** |
| the author's copies of GHOST's scripts | identical (sha256) to GHOST's originals; `patterns.py` regenerated → `patterns.out` byte-identical |

**What the author's scripts can and cannot show.**
- `scheme_check.py` is exponent arithmetic. It *assumes* the cone gain, the two-slab count and the transfers, so it
  cannot test them.
- `sourceA_check.py` is a linear-algebra check of a two-line conservation identity.
- The structural claims therefore had to be checked by hand. The new independent computations are in §3.

## 3. The referee's own adversarial checks

The code is independent of the author's. GHOST's `exps_k` is used only as a cross-check.
- `ref_check.py` → `ref_check.out`.
- `ref_lemma41.py` → `ref_lemma41.out`.

**(A) Independent exponent model of the whole scheme, for all 0 < γ < 1.**
- **Range.**
  - 147 values of γ, including 0.001, 0.4999, 0.5, 0.5001 and 0.995.
  - Three values of η: γ₀/200 (the `TriReal` maximum), γ₀/1000, and γ₀/12 (the boundary of Remark 6.3).
  - g ∈ {2, 3}, every κ combination, and a label grid that includes the critical threshold −γ₀ − 4η exactly and just
    below it.
- **Adversarial choice.** I took the one slab from the larger α-ghost window only, never from v₁/v₂'s SG label. This
  never gives a better margin than GHOST's model, and the cross-check (A′) confirms it: over 4000 random points,
  GHOST − mine ≥ −1e−15.
- **Results under `TriReal`.** Every margin is ≥ 0. The minima, divided by η:

| Step | Minimum margin / η |
|---|---|
| NC | 0.99249 |
| TR | 190.99 |
| Non-critical | 0.99249 |
| Op-1 vine, k = 0 / 1 / 2 | 2.0 / 9.0 / 4.0 |
| Op-1 VC of two double bonds, k = 0 / 1 / 2 | 3.0 / 10.0 / 5.0 |
| Op-2 creation patterns | ≥ 99.5 |

- **Prop 3.1.** Its lower bound is never violated and is attained: the minimum slack is 0.
- **At the Remark 6.3 boundary η = γ₀/12.** Every scheme margin is ≥ 0.87η, while the plain R38 group-D margin there is
  −0.17.

**(B) Group B, B = 2 at γ ≤ 1/2.** I used a 400-step grid at four (γ, η) points. The minimum is γ/2 − η/2 − η³, which is
**η² below** the "A, B = 2 value" that the note's §9 claims as a lower bound (see R3).

**(C) The Lean `arith_B2_alpha` via `lhs_ba`.** Its exponent condition is 2γ₀ − 2γ + 3η + 3η² + η³ ≤ 0. It fails at
every γ ≤ 1/2, and also on γ ∈ [0.5001, 0.5018] at η = γ₀/200. Every failure with γ > 1/2 violates `hH` (see R2).

**(D) Conservation, in exact rational arithmetic, with my own code.**
- **D1, flower chain.** An HVC chain of s ∈ {2, 3, 4} random survivor blocks plus e*, with the outer joints joined by e*
  and a common neighbour z. In all 18 cases r_z ≡ 0.
- **D2, one Op-2 step creates both ghosts.** Take the triangle (v₁, v₂, v₃), a second v₁v₂ bond and a common neighbour z.
  Then r_z is not forced to 0, and rank(r_x, r_y) = 2 on decorations. So this case is eligible and its two free gaps are
  independent, as Thm 6.1(e) needs.
- **D3, two different objects.**
  - If their far joints are joined by a double bond, r_z ≡ 0 in all 8 cases. So two objects can also force a zero gap.
  - If their far joints are open, r_z is free and r_x = r_y is attainable in all 8 cases.

**(E) Lattice two-step test** (d = 3, L ∈ {40, 48}): the creation of r_y followed by the count of a with windows Γ_x and
Γ_y.
- The NC count is ≤ #NC × (one slab), and #NC ≈ 2 × (Q_yL)³θ₀².
- TR actual / (#annulus · L³t_xt_y/θ₀) lies in 0.49–1.15.
- Actual / R38-sequential lies in 0.14–0.35. The gain is real.

**Lemma 4.1 on an explicit molecule (`ref_lemma41.py`).**
- **Molecule.** A vine (I) U′ = {y→y₂, y₂→y}, an α-atom x with charge c_x, and the later triangle (x, y, z). All
  conservation laws and unit balls are imposed, and both windows Γ_x and Γ_y are used.
- **Brute-force count of (r, y₀, a).** N / (Lemma 4.1 model) stays between 90 and 125 for L = 12…24, at both parameter
  sets: bounded, with no growth. (N / sequential) / t_U is roughly constant, so the joint gain is the factor t_U, as
  claimed.

## 4. Claim by claim

| # | Claim (the note) | Verdict |
|---|---|---|
| 1 | Lemma 2.1 (one object, two ghosts ⇒ r_z ≡ 0; r_x = −r_y) | **CONFIRMED** (the true statement is the stronger closed-set form, §4.1) |
| 2 | Cor 2.2 (a) HV/HVC joints never ghosts; (b) the proposed HV ∪ {z, w} never an Op-2 step; (c) group-D ghosts come from two steps or one Op-2 step | (a) **CONFIRMED WITH REPAIR** (R1, flower W′ with ≥ 2 survivors); (b), (c) **CONFIRMED** |
| 3 | Prop 3.1 (deficit ≤ 4η + gη² + η³, zone min label > q*) and the correction to the planning notes | **CONFIRMED** |
| 4 | Remark 3.2 (pure creation-slack banking falls short at d = 3) | **CONFIRMED** (arithmetic; not load-bearing) |
| 5 | Lemma 4.1, Remark 4.2 (count of the enlarged object) | **CONFIRMED** (not used by the final scheme) |
| 6 | Remark 4.3 (a literal merge changes the run) | SKETCH as labelled; plausible; not needed |
| 7 | Lemma 5.1 (two slabs), Lemma 5.2 (cone) | **CONFIRMED** |
| 8 | Lemma 6.2 (the later ghost's gap is free, with an alive centre) | **CONFIRMED** |
| 9 | Theorem 6.1 (★), cases (a)–(e) and margins | **CONFIRMED** |
| 10 | Remark 6.3 (constants) | **CONFIRMED** |
| 11 | Theorem 7.1 (telescoping) and "the rest of the run is unaffected" | **CONFIRMED** |
| 12 | §8 flower (Operation 1E ghosts) | **CONFIRMED WITH REPAIR** (R1) |
| 13 | §9 grid and closed-form table | Grid **CONFIRMED** (byte-identical); two table entries **FALSE/imprecise**, harmless (R3) |
| 14 | §10 Lean-facing hypotheses | **CONFIRMED WITH REPAIR** (R2) |
| 15 | §11a cross-check with the counting note, proof of its ghost lemma G | **CONFIRMED** |

### 4.1 Lemma 2.1: CONFIRMED

I attacked each hidden assumption in turn.
- **c_v = 0 on S.** It is part of TARGET Def `defdecmol` (L1308: "c_v = 0 when v has degree 4"), and M_sb = M(𝒢_sb).
  - The joints x and y have degree 4 at the removal: two U′ bonds plus xy and xz, and bonds are never created. So they
    are original degree-4 atoms.
  - Interior atoms of a vine-like object have all four bonds in it.
  - SUPP's E23 row (low-degree atoms and self-loops kept with their charges) concerns atoms of degree < 4, so it does not
    touch S.
- **Directions.** The pairs at v₁ and v₂ are SG pairs with opposite directions. This forces the triangle to be a directed
  3-cycle, so exactly one of xz, yz leaves S. Hence the flux identity is k(xz) = k(zy), which is r_z = 0.
- **z already cut.** If z is a remnant of an earlier cut (a ghost), its gap is a function of bond momenta only. The
  identity is unaffected.
- **The flower re-cut and the cut-all reading.** A re-cut remnant has degree 0 (O75 §11.3) and is never a ghost. The
  formalization uses the ghost model (R38), not the cut-all reading.
- **Explicit molecules.** The author's 34 checks, plus my D1 (18) and D3 (8), all in exact arithmetic.

**Remark (a strengthening, not a defect).** The proof never uses "one object". It uses only this:

> *S is a set of charge-0 atoms of M_sb whose only boundary bonds are xz and yz.*

D3 shows two *different* objects can produce such an S, and then the triangle is again ineligible. Stating the lemma in
this closed-set form is what R1 needs.

### 4.2 Cor 2.2: (b), (c) CONFIRMED; (a) CONFIRMED WITH REPAIR

- **(a)** is correct for TARGET's HV/HVC: the adjoint VC is removed in one step, so Lemma 2.1 applies. It is also correct
  for the flower's single-survivor W′ = 𝕊 ∪ {e*} (O75 §11.1).
- **The gap in (a).** For an HVC W′ with s ≥ 2 survivors, O75 §11.1 removes the survivors "one at a time, and e*
  remains". The two outer joints are then created at *different* steps, so Lemma 2.1 as stated does not apply. §8
  nevertheless cites Cor 2.2(a) for "the HV W′".
- **Why the conclusion still holds (R1).** Either of two arguments suffices.
  1. The closed-set argument gives r_z ≡ 0 for the whole chain. My D1 checks this in exact arithmetic for
     s ∈ {2, 3, 4}.
  2. By O75 §11.3, every removal after the first in a chain re-cuts a remnant, so ΔF = 1, and its fresh outer joint is
     β. A triangle at the two outer joints is then group C, not D.
- **(c)** is correct. D2 shows the same-Op-2-step case is genuinely eligible, with two independent free gap vectors.

### 4.3 Prop 3.1: CONFIRMED

- **Re-derivation.** RHS = −η³ − γ − 3η − q_x − q_y − γ₀ − gη² + (κ_x + κ_y)η. The count is γ + s(ρ), with
  Δχ = m − 1 − |N| = −1 for both g = 2 and g = 3.
- **Margin.** For ρ ≥ −2γ, margin ≥ −min(q_x, q_y) − γ₀ − 3η − gη² − η³ + κη. This needs only ρ ≥ max(q_x, q_y), which
  the ghost windows themselves supply. My (A) uses exactly this adversarial ρ and finds the bound attained.
- **The correction to the planning notes is right.** GHOST §3c's own last line already says "group D fails (margin
  −4η)" at γ ≤ 1/2. The planning notes substituted the γ > 1/2 closed form. The counting note, §3.4, agrees
  independently.

### 4.4 Remark 3.2: CONFIRMED (not load-bearing)

- The vine creation margin is −γ + 3η + (d−2)κη − (d−2)q − η³, which is 2η − η³ at the top label for d = 3.
- The VC of two double bonds has margin 3η − (d−3)q − η³ for q ≥ −2γ, which is 3η − η³ at d = 3, constant in q.
- So the shortfall arithmetic holds as stated.

### 4.5 Lemma 4.1 and Remark 4.2: CONFIRMED (not used by the final scheme)

- **Lemma 4.1.**
  - Δχ = −(2m_U − 2) − 3 + m_U = −(m_U + 1).
  - The exponent is dq_U + 3γ + s_x + s_U.
  - The margin is (d−1)γ − γ₀ − (d−2)η − 2η² − η³. Every step re-derived.
  - **The key point is legitimate.** Γ_y is a window of M_pre, y is deleted, and Γ_y = 2⟨y₀, r⟩ + f(a, r). So Γ_y is a
    genuine slab on y₀.
  - `ref_lemma41.py` confirms the count on an explicit molecule (§3).
- **Remark 4.2.** Δχ = −(m_U + 2), and the margin is dγ − 2γ₀ − (d+2)η − 4η² − η³. Re-derived.

### 4.6 Lemmas 5.1, 5.2: CONFIRMED

- **Lemma 5.1.**
  - The proofs are correct: the disjoint 1/L-cubes lie in K⁺, and the area of the intersection of two strips is
    4T₁T₂/sin θ.
  - **Cosmetic.** In Thm 6.1(b), t_x = δ⁻¹L^{−2γ}/(2|c_x|) ≥ ½L^{−γ−η}. So "t ≥ 1/L" needs L^{1−γ−η} ≥ 2. This holds for
    L ≥ L₀ under `TriReal`, since 1 − γ − η ≥ 199η. §10's "γ + η ≤ 1" should say this, or read "γ + η < 1".
- **Lemma 5.2.** Correct. The constant observed in my (E) is about 2.

### 4.7 Lemma 6.2: CONFIRMED

- **(i).** α-atoms arise only at ΔF = 0 Op-1/1E removals and in Op 2.
  - Op 3 runs after all of Op 2 (TARGET L2142 order).
  - R29's skipped triangles have their v₁, v₂ cut in Op 3.
  - Component-creating removals make β joints.
- **(ii).** I checked that every α-creating count fixes the gap first, then bounds the rest uniformly.
  - DH23 L1797–1801 fixes (x₀, y₀) at one joint with L^d(RL)^d, and the rest is uniform in r. The same holds for the VC
    of two double bonds.
  - For T-vines, N1 §3.2 says "joint pair L^d(RL)^d; … r-linear cross terms only shift windows".
  - Flower Lemma 5 (O75 §4.6) lists among its inputs "(ii) the gap restriction at one joint".
  - **Flower subtlety I checked.** A removal whose gap is already fixed by a previously cut joint is a re-cut. It has
    ΔF = 1, so its fresh joint is β. Hence every α-creating 1E removal has both joints fresh and a free gap. The note
    should say so in §8 (part of R1).
  - **Robustness.** If conservation forced r_y = ±c_x, the count at s(P) would not sum r_y freely. The cone bound would
    still be a valid upper bound, because the cone count is ≥ 1 (Q_yθ₀L ≥ 1). So (★) at s(P) does not depend on r_y
    being genuinely free.
  - The κ_y = 0 requirement for critical pairs excludes the ball case.
- **(iii).** x is never re-cut and is deleted only at tri(P) > s(P), so c_x is a current parameter at s(P). This is not
  a dead-hit situation (erratum E21).

### 4.8 Theorem 6.1: CONFIRMED

- **(a) Monotonicity.** I checked the sup-over-parameters subtlety.
  - After tri(P), (f′) constrains deleted data, just as (f) does. The post count is sup over current parameters of
    decorations inherited from M_sb-decorations in the class, so A_pre ≤ I·A_post holds within each class.
  - The only centre used inside a count is c_x at s(P), and it is alive.
  - Prop 9.6 and Op 5 are upper bounds, so a further restriction only lowers them.
- **(b) TR.** Γ_x and Γ_y are two of the B − 1 = 2 independent block relations.
  - For g = 2 the blocks are x, y and the post component of z; for g = 3 they are the three ghosts.
  - The margin 2γ − γ₀ − 9η − gη² − η³ is label-free. Re-derived.
- **(c), (d), (e).** Re-derived. My (A) reproduces every minimum (§3).
  - The non-critical infimum is η − gη² − η³, approached as the minimum label → (−γ₀ − 4η)⁻. Thm 6.1(d) states this
    correctly; the §9 figure "≥ 2.69" is a grid artefact (R3).
- **Two facts the note uses implicitly.** I checked both.
  1. A group-D step creates no α-atom (#new α = |N| − m = 0). So ν^tri and ν^cre are never both nonzero at one step.
  2. Each ghost lies in exactly one triangle, so ν^tri ≤ 1 and ν^cre ≤ 2.

### 4.9 Remark 6.3, Theorem 7.1, the run unchanged: CONFIRMED

- **Remark 6.3.** The constraints are correct. My (A) at η = γ₀/12 confirms them.
- **Theorem 7.1.** The telescoping is a counting identity over the NC critical pairs.
- **The run unchanged.** (f′) enters no rule of the run, so `subpro`, Cor 1.16′, `finalmol`, `excessprop1`(3), F_im ≤ R,
  p⁺_op and Z_tot are literally those of R38's run. The cost is a factor 2^{#critical} ≤ 2^{n_sb}, which is absorbed in
  C₀^{n_sb}.
- **Lean engineering cost (not a mathematical gap).** The assembly must carry the (f′) bits and the maps s(P) and
  tri(P) as specification data, so that the creation-step lemma receives its cone hypothesis. §10.3 says so.

### 4.10 §10 Lean-facing hypotheses: CONFIRMED WITH REPAIR (R2)

- **Coverage of `hH`.** Every `hH` hypothesis in the Lean ghost step for γ > 1/2 is covered by §10.1:
  - `arith_P5_alpha2`, `arith_B2_alpha`, `arith_B2_beta`;
  - the wrappers `leaf_P5_alpha2`, `leaf_B2_alpha`, `leaf_B2_beta`, `final_B2`, `triangle_excess_ghost`.
  - Every other lemma there assumes only `TriReal`, which has no γ > 1/2 hypothesis, so it already holds for all γ.
- **`arith_B2_beta`.** The re-proof with `min γ (1-γ) ≤ γ` works for **all** γ. It needs
  η² − γ/2 + η/2 + η³ ≤ 0, which follows from γ ≥ 200η.
- **`arith_B2_alpha` (R2).** The `lhs_ba` count fails exactly where 2γ₀ − 2γ + 3η + 3η² + η³ > 0.
  - That is every γ ≤ 1/2, **and** a band just above 1/2 where `hH` fails (my (C): γ ∈ (0.5, 0.5018] at η = γ₀/200).
  - So once `η₀ ≤ (2γ − 1)/8` is deleted, the ghost-label slab (`card_slabF_nu`) must be used **whenever `hH` fails**
    (simplest: for all γ), not only "at γ ≤ 1/2" as written.
  - Its margin (d−1)(γ − η) − γ₀ − 2η² − η³ is positive for every γ ∈ (0, 1).
- **Other items.** The (T-TR), (T-NC) and `hcone` forms are mutually consistent: sin² ≥ θ₀² versus sin² < θ₀², with
  θ₀² = L^{−12η}.

## 5. Repairs required (none changes the result)

- **R1 (§2 and §8, flower).**
  - State Lemma 2.1 in its closed-set form: S is a set of charge-0 atoms of M_sb whose only boundary bonds are xz and yz.
  - Use it in §8 for an HVC W′ with s ≥ 2 survivors, whose outer joints are created at different steps. Alternatively,
    cite O75 §11.3: the later outer joint is β.
  - Add to §8 that α-creating 1E removals have both joints fresh, since a removal with a re-cut has ΔF = 1. So their gap
    is free, as Thm 6.1(e) needs.
- **R2 (§10.1).** For `arith_B2_alpha`, replace "At γ ≤ 1/2" by "whenever 8η > 2γ − 1, in particular for all γ ≤ 1/2".
  Simplest is to use the ghost-label slab for all γ. Also make §10's "γ + η ≤ 1" read "γ + η < 1 (L ≥ L₀)".
- **R3 (§9 table).**
  - Group B, B = 2 at γ ≤ 1/2 is (d−1)(γ−η) − 3γ/2 + 3η/2 − η³, which is γ/2 − η/2 − η³ at d = 3. That is η² *below*
    the A, B = 2 value, so "≥ the A, B = 2 value" is false. The closed-form check skipped these patterns, so they are not
    among the "165/165". The value is still positive.
  - Group D non-critical: replace "≥ 2.69η" by "> η − gη² − η³ (infimum)".

## 6. Inputs taken as given (not re-proved here; the note marks them INPUT)

- I1, GHOST's Op-2 model.
- I2, the DH23/N1/O75 Op-1 counts. The counting note's Findings 1 and 2 concern Prop 9.6 operations (c)/(e), not
  these counts.
- I3, R29, R38 and E21.
- CompBeta.
- `finalmol` in the Lean assembly of the final count, which is combinatorial.
- Prop 9.6 at γ ≤ 1/2 (the counting note).
- I4 in the flower setting. I spot-checked it: SUPP's only charge-related deviation, E23, concerns atoms of degree < 4.

## 7. Files

The scripts and their outputs are not included in this repository. The re-runs of the author's scripts (§2) gave
outputs byte-identical to the author's.

| File | Content |
|---|---|
| `ref_check.py` → `ref_check.out` | checks (A)–(E) of §3 |
| `ref_lemma41.py` → `ref_lemma41.out` | the explicit-molecule brute force of Lemma 4.1 |

## 8. Overall verdict: **ACCEPT WITH REPAIRS**

**Reasons.**
- **Lemma 2.1 is correct.** It is momentum conservation over a closed set of charge-0 atoms. It makes the
  one-object configuration proposed for this route (HV ∪ {z, w}) never eligible.
- **The NC/TR scheme pays the deficit, and its size is right.** For γ ≤ 1/2 the deficit is 4η + O(η²), independently
  re-derived and agreeing with the counting note.
  - At TR pairs, the two energy windows already used in GHOST's block model (B − 1 = 2) give a margin
    2γ − γ₀ − 9η − ….
  - At NC pairs, a transfer of L^{5η} is funded by a cone restriction of aperture L^{−6η} at the later ghost's creation.
    That restriction is legitimate: the gap there is summed with a uniform remainder, the centre is alive, and the bound
    is valid even when the gap is forced.
  - The transfers telescope exactly.
- **The run is unchanged.** So `subpro`, Cor 1.16′, `finalmol` and the budgets of (together2)/(together3) carry over
  verbatim.
- **Every computation reproduces.** The author's scripts re-run byte-identically. My independent exponent model,
  conservation algebra and lattice brute-force tests all agree with the stated margins over 0 < γ < 1 under `TriReal`
  alone.
- **The repairs are small.** R1 is a citation and statement repair in the flower section. R2 widens a Lean instruction so
  that `hH` can actually be deleted. R3 corrects two table entries that are η-small and harmless. None affects the
  per-step statement (★), its telescoping, or the Lean-facing hypothesis set (`TriReal` only, no `hH`).
