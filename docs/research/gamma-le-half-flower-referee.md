# Referee report on the flower note (the flower supplement at 0 < γ ≤ 1/2)

## Reader's preface

- **Reviewed:** [the flower note](gamma-le-half-flower-notes.md), a line-by-line re-check at 0 < γ ≤ 1/2 of the written
  completion of TARGET's flower estimate (Prop `flowerest1`).
- **Verdict:** ACCEPT WITH REPAIRS (§4). Every PROVED and CHECKED claim survived; the repairs R1–R5 (§3) are editorial
  or precision fixes.
- **How it was checked:** the sources were read in full or at the cited lines (§1); the note's script was re-run with
  byte-identical output; the five shorter resolution notes were also read in full by a second, independent reader; and
  the referee's own script `adversarial.py` ran 2,437,103 checks (A1–A7, §1) with 0 failures.
- **Repairs:** applied in the Lean formalization and not folded into the note. The L² bank confirmed in R3 was later
  replaced by L^{3/2} in the formalization (see the [note's preface](gamma-le-half-flower-notes.md#readers-preface)).
  The inputs G-low, P96-low and VE-low, not yet proved when this report was written (§4), are proved in the
  [ghost-step note](gamma-le-half-ghost-step-notes.md), the [counting note](gamma-le-half-counting-notes.md) and the
  [T-vine blueprint note](gamma-le-half-tvine-blueprint-notes.md).
- *Provenance: independent refute-first referee report, November 2026. The referee did not write the note under
  review.* The scripts named in the text are not included in this repository.
- **Abbreviations:** as in the [note's preface](gamma-le-half-flower-notes.md#readers-preface); "the note" is the
  flower note, and S in "S Lemma 4.2" is SUPP.

## 0. Versions read

**Sources read.** Their hashes match the note's abbreviated hashes:
- T `493eef6b…76727cb`; D23 `c7e47dfa…92335475`;
- SUPP v2 `b1d6d780…2047511`; O63 `a50e0f93…`; O73 `2735f332…`; O75 `47513e35…`; O82 `3c39999c…`; O83 `91b9ed4d…`;
  O102 `772bac47…`; O104 `2d711cbd…`; U-clock `2ccd325b…`;
- the Lean file `WaveTurbulence/Foundations/Flower/FinalMKStep/Pot.lean` as of commit `29488c88`.

## 1. What I did

I did not write the work under review.

- **Read in full:** SUPP v2; the note; O75 §§2–4.7 and §11; O83 §§4.2–4.6; O82 §4, Theorem 10.1, §11 ((11.6)–(11.9))
  and §14.
- **Read at the cited lines:** T606–616, T956–977, T1326–1345, T1384–1392, T1513–1532, T1534–1540, T1668–1672,
  T2135–2220, T2295–2299, T2459–2476 and T323–327; D23 1005–1095; N3 §§0, 1.3, 2.2 and 4; N2 §2; REF2's verdicts;
  the list of open steps drawn up when the extension was planned and the planning notes for the extension (both not
  included).
- **Independent sweep of O63, O73, O102, O104 and U-clock.** A second reader, working independently of me, read these
  five notes in full, looking for γ > 1/2 uses that no token search would find. That reader was given the author's row
  list but not my conclusions. I checked each of that reader's positive findings against the files myself (§3.3).
- **Re-ran the author's script.** The output is byte-identical to the author's: 563,880 inequalities, 0 failures.
- **Adversarial script.** `adversarial.py` writes `out_adversarial.txt`: 2,437,103 checks, 0 failures. It covers:
  - (A1) every η-consequence and exponent inequality, at η on the exact boundary √η = min(1/(200d), γ/10). The author's
    grid rounds η down to a dyadic value; mine does not. It uses about 3,000 random and extreme γ ∈ (0, 1/2] and
    d = 3–12, 20, 40, 60.
  - (A2) a sympy re-derivation of O83's four relative terms, of its Step-2(c) term and of the §4.6 tail ratio.
  - (A3) F6 in closed form (hypergeometric), with a quadrature cross-check, and the window-emptiness threshold.
  - (A4) the re-cut ledger, recomputed from T2159, and the (finalcount1′) extra factor.
  - (A5) the `hmarg` algebra and the L² bank.
  - (A6) a mutation test of the author's script.
  - (A7) the budget arithmetic.

## 2. Verdicts, claim by claim

### 2.1 §1 facts and the CHECKED claim

| Claim | Verdict | Notes |
|---|---|---|
| F1–F4 | **CONFIRMED** | Elementary. A1 checks each one at the boundary η. |
| F5 (δ-slack) and its scope | **CONFIRMED** | See below. |
| F6 (D23 Lemma 6.6(2) at γ ≤ 1/2) | **CONFIRMED WITH REPAIR** | See R1. |
| F6, window emptiness | **CONFIRMED** | S = L^{2γ}(τ_*+2δ) < L once L^{1−2γ} > τ_*+2δ. The same holds for T's `lemlayer2` window L ≤ \|s\| ≤ 𝔇δL^{2γ} (T972). The only main-η use of D23 1076 is O83's (S2), and it sits inside that window. O82's uses take an auxiliary η₀ (checked by grep over all nine notes). |
| F7 | **CONFIRMED** | min(L^d, L^{d+1−2γ}) = L^{d−γ+γ₀}. A1 checks it for every γ ∈ (0,1), not only γ ≤ 1/2. |
| F8 | **CONFIRMED** | d − 5γ ≥ 1/2 and d − 4γ ≥ 1 hold with equality at d = 3, γ = 1/2. T allows equality (T2214, T2218). |
| CHECKED (563,880 / 0) | **CONFIRMED** | See below. |

**F5 scope.** The δ⁻¹ factor is absorbed once per gain in each place it is used:
- O82 (11.6) carries one factor (μ^{−p}+μ^{−1}+L^{−1}) against C^{n+1}(L^{2d}/μ)ⁿ;
- O82 §14 has one factor μ⁻¹ per unequal-layer pair, and §15 one δ⁻¹ ≤ L^{2η} per pair;
- O83 §4.6 has one factor per incoherent rung;
- O82 (4.3)/(4.9) is a scalar estimate, with one factor.

None is raised to the order n.

**The CHECKED claim.**
- My re-run of the author's script gives identical output.
- The grid is not vacuous. With γ₁ := min(1, a_γ) substituted, the author's script reports 109,226 failures. With
  γ₀ := 1 − γ, it reports 52,608.
- Editorial: the script's labels F5–F12 do not match the note's F5–F8. For example, script "F5" is O83 Step 2(a), while
  the note's F5 is the δ-slack rule.

### 2.2 §2 inputs proved elsewhere

| Item | Verdict | Notes |
|---|---|---|
| G-low | **CONFIRMED** as a well-formed input statement | It correctly includes O75's Operation-1E outer-joint ghosts (O75 L900, at most 2N_E). It correctly excludes the degree-0 re-cut halves. The "why needed" margin (2γ−1) − 4η − … < 0 is immediate. |
| P96-low | **CONFIRMED** (scope) | Matches the planned scope (DH23 Prop 9.6, cases other than (4); DH23 Prop 10.4(2) and its counting inputs; case (4)′ written in terms of the enlarged family; all at γ ≤ 1/2) and the T2192–2200 inputs O75 uses. |
| VE-low | **CONFIRMED WITH REPAIR** | See R4. |
| TV1–TV6 | **CONFIRMED** as cited | REF2 confirmed N2 items 1–5, including §2.1 (𝔍 ≲ L^{η³}) and §2.4 (≤ 13 atoms). REF3 confirmed N3's Corollary 1.16′ and Theorem 6. |
| TV7 | Status label | Only clause (6) is argued explicitly (N2 §2.3, via Lemma 8.1′, `blockchainprop` and Corollary 1.16). It is better labelled GEN. §5 does not depend on it: clause (6) is also argued directly from T1330, `disjointlem`(b) and TV2(F1). |

### 2.3 §3 audit table (75 rows)

- **Counts.** I recounted the codes: 51 V, 13 J, 3 F, 3 H, 4 N and 1 superseded, total 75. They match §0.
- **Coverage of SUPP and O75.** I read both in full and grepped O75 for every γ. Every γ-bearing line is in the table.
  - SUPP: L29, 46, 193, 222, 417, 421, 501, 509, 511, 528, 539, 544, 546, 548, 558–560, 606, 667, 715, 728, 732.
  - O75: L13, 71, 439, 499–501, 549–561, 619, 631, 868–886, 900, 921–924, 939–941.
  - Rows marked V are V. Rows marked J have correct replacement justifications (verified in §2.4 below).
- **Coverage of O63, O73, O102, O104 and U-clock** (independent full read). **No missed γ > 1/2 use.** Every comparison
  involving μ = δL^{2γ} in these notes is an upper bound (μ ≤ L²) or a lower bound (μ ≥ 1, 2 or 4/π). None uses μ ≥ L,
  2γ − 1, γ₁ = 1 or γ₀ = 1 − γ.
  - Some further uses are verbatim but missing from the lists:
    - o73 L429, L646 (the case a > r needs only μ ≥ 1), L855, 863, 873;
    - o102 L379 and L524 (covered by O102-2);
    - U-clock L759–760, which needs γ₁ − √η ≥ η⁸. That follows from √η ≤ γ/10.
  - These are harmless omissions.
- **Row errors** (I checked both in the files):
  - **O104-4** is mislabelled. O104 L811 is the dParent "added protected vertex" row (L^{20d} trivial part plus 3
    ladders, via T2297), not an excision row. It is superseded by SUPP's nonplain column at b ≤ 30P (SUPP §11), so "not
    used" stands.
  - **UC-3** gives the wrong section. Lemma U.3 is stated in U-clock §4(d) and proved in §7; §5 is Lemma U.1. Its scope
    sentence is too narrow (R4).
- **The correction to the list of open steps** (O82 L121 is the scalar Proposition 4.1) is **CONFIRMED**. So is the new
  item at O82 L608 ("using γ₁ = min(1, a_γ)").

### 2.4 §4 proofs of the changed items

| Item | Verdict | Notes |
|---|---|---|
| §4.1, O82 Prop 4.1 and Thm 10.1 | **CONFIRMED** | (4.5): D23 Lemma 6.5(2) contains no γ. (4.6): F6 with η₀. (4.7): L^{−(d−1)}. Total L^{−1+2η₀}, so (4.2) holds with γ̃₁ = 1. (4.8): M_*⁻¹ ≤ L⁻¹ ≤ L^{−2γ}. (4.9): μ⁻¹ ≤ L^{−2γ+ε} for L ≥ δ^{−1/ε}. Theorem 10.1: (10.14)–(10.15) gives L^{−a_γ+2η₀}, and the exclusion correction is μL^{−d} ≤ L^{−(d−1)}. The proposed text for L121–124 and L608 is correct for all γ ∈ (0,1). |
| §4.2, O83 Lemma R | **CONFIRMED** | A2 reproduces all four relative terms of Step 2(a) exactly, with their δ-powers, and the Step-2(c) term. min ≥ min(1, 2γ−2η) = 2γ−2η > 2γ−√η for η < 1/4. Step 2(c) gives 2γ, using dη ≤ (d−2)γ. The Step-1 absorptions reduce to L^{√η} ≥ 2c₁/(c₀δ). The new sentence for L349–352 is correct for every γ. *Editorial:* the first "required text change" (replace "(d−2)γ ≥ dη" by "dη ≤ (d−2)γ") changes nothing, since both say the same inequality. |
| §4.3, O83 §4.6 tail | **CONFIRMED** | The ratio is 32C_dδ⁻¹L^{−√η} (A2). The threshold is per rung and independent of m. The coherent-rung remark is right. |
| §4.4, O82 (11.8) | **CONFIRMED** | The margin 2γp − (γ₁ − η) = (1−γ)η holds exactly (A1). |
| §4.5, (finalcount1′) and the re-cut ledger | **CONFIRMED** | Recomputed from T2159: RHS = L^{2γ₀−η³+3η²} (ΔV_β = 1) and L^{3γ₀+5η²−η³} (ΔV_β = 0), both ≥ L^{γ₀+2η³}. Inserting F_im ≤ R′ + N_E and p⁺ ≤ 2R − 2 + N_E into (together2) gives exactly (3γ₀+5η²)N_E. *Editorial fix on (atomcountbd):* also CONFIRMED. In T's lemma the symbol r is overloaded: the number of vectors, and in the second bound a gap. O75 L879's "\|r\| ≥ L⁻¹" is a mis-citation. The bound used is the first, unconditional one. |

### 2.5 §5 Theorem 7.5′-low (the O75 §§4.1–4.7 classification for T-vines): CONFIRMED, relative to TV1–TV7 and the inputs proved elsewhere

I checked the family-specific steps where a T-vine could differ from a drawn vine:

- **(G3) Vine type depends only on internal bonds.**
  - T's block definition (T1328) is a degree condition inside an atomic group.
  - N3 §4.1's `IsTVine` is IsBlock ∧ multiplicity ≤ 2 ∧ (closure built from S's own bonds reduces by (Y2)-steps to T).
    All three clauses are internal to S.
  - O75's own Lemma 3 proof uses exactly this argument for drawn vines ("the block conditions (T1328) are degree
    conditions within the group").
  - The only way splicing can add a bond inside a survivor is a bond between the two outer joints of the chain. That is
    an HVC by definition, and 75-W1 turns its image into an HV. So no survivor changes type.
- **Lemma 2 (twists).** Twists act only at core vines, which are (I) and (II) minus (II-e) in both families (N3 §4.4
  BAD; T Prop `molecpl` read with "non-core = normal or (II-e)"). So Lemma 2 is literally the same lemma.
- **Clause (6′), the (L-b) member.**
  - N3 §2.2 gives the sources' semantics: delete I(U) and E(U°), keep the joints and the adjoint bond.
  - Removing the HV (𝕊, e*) with σ(𝕊) = 1 therefore deletes E(𝕊) ∋ f and keeps e*.
  - So the double bond {f, e*} is destroyed, and only the single bond e* remains.
  - O75 §11.1 removes this HV "exactly as T removes HV's" (ΔF = 0 through e*), which is consistent.
  - SUPP clause 7's wording "including its additional bond" means that the object includes e*. It does not mean that
    e* is deleted.
- **Lemma 5 (T-vine survivor count).**
  - N2 §2.1's three steps use only:
    - the conservation forced by ΔF = 1 (generic);
    - the piece parametrization from the joint whose bonds are fixed;
    - the fact that rungs avoid joints ("a block joint has U-degree 2").
  - None of these uses the total degree of a joint.
  - The re-cut variant uses J°'s own (c, β), which is family-free.
- **Clauses (2), (4) and (6), and Props 4.7/4.8.** The substitutions (a)–(f) of §5.1 are the only places where the family
  enters. I checked each clause's dependencies against O75's text:
  - Lemma 8.1′ in (Q);
  - Corollary 1.16′ (1)–(4) in clause (4)(a), Prop 4.7 (𝒞₂ has ΔF = 0) and Prop 4.8(δ);
  - Theorem 1.15 (F1) for `disjointlem` (i)–(ii);
  - Theorem 6(iv) for the ladder and atom counts.
  - The block VC:I+I, which is missing from DH23's `subsetvc`, is in TV3's list and is covered by TV3(3).
- **Remark (c), "O75's remark at L367 is false": CONFIRMED.** Two σ = 1 members sharing both joints are atomic groups,
  so they share the unique joint bond f. Each joint then has DV-degree 3, so a DV′ (or a T DV of two (V)'s) is not
  saturated. The remark is not used anywhere in O75.

**Caveat.** §5 is a dependency-level proof: every family dependence of a refereed O75 step is routed through a listed
T-vine fact. It inherits TV's status. The T-vine facts are proved for all sizes, but their finite bases are CHECKED by
Python only (the T-vines with at most 13 atoms).

### 2.6 §6 the "20 variables" constant: CONFIRMED WITH REPAIR

- The value 13 is right: at most 3 maximal ladders and at most 13 atoms outside them.
  - N2 §2.4 counts 3 + 2 + 3·2 + 2. N3 Theorem 6(iv) proves it for all sizes. REF2 and REF3 confirmed it.
  - The note's split into "4 two-atom pieces" gives the same total.
  - The 13 free vectors are 2 per non-ladder 2-atom piece, 3 for the core and the 2 fixed joint bonds (N2 §2.1).
- The claim that the constant enters no L-exponent of SUPP is **CONFIRMED**. The 20d in O75's (finalsbest1′) is T's
  per-ladder and per-atom allowance (L^{20dq′+20dm′}), not this per-vine constant. The constant enters only through
  ρ_fin ≥ ρ_sb − C₀p_op (T2213, O75 L497) and O83 (c2).
- **R2** concerns one side claim of §6.

### 2.7 §7 Lean-facing hypotheses

| Item | Verdict | Notes |
|---|---|---|
| §7.1, η_fl | **CONFIRMED** | Every listed consequence holds at the exact boundary (A1). |
| §7.2, the finding | **CONFIRMED** | The Lean file `Pot.lean` (commit `29488c88`) has `hW_RCp (… hmarg : 2 * min γ (1 - γ) + 4 * η ^ 2 ≤ 1 …)`. `Obj.lean:174` repeats it, and `hmarg_of_h8` is used at `Obj.lean:228`. At γ ≤ 1/2, hmarg holds iff γ ≤ 1/2 − 2η², with the exact threshold checked. It is false at γ = 1/2 for every η > 0. The docstring margin follows from hmarg using ε₀ ≤ η²/2 and 8η⁶ ≤ η²/2. T325 does single out γ = 1/2 (the Boltzmann–Grad scaling). |
| §7.2, the recommended change | **CONFIRMED WITH REPAIR** | See R3. |
| §7.3 | No mathematical claim to referee | Consistent with the planning notes for the extension (not included). The author correctly flags that shape-derived Lean constants (e.g. `hρ : rho ≤ rho' + 88`) must be re-derived from TV4. |

### 2.8 §0 and §8

- The headline (items 1–7) agrees with the verdicts above, subject to R3's wording.
- §8's statement of what is not proved is accurate and honest.
- I found **no counterexample**. Nothing in the flower layer adds a γ-restriction beyond G-low, P96-low, VE-low and TV.

## 3. Required repairs (all editorial or precision; none changes a statement's truth, an exponent or the budget)

- **R1 (F6 headline).** Replace "For every fixed γ ∈ (0, 1/2] and P > η⁻², (NTlem22) holds" with:
  > "for γ = 1/2 (D23's main branch), and for γ < 1/2 whenever P(1−2γ) ≥ 1 + a_γ − η, in particular for P > η⁻² with
  > η² ≤ (1−2γ)/(2d−1)".

  The body already says this. The headline overstates it, as does D23 L1090's word "trivial". For example, d = 3,
  γ = 0.49, η = 0.1 and P = 101 give P(1−2γ) = 2.02 < 2.94 = 1 + a_γ − η. The note uses F6 only with O82's free
  auxiliary η₀, so nothing downstream changes.
- **R2 (§6 side claim).** "Less than 20P vines contain a special node … disjoint realizations (Lemma 1)" is inaccurate.
  Lemma 1 gives disjoint **twist-active sets**. Consecutive vines share a realization node (𝔲₁ʲ = 𝔲₂^{j+1}), so the
  honest bound is ≤ 2·16P = 32P. Any O(P) suffices, and T2297(4) is unused in SUPP's route, so this is immaterial.
- **R3 (§0.6 and §7.2, the Lean survivor budget).** The change `g1E := g1 − 2·pendRC` is safe step by step:
  - `pendRC` (`FinalMKDefs/Count.lean:458`) counts present survivors that share a joint with an earlier survivor. It
    never increases, so doubling the bank only strengthens every step that lowers it.
  - The budget claim needs correcting. By `Count.lean`'s own `g1E` docstring, the total survivor charge of the Lean
    proof is L^{(1+γ₀)m}, m = N_E. With the doubled bank it becomes L^{(2+γ₀)N_E} ≤ L^{5b}, i.e. ≤ 130 per P, not
    "exactly" SUPP's 4b = 104 row.
  - The excess L^{γ₀N_E} ≤ L^{26P} is absorbed by (10.4), since 21086d + 575.2 < 10⁶d³. So the conclusion stands, but
    "the total stays inside SUPP's 4b row" should read "exceeds it by at most L^{γ₀N_E} ≤ L^{26P}, which (10.4) absorbs".
  - The note's "21086d + 601.2" is 549.12 + 52 = 601.12, rounded up. It is correct as an upper bound.
- **R4 (row UC-3 and VE-low wording).**
  - Lemma U.3 is in U-clock §4(d) and §7, not "§4–§5".
  - "family-free except Step 3" is too narrow. U-clock Step 4's core-vine induction outputs (sumintI1) expressions
    whose non-core units are T-vines, so Step 4 also rests on "T-vines are Nor units" (N1 Theorem N).
  - Since VE-low names the whole of Lemma U.3, this is a wording fix, not a gap. S Lemma 4.2 at γ ≤ 1/2 is verbatim:
    T1670 uses `lemlin`'s first, trivial bound δL^{d+2γ}, which is uniform in all modulations.
- **R5 (smaller editorial points).**
  - Row O104-4: relabel it as the dParent added-protected-vertex row, superseded by SUPP §11's nonplain column.
  - §4.2: drop the no-op replacement.
  - Align the script's F-labels with the note's.
  - Label TV7 as GEN.
  - Optionally list the extra verbatim uses of §2.3.

## 4. Overall verdict

**ACCEPT WITH REPAIRS.**

Every PROVED and CHECKED claim survives refutation. The γ ≤ 1/2 audit of SUPP v2 and O63–O104 plus U-clock is complete:
an independent full read found no missed γ > 1/2 use. All 13 changed justifications are correct, and every exponent was
re-derived, symbolically where cheap. The δ-slack is used per gain only. The O75 marked-vine classification transfers to
𝒱_enl, relative to the refereed T-vine facts. I checked the two places where T-vines could differ (internality of the
type under splicing, and the σ = 1 (L-b) member) against the sources' removal semantics. The 13-atom constant is right
and is not budget-relevant. The Lean `hmarg` finding is real and correctly diagnosed.

The repairs R1–R5 fix one overstated headline (F6), one inaccurate side count (§6), one budget sentence (§7.2, with the
conclusion intact), and some row and section labels. None of them is a GAP or a FALSE claim.

The result is conditional exactly as the note says: FL-low holds relative to G-low (OPEN, HIGH risk), P96-low, VE-low
and TV.

## 5. Files

The scripts and their outputs are not included in this repository.

| File | Content |
|---|---|
| `adversarial.py`, `out_adversarial.txt` | the referee's checks A1–A7: 2,437,103 checks, 0 failures |
| re-run output | re-run of the author's script (byte-identical to the author's output) |
