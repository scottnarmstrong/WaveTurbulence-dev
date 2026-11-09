# The flower supplement at 0 < γ ≤ 1/2

## Reader's preface

**What this note proves.** It re-checks, line by line at 0 < γ ≤ 1/2, the written completion of TARGET's flower
estimate (Prop `flowerest1`): SUPP and its resolution notes O63–O104 and U-clock, written for 1/2 < γ < 1. All 75 uses
of γ are classified (§3): none fails, 51 hold verbatim, 13 hold with a changed justification (§4), and the rest are
vine-family items, standing hypotheses, inputs proved elsewhere (§2) and one superseded step. O75's marked-vine
classification holds for the enlarged family (Theorem 7.5′-low, §5), and "20 variables per vine" becomes 13 (§6).

**How it fits the repair.** It supports [§6 of the overview](../GAMMA-LE-HALF.md#6-the-flower-estimate-for-γ--12) and
the errata entries E29–E46 (the flower completion) and E1 ([ERRATA](../ERRATA-AND-DEVIATIONS.md)). Its inputs (§2) are
proved in the [ghost-step note](gamma-le-half-ghost-step-notes.md) (G-low), the [counting note](gamma-le-half-counting-notes.md)
(P96-low), the [T-vine blueprint note](gamma-le-half-tvine-blueprint-notes.md) (VE-low) and N1–N3 (TV); the label
"HIGH risk" on G-low below records the state when this note was written.

**Where it is in Lean** (names relative to the namespace `WaveTurbulence`):
- `GammaLow.Flower.stage1MKGateLow` (`WaveTurbulence/Foundations/GammaLow/Flower/Stage1MK/B4.lean`): the marked
  stage 1 over the enlarged family.
- `GammaLow.Flower.H2.finalCountGateLowMK_holds` (`WaveTurbulence/Foundations/GammaLow/Flower/FinalMK/H2/Final.lean`):
  the marked final count at γ ≤ 1/2; the re-cut bank is in `WaveTurbulence/Foundations/GammaLow/Flower/FinalMK/H2/Bank.lean`.
- `GammaLow.Close.flower_low_closed` (`WaveTurbulence/Foundations/GammaLow/Close/Final.lean`): the flower estimate for
  0 < γ ≤ 1/2. It is glued to the γ > 1/2 proof (`layergardenFlower_v3`) into the frozen full-range statement
  `layergardenFlower_v4`.

**A correction made by the formalization.** §7.2 (confirmed by the referee's R3) proposes reserving L² per pending
re-cut. The Lean formalization showed that L² exceeds the budget L^{2m} of the marked count, and uses L^{3/2} instead,
which works for every γ (`Bank.lean` above). This corrects this note, not the papers
([ERRATA, section D](../ERRATA-AND-DEVIATIONS.md#d-formalization-issues-not-errata)). §7.2 is left as written.

**Status.** Accepted with repairs by an independent refute-first referee
([report](gamma-le-half-flower-referee.md)). The referee's repairs are listed in the report; they were applied in the
Lean formalization and are not folded into this text.

*Provenance: written and independently refereed in November 2026.* The scripts named in the text are not included in
this repository.

**Abbreviations.**
- TARGET or T: Y. Deng, Z. Hani, *Long time justification of wave turbulence theory*, arXiv:2311.10082v2; line
  numbers are lines of its TeX source.
- DH23 or D23: Y. Deng, Z. Hani, *Derivation of the wave kinetic equation: full range of scaling laws*,
  arXiv:2301.07063; line numbers as above.
- D21: Y. Deng, Z. Hani, *Full derivation of the wave kinetic equation*, arXiv:2104.11204; line numbers as above.
- N1, N2, N3: the three earlier research notes on T-vines, [`gamma-le-half-repair-1-notes.md`](gamma-le-half-repair-1-notes.md),
  [`gamma-le-half-repair-2-notes.md`](gamma-le-half-repair-2-notes.md), [`gamma-le-half-repair-3-notes.txt`](gamma-le-half-repair-3-notes.txt);
  REF1, REF2, REF3: their referee reports `gamma-le-half-repair-{1,2,3}-referee.md`.
- GHOST: [`ghost-triangle-notes.txt`](ghost-triangle-notes.txt) (the first analysis of the ghost step).
- SUPP: [`flowerest1/SUPPLEMENT-v2.md`](flowerest1/SUPPLEMENT-v2.md), the written completion of TARGET's flower
  estimate; O63, O73, O75, O82, O83, O102, O104, U-clock (UC): its resolution notes
  [`flowerest1/o63-RESOLUTION.md`](flowerest1/o63-RESOLUTION.md), …, [`flowerest1/uclock-RESOLUTION.md`](flowerest1/uclock-RESOLUTION.md).
  The line numbers cited here for U-clock (rows UC-1 to UC-3, e.g. L979) refer to a later revision of that note
  (sha256 prefix `2ccd325b`) than the snapshot in this repository; the other source files match their repository
  copies.
- ERRATA: [`../ERRATA-AND-DEVIATIONS.md`](../ERRATA-AND-DEVIATIONS.md); E1, E20, … are its entries.
- The ghost-step note, the counting note, the T-vine blueprint note: the other notes of this repair, linked above.
- FL-low: the flower layer (Prop `flowerest1`) at 0 < γ ≤ 1/2. G-low, P96-low, VE-low, TV: its inputs (§2).
- 𝒱_enl: the enlarged vine family {(I), (II), T-vines} (§5.1). GEN: N3's label for a source statement whose proof is
  unchanged when read in the enlarged family.
- R38: a ruling of the formalization project that fixes a reading of the sources; it is described where it is used
  and in ERRATA (entry E20).

## Sources (sha256)

| Name | File | sha256 |
|---|---|---|
| T (TARGET) | `WKE-Longer_times_Final_arXiv.tex` (arXiv:2311.10082v2) | `493eef6b…727cb` |
| D23 | `Revision_Submit.tex` (arXiv:2301.07063) | `c7e47dfa…35475` |
| SUPP | `flowerest1/SUPPLEMENT-v2.md` | `b1d6d780…047511` |
| O63 | `flowerest1/o63-RESOLUTION.md` | `a50e0f93…55ebc4` |
| O73 | `flowerest1/o73-RESOLUTION.md` | `2735f332…e23` |
| O75 | `flowerest1/o75-RESOLUTION.md` | `47513e35…c96d` |
| O82 | `flowerest1/o82-RESOLUTION.md` | `3c39999c…a099eff` |
| O83 | `flowerest1/o83-RESOLUTION.md` | `91b9ed4d…b869` |
| O102 | `flowerest1/o102-RESOLUTION.md` | `772bac47…55ab` |
| O104 | `flowerest1/o104-RESOLUTION.md` | `2d711cbd…c5f2` |
| UC (U-clock, premise of SUPP §12.3) | `flowerest1/uclock-RESOLUTION.md` | `2ccd325b…f20f112` |
| N1, N2, N3 | `gamma-le-half-repair-{1,2,3}-notes.{md,md,txt}` | `e7e876e5…`, `ac936aed…`, `92a9909a…` |

Line numbers "SUPP L…", "O75 L…", etc. are lines of these files. "T…" and "D23 …" are TeX lines.

**Labels.** PROVED: complete proof written here (or in a cited note and confirmed by its referee, which is named).
CHECKED: verified by `check_exponents.py` on a finite exact-arithmetic grid. SKETCH: argued, not written in full.
OPEN: not established. INPUT PROVED ELSEWHERE: a statement that this note does not prove; it is proved in another note
of this repair, named where it is used (§2).

---

## 0. Result

1. **Every use of γ in SUPP and in O63, O73, O75, O82, O83, O102, O104 and U-clock has been located and
   classified.** There are 75 rows in §3.
   - None of them fails at γ ≤ 1/2.
   - **51 hold verbatim**, in statement and proof. Two of these (SUPP S5, S27) also rest on an input proved elsewhere
     for T-vine chains.
   - **13 hold with a changed justification**, which is given and PROVED here (12 places, plus O83's own summary row).
     - Each was one of: the hypothesis 1/2 < γ < 1 inside a lemma; the formula γ₀ = 1 − γ or γ₁ = min(1, a_γ); or a
       phrase "since 2γ > 1 ≥ γ₁" or "the case γ ≥ 1/2 is the relevant one".
     - Each is replaced by γ₀ = γ, γ₁ = 2γ and, where needed, an absorption of a fixed δ⁻¹ into the existing √η, ε or
       η slack once L is large after δ (§1, F5).
   - **3 are vine-family items**, treated in §5 and §6.
   - **3 are the standing hypotheses or the γ-restriction itself** (SUPP L29, L667, L715), and **4 are replaced by
     inputs proved elsewhere** (§2).
   - 1 row is a superseded excision cost that SUPP does not use.
2. **The real γ ≤ 1/2 content of the flower is not analytic.** It is:
   - the ghost step (G-low), an INPUT PROVED ELSEWHERE (in the ghost-step note). It must also cover O75's Operation-1E
     outer-joint ghosts;
   - the T-side Stage-2 inputs (P96-low: DH23 Prop 9.6, cases other than (4), and case (4)′ written in terms of the
     enlarged family; DH23 Prop 10.4(2) and its counting inputs; all at γ ≤ 1/2) and the T-vine vine estimate (VE-low:
     the `sumint` hypotheses (i)–(iii) for T-vine charts at all sizes, and stage 1 with T-vines (splicing, class count,
     the `vineest` repairs), including the T-vine version of U-clock's modulated Lemma U.3). These are INPUTS PROVED
     ELSEWHERE, in the counting note and the T-vine blueprint note.
3. **The O75 §§4.1–4.7 marked-vine classification holds for the γ ≤ 1/2 family 𝒱_enl = {(I), (II), T-vines}.**
   - This is Theorem 7.5′-low (§5): PROVED, given the REFEREED T-vine combinatorics (N2 Lemma 8.1′, Theorem 1.15,
     N3 Cor 1.16′, Theorem 6(iv), N1/N2 Step-1 counts).
   - Every clause and every number of O75 Theorem 7.5′ is unchanged.
   - LF twists act only at core (bad) vines, so Lemma 2 is literally the same lemma in both families.
4. **The "20 variables per vine" constant (T2297) becomes 13** (§6).
   - A T-vine has at most 13 atoms, and at most 13 free vector variables, outside its at most 3 maximal ladders.
   - In SUPP's adopted (non-excision) route the constant enters no L-exponent at all. It enters only through
     "ρ changes by ≤ C₀ per removal" (T2213, O75 L497) and O83 §8 (c2).
5. **The budget is unchanged.** B = 21006d + 546.01 (plain) and 24266d + 630.01 (nonplain) are γ-free, and (10.4)
   holds as before.
6. **Lean-facing finding (§7.2).** The re-cut lemma `FinalMKStep.hW_RCp` (and `hW_RC'p`) of the γ > 1/2 Lean flower
   proof takes `hmarg : 2·min γ (1−γ) + 4η² ≤ 1`.
   - At γ = 1/2 this is false for every η > 0. At γ ≤ 1/2 it holds iff γ ≤ 1/2 − 2η².
   - The paper does not need it. O75 pays L^{3γ₀+5η²} ≤ L² per survivor, against SUPP's row "Survivors: 4b".
   - The Lean survivor budget must bank L² per pending re-cut, i.e. `g1E := g1 − 2·pendRC`. The margin then becomes
     2γ₀ + 4η² ≤ 2, which holds for every γ ∈ (0,1). The total stays inside SUPP's 4b row.
   - Without this change FL-low cannot reach γ = 1/2, which T L325 singles out.
7. **No counterexample.** The audit found no configuration in which the flower layer fails at γ ≤ 1/2. The flower
   layer adds no restriction on γ beyond its inputs proved elsewhere. If G-low closes only on (γ*, 1), FL-low inherits
   exactly that range.

---

## 1. Conventions and facts at 0 < γ ≤ 1/2

Throughout, d ≥ 3. γ₀ := min(γ, 1−γ) and γ₁ := min(2γ, 1, 2(d−1)(1−γ)) (T613). Write μ := δL^{2γ} and
a_γ := 2(d−1)(1−γ). The order of choices is SUPP L29's: γ, then η (small depending on d, γ), then P, then δ, then L.

- **F1.** γ₀ = γ and γ₁ = 2γ. PROVED.
  - *Proof.* 1 − γ ≥ 1/2 ≥ γ. Also 2(d−1)(1−γ) ≥ d − 1 ≥ 2 > 1 ≥ 2γ.
- **F2.** d − 2γ ≥ d − 1 ≥ 2 > 1 ≥ γ₁. PROVED.
- **F3.** a_γ ≥ d − 1 ≥ 2. Hence γ̃₁ := min(1, a_γ) = 1 ≥ γ₁. PROVED.
  - So every bound proved with error L^{−γ̃₁+ε} implies the one with L^{−γ₁+ε}. Minor arcs are slack.
- **F4.** 3γ₀ + 5η² ≤ 3/2 + 5η² < 2 once η² < 1/10. PROVED.
  - More generally γ₀ ≤ 1/2 for every γ ∈ (0,1). So SUPP L421 and O75 L501 never needed γ > 1/2.
- **F5 (δ-slack rule).** μ ≥ 1 and μ → ∞ as L → ∞. For every fixed ε > 0, μ⁻¹ = δ⁻¹L^{−γ₁} ≤ L^{−γ₁+ε} once
  L ≥ δ^{−1/ε}. PROVED (F1).
  - This replaces every "μ⁻¹ ≤ L^{−γ₁+ε} since 2γ > 1 ≥ γ₁".
  - **Scope.** It is used only where the factor δ⁻¹ occurs once per gain that carries its own ε (√η, η):
    - once per regular object in O82 (4.3) and (11.8);
    - once per unequal-layer pair in O82 §14;
    - once per incoherent rung in O83 §4.6.
  - It is never raised to the order n. Each use below was checked to be of this per-gain form. The threshold for L
    depends on δ, ε and fixed constants only, as SUPP L29 allows.
- **F6 (D23 Lemma 6.6(2) at γ ≤ 1/2).** For every fixed γ ∈ (0, 1/2] and P > η⁻², (NTlem22) (D23 L1081–1083) holds.
  PROVED.
  - D23's proof (L1090) says: "if γ < 1/2 then (NTlem22) is trivial due to the factor ⟨s/(δL^{2γ})⟩^{−P}, so we will
    assume γ ≥ 1/2". So γ = 1/2 is covered by D23's main branch.
  - *The trivial branch made explicit.* For γ < 1/2, bound the sum by Dλ^{4d}L^{2d}. Then
    ∫_{|s|≥L}⟨s/μ⟩^{−P}ds ≤ 2μ^P L^{1−P}/(P−1) = (2/(P−1)) δ^P L^{1−P(1−2γ)}.
  - This is ≤ L^{−a_γ+η} once P(1−2γ) ≥ 1 + a_γ.
  - For P > η⁻² this holds if η² ≤ (1−2γ)/(2d−1). In O82, which uses an auxiliary η₀ with q > η₀⁻², the condition is
    η₀² ≤ (1−2γ)/(2d−1).
  - The condition degenerates as γ ↑ 1/2. That is harmless: η may depend on γ, and at γ = 1/2 D23's main branch
    applies.
  - **Window emptiness.** In O83 Lemma R the window L < |s| ≤ S := δL^{2γ}(𝔇+2) is empty for γ < 1/2 once
    L^{1−2γ} > τ_* + 2δ, because 𝔇 = τ_*/δ. There (S2) is not even needed.
- **F7 (atomcountbd).** T2465 gives 𝔈₂ ≲ δ⁻¹min(L^d, L^{d+1−2γ}) = δ⁻¹L^{d−γ+γ₀}, for every γ ∈ (0,1). PROVED.
  - *Proof.* For γ ≤ 1/2, min = L^d = L^{d−γ+γ}. For γ > 1/2, min = L^{d+1−2γ} = L^{d−γ+(1−γ)}.
- **F8 (T's own exponent conditions, read at γ ≤ 1/2).** PROVED.
  - d − γ − 4γ₀ = d − 5γ ≥ 1/2 (T2214).
  - d − 2γ − 2γ₀ = d − 4γ ≥ 1 (T2218).
  - L^{(γ−5η)/2} ≥ L^{γ/4} needs η ≤ γ/10 (T2198).
  - The gains L^{−(γ₁−√η)g} are gains iff √η < γ₁ = 2γ.

**CHECKED.** `check_exponents.py` tests F1–F8 and every exponent inequality cited in §3 and §4, in exact rational
arithmetic.
- Grid: d = 3..12; 508 values of γ in (0, 1/2], including γ = 1/2, 1/2 − 10^{−k} and 10^{−k}; three values of η each,
  at and below η_fl(d, γ) of §7.1.
- Result: 563,880 inequalities, 0 failures (`out_check_exponents.txt`).

---

## 2. Inputs proved elsewhere

The flower layer at γ ≤ 1/2 uses four statements that it does not prove. Each is proved elsewhere: G-low in the
ghost-step note, P96-low in the counting note, VE-low in the T-vine blueprint note, and TV in N1–N3.

- **(G-low) ghost step [two α-ghosts at a triangle, erratum E20, for γ ≤ 1/2; HIGH risk].**
  - *Input proved elsewhere:* the ghost-step note (Theorems 6.1 and 7.1; §8 for the Operation-1E ghosts).
  - *Statement needed.* For 0 < γ ≤ 1/2 there is a hypothesis H_G(γ, η), satisfiable by all sufficiently small η > 0
    (depending on d, γ), such that the following holds.
  - Take T's Stage 2 (T2101–2218) with the repairs E16, E17, E19, E20, E21, E28 made during the formalization (ERRATA),
    run on any molecule 𝕄_sb that satisfies O75 Theorem 7.5′(1)–(6′) (in the γ ≤ 1/2 reading of §5), with Operation 1
    including Operation 1E.
  - Then the charged per-step deviations of all Operations 1–4, including every Operation-2 triangle containing
    already-cut degree-2 atoms (ghosts), telescope with the final-component bounds (finalcount) to give (together2) and
    (together3), with O75's extra factor L^{(3γ₀+5η²)N_E}.
  - The ghosts include the outer-joint remnants of the images 𝕎′ produced by Operation 1E (O75 L900, §11.3: at most
    2N_E more ghosts). The isolated re-cut halves are excluded: they have degree 0 and cannot be ghosts (O75 L890).
  - *γ > 1/2 version.* Ruling R38 (the charged per-step bound of erratum E20, for 1/2 < γ < 1), with
    H_G = (8η ≤ 2γ − 1), as in SUPP L29 and L732.
  - *Why it is needed.* GHOST §3c's group-D margin (2γ−1) − 4η − gη² − η³ is negative for every γ ≤ 1/2. CHECKED in
    `check_exponents.py`.
- **(P96-low) T-side final count at γ ≤ 1/2 [DH23 Prop 9.6, cases other than (4); DH23 Prop 10.4(2) and its counting
  inputs; case (4)′ written in terms of the enlarged family].**
  - *Input proved elsewhere:* the counting note.
  - *Statement needed.*
    - Prop `lgmolect` (T2192–2200): DH23 Prop 9.6 cases (1)–(6), with case (4)′, operation (e) and the ι/κ property for
      case (6), and the (3,3) odd component via Prop 10.2's L^{−3γ₀/5}.
    - The imperfect-component bound 𝔄 ≲ 1 used in T2197 and in O75 §11.4.
    - Prop 10.4(2) with "not Y-exceptional", and its counting inputs A.3(4), the small-gap pair and the merge.
  - All at γ ≤ 1/2 with γ₀ = γ and γ₁ = 2γ.
  - O75 uses these only as T's own Stage-2 steps, unchanged.
- **(VE-low) vine estimate for SG chains containing T-vines [the `sumint` hypotheses (i)–(iii) for T-vine charts at
  all sizes; stage 1 with T-vines (splicing, class count, the `vineest` repairs)].**
  - *Input proved elsewhere:* the T-vine blueprint note.
  - *Statement needed.*
    - T Prop `vineest` (T1742–1751) for chains whose normal ingredients are T-vines, in the weighted local form of SUPP
      Lemma 5.3 (5.7).
    - The modulated form, U-clock Lemma U.3: the lower-joint clock modulation e^{πiλτ_b} at cost ⟨λ⟩^{6η⁶}.
    - The class count `Stage1Counts` (iv) for T-vines.
  - Both are expected from N1 Theorem N, which makes T-vines Nor units of `sumint`, once the all-size `sumint`
    hypotheses (i)–(iii) for the piece chart (caveat C3 of REF1) and the repairs E2d, E4, E14, E24–E26 are written.
  - *Why this is all that is needed.* SUPP's additions to Lemma 5.3 (frontier factors via Lemmas 3.1–3.2, 4.1, 4.2,
    5.1, 5.2) and U-clock's additions (Step 3: replace λ₀¹ by λ₀¹+λ in the (sumintI1) expression; Step 4 only for core
    vines) are family-free.
    - Lemma 4.2 needs only `sumint`'s hypotheses.
    - LF cancellation (Lemma 5.2, U-clock Step 4) concerns core vines, which are the same (I) and (II) in both families.
- **(TV) T-vine combinatorics [REFEREED; finite bases (T-vines with at most 13 atoms) CHECKED].** Used as proved:
  - TV1: N2 Lemma 8.1′ (`vinechainlem` with DV′; N2 N6; REF2).
  - TV2: N2 Theorem 1.15 (F1)–(F6), with N3's patch of (c′) (REF2, REF3).
  - TV3: N3 Cor 1.16′ (1)–(4) under the sources' removal semantics (REF3).
  - TV4: N3 Theorem 6(iv): ≤ 3 maximal ladders and ≤ 13 atoms outside them (REF3).
  - TV5: the T-vine Step-1 counts. ΔF = 0: N1 §3.2. ΔF = 1: N2 §2.1, giving 𝔍 ≲ L^{η³} (REF1, REF2).
  - TV6: Prop 9.5′ ("a vine component is LG"; N1 §3.2, N2 §2.3).
  - TV7: `subpro` (1)–(6) for 𝒱_enl (GEN; N2 §2.3, REF2).

---

## 3. The audit table: every γ use

Verdict codes:
- **V**: holds verbatim (statement and proof).
- **J**: statement verbatim, justification changed; the new justification is given or referenced.
- **N**: replaced by an input proved elsewhere (§2).
- **H**: the standing γ hypothesis itself.
- **F**: concerns the vine family; see §5 or §6.

The "Prf" column gives the status of the γ ≤ 1/2 claim.

### 3.1 SUPP v2

| # | Place | Use | γ ≤ 1/2 | Code | Prf |
|---|---|---|---|---|---|
| S1 | L29 | "1/2<γ<1; choose 8η ≤ 2γ−1" | 0<γ≤1/2; η ≤ η_fl(d,γ) (§7.1) and H_G(γ,η) | H, N | — |
| S2 | L46 | normalization δ/(2L^{d−γ}), factor L^{(1−γ)n} substantive | no γ restriction; 1−γ ≥ 1/2 | V | PROVED |
| S3 | L193 (Lemma 4.1) | gain (C₁δ)ⁿL^{−(γ₁−√η)g} | `proplayer1` (T953) holds for all γ; the frontier insertion is γ-free | V | PROVED |
| S4 | L221–222 (Lemma 4.2) | `sumint` with Fourier-measure amplitude | `sumint` is sealed for all γ (two-branch) | V | PROVED |
| S5 | §5, Lemma 5.3 | local weighted `vineest` | γ-free; for T-vine chains | V, N (VE-low) | — |
| S6 | §6, Thm 6.3′ | common-profile extrapolation | γ-free | V | PROVED |
| S7 | L417 | vine classification, O75 §§4.1–4.7 | Theorem 7.5′-low | F | §5, PROVED given TV |
| S8 | L417 | isolated half cost L^{γ₀+2η³} | F7 | V | PROVED |
| S9 | L421 | L^{(3γ₀+5η²)N_E} ≤ L^{2N_E}, "γ₀ = 1−γ < 1/2" | γ₀ = γ ≤ 1/2, F4 | J | PROVED |
| S10 | L415–419 | R=1 components "absorbed by α/β allowances" | T's 3C₀η² ≤ ½min(γ/4, γ₀) holds for η small (O75 L924) | V | PROVED |
| S11 | L436–443 (Thm 7.3′) | L^{2γr} ≤ L^{2r}, γ₁ ≤ 1 | γ-free in the stated form | V | PROVED |
| S12 | L483 | β_v = δL^{2γ}(…), M₂^{−1/18} | γ-free | V | PROVED |
| S13 | L501 | S = δL^{2γ}M ≥ 1 for large L | true for every γ > 0 | V | PROVED |
| S14 | L509 | "d − 2γ > 1 pays this loss" | F2 | V | PROVED |
| S15 | L511 | continuum comparison, L^{−γ₁+√η} | O82 (11.8)–(11.9): rows O82-7, O82-8 | J | PROVED |
| S16 | L527–528 (8.7) | rung factor 𝖡_j | the statement is γ-free; proof rows O83-4..O83-8 | V | PROVED |
| S17 | L539 | ball radius L^{−γ+η} | γ-free | V | PROVED |
| S18 | L544 | "for d ≥ 3 and γ > 1/2 these bounds give the same gain" | holds for every γ ∈ (0,1) with dη ≤ (d−2)γ and η < 1/4 (§4.2) | J | PROVED |
| S19 | L546 | tail δ⁻²L^{2d−4γ} "smaller than the required rung bound" | required bound δ⁻¹L^{2d−4γ+√η}; holds once 32C_dδ⁻¹ ≤ L^{√η} (§4.3) | J | PROVED |
| S20 | L548 | end loss 2δ²L^{d+3γ+2} ≤ L^{20d} | γ-free | V | PROVED |
| S21 | §9 (9.1) | (πcδ)^{−a}L^{−2γa}M₂^{−a}; Lemmas 9.2–9.5 | γ-free; Lemma 9.3's top argument uses only `block_clcn` for a (CL) block (§5.2) | V | PROVED |
| S22 | §10 | Lemma 10.1, Thm 10.2, budget B, (10.4) | γ-free (O102 rows) | V | PROVED |
| S23 | L667 | §11 "1/2<γ<1" | 0<γ≤1/2, with the inputs proved elsewhere (§2) | H | — |
| S24 | L715 | "the restriction 1/2<γ<1 is substantive" | replace by: (11.1) at γ ≤ 1/2 holds relative to G-low, P96-low, VE-low, TV | H | — |
| S25 | L728 (E10/E12/E13 row) | L^{−3γ₀/5} for degree-3 odd atoms | T-side (D23 Prop 10.2) | N (P96-low) | — |
| S26 | L732 (E20/E21 row) | "Choose 8η ≤ 2γ−1" | H_G(γ, η) | N (G-low) | — |
| S27 | §12.3 | U-clock premise | rows UC-1..UC-3 | V, N (VE-low) | — |

### 3.2 O63

| # | Place | Use | Code | Prf |
|---|---|---|---|---|
| O63-1 | L78 | normalization δ/(2L^{d−γ}) | V | PROVED |
| — | L104, 267–272 | γ here is a multi-index | (not a use) | — |

O63 has no γ-dependent step. Theorem 6.3′ and Lemmas A–D are γ-free.

### 3.3 O73

| # | Place | Use | Code | Prf |
|---|---|---|---|---|
| O73-1 | L86–139, (4.1)–(4.3) | T's pair estimates T1029, T1034–1043 (all γ); "γ₁ ≤ 1, 2γ < 2 ⇒ L^{2γr}L^{(γ₁−√η)(g−g_J)} ≤ L^{3r}" | V | PROVED |
| O73-2 | L116 | "C₂ ≤ L^{√η−η}" | V | PROVED |
| O73-3 | L147, L240 | selected reciprocal (πcδ)^{−a}L^{−2γa}M₂^{−a} | V | PROVED |
| O73-4 | L390–419 | terminal pin cost L^{2γ} ≤ L² | V | PROVED |
| O73-5 | L603 | c_g = γ₁ − √η > 0 | V: needs √η < 2γ, part of η_fl (§7.1) | PROVED |
| O73-6 | L658, L812, L828 | β_v; μ^e ≤ L^{2e}; μ ≥ 1 | V | PROVED |

### 3.4 O75 (γ uses; the vine-family content is §5)

| # | Place | Use | γ ≤ 1/2 | Code | Prf |
|---|---|---|---|---|---|
| O75-1 | L13, L202, L619, L631 | L^{(3γ₀+5η²)N_E} ≤ L^{2N_E} | F4 | V | PROVED |
| O75-2 | L499–501 (finalcount1′) | "since γ₀ = 1−γ < 1/2, 3γ₀+5η² < 2" | γ₀ = γ ≤ 1/2, F4 (§4.5) | J | PROVED |
| O75-3 | L497 | "≤ 3 ladders and fewer than 20 other atoms" | ≤ 13 (TV4, §6) | F | PROVED |
| O75-4 | L539–561 (Lemma F, Step 2; superseded by O83 Thm 8.3 in SUPP) | (δL^{2γ})⁻¹ is the gain scale; C_NL^{−2d} < δ⁻¹L^{2(d−γ)−γ₁} | F5; γ-free | V | PROVED |
| O75-5 | L814 (audit note B), L900 | E20 repair "for γ > 1/2"; outer-joint ghosts covered by R38 for γ > 1/2 | G-low must include them (§2) | N | — |
| O75-6 | L879–881 (§11.3 re-cut) | L^{d−γ+γ₀+η³} choices; step deviation ≲ L^{γ₀+2η³} ≤ (excesseqn2+) | F7; inequalities §4.5 | V (editorial: see §4.5) | PROVED |
| O75-7 | L885–886 | refunds L^{(γ−5η)/2} ≥ 1, L^{γ₀+2η²−η⁵} ≥ 1 | η ≤ γ/5 | V | PROVED |
| O75-8 | L922–924 (§11.4) | 3C₀η² ≤ ½min(γ/4, γ₀) | η small depending on γ | V | PROVED |
| O75-9 | L939–941 ((E5′) check) | "2γ+1 > γ₁" | true for all γ | V | PROVED |
| O75-10 | L288 (Lemma 2(d)); SUPP L568 (Lemma 9.3) | SG top: stem exits through 𝔲₁₁ | `block_clcn` only (§5.2) | V | PROVED |

### 3.5 O82

| # | Place | Use | γ ≤ 1/2 | Code | Prf |
|---|---|---|---|---|---|
| O82-1 | L121–124 (Prop 4.1 hypotheses) | "1/2<γ<1, γ₁ = min{1, 2(d−1)(1−γ)}" | read γ̃₁ := min(1, a_γ) in (4.2), and γ₁ = min(2γ, γ̃₁) in (4.3) (§4.1) | J | PROVED |
| O82-2 | L184–193 (4.5)–(4.6) | D23 L1013–1038(2) (γ-free); D23 L1076–1086(2) | F6 | V | PROVED |
| O82-3 | L211 | "γ₁ ≤ 1 ≤ d−1" | γ̃₁ = 1 ≤ d−1 | V | PROVED |
| O82-4 | L233 | "μ⁻¹ = δ⁻¹L^{−2γ} ≤ L^{−γ₁+ε} … since 2γ > 1 ≥ γ₁" | F5 with γ₁ = 2γ; M_*⁻¹ ≤ L⁻¹ ≤ L^{−2γ} | J | PROVED |
| O82-5 | L501–608 (Thm 10.1) | error L^{−γ₁+ε} with "γ₁ = min(1, a_γ)" (L608) | holds verbatim with γ̃₁ = 1 (F3), which implies L^{−2γ+ε} | J | PROVED |
| O82-6 | L620, L918, L1299 | "d − 2γ > 1 ≥ γ₁", "a_γ ≥ γ₁" | F2, F3 | V | PROVED |
| O82-7 | L733–737 (11.8) | "2γp > 1 − η ≥ γ₁ − η"; "second term because 2γ > 1" | 2γp = 2γ − γη > 2γ − η = γ₁ − η since γ < 1; μ⁻¹ by F5 with ε = η; L⁻¹ ≤ L^{−2γ+η} (§4.4) | J | PROVED |
| O82-8 | L739–757 (11.9) | interpolation (γ₁−η)(1−t) ≥ γ₁ − 2η | γ-free | V | PROVED |
| O82-9 | L868–916 (Lemma 14.1) | equal and unequal layers; "γ₁ ≤ 2γ, a_γ" | already in γ₁ ≤ 2γ form; (14.3) by F6 | V | PROVED |
| O82-10 | L926–935 (Prop 14.2) | μ^e ≤ L^{2e}, γ₁ ≤ 1 | γ-free | V | PROVED |
| O82-11 | L945 | sharpened L^{−(γ₁−2η)}; absorb C_δ into L^{2η−η₀} | per pair: δ⁻¹L^{−2γ} ≤ L^{−2γ+2η} and C_δL^{−a_γ+η₀} ≤ L^{−2γ+2η} | V | PROVED |
| O82-12 | L1006, L1036, L1194, L1229–1230 | gains γ₁ − 100dη ≥ γ₁ − √η | 200dη ≤ √η | V | PROVED |

### 3.6 O83

| # | Place | Use | γ ≤ 1/2 | Code | Prf |
|---|---|---|---|---|---|
| O83-1 | L35, L132–148 | gains; δ³L^{4γ+2}; 2δ²L^{d+3γ+2} | γ-free | V | PROVED |
| O83-2 | L268–282 (Lemma S (S2)) | "the case γ ≥ 1/2 of that proof is the relevant one" | F6: D23's trivial branch for γ < 1/2, main branch at γ = 1/2; the window is empty for γ < 1/2 | J | PROVED |
| O83-3 | L321–323 (absorption) | first threshold L^{2γ−γ₁+√η} ≥ 2c₁/(c₀δ) | at γ ≤ 1/2 this is L^{√η} ≥ 2c₁/(c₀δ); second by F3 | V | PROVED |
| O83-4 | L330–352 (Step 2(a)) | relative terms ≤ 2^dL^{−min(1,2γ−2η)} > … "as 2γ > 1 ≥ γ₁" | min(1, 2γ−2η) = 2γ−2η > 2γ−√η = γ₁−√η (§4.2) | J | PROVED |
| O83-5 | L356–357 (Step 2(c)) | δL^{−2(d−1)γ+2dη} ≪ L^{−(γ₁−√η)} | 2(d−1)γ − 2dη > 2γ − √η (§4.2) | V | PROVED |
| O83-6 | L438–439 | "since 2γ > γ₁ − √η" | true for all γ; needs 2δ⁻¹ ≤ L^{√η} | V | PROVED |
| O83-7 | L441–444 (tail) | "once 32C_dδ⁻¹L^{−(2γ−1)} ≤ 1; here γ > 1/2 is used" | condition 32C_dδ⁻¹L^{−(2γ−γ₁+√η)} ≤ 1, which at γ ≤ 1/2 reads 32C_dδ⁻¹ ≤ L^{√η} (§4.3) | J | PROVED |
| O83-8 | L447–453 | L^{4γ}·L^{2(γ₁−√η)} ≤ L^{4+2} | γ-free | V | PROVED |
| O83-9 | L605, L661 ((c2)) | "≤ 20 non-ladder atoms per vine" | ≤ 13 (§6); bookkeeping only | F | PROVED |
| O83-10 | L646–647, L714 | summary of the γ > 1/2 uses | replace by O83-2, O83-4, O83-7 | J | — |

### 3.7 O102, O104, U-clock

| # | Place | Use | Code | Prf |
|---|---|---|---|---|
| O102-1 | L27, 132, 247, 272, 337, 472, 528 | time-integration gain 4/(πδL^{2γ}M₂) ≤ M₂⁻¹ | V | PROVED |
| O102-2 | L404–405 | (L1) δL^{2γ} ≥ 2; (L2) δC_d² ≤ 2L^{1−γ}: large L | V | PROVED |
| O104-1 | L108, 159, 234, 241 | phase definitions | V | PROVED |
| O104-2 | L613, 628–630 | C^mδ^{m+e}L^{2γe}L^eL^{−(γ₁−√η)g} ≤ (Cδ)^mL^{3e}… | V | PROVED |
| O104-3 | L807 | CδL^{2γ}·L^{γ₁−√η} ≤ L³ | V | PROVED |
| O104-4 | L811 | "L^{20d} trivial part + 3 ladders" (old excision row) | superseded by SUPP §11; not used | — |
| UC-1 | L131, 161, 194, 256, 642, 979 | normalization and phase definitions | V | PROVED |
| UC-2 | L404, 502–510, 759, 865 | (2γ+1)e ≤ 6, retained gains | V | PROVED |
| UC-3 | §4–§5 (Lemma U.3, Steps 1–4) | modulated vine estimate | family-free except Step 3's (sumintI1) reduction of non-core units | N (VE-low) | — |

**Comparison with §5 of the list of open steps drawn up when the extension was planned (not included).** All nine
rows of its table are confirmed. One correction: O82 L121 is the hypothesis of the scalar Prop 4.1, not of Thm 8.2′; it
reaches Thm 8.2′ only through the symbol γ₁ (O82-1, O82-5).

**New items, not in that table:**
- O82 L608, where Thm 10.1 silently redefines γ₁ := min(1, a_γ);
- O83 (S2), "the case γ ≥ 1/2 is relevant";
- O75 L497 and O83 (c2), the 20-atom constant;
- O75 L288 and SUPP L568 (Lemma 2(d), Lemma 9.3), which are generic;
- O75's DV remark (§5.4 (c));
- the Lean `hmarg` (§7.2).

---

## 4. Proofs of the changed items

### 4.1 O82 Prop 4.1 and Theorem 10.1 at γ ≤ 1/2 (O82-1, O82-2, O82-5). PROVED

**Claim.** For 0 < γ ≤ 1/2, O82 (4.2) holds with error L^{−γ̃₁+ε} = L^{−1+ε}. (4.3) holds with error L^{−2γ+ε}. Theorem
10.1 holds with L^{−1+ε}, hence with L^{−γ₁+ε}.

*Proof.*
- **The (4.2) and (10.6) inputs.**
  - (4.5) and (10.8)–(10.9) are D23 Lemma 6.5(2) (`NTSP`, D23 L1027–1033). Its statement and proof contain no γ.
  - (4.6), (10.10) and (14.3) are (NTlem22), which holds for every γ by F6. At γ ≤ 1/2 it gives
    L^{2d−a_γ+η₀} ≤ L^{2d−(d−1)+η₀}.
  - (4.7) and (10.11) are stationary phase, which is γ-free.
  - So the sum (4.5)+(4.6)+(4.7) is ≤ CD(W)λ^{4d}μ⁻¹L^{2d}·L^{−min(1−2η₀, a_γ−η₀, d−1)}. That is the bound with
    L^{−γ̃₁+ε} for ε ≥ 4η₀ (F3).
  - Theorem 10.1's subset expansion uses the same three scalar bounds, the factorial absorption (10.15) (γ-free), and
    the exclusion correction μL^{−d} ≤ L^{−(d−2γ)} ≤ L^{−(d−1)} (F2).
- **(4.3).**
  - Add (4.8): ≤ L^{2d}μ⁻¹·M_*⁻¹ ≤ L^{2d}μ⁻¹L⁻¹, and L⁻¹ ≤ L^{−2γ}.
  - Add (4.9): ≤ L^{2d}μ⁻¹·μ⁻¹, and μ⁻¹ = δ⁻¹L^{−2γ} ≤ L^{−2γ+ε} once L ≥ δ^{−1/ε} (F5).
  - D21 L1305–1323 is a continuum lemma, uniform in μ > 1, so the substitution δL² → δL^{2γ} is valid for every γ, as
    O82 L233 says.
  - Total: error L^{−min(γ̃₁, 2γ)+ε} = L^{−γ₁+ε}. ∎

*Required text change in O82.* L121–124: "Let d ≥ 3, 0 < γ < 1, γ̃₁ := min{1, 2(d−1)(1−γ)} and γ₁ := min{2γ, γ̃₁} (T613).
(4.2) holds with γ̃₁; (4.3) holds with γ₁." L608: "using γ̃₁ = min(1, a_γ) ≥ γ₁".

### 4.2 O83 Lemma R, Steps 1–2, at γ ≤ 1/2 (= SUPP L544; O83-2..O83-5). PROVED

**Claim.** (4.3) of O83 holds for 0 < γ ≤ 1/2, provided dη ≤ (d−2)γ, η < 1/4, and L ≥ L₀(δ, η, d).

*Proof.*

**Step 1.**
- *Region |s| ≤ L.* (S1) and (B3) give C_φc₀δ⁻¹L^{2(d−γ)}min{1, |I∩J| + (c₁/c₀)μ⁻¹}. With γ₁ = 2γ:
  (c₁/c₀)μ⁻¹ ≤ ½L^{−(γ₁−√η)} iff L^{√η} ≥ 2c₁/(c₀δ).
- *Region L < |s| ≤ S.* It is empty for γ < 1/2 and L large (F6). At γ = 1/2, D23's main branch gives O83's bound
  ⟨𝔇+2⟩^{P_η}C δ⁻¹L^{2(d−γ)}L^{−a_γ+η}. Also a_γ − η ≥ d − 1 − η > γ₁ − √η (F3).

**Step 2 (a), x-type indicators.** The four relative terms are δL^{−(d−2γ)}, 2^dδL^{−1−(d−2)γ+dη}, L^{−(d−1)(γ−η)} and
L^{1−d}.
- d − 2γ > 1 (F2).
- 1 + (d−2)γ − dη ≥ 1 if dη ≤ (d−2)γ.
- (d−1)(γ−η) ≥ 2γ − 2η, since d ≥ 3 and γ > η.
- d − 1 ≥ 2.

So each term is ≤ 2^dL^{−min(1, 2γ−2η)} = 2^dL^{−(2γ−2η)}, using 2γ ≤ 1. Since 2γ − 2η > 2γ − √η = γ₁ − √η for η < 1/4,
the term is ≤ (2K₀)⁻¹δ⁻¹L^{2(d−γ)}L^{−(γ₁−√η)} for L large.

**Step 2 (b)** is symmetric.

**Step 2 (c).** The relative size is δL^{−2(d−1)γ+2dη}. Then 2(d−1)γ − 2dη ≥ 2(d−1)γ − 2(d−2)γ = 2γ > 2γ − √η.

Summing at most K₀ terms gives (4.3). ∎

*Required text change.*
- O83 L349–352: replace "(d−2)γ ≥ dη" by "dη ≤ (d−2)γ", and replace "since min(1, 2γ−2η) > γ₁ − √η (as 2γ > 1 ≥ γ₁
  and 2η < √η)" by:
  > since min(1, 2γ−2η) > γ₁ − √η. If 2γ ≤ 1, then γ₁ = 2γ and 2η < √η. If 2γ > 1, then min(1, 2γ−2η) > 1 − √η ≥
  > γ₁ − √η, because 2γ − 1 > 0 > 2η − √η.
- O83 L278: "for γ < 1/2 this is D23's trivial case (and the window L < |s| ≤ S is empty for L large); for γ ≥ 1/2 it
  is D23's main case".

### 4.3 O83 §4.6 tail at γ ≤ 1/2 (= SUPP L546; O83-7). PROVED

The tail contributes ≤ 32C_dδ⁻²L^{2d−4γ}𝔟(ψ_v)𝔟(ψ_w) per rung.

- *Incoherent rung.* The required bound is δ⁻¹L^{2(d−γ)}L^{−(γ₁−√η)}𝔟𝔟 = δ⁻¹L^{2d−4γ+√η}𝔟𝔟, using γ₁ = 2γ. The ratio is
  32C_dδ⁻¹L^{−√η}, which is ≤ 1 for L ≥ (32C_dδ⁻¹)^{1/√η}.
- *Coherent rung.* The required bound is δ⁻¹L^{2(d−γ)}𝔟𝔟; the ratio is 32C_dδ⁻¹L^{−2γ} ≤ 1.
- The threshold is per rung and independent of m, so the product over rungs is unaffected. ∎

*Required text change.* L443–444: "once 32C_dδ⁻¹L^{−(2γ−γ₁+√η)} ≤ 1, which holds for L large for every γ ∈ (0,1)
(2γ − γ₁ ≥ 0)". Delete "here γ > 1/2 is used". O83 then uses γ > 1/2 nowhere; replace L646–647 and L714 accordingly.

### 4.4 O82 (11.8) and L233 at γ ≤ 1/2 (O82-4, O82-7). PROVED

(11.8) is: μ^{−p} + μ⁻¹ + L⁻¹ ≤ CL^{−γ₁+η}, with p = 1 − η/2 and γ₁ = 2γ.
- μ^{−p} = δ^{−p}L^{−2γ+γη} ≤ L^{−2γ+η} once δ^{−p} ≤ L^{(1−γ)η}. The margin is (1−γ)η > 0, and it is strict since
  γ < 1.
- μ⁻¹ ≤ L^{−2γ+η} once L^η ≥ δ⁻¹.
- L⁻¹ ≤ L^{−2γ+η}, since 2γ ≤ 1.

δ appears once per object (Theorem 11.3 has one error factor per object), so F5 applies. ∎

*Text change.* L737: "2γp = 2γ − γη > γ₁ − η: if γ ≤ 1/2, γ₁ = 2γ and the margin is (1−γ)η; if γ > 1/2,
2γ − γη > 1 − η ≥ γ₁ − η. The second term: μ⁻¹ = δ⁻¹L^{−2γ} ≤ L^{−γ₁+η} for L ≥ δ^{−1/η}, since 2γ ≥ γ₁."

### 4.5 O75 (finalcount1′) and the re-cut ledger at γ ≤ 1/2 (O75-2, O75-6). PROVED

**(finalcount1′).** O75 L499 is 𝔄_sb ≤ L^{(3γ₀+5η²)N_E}L^{−η⁵(ρ+p)}L^{(R−1)(4γ₀+1/10)}. It needs:
- 3γ₀ + 5η² ≤ 2 (F4) for the extra factor L^{2N_E};
- d − γ − 4γ₀ ≥ 1/2 (F8) for T's own (finalcount1).

Both hold at γ ≤ 1/2. The proof (O75 §4.7) otherwise only inserts F_im ≤ R′ + N_E and p⁺_op ≤ 2R − 2 + N_E into
(together2), whose exponents are T's γ₀-forms. These are valid for every γ, given P96-low and G-low.

**Re-cut (§11.3).**
- The choices of (k_{ℓ₁}, k_{ℓ₂}) number 𝔈₂ ≲ δ⁻¹L^{d−γ+γ₀} (F7), so the step deviation is ≲ L^{γ₀+2η³}.
- RHS of (excesseqn2+) with ΔF = 1:
  - for ΔV_β = 1 it is L^{2γ₀−η³+3η²} ≥ L^{γ₀+2η³}, iff γ₀ ≥ 3η³ − 3η²;
  - for ΔV_β = 0 it is L^{3γ₀+5η²−η³} ≥ L^{γ₀+2η³}.
- Refunds: L^{(γ−5η)/2} ≥ 1 needs η ≤ γ/5; L^{γ₀+2η²−η⁵} ≥ 1 always.
- The net charge per re-cut in (together2) is L^{3γ₀+5η²−η³} ≤ L² (F4).

All CHECKED. *Editorial fix.* O75 L879 cites "(atomcountbd) with |r| ≥ L⁻¹". The r of T's Lemma `atomcountlem` is
the number of vectors, not a gap. The bound used is the first one of (atomcountbd), 𝔈₂ ≲ δ⁻¹min(L^d, L^{d+1−2γ}), which
equals δ⁻¹L^{d−γ+γ₀} for every γ (F7). The conclusion is unchanged.

---

## 5. O75 §§4.1–4.7 for T-vines: Theorem 7.5′-low

### 5.1 Setting and statement

- **The family.** Let 0 < γ ≤ 1/2. The vine family is 𝒱_enl: vines (I), (II), and T-vines (N3 §4.3 `IsVineGamma`).
  - Vine-like objects, HV, VC and HVC are built from 𝒱_enl exactly as from (I)–(VIII).
  - DV′ (two σ = 1 members sharing both joints and nothing else; TV1) replaces DV.
  - Removal of a vine-like object uses the sources' semantics: delete I(U) and E(U°); keep the end joints and an adjoint
    bond (N3 §2.2; T2140, D23 L1775).
- **Bad, normal and core.** Bad vines are (I) and (II); normal vines are the T-vines (N3 §4.3).
  - Core vines are the bad vines except (II-e): T Prop `molecpl` read with "non-core = normal or (II-e)", N3 §4.4 BAD.
  - LF twists, `defcong` and congruence′ act only at core vines (T1466–1480, T1934–1937). So they are the same objects in
    both families.
- **Theorem 7.5′-low.** For 0 < γ ≤ 1/2, with this family, O75 Theorem 7.5′ (O75 §3) holds clause by clause:
  (1), (2), (3), (4), (5), (6), (6′), (7), (8), (9) and Lemma F, together with the §11 fixes 75-W1, F1, F2, F3.
  - The numbers are unchanged: b ≤ 26P (30P with patterns), N_E ≤ 2b, |B| ≤ 4b, |S_split| ≤ 6b.
  - The extra factors are unchanged: L^{(3γ₀+5η²)N_E} ≤ L^{2N_E} and L^{(360d+16)b}.
  - The only textual substitutions are:
    - (a) `vinechainlem` (T1930) → TV1, and DV → DV′;
    - (b) `subsetvc` (T2431, D23 L2128) → TV3;
    - (c) `disjointlem` hypotheses (i), (ii) for vine-like objects → TV2 (F1);
    - (d) T1519 / T2213 "≤ 3 ladders and < 20 atoms" → TV4 "≤ 3 ladders and ≤ 13 atoms";
    - (e) the Step-1 counts D23 L1797–1801 and T2169–2177 for a removed T-vine → TV5 (for (I) and (II) they are T's own);
    - (f) D23 Prop 9.5 → TV6.
- **Status.** PROVED below, given TV1–TV7.
  - Clause (7)'s counting consequences also use G-low and P96-low.
  - §4.3 (the Stage-1′ identity) uses VE-low. That identity is not part of the classification.

### 5.2 Facts used, and why they are family-free

- **(G1) Realization of a (CL) block** (T Prop `block_clcn`, T1345–1353; D23 L741).
  - Let 𝕍 be any (CL) block with top joint v₁ and bottom joint v₂. Then 𝔲₁ = 𝔫(v₁), 𝔲₂ = 𝔫(v₂), and the branching nodes
    of 𝒢_sk[𝕍] are the 𝔫(v), v ∈ 𝕍. Its leaves are paired among themselves.
  - Its only exits are: the parent edge of 𝔲₁ and the child 𝔲₁₁ of 𝔲₁; and the children 𝔲₂₁, 𝔲₂₂ of 𝔲₂.
  - Interior atoms have degree 4 inside 𝕍, so all four of their tree edges are bonds of 𝕍.
  - The gap of 𝕍 is ±(k_{𝔲₂₁} − k_{𝔲₂₂}) (T Def `defdiff` T1938, T2300(7)).
  - This holds for every block, of any type and either σ.
- **(G2) Chains.** Consecutive ingredients of a VC share exactly their junction; non-consecutive ingredients are
  disjoint (concatenation, T1330; `disjointlem`(b) T1341, which needs (i), (ii), supplied for T-vines by TV2 (F1)).
  - In a (CL) chain, 𝔲₁ʲ = 𝔲₂^{j+1} and 𝔲₁₁ʲ = 𝔲₂₃^{j+1} (D23 L1673). This identifies the shared joint's node and its
    in-chain child; it uses (G1) only.
- **(G3) Type is internal.** Whether a vertex set S with joints j₁, j₂ is a vine of type (I), (II) or T depends only on
  the bonds of the molecule with both ends in S.
  - For (I) and (II) this holds by the template definitions.
  - For a T-vine, `IsTVine S j₁ j₂` is IsBlock ∧ multiplicity ≤ 2 ∧ the closure (built from S's internal bonds) has a
    (Y2)-path to T (N3 §4.1).
  - So redirecting an external bond of a joint, or merging an outside region into one atom, does not change the type,
    as long as the bonds inside S are unchanged.
- **(G4) No triple bonds in 𝕄_sk** (D23 L1741(c), T2052). A triple bond of a skeleton molecule would be a collapsed
  regular object. This is family-free. T-vines have multiplicity ≤ 2 by definition.

### 5.3 Proofs, clause by clause (O75 numbering)

**§2.3–2.5 (definitions).**
- Twist-active sets 𝐀(𝕍), markedness, 𝒱, 𝒱₀, runs, survivors, 𝒲_E, 𝒞_E, B and the support hypothesis (2.3) are defined
  through (G1), T1934 and the collection 𝒞 = TV1.
- N_E ≤ Σ_{𝕎∈𝒲_E}(1 + m_𝕎) ≤ 2b_V is pure counting.
- 𝒱 contains nothing from HVs or DV′s (T1934 reads "DV" as DV′).
- Runs are (CL) VCs by `blockchainprop` (T1379), which holds for arbitrary (CL) blocks (N1 §3.2 row 3).

**Lemma 1 (disjointness of the 𝐀(𝕍)).** O75's proof uses:
- `block_clcn`(2) (G1);
- "two vines of 𝒱 are atom-disjoint or consecutive ingredients of one (CL) chain sharing one joint". This holds because
  TV1's objects are disjoint atomic groups and by (G2);
- D23 L1673 (G2);
- T1349 (descendants of 𝔲₂₁, 𝔲₂₂ are excluded from the upper realization).

None of these names a vine type. **Verbatim.**

**Lemma 2 (invariance under unmarked twists).** Only core vines are twisted. Core vines are (I) and (II) minus (II-e),
which are the same templates in both families.
- (a)'s case analysis ("for vines (II) … for Vine (I) …") therefore covers every twisted vine.
- Markedness of the other vines, including T-vines, is unchanged by Lemma 1 and (G2).
- (b), (c), (e), (f) are statements about layer counts, stem layers, pins and frontier families. They hold because the
  twist changes only 𝐀(𝕍) of a core vine (T1470–1477).
- (d) uses (G1): the flower descends from 𝔲₁₁, 𝔲₂₁ or 𝔲₂₂, and the SG gap |k_{𝔲₂₁} − k_{𝔲₂₂}| ≤ L^{−γ+η} ≤ 1 against
  high-root separation |k|/2 (SUPP Lemma 9.2). This holds for any SG (CL) block, including T-vine tops of spliced
  chains.

**Verbatim.**

**§4.3 (Stage-1′ identity, (redvine)/(redvine2) for runs).** The three observations of T1948–1950 are combinatorial
and family-free. The analytic content is SUPP Lemma 5.3 and U-clock for runs, which may contain T-vines: this is
VE-low. **INPUT PROVED ELSEWHERE** (in the T-vine blueprint note; not part of the classification).

**Lemma 3 (images of SG chains).**
- Splicing a run merges a (CL) block into one atom and redirects the other bonds (T1352(2)).
- A survivor 𝕊ᵢ keeps all its internal bonds; only its joint's external bonds are redirected to the hinge.
- By (G3), 𝕊ᵢ is a vine of the same type, including a T-vine. Its gap is inherited (T1938).
- The single-survivor HVC image 𝕊 ∪ {e*} is an HV of 𝕊, which for a T-vine is a "hyper T" (75-W1).
- Part (i) is `blockchainprop`.

**Verbatim.**

**Clause (1).** Irreducibility and `propcplmol` (T1304) are family-free. **Verbatim.**

**Clause (2).**
- 𝒞₁ is disjoint because TV1's objects are disjoint.
- |H| = q_sk by construction.
- Triple bonds lie at merged atoms (G4).
- N_E ≤ 2b, |B| ≤ 4b, and the sharing structure follow from Lemma 3.

**Verbatim.**

**Clause (3).** Degenerate non-hinge atoms are tame by conservation and ε_v ≠ 0 (T556, T564, T1309, T1314–1316). This is
family-free. **Verbatim.**

**Clause (4) (uncovered SG objects).**
- (P) holds by (G3): a vine-like object of 𝕄_sb avoiding H has the same atoms and internal bonds in 𝕄_sk, hence the
  same types and gap.
- (Q) is TV1.
- Cases (a)–(d):
  - (a) 𝕐 is a DV′ or an LG/ZG vine-like object. 𝒱₀ ⊂ SG chains, and 𝒱 takes nothing from DV′ or HV (T1934). So 𝕐 is
    intact in 𝕄_sb and disjoint from 𝒞₁ ∪ 𝒞_E ∪ H ∪ B. "Lemma `subsetvc` applies" becomes TV3:
    - (1) location (L-a)/(L-b)/(L-c);
    - (2) the list: block I, block or hyper VC:I+I, block T-vine, hyper T-vine inside a T-vine ingredient; block I
      inside a (II).
  - (b) 𝕐 is an SG HV, so 𝕐 ∈ 𝒞₁.
  - (c) m_𝕐 = 0: T2052 and D23 L1743, family-free.
  - (d) 𝕐 ∈ 𝒲_E. Paths between survivors pass through B or e*. This uses only that 𝕐 is an atomic group whose bonds are
    the ingredients' bonds and possibly e* (TV1, (G2)).

**Verbatim**, with "DV" read as DV′ and `subsetvc` as TV3.

**Clause (5) (hinge pairs).**
- At each outer joint of a run, the bonds not in the run form a pair with the run's gap. This uses `defdiff` (T1938) for
  the run as a block.
- With degree 4 there are two pairs (D23 L1741(d), T2050).
- The choice rule and 75-F1 are bookkeeping.

**Verbatim.**

**Clause (6) (hinge configuration).**
- The degree argument is family-free.
- Replacing an aligned hinge by its run gives a concatenation of family vines (U's ingredients and the runs' vines).
  This is a vine-like object of 𝕄_sk by T1330 and `disjointlem`(b), with hypotheses (i), (ii) from TV2 (F1). It is
  exactly D23 L1745–1746, which is GEN for 𝒱_enl (TV7).
- Then (Q) = TV1.

**Verbatim.**

**Clause (6′) (objects meeting B).**
- Same ingredients as (6).
- The argument "it uses bonds leaving 𝕎, while 𝕎 is an atomic group" is TV1.
- *T-vine-specific check: the (L-b) member.* An HV container (𝕊, e*) with σ(𝕊) = 1 has the sub-object (I) {j₁, j₂},
  formed by e* and the joint bond f (TV3 (L-b)).
  - Its joints are in B, so it meets B.
  - Its bond f is an 𝕊-bond, so it is in the second alternative of (6′). It is destroyed when 𝕊 is removed (f is
    deleted).
  - Note e* survives and no triple bond arises: f ∥ e* is a double bond, not a triple.

**Verbatim.**

**Lemma 4 (destruction).** Immediate, family-free. **Verbatim.**

**Lemma 5 (single SG vine removal, joints of any degree).**
- ΔF ≤ 1: interior atoms have all their bonds in 𝕊, so the rest of the old component attaches through J₁° or J₂°.
  Family-free.
- Deviation bounds:
  - for 𝕊 of type (I) or (II), T's own (D23 L1797–1801; T2169–2177);
  - for 𝕊 a T-vine, TV5.
    - N2 §2.1 (ΔF = 1): fix the two bonds at one joint (L^{d−γ+γ₀+η³}, F7); then parametrize along the 2-cut tree of
      pieces; use (basiccount01) for each 2-atom piece (with ladder rungs giving one 𝔛ⱼ⁻¹ each) and (basiccount02) for
      the core, δ⁻²L^{3(d−γ)−γ₀} = δ⁻²L^{3d−4γ}. This gives 𝔍 ≲ L^{η³} ≤ L^{γ₀−η³}, which is better than (excesseqn2+).
    - N1 §3.2 (ΔF = 0): the same piece count, with the gap restriction at one joint, gives (excesseqn2) with the two α
      labels.
  - Neither count uses deg J₁, deg J₂. Both use the "≤ 3 ladders inside 𝕊" of TV4.
  - For an HV of a T-vine (75-W1), "the count uses only the bonds of 𝕊".
- Frozen resonances at pins and faces, and the O(1) change of ladders through a joint, are family-free.

**Verbatim**, with (e) of §5.1.

**Bookkeeping (4.6).** Degree arithmetic, family-free. **Verbatim.**

**Prop 4.7 (`excessprop1`′).**
- `cnblock` (T1367) holds for arbitrary (CN) and root (CL) blocks.
- HVs give ΔF = 0 (the adjoint bond).
- 𝒞_E: Lemma 5.
- 𝒞₂ gives ΔF = 0 by TV3(3) (connectivity under sources' semantics), replacing "Lemma `subsetvc` then gives ΔF = 0
  (T2167)".

**Verbatim.**

**Prop 4.8 (`finalmol`′).**
- ε-atoms, the triple-bond clause, imperfect and perfect components are as in O75. They are family-free given (2), (3)
  and requirement (f).
- Vine components, cases (α)–(δ): (α)–(γ) use only Lemma 4, (6) and (6′). (δ) is T's own case, i.e. DH23 Prop 9.5 with
  maximal SG members of containers. For 𝒱_enl this is TV6, with TV3(4) for disjointness of maximal SG members.

**Verbatim.**

**(finalcount1′), (finalsbest2′).**
- "ρ_fin ≥ ρ_sb − C₀p_op since each removal deletes one vine with ≤ 3 ladders and < 20 other atoms": for 𝒱_enl, TV4
  gives ≤ 3 ladders and ≤ 13 other atoms. Removed sub-objects of containers are of the TV2 (F3) types, which obey the
  same bound. C₀ is unchanged.
- The numbers are those of §4.5.
- (finalsbest2′) is family-free.

**Verbatim** with 13.

**§11 fixes.**
- 75-W1 (single-survivor HV): Lemma 3(ii) and Lemma 5; also the (L-b) remark above.
- 75-F1 (designated pairs at shared joints): bookkeeping.
- 75-F2 (re-cut ledger): §4.5. The interaction with ghosts is G-low.
- 75-F3 (R = 1 components): T2197's bounds, i.e. P96-low, and F8.

All are family-free or inputs proved elsewhere.

### 5.4 Where the T-vine theory enters (summary), and three remarks

- **Inputs used.**
  - Thm 1.15: (F1) in (G2) and clauses (6), (6′); (F3) in clause (4)'s list and in the shape bound for removed
    sub-objects.
  - Cor 1.16′: clause (4)(a) (location and list), Prop 4.7 (connectivity) and Prop 4.8 (disjoint maximal members).
  - Thm 6(iv): Lemma 5 (≤ 3 ladders) and (finalcount1′) (≤ 13 atoms).
  - Lemma 8.1′: (Q), clause (2) and Lemma 1.
  - The Step-1 counts: Lemma 5.
- **Remarks.**
  - (a) **σ = 1 T-vines** (62 classes ≤ 13 atoms; N1 §3.2) are the only T-vine feature with no drawn analogue other
    than (V). They occur in clauses (4) and (6′) through DV′ and the (L-b) member; both are handled above.
  - (b) **No marked vine is twisted.** In the drawn family the marked vines could be core or normal. Here too, and only
    unmarked core vines are twisted. So the T-vine version needs no twist theory for T-vines (N1 §3.2: "T-vines are
    normal").
  - (c) **O75's remark in §4.5 (L367) is false and should be deleted.** It says "A DV is saturated … DVs are kept only for
    fidelity". For DV′ with a shared joint bond the joints have degree 3 inside it (N3 §2.2, N2 §1.7 item 4), and the
    same holds for T's DV when the two (V)'s share their joint bond. So a DV′ can occur inside a connected unsaturated
    garden molecule with R ≥ 2. The remark is not used: case (a) treats DV′ containers with the LG/ZG ones, and Prop
    4.7/4.8 handle them through TV3.

---

## 6. The "20 variables per vine" constant

**Where it occurs.**
- T2297, `flowerest1` item (4): "at most 20 such variables per vine … loss of at most L^{20d} per vine, L^{400dP} in
  total". This concerns special-node vines treated trivially outside their ladders.
- T1519 (`layervine`) and T2213 ("at most 3 ladders and no more than 20 atoms apart from these ladders").
- O75 L497 and O83 L605/L661 ((c2)).
- O104 L811 (old excision row).

**Statement for T-vines (PROVED, from TV4 and N2 §2.1).** A T-vine has at most 3 maximal ladders.
- Outside them it has at most 13 atoms (time variables): 2 joints, 3 core atoms, and at most 4 two-atom pieces (the
  degree-6 piece and at most 3 length-1 runs; N3 Thm 6 proof of (iv)).
- After fixing the 2 bonds at one joint, its decoration is parametrized by 2 free vectors per 2-atom piece and 3 for
  the core (N2 §2.1). So at most 2·4 + 3 + 2 = 13 vector variables lie outside the ladders.
- Hence the trivial treatment costs at most L^{13d} ≤ L^{20d} per vine.
- "Less than 20P vines contain a special node" holds as before: at most 8 special nodes per tree, 2P trees, and
  disjoint realizations (Lemma 1).
- **So T2297 holds verbatim for T-vines, with 20 replaced by the smaller constant 13.** Sub-objects removed in
  Operation 1 obey the same bound (TV2 (F3)).

**Role in the adopted route.** SUPP v2 does not use T2297 item (4). Special-node vines are O75's marked survivors,
and their cost is per split atom, (60d+2)|S_split| (O75 (finalsbest1′)), independent of the vine's size. The constant
enters only through "ρ changes by ≤ C₀ per operation" (T2213, O75 L497) and O83 (c2). Neither affects an L-exponent or
the budget B.

---

## 7. Lean-facing hypotheses (FL-low)

### 7.1 The η-choice of the flower layer

**Hypothesis.** η ≤ η_fl(d, γ), where √η ≤ min(1/(200d), γ/10). CHECKED.

This implies everything the flower layer needs at γ ≤ 1/2:
- η ≤ 1/40, η ≤ 1/16, 200dη ≤ √η (O82 standing; Lean `hη40`);
- η ≤ γ/10 and 5η ≤ γ (T2198 refunds; Lean `hγη : 5η ≤ γ` in `FinalMKStep/Obj.lean:174`);
- √η < 2γ = γ₁ (positivity of every gain c_g = γ₁ − √η);
- dη ≤ (d−2)γ (O83 Step 2(a)), since dγ²/100 ≤ (d−2)γ for d ≥ 3 and γ ≤ 1/2.

Additionally:
- the auxiliary η₀ of O82 §§4, 10, 14 must satisfy η₀² ≤ (1−2γ)/(2d−1) when γ < 1/2 (F6). It is not a hypothesis on η.
- T's own C₀-condition 3C₀η² ≤ ½min(γ/4, γ₀) (O75 §11.4; T2197).

Then FL-low takes the conjunction with H_G(γ, η) from G-low and the counting note's η-conditions. All L-thresholds are
of the form L ≥ L₀(d, γ, η, P, δ), as SUPP L29 allows.

### 7.2 Finding: the Lean re-cut margin fails at γ = 1/2

*[Editor's note: the Lean formalization banks L^{3/2}, not L², per pending re-cut; see the [Reader's preface](#readers-preface).]*

**Facts.** The γ > 1/2 Lean file `WaveTurbulence/Foundations/Flower/FinalMKStep/Pot.lean` (as of commit `29488c88`) has
these at lines 98–101 and 118–119:
- `hmarg_of_h8 : 8η ≤ 2γ − 1 → 2·min γ (1−γ) + 4η² ≤ 1`;
- `hW_RCp (hmarg : 2·min γ (1−γ) + 4η² ≤ 1) …`;
- the same hypothesis appears in `Obj.lean:174` (`hW_RC'p`).

The docstring (lines 8–19) explains it. The Lean model deletes the isolated re-cut half (`vinePostG`). It pays the re-cut
step, excessRHS2 = L^{γ₀−η³+η²} plus a β label L^{γ₀+2η²}, from one banked L per pending re-cut (`g1E = g1 − pendRC`).
The margin is 2γ₀ + 3η² + 8η⁶ + ε₀ − 1 ≤ 0.

**Consequence.** At γ ≤ 1/2, hmarg ⟺ γ ≤ 1/2 − 2η² (CHECKED). It is false at γ = 1/2 for every η > 0. So `hW_RCp` and
`hW_RC'p` cannot be instantiated at γ = 1/2, and FL-low would miss γ = 1/2.

**The paper is not affected.** O75 §11.3 keeps the isolated half as a component (E28). Its per-survivor charge is
L^{3γ₀+5η²−η³} ≤ L² (§4.5), which is SUPP's row "Survivors: 4b = 104P".

**Recommended Lean change.** Bank L² per pending re-cut: `g1E := g1 − 2·pendRC`.
- The margin becomes 2γ₀ + 3η² + 8η⁶ + ε₀ ≤ 2, which holds for every γ ∈ (0,1) with η ≤ 1/40 (CHECKED at γ = 1/2).
- The initial budget becomes L^{2·pendRC₀} ≤ L^{2N_E} ≤ L^{4b}, which is exactly SUPP's row "Survivors: 4b".
- If the current Lean assembly charges only L^{pendRC₀} ≤ L^{2b}, the extra L^{2b} ≤ L^{52P} still fits (10.4), which
  then reads 21086d + 601.2 < 10⁶d³ (true for every d ≥ 1).
- The fallback is the narrower bank L^{1+4η²}, whose margin 2γ₀ + 4η² ≤ 1 + 4η² holds for all γ ≤ 1/2.

This is a statement about the Lean code as read, not a Lean build. The γ > 1/2 halves are unaffected.

### 7.3 Statement carriers and family interface

- **Carriers.** These are the flower carriers listed in the planning notes for the extension (not included). They take
  S = {γ ≤ 1/2}, with no new mathematics:
  - `Flower.Cases`, `Fam.Defs`, `CompMK`, `MkAsm.Helpers`;
  - `MkDefs.Stage1MK.MarkedComponentBoundAtI`, `ProtWhole.RegularComponentBoundAtI`;
  - `FinalMKDefs.{Count,Fine}`, `FinalMKFine.Gate`, `FinalMKGarden.MainMK`;
  - `FlowerTop.CaseAssembly.FlowerCaseAt`, `FinalAssembly.CoupleHalfAt`.
  - The anchor `layergardenFlower_v4` is v3 without `1/2 < P.γ →`.
  - The analytic flower layer (Filt*, IncTop, LadFilt, FlCoef, Prot*) is CLEAN (no γ > 1/2 use) by an independent
    analysis of the Lean code in the planning notes for the extension (not included). This agrees with §3: no analytic
    γ > 1/2 use survives.
- **Marked stage 1 / FinalMK with T-vines.** Replace the template-indexed survivor and marked-vine code (V-NORMAL in
  Mk*, V5W*) by consumers of these statements:
  - TV1 (`vinechainlem′`, DV′);
  - TV2 ((F1)–(F6));
  - TV3 (Cor 1.16′ with the sources' removal semantics, including the (L-b) member);
  - TV4 (≤ 3 ladders, ≤ 13 atoms);
  - TV5 (Step-1 counts with joints of any degree);
  - (G3) (type is internal: `IsTVine` depends only on `bondsBetween` inside S).
  - Lemma 2 stays template-based: core vines only.
- **Constants derived from the drawn shapes.** Examples are the ρ-change bound `hρ : rho ≤ rho' + 88` in `hW_RCp` and
  the `L^{20d}`-type bounds. They remain valid because T-vine shape constants are smaller (13 < 20), but their proofs
  must be re-derived from TV4, not from the eight templates.
- **Ghost hypotheses.** The `h8 : 8η ≤ 2γ − 1` hypotheses in `FinalMKChain/{Chain,ChainE,Ph2}.lean` and
  `FinalMKPhase1/{Cov6,Pot1}.lean` are the E20 ghost arithmetic. They become H_G(γ, η) of G-low. `hmarg` is §7.2.

---

## 8. What is not proved here, and risks

- **INPUTS PROVED ELSEWHERE** (§2):
  - G-low (the ghost-step note; HIGH risk, critical path);
  - P96-low (the counting note);
  - VE-low (the T-vine blueprint note; including U-clock Lemma U.3 for T-vine units and the T-vine class count);
  - TV (REFEREED; its finite bases, the T-vines with at most 13 atoms, are CHECKED only).

  This note proves the flower layer *relative to* these inputs, nothing more.
- **Coverage of the audit.**
  - Read in full: SUPP v2 and O75 (and their source passages T1926–1946, T2070–2218, T2290–2302, T2455–2476,
    D23 L1005–1092).
  - Read in full at every γ-bearing passage and its section: O82 (§§4, 10, 11, 14, 15, 16, 19) and O83 (§§4.1–4.7, 8).
  - Read at every occurrence of γ, γ₀, γ₁, μ = δL^{2γ}, 1/2, and of every count or exponential-sum citation, with the
    surrounding argument: O63, O73, O102, O104, U-clock.
  - A γ > 1/2 use that mentions none of these tokens could in principle have been missed in the latter five.
    Mitigations:
    - those five notes derive their L-powers from T's and O82's estimates, which are covered;
    - an independent analysis of the Lean code for γ > 1/2 uses (in the planning notes for the extension, not
      included) found the corresponding Lean (Prot*, Filt*, FlCoef, …) CLEAN.
- **δ-slack (F5).** Each use was checked to be per gain, not per order. A referee should re-check O82 Theorem 11.3:
  its one error factor per object is (μ^{−p} + μ⁻¹ + L⁻¹), multiplied by C^{n+1}(L^{2d}/μ)ⁿ, so the δ⁻¹ is not raised to
  n.
- **F6 near γ = 1/2.** For γ < 1/2 the trivial branch of D23 Lemma 6.6(2) needs η₀ ≲ ((1−2γ)/d)^{1/2}. Constants
  therefore degenerate as γ ↑ 1/2 unless one uses D23's main branch there. D23 asserts its main branch for γ ≥ 1/2
  only; I did not check whether it also works slightly below 1/2. This is harmless for a fixed γ.
- **§5 assumes the REFEREED T-vine results exactly as stated in N2/N3.** The only point where a T-vine feature with no
  drawn analogue enters is σ = 1 (DV′ and the (L-b) member). It is treated explicitly.
- **No counterexample.** Nothing found suggests `flowerest1` fails at some γ ≤ 1/2 beyond what the ghost step (two
  α-ghosts at a triangle, erratum E20) for γ ≤ 1/2 may imply.

---

## 9. Files

The script and its output are not included in this repository.

| File | Content |
|---|---|
| `check_exponents.py` | exact-arithmetic grid check of F0–F12 and every exponent inequality of §§3–4 and §7, the `hmarg` threshold, and the GHOST group-D sign |
| `out_check_exponents.txt` | its output: 563,880 inequalities, 0 failures |
