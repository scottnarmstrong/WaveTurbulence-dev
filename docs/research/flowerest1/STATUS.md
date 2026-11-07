# flowerest1 supplement: open-item tracker (wt-orch)

Supplement: SUPPLEMENT-v1.md (ddd81fe1…). Proposition 10.3 assembles the proof from the OPEN items below plus the
aggregate budget (10.3)/(10.4).

| Item | Packet | Agent | State |
|---|---|---|---|
| 6.3 marked grouped estimates and external decay | o63 | Opus | **CLOSED WITH VARIANT** (Thm 6.3′: one Lagrange extrapolation, zero L-loss; Prop 10.3′; Section 6 marks removed). Referee pending |
| 7.3 layered pinned and face estimate | o73 | Astra cx-open73 | **CLOSED WITH VARIANT** (Thm 7.3′ §21: unexcised protected objects, individual faces incl. dChild F_ch; c = 400d per incidence, total 10400d; zero lost incoherency). Referee running (ref/REFEREE-73.md) |
| 7.5 exceptional pieces, modified subpro, budget | o75 | Opus | **CLOSED WITH VARIANT** (Thm 7.5′: marked vines unspliced, 𝕄_sb connected; extra L^{(360d+16)b}, b ≤ 26P). Budget B = 9384d+416.01+26(c73+c82), which fits if c73, c82 ≤ 19,000d³ (sufficient). Lemma F covers M2 (audit of the Lean ladder box). Referee pending |
| 8.2 layered spectrally truncated chain | o82 | Astra cx-open82 | **CLOSED WITH VARIANT** (Thm 8.2′ §19: whole-kernel protected objects, signed face collections; L^{(1222d+130)P}; zero lost incoherency; M₂^{-1/18} per selected occurrence INSIDE a protected regular object). REFEREE-82: no FAIL; F2/F3 statement fixes sent to Astra |
| 10.2 weighted expansion remainders | o102 | Opus | **CLOSED** (Theorem R; absolute bounds; zero budget use). Referee pending |
| Proved lemmas 2.1–10.1 | ref | Opus referee | DONE: 21 PASS (7 after small fixes; 4.1 proof fix). Found missing items M1 → 10.3, M2 → 8.3, M4 → 10.4 |
| Lean plan | leanplan | Opus architect | running |
| 8.3 upper M₂ filters on large-gap ladders (new, referee M2) | o83 | Opus | **CLOSED** (Thm 8.3: box-robust E5 core, cost 𝔟(ψ) per filter, zero B; Lemma F verified with G1–G5; R2/R3 covered). Errata candidates: G2, G3 in T1989–1991. Referee running (ref/REFEREE-83.md) |
| 10.3 aggregate count and budget (new, referee M1) | o75 §8 | Opus | **DONE conditionally** on C7.3, C8.2, gain retention, and the E5 ladder bound |
| 10.4 derivative and dagger patterns (new, referee M4) | o104 | Opus | **REDUCED** (Thm 10.4: dRoot, dParent and † reduce to the plain items; ≤ L^{300dP}). Residual 10.4.C is absorbed by o73 Thm 7.3′ (refereed); CLOSED. Readings R1–R3 to go into v2 |
| Supplement v2 (referee fixes, restated 7.5, new items) | — | — | after o75 |

## Errata to add to the public list (after referee)
- From o83: G2 (sharp gap indicators are not admissible Poisson modulations in ladderl1new's sketch) and G3 ("bound the last rung trivially" does not factor the sum), both at T1989–1991.
- The normalization (δ/(2L^{d−1}))ⁿ → (δ/(2L^{d−γ}))ⁿ at T2264–2265 (m28, upgrade if refereed).
- The order-zero flower convention (reinterpretation, record as a deviation).

## Referee results
- REFEREE (v1 lemmas): 21 PASS, 7 after small fixes.
- REFEREE-2 (6.3′, 10.2, 7.5′): no FAIL.
  - 6.3′, Lemma A and Theorem R: PASS. Prop 10.3′: PASS, conditional on (5.1).
  - 7.5′ and Lemma F: PASS AFTER FIX (75-F1..F3, W1, C, LF, §8; sent to the o75 author). Budget: PASS,
    conditional on the contracts.
  - Ruling: v2 and Lean follow o75's non-excision route.
  - New requirements: (G-ret) gain retention for 7.3 and 8.2; (E5′) the shifted-box ladder bound (o83 Theorem K;
    REFEREE-83 pending); all contracts uniform over profiles with S^{40d,40d} norm ≤ C₁.
- REFEREE-83: PASS (one sentence fix R3(b), sent). G2/G3: one CANDIDATE EXPOSITION erratum; already filled in main's Lean (Spine/RungTotal, Spine/FibreSum).
- REFEREE-82: no FAIL. F1 (skeleton selected faces must come from 7.3 with the reciprocal kept) added to REFEREE-73's checklist; F2/F3 fixes sent.
- REFEREE-73: no FAIL. Thm 7.3′ is sufficient; the extra item F1 passes as a variant (Prop 20.1 split). Fixes routed: o73 (F2, REC, UF, P8, L19, RT, E1, PIN, C), o75 and o82 (73-W wording), o104 (Prop 7.4(a) port convention; (7.2) phases consumed).

## ALL EIGHT ITEMS CLOSED AND REFEREED, NO FAIL (2026-11-07 ~16:20 UTC). Editorial revisions in progress; SUPPLEMENT-v2 being integrated.

## ALL EIGHT ITEMS CLOSED (2026-11-07 ~15:30 UTC), pending REFEREE-82 and REFEREE-73. Next: SUPPLEMENT-v2 (the integrated complete proof).

## U-clock (premise of SUPPLEMENT-v2 §12.3)
- uclock: **CLOSED WITH VARIANT** (Theorem U-clock §4). The printed (redvine) T1954–T1957 is false (E26); an exact
  native-lower-clock identity replaces it, with the modulated Lemma 5.3 and consumption. No new L-power; B unchanged
  (21006d + 546.01 plain; 24266d + 630.01 nonplain).
  - The unweighted case is already in main's Lean (Represents.vineCase_prefix et al.).
  - Four new Lean pieces (§14) were sent to S-MARKED.
  - Referee running (ref/REFEREE-UCLOCK.md).
- => The paper-level proof of flowerest1 has no open premise, pending REFEREE-UCLOCK.
