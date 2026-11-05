# B2.1 `regularAsymptotics`: the RA2 / RA1-TREES / RA1-couples chain (preliminary audit)

Auditor: `wt-orch`, refute-first. Date: 2026-11-04 17:20 UTC. Status: **preliminary**. The composed proof does not
exist yet; the final type audit runs on it once it does.

## Pins

| piece | owner | location | pin (17:14 UTC) |
|---|---|---|---|
| RA2 REGREF | wt-torus | `/home/scott/wt-scratch/regref` | 53 files, digest `0f493cab6c68` |
| RA1-TREES | wt-l2s | `/home/scott/wt-scratch/ra1-trees` (+ `Foundations/RegAsymp/Tree*` on `w/wke-l2s`) | 1507 files, digest `ab87705855a2` |
| RA1 couples | wt-ansob, then Sonnet | `/home/scott/wt-scratch/regasymp` (+ 8 Foundations files on `w/bproc`) | being rebuilt on snapshot 9 |

`regref/SHA256SUMS` fails on `OBLIGATIONS.md` only. That file was restated for F80 after the sums were written, and
`OBLIGATIONS.pre-F80.md` keeps the old text.

## Finding C-1: the chain does not compose against the frozen B1

- **All three pieces were built against snapshot 7/8's B1.**
  - Their `WaveBDraft/System.lean` is `59365906…` (snapshots 7 and 8).
  - The frozen B1 (`w/freeze-b1`, D7) is snapshot 9, with `System.lean` `cc53aad3…`.
  - The only difference is the `XNorm` guard (F80), so `XNorm`, `XNormRestr` and everything built on them are
    different constants.
- **Each piece's own exact-type check ran against that same B1.**
  - RA2's `check/typeaudit.log` ("Expr-equal to the pinned B2.1"), RA1-TREES' `TYPE-AUDIT.md` and RA1 couples'
    `check-exact-f80.sh` all compare inside environments whose B1 is `59365906`.
  - So none of them shows equality with the B2.1 anchor on `w/freeze-b2`.
  - INCOH-INST had the same issue. There my control 2 confirmed that a snapshot-8 build fails the snapshot-9 type audit
    at `XNorm` (`INCOH-INST-snap9.md`).
- **RA2's Lean obligation and RA1's export are different statements.**
  - RA2's Lean obligation `RA1Couple` (`src/RegrefDraft/Obligations.lean`) is still the snapshot-8 form, with the
    remainder in B2's `XNormRestr`.
  - RA1 couples proves `RA1CoupleF80`, with the remainder in the landed `Fourier.mixedRestrictionNorm`.
  - A bridge `RA1CoupleF80 → RA1Couple` is needed. It should be short (`XNormRestr ≤ mixedRestrictionNorm`, RA2's
    `B2Bridge`), but it is not written.

**Consequence.** B2.1 cannot be sealed from the current artifacts. The pieces must first be rebuilt on snapshot 9,
with proof-only repairs where `XNorm` is unfolded (`NormShift`, `B2Bridge`, `Couples`, and whatever else fails),
bridged, and composed.

## Statement-level notes

- B2.1 itself (statement fidelity) was audited in the B2 audits and approved as D8. `RA1Couple`, `RA1CoupleF80` and
  `RA1Tree` are internal obligations, not frozen statements. Once the composition proves the anchor's exact type with
  standard axioms, their faithfulness to DH23 Prop 6.1 matters only for the graph status of DH23 Prop 6.1, not for
  B2.1.
- RA2 records a finding, REGREF-1 (TARGET L1171–L1173): "translate by r" does not cover trees whose lone leaf lies in
  a lower layer (`q' < r`), and RA2 proves that case by a trace argument. To be filed in FINDINGS by the orchestrator;
  not re-verified here.
- RA1 couples' statement review (`audits/RA1Couple-F80-statement-review.md`, 55 rows) and RA1-TREES' `TYPE-AUDIT.md`
  were written by the packets' own authors, so they are not independent audits.

## Remediation in progress (2026-11-04)

- RA1 couples (Sonnet agent): rebuilding the 279-module closure with snapshot 9's `System.lean`, with proof-only
  repairs.
- B21-SNAP9 (new Sonnet agent; scratch `/home/scott/wt-scratch/b21-snap9`, worktree `wke-l2s`):
  - rebuild RA2 and RA1-TREES on snapshot 9;
  - prove `RA1Couple_of_F80`;
  - merge `w/bproc`'s Foundations;
  - compose `regularAsymptotics_snap9 := regularAsymptotics_of_obligations (RA1Couple_of_F80 regular_couple_asymptotics) ra1Tree`.

## Final audit, when the composition exists (wt-orch)

1. Run `TypeExprAudit9`, with the reference being `waveb9dev` (pinned snapshot 9 + B2 final, its own B1 copy):
   - literal Expr equality of the theorem type;
   - equality of every reachable definition;
   - the control: a snapshot-8 build must fail.
2. Axioms.
3. Hygiene.
4. Port as the B2.1 seal on `w/freeze-b2` (provider stub `Provider/RegularAsymptotics`), then ABI.
5. The second-key seal audit belongs to someone other than wt-orch.
