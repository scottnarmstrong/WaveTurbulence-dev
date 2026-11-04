# Re-check: wt-l2s's INCOH-INST (B2.2 `incoherentDecay`) on B1 snapshot 9

Auditor: `wt-orch`, refute-first. Date: 2026-11-04 (Task 36, before sealing B2.2 on `w/freeze-b2`).

**Scope.** INCOH-INST (`/home/scott/wt-scratch/incoh-inst`, `HANDOFF.md`, READY incoh-inst) was built and audited on
snapshot 8's B1 `System`. Snapshot 9 changed one B1 definition, `XNorm` (F80: the a.e. `C^{Λ₁}` guard), and B2.2 is
stated with `XNormRestr`. The questions:
- does the proof still compile on snapshot 9?
- is its theorem still exactly the B2.2 anchor of the final candidate on snapshot 9?

## Verdict

**PASS, after three proof repairs (mine; no statement changes).**
- On snapshot 9, all 264 modules of the proof closure compile, and the type audit passes against a reference on
  snapshot 9. The axioms are standard.
- **I-1 (the original audit could not see B1).** wt-l2s's type audit loaded its reference from
  `/home/scott/wt-scratch/waveb2/build`, which holds only `WaveB2Draft`. The reference's B1 modules therefore
  resolved to the proof's own build, so B1 definitions were never compared independently. My re-run uses a
  reference with its own B1 and catches a B1 change (control below).

## 1. Inputs

- **Pin.** I copied the packet at 11:28 UTC: `SHA256SUMS` verifies (109 files); 274 sources, list digest
  `95f2eafc08ec…`.
- **Closure.** The import closure of `IncohInst.IncoherentDecay` is exactly the packet's 264-module build list:
  - 154 REG-STRUCT modules, byte-identical to those pinned for the B2 providers;
  - 74 authored by wt-l2s;
  - 24 LINKS, LAYERREG and ENHANCED drafts (via mexp), 10 regref modules;
  - the B1 `Core`/`System` copies and a Regular copy without §4's draft theorems.
- **Project imports.** All 606 Wave A and Foundations modules the proof imports are on main, byte-identical to the
  ones the packet used. 353 of them (352 `Foundations/Incoh`, one `Foundations/WKE`) postdate `w/freeze-b1`'s base.

## 2. Rebuild on snapshot 9

**Environment.** The pin, with `WaveBDraft/System.lean` replaced by snapshot 9's (`cc53aad3acd7…`; `Core` is the
same in both). Built on dev's build, in the packet's order, one `lean` at a time.

**Three modules unfold `XNorm` and needed proof repairs.** The guard is now a conjunction, and the per-frequency
`if` inside the integral is gone.
- **`TimeBridge.lean`.** It is byte-identical to `sumint`'s scratch file. I applied the same repair as in the
  `sumint` seal: three `XNorm` lemmas at `Λ₁ = 0`.
- **`IncohInst/NormBridge.lean`, `XNorm_le_mixed`.**
  - The guard is now discharged from `MixedFourierAdmissible`: integrability, and the a.e. `ContDiff` of
    `mixedTimeFourier` transported by `timeFT_eq_mixed`.
  - The per-frequency rewrite is dropped.
- **`RegrefDraft/NormShift.lean`, `XNorm_shift`.**
  - The a.e. `ContDiff` conditions of `F` and of `F(· − c)` are equivalent. This is `contDiff_const_mul_iff`, the
    step the old proof used per frequency, under `Filter.eventually_congr`.
  - The integrands agree as before.

**Result.** All 264 modules compile with 0 errors, and the three repaired modules have no warnings. The axioms of
`WaveTurbulence.IncohInst.incoherentDecay` are [propext, Classical.choice, Quot.sound].

## 3. Type audit

**Program.** wt-l2s's `TypeExprAudit.lean`. The only change is the reference search path.
- **The reference is `waveb9dev/build`:** snapshot 9's B1 and the `waveb2-snap-final` B2 modules, all verified
  byte-identical to their sources, built on dev's Wave A.
- It holds both `WaveBDraft` and `WaveB2Draft`, so the reference environment is independent of the proof's build
  for B1 as well.

| run | proved environment | reference | result |
|---|---|---|---|
| main | rebuild on snapshot 9 | snapshot 9 + B2 final | **PASS**: literal Expr equality of the theorem type; all 215 reachable definitions equal in type and value |
| control 1 | rebuild on snapshot 9 | wt-l2s's `waveb2/build` (B2 only) | PASS. This is the I-1 weakness: B1 comes from the proof's own build. |
| control 2 | wt-l2s's original build (snapshot 8) | snapshot 9 + B2 final | **FAIL: `reachable source definition differs: WaveTurbulence.XNorm`** |

**Control 2 shows the audit sees the F80 change.** The theorem type alone passes in both directions: it names
`XNorm` without unfolding it. Only the reachable-definition check detects the change.

## 4. Consequences

- **The B2.2 seal on `w/freeze-b2`** uses the repaired files. The provider is the anchor's statement, closed by
  `WaveTurbulence.IncohInst.incoherentDecay`. See `FREEZE-B2-PLAN.md`.
- **wt-l2s's scratch** still has the snapshot-8 proofs of `NormBridge` and `NormShift`. I did not edit it. They
  should take the same repairs, and re-run their audit with a reference that contains B1 (I-1).
