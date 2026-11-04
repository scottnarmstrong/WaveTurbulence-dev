
## Queued prover tasks (orchestrator)

- **F-5 (B2 freeze REQUIRED):** prove the decaying-kernel version of `tendsto_pvResonantIntegral` (exact statement and
  proof sketch: `docs/campaign/orch/audits/WaveB2-handoff.md` addendum 2). Candidate: wt-resonant after C3 SKELETON
  (it wrote the Resonant integrals), or wt-l2s after PL1.

- **B2 freeze scope (orchestrator ruling 2026-11-04, small frozen surface):** freeze only the B2 declarations reachable
  from a frozen consumer (B2.1, B2.2 and the Regular/Molecules obligations); hold out the 63 declarations used only by
  the held-out B2.3 (countA, IsLadder, IsBlock, IsCutData, …) with B2.3 until packet G8. Regenerate the B2 FREEZE-LIST
  accordingly (wt-orch, after Task 24). Independent re-check: PASS WITH REQUIRED FIXES (only F-5 open).
- **Helpers for L3 (proplayer2):** the auditor's probe lemmas `KTstar_indep_of_le`, `item2_integrand_of_le`,
  `KTstar_relayer` (`/home/scott/wt-scratch/b2-audit/Q1.lean`, `Q3.lean`) can be adopted by the L3 prover.
