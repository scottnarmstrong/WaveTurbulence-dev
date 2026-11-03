# Packet NLS-BRIDGE (pre-freeze) — prove the Wave B gate `nlsAkBridge` from the landed NLS theory

Read `COMMON.md` first.

**Goal.** Prove the Wave B tier-B1 statement `nlsAkBridge`
(`/home/scott/wt-scratch/waveb-snap-5/WaveB1-Statements.lean:184`, all four conjuncts: forward, backward,
uniqueness, measurability) exactly as drafted in snapshot 5. Do not weaken, specialize or edit it. Its type, as
the main assembly consumes it, is in `/home/scott/wt-scratch/main-assembly/nlsAkBridge-type.txt`. Together with
`propansatz` it gives the frozen `main` (`MainGlue.main_of_propansatz_nlsAkBridge`,
`/home/scott/wt-scratch/main-assembly/`), so this packet closes the whole NLS side of Theorem 1.1.

**What is landed (main, `WaveTurbulence/Foundations/NLS/**`, namespace `WaveTurbulence.NLS`):**

- forward reduction: `Reduction.lean` (`wickGauge`, `reducedCoeff`, `massAvg_eq`, `wickGauge_eq`, phase lemmas);
- backward reduction: `Backward.lean` (`backCoeff`, `backSolution`, `IsAkSolution.isSmoothNLSSolution`);
- the a-system: `AkSystem.lean` (`IsAkSolution`, `aNonlin`, `wickConv`), with LWP, persistence and uniqueness in
  `AkLocal`, `AkPersistence`, `AkUnique`, `AkGronwall`, `AkMass`;
- measurability: `Measurability.lean` (`measurableSet_solvableEvent`,
  `measurable_indicator_norm_torusFourierCoeff_sq`);
- `MainGlue/**`: smooth data, observables, mass event.

**What is missing** is the identification of snapshot 5's own definitions (`IsASolution`, `ZNormOn`, `jbr` in
`WaveB1-System.lean`) with the landed ones (`NLS.IsAkSolution`, the Foundations norms), plus the four conjuncts
assembled from the landed theorems. Expect differences in:

- parameter conventions (`D` and `T = D δ T_kin` against the landed `T`, `𝔇`);
- the form of the phase and gauge factors in the forward map;
- the hypotheses: rapid decay `∀ s, ∃ C, ⟨k⟩^s |c| ≤ C` against the landed `IsRapidDecay`;
- finiteness of `ZNormOn` against `IsAkBounded`.

If a conjunct is false as drafted, stop and report exactly why with a counterexample sketch. The statement is
still pre-freeze and the author can fix it. Do not prove a modified version silently.

**Where:**

- Statement-independent lemmas about the landed objects go into Foundations on your branch, in files
  `WaveTurbulence/Foundations/NLS/Bridge*.lean`, namespace `WaveTurbulence.NLS`.
- The bridge to snapshot 5's definitions and the proof of `nlsAkBridge` go into untracked scratch at
  `/home/scott/wt-scratch/nls-bridge/`. Build there against a local copy of snapshot 5; the main-assembly build
  scripts show how. After the Wave B freeze you will move the scratch part into Foundations, importing the frozen
  definitions.

**Worktree:** `/home/scott/WaveTurbulence-worktrees/wke-l2s` (branch `w/wke-l2s`; merge main first).

**Done:**

- `nlsAkBridge` compiles in scratch with no sorry, and `#print axioms` shows only the standard three;
- the Foundations part is committed;
- `HANDOFF.md` is written in the scratch directory;
- you report `READY nls-bridge`.
