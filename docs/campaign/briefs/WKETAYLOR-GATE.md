# Packet WKETAYLOR-GATE (pre-freeze): prove the Wave B gate B1.5 `wkeTaylor` from the landed WKE theory

Read `COMMON.md` first.

**Goal.** Prove B1.5 `wkeTaylor` exactly as drafted in snapshot 7
(`/home/scott/wt-scratch/waveb-snap-7/WaveB1-Statements.lean`, `theorem wkeTaylor`; TARGET (wketaylor)–(taylorbound)
L752–L758, F10). The statement is
`‖𝒰_N‖_{𝔖^{4Λ,4Λ}} ≤ C₂(C₁δ)^N`, with C₁ independent of 𝔇 and Λ.

Do not weaken, specialize or edit the statement. If a conjunct is false as drafted, stop and report it with a
counterexample sketch. The statement is pre-freeze, and the author can fix it.

This is the last of the three gates your `propansatz_of_gates` needs that is not a deep combinatorial result. With it,
`main` reduces to:
- `layergarden` (B1.2);
- B1.12 (`layergardenFlower`);
- the two expansion obligations behind `fixedpoint`.

**Landed inputs (main).**
- WKE-TAYLOR: `WaveTurbulence/Foundations/WKE/**`, the Taylor expansion `taylorU` and its bounds.
- The general-d weighted trilinear estimates: `Foundations/WKEL2`.
- The bridge `wkeTaylorTerm_eq_taylorU` (B1 `WaveB1-Bridges.lean`, snapshot 7).
- The Foundations norm bridges: NORM-BRIDGE scratch `/home/scott/wt-scratch/norm-bridge`, plus landed
  `Foundations/Fourier/Norm00V*`.

The `SNormR` vs `spatialNorm` identification lives in NORM-BRIDGE. Reuse it; do not reprove it.

**Model.** NLS-BRIDGE (`/home/scott/wt-scratch/nls-bridge`) did the same job for `nlsAkBridge`. Copy its
`verify_source.py` and type-audit pattern, including a textual comparison against the snapshot type.

**Where.**
- Statement-independent lemmas: Foundations on your branch, `WaveTurbulence/Foundations/WKE/TaylorGate*.lean`.
- The gate proof: scratch `/home/scott/wt-scratch/wketaylor-gate/`, against snapshot 7.

**Worktree.** `/home/scott/WaveTurbulence-worktrees/cumul`. Merge main first.

**Done.**
- The gate compiles at the exact type, with no sorry and only the standard axioms.
- A HANDOFF is written.
- You report `READY wketaylor-gate`.

**Afterwards (post-freeze).** You will port INDUCT to the frozen module names. The freeze is awaiting the author.
