# Packet JR-OPS — DH21 class J / class R operators (the analytic core of packets J1, J2; critical path)

Read `COMMON.md` first. Blueprint rows `DH21.classJR`, `DH21.classJR2` in
`/home/scott/WaveTurbulence-dev/docs/blueprint/GRAPH.md` (packets J1, J2 on the critical path).
Worktree: your current one (`/home/scott/WaveTurbulence-worktrees/wke`); new branch `git switch -c w/jr-ops main`.
Files: `WaveTurbulence/Foundations/ClassJR/**` (namespace `WaveTurbulence.ClassJR`).
Sources: DH21 `/home/scott/wave-turbulence/references/src-2104.11204/Inventiones-Final_Version.tex` L936–L1060 (Prop 5.1
statement for context; Def 5.2, Lemmas 5.3–5.8), DH23 `/home/scott/wave-turbulence/references/src-2301.07063/Revision_Submit.tex`
L955–L969 (the improved weights DH23 uses: X^{1−η} instead of DH21's X^{1/9}; FINDINGS/DH21 map E11 — determine which
weights TARGET's route needs and state the lemmas in the form that serves both, or in DH23's form, documenting it).
Map: `/home/scott/wave-turbulence/maps/DH21.md` (§5 entries). Landed inputs: `Foundations/Fourier/**` (χ₀, Gevrey,
time-Fourier norms), `Foundations/Combinatorics/**` (DH21 Lemma A.4 `combineq`, from MISC-A, if landed; otherwise
prove what you need locally under a distinct name).

Goals (commit after each):
1. **Def 5.2 and Lemmas 5.3–5.5**: class J and class R operators (kernels with Gevrey-weighted L¹ norms of their
   time-Fourier transforms); closure: J∘J, J∘R, R∘R are class J with norm ≤ C·(product of norms).
2. **Lemmas 5.6–5.8**: I_{εα} J I_{μ−εα} and its R analogue decompose into class J + class R; the identity
   I_{εα} I_{μ−εα} = χ_∞(α)/(επiα) J + J + R.
3. As far as possible without the frozen combinatorial definitions: the Lemma 5.9–5.10 statements of DH21 that are pure
   operator statements (report which parts need regular-chain combinatorics, packet J2's `DH21.regchainlem`).
Done: `READY jr-ops`.
