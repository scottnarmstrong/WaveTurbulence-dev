# wt-orch Task 4c — statement review of landed infrastructure (while Wave B stage 1 is being drafted)

Main now has ~13k lines of landed Foundations code from the provers (TORUS-FOURIER, GAUSS-HC, CUMUL partial, WKE
partial, NT-CIRCLE audit, GAUSSSUM partial, AN-SOB partial, NLS partial). These are not frozen, but their main
theorems will become graph nodes. Do a light refute-first **statement** review (not proofs): for each module's main
results, check the Lean statement against the cited source formula (TARGET/DH21/DH23/GIT20 lines in the docstrings):
hypotheses too strong to be dischargeable at the use site, junk-value hazards (tsum/integral/division), missing
uniformity of constants, wrong normalizations. Priorities: `Foundations/Cumulant/**` (inversion, propertycm with the
F30 ranges), `Foundations/Gaussian/Isserlis*`, `Foundations/Torus/**` (normalizations vs (1.2), Laplacian multiplier),
`Foundations/NLS/**` (a-system ε, Ω, C_ζ vs (akeqn2), (defcoef0), (res)), `Foundations/WKE/**`.
Write `docs/campaign/orch/audits/Infra-review-1.md` (table: module, declaration, verdict, issue, fix), commit on w/orch.
Interrupt this task as soon as the orchestrator announces Wave B stage 1 (Task 4b has priority). Print `READY task4c`.
