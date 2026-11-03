# Packet NT6 APPROXNT — DH23 Prop 6.4 (lattice-sum approximation) and its large-order extension (F33)

Read `COMMON.md` first. Blueprint rows `DH23.approxnt`, `GAP.largeOrder.nt` (packet NT6, upstream of RA1 REGASYMP on the
near-critical chain). Worktree `/home/scott/WaveTurbulence-worktrees/torus-fourier`; new branch
`git switch -c w/approxnt main`. Files: `WaveTurbulence/Foundations/ApproxNT/**` (namespace `WaveTurbulence.ApproxNT`).

Sources: DH23 `/home/scott/wave-turbulence/references/src-2301.07063/Revision_Submit.tex` L984–L1010 (Prop 6.4; proof
"= DH21 Prop 6.1"), DH21 `/home/scott/wave-turbulence/references/src-2104.11204/Inventiones-Final_Version.tex`
L1504–L1657 (Prop 6.1's proof; DH21 is for γ = 1/generic tori — use DH23's γ-range versions of the number-theory
lemmas, FINDINGS F13). FINDINGS F33 (orders up to N_{p+1}^4 = (log L)^{C(𝔇)}; route R14 (a): the bound must hold
uniformly in that range). Maps: `maps/DH23.md` (approxnt entry), `maps/DH21.md` (Prop 6.1).

Landed inputs (import, don't edit): your `Foundations/NTSP/**` (DH23 Lemmas 6.5, 6.7, TARGET Lemma 5.2),
`Foundations/Resonant/**` (p.v. 1/Ω, DH21 Lemma 6.3), `Foundations/Fourier/**` (Poisson, Gevrey, phase lemmas);
in progress elsewhere: `Foundations/WeylSums/**` minor-arc lemmas DH23 6.6(1),(2) (wt-gausssum, packet MINOR-ARCS) —
use their statements as soon as they land; until then structure your proof so those two lemmas enter as clearly named
inputs of internal helper lemmas (distinct names, never as hypotheses of the final theorem).

Goals (do not end your turn at milestones):
1. State DH23 Prop 6.4 exactly (the sum I over x_j, y_j ∈ ℤ_L^d of W·Ψ(δL^{2γ}⟨x_j,y_j⟩) = L^{2dn}∫WΨ + error, the
   approximation I_app with p.v. 1/⟨x,y⟩ and δ(⟨x,y⟩) factors, the triangular support structure) for n up to
   N_{p+1}^4 and box sizes with ∏λ_j ≤ C^n, uniformly (the large-order extension), and prove it via the major/minor arc
   decomposition (DH21 Prop 6.1's proof with DH23's lemmas).
2. Record every place the source's n ≤ N³ = (log L)^{12} restriction was used and how the extension handles it.
Done: `READY approxnt`.
