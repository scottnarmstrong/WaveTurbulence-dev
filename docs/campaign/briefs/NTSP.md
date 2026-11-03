# Packet NT5 NTSP — DH23 Lemmas 6.5, 6.7 and TARGET Lemma 5.2 (oscillatory lattice sums)

Read `COMMON.md` first. Blueprint rows `DH23.NTSP`, `T.lemlayer1`, `DH23.NTintlem` (packet NT5; upstream of NT6 APPROXNT
and RA1 REGASYMP, near the critical path). Worktree: `/home/scott/WaveTurbulence-worktrees/torus-fourier`; new branch
`git switch -c w/ntsp main`. Files: `WaveTurbulence/Foundations/NTSP/**` (namespace `WaveTurbulence.NTSP`).
Landed inputs (import, don't edit): `Foundations/Fourier/{PoissonLattice,NonstationaryPhase,BilinearPhase,Chi0,...}`
(χ₀, Poisson summation on ℤ_L^d, non-stationary and bilinear stationary phase), `Foundations/Resonant/**` (resonant
measure, principal value).

Goals (commit after each; do not end your turn at milestones):
1. **TARGET Lemma 5.2** (`lemlayer1`, `/home/scott/wave-turbulence/paper/source/WKE-Longer_times_Final_arXiv.tex`
   L958–L969): for |s| ≤ L, Σ_{(g,h)∈ℤ^{2d}} |∫∫ χ₀(x−a)χ₀(y−b) e[⟨Lg+ξ,x⟩ + ⟨Lh+ξ′,y⟩ + s⟨x,y⟩] dx dy| ≲ ⟨s⟩^{−d}
   (proof: "an easier version of DH23 Lemma 6.5", L966).
2. **DH23 Lemma 6.5** (`NTSP`, `/home/scott/wave-turbulence/references/src-2301.07063/Revision_Submit.tex`
   L1013–L1074): (1) ∫_ℝ |∫ χχΦ e(ξ·x + ζ·y + s⟨x,y⟩)| ds ≲ Dλ^{2d}; (2) the nonzero Poisson modes are
   ≲ Dλ^{2d} L^{−1+2η}(1+|ξ|+|ζ|) when supp Φ ⊂ {|s| ≲ L}. Read the source for Φ, D, λ.
3. **DH23 Lemma 6.7** (`NTintlem`, DH23 L1143–L1156): μ⁻¹∫ψ(μΩ)χ₀χ₀Φ e(·) is bounded and converges to
   (∫ψ)∫δ(Ω)χ₀χ₀Φ e(·) with error Dλ^{2d} μ^{−(1−2η)} (1+|ξ|+|ζ|), δ(Ω) read via the landed resonant measure.
Done: `READY ntsp`.
