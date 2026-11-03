# Packet NT10 LEMLIN — TARGET Lemmas `lemlin` and `lemcubic0`

Read `COMMON.md` first. Blueprint rows `T.lemlin`, `T.lemcubic0` (packet NT10). Worktree:
`/home/scott/WaveTurbulence-worktrees/cumul`; new branch `git switch -c w/lemlin main`. Files:
`WaveTurbulence/Foundations/LemLin/**` (namespace `WaveTurbulence.LemLin`). Landed inputs: `Foundations/Fourier/**`
(χ₀, Poisson summation on ℤ_L^d `PoissonLattice`, non-stationary phase, bilinear stationary phase).

Goals (commit after each; do not end your turn at milestones):
1. **`lemlin`** (TARGET `/home/scott/wave-turbulence/paper/source/WKE-Longer_times_Final_arXiv.tex` L1536–L1543): for
   L⁻¹ ≤ |r| ≤ L^{−γ+η}: ∫_{[τ, τ+δL^{2γ}]} |Σ_x χ₀(x−a) e(s⟨r,x⟩ + ⟨ξ,x⟩)| ds ≲ min(δL^{d+2γ}, L^d |r|⁻¹)
   (x over ℤ_L^d). Note FINDINGS F23: TARGET's `sumint` case (d) for γ > 8/9 needs a second bound of `lemlin` using
   |r| ≥ L⁻¹ that the paper does not state — work out and prove that bound too (state it separately).
2. **`lemcubic0`** (L1544–L1553): for |s|, |t| ≤ L and Λ ∈ {⟨x,z⟩, ⟨z, x+y−z⟩}:
   Σ_{(g,h,q)∈ℤ^{3d}} |∫∫∫ χχχ e[…] e(t⟨x,y⟩ + sΛ)| ≲ (1+|s|+|t|)^{−d}.
Done: `READY lemlin`.
