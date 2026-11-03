# Packet N1 AN-FOURIER — Gevrey cutoffs, time-Fourier norms 𝔛, restriction norms, Fourier-L¹ products

Read `COMMON.md` first. Blueprint rows `T.cutoffs`, `AN.gevrey`, `AN.timeFourier`, `AN.fourierL1Product` (packet N1)
in `/home/scott/WaveTurbulence-dev/docs/blueprint/GRAPH.md`; Wave B proposal `docs/blueprint/WAVE-B.md` §2.6.
Worktree `/home/scott/WaveTurbulence-worktrees/an-fourier`, branch `w/an-fourier`. Files: `WaveTurbulence/Foundations/Fourier/**`.

Sources: TARGET `/home/scott/wave-turbulence/paper/source/WKE-Longer_times_Final_arXiv.tex` L579–L595 (norms
(normX), (normX1), (normX2), (locnorm), (defznorm)), L615–L623 (χ₀, Gevrey class 2), L1007–L1012 (Fourier-L¹
products); DH21 L982 (Rodino, Gevrey functions).

Goals (commit after each):
1. **AN.gevrey**: an explicit even C^∞ function χ₀ : ℝ → [0,1], = 1 on [−1/2,1/2], = 0 off (−1,1), with
   `|χ₀^{(m)}| ≤ (2m)!` for all m (Gevrey 2) — construct it concretely (e.g. from exp(−1/x)-type bumps; you may need
   a Gevrey-2-preserving construction, check the constants); tensor product on ℝ^d; χ_∞ = 1 − χ₀; Fourier decay
   `|χ̂₀(ξ)| ≤ C e^{−c|ξ|^{1/2}}`; closure of Gevrey bounds under products/composition with affine maps. This χ₀ is
   a candidate for the Wave B frozen definition: keep its definition simple and self-contained in one file
   `Fourier/Chi0.lean`.
2. **AN.timeFourier**: time Fourier transform on ℝ^r (Mathlib `Real.fourierIntegral`/`VectorFourier`); the weighted
   L¹ Fourier norms 𝔛^θ and 𝔛^{θ,Λ₁,Λ₂} (with L^∞_k inside) as in (normX)/(normX1), ENNReal-valued (no junk 0: := ∞
   when the defining integrals do not make sense, see WAVE-B §2.6); restriction norms (locnorm) (inf over extensions);
   basic lemmas: products (Banach-algebra-type bound for 𝔛^θ with θ ≥ 0), translations, modulations, multiplication
   by cutoffs, Hölder interpolation in θ.
3. **AN.fourierL1Product** (L1007–L1012): Fourier-L¹ norms of products of localized smooth factors under unimodular
   integer changes of variables, bounded by C^n ∏ of W^{d+1,1}-type norms.
Done: `READY an-fourier`.
