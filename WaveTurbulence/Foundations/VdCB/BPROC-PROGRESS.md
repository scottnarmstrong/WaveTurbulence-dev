# NT-BPROC progress

Branch `w/bproc`, based on `main` in the former AN-SOB worktree. Owned namespace and files:
`WaveTurbulence.VdCB`, `WaveTurbulence/Foundations/VdCB/**`.

Checked foundation: `Phase`, `IntegrationByParts`. The phase is the existing
`NumberTheory.expPhase`; the chain rule, `2π` Lipschitz estimate, interval-length bound and
exact oscillatory integration-by-parts formula are proved. Check:
`nice -n 5 lake build WaveTurbulence.Foundations.VdCB.IntegrationByParts` returned
`Build completed successfully (3510 jobs).`, no warnings.

No truncated-Poisson, stationary-phase or B-process theorem is yet claimed.

API issue raised with the orchestrator: a bare absolute derivative-comparability phase
class is not stable under the B-transform. The resonant `x^(3/2)` example in Olivier
Robert, *On van der Corput's k-th derivative test for exponential sums*, Lemma 7,
https://perso.univ-st-etienne.fr/rool6510/robert-2015-indag.pdf, has a main term of order
`N^(3/4)`. For `F=N^(3/2)`, the requested pair `(11/30,16/30)` would give `N^(43/60)`.
Robert Section 5 explains the need for stable semi-monomial classes; the conventional
model profile has decreasing first derivative `x^(-s)`, `s>0`, with controlled perturbations.
A clarification was requested; generic analytic work continues independently.
