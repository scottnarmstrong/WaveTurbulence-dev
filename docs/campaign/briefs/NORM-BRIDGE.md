# Packet NORM-BRIDGE (pre-freeze) — bridges between the Wave B norms and the landed Foundations norms

Read `COMMON.md` first. Context: the Wave B tier-B1 statements use their own (self-contained) norms `SNorm`, `SNormR`,
`XNorm`, `XNormRestr`, `XNorm00`, `XNorm00Restr` (drafts: `/home/scott/wt-scratch/waveb-snap-3/WaveB1-System.lean`;
readings agree with the landed ones per `docs/campaign/orch/audits/Infra-review-2.md` S3), while the landed analysis
(`WaveTurbulence/Foundations/Fourier/**`: `spatialNorm`, `mixedFourierNorm`, `timeFourierNorm`, restriction norms,
product/cutoff/interpolation lemmas) proves estimates for the Foundations norms. Provers need equalities so the landed
estimates apply to the frozen statements. Also B1.6 `sumint` needs an 𝔛^{θ,0,0} norm over a general vector-variable
type V, which Foundations lacks.

Work: (a) in Foundations (normal branch `w/norm-bridge` from main, files `WaveTurbulence/Foundations/Fourier/Norm00V*.lean`
namespace `WaveTurbulence.Fourier`): add `mixedFourierNorm00` over a general finite-dimensional V with the basic lemmas
the landed `mixedFourierNorm` has (cutoff multiplication, products, restriction). (b) In untracked scratch
`/home/scott/wt-scratch/norm-bridge/` against a local copy of snapshot 3: prove `SNormR Λ₁ Λ₂ F = spatialNorm Λ₁ Λ₂ F`,
`XNorm θ Λ₁ Λ₂ F = mixedFourierNorm …` (and the restriction versions), `XNorm00 = timeFourierNorm`/`mixedFourierNorm00`
(state precisely; momentum words vs multi-indices; agreement-on-B vs functions on B; a.e. vs pointwise guards — if a
bridge is false as stated, report exactly why). After the Wave B freeze you move (b) into Foundations importing the
frozen norms. Worktree: `/home/scott/WaveTurbulence-worktrees/cumul`. Done: `READY norm-bridge`.
