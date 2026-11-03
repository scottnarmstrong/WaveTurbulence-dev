# Packet X1 FLOWER-DEF (pre-freeze, design + proofs) — flower trees/gardens, kernels, parametrix identities

You drafted the deferred flower objects (`/home/scott/wt-scratch/waveb/WaveB1-Deferred.lean`: `KGflower`, `topCountBelow`,
`FlowerRestr`, `truncSumHζ`, `WTPrefixP`, B1.12 `layergardenFlower`) and the Duhamel identity. This packet (blueprint X1,
critical path: X1 → X2 → X3 → I2 → Z1) settles them so that B1.12 can be frozen and `fixedpoint` proved.

Known problems (all in `/home/scott/WaveTurbulence-dev/docs/FINDINGS.md`): **F26** (TARGET L2279–L2305 re-runs §5–§11 for
flower gardens only through a list of adjustments; operator identities asserted), **F39** (𝒳's kernel as printed has
only flower trees of order ≥ 1, so (1−ℒ₁)𝒳 = 1+𝒴 needs an identity term), **F46** (L2288 read literally makes the
𝒴/𝒲 sums empty; delta-1 D1: `truncSumHζ` is empty for kinds ≠ 0), **F25** (prefactor typo in `jtflower`/`kqflower`).
Sources: TARGET L2258–L2305 (flower trees, parametrix), DH21 §11 (`/home/scott/wave-turbulence/references/src-2104.11204/Inventiones-Final_Version.tex`
Def 11.1, Prop 11.2 L2660ff, Cor 11.3), DH23 §11 (`Revision_Submit.tex`), DH21-2 §4 (N = ⌊(log L)^4⌋ variant); maps
`maps/T-part2.md` §12, `maps/DH21.md` §11; wt-orch's `figure-defs.md` §7 and `GRAPH-topology.md` I14–I15, G-1.

Work in untracked scratch `/home/scott/wt-scratch/flower/` against snapshot 5 + your SYS-DEFS/Duhamel scratch.
Goals (do not end your turn at milestones):
1. Reconstruct from DH21 §11 the exact flower-tree classes and kernels for 𝒳, 𝒴, 𝒲 (with the identity term, F39), and
   prove the operator identities (1−ℒ₁)𝒳 = 1+𝒴 and 𝒳(1−ℒ₁) = 1+𝒲 (`GAP.operatorIdent`) for the Lean ℒ₁ of snapshot 5
   (your Duhamel `Lop`).
2. Fix the flower sums: corrected `truncSumHζ` for kinds 𝒴/𝒲 (F46/D1), with the 𝒴/𝒲 restrictions DH21 uses.
3. Redraft B1.12 `layergardenFlower` so that it is sufficient for `fixedpoint`'s proof (stage-3 R8: the M₁/M₂ cutoffs and
   the time-derivative variants of L2312, L2320–L2338), as a frozen-candidate statement with docstring and deviations.
4. A design memo `FLOWER-DESIGN.md`: what changed relative to TARGET's text, why, with source lines (these will be
   reviewed by wt-orch and then shown to the author for a freeze of B1.12).
Done: `READY flower`.
