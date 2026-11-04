# VINEPARAM (M9) — ongoing

Main merged as 9dd58fc before starting. Scratch continuation in
`/home/scott/wt-scratch/vines/src/`, namespace `WaveTurbulence.Vine.Param`;
handoff `/home/scott/wt-scratch/vines/param/HANDOFF.md`. No repository Lean
changes pending Wave B freeze. The type-II endpoint is m=1 (F72).

The source scope is molecule-level integral affine charts and exact
resonance identities, all eight types with inserted ladders (F22).
Garden-level leaf/internal-node ordering estimates remain V4.

## Checked local rung/ladder charts and source-sign ruling

`VineParamRungCharts`: all six balanced rung orientations, explicit affine
encode/decode inverses over any additive commutative group.
`VineParamRungResonance`: exact lower bilinear resonance, upper gap correction,
and ternary/nontrivial coefficients. `VineParamLadderCharts`: explicit
triangular bijection at arbitrary ladder length (including zero/one rungs).
`VineParamTriangleCore`: same-direction zero-gap triangle chart, signed
resonance identities, momentum identities and scalar source-sign regression.
Focused serial build of these four modules passed, exit0, no warnings.
The 13-declaration probe `param/Axioms.lean` passed, standard axioms only.

Owner ruling 2026-11-04: “Use signed forms; flag for audit.” The literal
TARGET Step 2(C-ii) signs do not match Figure (D)'s directed Gamma formulas;
the exact example and corrected signed formulas are recorded in
`param/HANDOFF.md`, flagged for independent source audit. No template change.
Remaining M9 includes actual molecule transport, normal core orientation
cases and the full eight-type assembly. Continuing directly.
