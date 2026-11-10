# F79 kernel check — VINEPARAM → V4 / signed sumint

**Confirmed. Use the signed core forms, per the owner ruling.**

The following declarations have compiled with default budgets and were included
in the 151-declaration audit (all names matched, standard axioms only, zero
warnings/errors):

- `WaveTurbulence.Vine.Param.TriangleCore.phase_zero`
- `WaveTurbulence.Vine.Param.TriangleCore.phase_two`
- `WaveTurbulence.Vine.Param.TriangleCore.phases_sum`
- `WaveTurbulence.Vine.Param.TriangleCore.displayed_sign_counterexample`

Files: `<scratch>/vines/src/VineParamTriangleCore.lean`;
audit: `<scratch>/vines/param/Axioms-Checkpoint.lean` and `.log`.
For Figure (D)'s same-direction core, at g=0 and conservation e=a+b,
d=a+b−c, the actual Gamma factors are

    2ab,  −2(c−a)(c−b),  2c(c−a−b).

The checked chart gives first factor +2⟪u₁,u₂⟫ and another factor
**−2⟪u₃,u₁+u₂−u₃⟫**, with exact zero sum. Molecular negative Gamma flips
the whole triple; it does not remove the relative minus sign.
The scalar source-coordinate regression a=b=1,c=g=0 has actual −Gamma(w₁)=−2,
whereas the source's displayed 2(a−e)(b−e) is +2.

A stronger independent quadratic-matrix obstruction certificate is queued as
`VineParamF79Determinant.lean`: actual symmetric coefficient determinants all
zero; the third factor for the printed two-positive nonlinear pair has
coefficient determinant −4 (Hessian determinant −32). Its build status will
be appended here once checked. This distinction does not affect the already
checked relative sign or the approved signed-extension decision.

No source interpretation, template, frozen anchor, or unsigned B1.6 statement
has been edited. The signed reading remains flagged for independent audit.
The full arbitrary-insertion M9 assembly is still in progress.

The coordination contract files were not present when this note was written;
M9 will align its final result to Contract.lean when it is available.

## Stronger certificate completed

`VineParamF79Determinant.lean` now compiles, including `actualGram_eval`,
`positiveThird_eval`, `actualGram_det`, `positiveThird_det` and
`no_linear_pullback`. The latter excludes every real 3×3 linear substitution
and every scalar sign change on any actual source Gamma matrix. The checked
symmetric determinant is **−4**, hence Hessian determinant **−32**; an earlier
informal mention of 32 referred to the nonzero magnitude/sign convention.
The source quadratic-part obstruction is now kernel checked as well as the
explicit signed normal forms and the scalar regression.

The refreshed158-declaration axiom audit includes all five determinant results
and both representative difference-support packages: all names matched,
standard axioms only, zero errors/warnings. See the same checkpoint files.

Further kernel-checked evidence (M9 construction): both normalized type-III
joint choices J0III000 and J1III000 now provide full finite signed
certificates, consumed by NormalizedVineCertificate.fullChart. The complete
one-rung insertedFullChart constructor also preserves those exact common and
relative core signs. The356-query construction audit matched with only the
standard axioms. This strengthens the F79 outcome above; the exact all-vine
VINEPARAM theorem is still being assembled.
