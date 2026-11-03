# NT-BPROC handoff

## Scope and source-facing results

All implementation and documentation changes are confined to
`WaveTurbulence/Foundations/VdCB/`. The public import is
`WaveTurbulence.Foundations.VdCB.BProcess`; namespace `WaveTurbulence.VdCB`.
See `API.md` for precise interfaces and `BPROC-PROGRESS.md` for staged checks.

1. `SharpPoisson.norm_sum_sub_poisson_derivative_range_le` proves the sharp
   truncated Poisson estimate for natural endpoints, global C2 phase,
   actual nonpositive second derivative, derivative range `[alpha,beta]`,
   and `0<eta≤1`. The frequency window is exactly
   `alpha-eta < nu < beta+eta`, and the error is
   `10*(eta^-1+log(beta-alpha+2))`. This is the precise version proved,
   not a claim of arbitrary real endpoints or minimal C1 regularity.
2. `SharpStationary` and `SharpStationaryNegative` give actual C3 stationary
   phase with explicit curvature/cubic/radius errors and signs `+1/8`
   and `-1/8`. `BProcessSelected` and `BProcessNegative` select actual
   stationary points and prove finite B-process formulas and error bounds.
3. `CircleCountingBridge.norm_sum_circle_endpoint_dyadic_le` proves the
   actual dyadic endpoint exponential-sum input required by wt-nt, with
   `(kappa,lambda)=(11/30,16/30)`. It assumes only `R≥1`, arbitrary real
   center `c`, harmonic `n:Nat>0`, dyadic index `m`, and block scale
   `U=R/2^(m+1)≥1`. The phase is exactly
   `expPhase (n*Counting.circleHeight R c x)`. It covers both octants,
   exact strict/open boundaries, and clipping of the final dyadic block.
   The resulting unconditional translated closed-disc discrepancy and
   annulus results are exported in the same module at exponent `27/41`.

The actual source phase is handled directly, as authorized by the user's
circle-family option. No smallness restriction on its multiplicative arc
factor is introduced. The physical lattice shift is tracked: the dual is
`R*sqrt(h^2+nu^2)+c*nu`, with negative-curvature quarter phase `-1/8`.
The bound consumes the actual landed fifth-derivative/A-process theorems,
not an assumed dual-sum estimate. All B errors are optimized and absorbed;
short intervals and high harmonics have separate proved estimates.

The shared `HasDerivativeBounds`, decreasing-power `HasPowerProfile`, and
`IsExponentPair` definitions, trivial pair, coordinate transforms and
coordinate arithmetic are available. **Generic analytic closure of
`IsExponentPair` under B is not proved or claimed.** The approved direct
circle-family route supplies the B-transform form needed by counting.

## Independent statement check

A separate read-only reviewer checked the exact dyadic export against
`Counting.CircleEndpointTransfer`, the translations/reflections, clipping,
critical-point identities, actual weighted A-estimate consumption, and error
absorption. Verdict: PASS for the approved direct circle-family route.
No frozen anchors or manifest statuses were edited or promoted.

| Expanded dyadic-export binder | Classification |
| --- | --- |
| `R : Real` | TYPING |
| `hR : 1 ≤ R` | SOURCE |
| `c : Real` | TYPING, arbitrary center |
| `n : Nat` | TYPING |
| `hn : 0 < n` | SOURCE |
| `m : Nat` | TYPING |
| `hU : 1 ≤ R/2^(m+1)` | SOURCE |

Counts: TYPING 4, SOURCE 3, STANDING 0, RULED 0, EXCESS 0.
Meaning-carrying definitions are literal numeric/phase/finite-set formulas;
the endpoint interval is explicitly `Counting.integerInterval` (closed).
Producer-to-consumer composition is in the proofs of the unconditional disc
and annulus theorems, supplying every endpoint estimate internally.

## Checks, uncertainties, errata

Targeted public build:
`nice -n 5 lake build WaveTurbulence.Foundations.VdCB.BProcess`
returned `Build completed successfully (9237 jobs).`, without warnings.
Additional focused build and axiom evidence is recorded in the progress log.
Final axiom check and post-merge check are recorded below when complete.

No suspected pinned-paper erratum was found. Explicit scope choices are the
regularity/endpoint version of Poisson stated above and the user-approved
direct circle-family route in place of a generic profile-closure theorem.
Constants are explicit and generous, not optimized. No known mathematical
uncertainty remains in the direct-family counting interface; a claim about
full generic exponent-pair closure would require additional work.

`nice -n 5 lake env lean /home/scott/wt-scratch/bproc/CompletedCircleAxioms.lean`
exited 0. `#print axioms` for sharp Poisson, both sharp stationary signs,
negative selected B-process, optimized actual source, actual endpoint block,
exact dyadic counting input, unconditional disc and annulus bounds, and the
trivial exponent pair reports only `[propext, Classical.choice, Quot.sound]`.

Merged main `430d637` at clean point (merge commit `e09211d`). The post-merge
public build again returned `Build completed successfully (9237 jobs).`
`git diff main --check` passed. A scan of VdCB Lean files found no forbidden
proof placeholders, custom axioms, unsafe/opaque declarations, or budget
overrides; the largest VdCB Lean file has 143 lines. Independent review
reported no statement defect. The working tree was clean before this final
handoff-log update.
