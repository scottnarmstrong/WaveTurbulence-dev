# Theorem 7 implementation check (2026-11-03)

This is worker-side implementation evidence, not an independent frozen-anchor
or manifest promotion. The exact implementation export is
`WaveTurbulence.WKEL2.exists_collisionTerm_bound`, in `Trilinear.lean`,
introduced at `ae6eadc`. The packet brief authorizes this implementation;
manifest and frozen-theorem ownership remain with the orchestrator. There is
no separate frozen Theorem 7 anchor in this packet. The frozen `wkelwp`
anchor is not imported and remains outside this completion claim.

## Pinned source and mathematical statement

`docs/research/git20-general-d.md`, lines 170–177, Theorem 7; TARGET TeX
lines 2514–2517, `(schappend8)`. The research-note SHA256 is
`a5be8c25934effaa3876e14da5f306d1cfebb7c9c6b1f2db5eb65eddc26b137f`.

For d ≥ 3 and s > d/2−1, there is a constant depending only on d,s that
bounds each of the four collision terms by the product of the three Z_s
norms. The implementation treats real signed Borel representatives, so it
includes nonnegative Borel inputs. Actual weighted `MemLp 2` membership is
the source condition “finite Z_s norm”; it is not replaced by finiteness of
the totalized real integral in `weightedL2Norm`.

## Expanded binder comparison

| Binder | Bin | Source meaning |
|---|---|---|
| implicit `d : ℕ` | TYPING | Euclidean dimension in Theorem 7 |
| `hd : 3 ≤ d` | SOURCE | d ≥ 3 |
| `s : ℝ` | TYPING | Real weight exponent |
| `hs : (d : ℝ)/2 - 1 < s` | SOURCE | Strict threshold, with no additional margin |
| `j : Fin 4` | TYPING | The four indices 0,1,2,3 |
| `f₁ : Mom d → ℝ` | TYPING | First real input |
| `f₂ : Mom d → ℝ` | TYPING | Second real input |
| `f₃ : Mom d → ℝ` | TYPING | Third real input |
| `Measurable f₁` | SOURCE | Borel representative of first measurable input |
| `Measurable f₂` | SOURCE | Borel representative of second measurable input |
| `Measurable f₃` | SOURCE | Borel representative of third measurable input |
| `MemLp (weightedFunction s f₁) 2` | SOURCE | First input belongs to Z_s |
| `MemLp (weightedFunction s f₂) 2` | SOURCE | Second input belongs to Z_s |
| `MemLp (weightedFunction s f₃) 2` | SOURCE | Third input belongs to Z_s |

Counts: SOURCE 8, TYPING 6, STANDING 0, RULED 0, EXCESS 0. The witness
`∃ C : ℝ, 0 ≤ C` lies before j and all three inputs; neither reference
vectors, kernel integrability estimates, M₁/M₂ constants, nor an operator
norm bound are hypotheses of the theorem. Output weighted membership is
proved together with the norm inequality. Borel models and representative
independence for the Banach solution theory are subsequent implementation
obligations; the theorem here is explicitly about Borel representatives.

## Definitions and normalization consumed

- `Mom d` is the unchanged frozen `EuclideanSpace ℝ (Fin d)`.
  SHA256: `22aaac77bd1887265c3d8fec49f6975ae68311e18529151740ba0e74557e5d87`.
- `weightedFunction s f k = (1+‖k‖²)^(s/2) * f k` is exactly the integrand
  multiplier in the frozen norm. `weightedL2Norm_eq_norm_toLp` proves the
  actual L² norm identity under actual weighted membership.
- Frozen `WeightedL2Norm.lean` SHA256:
  `92726d25128176c80d96bd3c18b475967dc900fdcec08f9cf5df71c9550fc52f`.
- `collisionTerm j` is the landed `WKE/CollisionOp.lean` term using
  `deltaInt`, with the four literal kernels of TARGET `(schappend1–4)`.
  Resonant measure omits the delta factor 1/2; the proved signed reading
  `integral_resonantMeasure_eq_two_deltaInt` restores it.
- Frozen `CollisionOp.lean` SHA256:
  `5246fe71b1082f7aa3f784220e77849dcb9a1debe013ebb06e7e489636a748c4`.
- The gain proof first proves extended nonnegative squared integrability,
  then derives actual kernel integrability almost everywhere, then uses
  the signed delta reading. It does not assume pointwise gain finiteness.
- The uniform constant is the sum of the four proved nonnegative constants;
  this is an allowed choice of C(d,s), with no claim of optimality.

## Mechanical evidence

`nice -n 5 lake build WaveTurbulence.Foundations.WKEL2.Trilinear`
exited 0, with no warnings. The implementation and all of its project
prerequisites contain no sorry, axiom declaration, or budget override.

`nice -n 5 lake env lean /home/scott/wt-scratch/wke-l2s/Theorem7Axioms.lean`
exited 0. All six checked results (unweighted gain pairing, weighted gain
pairing, nonnegative L² duality, weighted absolute-gain squared bound,
signed gain trilinear bound, and the combined Theorem 7 export) depend
exactly on `[propext, Classical.choice, Quot.sound]`.

Goal 4 remains active: the three supporting solution-space lemmas, Picard,
Gronwall, equality of maximal times, and the full blow-up limit. This report
does not claim those results, or closure of the frozen `wkelwp` statement.
