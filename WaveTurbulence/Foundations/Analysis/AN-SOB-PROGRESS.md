# AN-SOB progress

Branch `w/an-sob`; merged main after the orchestrator's integration notice.
Owned modules only under `WaveTurbulence/Foundations/Analysis/`.

## Checked milestones

- `dd28a2f`: interval W¹,¹ and H¹ bounds, normed-space version, explicit counting-measure / ℓ² corollary.
- `4afb18c`: iterated cube and whole-space mixed-derivative Sobolev bounds.
- `3d2aee4`: weighted bound with constant `(2π)^d`; radial weight `(1+Σ x_i²)^d`.
- `d12186a`: imaginary-shifted cube inequality, uniform in all shifts.
- `8a8bae6`: Euclidean-carrier segment/Riesz kernel bound and radial integrability/scaling.
- `fc9d4bb`: first-derivative Morrey estimate on the closed square, including the real-integral
  large-parameter bound. Real exponent `p=2P`, sufficient range `p≥20002` (`P≥10001`), `M≥1`.
  Coefficients are explicitly `2^p` and `(2 * (squareMorreyConstant q).toReal)^p`, with `q=p/(p-1)`;
  see the exact Lean statement.

All listed milestones have narrow builds passing with zero warnings.
The nine main Sobolev/Riesz results checked in `/home/scott/wt-scratch/an-sob/Axioms.lean`
depend only on `propext`, `Classical.choice`, `Quot.sound`.

## Volume work (`75b1903`)

Checked narrow builds: `SimplexVolume`, `HeapOrderVolume`, `TwoChainBound`.
The heap formula is valid for every relation on `Fin n`: its volume is the number of compatible
permutations times `D^n/n!`. Coordinate ties are proved null using a proper linear subspace.
Two chains have volume `D^(m+n)/(m! n!)`; arbitrary coordinate interleavings are represented by a
finite equivalence, and the comparison with the one-chain denominator loses at most `2^(m+n)`.
The exponential bound includes the necessary range `d≤z`; the all-index version assumes `x≥1`.

## Source distinctions / candidate errata

- TARGET L2330 says the displayed inequality applies “for any function”. Literally with coefficient
  one and `M=1` it is false. For example on the unit square `K(t,s)=1+t`, `P=1`, the left supremum
  is `4`, while the two right terms are `7/3+1=10/3` when the derivative norm is Euclidean/operator
  norm. The proved version displays constants and a sufficient large-`P` range. No source file edited.
- Scaling a localized two-dimensional bump shows why a large exponent is needed: at radius `r`,
  the two powered coefficients are `r^(-2)` and `r^(2P-2)`. Choosing `r=M^(-P/200)` gives the
  source powers for `P≥10001`.
- DH21 L2428 (10.5) itself has ordinary mixed derivatives. TARGET L2004 uses the shifted version;
  both have checked proofs, in an equivalent iterated-integral representation.
- The scalar/ℓ² interval APIs currently assume a globally `C¹` curve; the spatial cube APIs assume
  global smoothness. These are sufficient for the smooth source applications. The L² curve is
  smooth as an ℓ²-valued curve; a coordinatewise-to-ℓ² regularity bridge is not claimed.
- The factorial/exponential formula is not true for arbitrary `z<d`, `0<x<1` if `(z-d)!` is read with
  truncated natural subtraction; its true ranges are explicit in the Lean statements.

## Remaining

The DH21 Lemma 10.2 resonance-decay estimate is still unproved.
Checked: `OscillatoryInterval`, `TimeForest`, `TimeForestVolume`, `CauchyConvolution`,
`CauchyResonance`, `ResonantConvolution`.
The forest representation uses parent-first indices, ≤3 branching children, actual Bochner
integration over the heap domain, and a finite frequency recursion with a proved characterization.
The absolute-volume bound is separate from the unproved resonance-decay claim.
The convolution estimate preserves the two output centres `0,q` and the factor `⟨q⟩⁻¹`.
Next: smooth-cutoff Duhamel Fourier kernel; then connect the recursive analytic model to the actual
heap domain (nonnegative gaps require the feasible lower-endpoint construction).
Checked: `TimePrimitive`, `CutoffPrimitive`, `CutoffPrimitiveBounds`, `CutoffFourierDecay`,
`CutoffFourierFormula`, `CutoffTimeKernelBound`. The complete kernel bound is
`‖Kχ(a,τ,q)‖ ≤ Cχ ⟨q⟩⁻¹ (W(τ)+W(τ-q))`, `W(s)=(1+s²)⁻¹`, uniform `a∈[0,1]`.
Kernel, resonance convolution, forest frequency characterization and absolute-volume bound have
axiom checks showing only the three standard axioms (probe `KernelAxioms.lean` in scratch).
Remaining: spectral/Fubini assembly and the tree induction, including the feasible lower-endpoint
construction for gapped domains.
No completion or `READY` claim is made for the packet.
