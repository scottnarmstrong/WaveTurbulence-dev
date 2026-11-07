# R11: missing time dimensions in the plain-kernel interface

The requested construction cannot satisfy the current flower gate's plain positive-order `Stage1Piece.Sound` together with its bounded-mass `RepresentsInt`. This is an obstruction to the auxiliary spine interface, not a counterexample to TARGET's flower estimate.

## An explicit source example

Use the existing `WaveBProbes.flowerGarden` (`pinned/CoreProbes.lean`, lines 123–137): two ternary corollas, root signs (+,−), left children marked as flowers, middle children paired across the trees, and right children paired across the trees. All layers are zero. The imported theorem `flowerGarden_canonH` proves `IsCanonH 1` for this garden. It has order 2, and each initial tree has order 1, so it is an X flower with no attached lower gardens. Take the plain pattern, no cutoffs, no dagger weight, k=0, k'=(1,1,1)/L, and 0<s<t<1. The flower sign relative to its root is +1.

Both roots are flower parents. Hence the two factors δ(t_root−s) remove **all** time integrations. The following exact identities are proved in this packet:

- `corolla_all_parents`, `corolla_fixed`, `corolla_no_free_times`;
- `corollaDecoration`: an actual integer (0,1)-decoration in dimension 3, with labels in each tree
  root=0, left=1, middle=2, right=1 (each label means the constant vector);
- `corolla_eps`: its original epsilon product is 1;
- `corolla_phase`: the two signed phases at time s multiply to 1, with no phases removed;
- `corolla_plain_timeIntegral`: the literal free-coordinate integral in `kernelGenLeavesTerm` at this decoration is 1, independently of t and s.

This is nondegenerate: epsCoef(1,2,1)=1, and 1−2+1=0. It does not use the all-equal Wick degeneracy. Choose the same positive Schwartz input profile at each input leaf. For every decoration, the paired corollas have equal resonances and opposite signs, so the phases cancel; their epsilon factors multiply to a square. The garden zeta is i·(−i)=1. Every summand is nonnegative and the displayed decoration gives a strictly positive one. The summable garden value is therefore a constant a>0 independent of s and t. Fix L, all other admissible parameters, and the input profile, and let s=t/2 decrease to zero. The root weight and every loss/cutoff factor of the gate are fixed in this limit. Take N=2 and parameters with N_1≥2, as allowed by the prefix.

The last paragraph's positivity/summability argument is mathematical evidence; this packet does **not** contain a Lean theorem computing the whole infinite decoration sum or negating `FlowerStage1At`.

## What the gate permits instead

`pinned/SourceSplicedKernel.lean` lines 49–80 integrates over **all** branches of a plain G_sb. There is no fixed-time-node field in `SplicedKernelData`. Its only time-dependent amplitude data are unit-modulus frequency exponentials. Edge and hinge amplitudes depend on momenta; `SplicedAmplitudeBounds` bounds their norms by 1 and their spatial supports by unit balls.

At p=0, `Sound.layer_le` forces all branch layers to be zero. For common exterior time t≥0, the time domain is a subset of [0,t]^(order G_sb). This packet proves the exact inequality

    ‖splicedTimeIntegral G D L γ δ base z‖ ≤ t ^ G.order

as `norm_splicedTimeIntegral_le`, uniformly in the frequency choices. It also proves `norm_average_splicedTimeIntegral_le`: any frequency superposition of total variation M is bounded by M·t^(order G). Thus a finite frequency partition or Fourier averaging cannot remove the time-volume factor.

For the full normalized kernel, the unit-ball supports leave at most B(L,d) possibilities per bond, uniformly in the centres. A plain decoration is determined by its bond labels and the prescribed root labels. The amplitudes and epsilon/gap factors have norm ≤1. Consequently, for fixed L,d and order≤2, the whole normalized spliced kernel is bounded by B'·t^(order G_sb). This is a finite lattice-counting observation, not a theorem newly formalized in this packet.

`Sound.order_pos` requires order G_sb≥1. Hence each kernel is O(t). The gate's integral mass bound is independent of t and s: with N=2, the possible orders, hinge counts, and class/piece counts are uniformly bounded by its `Stage1Counts`; the g_sk,b_sk factors can only decrease the mass for L≥1. Summing the pieces would give a≤C·t for all sufficiently small t, with one finite C independent of t. The elementary contradiction is Lean-checked as `no_uniform_time_mass_bound`.

This also explains the zero-order issue: pairing the two flowers as suggested in TARGET's footnote gives the regular (1,1) mini-couple. Reducing that regular component can leave a zero-order skeleton, but `Sound.order_pos` excludes it. Keeping a positive-order skeleton instead retains the unwanted integrated time coordinate(s).

## Two routes checked

1. **Fix parent resonances and remove their phases (TARGET L2295).** This is a valid step in estimating a fixed-time kernel, but it leaves the time coordinates fixed. `corolla_fixed_timeIntegral` proves the result is still 1 even with all parent phases removed. A finite L-power frequency loss does not supply the missing t^(-1) (or t^(-2) for retaining both branches).
2. **Pair flowers and reuse the ordinary skeleton/splicing machinery.** Pairing repairs marked-leaf typing but does not replace a trace by an ordinary integral. Full regular reduction gives the excluded zero-order case; retaining positive order is subject to the checked shrinking-volume estimate. Momentum-only bounded amplitudes cannot encode a Dirac time trace.

This meets the explicit STOP condition in the brief and R11. No gate has been weakened or changed. No `flowerStage1PieceOf`, complete `Sound`, or `Represents` theorem is claimed.

## Other interface issue to retain on the audit list

TARGET L2261 and L2287 expressly omit irreducibility for flower gardens. After pairing flowers, a disjoint union of two of the above corolla pairs is a legitimate width-four input with disconnected plain completion. S2a/S4's existing Sound construction requires a prime irreducible skeleton and produces a connected garden. Componentwise assembly is therefore another issue the auxiliary flower interface must account for. This secondary point is not formalized here and is not needed for the R11 stop.
