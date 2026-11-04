# PL1 working handoff — carrier interface

Status: **in progress**, 2026-11-04. This is the requested C2 instantiation interface, not a `READY pl1-core` claim. The couple analytic core, including canonical source agreement, is complete. Stage 1 still needs the tree ordered-boundary/phase assembly; Stages 2–3 remain open.

## Structural data

All declarations below are in `WaveTurbulence.Incoh`. No structure has an estimate or a conclusion-shaped field.

| declaration | fields / data | meaning for C2 |
|---|---|---|
| `LinkParameters d` (`LinkFactor.lean`) | `leftCenter`, `rightCenter`, `leftShift`, `rightShift : Mom d` | The two cutoff centers and two linear Fourier frequencies after localization. These are universally quantified analytic parameters, not garden assumptions. |
| `LayerLink d` (`LayerLink.lean`) | extends `LinkParameters d`; `leftLayer`, `rightLayer : ℤ`; `orientation : ℤˣ` | The integer layers of the two linked branching nodes and the chosen node's sign. |
| `Q : Fin n → LayerLink d` | an actual finite link family | C2 enumerates the code's links. Each link has two time coordinates `Fin 2`. |
| `RootCoordinates n r` (`RootCoordinates.lean`) | `restCount : ℕ`; `permutation : Fin (n * 2) ≃ (Fin r ⊕ Fin restCount)` | A finite permutation selecting the external/frozen vertex times. `r` defaults to `2` for the two couple roots. Boundary marginals may select more vertices. The measurable equivalence and its measure preservation are proved, not fields. |
| `I : Set (Fin n → Fin 2 → ℝ)` | `MeasurableSet I`; `I ⊆ Set.univ.pi (fun i => linkBox (Q i))` | The actual internal time-order domain. These are structural measurability and containment obligations, not analytic bounds. |

`linkBox Q = Icc ![Q.leftLayer,Q.rightLayer] ![Q.leftLayer+1,Q.rightLayer+1]`, with integer layers cast to reals. `LayerLink.IsIncoherent Q` is the literal inequality of those two integers. `incoherenceCount Q` is the cardinality of the filtered finite family; it is not an assumed kernel bound.

`RootCoordinates.rootVertex` and `rootLinks` compute the selected vertices and the links they touch from `permutation`. Their cardinality bound, root/internal unit-box decomposition, untouched-link independence and marginal bounds are proved. `RootCoordinates.linkDensity` is the actual integral of `normalizedLinkIntegrand` over the nonselected coordinates.

The layer-range premise is `∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D`. This bounds the actual frequency window. The analytic standing parameters are `d ≥ 3`, `0 < γ < 1`, positive small `η`, `0 < δ ≤ 1`, and a positive layer range `D`. The incoherence count is computed from `Q`; results needing nontrivial incoherence explicitly require `1 ≤ incoherenceCount Q`.

## Literal link and F62

`linkEpsilon x y = 1 - 1_{x=0} - 1_{y=0}` remains the **single-branching-node** coefficient. It takes values `1,0,-1`, matching C2's `epsXY_eq_cases`.

**The actual per-link coefficient is its square**, to match C2 `epsDec_eq_prod_links`: `linkWickFactor x y = (linkEpsilon x y)^2`, with values `1,0,1`. `linkAmplitude` uses this squared factor. The localized lattice factor is the literal sum of `linkAmplitude * WeylSums.e linkPhase` over the pair lattice. Its time frequency is `orientation * δ * L^(2γ) * (t_left-t_right)`.

F62 is the source defect at TARGET `(incohproof10)`: the product over all branching nodes contributes both equal endpoint coefficients of every link. The squared factor is required for exact instantiation. Mask removal uses the two coordinate axes **with the origin omitted**, retaining an `O(L^d)` correction. The F62 correction has been rebuilt through `CoupleExtension.lean` (`d240a9b`, corrected mask committed in `7943955`). The punctured-axis proof retains the same explicit `2(5L)^d` error bound.

The source normalization is literal: `(δ / (2 * L^(d-γ)))^(2n)`. A global unit sign/phase of the garden is not stored in these analytic data and may multiply the kernel without changing the norm.

## C2 consumption

The reported C2 packet is `/home/scott/wt-scratch/links`, with `src/LinksDraft/Incoh1.lean` and `HANDOFF.md`. Its relevant outputs are `incoh_relation`, `incoh_unimodular`, `linkCoords_surjective`, `node_linear`, `decEquiv`, and `epsDec_eq_prod_links`; tree link/layer results are available separately. They are not imported here from scratch, and no B2 draft or characterization stub is an analytic dependency.

The coupling from C2 to this analytic core needs:

1. enumerate the actual links and choose their endpoint time-coordinate ordering;
2. fill the two integer layers and the unit orientation;
3. identify C2's single-node epsilon with `linkEpsilon` and its paired product with `linkWickFactor`;
4. select root/boundary vertex coordinates by a finite permutation;
5. supply the actual measurable internal time domain and its unit-box containment.

The cutoff centers/Fourier shifts arise in PL1 localization and remain free in the core estimates. The leaf-function product, unimodular coordinate change and Fourier localization carrier for Stage 2 are not yet added here; the landed C2 scratch results are the intended inputs. No tree analogue of the couple unimodular theorem is assumed.

## Proven milestones and checks

Before F62, focused gated builds passed for the literal short- and long-time bounds, product decay, exact coupling cancellation, actual selected-density bounds, and the common root-density endpoints. Milestones include `ad41e46`, `ac012d7`, `197ab9a`, `a371bbf`, and `46898cd`. `nice -n 5 lake build WaveTurbulence.Foundations.Incoh.<Module>` was used, one targeted build at a time through `wt-throttled`; no whole-library or Mathlib rebuild was requested.

The scratch audit `/home/scott/wt-scratch/wke-l2s/pl1/AxiomsFrequency.lean` printed exactly `[propext, Classical.choice, Quot.sound]` for `exists_shortTime_box_bounds`, `exists_longTime_box_bounds`, `mixedFourierNorm00_interpolate`, and `eLpNorm_le_of_one_and_pointwise`. This audit will be repeated after the F62 rebuild and for the final assembled results.

The corrected-mask `RootDensityLp.lean` and `CoupleExtension.lean` now build, proving the physical interpolation and positive couple Fourier estimate. `/home/scott/wt-scratch/wke-l2s/pl1/AxiomsSquared.lean` rechecked the corrected mask, both frequency box bounds, root endpoints, physical Lp bound, couple Fourier bound, and mixed interpolation: every result uses exactly `[propext, Classical.choice, Quot.sound]`. Commit `88f1def` proves `cumulativeKernel_eq_setIntegral`, `cumulativeKernel_eq_localBoxIntegral`, `coupleExtension_agrees` on the full root box, and `exists_cumulativeKernel_timeRestriction_bound` with exponent `γ₁−100dη`. The focused `CoupleExtensionAgreement` build passed. The scratch audit `AxiomsCouple.lean` checked all four declarations: each uses exactly `[propext, Classical.choice, Quot.sound]`. The full core theorem, tree Fourier/derivative assembly, localization, and abstract `proplayer1` are not yet claimed proved. No `READY` milestone is claimed by this working handoff.
