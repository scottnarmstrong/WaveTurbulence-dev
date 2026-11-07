# DEGEN-VINE handoff (GAP.degenerate.vine, F21; ruling R13)

Scratch: /home/scott/wt-scratch/degen-vine, namespace `WaveTurbulence.DegenVine`. READY degen-vine (see the end).

## 1. Determination: what is the correct statement, and is TARGET L1844-L1846 wrong?

**Source readings.** TARGET L1844-L1846 (Step 3 of `vineest`): "once `r = k_{u21}-k_{u22} = k_{u1}-k_{u11} != 0`, we may replace
`epsilon_x` in (tildeK2) by 1, since if any `epsilon` factor is not 1, this would imply some restrictions on the relevant
variables (such as `x_j^i = 0` or `y_j^i = 0`, or `u_1+u_2-u_3 = 0` etc.), which allows us to sum over these variables trivially
and gain an extra power `L^{-0.1 gamma_0}`".  The same sentence in DH23 L1448 ("... we can sum over them trivially, gain a power
using `L^d << L^{2(d-gamma)}`, and treat the rest of the variables using the same arguments below") and DH23 §10.5 =
`extradegen` (L1979-L1989; item (1): "any degeneracies occurring in these expressions only produce lower order remainder terms
(for example, they correspond to `x_j = y_j = 0` ... in Lemma sumintest1)").

**Verdict (F21 / ε): CONFIRMED as a GAP, not a false claim.**  The step is correct only if "sum these variables trivially" means
*only the restricted variable(s)*, and "the rest" is estimated by the `sumint` argument itself (DH23 L1448 says exactly this).
Read literally as TARGET's "trivial summation" of the whole restricted sum it fails for large `M`:
trivial summation of `M-1` free variables costs `L^{(M-1)d}` against the budget `L^{M(d-gamma)}`, i.e. a loss `L^{M gamma - d}`
(positive exponent as soon as `M > d/gamma`; e.g. `d = 3`: `M >= 7` at `gamma = 1/2`, `M >= 4` at `gamma = 0.9`; the vines of
the source have `M` up to `N_1^4`).  And the "rest of the variables" claim is *not* a corollary of the `sumint` statement as a black
box:
* the indicator `1[x_v = 0]` is not an admissible weight: its `S^{30d,30d}` norm is `~ L^{31 d}` (scale `1/L`);
* deleting the rung (datum surgery) breaks `T_1` square/unimodular and `Admissible` (ii)/(iii) (a variable is a difference of two
  rows; neighbouring variables use the deleted rungs' labels);
* the gain `L^{-0.1 gamma_0}` is **not needed** for (vineest2): only a bound by `C^M` times the main bound is.

**What is true and proved here (new, complete in Lean).**  Every degenerate indicator is a *character mixture*: for integer
`c : VIdx -> Z`, `h : Fin 4 -> Z`, `1[sum_v c_v X_v + sum_k h_k E_k = 0] = int_{[0,1]^d} e^{2 pi i L <a, y>} da`, which splits into an
output scalar `u(a,E)` (unimodular) and an *input character* `prod_v e^{2 pi i <L c_v a, X_v>}` (Fourier inversion on `Z_L^d`; mass 1).
The `sumint` kernel estimate is **uniform in the input modulation `nu`**
(`SumintSigned.exists_source_static_power_bound` is `forall p nu r`), and `XNorm00` is a sup over the output `v`, so output-dependent
unimodular scalars are free.  Hence, redoing only the top recombination
(`SumintSigned.XNorm00Restr_source_of_kernel_bound`) with the multiplier, the lattice sum weighted by ANY character mixture of mass
`K` obeys the `sumint` bound with the constant multiplied by `K`.  `epsilon_{k1 k2 k3} = 1 - 1[k2=k1] - 1[k2=k3]`
(`epsCoef_eq_one_sub`), so `epsilon` over `n` nodes is a mixture of mass `3^n`.

**Correct statement** (Lean: `clockedBoundEps_of_restr`, `clockedBoundDef_of_restr`): for the V5 engine hypotheses (restriction norms
`beta_rho` of the clocked weights, `Admissible` family, `M <= N_1^4`, ...), with `epsilon(x) = prod_{i in I} eps(k_i^1,k_i^2,k_i^3)`
where each label `k_i^j` is a weight-row momentum (`kVec`/`lVec`) or a boundary vector `E_c`:
`XNorm00Restr(2 eta^8)(outBox)(outSet)(clockedExprEps) <= (cc_eta+1) * ofReal(3^{|I|} * engineConst * maxPar^{eta^6} *
sumintRHS0 * prod_rho L^{weightExp g_rho}) * prod_rho (Cfs * beta_rho)` -- the V5 main-term bound times `3^{|I|}`.  The degenerate part
alone (`epsilon - 1`, supported where some node is degenerate, `exists_degenerate_of_prod_ne_one`) has the same bound with `3^{|I|}+1`.
`|I| = |U|` (regional nodes of the chain) `<= M + O(1)`, so `3^{|I|}` is absorbed into `C_1` exactly as the engine constants.
No gain `L^{-0.1 gamma_0}` is claimed or needed; TARGET's sentence should be reworded (see 6).

## 2. Files (all in /home/scott/wt-scratch/degen-vine/DegenVine/, 21 modules, 2456 lines, max 229 lines)

Light (no `sumint` proof closure; importable together with V5's flat engine modules):
* `Eps` : `epsCoef = 1 - 1[b=a] - 1[b=c]`, support, `prod_eps_sub_one` (defect expansion), `|eps - 1| <= 2`.
* `CharMix` : `CharMix S d` (finite measure `mu`, input frequencies `zeta`, output scalars `u`, `|u| <= 1`), `val`, `mass`, `norm_val_le`, `charOf_add`.
* `SignedExprMix` : `signedExprMix`, the statement `SumintMixSigned`.
* `MixAlgebra` : `one/neg/add/mul` with `val_*` and `mass_*`.
* `MixIndicator` : `integral_fourierChar_unit`, `indicator`, `val_indicator` (exact: `= if n = 0 then 1 else 0` when `affVal = latticePoint L n`), `mass_indicator = 1`.
* `EpsMix` : `epsMom`, `AffRef`, `epsNode` (mass 3), `val_epsNode`, `exists_prod_mix`, **`exists_eps_mix`** (mass `3^card`), `epsMom_latticePoint` (bridge to `epsCoef` on integer labels: V4's `clRegionalEpsilon`).
* `SumintMixDoubled` : `SumintMixSignedDoubled`, `sumintMixSignedDoubled_of : SumintMixSigned -> SumintMixSignedDoubled`.
* `ScaledSumintMix` : `SumintMixDoubledAt`, `ScaledSumintMixAt`, `scaledSumintMixAt_of`, `signedExprMix_reweight_scale`.
* `ClockedExprMul` : `clockedExprMul`, `signedExprMix_modeDatum`, `clockedExprMul_hasSum` (interchange with the multiplier).
* `ClockedBoundMix` : `mode_bound_mix`, `clockedBoundMix`.  `ClockedBoundMixRestr` : **`clockedBoundMix_of_restr`** (= `VineEstS3.Eng.clockedBound_of_restr` + multiplier, factor `Mx.mass`).
* `Split` : `clockedExprWith`, `clockedExprWith_split` (`K_e = K_main + K_{e-1}` under absolute summability), `norm_clockedExprWith_le` (two-term Minkowski).
* `Degenerate` : `labelRef`, `labMom`, `epsOf`, `clockedExprEps`, `clockedExprDef`, **`clockedBoundEps_of_restr`**, **`clockedBoundDef_of_restr`**.

Heavy (closure on `SumintSigned.*`, sumint-signed-fresh; do NOT import with the light V5 modules, see 4):
* `MixLocalized, MixNorm, MixCounted, MixRecomb` : the multiplied localized/counted ambient extension, its agreement with the multiplied lattice sum, mass bound,
  norm bound `XNorm00_mixLocalized_le`, `XNorm00_mixCounted_le`, and **`XNorm00Restr_mix_of_kernel_bound`** (the analogue of `XNorm00Restr_source_of_kernel_bound`, same hypothesis `hkernel` uniform in `(p, nu, c)`).
* `MixSumint` : `exists_mix_restriction_interpolated_bound`, `exists_mix_sumint_bound`.
* `SumintMix` : `sumintMix` (prefix form, SumintSigned datum).  `SumintMixSigned` : `sumintMixSigned : SumintMixSigned` (V4 datum + core signs, via `SumintSigned.ofOrig`).  `SumintMixFinal` : **`sumintMixSignedDoubled : SumintMixSignedDoubled`, unconditional**.

## 3. Approach (proof)
1. `DH23 §10.5`/TARGET reduce to: `sum_x eps(x) F(x)` with `eps` supported-modified on affine subspaces.  Instead of restricting sums, write `eps` as a
   character mixture; then `sum_x m(E,x) W(x) int phase = int dmu(a) u(a,E) [sum_x chi_a(x) W(x) int phase]`.
2. `exprMix` is `D.expr` with the multiplier.  `mixLocalized` = finite-sum form of `localizedSourceExtension` with `m(E,x)` inserted; `mixLocalized_eq_integral` writes it as a `(xi,a)`-mixture of the plain `weightedSourceExtension` at the shifted modulation
   `nu(xi)+zeta(a)` (Fubini + `weightedSourceExtension_eq_sum` + `normalized_source_coefficient_expansion`); `XNorm00_integral_weightedSourceExtension_le` (generic measure space) gives the bound `mass * (coefficient mass) * B`.
3. The counted recombination (labels) is copied from SumintSigned with `|m| <= mass` in the integrability/mass steps; final numerics copied from `SourceSumintBound` (mass is a global factor).
4. Engine: `ScaledSumint`/`ClockedExpand2`/`ClockedBound`/`ClockedBoundRestr` re-proved with the multiplier (text-adapted; the only changes are `signedExprMix ... Mx`, the factor `Mx.mass`, and `M.val` carried through the mode interchange).
5. `exists_eps_mix`: node mixture `1 - ind(k2-k1) - ind(k2-k3)` (mass 3), products by `exists_prod_mix`; the lattice property of label differences uses `sum_k h_k = 0` (coefficient sums 1 of rows/boundary) and `E_c in wBar + Z_L^d` (members of `outSet`).

## 4. Checks run (exact)
* Fresh rebuild of the closure, topological order, new dir `build-fresh`, exit codes in `logs-fresh/EXIT.txt`: all 21 modules `exit 0`; no `error`/`sorry` in any log.
* `#print axioms` (validation/AxHeavy.lean, AxLight.lean): `sumintMixSignedDoubled, sumintMixSigned, sumintMix, exists_mix_sumint_bound, XNorm00Restr_mix_of_kernel_bound, clockedBoundEps_of_restr,
  clockedBoundDef_of_restr, clockedBoundMix_of_restr, exists_eps_mix, CharMix.val_indicator, epsMom_latticePoint, clockedExprWith_split, norm_clockedExprWith_le, prod_eps_sub_one`: all `[propext, Classical.choice, Quot.sound]`.
* Hygiene grep (`sorry|admit|axiom|opaque|unsafe|maxHeartbeats|set_option`) over DegenVine/*.lean: no hits.  No file > 1500 lines.
* Exact-type check: there is no pinned Lean statement for GAP.degenerate.vine; `sumintMixSignedDoubled_iff : SumintMixSignedDoubled <-> WTPrefixA SumintMixDoubledAt := Iff.rfl` (ScaledSumintMix) compiles, so the unconditional heavy theorem is literally the hypothesis `hdb` of the engine; with `Mx = CharMix.one` (value 1, mass 1) `SumintMixDoubledAt` is V5's `SumintDoubledAt` (V5's `clockedBound_of_restr` is the `Mx = one` case: same proof).

## 5. Interface for V5 / vineest assembly (what V5 must supply; typing data, no new analytic obligation)
1. `hdb : SumintMixDoubledAt A P` -- from `sumintMixSignedDoubled` (module `SumintMixFinal`), exactly as `SumintFinal` supplies `SumintDoubledAt`.
2. The ε identification: `clRegionalEpsilon G U kappa = epsOf D L l1 l2 l3 x E` (as reals) for E in `outSet`, where `l1 l2 l3 : I -> Row D + Fin 4` select, for each regional node `v in U`, which weight row (pair-leaf `kVec`, branch `lVec`) or boundary vector is its child `j`.
   Ingredients exist in V4: `assembly_pair_momentum`, `assembly_branch_momentum` (decoration value = `kVec`/`lVec` at `sumintBoundary`), and `DegenVine.epsMom_latticePoint` (`epsMom (base + latticePoint L n_j) = epsCoef n_j`).  A child outside `U` that is neither a pair leaf nor a branch row of the chain is a boundary vector (`E_c`).
   (If some child label is NOT of this form, the hypotheses of `exists_eps_mix` need an `AffRef` for it: any integer-affine label with coefficient sum 1 works unchanged.)
3. `|I| = |U|` and absorb `3^{|I|}` into `C_1` (`|U| <= M + 1`; V5 to confirm).
4. Everything else is the V5 engine's own `hclock/hres/hcont/...` (unchanged).
Then Step 3 with ε: apply `clockedBoundEps_of_restr` in place of `clockedBound_of_restr`; no separate degenerate term.  (`Split` gives the explicit main + defect decomposition `K_eps = K_main + K_{eps-1}` and its Minkowski inequality, if V5 prefers to keep V5's `clockedBound_of_restr` for the main term; it needs absolute summability of `x |-> ||int clockedIntegrand||`, which V5's `clockedExpr_hasSum` interchange proves internally.)

## 6. Finding note for the ledger (TARGET L1844-L1846, CANDIDATE erratum -> CONFIRMED as a gap with repair)
* Location: TARGET L1844-L1846 (Step 3 of `vineest`; also the same sentence DH23 L1448 "once we confirm r != 0, we replace epsilon by 1").
* Quote: "we may replace `epsilon_x` in (tildeK2) by `1`, since if any `epsilon` factor is not `1`, this would imply some restrictions on the relevant variables ... which allows us to sum over these variables trivially and gain an extra power `L^{-0.1 gamma_0}`".
* Problem: not an error in the claim `|degenerate part| <~ main bound`, but the justification "trivially" is insufficient: restricting a variable does not change that the other `M-1` variables must still be estimated with the oscillatory gain `L^{-gamma}` each (trivial summation: `L^{(M-1)d}` vs `L^{M(d-gamma)}`); the omitted step is a restricted/modulated `sumint`.  The gain `L^{-0.1 gamma_0}` is not needed.
* Repair (proved here): `epsilon` is a character mixture of mass `<= 3^n`; `sumint` (whose kernel estimate is uniform in the input modulation) holds for mixture-weighted sums with the constant times the mass.  Suggested rewording: "`epsilon_x` is a bounded combination (`<= 3^{n}` terms) of indicators of affine constraints on `x`; each indicator is an average of linear input phases, to which the proof of Proposition sumint applies verbatim (its kernel bound is uniform in the linear phases), so `epsilon` may be replaced by `1` at the cost of the constant `3^n <= C^M`."

## 7. Uncertainties / deviations
* The classification of which label (row/boundary) each regional child is (interface item 2) is V5/V4 typing data not proved here; the theorem is stated with the labels as parameters.
* Import clash (scratch environment): the heavy `SumintSigned.*` closure and V5's flat modules (`Words`, ...) define the same names and cannot be imported in one file (`validation/Both.lean` fails: `import Words failed`); the engine modules (light) take `SumintMixDoubledAt` as a hypothesis, the unconditional heavy theorem lives in `SumintMixFinal` (same split as V5's `SumintFinal`).  At landing both are on the same consistent set of modules.
* The multiplier acts at the doubled step `2 delta` as in V5; `engineConst` etc. are V5's.  No gain `L^{-(d-2gamma)}` for the restricted rungs is claimed (it needs pair-specific analysis; not needed).
* Adapted-from sources (read-only, sha256 at first read): COPIED-SHA256SUMS.

READY degen-vine
