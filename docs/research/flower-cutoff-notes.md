# research-flowercut — FLOWER-CUT study (for wt-orch), 2026-11-06

Scope: the cutoff clauses of `layergardenFlower_v2` (B1.12, D10). The question: are they true and provable by a
route the formalization can take? Posture: refute first. Nothing outside this directory was edited.

Pinned inputs (copies + SHA256SUMS in `pinned/`): FS9 Gates/Defs, lg-spine-u Stage1Interface, Stage1Gate and
SourceSplicedKernel, research-flower NOTES. Main at 657e877 (frozen defs read with `git show main:`). TARGET
L2257–L2338, L1955–L2095 (redvine2/3, ladderl1old, ladderl1new, finalsbest1/2), L1596–L1660 (sumint), L1429–L1481
(twists, LF twists), L886–L960 (coherence, canonequiv). DH21 L2680–L2760 (Cor 11.3 `extragaincor`, the Prop 12.2
argument with (Rdecompose)). DH23 L1992–L2024.

## 0. RECOMMENDATION: NEEDS-SUCCESSOR

The frozen cutoff clauses are not provable by any route the formalization has, and TARGET's argument does not
apply to them.
- The frozen weights are `φ_M(max)`: Lipschitz, non-factorizing, and kinked wherever two leaf norms (or two stem
  Ω's) tie.
- TARGET says "by a smooth cutoff function" (L2283, L2285), and DH21 (cited at L2299 and L2321) builds the cutoff in
  product form: a dyadic partition per leaf, with `M₀` the largest index (DH21 L2731), and per-node partitions of the
  stem Ω's (L2735).
- That product form is
  `Ψ_j(y) = ∏_a χ₀(y_a/2^jL) − ∏_a χ₀(y_a/2^{j−1}L)` (and `Ψ_0 = ∏_a χ₀(y_a/L)`).
  It is smooth, it factorizes through every slot, and it has every property the consumers use (Lean-checked, §8).
- So the freeze mis-transcribed TARGET's intended cutoff. This is an erratum in the freeze, not in TARGET.

The proposed successor is `layergardenFlower_v3`.
- Its text is `layergardenFlower_v2` verbatim, with `flowerSum` replaced by `flowerSumP`, which uses product-form
  `cutWeight1P` and `cutWeight2P` (§5).
- The uncut clauses are literally unchanged (`flowerSumP_none : … = flowerSum … none none …`, `rfl`, checked).
  FS9 can keep working on them.

Provability of v3:
- **cut1 (M₁):** provable, via a polynomial-coefficient (Markov/Lagrange) extraction from a twist-compatible
  uniform family (§6). The exponents close. It needs one new capability: smooth weights on the inter-layer
  "attached-root" bonds (BOND-WT). No faithful M₁ cutoff can avoid this (§6.4).
- **cut2 (M₂):** this stays a research item (FC4), in any form. There is no evidence that the product form is
  false, so this is not a STOP. If FC4 fails, the consumer (fixedpoint Part 2) is what breaks. That would be a
  STOP-level escalation then, not now.

## 1. The frozen text (transcribed)

Statement `layergardenFlower_v2`, clause (1), binders `cut1 cut2 : Option ℕ`:
- premise `(∀ j₂ ∈ cut2, ∃ j₁ ∈ cut1, ((2:ℝ)^j₁ * P.L)^10 ≤ ‖latticePoint P.L n‖)`;
- conclusion `‖flowerSum … cut1 cut2 ζ t s n n'‖ ≤ jbr(k−ζk')^{−4Λ_{p+1}Pm} · L^{c(100d)^3 Pm} · δ^{2νN} ·
  (cut1.elim 1 fun j₁ => ((2^j₁ L))^{−80 d Pm}) · (cut2.elim 1 fun j₂ => if ∀ j, pat j = .plain then (2^j₂ L)^{−Pm/9}
  else 1)`, with `c = 1` for all-plain patterns and `c = 2` otherwise.

`flowerSum` (Defs/FlowerSum.lean) puts these into `kernelKgen`'s decoration weight `wt`:
`(cut1.elim 1 fun j₁ => LG.cutWeight1 p P.L j₁ k) * (cut2.elim 1 fun j₂ => LG.cutWeight2 P.L j₂ k) * (dagger…)`.

The frozen weight definitions:
- `cutWeight1 p L j₁ k = ∏ j : Fin w, dyadicCut L j₁ (sup over {a : a.1.1 = j ∧ IsTopLeaf p a ∧ ¬IsFlowerNode a}
  of ‖k a‖₊)`.
- `cutWeight2 L j₂ k = ∏ j, dyadicCut L j₂ (sup over {b : GBranch, b.1.1 = j ∧ OnStem b.toNode ∧ ¬IsFlowerParent b}
  of ‖omegaNode G k b‖₊)`.
- `dyadicCut L j x = if j = 0 then χ₀(x/L) else χ₀(x/2^jL) − χ₀(x/2^{j−1}L)`.
- `χ₀(x) = smoothTransition(2 − 2|x|)`, which is non-increasing in |x| and strictly decreasing on 1/2 < |x| < 1.

So per tree, the weight is `φ_M(max_a y_a) = min_a χ₀(y_a/M) − min_a χ₀(2y_a/M)` for j ≥ 1. This is a joint function
of all the top-leaf momenta (or all the stem Ω's) of the tree, with a kink at every tie.

## 2. TARGET's treatment, re-derived

- **(1), L2294, the M₁ gain.** TARGET says the M₁^{−80dP} "comes in the same way" as the decay ⟨k−ζk'⟩^{−4ΛP}.
  - That decay is exact algebra. k−ζk' = Σ±k_ℓ holds for every decoration, so ⟨k−ζk'⟩^{2m} is a polynomial in the
    leaf momenta. Each monomial is redistributed to the leaf profiles (FS9 `weightCost`).
  - The cutoff has no such identity. The intended mechanism (DH21 L2731) is per-leaf: the leaf ℓ carrying the
    annulus piece χ_{M₀}(k_ℓ) has profile χ_{M₀}·F, with S-norm ≲ M₀^{−λ}‖F‖_{S^{·,·+λ}}.
  - The budget closes. We need 40d per tree, and λ = 40d at a layer-p leaf requires
    F_p ∈ S^{40d, 80d + 8Λ_{p+1}} ⊂ S^{Λ_p,Λ_p}. This holds since Λ_p = 40d·Λ_{p+1} ≥ 80d + 8Λ_{p+1} when
    Λ_{p+1} ≥ 40d (p < 𝔇), and φ(δp) is Schwartz (WTParams.φ, norm C₂).
- **(6), L2299, the M₂ gain.** TARGET fixes one stem node n_j per tree with |Ω_{n_j}| ∼ M₂. The other cutoffs "play
  no role", which is the telescoped product form. The gain comes from the oscillation in t_{n_j}: integrate t_{n_j}
  first and count the Ω values (L^{20d}), as in DH21 Cor 11.3 (gain M^{−1/9}M₀^{5d}).
  - Twist invariance of the stem Ω's is (7), L2300. It needs |k| ≥ M₁^{10} and the M₁ support: SG twists cannot
    split the stem.
- **DH21's construction (L2731, L2735).** 1 = Σ_R χ_R(k_ℓ) for each leaf separately, and M₀ = max_ℓ R_ℓ. Summing
  over tuples with max R_ℓ = M₀ gives exactly Ψ_{M₀} above, since Σ_{R'≤R} χ_{R'} = χ₀(·/R) telescopes. The Ω
  cutoffs are done the same way, per stem node. DH23 L2021 and TARGET L2321 inherit this ("Prop 12.2 of DH21",
  "Corollary 11.3").
- **Consumer (fixedpoint Part 2, L2318–L2331).** The cutoffs are used for:
  - the partition Σ_{M₁,M₂} X_{M₁M₂} = X;
  - support: all non-flower leaves |k_ℓ| < M₁, and all stem Ω's (≠ f^pr) ≤ M₂, for the finite (k,k') count, the
    same-sign stem, `finitelem`, and the stem-shift invariance;
  - the gains: M₁^{−80dP} and M₂^{−P/9}, which pay for (M₁M₂)^{C₀} representatives, M₂^{P/100} from Sobolev in (t,s),
    and M₁^{20dP}.

## 3. Why the frozen weights cannot be carried (the obstruction)

These are structural failures. They do not depend on the Dirac or on FS9's particular gate.
1. **Regular objects (the first Stage-1 step).** The skeleton reduction (redkg → redvine, T L1955) replaces each
   regular couple Q at a skeleton leaf pair by K*_Q(t,s,k_ℓ), a function of one bond momentum.
   - In a layer-p tree, the leaves of a collapsed regular couple are top leaves. `min_a χ₀(‖k_a‖/M)` couples them
     with every other top leaf of the tree, so the summand does not factor through K*_Q at all.
   - The product form factors: Q's leaves just get the profile g·F_p (leafwise REG chain).
2. **LF-twist cancellation.** The unit LF twist replaces the coherent T(u2) and Q(u23,u0) by other coherent objects
   (Def lftwist). The cancellation then compares coherent approximants (Props proplayer3/4). Those exist for product
   inputs (a modified profile), not for weights that couple the internal leaves to the outside.
3. **Slots.** RepresentsInt averages products of the following:
   - per-leaf profiles (C^{40d});
   - per-bond edge amplitudes (`SNorm (30d) 0 ≤ 1`, unit-ball support);
   - hinge amplitudes, which may be arbitrary bounded functions, but only of hinge-incident bonds, and each hinge
     costs L^{η^7} plus a ladder split;
   - decoration restrictions.

   An average, with bounded mass, of products of uniformly C^1 factors is C^1. `φ_M(max)` is not C^1 at ties
   (χ₀' ≠ 0 on (1/2,1)). Even on the lattice, interpolating a gradient jump of 1/M at spacing 1/L needs m-th
   derivatives of order L^{m−1}/M, far above 1 for m = 30d.
4. **Stage 2 Poisson (sumint).** Ladder-rung sums need the amplitude W to have ‖Ŵ‖_{L¹} bounded. A min-type W has
   only |ξ|^{−2} Fourier decay across the kinks, so the weighted L¹ norm is infinite.

Candidate routes from the brief:
- **Exact partition into product cutoffs: impossible.** A finite sum (or bounded average) of products of smooth
  factors is smooth, and min_a χ₀ is not. The layer-cake identity
  `χ₀(max/M) = ∫ ∏_a 1{y_a < uM} μ(du)` (μ = −dχ₀) is exact, but its factors are sharp indicators. Those fail
  points 2–4 above (the twist Taylor step needs smooth profiles; Poisson needs smooth amplitudes).
- **Positive majorant: fails.** The kernel is oscillatory, so |Σ_κ w K| ≤ Σ_κ W K needs K ≥ 0.
  `w ≤ C M^{−40d}Σ_a⟨k_a⟩^{40d}` is true pointwise but useless.
- **Comparison with the uncut clause: fails.** There is no monotonicity, and min ≠ product
  (`frozen_ne_product`, §8).
- **Soft-min smoothing: fails.** An ε-error needs derivatives ≲ ε^{1−m}M^{−m}, and ε can only reach about 1/L, which
  is useless against absolute bounds.

Truth of the frozen clause: unknown. It is plausibly true, but proving it would need new analysis (Lipschitz joint
weights through regular-object asymptotics, twist approximants and Poisson summation) with no source. This is not
a STOP: no falsity evidence, and the successor is what TARGET means.

## 4. Consumer compatibility (what the successor must keep)

From main's drafts (X3DyadicReduction, X3DaggerExpansion, X3KerInv, X3DerivFl, X2E FlowerSumTops, V2Chain
FixedpointS/GateTypes), the consumers use exactly these properties:
- 0 ≤ w ≤ 1;
- HasSum over j = 1 (the M₁ and M₂ decompositions);
- `≠ 0 → every non-flower leaf < 2^j L` (`flowerKernelGen_cut1_eq_zero`, `lt_of_dyadicCut_ne_zero` uses);
- `some stem |Ω| ≥ 2^j L → cut2 = 0` (`treeCut2_eq_zero_of`);
- cut1 depends only on the leaves, and cut2 only on the stem Ω's (`treeCut1_stemShift`, and `hcut2` in X3KerInv);
- the garden weight is the product over trees of the tree weights (X2E identity).

The product form has all of these. The first three are Lean-checked (§8), and the last three hold by definition.
The frozen `fixedpoint_v2` statement contains no cutoff. Only its proof chain (GateTypes copy of B1.12) and the
non-frozen X-level drafts change.

## 5. Successor text (exact Lean, frozen style; names are proposals)

```lean
-- Defs/ProdDyadicCut.lean
/-- **Product-form dyadic cutoff** (T L2283, L2285 "by a smooth cutoff function"; DH21 L2731): a dyadic
partition per entry, cut at the largest index: `Ψ_0 = ∏_a χ₀(y_a/L)`,
`Ψ_j = ∏_a χ₀(y_a/(2^j L)) − ∏_a χ₀(y_a/(2^{j−1} L))`. They sum to `1`; `Ψ_j ≠ 0` forces every `y_a < 2^j L`
and, for `j ≥ 1`, some `y_a > 2^j L / 4`. -/
noncomputable def prodDyadicCut {ι : Type*} (L : ℝ) (j : ℕ) (s : Finset ι) (y : ι → ℝ) : ℝ :=
  if j = 0 then ∏ a ∈ s, chi0 (y a / L)
  else ∏ a ∈ s, chi0 (y a / (2 ^ j * L)) - ∏ a ∈ s, chi0 (y a / (2 ^ (j - 1) * L))

-- Defs/LayeredGardenCutWeight1P.lean   (namespace LayeredGarden, same variables as cutWeight1)
open Classical in
/-- The `M₁` weight, product form (T L2283, L2294; DH21 L2731): per tree, `Ψ_{j₁}` of the norms of the
non-flower top leaves. -/
noncomputable def cutWeight1P (p : ℕ) (L : ℝ) (j₁ : ℕ) (k : GNode LG.garden.tree → Mom d) : ℝ :=
  ∏ j : Fin w, prodDyadicCut L j₁ (Finset.univ.filter fun a : GNode LG.garden.tree =>
    a.1.1 = j ∧ LG.IsTopLeaf p a ∧ ¬ LG.IsFlowerNode a) (fun a => ‖k a‖)

-- Defs/LayeredGardenCutWeight2P.lean
open Classical in
/-- The `M₂` weight, product form (T L2285, L2299; DH21 L2735): per tree, `Ψ_{j₂}` of the `|Ω_𝔫|` over the
stem branching nodes other than `𝔣^pr`. -/
noncomputable def cutWeight2P (L : ℝ) (j₂ : ℕ) (k : GNode LG.garden.tree → Mom d) : ℝ :=
  ∏ j : Fin w, prodDyadicCut L j₂ (Finset.univ.filter fun b : GBranch LG.garden.tree =>
    b.1.1 = j ∧ LG.OnStem b.toNode ∧ ¬ LG.garden.IsFlowerParent b)
      (fun b => |omegaNode LG.garden k b|)

-- Defs/FlowerSumP.lean: `flowerSum` verbatim (same binders, same carrier, same kernelKgen call) except the weight
--   (fun k => (cut1.elim 1 fun j₁ => LG.cutWeight1P p P.L j₁ k) *
--     (cut2.elim 1 fun j₂ => LG.cutWeight2P P.L j₂ k) * (dagger.elim 1 fun c => LG.sibWeight c k))

-- Theorems/LayergardenFlowerV3.lean: `layergardenFlower_v2` verbatim, `flowerSum` → `flowerSumP`
--   (full text type-checked in probe/FlowerCut.lean, theorem `layergardenFlower_v3`).
```

Docstring paragraph for v3: "Versioned successor (ruling D__): the M₁, M₂ cutoff weights are TARGET's smooth
cutoffs in DH21's product form (`prodDyadicCut`); `cutWeight1`/`cutWeight2` (φ of a maximum) are not smooth and do
not factor through the regular-object reduction. Clauses without cutoffs are unchanged (`flowerSumP` agrees with
`flowerSum` there by `rfl`). v2 stays frozen and open."

Proposed D-entry (standing authorization applies, so record and go; keep the statement audit):
> D__ — FLOWER-CUT: `layergardenFlower_v3` with product-form cutoffs `prodDyadicCut`, `cutWeight1P`,
> `cutWeight2P`, `flowerSumP` is the anchor for the B1.12 cutoff clauses. `layergardenFlower_v2` stays frozen;
> its uncut clauses are identical. The fixedpoint_v2 proof chain (GateTypes, FixedpointS) moves to v3, and the
> X-level drafts (X2Kernel `treeCut1/2`, FlowerTop `treeCut1K/2K`, X3*, X2E FlowerSumTops) move to the product
> form. Freeze erratum: `cutWeight1`/`2` mis-transcribe TARGET's smooth cutoff (DH21 L2731); TARGET gap
> E-F5′ (§9).

## 6. Proof route for v3 and the constants

### 6.1 cut1: Markov extraction from a uniform family

Write g_R(k) = χ₀(‖k‖/R) and φ_M = g_M − g_{M/2} ≥ 0 (support ‖k‖ ∈ (M/4, M)), and M = 2^{j₁}L with j₁ ≥ 1.
(j₁ = 0 has no lower support, so its gain L^{−80dP} comes from slack. See 6.3.)
1. **Split per tree.** A_j = A_j^p (layer-p leaves) ⊔ A_j^att (attached roots: lower-layer children of layer-p
   nodes). Then Ψ^{(j)} = T1 + T2 with:
   - T1 = [∏_{A^p} g_M − ∏_{A^p} g_{M/2}] · ∏_{A^att} g_M;
   - T2 = ∏_{A^p} g_{M/2} · [∏_{A^att} g_M − ∏_{A^att} g_{M/2}].
2. **T1 by coefficient extraction.** T1 = (Π(1) − Π(0))·∏_{att} g_M, where Π(z) = ∏_{a∈A^p}(g_{M/2} + zφ_M)(k_a).
   - The flower sum with weight Π(z) is a real polynomial of degree ≤ D_j ≤ 6N_{p+1}+3 in z (per tree, so 2P
     variables). Each z-coefficient c_m has m annulus leaves.
   - Lagrange at D+1 equispaced nodes in [0,ρ]: |c_m| ≤ (4e)^D ρ^{−m} sup_{[0,ρ]}|p|. The identity behind the
     m = 1 term is `hasDerivAt_prod_affine` (§8).
   - Take ρ = (M/4)^{40d}/D. At |z| ≤ ρ the profile (g_{M/2} + zφ_M)F_p has
     S^{40d,40d+8Λ} norm ≤ C‖F_p‖_{S^{40d,80d+8Λ}}(1 + 1/D), so the product over the leaves is ≤ e·C^{#leaves}.
   - Hence |T1-part| ≤ Σ_{m≥1} ρ^{−m}(4e)^D·B_unif ≤ 2D(4e)^D (4/M)^{40d} B_unif per tree.
3. **T2 by an auxiliary input-leaf cutoff.** On supp T2, some attached root has ‖k_a‖ > M/4. Then some input leaf
   below a has ‖k_ℓ‖ > M/(4n_a) ≥ M' := M/(4n_max). Hence T2 = T2·(1 − ∏_{ℓ ∈ input leaves of tree j} g_{M'}(k_ℓ)),
   exactly.
   - 1 − ∏(1 − ψ), with ψ = 1 − g_{M'}, is again a sum of coefficients of the uniform family
     ∏_ℓ(1 + zψ(k_ℓ)) (profiles of every layer ≤ p, decay Λ_q ≥ Λ_p).
   - Same extraction: the gain is (M')^{−40d} = (4n_max)^{40d}M^{−40d}, and n_max ≤ 3N_{p+1}^4 + 1 is
     polylog in L.
   - The factor [∏_{att} g_M − ∏_{att} g_{M/2}] is two uniform bounded bond-weight terms. No decay redistribution
     at attached roots is needed.
4. **The family is twist-compatible.** Per tree, every layer-p leaf (or every input leaf) gets the same profile, and
   every attached-root bond gets the same smooth g.
   - LF twists keep layers.
   - The coherent objects that an LF twist replaces lie in one layer (Def defcoh: linked branching nodes share a
     layer; canonequiv (ii) then puts their paired leaves there too; to verify in FC3). So they see a uniform
     profile, and the coherent approximants exist (with profile gF_p; FS9's internal δ^{8νN} slack is per the
     research-flower NOTES §5).
   - At bond level: a unit twist keeps the molecule and the bond momenta, and changes only u2's parent bond. So at
     every layer-p atom, the set of "top bonds" (bonds to lower-layer children, and leaf bonds) is preserved. I
     checked this by hand on the cross-layer case (u3 in layer p; u4, u2 below), where the multiset at v3 is
     unchanged.
   - In the all-layer-p case, the top-leaf momenta that move (k(v2–v4) → k(v2–v3), a shift by r) sit at the
     replaced Q(u23,u0). That is the same root-momentum shift the uncut cancellation already absorbs.
   - Needed: FT-TREE, i.e. LF twists keep the garden tree of every top leaf. This is plausible from
     `FamilyOperation.output_topOrder`, but not proved.

### 6.2 Constants (cut1)

- Per tree, the gain is 2D(4e)^{D_j}·(4n_max)^{40d}·4^{40d}·M^{−40d}. The gain is per tree, so the TARGET budget is
  40d per tree.
- Over 2P trees this is M^{−80dP}·[4^{80dP}(8 n_max D)^{80dP}]·(4e)^{ΣD_j}.
- (4e)^{ΣD_j} ≤ (4e)^{2N+2P}. It is absorbed by δ^{νN} slack, since δ ≪_ν 1 and FS9's internal δ^{8νN} beats the
  stated δ^{2νN}.
- 4^{80dP}(8n_max D)^{80dP} ≤ L^{P}. It is absorbed by the L^{(100d)^3P} slack, since the internal flower losses are
  L^{O(d)P}.
- So the clause's M₁^{−80dP} closes with c = 1 or c = 2 unchanged.

### 6.3 cut2: research (FC4), with constants if TARGET (6) goes through

- Telescope the per-tree product. One annulus node b_j has |Ω| ∈ (M₂/4, M₂). The other stem nodes carry χ₀(Ω/M₂)
  or χ₀(2Ω/M₂).
- **Upper cutoffs.** χ₀(Ω_c/R) = ∫χ̂₀(τ)e^{iτΩ_c/R}dτ, i.e. a time offset τ/(πδL^{2γ}R) of node c's phase, averaged
  with mass ‖χ̂₀‖_{L¹}.
  - This is smooth in α-space, where TARGET's finalsbest2 route is harmless.
  - Momentum-space rough: stem momenta are ≈ k with |k| ≥ M₂^{10}. So in Stage 2 they must enter as time offsets,
    not edge amplitudes.
- **Gain.** Integrate in t_{b_j} first. This gives 1/(δL^{2γ}Ω_{b_j}) times boundary terms in which b_j merges with
  its stem parent or child. Those are two-node stubs at a free time, close to design C's stubs and the
  dParent/dChild patterns.
  - Counting Ω values costs L^{20d}.
  - Per tree: min(1, L^{20d+O(1)}/M₂) ≤ (L^{C}/M₂)^{1/18}, i.e. M₂^{−P/9}·L^{CP/9} in total. This is absorbed by the
    L^{(100d)^3P} slack if the internal bound is ≤ L^{(100d)^3P − CP/9}.
  - For j₂ = 0 (and j₁ = 0) the stated gains L^{−P/9} (and L^{−80dP}) come purely from slack. TARGET's real losses
    are about L^{500dP} ≪ L^{(100d)^3P}.
- **Open.**
  - Stem nodes inside regular trees on the stem. DH21 Cor 11.3 (a) uses the explicit regular-chain structure
    (maincoef). In the layered REG chain this means Ω-weights or offsets on lone-leaf-path nodes.
  - The merged-time boundary terms.
  - V5/vines with stem atoms inside.
- Twist invariance: TARGET (7) (needs the M₁ support and |k| ≥ M₁^{10}). This is fine for the product form.

### 6.4 Why BOND-WT is unavoidable (for any faithful M₁ cutoff)

- The consumer needs `w ≠ 0 → every leaf of the X-tree < M₁`. X's leaves are the arguments of a_k(p).
- In the moment expansion, a leaf becomes either a layer-p pair (a profile) or the root of an attached cumulant
  garden G' ∈ G_p (an internal node of the big layered garden).
- So the weight must depend on internal-node momenta k_a. A cutoff on deeper input leaves is not definable at the
  X level.
- Cross-layer time constraints are automatic, since t_a < q+1 ≤ p < t_u. So K_G factorizes as top-level kernel ×
  ∏ K_{G'}. But cross-layer twists prevent a black-box treatment of the G'.
- Inside regular objects, things simplify: chain-node momenta equal the object's external momentum, and inner-couple
  roots are pair momenta. A bond weight there becomes an external weight or an input at an internal pair position.
  Inside CL blocks or V5 vines it stays a genuine internal bond weight.
- TARGET (1) "in the same way" is silent on this. That silence is the TARGET gap.

## 7. Packets (sizes are honest estimates)

- **FC0 FREEZE-V3** (wt-orch).
  - Work: the four defs and the anchor above, a provider stub, a review page and the D-entry, plus a statement
    audit (second key).
  - Size: ~200 lines; 0.5 session plus a 0.5-session audit. Do it now.
- **FC1 CONSUMER-REWIRE** (Sonnet).
  - Work: X2Kernel `treeCut1/2` and FlowerTop `treeCut1K/2K` move to the product form. X3DyadicReduction,
    X3DaggerExpansion, X3KerInv and X3DerivFl swap lemmas (the probe's `prodCut_*` lemmas are drop-in). Re-prove
    the X2E FlowerSumTops/identity, and move the GateTypes and FixedpointS text to v3.
  - Size: 0.5–1k lines; 1–2 sessions. Can start right after FC0.
- **FC2 MARKOV-REDUCTION** (Opus).
  - Work: the v3 cut1 clause from a UNIFORM-FAMILY gate (6.1–6.2): polynomial-coefficient extraction (Lagrange,
    in Mathlib), the per-tree T1/T2 split, the auxiliary input-leaf cutoff, and the constants.
  - Size: 1–1.5k lines; 2–3 sessions.
- **FC3 UNIFORM-FAMILY + BOND-WT** (Opus; research first).
  - Work: the flower bound for per-tree uniform z-families of input-leaf profiles, plus uniform bounded smooth
    inter-layer top-bond weights. Its obligations:
    - FT-TREE;
    - bond-level twist invariance (6.1 item 4);
    - regular objects (chain/pair-momentum reduction, 6.4);
    - V5 vine kernels with internal bond weights;
    - Stage-2 edge amplitudes (`SNorm 30d` after rescaling by C^{#bonds}).
  - Size: 3–6k lines; 6–10 sessions; moderate research risk. Merge it with research-flower's design-C packets P1
    (excision: weights at anchored sibling slots become outer coefficients) and P3 (FLOWER-TWIST: FT5/FT6 are
    replaced by bond-level invariance + FT-TREE).
- **FC4 FLOWER-M2** (Opus, research with STOP authority).
  - Work: the v3 cut2 clause (6.3).
  - Size: research 2–4 sessions; implementation to be estimated after the research (likely 3–6k).
  - If FC4 fails, the fixedpoint Part 2 union bound over k has no substitute (§2). Escalate then.
- **Order.** FC0 → FC1 now. FC2 once FS9's uncut gate shape is fixed. FC3 together with design C. FC4 in parallel.
  None of these blocks the uncut clauses.

## 8. Lean checks (transient; probe/FlowerCut.lean, sha in probe/SHA256SUMS, log logs/FlowerCut.log)

Run: `cd <repo> && nice -n 5 lake env lean …/probe/FlowerCut.lean`. Exit 0 in ~75 s
wall, no maxHeartbeats. The only `sorry` is the successor anchor `layergardenFlower_v3`, which is intentional. All
other declarations depend only on propext, Classical.choice and Quot.sound.

Checked:
- `prodCut_nonneg` and `prodCut_le_one`.
- `sum_prodCut` (telescoping to ∏χ₀(·/2^J L)) and `hasSum_prodCut` (Σ_j Ψ_j = 1, for y ≥ 0, L > 0).
- `lt_of_prodCut_ne_zero` (upper support) and `exists_gt_of_prodCut_ne_zero` (lower support for j ≥ 1, the source of
  the gain).
- `frozen_ne_product`: two leaves at 3L/4 give c = χ₀(3/4) ∈ (0,1) for the frozen form and c² for the product
  form.
- `hasDerivAt_prod_affine`: the z-coefficient of ∏(g_a + z h_a) is the marked-leaf sum.
- `cutWeight1P`, `cutWeight2P` and `flowerSumP` against main's frozen defs. `cutWeight1P_support` is the per-tree
  consumer support, and `flowerSumP_none` (rfl) shows the uncut clauses are unchanged.
- The full `layergardenFlower_v3` statement type-checks.

Not checked in Lean:
- the non-differentiability of φ(max) at ties (argued from χ₀' ≠ 0 on (1/2,1));
- the Lagrange coefficient bound;
- FT-TREE and bond-level twist invariance;
- everything in FC3 and FC4.

## 9. Errata candidates

- **E-F5′ (refines E-F5).**
  - *Freeze erratum:* `cutWeight1`/`cutWeight2` = φ_M(max) is not TARGET's "smooth cutoff". The intended object is
    DH21's product partition (L2731, L2735).
  - *TARGET gaps:* (i) in the layered setting the M₁ cutoff falls on attached-garden roots (internal nodes), so (1)
    is not "the same way" as the leaf decay. (ii) In (6), the upper Ω-cutoffs at the other stem nodes, and the
    boundary terms of the t_{n_j} integration, are not discussed. Stem nodes inside regular trees need DH21 Cor 11.3
    (a)'s regular-chain argument.
- **Exposition.** The j₁ = 0 and j₂ = 0 gains (L^{−80dP}, L^{−P/9}) carry no mechanism. They are slack in
  L^{(100d)^3P}. This is harmless, but any formal proof must reserve that slack.
