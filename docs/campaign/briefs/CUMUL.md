# Packet CUMUL — complex Gaussians, complex Isserlis, cumulants

Read `COMMON.md` (same directory) first.
Worktree: `/home/scott/WaveTurbulence-worktrees/cumul`, branch `w/cumul`.
Files you own: `WaveTurbulence/Foundations/Gaussian/ComplexGaussian.lean`, `WaveTurbulence/Foundations/Gaussian/Isserlis*.lean`,
`WaveTurbulence/Foundations/Cumulant/**`.

## Goal (in this order; commit after each)

1. `ComplexGaussian.lean`: the DRAFT `stdComplexGaussian` (verbatim below) and its API: probability measure; for
   `g` with this law, `𝔼 g^a (conj g)^b = a! · [a = b]` (all `a b : ℕ`), integrability of all such monomials,
   `𝔼|g|² = 1`, rotation invariance (`e^{iθ} g` has the same law). Existence: on `Ω = (ι → ℂ)` with
   `Measure.infinitePi (fun _ => stdComplexGaussian)`, the coordinates are iid with this law (for any countable `ι`,
   in particular `ι = Fin d → ℤ`).
2. `Isserlis.lean`: **DH21 Lemma A.2** (`isserlis0`, DH21 TeX
   `/home/scott/wave-turbulence/references/src-2104.11204/Inventiones-Final_Version.tex` L2797–L2807): for an iid
   family `η : ι → Ω → ℂ` with law `stdComplexGaussian`, indices `k : Fin n → ι` (not necessarily distinct) and signs
   `ζ : Fin n → Bool`: `𝔼 ∏_j η_{k_j}^{ζ_j} = ∑_{𝒫} ∏_{{j,j'} ∈ 𝒫} [k_j = k_{j'}]`, the sum over perfect matchings
   `𝒫` of `Fin n` pairing opposite signs. Choose a clean Lean carrier for "partitions into pairs with opposite signs"
   (e.g. bijections from the `+` positions to the `−` positions, which is what the proof counts) and prove the
   equivalence with the source's pairing formulation if you choose a different carrier.
3. `Cumulant/`: the DRAFT `cumulant` (verbatim below), then
   - the inversion formula **TARGET (eqncm2)** (TARGET TeX
     `/home/scott/wave-turbulence/paper/source/WKE-Longer_times_Final_arXiv.tex` L571–L577): for nonempty `s` and
     every needed product integrable, `∫ ∏_{j∈s} X_j dμ = ∑_{𝒫 : Finpartition s} ∏_{A ∈ 𝒫} cumulant μ X A`
     (Möbius inversion on the partition lattice; note μ need not be a probability measure — TARGET takes
     expectations "assuming an event F", i.e. against `P.restrict F`);
   - **TARGET Lemma `propertycm`** (L2343–L2351, (eqncm3)): cumulants of products `Y_i = ∏_{j ∈ S_i} X_j` over
     pairwise disjoint `S_i` equal the sum over partitions of `⋃ S_i` that are *irreducible* (no proper subfamily
     `A` with `⋃_{i∈A} S_i` a union of blocks) of the products of cumulants. State irreducibility as the source does.
   - Gaussian cumulants: for the iid complex Gaussian family, `cumulant P (fun j => η_{k_j}^{ζ_j}) s = 0` unless
     `|s| = 2` with opposite signs, and `= [k_j = k_{j'}]` in that case;
   - the symmetry vanishing used in TARGET (gaugeinv) L567–L570: if the joint law of `(X_j)` is invariant under
     `X_j ↦ e^{iζ_jθ} X_j` for all θ, then moments and cumulants vanish unless `∑ ζ_j = 0` (an abstract lemma over
     a finite measure `μ`; the translation version with `∑ ζ_j k_j = 0` likewise).

Maps: `/home/scott/wave-turbulence/maps/DH21.md` (DH21-isserlis0, DH21-correlcal), `T-part1.md` (defcm, propertycm,
gaugeinv). Mine Scott's repos (Critical2DKPZ, KPZ "cumulants", DOZZ, RegularityStructures-dev) for cumulant/Wick code.

## DRAFT definitions (verbatim; namespace `WaveTurbulence`, `open MeasureTheory ProbabilityTheory`)

```lean
/-- The law of a centered normalized complex Gaussian `g` (`𝔼 g = 0`, `𝔼|g|² = 1`, circularly
symmetric): real and imaginary parts independent `N(0, 1/2)`. -/
def stdComplexGaussian : Measure ℂ :=
  ((gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2))).map Complex.equivRealProd.symm

/-- The cumulant `𝕂((X_j)_{j ∈ s})` of TARGET Def `defcm` (eqncm), with expectations taken against a measure `μ`
(`μ = P.restrict F` for "assuming the event `F`"): the sum over all partitions `𝒫` of `s` of
`(-1)^{|𝒫|-1} (|𝒫|-1)! ∏_{A ∈ 𝒫} 𝔼 ∏_{j ∈ A} X_j`. -/
def cumulant {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι] (μ : Measure Ω) (X : ι → Ω → ℂ)
    (s : Finset ι) : ℂ :=
  ∑ P : Finpartition s, (-1 : ℂ) ^ (P.parts.card - 1) * ((P.parts.card - 1).factorial : ℂ) *
    ∏ A ∈ P.parts, ∫ ω, ∏ j ∈ A, X j ω ∂μ
```

## Stop conditions

Done: `READY cumul`. Blocked > ~1 hour on one ingredient: `STOPPED cumul: <reason>` with a proposed route.
