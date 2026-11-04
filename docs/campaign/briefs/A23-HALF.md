# Packet A23-HALF: DH23 Lemma A.2(3) for γ > 1/2, and the refined basic count

Read `COMMON.md` first.

## Goal

Prove in Lean the γ > 1/2 branch of DH23 Lemma A.2(3) (`Revision_Submit.tex` L2050–L2091). DH23 only sketches it
(L2088–L2091). The independent referee wrote a complete paper proof:
`docs/research/case4-gamma-above-half-referee.txt`, item 4. Its saving is

`κ(γ) = min((2γ−1)/3, 1−γ)` up to log factors.

The proof uses:

- the bilinear count;
- a lattice-point bound for thin annuli (exponent 2/3 suffices);
- `estcross`.

This is the one new counting input of FINDINGS F75, which closes DH23 Prop 9.6 case (4) for γ ∈ (1/2, 1). It is needed
whatever the author decides on the γ range. The research note is `docs/research/case4-gamma-above-half.txt`, §8
("for Lean").

## What to prove

1. **The system {(1,2,3),(1,4,5)} of Lemma A.3(4) (L2106)**, with the two adjacent degree-3 endpoints of "T minus a
   bond" removed together. Prove it in both reparametrized forms:
   - the cyclic form `ζ = x + y − v − z`;
   - the anti-parallel form `ζ = x − v`.

   The bound is ≲ `L^{−γ₀ − κ(γ)}`, up to logs. State it with the γ-dependent saving κ(γ), not with 10η, so the lemma
   does not depend on η.
2. **The reparametrization identities** for all 16 sign patterns. The referee checked them by hand and by random
   tests.

## Inputs

The repo already has much of what this needs. **Search before writing anything.**

- **Landed counting lemmas:** `Foundations/CountLemmas/**`, including `countLemma_bound` and `atomCountLemma_bound`.
  `atomCountLemma_bound` carries the `k ≠ 0` hypothesis that the referee notes TARGET Lemma A.9 needs (cf. F43).
- **Estcross:** `Foundations/CountLemmas/Estcross*.lean`, or search for `estcross`.
- **Fixed-sum fibre bounds:** the improved annulus and fixed-sum fibre bounds (`Improved*`, with the circle exponent
  27/41).
- **Bilinear count and thin-annulus lattice bounds:** `Foundations/NTSP`, `WeylSums`, `NumberTheory`, `ApproxNT`.

## Where

- **Foundations:** on your branch, `WaveTurbulence/Foundations/CountLemmas/A23Half*.lean`, namespace
  `WaveTurbulence.CountLemmas`.
- **Worktree:** `/home/scott/WaveTurbulence-worktrees/torus-fourier`. Merge main first.

## Done

- No sorry, standard axioms only.
- A HANDOFF.
- Report `READY a23-half`.
