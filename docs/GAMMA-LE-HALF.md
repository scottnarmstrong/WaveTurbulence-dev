# The range 0 < γ ≤ 1/2: what went wrong, and how it was repaired

*Status: the repaired proof is formalized in Lean. The Lean proof of Theorem 1.1 for the full range 0 < γ < 1, as
printed, is complete and was sealed on the main branch on 2026-11-09. Two independent audits of the sealed proof are
under way ([how it was checked](#8-how-it-was-checked)).*

This page is for readers who know the paper and want to know what changed below γ = 1/2. Erratum numbers (E1, E20, …)
refer to [ERRATA-AND-DEVIATIONS.md](ERRATA-AND-DEVIATIONS.md), decision numbers (D6, …) to
[DECISIONS.md](DECISIONS.md). Lean names are given relative to the namespace `WaveTurbulence`.

## In short

- Deng and Hani's *Long time justification of wave turbulence theory* (arXiv:2311.10082, "TARGET" below) states its
  main result, Theorem 1.1, for every scaling exponent 0 < γ < 1 (see the
  [README](../README.md#the-exponent-γ-and-the-values-that-matter-physically) for what γ means).
- **For 0 < γ ≤ 1/2 the printed proof has a gap.** It relies on a counting estimate from the companion paper DH23
  (Deng–Hani, *Derivation of the wave kinetic equation: full range of scaling laws*, arXiv:2301.07063),
  **Proposition 9.6**, and one case of that proposition is false in this range (erratum **E1**). The range contains
  **γ = 1/2, the "ballistic" scaling law** that Deng and Hani single out as physically natural.
- **The repair has three ingredients:**
  1. an enlarged family of *vines*, the **T-vines**, which absorbs the components on which Prop 9.6 fails;
  2. **Prop 9.6 re-proved** for γ ≤ 1/2 over the enlarged family;
  3. a corrected **"ghost" step** in the counting procedure (erratum **E20**), valid for every 0 < γ < 1.

  The rest of the proof, including the long "flower" estimate, carries over once every place that used γ > 1/2 has
  been checked again.
- **In Lean.** The frozen statement of Theorem 1.1, `main`, is the printed statement for 0 < γ < 1 on the square
  torus. It was written and approved on 2026-11-03, before the gap was known (D6), and it was never changed. Its proof
  uses only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## 1. The problem (erratum E1)

The proof bounds sums over large combinatorial objects called *molecules*, which encode the terms of the solution's
expansion. It proceeds in two stages.
- **Stage 1** finds special sub-structures called *vines* and splices them out. Their sums are bounded separately by
  the vine estimate (TARGET Prop `vineest`).
- **Stage 2** removes the remaining atoms one at a time (*cuts*), keeps an exact tally of the gains and losses, and
  finally bounds the components that are left. DH23 Prop 9.6 is that final bound.

Case (4) of the proof of Prop 9.6 (DH23 L1883–L1886) concerns components with two atoms of a certain kind ("β-atoms")
and claims that, after an enumeration, such a component "must be a vine". **That claim is false.** The smallest
counterexamples are a 4-atom block, three 5-atom blocks, five 7-atom blocks and a 9-atom block, and they repeat in an
explicit infinite family of molecules, the *necklaces*.

Why exactly γ ≤ 1/2: in the bad component the two β-atoms come from cuts with a small gap, of size about 1/L. The
energy constraints those atoms must satisfy have width δ⁻¹L^{−2γ}. When γ ≤ 1/2 this width is at least 1/L, so the
constraints are automatically satisfied, and the component's count is of order 1 instead of a negative power of L.
Prop 9.6 needs a negative power. For γ > 1/2 the width is smaller than 1/L, and a different argument closes the case
(F75 in E1). That argument is part of the formal proof for 1/2 < γ < 1.

What fails, for 0 < γ ≤ 1/2: DH23 Prop 9.6 (`lgmolect`), DH23 `kqmainest2`, TARGET `lgmolect` and TARGET
(finalcount1). The necklace molecules themselves are few, and a heuristic estimate puts their total contribution at a
fixed negative power of L.

Details, the explicit necklace, and the scripts that check it: [E1](ERRATA-AND-DEVIATIONS.md#e1--dh23-prop-96-lgmolect-case-4-is-false-for-0--γ--12).

## 2. The repair in one paragraph

The offending blocks behave like vines in every way that matters for the vine estimate: the hypotheses of TARGET
Prop `sumint`, which drive that estimate, hold for them exactly as for the vines drawn in DH23. So instead of
meeting them in stage 2, where Prop 9.6 fails, the repaired proof **treats them as vines in stage 1**: they are
collected, spliced out and bounded by the vine estimate. What reaches stage 2 then satisfies a corrected Prop 9.6.
The vine family used by the proof depends on γ:

| Range | Vine family 𝒱_γ | Lean |
|---|---|---|
| 1/2 < γ < 1 | the vines (I)–(VIII) drawn in DH23 (unchanged) | `Molecule.IsVineGamma` |
| 0 < γ ≤ 1/2 | vines (I) and (II), and the T-vines | `Molecule.IsVineGamma`, `Molecule.IsVineEnl` |

Every drawn vine (III)–(VIII) is a T-vine (`TVine.Struct.Drawn.drawnTVine`), so for γ ≤ 1/2 the family contains the
paper's. For γ > 1/2 nothing changes; the proof for that range is the one already formalized and audited
(`main_v2`).

## 3. Ingredient 1: T-vines

**Definition.** Let S be a block of a molecule with two joints. Delete the joints and reconnect their neighbours; the
result is the *closure* of S. Then S is a **T-vine** if
- no two atoms of S are joined by more than two bonds, and
- the closure reduces to the *doubled triangle* (three atoms, each pair joined by exactly two bonds) by repeating
  one move (DH23's (Y2)): remove two atoms joined by three bonds, each of which has exactly one other bond, and join
  their two other neighbours by a new bond.

The bead of the necklace counterexample is a 5-atom T-vine. Every T-vine has an odd number of atoms, at least 5. The
exact Lean text is `Molecule.IsTVine` in
[`WaveTurbulence/Foundations/TVine/Defs.lean`](../WaveTurbulence/Foundations/TVine/Defs.lean). It was approved before
any proof was written (D11) and is pinned by its hash, so that it cannot change silently (D16).

**What was proved about T-vines**, for all sizes:

| Result | Lean |
|---|---|
| The pieces of a T-vine and their shapes; the structure of a layer of vines (a spine, pendants and at most three ladders); the sub-objects of a vine | `TVine.Struct.pieceShape_holds`, `TVine.Struct.layervine_holds`, `TVine.Struct.subObjects_holds`, `TVine.Struct.cor116Single_holds` (`WaveTurbulence/Foundations/TVine/Struct/Final.lean`) |
| Every drawn vine (III)–(VIII) is a T-vine | `TVine.Struct.Drawn.drawnTVine` |
| A size bound, \|S\| ≤ 11 + 2·(number of deletable rungs), which reduces the structure theorems to finitely many base cases (T-vines with at most 13 atoms) | `TVine.Checker.sizeBound`, `TVine.Checker.generation` |
| The base cases, decided by a checker that is proved sound in Lean and run by `decide`, so that Lean's kernel checks every case (no `native_decide`, no external computation) | `TVine.Checker.pieceShapeBase`, `TVine.Checker.subObjBase`, `TVine.Checker.familiesBase` |
| Every T-vine has an explicit parametrization ("chart") of the form the vine estimate needs | `TVine.Chart.tvineChart_holds` |
| The vine estimate, TARGET Prop `vineest`, for chains of vines from 𝒱_γ, for every 0 < γ < 1 | `GammaLow.Famb.vineEstGammaHalfMK` |

For the drawn vines the formal proof uses a large catalogue of parametrization certificates (the separate library
`WaveTurbulenceVineParam`, decision D12). For T-vines the chart theorem replaces such a catalogue.

Sources: the three research notes on T-vines,
[1](research/gamma-le-half-repair-1-notes.md), [2](research/gamma-le-half-repair-2-notes.md) and
[3](research/gamma-le-half-repair-3-notes.txt), and the blueprint note
[`gamma-le-half-tvine-blueprint-notes.md`](research/gamma-le-half-tvine-blueprint-notes.md). Each has an independent
referee report; all are listed in [`research/INDEX.md`](research/INDEX.md).

## 4. Ingredient 2: Proposition 9.6 for γ ≤ 1/2

**Case (4).** With T-vines in the family, the enumeration claim of case (4) becomes true: a component of that kind is
a vine of 𝒱_γ (a vine (II) or a T-vine). Such a component has a large gap (Prop 9.5 for the enlarged family), and
the paper's own large-gap argument then gives the required bound.

**The other cases.** Every case of Prop 9.6, together with DH23 Props 9.4, 9.5 and 10.4 on which it rests, was
re-proved for 0 < γ ≤ 1/2 with every exponent explicit. This range is in one respect easier than γ > 1/2: the energy
window δ⁻¹L^{−2γ} is at least the lattice spacing 1/L, so every lattice count is a volume count, and no number theory
is needed. Two steps need a sharper counting bound at γ < 1/2 than the one the printed text cites. Both sharper
bounds follow from DH23's own Appendix A; they are recorded as exposition errata (E47, E48).

**In Lean.**
- `GammaLow.FinalCount.prop96_low_closed`: DH23 Prop 9.6 over 𝒱_γ for 0 < γ ≤ 1/2, all cases.
- `GammaLow.Close.finalCountGateLow_proved`: the whole final count for 0 < γ ≤ 1/2, i.e. TARGET (finalcount1),
  including the ghost repair of §5.

Source: [`gamma-le-half-counting-notes.md`](research/gamma-le-half-counting-notes.md) and its
[referee report](research/gamma-le-half-counting-referee.md).

## 5. Ingredient 3: the ghost step (erratum E20)

**The issue.** In stage 2 a *ghost* is an atom that was already cut at an earlier step and later lies on a triangle
that the procedure removes. DH23's per-step bound (Prop 9.4) does not cover triangles with ghosts (E20). For
γ > 1/2, a repair that charges each ghost's earlier gain at the triangle step works, under the condition
8η ≤ 2γ − 1 on the small parameter η. That condition is harmless there, because η is chosen after γ. For γ ≤ 1/2
the condition cannot hold, and the per-step bound does fail, by a small factor L^{4η+O(η²)}, when two ghosts with
large labels meet at a triangle.

**The repair**, valid for every 0 < γ < 1:
1. Two ghosts produced by the same removal never meet at a triangle the procedure removes: conservation of momentum
   over the removed object forces a zero gap at the third atom, and such a triangle is not eligible.
2. Otherwise the two ghosts were created at two different steps. Each such pair is classified in advance by the angle
   between the ghosts' gaps:
   - **transverse** pairs: the triangle step has enough room by itself, using both energy constraints;
   - **near-collinear** pairs (angle below L^{−6η}): the step that creates the later ghost counts its gap inside a
     narrow cone, which gains a power of L; part of that gain, L^{5η}, is set aside and spent at the triangle step.
3. These transfers cancel pair by pair, so the overall tally is unchanged. The procedure itself, its molecules and its
   budgets are unchanged too.

**In Lean.** For γ ≤ 1/2 the per-step bound is false, so the Lean statements bound the whole run at once:
- `GammaLow.FinalCount.Ghost.chainCoverLow'_holds` and `GammaLow.FinalCount.Ghost.chainCoverLowL'_holds`, for the
  final count;
- `GammaLow.Flower.H2.Ghost.chainCoverLowLE'_holds`, for the marked count inside the flower estimate.

Source: [`gamma-le-half-ghost-step-notes.md`](research/gamma-le-half-ghost-step-notes.md). Its independent referee
accepted it with minor repairs ([report](research/gamma-le-half-ghost-step-referee.md)), and two alternative
approaches, worked out separately, confirmed the conclusion.

## 6. The flower estimate for γ ≤ 1/2

TARGET's flower estimate (Prop `flowerest1`) has a printed proof that needed a substantial written completion (errata
E29–E46). That completion was first written for 1/2 < γ < 1. For the full range, every one of its 75 uses of γ was
located and checked again at γ ≤ 1/2:
- none fails;
- 51 hold verbatim;
- 13 hold with a different justification, written out in the note;
- the remaining 11 are uses of the vine family (handled by T-vines), the standing hypotheses themselves, inputs that
  ingredients 1–3 supply, and one superseded step that the completion does not use.

The marked version of stage 1 and of the final count then had to be redone over 𝒱_γ.
- `GammaLow.Flower.stage1MKGateLow`: the marked stage 1.
- `GammaLow.Flower.H2.finalCountGateLowMK_holds`: the marked final count.
- `GammaLow.Close.flower_low_closed`: the flower estimate for 0 < γ ≤ 1/2.

Source: [`gamma-le-half-flower-notes.md`](research/gamma-le-half-flower-notes.md) and its
[referee report](research/gamma-le-half-flower-referee.md).

## 7. How the full-range theorem is assembled

The proof splits at γ = 1/2, with γ = 1/2 itself in the low half. For γ > 1/2 it uses the sealed, audited theorems
`layergarden_v2` and `layergardenFlower_v3`. For γ ≤ 1/2 it uses the two new halves,
`GammaLow.Close.layergarden_low_closed` and `GammaLow.Close.flower_low_closed`. The glue lemmas
`GammaLow.Glue.wtPrefix_of_halves` and `GammaLow.Glue.wtPrefixP_of_halves` join the two halves (the split is
`by_cases h : 1 / 2 < γ`).

```text
γ > 1/2: layergarden_v2, layergardenFlower_v3      (sealed and audited)
γ ≤ 1/2: GammaLow.Close.layergarden_low_closed,
         GammaLow.Close.flower_low_closed            (new)
          │  GammaLow.Glue.*_of_low
          ▼
GammaLow.Close:        layergardenFlower_v4_full, layergarden_full, fixedpoint_full, propansatz_full, main_full
          │  (one-line provider per statement, WaveTurbulence/Provider/)
          ▼
frozen statements:     layergardenFlower_v4, layergarden, fixedpoint, propansatz, main
```

The frozen statements proved this way:

| Lean (frozen) | Paper | Frozen | Range |
|---|---|---|---|
| `main` | TARGET Theorem 1.1 | 2026-11-03 (D6) | 0 < γ < 1, as printed |
| `propansatz` | TARGET Prop `propansatz` | 2026-11-04 (D7) | 0 < γ < 1 |
| `fixedpoint` | TARGET Prop `fixedpoint` | 2026-11-04 (D7) | 0 < γ < 1 |
| `layergarden` | TARGET Prop `layergarden` | 2026-11-04 (D7) | 0 < γ < 1 |
| `layergardenFlower_v4` | TARGET Prop `flowerest1` | 2026-11-09 (D16) | 0 < γ < 1 |

The first four were frozen before the gap was found, and they were not changed. `layergardenFlower_v4` is the
already-audited `layergardenFlower_v3` without the hypothesis 1/2 < γ (D16). v3 itself is a corrected form of the
flower statement (E34, E41, E42; deviations in the errata file).

## 8. How it was checked

- **On paper.** Each research note was checked by an independent referee, who had not written it and set out first to
  refute it. All four were accepted with small repairs, which were applied in the Lean formalization.
- **The new statement.** `layergardenFlower_v4` was audited independently before it was frozen: it is faithful to the
  source and has no hypothesis beyond it.
- **Lean.** No `sorry` and no added axiom anywhere. `#print axioms` of each of the five final theorems in
  `WaveTurbulence/Foundations/GammaLow/Close/Final.lean` lists only `propext`, `Classical.choice` and `Quot.sound`.
  Each of the five was checked to have exactly the type of its frozen statement.
- **Sealing (2026-11-09).** Each frozen statement's placeholder proof was replaced by a one-line reference to its
  proof, and tooling checked that the statement itself did not change. Seal commits on main: `4558dd65`
  (`layergardenFlower_v4`), `2e2c16ef` (`layergarden`), `008e27f9` (`fixedpoint`), `6f4a03d2` (`propansatz`),
  `bfbb5546` (`main`).
- **Independent audits.** Two auditors who did not write the proof each audit all five statements: statement
  fidelity against the paper's source, hidden hypotheses, axioms, and a full replay of the proof in Lean's kernel.
  The audits are under way. Their records will be in [`audits/full-range/`](audits/full-range/README.md).

**What the formalization caught in our own work** (not errata of the paper):
- Our research note on the flower count proposed reserving a factor L² for each pending re-cut. The formalization
  showed that L² overshoots the budget of the marked count, and uses L^{3/2}, which fits for every γ
  (`WaveTurbulence/Foundations/GammaLow/Flower/FinalMK/H2/Bank.lean`). This corrects our note, not the paper.
- Two lemmas of the earlier formal proof, `Vine.not_isVC_five_of_branching` and
  `Vine.not_isVC_five_or_seven_of_erase_connected`, rely on the fact that no drawn vine has 5 or 7 atoms. T-vines with
  5 and 7 atoms exist, so the lemmas fail for the enlarged family. They were not carried over, and the arguments that
  used them were redone.

## 9. Where things are in Lean

All paths are under `WaveTurbulence/Foundations/`. Together, the two areas below have about 315,000 lines in about
1,670 modules.

| Directory | Contents |
|---|---|
| `TVine/Defs.lean` | the definition of T-vines and of 𝒱_γ (pinned text) |
| `TVine/Core`, `TVine/Struct` | the combinatorics of T-vines and the structure theorems |
| `TVine/Checker` | the verified checker for the base cases |
| `TVine/Chart` | the charts (parametrizations) of all T-vines |
| `GammaLow/Fama` | stage 1 over 𝒱_γ (`GammaLow.Fama.stage1ReductionGateLow`) |
| `GammaLow/Famb` | the vine estimate over 𝒱_γ |
| `GammaLow/Famc` | the vine-containing objects, the spliced count, `layervine`, `subpro` |
| `GammaLow/FinalCount` | the final count for γ ≤ 1/2: DH23 Props 9.4–9.6 and 10.4, and the ghost step |
| `GammaLow/Flower` | the flower estimate for γ ≤ 1/2: marked stage 1 and marked count |
| `GammaLow/LGLow` | `layergarden` for γ ≤ 1/2 |
| `GammaLow/Glue`, `GammaLow/Close` | the split at γ = 1/2 and the five full-range theorems |

## 10. History

- **2026-11-04.** The failure of DH23 Prop 9.6 for γ ≤ 1/2 was found and confirmed by an independent referee (E1).
  The formal target was restricted to 1/2 < γ < 1 by new versions of the affected statements (`main_v2` and others;
  D9, D10). The original full-range statements stayed frozen, and research on a repair began.
- **2026-11-05.** After three rounds of independent refereeing, the T-vine definition was approved (D11).
- **2026-11-08 to 2026-11-09.** Theorem 1.1 for 1/2 < γ < 1 (`main_v2`) was sealed and passed two independent audits
  ([records](audits/v2-chain/README.md)).
- **2026-11-09.** The remaining research was written and refereed: the ghost step, the counting, the flower re-check
  and the T-vine blueprint. The full-range flower statement `layergardenFlower_v4` was frozen (D16). The γ ≤ 1/2
  formalization was completed and landed on main, and the five full-range statements were sealed (D17).
