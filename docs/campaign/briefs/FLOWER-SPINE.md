# Packet FLOWER-SPINE (pre-freeze): the B1.12 `layergardenFlower` spine

Read `COMMON.md` first.

## Where things stand

With X3 closed, `main` rests on exactly two frozen-candidate statements:

- **B1.2 `layergarden`**: wt-cumul is building its spine (LG-SPINE, `/home/scott/wt-scratch/lg-spine`).
- **B1.12 `layergardenFlower`**: your flower-garden estimate (snapshot 9, `/home/scott/wt-scratch/waveb-snap-9/WaveB1-Flower.lean`).

## Goal

Prove B1.12 at its exact snapshot-9 type, from a minimal set of named, literally stated intermediate inputs. The
statement is `layergardenFlower_of_spine : FlowerSpineInputs → LayergardenFlowerGate`.

The source is TARGET `flowerest1`, L2279–L2305, the deterministic core. Its proof parallels the `layergarden` proof
(§§5–12) for flower gardens: canonical layered flower gardens, the stage-1 and stage-2 reductions, vines, ladders,
`lgmolect`, and the time-integral bounds.

## Rules

- **Share inputs with LG-SPINE.** Where TARGET's flower argument uses the same intermediate statement as `layergarden`,
  use wt-cumul's spine input **word for word**. Read its `SPINE.md` and `SpineInputs.lean`. Only add flower-specific
  inputs where the flower argument genuinely differs.
- **Inputs are literal source statements.** Inputs must be literal transcriptions of source statements, not convenient
  strengthenings. The spine itself does the assembly logic.
- **Keep the γ-sensitive inputs separate and explicit.** These are `lgmolect`, (finalcount1) and (finalsbest2):
  FINDINGS F69b/F73 show they fail for γ ≤ 1/2, and the author may restrict to γ ∈ (1/2, 1).

## Output

A `SPINE.md` table with one row per input: source lines, consumer step, and providing packet (or "unowned").

## Where

- **Scratch:** `/home/scott/wt-scratch/flower-spine/`, built on your FLOWER, X2 and X3 work.
- **Worktree:** `/home/scott/WaveTurbulence-worktrees/gauss-hc`. Merge main first.

## Done

- `layergardenFlower_of_spine` compiles, with no sorry and only standard axioms.
- Its type check against snapshot 9 passes.
- Report `READY flower-spine`.
