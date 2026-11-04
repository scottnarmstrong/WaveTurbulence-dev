# Escalation F69b: a false intermediate statement in DH23 (and TARGET) for γ ≤ 1/2

Prepared 2026-11-04 for Scott. This is a decision for the author. Nothing in the campaign is blocked while it is
pending.

## What was found

- **The false statements.** For **0 < γ ≤ 1/2**, the following are false as stated:
  - DH23 Prop 9.6 (`lgmolect`, `Revision_Submit.tex` L1820);
  - TARGET's restatement of it (L2192–L2197);
  - DH23 `kqmainest2` (L1681–L1690);
  - TARGET (finalcount1) (L2114).
- **What is not claimed.** The main theorems are **not** shown to be false. Only this chain of intermediate statements
  fails.

### The counterexample: the necklace N_m

- **Structure.** N_m is a cycle of m "T-beads" closed by one bead carrying two degree-3 atoms. A T-bead is a triangle of
  double bonds, with both copies of one double bond subdivided by the two β-atoms.
- **Admissibility.** N_m comes from a genuine prime, non-degenerate couple. In TARGET it is a canonical layered couple
  in 𝒞₁ (all nodes in layer 0) satisfying requirements (a)–(f).
- **The cutting algorithm.**
  - N_m has no vine-like objects.
  - Steps 1, 2 and 4 of DH23's cutting algorithm never touch it.
  - In every Step-3 order, T-beads become case-(4) components with V_α = 0, V_β = 2.
- **The count.**
  - Each tiny-gap T-bead contributes 𝔄₀ ≥ c, independent of L. The argument needs 𝔄₀ ≲ L^{−η²}.
  - For γ ≤ 1/2 the β-atom constraint is automatic. DH23's own Lemma A.2(1) gives no gain there.
  - With m of order η⁻⁶ beads, the count exceeds the right side of `kqmainest2` by a positive power of L.
  - TARGET (finalcount1) fails once 4η⁶(5m+4) > 3(d−γ).

### Where DH23 goes wrong

- **The error.** At L1885 ("an enumeration shows 𝕄₀ must be a vine"). This rests on DH23 Lemma `ylem1` (L1937), which
  is itself false.
- **Why ylem1 fails.** Its proof assumes every (Y)-reduction ends by removing a triple bond. For the T-bead, the
  reduction ends at the triangle of double bonds, with no such step. DH23's own introduction (L579ff) says that
  triangle has 𝔄 ≈ 1.

### How it was established

1. A prover found a kernel-checked counterexample to `ylem1` (FINDINGS F69).
2. An investigator showed our vine templates are faithful and that `ylem1` itself is false
   (`docs/research/ylem1-investigation.md`).
3. A research agent, trying to close the resulting gap at L1885, found the necklace
   (`docs/research/dh23-prop96-case4.md`).
4. An independent adversarial referee tried every route to refute it and confirmed it with its own code
   (`docs/research/dh23-prop96-referee.txt`).

The scripts are in `/home/scott/wt-scratch/prop96-case4/` and `/home/scott/wt-scratch/prop96-verify/`.

### Related points

- **γ < 2/3 (Q-bead).** If vine (II) is read literally (two double bonds, as drawn in Def 5.1), "Q-bead" necklaces break
  the same four statements for all **γ < 2/3**.
  - DH23's vine (II) parametrization (L1421) is consistent with a one-double-bond vine (II), but does not define it.
  - Whether DH23's vine cancellation still works in that case is unchecked.
- **Possibly more.** DH23 `kqmainest1` (L1633) and TARGET (finalsbest2) (L2078), which bound the actual oscillatory
  sums, may also fail. This is not established: it would need a lower bound on the time integrals.

**Update (2026-11-04, `docs/research/vine2-m1.txt`):** vine (II) with one double bond works (every vine estimate and
the twist cancellation go through at m = 1), which repairs the Q-bead failure for all γ. What remains false is only the
T-bead necklace for **γ ≤ 1/2**; option (2) below needs only γ ∈ (1/2, 1) plus the m = 1 vine and the T-type counts
for γ > 1/2 (no longer (2/3, 1)). FINDINGS F72.

## What it means for the formalization

Ruling D2 sets the target as **0 < γ < 1**, and the frozen `main` (Wave A) quantifies over `γ ∈ Ioo 0 1`. The
statements above sit inside the proof of `layergarden` (B1.2), the combinatorial core. They are not frozen, so no
frozen statement is false. But the proof route TARGET gives does not go through for γ ≤ 1/2, and possibly not for
γ < 2/3.

## Options

- **(1) Keep 0 < γ < 1 and repair the argument.**
  - The suggested repair treats small-gap "T-type" chains like vine chains in stage 1. It also adds a one-double-bond
    vine (II).
  - It needs new results that do not exist: a Prop 7.6-type bound for T-type blocks, and extensions of DH23 Lemma 8.1
    and Props 9.1, 9.5 (and of `vinechainlem`, `subpro`, `subsetvc`, `finalmole`).
  - This is research with an uncertain outcome.
- **(2) Restrict the formal target to γ ∈ (1/2, 1).**
  - This drops γ = 1/2, which TARGET singles out (L325).
  - The frozen `main` would need a versioned successor (`main_v2` with `γ ∈ Ioo (1/2) 1`), which you would approve.
  - For γ ∈ (1/2, 2/3) we would still need the vine (II) / Q-bead question settled, or a restriction to (2/3, 1).
- **(3) Write to Deng and Hani** with the necklace example. Ask whether they know a fix, and whether `kqmainest1` and
  the main theorems are affected. This is independent of (1) and (2).

## Recommendation

1. **(3) now.** The example is concrete and has been checked twice. I can draft the note to the authors from the three
   research files if you want.
2. **Keep the frozen target as it is for now.**
   - Almost all of the remaining work is independent of γ, or only uses γ > 1/2 inside lemmas.
   - Run the repair (1) as a research packet in parallel.
   - Decide on (2) later, if the repair or the authors' answer does not settle it.
3. **Commission next**, as the cheaper and γ-local questions:
   - whether `kqmainest1` / (finalsbest2) also fail;
   - whether the vine (II) cancellation works with one double bond (which decides γ ∈ (1/2, 2/3)).
