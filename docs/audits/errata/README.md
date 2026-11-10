# Independent verification of the errata (2026-11-10)

Before publication, every entry of [`../../ERRATA-AND-DEVIATIONS.md`](../../ERRATA-AND-DEVIATIONS.md) that claimed an
ERROR or a GAP in the printed papers and was still marked CANDIDATE was checked independently: 14 entries in all. A
claim about the authors' papers should not be published on the strength of a single writer's analysis.

**Who checked, and how.** Three verifiers, each working separately and refute-first, and none of whom wrote the
entries they checked. Each verifier:
- read the printed sources first, pinned by sha256 (TARGET `493eef6b…`, DH23 `c7e47dfa…`, and DH21 and GIT20 where
  needed; the same pins as the errata file);
- quoted the printed text at the cited lines and checked the line numbers;
- reconstructed each claim from the source alone, and tried to refute it: a reading the entry missed, a convention, a
  later line that covers it, or a standard step an expert would supply;
- re-checked every concrete counterexample or computation by hand or with their own scripts;
- gave a verdict: CONFIRMED, CONFIRMED WITH CORRECTIONS (with the exact corrections), or NOT CONFIRMED.

The verifiers did not check the Lean proofs. The Lean status stated in the entries was checked separately against the
repository.

## Reports

| Report | Entries | Verdicts | Scripts |
|---|---|---|---|
| [`EV-A.md`](EV-A.md) | E2b, E2c, E11, E17, E20, E23 | E2b, E11 CONFIRMED; E2c, E17, E20, E23 CONFIRMED WITH CORRECTIONS | [`EV-A-scripts/`](EV-A-scripts/) |
| [`EV-B.md`](EV-B.md) | E2d, E16, E18, E24, E26 | E16, E26 CONFIRMED; E2d, E18, E24 CONFIRMED WITH CORRECTIONS | in the report's appendix |
| [`EV-C.md`](EV-C.md) | E2g, E39, E45 | all three CONFIRMED WITH CORRECTIONS | [`EV-C-scripts/`](EV-C-scripts/) |

**Result.** All 14 claims were confirmed: 6 as written and 8 with corrections. None was withdrawn. Every correction was
applied to the errata on 2026-11-10, and the 14 entries are now marked CONFIRMED. Some corrections changed an entry's
class:

| Entry | Class before | Class now |
|---|---|---|
| E2c | ERROR | EXPOSITION |
| E2d | ERROR | MINOR |
| E18 | ERROR | MINOR |
| E23 | GAP | EXPOSITION |
| E2g | GAP | EXPOSITION |
| E39 | GAP | EXPOSITION |
| E45 | GAP | GAP (through E30 and E31) |

The other corrections fix titles, line numbers and wording, add fairness notes on the authors' practice, and state
where a counterexample is shown only at graph level or in a local model.

## Reading note

The reports are the verifiers' working records, unedited apart from paths. Their internal names (for example "ruling"
numbers) refer to the formalization's working records and are explained in the errata entries where they matter.
Absolute local paths were replaced by placeholders: `<repo>` is a checkout of this repository. The source paths cited
in the reports (for example `references/src-2311.10082/`) are relative to a local copy of the papers' LaTeX sources,
which is not part of the repository. Lean names refer to the repository at the time of writing, main at `636c5a46`; a
later clean-up removed some unused helpers, which remain in the git history at that commit.
