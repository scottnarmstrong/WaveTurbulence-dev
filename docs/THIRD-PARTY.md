# Third-party code

Five Lean files contain code adapted from Jason Hickey's [`salt`](https://github.com/jyh/salt), at commit
`3d7274047aabeea823abf1c0bdf675ce165dbca2`, which is released under the Apache License 2.0. The license text is in
[`WaveTurbulence/Foundations/NumberTheory/SALT-LICENSE`](../WaveTurbulence/Foundations/NumberTheory/SALT-LICENSE).

| file | adapted from (`salt`) | copyright notice in the file header |
|---|---|---|
| [`WaveTurbulence/Foundations/NumberTheory/Phase.lean`](../WaveTurbulence/Foundations/NumberTheory/Phase.lean) | `Salt/ExpSum/Kusmin.lean` | Jason Hickey |
| [`WaveTurbulence/Foundations/NumberTheory/KusminLandau.lean`](../WaveTurbulence/Foundations/NumberTheory/KusminLandau.lean) | `Salt/ExpSum/Kusmin.lean` | Jason Hickey |
| [`WaveTurbulence/Foundations/NumberTheory/SecondDifference.lean`](../WaveTurbulence/Foundations/NumberTheory/SecondDifference.lean) | `Salt/ExpSum/VdCorput2.lean` | Jason Hickey |
| [`WaveTurbulence/Foundations/NumberTheory/HalfPowerSums.lean`](../WaveTurbulence/Foundations/NumberTheory/HalfPowerSums.lean) | `Salt/ExpSum/DerivTest.lean` (the head bound; the tail bound is new) | Jason Hickey, Scott Armstrong |
| [`WaveTurbulence/Foundations/Counting/MonotoneIntervals.lean`](../WaveTurbulence/Foundations/Counting/MonotoneIntervals.lean) | `Salt/ExpSum/VdCorput2.lean` | Jason Hickey, Scott Armstrong |

These five files keep their original notices: each header keeps its copyright line (as in the table) and points to
`SALT-LICENSE`, as section 4 of the license requires. They are the only Lean files in the repository that carry a
third-party notice.

Four other files adapted from `salt`, `NumberTheory/SawtoothFourier.lean`, `WeylDifferencing.lean`, `SineSeries.lean`
and `IntegerDistance.lean` (added in commit `55594f3`), were deleted as unused code in commit `7e7fc08d`; they remain in
the git history with their notices.
