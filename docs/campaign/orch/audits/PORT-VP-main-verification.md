# D12 canonical main verification

Source landing: 66fa48dff0d465298fb989488dc374dbfa8e6519 (pushed); source commit c65534d, separate pure-checker performance commit d22c409. The1824-module catalogue (505220lines, max1030) and both closed exports are now on canonical main in the D12 separate Lake library. Main imports one small Foundations.Vine.Param interface.

Fresh isolated canonical-worktree compilation covered every catalogue module; Grouped passed11208 jobs, public wrapper/Main/root11211 jobs. Independent direct and public-wrapper consumers and standard-axiom checks passed. Worktree full landing gate passed16239 jobs and7193-file frozen/module guard. Canonical main then passed its actual incremental Lake landing gate (16239 jobs), duplicate/sorry scan, FROZEN-ANCHOR GUARD and7193-file module check; the exact public-wrapper consumer on main passed and both exports again report only propext, Classical.choice, Quot.sound. Full packet review/source map/repair diff are adjacent.

Main validation reused only the verified same-package canonical donor library outputs: 29200 lib/IR/root files, with 7196 equal complete source/config/dependency pins. All copies were rehashed and had distinct writable inodes; no dependency or raw scratch proof artifact was copied, and main-library outputs rebuilt normally. Donor was clean and its root gate/consumers bound by a receipt; transfer ran under main.lock. This is incremental main validation, not a fresh main rebuild. Complete transfer record SHA256 8ec16fdbd17ca2d037a6954ee9bdeb863d2070b6078834b7d8b0576d44da9a08 is preserved at /home/scott/wt-scratch/port-vp/CANONICAL-CACHE-TRANSFER.json.

A first cache preflight failed before any copying/build because main contains three pre-existing ignored source-data files: scratch/Draft.lean (D6 author-review hash938afa97...), scratch/Probe.lean and scratch/Probe2.lean. Root aborted the uncommitted merge under the lock, preserved all three files, then retried with an exact path/hash allowlist outside both libraries. Every other extra on-disk Lean file remains rejected; all tracked source imports were checked with the nested-comment-aware parser and unsupported import syntax fails closed. None imports these data modules. Exact hashes are recorded in the transfer manifest. The successful retry logs are retained; the initial redirected log was overwritten on retry, so this records the observed failed preflight rather than claiming a preserved complete first-attempt log.

Copied catalogue warnings remain (53 warning lines in the wrapper log); no warning-free build or new suppression is claimed. Frozen files, toolchain, Lake dependency pins, shared Mathlib sources/artifacts and source hypotheses are unchanged. The source-facing grouped equality is of atom-set families; list-counting consumers still need their actual nodup/count bridge. No source theorem anchor was sealed by this library port.

```text
DRAFT_ANCHORS: 10
  WaveTurbulence/Frozen/Theorems/Main.lean
  WaveTurbulence/Frozen/Theorems/Fixedpoint.lean
  WaveTurbulence/Frozen/Theorems/Layergarden.lean
  WaveTurbulence/Frozen/Theorems/LayergardenFlower.lean
  WaveTurbulence/Frozen/Theorems/Propansatz.lean
  WaveTurbulence/Frozen/Theorems/MainV2.lean
  WaveTurbulence/Frozen/Theorems/PropansatzV2.lean
  WaveTurbulence/Frozen/Theorems/LayergardenV2.lean
  WaveTurbulence/Frozen/Theorems/FixedpointV2.lean
  WaveTurbulence/Frozen/Theorems/LayergardenFlowerV2.lean
UNREGISTERED_SORRIES: 0
DRAFT_IMPORT_VIOLATIONS: 0
SEALED_THIS_TURN: 0
```
