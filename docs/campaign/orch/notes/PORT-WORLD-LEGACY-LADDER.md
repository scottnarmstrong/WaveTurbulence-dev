# Canonical-world legacy ladder boundary

This records an implementation compatibility defect, not an erratum in a mathematical source. No frozen declaration changes.

The old `Degen.MaximalLadderDisjoint` proves `chordLeft_mem_maximalLadders` and the right-hand analogue using an induced-edge-count field that the canonical selected-ladder predicate does not contain (copied source lines 93–142). Its six-atom example has three double rungs, a cyclic upper rail and an open lower rail. The full six-atom set is a selected ladder, so the four-atom left set is not maximal. The old proof fails at the removed field; its maximality conclusion is false in the current carrier.

`WorldA7.full_isLadderSet` constructs the actual full selected ladder, and `WorldA7.chordLeft_not_maximal` uses that proper superset to refute the old conclusion. Both are ordinary kernel proofs; no source theorem is refuted. The compatibility module also proves that the example is a genuine molecule. Current `world-a7/results.json` records their module compilation as exit 0. The planned world axiom/consumer audit remains required before certification.

R59 retires the incompatible legacy assertions from the future production import closure, preserving their original bytes and this refutation as evidence. The independently extracted `SelectedLadderGeometry` block (original lines 162–730) is byte-identical and already recompiles under the canonical definitions. The four redirected consumers may use this valid block. None may use the retired maximality assertions or a stale olean of the original module. No original statement may be weakened to force the obsolete module through.

This removes the obsolete internal assertions from the intended port scope; it does not certify the pending 3414-module world, the assembly overlay, or its source-facing target exports. The excluded assembly dependencies and changed C2Can/UnselOK consumers still need the separately owned closure rebuild and exact consumer/axiom/source audits.

Snapshot recorded 2026-11-06 00:11 UTC:

| Evidence file | SHA256 |
|---|---|
| `/home/scott/wt-scratch/world-a7/src/appb/Degen/MaximalLadderDisjoint.lean` | `9db836839b74af0bba25d4b77349a4e471ec913ae51a509dcfd16a84c58ee791` |
| `/home/scott/wt-scratch/world-a7/src/compat/WorldLadderCounterexample.lean` | `8b44d695e600ef4c8e5d0bad6b386beffe4dc6310074031e94062d3538aab8d4` |
| `/home/scott/wt-scratch/world-a7/src/compat/WorldSelectedLadderDisjoint.lean` | `19a619222bdeec14d9a03a7008fe8e05035ed4ac876aecd0bbd3d5630c4cea4e` |

Independent read-only review (v5_w13, Terra medium, 2026-11-06 00:13 UTC): PASS. Reviewer did not author the old or new evidence. The old/new chord source/target arrays, molecule structure and left atom set match. The obsolete proof explicitly invokes the removed induced-edge-count field; the new full selected-ladder witness directly refutes its maximality conclusion. The extracted block is byte-identical, all three recorded SHA256s match, and both compatibility modules have exit 0 in results.json. The reviewer checked that R59 forbids stale artifacts and weakening and leaves source/consumer/axiom certification open. No source was edited or new build run for this review.
