# wt-orch Task 5 — refute-first audit of the general-d trilinear estimate (priority until Wave B stage 1 is announced)

`docs/research/git20-general-d.md` (on main; `git merge main`) claims a complete proof that the trilinear estimate
(TARGET (schappend8), L2516) ‖𝒦_j(φ1,φ2,φ3)‖_{Z_s} ≤ C(d,s) ∏‖φ_i‖_{Z_s} holds for every d ≥ 3, s > d/2 − 1, j = 0..3
(its Theorem 7), which would keep the frozen `wkelwp` (blow-up conjunct) provable as stated (FINDINGS F32). It is new
mathematics (GIT20 proves only d = 3; Remark 2.6 is unproved).

Try hard to refute it. Check every inequality, every change of variables (Jacobians, the hyperplane measure normalization
(2|ℓ₁|)⁻¹∫_{ℓ₁^⊥} as in the frozen `collisionOp`), the uniformity in k of the two Hölder bounds, the weighted
Schur/AM–GM step, the symmetry lemma, the gain-term reduction (|k|² ≤ |k1|²+|k3|² on the resonant set), the exponent
bookkeeping near s = d/2 − 1 for large d, and the claimed passage to the blow-up criterion through Appendix C. Test the
worst cases numerically if useful (scratch scripts outside the repo). Verdict: CORRECT / CORRECT WITH FIXES (list) /
WRONG (counterexample or the failing step). File `docs/campaign/orch/audits/GIT20-general-d.md`, commit on `w/orch`,
print `READY task5`. Wave B stage audits (Task 4b) take priority when announced.
