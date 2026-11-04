# RA1-TREES — ongoing

Exact target: `/home/scott/wt-scratch/regref/OBLIGATIONS.md`, RA1Tree.
Scratch: `/home/scott/wt-scratch/ra1-trees`; pins in PIN.json and RA1Tree-type.txt.
Main merged first, branch merge commit 87e9ff7.

First checked milestone:
- Foundations/RegAsymp/TreeMarkedEnumeration.lean: actual marked finite-index products and
  coefficient reindexing through landed mcRep_on_enumeration. Canonical single-module Lake
  build PASS, zero warnings.
- Scratch RA1Trees.TreeTimeExpansion: source tree link-energy relation, exact phaseIntegral
  identity with chainAtilde and actual MCExpT coefficient family. Strict scratch PASS.
- TreeCoefficientEnumeration, TreeSourceProfile, ActualTreeProfile: actual selected source
  addresses enumerate NT links; exact resProfile representation of the original phase integral,
  with one family chosen before decoration/scale/root. Strict scratch PASS, zero warnings.
- validation/axioms.log: eight results, all exactly propext/Classical.choice/Quot.sound.

Checks use the repository's full Lean options including autoImplicit=false. MAINCOEF-T,
Cancel.MCBridge and RegAsymp.PhiProfile were built as individual canonical targets; project-only
prerequisites reused/rebuilt as needed, no Mathlib rebuild. No root/frozen edits.

Remaining: actual physical kernel minus app, Wick/source spectral exchanges, tree spatial
transport, Nstar identification and bound, time-factor bound, constant/type/axiom audits.
No final RA1Tree claim. No suspected new source erratum or mathematical obstruction.
Coordination is through the two PROGRESS.md files only; see scratch PROGRESS.md for current names.

Second checked milestone:
- TreePolynomialProfile and TreeTensorProfile canonical Lake PASS, zero warnings: actual
  cutoff monomial Fourier inversion and geometric weighted tensor profile mass.
- Scratch TimeDegree, TimeHomogeneity, TimePointwiseBound, TimeDiagonal, TimePolynomial,
  TimePolynomialBudget, TimePolynomialProfile and TreeTimeFactor strict PASS, zero warnings.
- exists_tree_JB_time_bound proves the required geometric literal JBtree norm bound on
  the forward source triangle, with its constant before every code/order/exponent. It holds
  even without dominance/well-formedness; all source integration endpoints are retained.
- Expanded validation/axioms.log: twelve checked results, standard three axioms only.
Remaining list above is reduced by the completed time-factor bound. Physical remainder,
Nstar identification/bound and final exact RA1Tree assembly remain unfinished.
