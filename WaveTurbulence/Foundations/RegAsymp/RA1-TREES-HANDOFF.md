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

Third checked components (source wrappers are in scratch):
- TreeFrequencyRows and TreeAugmentedFrequencyRows: actual source integer momentum rows,
  including the temporary root input, have a linear-in-source-order frequency pullback.
- TreePhysicalEnergy, TreeKernelReindex, TreePhysicalProfile: exact original KTstar finite
  profile expansion inside its literal integer-decoration sum. Original squared Wick,
  global garden.zeta, physical2delta and source leaf inputs are retained. Strict PASS.
- TreeLeafProfiles canonical Lake PASS: leaf-only Fourier inversion, actual transposed
  source phases, independent moment factorization, and translation-uniform appended root
  input mass. Retains link cutoffs in physical space for the NT first-moment budget.
The additional components' combined axiom audit is pending the next checkpoint.

Fourth checked milestone:
- TreeLeafCellMeasure, TreeRootLeafAmplitude, TreeRootLeafEnvelope and TreeRootLeafMixture
  canonical targeted Lake PASS, zero warnings. Actual moving-root amplitudes have strongly
  measurable derivative tensors and a uniform geometric derivative mass, using J+1 leaf
  moments for J derivatives plus the NT shift. The original root partition remains inside
  the amplitude, with the landed locally finite overlap bound.
- Scratch TreeHalfCellProfiles, TreeLeafFrequencyBudget and TreeCellCover strict PASS.
- Expanded validation/axioms.log: 29 results strict PASS, only the standard three axioms.
- Scalar NT/Wick application and the literal Nstar recursion/final assembly remain open.

Fifth checked milestone:
- TreeRootPairedProfile canonical targeted Lake PASS: common original-lambda envelope
  gives the full literal tree spatial Fourier norm, with all typing/L1 premises proved.
- Scratch TreeScalarProfile/Estimate and TreeNTSpatialEstimate strict PASS. The actual
  SRep fields yield L^(-gamma1+2eta) for the root-localized tree NT spectral mixture,
  Knt before Aorder; J+1 moments retain K>=d+2+J.
- TreeRebasedChain, TreeShiftedCoefficients, TreeAtRebase, TreeCoefficientLimit and
  TreeLimitRebase canonical targeted Lake PASS, zero warnings.
- Scratch TreePairRegularization, TreeActualRegularizedLimit, TreeLeadingExpansion,
  TreeLeadingChainJ, TreeJBCutoff, TreeLeadingClassification, TreeClassifiedExpansion
  strict PASS, zero warnings. The original tree expansion now has fully proved J4:
  all integrated components are zero off dominant/special, else (-1)^|Z|*literal JBtree,
  with source lower clock s, both root signs and empty chain retained. No limit premise.
- Expanded validation/axioms.log: 44 results strict PASS, standard three axioms only.
Remaining: exact physical spectral/leading exchanges, Wick source application, literal
Nstar recursion and its spatial bound, final constants and exact RA1Tree audit.
