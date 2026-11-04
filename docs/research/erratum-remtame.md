# A source-exact obstruction in TARGET remtame

Location: TARGET `WKE-Longer_times_Final_arXiv.tex` L2152, `remtame`.
Quoted criterion: “some component contains exactly one atom adjacent to v”.
The source concludes that all incident labels at the removed tame atom v
are fixed in the counting problem. This is false: the criterion must count
crossing **bonds**, not neighboring atoms. Its negation in case (ii) must
be changed consistently. DH21 Lemmas 9.13–9.14 and DH23 §10.5(4) use the
bridge / single-crossing-bond criterion and do not have this defect.

## Explicit garden counterexample

There are atoms v,u,w,A,B,C,D. Opposite-oriented double bonds join u–v,
v–w, A–B, and C–D. Single bonds are u→A, B→u, w→C, D→w.
Thus V=7, E=12. The degrees of v,u,w are 4, and those of A,B,C,D are 3;
every in-degree/out-degree is at most two. The molecule is connected,
nonsaturated, and has no self-loop or triple bond.

This is a garden of four trees, with roots A,B,C,D and root signs
(+,-,+,-). Choose PC bonds A–u, u–v (one of the double bonds), C–w;
all remaining bonds are LP bonds. The tree orders are (3,1,2,1), so R=2
and E=2V-R as required. Leaf signs and pairings match the indicated bond
directions. There are no two-node mini-couples or mini-trees (which would
require triple bonds), or one-node self-loop insertion. Hence the example
is prime. The u–v–w chain gaps are zero and the A–B/C–D gaps are large,
so the SG-VC merging does not force removal of v or make it a hinge.

Take d≥3, L a sufficiently large integer divisible by 8, and put
q=t=e1/8, k=s e2 with s in [1/4,1/2] ∩ L^{-1}Z. All bonds at u,v,w
have label k. Give A→B and C→D label k+e1/4; give B→A and D→C label
e1/8. Then each root has value -e1/8. At A,B,C,D the ordered children
are (k,k+e1/4,e1/8), up to exchanging the outer children, and the source
interaction coefficient is +1. At u,v,w all four ports agree and the
coefficient is -1. Thus the actual reduced coefficient product is nonzero.
All label vectors lie in the same fixed unit ball, independent of s.

The source energy sums are 0 at u,v,w, +3/64 at A,C, and -3/64 at B,D:
|k+e1/4|²-|k|²-|e1/8|²=3/64 because k is orthogonal to e1.
Thus all atom momentum parameters, energy centers, external roots and
localization centers can be fixed while k varies over at least L/4 choices.
Nonzero gaps at A,B,C,D are bounded below independently of L, so they are
LG for large L; v,u,w are ZG and tame. No F43 zero-frequency estimate is
needed anywhere.

After removing v, the residual components are {u,A,B} and {w,C,D}.
Each contains exactly one atom adjacent to v, namely u or w. Each has
TWO crossing bonds, of opposite directions and equal label k. Their
contributions to both cut momentum and cut energy cancel, so the cut
identity supplies no fixed value for k. In fact k varies as above.
The circuit rank changes from 12-7+1=6 to 8-6+2=4, i.e. Delta chi=-2.
Thus this is precisely the large-gain branch, not the fixed-label branch.

## Review and consequence

An independent source reviewer checked both a generic molecule route and
an explicit prime-garden realization, and confirmed the defect. The
proposed correction is to replace BOTH occurrences of the adjacent-atom
criterion in remtame by “exactly one bond connecting the component to v”.
That correction agrees with the already proved scratch bridge lemmas.
No source text, frozen file, shared findings ledger or draft was edited.

The separate TARGET subpro(3) non-hinge tameness claim remains valid:
see DEGENERATE-TAME.md and the checked GardenLocal proof. This erratum
concerns the subsequent fixed-value removal branch, not tameness itself.
A source-exact proof of the uncorrected remtame branch cannot be supplied.
