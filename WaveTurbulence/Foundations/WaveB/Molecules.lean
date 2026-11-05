/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.RegularHeldOut

/-!
# Wave B, tier B2 — molecules and the counting quantities (DRAFT for author approval)

Drafts of WAVE-B v2 §2.9 and §3.6–§3.11 (TARGET Def `defmol` L1295, Def `defcplmol` L1297–L1302,
Def `defdecmol` L1308–L1325, Def `defblock` L1328–L1331, Def `defvine` L1384–L1394 with
`Vines.png`, Def `defdiff` L1938–L1941, Def `defcut` L2117–L2127, (defcounta2) L2129–L2137, (defdev);
figure-defs §0, §1, §4; review I9 / row P5 `MOL.countq`). Self-contained (freeze-set closure policy).

* §1 Molecules as **half-edge (dart) structures** (F40): atoms, darts, the bond involution `mate`, the
  orientation `out`; degrees, components, circuit rank `χ = E - V + F`; the molecule predicate.
* §2 Atomic groups, blocks, `σ(𝔹)`.
* §3 The molecule `𝕄(𝒢)` of a garden (PC and LP bonds, directions by signs).
* §4 `(c_v)`-decorations, `Γ_v`, restricted decorations; gaps and their kinds SG/LG/ZG.
* §5 Standalone ladders (explicit rail-direction clause), maximal ladders, `q`, `m`, `ρ`.
* §6 Vines (I)–(VIII): templates with slots and groups, expansion by `k ≥ 0` rungs per slot (F37; vine (II)
  from one rung, F72), the vine predicate (block + undirected template isomorphism; no direction clause, figure-defs V2).
* §7 Cuts (F40: the incoming dart of `ℓ₁` and the outgoing dart of `ℓ₂` stay at `v₁ = v`, all other
  darts at `v` move to the new atom `v₂`); α- and β-cuts.
* §8 The counting quantities `𝔈`, `𝔄` (T (defcounta2)) and the deviation `𝔇𝔢𝔳` (T (defdev)), generic
  in the molecule; atom labels α/β/ε.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-! ## §1 Molecules as half-edge structures -/

/-- **A pre-molecule** (T Def `defmol`, L1295; half-edge encoding, review F40, figure-defs §4): a
finite set of atoms (names in `V`), the darts `D` (half-edges; every element of the finite type `D` is
a dart), the atom `atom x ∈ atoms` of each dart, the involution `mate` without fixed points pairing
darts into bonds, and the orientation `out x` (`true`: the bond leaves its atom at `x`); the two darts
of a bond have opposite orientations. A self-loop is two darts at the same atom (it counts as one
outgoing and one incoming bond). The molecule axioms are `IsMolecule`. -/
structure Molecule (V D : Type*) where
  atoms : Finset V
  atom : D → V
  mate : D → D
  out : D → Bool
  atom_mem : ∀ x, atom x ∈ atoms
  mate_mate : ∀ x, mate (mate x) = x
  mate_ne : ∀ x, mate x ≠ x
  out_mate : ∀ x, out (mate x) = !out x

namespace Molecule

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

/-- The darts at the atom `v`. -/
def dartsAt (v : V) : Finset D := Finset.univ.filter fun x => M.atom x = v

/-- The degree `d(v)` (bonds of both directions; a self-loop counts twice). -/
def deg (v : V) : ℕ := (M.dartsAt v).card

/-- The out-degree. -/
def outdeg (v : V) : ℕ := ((M.dartsAt v).filter fun x => M.out x = true).card

/-- The in-degree. -/
def indeg (v : V) : ℕ := ((M.dartsAt v).filter fun x => M.out x = false).card

/-- The bonds, each represented by its outgoing dart. -/
def bonds : Finset D := Finset.univ.filter fun x => M.out x = true

/-- The endpoints of the bond of the dart `x`, as an unordered pair. -/
def ends (x : D) : Sym2 V := s(M.atom x, M.atom (M.mate x))

/-- Two atoms are adjacent (undirected) if a bond joins them. -/
def Adj (u v : V) : Prop := ∃ x, M.atom x = u ∧ M.atom (M.mate x) = v

/-- The number `F` of connected components (undirected; T Def `defmol`). -/
noncomputable def numComponents : ℕ := Nat.card (Quot fun u v : M.atoms => M.Adj u.1 v.1)

/-- The circuit rank `χ = E - V + F` (T Def `defmol`). -/
noncomputable def circuitRank : ℤ := (M.bonds.card : ℤ) - M.atoms.card + M.numComponents

/-- `u` and `v` lie in the same component. -/
def SameComponent (u v : V) : Prop := Relation.EqvGen M.Adj u v

/-- **The molecule axioms** (T Def `defmol`): (i) every atom has at most 2 outgoing and at most 2
incoming bonds; (ii) no component is saturated (consists only of degree-4 atoms). -/
def IsMolecule : Prop :=
  (∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2) ∧
    ∀ v ∈ M.atoms, ∃ u ∈ M.atoms, M.SameComponent v u ∧ M.deg u ≠ 4

/-! ## §2 Atomic groups and blocks (T Def `defmol`, last sentence; Def `defblock`) -/

/-- A dart of the atomic group `S` (both ends in `S`; T: an atomic group carries all bonds between its
atoms). -/
def InGroup (S : Finset V) (x : D) : Prop := M.atom x ∈ S ∧ M.atom (M.mate x) ∈ S

@[instance_reducible, instance] def instDecidableInGroup (S : Finset V) (x : D) : Decidable (M.InGroup S x) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Degree within the atomic group `S`. -/
def degIn (S : Finset V) (v : V) : ℕ := ((M.dartsAt v).filter fun x => M.InGroup S x).card

/-- Out-degree within `S`. -/
def outIn (S : Finset V) (v : V) : ℕ :=
  ((M.dartsAt v).filter fun x => M.InGroup S x ∧ M.out x = true).card

/-- In-degree within `S`. -/
def inIn (S : Finset V) (v : V) : ℕ :=
  ((M.dartsAt v).filter fun x => M.InGroup S x ∧ M.out x = false).card

/-- The atomic group `S` is connected: any two of its atoms are joined by a path of bonds of `S`
(T Def `defblock`, figures; F57). -/
def GroupConnected (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S,
    Relation.EqvGen (fun a b => ∃ x, M.InGroup S x ∧ M.atom x = a ∧ M.atom (M.mate x) = b) u v

/-- **A block with joints `j₁ ≠ j₂`** (T Def `defblock`, figure-defs §0.2; F57, B2-CL-5): the joints have
out-degree `1` and in-degree `1` within `S`, every other atom of `S` has degree `4` within `S`, and the atomic
group `S` is connected. Connectedness is not in the source's degree-only wording, but the figures draw connected
blocks, and without it the concatenation claim of `defblock` (T L1330; DH23 Def 4.10) and the alternative (b)
of `disjointlem` (T L1337–L1341; DH23 Lemma 4.11) are false (F57: wt-nt's `MoleculeBlockEdgeCase`). `IsBlock` is
not decidable as written; no statement decides it. -/
def IsBlock (S : Finset V) (j₁ j₂ : V) : Prop :=
  S ⊆ M.atoms ∧ j₁ ∈ S ∧ j₂ ∈ S ∧ j₁ ≠ j₂ ∧
    M.outIn S j₁ = 1 ∧ M.inIn S j₁ = 1 ∧ M.outIn S j₂ = 1 ∧ M.inIn S j₂ = 1 ∧
    (∀ v ∈ S, v ≠ j₁ → v ≠ j₂ → M.degIn S v = 4) ∧ M.GroupConnected S

/-- The molecule with the bond of the dart `e` removed: the darts `e` and `mate e` are deleted, everything else
is unchanged (used for the adjoint of a hyper-block). -/
def eraseBond (e : D) : Molecule V {x : D // x ≠ e ∧ x ≠ M.mate e} where
  atoms := M.atoms
  atom := fun x => M.atom x.1
  mate := fun x => ⟨M.mate x.1,
    fun h => x.2.2 (by have hh := congrArg M.mate h; simpa only [M.mate_mate] using hh),
    fun h => x.2.1 (by have hh := congrArg M.mate h; simpa only [M.mate_mate] using hh)⟩
  out := fun x => M.out x.1
  atom_mem := fun x => M.atom_mem x.1
  mate_mate := fun x => Subtype.ext (M.mate_mate x.1)
  mate_ne := fun x h => M.mate_ne x.1 (congrArg Subtype.val h)
  out_mate := fun x => M.out_mate x.1

/-- **A hyper-block with joints `j₁, j₂`** (T Def `defblock`; F57, B2-CL-5): the atomic group `S` is a block
`𝔹` with one bond added between its joints. Equivalently, some bond `e` of `S` joins `j₁` and `j₂`, and with `e`
removed, `S` is a block with joints `j₁, j₂`: its **adjoint**, which is connected (`IsBlock`). Connectedness of
`S` itself would not suffice: the adjoint could split into two pieces, one at each joint. -/
def IsHyperBlock (S : Finset V) (j₁ j₂ : V) : Prop :=
  ∃ e : D, M.ends e = s(j₁, j₂) ∧ (M.eraseBond e).IsBlock S j₁ j₂

/-- The number of bonds between two atoms. -/
def bondsBetween (a b : V) : ℕ := (M.bonds.filter fun x => M.ends x = s(a, b)).card

/-- `σ(𝔹)`: the number of bonds between the joints (T Def `defblock`). -/
def sigma (j₁ j₂ : V) : ℕ := M.bondsBetween j₁ j₂

/-- A bond goes from `a` to `b`. -/
def Directed (a b : V) : Prop := ∃ x, M.out x = true ∧ M.atom x = a ∧ M.atom (M.mate x) = b

@[instance_reducible, instance] def instDecidableDirected (a b : V) : Decidable (M.Directed a b) := by
  unfold Directed
  infer_instance

/-- The undirected bond multiset of the atomic group `S`. -/
def groupBonds (S : Finset V) : Multiset (Sym2 V) :=
  ((Finset.univ.filter fun x => M.out x = true ∧ M.InGroup S x).val).map M.ends

end Molecule

/-! ## §3 The molecule of a garden (T Def `defcplmol`, L1297–L1302) -/

section GardenMolecule

variable {w : ℕ}

/-- The parent of a non-root node (a branching node). The membership proof is inline (B2-CL-12, closure policy of
B1 CL-17/CL-18: no frozen declaration uses a proved theorem of the project; cf. B1's `GBranch.child`). -/
def GNode.parent {tree : Fin w → TTree} (a : GNode tree) (h : a.1.2 ≠ []) : GBranch tree :=
  ⟨(a.1.1, a.1.2.dropLast), by
    have cons_mem : ∀ (i j : Fin 3) (S : Finset TTree.Path) (q : TTree.Path),
        j :: q ∈ TTree.pre i S ↔ i = j ∧ q ∈ S := by
      intro i j S q
      simp only [TTree.pre, Finset.mem_image, List.cons.injEq]
      constructor
      · rintro ⟨q', hq', rfl, rfl⟩
        exact ⟨rfl, hq'⟩
      · rintro ⟨rfl, hq⟩
        exact ⟨q, hq, rfl, rfl⟩
    have key : ∀ (t : TTree) (p : TTree.Path) (i : Fin 3), p ++ [i] ∈ t.nodes → p ∈ t.branching := by
      intro t
      induction t with
      | leaf =>
        intro p i hp
        simp [TTree.nodes] at hp
      | node l m r ihl ihm ihr =>
        intro p i hp
        rcases p with _ | ⟨j, p⟩
        · simp [TTree.branching]
        · simp only [List.cons_append, TTree.nodes, Finset.mem_insert, Finset.mem_union, cons_mem,
            reduceCtorEq, false_or] at hp
          simp only [TTree.branching, Finset.mem_insert, Finset.mem_union, cons_mem, reduceCtorEq,
            false_or]
          rcases hp with (⟨rfl, hq⟩ | ⟨rfl, hq⟩) | ⟨rfl, hq⟩
          · exact Or.inl (Or.inl ⟨rfl, ihl p i hq⟩)
          · exact Or.inl (Or.inr ⟨rfl, ihm p i hq⟩)
          · exact Or.inr ⟨rfl, ihr p i hq⟩
    have hp := a.2
    have e : a.1.2.dropLast ++ [a.1.2.getLast h] = a.1.2 := List.dropLast_append_getLast h
    rw [← e] at hp
    exact key _ _ _ hp⟩

/-- The darts of `𝕄(𝒢)`: two darts for each PC bond (a non-root branching node `c` and its parent;
`true` = the dart at the parent), and one dart for each paired leaf `ℓ` with a parent whose partner
also has a parent (the dart of the LP bond at the parent of `ℓ`; leaf pairs involving a root leaf give
no bond, T L1316). -/
abbrev GardenDart (G : Garden w) : Type :=
  ({c : GBranch G.tree // c.1.2 ≠ []} × Bool) ⊕
    {ℓ : GLeaf G.tree // G.mark ℓ = none ∧ ℓ.1.2 ≠ [] ∧ (G.pair ℓ).1.2 ≠ []}

/-- **The molecule `𝕄(𝒢)` of a garden** (T Def `defcplmol`): atoms the branching nodes; a PC bond
between a node and each branching child, directed towards the child iff the child has sign `-`; an LP
bond between the parents of two paired leaves, directed from the parent whose paired child has sign
`-` to the one whose paired child has sign `+`. The facts the body needs about the pairing (the partner of
an unmarked leaf is unmarked and different) are proved inline (B2-CL-12). -/
def Garden.molecule (G : Garden w) : Molecule (GBranch G.tree) (GardenDart G) where
  atoms := Finset.univ
  atom := fun x => match x with
    | .inl (c, true) => GNode.parent c.1.toNode c.2
    | .inl (c, false) => c.1
    | .inr ℓ => GNode.parent ℓ.1.toNode ℓ.2.2.1
  mate := fun x => match x with
    | .inl (c, b) => .inl (c, !b)
    | .inr ℓ => .inr ⟨G.pair ℓ.1, by
          by_contra hm
          have h1 := (G.pair_eq_iff (G.pair ℓ.1)).2 hm
          rw [G.pair_pair] at h1
          exact ((G.pair_eq_iff ℓ.1).1 h1.symm) ℓ.2.1,
        ℓ.2.2.2, by rw [G.pair_pair]; exact ℓ.2.2.1⟩
  out := fun x => match x with
    | .inl (c, true) => decide (G.sign c.1.toNode ≠ 1)
    | .inl (c, false) => decide (G.sign c.1.toNode = 1)
    | .inr ℓ => decide (G.sign ℓ.1.toNode ≠ 1)
  atom_mem := fun _ => Finset.mem_univ _
  mate_mate := by
    rintro (⟨c, b⟩ | ℓ)
    · simp
    · simp only [Sum.inr.injEq]
      exact Subtype.ext (G.pair_pair ℓ.1)
  mate_ne := by
    rintro (⟨c, b⟩ | ℓ)
    · simp
    · simp only [ne_eq, Sum.inr.injEq]
      intro h
      exact ((G.pair_eq_iff ℓ.1).1 (congrArg Subtype.val h)) ℓ.2.1
  out_mate := by
    rintro (⟨c, _ | _⟩ | ℓ)
    · simp
    · simp
    · have hs := G.pair_sign ℓ.1 (fun h' => ((G.pair_eq_iff ℓ.1).1 h') ℓ.2.1)
      change decide (nodeSign G.sig (G.pair ℓ.1).1 ≠ 1) = !decide (nodeSign G.sig ℓ.1.1 ≠ 1)
      rw [hs]
      rcases Int.units_eq_one_or (nodeSign G.sig ℓ.1.1) with h | h <;> rw [h] <;> decide

end GardenMolecule

/-! ## §4 Decorations of molecules, `Γ_v`, restrictions, gaps (T Def `defdecmol`, Def `defdiff`) -/

namespace Molecule

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) {d : ℕ}

/-- The vector of a dart for integer labels `κ` on the coset `w + ℤ_L^d` (`w = 0`: lattice
decorations; `w = k`: the `k`-decorations of couples, T L1316). -/
noncomputable def kvec {D : Type*} (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (x : D) : Mom d :=
  w + latticePoint L (κ x)

/-- `ζ_{v,ℓ}`: `+1` for the outgoing dart, `-1` for the incoming one. -/
def dartSign (x : D) : ℝ := if M.out x = true then 1 else -1


/-- **A `(c_v)`-decoration** (T Def `defdecmol`, (decmole1)): labels constant on bonds with
`∑_{ℓ ↔ v} ζ_{v,ℓ} k_ℓ = c_v` at every atom (`c_v = 0` at degree-4 atoms is a condition on `c`,
imposed where the parameters are quantified, `countE`). -/
def IsDecoration (L : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ)) : Prop :=
  (∀ x, κ (M.mate x) = κ x) ∧
    ∀ v ∈ M.atoms, ∑ x ∈ M.dartsAt v, M.dartSign x • kvec L w κ x = c v

/-- `Γ_v = ∑_{ℓ ↔ v} ζ_{v,ℓ} |k_ℓ|²` (T (defomegadec)). -/
noncomputable def Gamma (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (v : V) : ℝ :=
  ∑ x ∈ M.dartsAt v, M.dartSign x * ‖kvec L w κ x‖ ^ 2

/-- **Restricted decorations** (T Def `defdecmol`, last paragraph): `|Γ_v - β_v| ≤ δ^{-1}L^{-2γ}` at
every atom and `|k_ℓ - k_ℓ^0| ≤ 1` at every bond. -/
def IsRestricted (L γ δ : ℝ) (w : Mom d) (β : V → ℝ) (k0 : D → Mom d) (κ : D → (Fin d → ℤ)) :
    Prop :=
  (∀ v ∈ M.atoms, |M.Gamma L w κ v - β v| ≤ δ⁻¹ * L ^ (-2 * γ)) ∧
    ∀ x, ‖kvec L w κ x - k0 x‖ ≤ 1

/-- The kinds of gaps (T Def `defdiff`): zero, small `0 < |r| ≤ L^{-γ+η}`, large `|r| > L^{-γ+η}`. -/
inductive GapKind
  | ZG
  | SG
  | LG

/-- Decidable equality of gap kinds, written out as for B1's `MarkTag` (B2-CL-12, CL-17/CL-18 policy: no
`deriving` in the freeze set). -/
@[instance_reducible, instance] def instDecidableEqGapKind : DecidableEq GapKind := fun a b =>
  match a, b with
  | .ZG, .ZG => isTrue rfl
  | .ZG, .SG => isFalse fun h => GapKind.noConfusion h
  | .ZG, .LG => isFalse fun h => GapKind.noConfusion h
  | .SG, .ZG => isFalse fun h => GapKind.noConfusion h
  | .SG, .SG => isTrue rfl
  | .SG, .LG => isFalse fun h => GapKind.noConfusion h
  | .LG, .ZG => isFalse fun h => GapKind.noConfusion h
  | .LG, .SG => isFalse fun h => GapKind.noConfusion h
  | .LG, .LG => isTrue rfl

/-- The kind of a gap vector `r`. -/
noncomputable def gapKind (L γ η : ℝ) (r : Mom d) : GapKind := by
  classical
  exact if r = 0 then .ZG else if ‖r‖ ≤ L ^ (-γ + η) then .SG else .LG

/-- The gap of the triple `(v, ℓ₁, ℓ₂)`, given by darts `x₁, x₂` at `v` of opposite directions:
`r = k_{ℓ₁} - k_{ℓ₂}` (T Def `defdiff`, second paragraph). -/
noncomputable def gapAt {D : Type*} (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (x₁ x₂ : D) :
    Mom d :=
  kvec L w κ x₁ - kvec L w κ x₂

/-- `r` is the gap of the block `S` with joints `j₁, j₂` (T Def `defdiff`): the difference of the
vectors of the two bonds of `S` at the joint `j₁` (up to sign, the same at `j₂`). -/
def IsBlockGap (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (S : Finset V) (j₁ : V) (r : Mom d) :
    Prop :=
  ∃ x₁ x₂, M.atom x₁ = j₁ ∧ M.atom x₂ = j₁ ∧ M.InGroup S x₁ ∧ M.InGroup S x₂ ∧
    M.out x₁ = true ∧ M.out x₂ = false ∧ r = gapAt L w κ x₁ x₂

/-! ## §5 Standalone ladders (T Def `defvine`, ladder part; figure-defs §1, standalone ladders) -/

/-- **A ladder of length `m ≥ 1`** (T L1384–L1386; DH23 Def 5.1, L789–L808; figure-defs §1; F37; F53, B2-CL-3).
The ladder selects its rung and rail bonds:
- atoms `u_0..u_m`, `v_0..v_m`, all distinct;
- rungs: exactly two bonds between `u_j` and `v_j`;
- rails: for each `j < m`, exactly one bond between `u_j` and `u_{j+1}`, exactly one between `v_j` and `v_{j+1}`, and
  the two are oppositely directed (`u_j → u_{j+1}` iff `v_{j+1} → v_j`).

The exact multiplicities exclude extra parallel copies of the selected rungs and rails. Bonds between end atoms
`u_0, v_0, u_m, v_m` are allowed, including a chord closing one rail (figure-defs §1: "the end atoms may have bonds
outside the ladder"). Since the degree is `≤ 4`, an interior atom is saturated by its rung and its two rails, so any
other bond inside the atom set joins end atoms. This is a consequence, not a premise.

There is no induced clause: the old "`4m + 2` bonds in the atomic group" made two overlapping length-1 ladders
maximal on wt-ansob's `chordLadder` (probes). This is wt-ansob's `Degen.SourceLadder` verbatim (the owner's ruling,
DEGEN). -/
def IsLadder {m : ℕ} (u v : Fin (m + 1) → V) : Prop :=
  1 ≤ m ∧ Function.Injective (Sum.elim u v) ∧ (∀ j, u j ∈ M.atoms ∧ v j ∈ M.atoms) ∧
    (∀ j, M.bondsBetween (u j) (v j) = 2) ∧
    (∀ j : Fin m, M.bondsBetween (u j.castSucc) (u j.succ) = 1 ∧
      M.bondsBetween (v j.castSucc) (v j.succ) = 1 ∧
      (M.Directed (u j.castSucc) (u j.succ) ↔ M.Directed (v j.succ) (v j.castSucc)))

/-- The atom set of a ladder. -/
def ladderAtoms {V : Type*} [DecidableEq V] {m : ℕ} (u v : Fin (m + 1) → V) : Finset V :=
  (Finset.univ.image u) ∪ (Finset.univ.image v)

/-- `S` is the atom set of a ladder. -/
def IsLadderSet (S : Finset V) : Prop :=
  ∃ m : ℕ, ∃ u v : Fin (m + 1) → V, M.IsLadder u v ∧ ladderAtoms u v = S

/-- **The maximal ladders** (T Prop `ladderl1old`, L1994): the atom sets of ladders not contained in
the atom set of a larger ladder. With selected bonds, maximal ladders are pairwise disjoint in every molecule, as
DH23 `kqmainest2` counts them: `Molecule.maximalLadders_pairwiseDisjoint` (`WaveB2-Ladders.lean`, B2-CL-4, ported
from wt-ansob's `Degen.sourceMaximalLadders_pairwiseDisjoint`). -/
noncomputable def maximalLadders : Finset (Finset V) := by
  classical
  exact M.atoms.powerset.filter fun S =>
    M.IsLadderSet S ∧ ∀ S' : Finset V, M.IsLadderSet S' → S ⊆ S' → S' = S

/-- The length `z = #rungs - 1` of a ladder from its atom set. -/
def ladderLength (S : Finset V) : ℕ := S.card / 2 - 1

/-- `q`: the number of maximal ladders. -/
noncomputable def numLadders : ℕ := M.maximalLadders.card

/-- `m`: the number of atoms in no maximal ladder. -/
noncomputable def numFree : ℕ := by
  classical
  exact (M.atoms.filter fun v => ∀ S ∈ M.maximalLadders, v ∉ S).card

/-- `ρ = q + m` (T (defcounta2)). -/
noncomputable def rho : ℕ := M.numLadders + M.numFree

/-- `r` is the gap of the ladder with atoms `u, v` (T Def `defdiff`: `k_ℓ - k_ℓ'` for the two rails
between the first two rungs; up to sign it is the same for every pair of parallel rails). -/
def IsLadderGap {m : ℕ} (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (u v : Fin (m + 1) → V)
    (hm : 1 ≤ m) (r : Mom d) : Prop :=
  ∃ x y, M.ends x = s(u 0, u ⟨1, by omega⟩) ∧ M.ends y = s(v 0, v ⟨1, by omega⟩) ∧
    M.atom x = u 0 ∧ M.atom y = v 0 ∧ r = gapAt L w κ x y

end Molecule

/-! ## §6 Vines (I)–(VIII) (T Def `defvine`, L1384–L1394, `Vines.png`; figure-defs §1, WAVE-B §3.6) -/

/-- The eight vine types. -/
inductive VineType
  | I | II | III | IV | V | VI | VII | VIII

/-- Decidable equality of vine types, written out (B2-CL-12, CL-17/CL-18 policy: no `deriving` in the freeze
set). -/
@[instance_reducible, instance] def instDecidableEqVineType : DecidableEq VineType := fun a b =>
  match a, b with
  | .I, .I => isTrue rfl
  | .I, .II => isFalse fun h => VineType.noConfusion h
  | .I, .III => isFalse fun h => VineType.noConfusion h
  | .I, .IV => isFalse fun h => VineType.noConfusion h
  | .I, .V => isFalse fun h => VineType.noConfusion h
  | .I, .VI => isFalse fun h => VineType.noConfusion h
  | .I, .VII => isFalse fun h => VineType.noConfusion h
  | .I, .VIII => isFalse fun h => VineType.noConfusion h
  | .II, .I => isFalse fun h => VineType.noConfusion h
  | .II, .II => isTrue rfl
  | .II, .III => isFalse fun h => VineType.noConfusion h
  | .II, .IV => isFalse fun h => VineType.noConfusion h
  | .II, .V => isFalse fun h => VineType.noConfusion h
  | .II, .VI => isFalse fun h => VineType.noConfusion h
  | .II, .VII => isFalse fun h => VineType.noConfusion h
  | .II, .VIII => isFalse fun h => VineType.noConfusion h
  | .III, .I => isFalse fun h => VineType.noConfusion h
  | .III, .II => isFalse fun h => VineType.noConfusion h
  | .III, .III => isTrue rfl
  | .III, .IV => isFalse fun h => VineType.noConfusion h
  | .III, .V => isFalse fun h => VineType.noConfusion h
  | .III, .VI => isFalse fun h => VineType.noConfusion h
  | .III, .VII => isFalse fun h => VineType.noConfusion h
  | .III, .VIII => isFalse fun h => VineType.noConfusion h
  | .IV, .I => isFalse fun h => VineType.noConfusion h
  | .IV, .II => isFalse fun h => VineType.noConfusion h
  | .IV, .III => isFalse fun h => VineType.noConfusion h
  | .IV, .IV => isTrue rfl
  | .IV, .V => isFalse fun h => VineType.noConfusion h
  | .IV, .VI => isFalse fun h => VineType.noConfusion h
  | .IV, .VII => isFalse fun h => VineType.noConfusion h
  | .IV, .VIII => isFalse fun h => VineType.noConfusion h
  | .V, .I => isFalse fun h => VineType.noConfusion h
  | .V, .II => isFalse fun h => VineType.noConfusion h
  | .V, .III => isFalse fun h => VineType.noConfusion h
  | .V, .IV => isFalse fun h => VineType.noConfusion h
  | .V, .V => isTrue rfl
  | .V, .VI => isFalse fun h => VineType.noConfusion h
  | .V, .VII => isFalse fun h => VineType.noConfusion h
  | .V, .VIII => isFalse fun h => VineType.noConfusion h
  | .VI, .I => isFalse fun h => VineType.noConfusion h
  | .VI, .II => isFalse fun h => VineType.noConfusion h
  | .VI, .III => isFalse fun h => VineType.noConfusion h
  | .VI, .IV => isFalse fun h => VineType.noConfusion h
  | .VI, .V => isFalse fun h => VineType.noConfusion h
  | .VI, .VI => isTrue rfl
  | .VI, .VII => isFalse fun h => VineType.noConfusion h
  | .VI, .VIII => isFalse fun h => VineType.noConfusion h
  | .VII, .I => isFalse fun h => VineType.noConfusion h
  | .VII, .II => isFalse fun h => VineType.noConfusion h
  | .VII, .III => isFalse fun h => VineType.noConfusion h
  | .VII, .IV => isFalse fun h => VineType.noConfusion h
  | .VII, .V => isFalse fun h => VineType.noConfusion h
  | .VII, .VI => isFalse fun h => VineType.noConfusion h
  | .VII, .VII => isTrue rfl
  | .VII, .VIII => isFalse fun h => VineType.noConfusion h
  | .VIII, .I => isFalse fun h => VineType.noConfusion h
  | .VIII, .II => isFalse fun h => VineType.noConfusion h
  | .VIII, .III => isFalse fun h => VineType.noConfusion h
  | .VIII, .IV => isFalse fun h => VineType.noConfusion h
  | .VIII, .V => isFalse fun h => VineType.noConfusion h
  | .VIII, .VI => isFalse fun h => VineType.noConfusion h
  | .VIII, .VII => isFalse fun h => VineType.noConfusion h
  | .VIII, .VIII => isTrue rfl

/-- **A vine template**: `n` atoms (`0 = J₁`, `1 = J₂`), the undirected bonds (with multiplicity,
including the slot members), the slots (pairs of parallel single bonds `(x⋯y, x'⋯y')`, the two rails of a
ladder segment, at which `k ≥ 0` rungs may be inserted; in (II) both rails end at `J₂`), and the groups
(T L1489–L1499, figure-defs V5). -/
structure VineTemplate where
  n : ℕ
  bonds : List (ℕ × ℕ)
  slots : List ((ℕ × ℕ) × (ℕ × ℕ))
  groups : List (List ℕ)

/-- **The templates** (figure-defs §1(a), transcribed from `Vines.png`; atom names in the comments).

**(II) starts from one rung (B2-CL-21, FINDINGS F72).** Vine (II) is the ladder of `m ≥ 1` rungs between its
two joints (DH23 L1421–L1449 and L1481 "`m ≥ 1` for vines (II)"; T Def `defvine`, L1384). Its template is the
`m = 1` member, the 4-atom Q-block `J₁ - (a = b) - J₂`, and its one slot is the pair of rails `a⋯J₂`,
`b⋯J₂`. So `expand [k]` has `m = k + 1` rungs: `2k + 4` atoms and `4k + 6` bonds. The two-rung vine drawn in
`Vines.png` is `expand [1]`. -/
def VineType.template : VineType → VineTemplate
  -- J₁ J₂
  | .I => ⟨2, [(0, 1), (0, 1)], [], []⟩
  -- J₁ J₂ a b (the Q-block, one rung `a = b`; slot: the rails `a⋯J₂`, `b⋯J₂`)
  | .II => ⟨4, [(0, 2), (0, 3), (2, 3), (2, 3), (2, 1), (3, 1)], [((2, 1), (3, 1))], [[2, 3]]⟩
  -- J₁ J₂ a b c g h e f
  | .III => ⟨9, [(0, 2), (0, 3), (2, 3), (2, 3), (4, 5), (4, 6), (5, 6), (5, 6), (7, 8), (7, 8),
      (1, 7), (1, 8), (2, 4), (3, 5), (4, 7), (6, 8)],
      [((2, 4), (3, 5)), ((4, 7), (6, 8))], [[4, 5, 6], [2, 3], [7, 8]]⟩
  -- J₁ J₂ a b c m e f g
  | .IV => ⟨9, [(0, 2), (0, 3), (2, 3), (2, 3), (4, 5), (4, 5), (5, 6), (5, 6), (7, 8), (7, 8),
      (1, 7), (1, 8), (2, 4), (3, 6), (4, 7), (6, 8)],
      [((2, 4), (3, 6)), ((4, 7), (6, 8))], [[4, 5, 6], [2, 3], [7, 8]]⟩
  -- J₁ J₂ a b c d e f g
  | .V => ⟨9, [(0, 1), (0, 2), (1, 3), (2, 3), (2, 3), (4, 5), (4, 5), (4, 6), (5, 7), (6, 7),
      (6, 8), (6, 8), (7, 8), (7, 8), (2, 4), (3, 5)],
      [((2, 4), (3, 5))], [[6, 7, 8], [2, 3], [4, 5]]⟩
  -- J₁ J₂ a b c d e f x y p q r g₁ g₂
  | .VI => ⟨15, [(0, 2), (0, 3), (2, 3), (2, 3), (4, 5), (4, 5), (4, 6), (5, 8), (6, 7), (6, 7),
      (7, 9), (8, 9), (8, 9), (10, 11), (10, 12), (10, 12), (11, 12), (11, 12), (13, 14), (13, 14),
      (1, 13), (1, 14), (2, 4), (3, 5), (8, 10), (9, 11), (6, 13), (7, 14)],
      [((2, 4), (3, 5)), ((8, 10), (9, 11)), ((6, 13), (7, 14))],
      [[10, 11, 12], [2, 3], [4, 5], [6, 7], [8, 9], [13, 14]]⟩
  -- J₁ J₂ a b p q r c d e f
  | .VII => ⟨11, [(0, 2), (0, 3), (2, 3), (2, 3), (4, 5), (4, 5), (4, 6), (4, 6), (5, 6), (7, 8),
      (9, 10), (9, 10), (1, 9), (1, 10), (2, 7), (3, 8), (5, 7), (6, 8), (7, 9), (8, 10)],
      [((2, 7), (3, 8)), ((5, 7), (6, 8)), ((7, 9), (8, 10))], [[4, 5, 6], [2, 3], [9, 10], [7, 8]]⟩
  -- J₁ J₂ a b p q e f g h i
  | .VIII => ⟨11, [(0, 2), (0, 6), (2, 3), (2, 3), (4, 5), (4, 5), (1, 4), (1, 5), (3, 7), (6, 7),
      (6, 7), (8, 9), (8, 10), (8, 10), (9, 10), (9, 10), (2, 4), (3, 5), (6, 8), (7, 9)],
      [((2, 4), (3, 5)), ((6, 8), (7, 9))], [[8, 9, 10], [2, 3], [4, 5], [6, 7]]⟩

/-- `Bad` vines: (I) and (II); the others are normal. -/
def VineType.IsBad : VineType → Bool
  | .I | .II => true
  | _ => false

/-- The rails `z - w₁ - ⋯ - w_k - z'`. -/
def railBonds (z : ℕ) (ws : List ℕ) (z' : ℕ) : List (ℕ × ℕ) := List.zip (z :: ws) (ws ++ [z'])

/-- **Ladder insertion with `k ≥ 0` rungs at one slot** (figure-defs §1(a); F37: `k = 0` leaves the
template unchanged, which for every type but (II) is the vine as drawn): the slot bonds `x⋯y`, `x'⋯y'` are replaced by rails `x - u₁ - ⋯ - u_k - y`,
`x' - v₁ - ⋯ - v_k - y'` and rungs `u_i = v_i`; each rung is a new group. -/
def insertRungs (T : VineTemplate) (slot : (ℕ × ℕ) × (ℕ × ℕ)) (k : ℕ) : VineTemplate :=
  if k = 0 then T else
    let us := (List.range k).map (T.n + ·)
    let vs := (List.range k).map (T.n + k + ·)
    ⟨T.n + 2 * k,
      ((T.bonds.erase slot.1).erase slot.2) ++ railBonds slot.1.1 us slot.1.2 ++
        railBonds slot.2.1 vs slot.2.2 ++ (List.zip us vs).flatMap (fun p => [p, p]),
      T.slots, T.groups ++ (List.zip us vs).map (fun p => [p.1, p.2])⟩

/-- **The expanded template `T_X(k⃗)`**: `k_s` rungs inserted at slot `s` (one insertion per slot). -/
def VineType.expand (X : VineType) (k : List ℕ) : VineTemplate :=
  (X.template.slots.zip k).foldl (fun T sk => insertRungs T sk.1 sk.2) X.template

namespace Molecule

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

/-- **A vine of type `X`** (T Def `defvine`; figure-defs §1(a), V2): the atomic group `S` is a block with
joints `{j₁, j₂}`, and for some numbers `k⃗ ≥ 0` of inserted rungs (F37, DH23's family; for (II) every
`m ≥ 1` rungs, F72) the undirected multigraph of `S` is isomorphic to the expanded template `T_X(k⃗)` by a map
sending `{j₁, j₂}` onto `{J₁, J₂}`. No direction clause (the direction facts follow from the block axioms, 2-cut lemma). -/
def IsVine (X : VineType) (S : Finset V) (j₁ j₂ : V) : Prop :=
  M.IsBlock S j₁ j₂ ∧ ∃ k : List ℕ, k.length = X.template.slots.length ∧
    ∃ f : V → ℕ, Set.InjOn f S ∧ S.image f = Finset.range (X.expand k).n ∧
      ({f j₁, f j₂} : Finset ℕ) = {0, 1} ∧
      (M.groupBonds S).map (Sym2.map f) = ((X.expand k).bonds.map fun p => s(p.1, p.2) : Multiset _)

/-! ## §7 Cuts (T Def `defcut`, L2117–L2127; F40, figure-defs §4) -/

/-- **The cut** of the atom `v` along the darts `x₁` (incoming dart of `ℓ₁` at `v`) and `x₂` (outgoing
dart of `ℓ₂` at `v`), creating the new atom `v₂`: `x₁, x₂` stay at `v₁ = v`, every other dart at `v`
moves to `v₂` (F40: well defined for self-loops). The preconditions are `IsCutData`. -/
def cut (v v₂ : V) (x₁ x₂ : D) : Molecule V D where
  atoms := insert v₂ M.atoms
  atom := fun x => if M.atom x = v ∧ x ≠ x₁ ∧ x ≠ x₂ then v₂ else M.atom x
  mate := M.mate
  out := M.out
  atom_mem := fun x => by
    split_ifs
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (M.atom_mem x)
  mate_mate := M.mate_mate
  mate_ne := M.mate_ne
  out_mate := M.out_mate

/-- The cut data are admissible: `x₁` incoming and `x₂` outgoing at `v` on two different bonds
(`x₂ ≠ mate x₁`: a self-loop at `v` is one bond; B2-CL-14, FINDINGS F66), and `v₂` a fresh atom
(T Def `defcut`, L2118: two bonds of opposite directions at `v`; the remark after it allows `d(v) = 2`). -/
def IsCutData (v v₂ : V) (x₁ x₂ : D) : Prop :=
  v ∈ M.atoms ∧ v₂ ∉ M.atoms ∧ M.atom x₁ = v ∧ M.atom x₂ = v ∧ x₂ ≠ M.mate x₁ ∧ M.out x₁ = false ∧
    M.out x₂ = true

/-- An **α-cut** does not generate a new connected component; otherwise it is a **β-cut**. -/
noncomputable def IsAlphaCut (v v₂ : V) (x₁ x₂ : D) : Prop :=
  (M.cut v v₂ x₁ x₂).numComponents ≤ M.numComponents

/-! ## §8 The counting quantities (T (defcounta2), (defdev); review I9, `MOL.countq`) -/

/-- **`𝔈`** (T (defcounta2)): the number of restricted `(c_v)`-decorations (lattice labels on the coset
`w + ℤ_L^d`) satisfying the admissibility predicate `Adm` (the inherited requirements, e.g. (a)–(f) of
T L2101–L2107 and the ladder-gap scales), maximized over the parameters `c` (with `c_v = 0` at
degree-4 atoms), `β` and `k⁰` (constant on bonds). `ℕ∞`-valued: an infinite set gives `⊤`, never the
junk `0`. -/
noncomputable def countE {d : ℕ} (L γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) : ℕ∞ :=
  ⨆ (c : V → Mom d) (_ : ∀ v ∈ M.atoms, M.deg v = 4 → c v = 0) (β : V → ℝ) (k0 : D → Mom d)
    (_ : ∀ x, k0 (M.mate x) = k0 x),
    {κ | M.IsDecoration L w c κ ∧ M.IsRestricted L γ δ w β k0 κ ∧ Adm κ}.encard

/-- The ladder weight `𝔛 = min((log L)², 1 + δ L^{2γ} P)` (T Prop `ladderl1old`, (ladderl1)). -/
noncomputable def ladderWeight (L γ δ P : ℝ) : ℝ := min (Real.log L ^ 2) (1 + δ * L ^ (2 * γ) * P)

/-- **`𝔄`** (T (defcounta2)): `𝔄 = 𝔈 · L^{-(d-γ)χ} (C₁^{-1}δ^{1/2})^χ ∏_j 𝔛_j^{z_j}` over the maximal
ladders `𝕃_j` (length `z_j`, gap scale `P_j = P 𝕃_j`; the restriction `|r_j| ∼₀ P_j` is part of `Adm`). -/
noncomputable def countA {d : ℕ} (L γ δ C₁ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (P : Finset V → ℝ) : ℝ≥0∞ :=
  (M.countE L γ δ w Adm : ℝ≥0∞) *
    ENNReal.ofReal (L ^ (-((d : ℝ) - γ) * M.circuitRank) * (C₁⁻¹ * δ ^ (1 / 2 : ℝ)) ^ M.circuitRank *
      ∏ S ∈ M.maximalLadders, ladderWeight L γ δ (P S) ^ ladderLength S)

end Molecule

/-- **`ℐ` is a deviation** of an operation `𝕄_pre ↦ 𝕄_pos` (T (defdev), L2135; F59, B2-CL-7): the operation
bound `𝔄_pre ≤ ℐ · 𝔄_pos`. This is the source's definition (T calls any such `ℐ` "the deviation"), and the form
in which per-operation bounds are stated. -/
def IsDeviation (Apre Apos I : ℝ≥0∞) : Prop := Apre ≤ I * Apos

/-- **The deviation ratio** `𝔄_pre / 𝔄_pos` in `ℝ≥0∞` (F59, B2-CL-7). It is the least `ℐ` with
`IsDeviation 𝔄_pre 𝔄_pos ℐ` only when `𝔄_pos ≠ ⊤` and (`𝔄_pos = 0 → 𝔄_pre = 0`) (probe
`deviation_le_iff_of_zero_compatible`). Otherwise it is not:
- `𝔄_pos = 0 < 𝔄_pre`: the ratio is `⊤`, but no `ℐ` works, since `⊤ · 0 = 0`;
- `𝔄_pos = ⊤ ≠ 𝔄_pre`: the ratio is `0`, which is not a bound, and the infimum is not attained;
- `(⊤, ⊤)`: the ratio is `0`.

Operation bounds are therefore stated with `IsDeviation`, not through this ratio. -/
noncomputable def deviation (Apre Apos : ℝ≥0∞) : ℝ≥0∞ := Apre / Apos

/-- **Atom labels** (T Prop `finalmol`, Remark `remiota`, Prop `excessprop1`): α-atoms with the dyadic
gap scale `Q_v ∈ [L^{-1}, L^{-γ+η}]` and `κ_v ∈ {0, 50}`, β-atoms, and ε-atoms (neither). -/
inductive AtomLabel
  | alpha (Q : ℝ) (κ : ℕ)
  | beta
  | eps

end WaveTurbulence
