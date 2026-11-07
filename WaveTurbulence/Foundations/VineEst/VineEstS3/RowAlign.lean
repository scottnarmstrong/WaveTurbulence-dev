/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.VineMonotone
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyRowEquiv
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLInteriorPredecessor
public import Mathlib.Logic.Equiv.Fintype
public import WaveTurbulence.Foundations.Molecule.CorePlacements
public import WaveTurbulence.Foundations.Molecule.VineTwistPlacements
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionData

/-! # Row alignment, part 2: block-aligned, predecessor-monotone branch enumeration (R22 (2))

`assemblyBranchBij hM9 B : ↥(U.erase a) ≃ VIdx` sends an interior atom `z` to a row of the vine block `vineOf z`, ordered
inside the block by decreasing depth.  Along the interior predecessor relation (a strictly deeper heavy-path descendant)
it is lexicographically increasing (`vineOf_desc_le`), so `assemblyIntOrder` is a `CLIntOrder`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.Twist VineParamContract TTree RegRed Finset
open WaveTurbulence.Reg.Skeleton
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- A bijection to `Fin N` that is strictly increasing in a given key (ties broken arbitrarily). -/
theorem exists_sorted_equiv {X κ : Type*} [Fintype X] [LinearOrder κ] (key : X → κ) (N : ℕ)
    (h : Fintype.card X = N) : ∃ e : X ≃ Fin N, ∀ x y, key x < key y → e x < e y := by
  classical
  let e0 := Fintype.equivFinOfCardEq h
  let g : X → κ ×ₗ Fin N := fun x => toLex (key x, e0 x)
  have hg : Function.Injective g := by
    intro x y hxy
    have := congrArg (fun z => (ofLex z).2) hxy
    exact e0.injective this
  let _ : LinearOrder X := LinearOrder.lift' g hg
  refine ⟨(Fintype.orderIsoFinOfCardEq X h).symm.toEquiv, fun x y hxy => ?_⟩
  have hlt : x < y := by
    show g x < g y
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hxy)
  exact (Fintype.orderIsoFinOfCardEq X h).symm.lt_iff_lt.mpr hlt

/-- The interior predecessor of `v` is a heavy-path descendant of `v`. -/
theorem clInteriorPredecessor_isDesc (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (v u : ↥(clInteriorBranches R)) (hu : clInteriorPredecessor hU R v = some u) :
    v.1.toNode.IsDesc u.1.toNode := by
  unfold clInteriorPredecessor at hu
  obtain ⟨z, hmem, hz, hzu⟩ := Option.pmap_eq_some_iff.mp hu
  have hd := (signPredecessor_target _ _ _ hz).2.2
  have h1 := clInteriorCrop_node hU R v
  have h2 := clForestBranch_node hU R z
  have h3 : u.1 = ((clForestBranchEquiv hU R) z).1 := congrArg (fun q : ↥(clInteriorBranches R) => q.1) hzu
  rw [← h1]
  rw [h3, ← h2]
  obtain ⟨hd1, hd2⟩ := hd
  refine ⟨rfl, ?_⟩
  show a.1.2 ++ (clInteriorCrop hU R v).1.2 <+: a.1.2 ++ z.1.2
  exact (List.prefix_append_right_inj _).mpr hd2

theorem isDesc_trans {x y z : GNode G.tree} (h1 : x.IsDesc y) (h2 : y.IsDesc z) : x.IsDesc z :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

theorem piece_upper_isDesc (B : CLChainAssembly G R n) (i : Fin n) :
    (assemblyPieceAt B i).upper.toNode.IsDesc (assemblyPieceAt B i).lower.toNode :=
  (Mole.cl_parent_strict_descendant G (assemblyPieceAt B i).vine.1 (assemblyPiece_cl B i)).1

theorem piece_upper_len_lt (B : CLChainAssembly G R n) (i : Fin n) :
    (assemblyPieceAt B i).upper.1.2.length < (assemblyPieceAt B i).lower.1.2.length :=
  (Mole.cl_parent_strict_descendant G (assemblyPieceAt B i).vine.1 (assemblyPiece_cl B i)).2

/-- The lower joints of the pieces form a descending chain: the lower joint of a later piece is a strict ancestor of
the lower joint of an earlier piece. -/
theorem assemblyPiece_lower_isDesc (B : CLChainAssembly G R n) (i j : Fin n) (hij : i ≤ j) :
    (assemblyPieceAt B j).lower.toNode.IsDesc (assemblyPieceAt B i).lower.toNode ∧
      (i < j → (assemblyPieceAt B j).lower.1.2.length < (assemblyPieceAt B i).lower.1.2.length) := by
  induction B with
  | single hV R =>
    have : i = j := Subsingleton.elim _ _
    subst this
    exact ⟨⟨rfl, List.prefix_refl _⟩, fun h => absurd h (lt_irrefl _)⟩
  | @append S T a' b' c' n' RP B X hT hi hU R ih =>
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · exact ⟨⟨rfl, List.prefix_refl _⟩, fun h => absurd h (lt_irrefl _)⟩
      · have hn : 0 < n' := B.length_pos
        have h1 := (ih ⟨0, hn⟩ j' (Fin.mk_le_of_le_val (Nat.zero_le _))).1
        have h2 : (assemblyPieceAt B ⟨0, hn⟩).lower = (assemblyPieceAt (.append B hT hi hU R) 0).upper :=
          assemblyPiece_zero_lower B hn
        have h3 := piece_upper_isDesc (.append B hT hi hU R) 0
        have h4 := piece_upper_len_lt (.append B hT hi hU R) 0
        rw [← h2] at h3 h4
        refine ⟨isDesc_trans h1 h3, fun _ => ?_⟩
        have h5 := h1.2.length_le
        exact lt_of_le_of_lt h5 h4
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · exact absurd (Fin.le_def.mp hij) (by simp)
      · exact ih i' j' (Fin.succ_le_succ_iff.mp hij) |>.imp id (fun h hlt => h (Fin.succ_lt_succ_iff.mp hlt))

section Align
variable (hM9 : VINEPARAM) (B : CLChainAssembly G R n)

/-- The chart-slot bijection: an interior atom to its row, block preserving. -/
noncomputable def chartRowEquiv : ↥(clInteriorBranches R) ≃ (assemblyShape hM9 B).VIdx :=
  (assemblyAtomEquiv hM9 B).symm.trans (assemblyVectorEquiv hM9 B)

theorem chartRowEquiv_fst (z : ↥(clInteriorBranches R)) :
    ((chartRowEquiv hM9 B z).1 : ℕ) = (vineOf hM9 B z : ℕ) := rfl

/-- Depth of the interior atom at the row `⟨i, j⟩` of the chart bijection. -/
noncomputable def slotDepth (x : (assemblyShape hM9 B).VIdx) : ℕᵒᵈ :=
  OrderDual.toDual ((chartRowEquiv hM9 B).symm x).1.1.2.length

/-- Within each block, reorder the slots by decreasing depth. -/
noncomputable def blockSort (i : Fin (assemblyShape hM9 B).I) :
    Fin ((assemblyShape hM9 B).n i) ≃ Fin ((assemblyShape hM9 B).n i) :=
  (exists_sorted_equiv (fun j : Fin ((assemblyShape hM9 B).n i) => slotDepth hM9 B ⟨i, j⟩) _
    (Fintype.card_fin _)).choose

theorem blockSort_lt (i : Fin (assemblyShape hM9 B).I) (j j' : Fin ((assemblyShape hM9 B).n i))
    (h : slotDepth hM9 B ⟨i, j⟩ < slotDepth hM9 B ⟨i, j'⟩) : blockSort hM9 B i j < blockSort hM9 B i j' :=
  (exists_sorted_equiv (fun j : Fin ((assemblyShape hM9 B).n i) => slotDepth hM9 B ⟨i, j⟩) _
    (Fintype.card_fin _)).choose_spec j j' h

/-- The aligned branch bijection: block `vineOf z`, decreasing depth inside the block. -/
noncomputable def assemblyBranchBij : ↥(clInteriorBranches R) ≃ (assemblyShape hM9 B).VIdx :=
  (chartRowEquiv hM9 B).trans (Equiv.sigmaCongrRight (blockSort hM9 B))

theorem assemblyBranchBij_fst (z : ↥(clInteriorBranches R)) :
    ((assemblyBranchBij hM9 B z).1 : ℕ) = (vineOf hM9 B z : ℕ) := rfl

theorem assemblyBranchBij_lexLt (u v : ↥(clInteriorBranches R))
    (h : vineOf hM9 B u < vineOf hM9 B v ∨
      (vineOf hM9 B u = vineOf hM9 B v ∧ v.1.1.2.length < u.1.1.2.length)) :
    (assemblyShape hM9 B).LexLt (assemblyBranchBij hM9 B u) (assemblyBranchBij hM9 B v) := by
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · have hu : (chartRowEquiv hM9 B u).1 = (chartRowEquiv hM9 B v).1 := Fin.ext (by
      rw [chartRowEquiv_fst, chartRowEquiv_fst, h1])
    have hkey : slotDepth hM9 B (chartRowEquiv hM9 B u) < slotDepth hM9 B (chartRowEquiv hM9 B v) := by
      simp only [slotDepth, Equiv.symm_apply_apply]
      exact OrderDual.toDual_lt_toDual.mpr h2
    simp only [assemblyBranchBij, Equiv.trans_apply, Equiv.sigmaCongrRight_apply]
    revert hkey hu
    generalize chartRowEquiv hM9 B u = xu
    generalize chartRowEquiv hM9 B v = xv
    obtain ⟨i, ju⟩ := xu
    obtain ⟨i', jv⟩ := xv
    intro hu hkey
    have hi : i = i' := hu
    subst hi
    exact Or.inr ⟨rfl, blockSort_lt hM9 B i ju jv hkey⟩

/-- The aligned, predecessor-monotone enumeration of the interior branches. -/
noncomputable def assemblyIntOrder : CLIntOrder B.isBlock R where
  e := (assemblyBranchBij hM9 B).trans (assemblyRowEquiv hM9 B).symm
  prev v u hu := by
    have hdesc := clInteriorPredecessor_isDesc B.isBlock R v u hu
    have hlen := clInteriorPredecessor_deeper B.isBlock R v u hu
    have hle := vineOf_desc_le hM9 B v (u.1.1.2.length - v.1.1.2.length - 1) u hdesc (by omega)
    apply assemblyRowEquiv_symm_lt
    apply assemblyBranchBij_lexLt
    rcases hle.lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hlen⟩

theorem assemblyIntOrder_block (z : ↥(clInteriorBranches R)) :
    (assemblyRowEquiv hM9 B ((assemblyIntOrder hM9 B).e z)).1 = (assemblyBranchBij hM9 B z).1 := by
  simp only [assemblyIntOrder, Equiv.trans_apply, Equiv.apply_symm_apply]

end Align

theorem exists_equiv_extending {X Y D : Type*} [Fintype X] [Fintype Y] [Finite D] (hc : Fintype.card X = Fintype.card Y)
    (f : D → X) (g : D → Y) (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ e : X ≃ Y, ∀ d, e (f d) = g d := by
  classical
  let e0 := Fintype.equivOfCardEq hc
  have hf' : Function.Injective (e0 ∘ f) := e0.injective.comp hf
  let e1 : {y // y ∈ Set.range (e0 ∘ f)} ≃ {y // y ∈ Set.range g} :=
    (Equiv.ofInjective _ hf').symm.trans (Equiv.ofInjective g hg)
  let σ : Equiv.Perm Y := e1.extendSubtype
  refine ⟨e0.trans σ, fun d => ?_⟩
  have hmem : (e0 (f d)) ∈ Set.range (e0 ∘ f) := ⟨d, rfl⟩
  show σ (e0 (f d)) = g d
  have := e1.extendSubtype_apply_of_mem (e0 (f d)) hmem
  rw [this]
  simp only [e1, Equiv.trans_apply]
  have : (Equiv.ofInjective (e0 ∘ f) hf').symm ⟨e0 (f d), hmem⟩ = d := by
    apply (Equiv.ofInjective (e0 ∘ f) hf').injective
    simp
  rw [this]
  rfl

section Anchor

theorem sourcePairAt_eq_cases (ℓ ℓ' : GLeaf G.tree) (h : sourcePairAt G ℓ = sourcePairAt G ℓ') :
    ℓ.1 = ℓ'.1 ∨ ℓ.1 = (G.pair ℓ').1 := by
  unfold sourcePairAt at h
  split_ifs at h <;> simp only [Prod.mk.injEq] at h <;> tauto

theorem placement_lower_eq (P P' : CorePlacement G) (h : P.retained.1 = P'.retained.1) : P.lower = P'.lower := by
  have h1 := P.child
  have h2 := P'.child
  have hn : (P.lower.child P.keep) = (P'.lower.child P'.keep) := by
    rw [← h1, ← h2]
    exact Subtype.ext h
  have e1 := congrArg (fun x : GNode G.tree => x.1.1) hn
  have e2 := congrArg (fun x : GNode G.tree => x.1.2) hn
  change P.lower.1.1 = P'.lower.1.1 at e1
  change P.lower.1.2 ++ [P.keep] = P'.lower.1.2 ++ [P'.keep] at e2
  have e3 := congrArg List.dropLast e2
  simp only [List.dropLast_concat] at e3
  exact Subtype.ext (Prod.ext e1 e3)

theorem child_isDesc (v : GBranch G.tree) (i : Fin 3) : v.toNode.IsDesc (v.child i) :=
  ⟨rfl, ⟨[i], rfl⟩⟩

/-- Two core placements whose lower joints are comparable and whose retained leaves lie in the same source pair have
the same lower joint. -/
theorem placement_pair_eq (hG : G.IsPlain) (P P' : CorePlacement G)
    (hc : P.lower.toNode.IsDesc P'.lower.toNode ∨ P'.lower.toNode.IsDesc P.lower.toNode)
    (h : pairOfLeaf G hG P.retained = pairOfLeaf G hG P'.retained) : P.lower = P'.lower := by
  rcases sourcePairAt_eq_cases P.retained P'.retained (congrArg Subtype.val h) with h1 | h1
  · exact placement_lower_eq P P' h1
  · exfalso
    have hr : P.retained.toNode = (G.pair P'.retained).toNode := Subtype.ext h1
    have hr' : P'.retained.toNode = (G.pair P.retained).toNode := by
      have : G.pair (G.pair P'.retained) = P'.retained := G.pair_pair _
      rw [← this]
      exact congrArg (fun l => (G.pair l).toNode) (Subtype.ext h1).symm ▸ rfl
    rcases hc with hc | hc
    · apply P.paired_outside
      rw [← hr', P'.child]
      exact isDesc_trans hc (child_isDesc _ _)
    · apply P'.paired_outside
      rw [← hr, P.child]
      exact isDesc_trans hc (child_isDesc _ _)

variable (hG : G.IsPlain) (B : CLChainAssembly G R n)

open Classical in
/-- The designated regional pair of the vine `i`: the pair of the retained leaf of a core placement at its lower joint
(when one exists with its pair in the region). -/
noncomputable def vineAnchor (i : Fin n) : Option ↥(clRegionalPairs hG U) :=
  if h : ∃ P : CorePlacement G, IsPlacementAt G (assemblyPieceAt B i).atoms (assemblyPieceAt B i).lower P ∧
      pairOfLeaf G hG P.retained ∈ clRegionalPairs hG U then
    some ⟨pairOfLeaf G hG h.choose.retained, h.choose_spec.2⟩
  else none

theorem vineAnchor_spec (i : Fin n) (p : ↥(clRegionalPairs hG U)) (hp : vineAnchor hG B i = some p) :
    ∃ P : CorePlacement G, IsPlacementAt G (assemblyPieceAt B i).atoms (assemblyPieceAt B i).lower P ∧
      p.1 = pairOfLeaf G hG P.retained := by
  unfold vineAnchor at hp
  split_ifs at hp with h
  · exact ⟨h.choose, h.choose_spec.1, by rw [← Option.some.inj hp]⟩

theorem vineAnchor_inj (i j : Fin n) (p : ↥(clRegionalPairs hG U)) (hi : vineAnchor hG B i = some p)
    (hj : vineAnchor hG B j = some p) : i = j := by
  obtain ⟨P, hP, hpP⟩ := vineAnchor_spec hG B i p hi
  obtain ⟨P', hP', hpP'⟩ := vineAnchor_spec hG B j p hj
  have hpair : pairOfLeaf G hG P.retained = pairOfLeaf G hG P'.retained := hpP.symm.trans hpP'
  wlog hle : i ≤ j generalizing i j P P'
  · exact (this j i hj hi P' hP' hpP' P hP hpP hpair.symm (le_of_not_ge hle)).symm
  have hdesc := (assemblyPiece_lower_isDesc B i j hle)
  have hl := placement_pair_eq hG P P' (Or.inr (by rw [hP.1, hP'.1]; exact hdesc.1)) hpair
  rw [hP.1, hP'.1] at hl
  by_contra hne
  have hlt : i < j := lt_of_le_of_ne hle hne
  have := hdesc.2 hlt
  rw [hl] at this
  exact lt_irrefl _ this

variable (hM9 : VINEPARAM)

theorem card_pairs_eq_vidx : Fintype.card ↥(clRegionalPairs hG U) = Fintype.card (assemblyShape hM9 B).VIdx :=
  (Fintype.card_coe _).trans ((card_clRegionalPairs B.isBlock R hG).trans
    ((assemblyShape_M hM9 B).symm.trans (Sumint.card_vector_index _).symm))

theorem exists_pairBij : ∃ e : ↥(clRegionalPairs hG U) ≃ (assemblyShape hM9 B).VIdx,
    ∀ (i : Fin n) (p : ↥(clRegionalPairs hG U)), vineAnchor hG B i = some p → (e p).1 = i := by
  obtain ⟨e, he⟩ := exists_equiv_extending (D := {i : Fin n // (vineAnchor hG B i).isSome})
    (card_pairs_eq_vidx hG B hM9)
    (fun i => ((vineAnchor hG B i.1).get i.2))
    (fun i => (⟨i.1, ⟨0, by simp [SumintShape.n]⟩⟩ : (assemblyShape hM9 B).VIdx))
    (fun i j h => Subtype.ext (vineAnchor_inj hG B i.1 j.1 _ (Option.eq_some_of_isSome i.2)
      (by
        have h' : (vineAnchor hG B i.1).get i.2 = (vineAnchor hG B j.1).get j.2 := h
        rw [h']
        exact Option.eq_some_of_isSome j.2)))
    (fun i j h => Subtype.ext (congrArg Sigma.fst h))
  refine ⟨e, fun i p hp => ?_⟩
  have hs : (vineAnchor hG B i).isSome := by rw [hp]; rfl
  have := he ⟨i, hs⟩
  have hpg : (vineAnchor hG B i).get hs = p := by simp [hp]
  simp only [hpg] at this
  exact congrArg Sigma.fst this

/-- The aligned pair bijection: the anchor pair of each vine `i` lies in block `i`. -/
noncomputable def assemblyPairBij : ↥(clRegionalPairs hG U) ≃ (assemblyShape hM9 B).VIdx :=
  (exists_pairBij hG B hM9).choose

theorem assemblyPairBij_anchor (i : Fin n) (p : ↥(clRegionalPairs hG U)) (hp : vineAnchor hG B i = some p) :
    (assemblyPairBij hG B hM9 p).1 = i := (exists_pairBij hG B hM9).choose_spec i p hp

/-- The aligned pair enumeration. -/
noncomputable def assemblyPairOrder : ↥(clRegionalPairs hG U) ≃ Fin (clLocalOrder1 R) :=
  (assemblyPairBij hG B hM9).trans (assemblyRowEquiv hM9 B).symm

end Anchor

end WaveTurbulence.VineEstS3
