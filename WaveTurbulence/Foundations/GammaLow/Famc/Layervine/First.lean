/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Defs
public import WaveTurbulence.Foundations.TVine.Struct.Statement
public import WaveTurbulence.Foundations.LayerCnt.Layervine
/-! # TARGET `layervine`, first bound, for T-vines (packet L5c, layervine′)

TARGET L1519: "`𝕍` consists of at most three ladders plus less than `20` extra atoms, so we can apply Proposition
`layerlad` to the part of (sumofexp0) involving atoms and bonds in one of these ladders, while the part involving
the extra atoms contribute at most a factor of `C_0^{100𝔇} ≤ C_2`." For T-vines the ladder count is N3 Theorem 6(iv)
(L3's `LaddersStatement`: at most `3` disjoint ladders, at most `13` uncovered atoms) and the groups are the pieces
(N3 §1.3, `Molecule.tvineGroups`).

The one new fact: **every interior rung of a ladder inside a T-vine lies in one piece** (`ladder_rung_samePiece`):
a set of at most two bonds separating the two atoms of a double-bonded rung would have to consist of the two rung
bonds, but the previous rung and the two rails still connect them. Hence the incoherent interior rungs of each ladder
inject into the incoherent pieces (pieces have at most `3` atoms, L3's `PieceShapeStatement`), and main's
multi-ladder layering bound `LayerCnt.multi_sum_le` applies with `G = g` (the T-vine incoherency index). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc
open Finset WaveTurbulence.LayerCnt WaveTurbulence.Vine

/-- **NAMED INPUT (N3 Theorem 6 (iv), shape constants; owner L3).** Exactly L3's `TVine.Struct.LaddersStatement`
(research-gamma-half-3/NOTES.txt L170, L291–L305) at the universe of garden molecules. -/
def LaddersInput : Prop := TVine.Struct.LaddersStatement.{0, 0}

/-- **NAMED INPUT (N2 Proposition 1.17(b), piece shape; owner L3).** Exactly L3's
`TVine.Struct.PieceShapeStatement` (= L6's `TVinePiecesInput`) at the universe of garden molecules. -/
def PieceShapeInput : Prop := TVine.Struct.PieceShapeStatement.{0, 0}

section rung
variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

/-- A bond not removed joins its ends in `ConnectedWithout`. -/
theorem connectedWithout_of_bond {S : Finset V} {F : Finset D} (hF : F ⊆ M.bonds) {a b : V}
    (ha : a ∈ S) (hb : b ∈ S) {x : D} (hxb : x ∈ M.bonds) (hxe : M.ends x = s(a, b)) (hxF : x ∉ F) :
    M.ConnectedWithout S F a b := by
  have hmF : M.mate x ∉ F := by
    intro h
    have h1 := (Finset.mem_filter.mp (hF h)).2
    have h2 := (Finset.mem_filter.mp hxb).2
    rw [M.out_mate, h2] at h1
    exact absurd h1 (by decide)
  have hxe' : s(M.atom x, M.atom (M.mate x)) = s(a, b) := hxe
  rcases Sym2.eq_iff.mp hxe' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Relation.EqvGen.rel _ _ ⟨x, ⟨h1 ▸ ha, h2 ▸ hb⟩, hxF, hmF, h1, h2⟩
  · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨x, ⟨h1 ▸ hb, h2 ▸ ha⟩, hxF, hmF, h1, h2⟩)

/-- A positive multiplicity gives a bond with these ends. -/
theorem exists_bond_of_pos {a b : V} (h : 0 < M.bondsBetween a b) :
    ∃ x ∈ M.bonds, M.ends x = s(a, b) := by
  obtain ⟨x, hx⟩ := Finset.card_pos.mp h
  exact ⟨x, (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩

variable {M}

theorem ladder_u_mem {m : ℕ} {u v : Fin (m + 1) → V} (j : Fin (m + 1)) : u j ∈ Molecule.ladderAtoms u v :=
  mem_union_left _ (mem_image_of_mem _ (mem_univ _))

theorem ladder_v_mem {m : ℕ} {u v : Fin (m + 1) → V} (j : Fin (m + 1)) : v j ∈ Molecule.ladderAtoms u v :=
  mem_union_right _ (mem_image_of_mem _ (mem_univ _))

/-- **An interior rung of a ladder lies in one piece**: no set of at most two bonds separates its two atoms inside
any group containing the ladder. -/
theorem ladder_rung_samePiece {S : Finset V} {m : ℕ} {u v : Fin (m + 1) → V} (hL : M.IsLadder u v)
    (hLS : Molecule.ladderAtoms u v ⊆ S) (c : Fin m) : M.SamePiece S (u c.succ) (v c.succ) := by
  have hinj := hL.2.1
  have huu : ∀ j k : Fin (m + 1), u j = u k → j = k := fun j k h => by
    have := hinj (a₁ := .inl j) (a₂ := .inl k) h
    simpa using this
  have hvv : ∀ j k : Fin (m + 1), v j = v k → j = k := fun j k h => by
    have := hinj (a₁ := .inr j) (a₂ := .inr k) h
    simpa using this
  have huv : ∀ j k : Fin (m + 1), u j ≠ v k := fun j k h => by
    have := hinj (a₁ := .inl j) (a₂ := .inr k) h
    simp at this
  have hcs : c.castSucc ≠ c.succ := (Fin.castSucc_lt_succ : c.castSucc < c.succ).ne
  intro F hF hFc
  set E := M.bonds.filter (fun x => M.ends x = s(u c.succ, v c.succ)) with hEdef
  have hE : E.card = 2 := hL.2.2.2.1 c.succ
  by_cases hEF : E ⊆ F
  · have hFE : F = E := (Finset.eq_of_subset_of_card_le hEF (by omega)).symm
    have hnot : ∀ {a b : V}, s(a, b) ≠ s(u c.succ, v c.succ) → ∀ x, M.ends x = s(a, b) → x ∉ F := by
      intro a b hab x hx hxF
      rw [hFE] at hxF
      exact hab (hx.symm.trans (Finset.mem_filter.mp hxF).2)
    have hr := hL.2.2.2.2 c
    obtain ⟨r1, hr1b, hr1e⟩ := exists_bond_of_pos M (show 0 < M.bondsBetween (u c.castSucc) (u c.succ) by
      rw [hr.1]; norm_num)
    obtain ⟨r2, hr2b, hr2e⟩ := exists_bond_of_pos M (show 0 < M.bondsBetween (u c.castSucc) (v c.castSucc) by
      rw [hL.2.2.2.1 c.castSucc]; norm_num)
    obtain ⟨r3, hr3b, hr3e⟩ := exists_bond_of_pos M (show 0 < M.bondsBetween (v c.castSucc) (v c.succ) by
      rw [hr.2.1]; norm_num)
    have n1 : s(u c.castSucc, u c.succ) ≠ s(u c.succ, v c.succ) := by
      intro h
      rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hcs (huu _ _ h1)
      · exact huv _ _ h1
    have n2 : s(u c.castSucc, v c.castSucc) ≠ s(u c.succ, v c.succ) := by
      intro h
      rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hcs (huu _ _ h1)
      · exact huv _ _ h1
    have n3 : s(v c.castSucc, v c.succ) ≠ s(u c.succ, v c.succ) := by
      intro h
      rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact huv _ _ h1.symm
      · exact hcs (hvv _ _ h1)
    have s1 := connectedWithout_of_bond M hF (hLS (ladder_u_mem _)) (hLS (ladder_u_mem _)) hr1b hr1e
      (hnot n1 r1 hr1e)
    have s2 := connectedWithout_of_bond M hF (hLS (ladder_u_mem _)) (hLS (ladder_v_mem _)) hr2b hr2e
      (hnot n2 r2 hr2e)
    have s3 := connectedWithout_of_bond M hF (hLS (ladder_v_mem _)) (hLS (ladder_v_mem _)) hr3b hr3e
      (hnot n3 r3 hr3e)
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ s1) (Relation.EqvGen.trans _ _ _ s2 s3)
  · obtain ⟨x, hxE, hxF⟩ := Finset.not_subset.mp hEF
    exact connectedWithout_of_bond M hF (hLS (ladder_u_mem _)) (hLS (ladder_v_mem _))
      (Finset.mem_filter.mp hxE).1 (Finset.mem_filter.mp hxE).2 hxF

/-- Four incidences into `S` give internal degree at least four. -/
theorem four_le_degIn_of_incidences {S : Finset V} {x : V} {ns : Fin 4 → V} (R : FourIncidences M x ns)
    (hns : ∀ k, ns k ∈ S) (hx : x ∈ S) : 4 ≤ M.degIn S x := by
  classical
  unfold Molecule.degIn
  have hsub : univ.image R.dart ⊆ (M.dartsAt x).filter (fun y => M.InGroup S y) := by
    intro y hy
    obtain ⟨k, -, rfl⟩ := mem_image.mp hy
    refine mem_filter.mpr ⟨?_, ?_, ?_⟩
    · simp [Molecule.dartsAt, R.atom_eq k]
    · rw [R.atom_eq k]; exact hx
    · rw [R.neighbor_eq k]; exact hns k
  have hc : (univ.image R.dart).card = 4 := by
    rw [card_image_of_injective _ R.injective]; simp
  calc 4 = (univ.image R.dart).card := hc.symm
    _ ≤ _ := card_le_card hsub

end rung

section count
variable {w : ℕ}

/-- A group containing two atoms of different layers is incoherent (stated without `Fintype V`, so that the
decidability instance is the one of `tvineIncoherency`). -/
theorem mem_incoherent_filter {V : Type} [DecidableEq V] {groups : Finset (Finset V)} {layer : V → ℕ}
    {P : Finset V} (hP : P ∈ groups) {x y : V} (hx : x ∈ P) (hy : y ∈ P) (hne : ¬ layer x = layer y) :
    P ∈ groups.filter (fun g => ¬ ∀ x ∈ g, ∀ y ∈ g, layer x = layer y) :=
  Finset.mem_filter.mpr ⟨hP, fun h => hne (h x hx y hy)⟩

/-- Abstract counting: rungs `{x i, y i}` (`i ∈ [1, m)`, pairwise disjoint) each inside a group of at most three
atoms; the incoherent rungs inject into the incoherent groups. -/
theorem card_incoherent_rungs_le {V : Type} [DecidableEq V] (groups : Finset (Finset V))
    (hcard : ∀ P ∈ groups, P.card ≤ 3) (f : V → ℕ) (m : ℕ) (x y : ℕ → V)
    (H : ∀ i ∈ Ico 1 m, ∃ P ∈ groups, x i ∈ P ∧ y i ∈ P)
    (hxy : ∀ i ∈ Ico 1 m, x i ≠ y i)
    (hdist : ∀ i ∈ Ico 1 m, ∀ j ∈ Ico 1 m, i ≠ j → x i ≠ x j ∧ x i ≠ y j ∧ y i ≠ x j ∧ y i ≠ y j) :
    ((Ico 1 m).filter (fun i => ¬ f (x i) = f (y i))).card ≤
      (groups.filter (fun g => ¬ ∀ a ∈ g, ∀ b ∈ g, f a = f b)).card := by
  let φ : ℕ → Finset V := fun i => if h : i ∈ Ico 1 m then Classical.choose (H i h) else ∅
  have hφ : ∀ i (h : i ∈ Ico 1 m), φ i ∈ groups ∧ x i ∈ φ i ∧ y i ∈ φ i := by
    intro i h
    have hs := Classical.choose_spec (H i h)
    simp only [φ, h, dite_true]
    exact hs
  apply Finset.card_le_card_of_injOn φ
  · intro i hi
    obtain ⟨hi, hne⟩ := Finset.mem_filter.mp hi
    obtain ⟨hP, hu, hv⟩ := hφ i hi
    exact Finset.mem_filter.mpr ⟨hP, fun h => hne (h _ hu _ hv)⟩
  · intro i hi j hj hij
    have hi' := (Finset.mem_filter.mp hi).1
    have hj' := (Finset.mem_filter.mp hj).1
    by_contra hne
    obtain ⟨hP, hui, hvi⟩ := hφ i hi'
    obtain ⟨-, huj, hvj⟩ := hφ j hj'
    have hφij : φ i = φ j := hij
    rw [← hφij] at huj hvj
    obtain ⟨d1, d2, d3, d4⟩ := hdist i hi' j hj' hne
    have hsub : ({x i, y i, x j, y j} : Finset V) ⊆ φ i := by
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl <;> assumption
    have h4 : ({x i, y i, x j, y j} : Finset V).card = 4 := by
      have e1 : x j ∉ ({y j} : Finset V) := by simpa using hxy j hj'
      have e2 : y i ∉ ({x j, y j} : Finset V) := by simp [d3, d4]
      have e3 : x i ∉ ({y i, x j, y j} : Finset V) := by simp [hxy i hi', d1, d2]
      rw [card_insert_of_notMem e3, card_insert_of_notMem e2, card_insert_of_notMem e1, card_singleton]
    have := (card_le_card hsub).trans (hcard _ hP)
    omega

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

/-- Interior rung atoms of a ladder inside a block are not its joints (they have four incidences inside). -/
theorem ladder_interior_not_joint {S : Finset V} {a b : V} (hB : M.IsBlock S a b) {m : ℕ}
    {u v : Fin (m + 1) → V} (hL : M.IsLadder u v) (hLS : Molecule.ladderAtoms u v ⊆ S) {i : ℕ}
    (hi1 : 1 ≤ i) (hi2 : i ≤ m - 1) :
    lad u i ∈ (S.erase a).erase b ∧ lad v i ∈ (S.erase a).erase b := by
  have hjd := Mole.block_joint_degrees M hB
  have hU := (ladderRungSeq M hL).upper i hi1 hi2
  have hV := (ladderRungSeq M hL).lower i hi1 hi2
  have hmemu : ∀ j, lad u j ∈ S := fun j => hLS (ladder_u_mem _)
  have hmemv : ∀ j, lad v j ∈ S := fun j => hLS (ladder_v_mem _)
  have hdu : 4 ≤ M.degIn S (lad u i) := four_le_degIn_of_incidences hU
    (fun k => by fin_cases k <;> simp [ladderRungSeq_u, ladderRungSeq_v, hmemu, hmemv]) (hmemu i)
  have hdv : 4 ≤ M.degIn S (lad v i) := four_le_degIn_of_incidences hV
    (fun k => by fin_cases k <;> simp [ladderRungSeq_u, ladderRungSeq_v, hmemu, hmemv]) (hmemv i)
  refine ⟨mem_erase.mpr ⟨?_, mem_erase.mpr ⟨?_, hmemu i⟩⟩, mem_erase.mpr ⟨?_, mem_erase.mpr ⟨?_, hmemv i⟩⟩⟩
  · intro h; rw [h] at hdu; omega
  · intro h; rw [h] at hdu; omega
  · intro h; rw [h] at hdv; omega
  · intro h; rw [h] at hdv; omega

/-- The piece through a non-joint atom (D11 `pieces`). -/
theorem exists_piece_through {S : Finset V} {a b x : V} (hx : x ∈ (S.erase a).erase b) :
    ∃ P ∈ M.tvineGroups S a b, ∀ y, y ∈ P ↔ y ∈ (S.erase a).erase b ∧ M.SamePiece S x y := by
  classical
  unfold Molecule.tvineGroups Molecule.pieces
  exact ⟨_, Finset.mem_image_of_mem _ hx, fun y => Finset.mem_filter⟩

/-- Pieces of a T-vine have at most three atoms (N2 Prop 1.17(b)). -/
theorem tvine_piece_card_le (hPS : PieceShapeInput) {S : Finset V} {a b : V} (hT : M.IsTVine S a b) :
    ∀ P ∈ M.tvineGroups S a b, P.card ≤ 3 := by
  intro P hP
  obtain ⟨core, -, hcore, hrest, -⟩ := hPS M S a b hT
  by_cases hPc : P = core
  · obtain ⟨x, y, z, -, -, -, rfl, -⟩ := hcore
    subst hPc
    exact (card_insert_le _ _).trans (by have := card_le_two (a := y) (b := z); omega)
  · obtain ⟨p, q, -, rfl, -⟩ := hrest P hP hPc
    exact card_le_two.trans (by norm_num)

/-- **The incoherent interior rungs of a ladder inside a T-vine inject into the incoherent pieces.** -/
theorem ladder_incCnt_le_tvineIncoherency (hPS : PieceShapeInput) {S : Finset V} {a b : V}
    (hT : M.IsTVine S a b) {m : ℕ} {u v : Fin (m + 1) → V} (hL : M.IsLadder u v)
    (hLS : Molecule.ladderAtoms u v ⊆ S) (f : V → ℕ) :
    incCnt (fun i => f (lad u i)) (fun i => f (lad v i)) 1 (m - 1) ≤ tvineIncoherency M S a b f := by
  have hm := hL.1
  have hinj := hL.2.1
  have huu : ∀ j k : Fin (m + 1), u j = u k → j = k := fun j k h => by
    have := hinj (a₁ := .inl j) (a₂ := .inl k) h
    simpa using this
  have hvv : ∀ j k : Fin (m + 1), v j = v k → j = k := fun j k h => by
    have := hinj (a₁ := .inr j) (a₂ := .inr k) h
    simpa using this
  have huv : ∀ j k : Fin (m + 1), u j ≠ v k := fun j k h => by
    have := hinj (a₁ := .inl j) (a₂ := .inr k) h
    simp at this
  have hrefl : ∀ x, M.SamePiece S x x := fun x F _ _ => Relation.EqvGen.refl _
  have H : ∀ i ∈ Ico 1 m, ∃ P ∈ M.tvineGroups S a b, lad u i ∈ P ∧ lad v i ∈ P := by
    intro i hi
    have hi' := mem_Ico.mp hi
    obtain ⟨hnu, hnv⟩ := ladder_interior_not_joint hT.1 hL hLS hi'.1 (by omega)
    obtain ⟨P, hP, hmemP⟩ := exists_piece_through (M := M) hnu
    refine ⟨P, hP, (hmemP _).mpr ⟨hnu, hrefl _⟩, (hmemP _).mpr ⟨hnv, ?_⟩⟩
    have hc := ladder_rung_samePiece hL hLS (⟨i - 1, by omega⟩ : Fin m)
    have e : (⟨i - 1, by omega⟩ : Fin m).succ = (⟨i, by omega⟩ : Fin (m + 1)) := Fin.ext (by simp; omega)
    rw [e] at hc
    rwa [lad_of_le u (by omega), lad_of_le v (by omega)]
  have hxy : ∀ i ∈ Ico 1 m, lad u i ≠ lad v i := by
    intro i hi
    have hi' := mem_Ico.mp hi
    rw [lad_of_le u (by omega), lad_of_le v (by omega)]
    exact huv _ _
  have hdist : ∀ i ∈ Ico 1 m, ∀ j ∈ Ico 1 m, i ≠ j →
      lad u i ≠ lad u j ∧ lad u i ≠ lad v j ∧ lad v i ≠ lad u j ∧ lad v i ≠ lad v j := by
    intro i hi j hj hij
    have hi' := mem_Ico.mp hi
    have hj' := mem_Ico.mp hj
    have hne : (⟨i, by omega⟩ : Fin (m + 1)) ≠ ⟨j, by omega⟩ := fun h => hij (congrArg Fin.val h)
    rw [lad_of_le u (show i ≤ m by omega), lad_of_le v (show i ≤ m by omega),
      lad_of_le u (show j ≤ m by omega), lad_of_le v (show j ≤ m by omega)]
    exact ⟨fun h => hne (huu _ _ h), huv _ _, fun h => huv _ _ h.symm, fun h => hne (hvv _ _ h)⟩
  unfold incCnt tvineIncoherency
  rw [show m - 1 + 1 = m by omega, Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const, smul_eq_mul, mul_one,
    zero_add]
  convert card_incoherent_rungs_le (M.tvineGroups S a b) (tvine_piece_card_le hPS hT) f m (lad u) (lad v) H hxy
    hdist using 2
  ext g
  simp only [Finset.mem_filter]

end count

end WaveTurbulence.GammaLow.Famc
