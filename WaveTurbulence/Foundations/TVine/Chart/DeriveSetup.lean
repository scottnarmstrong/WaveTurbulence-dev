/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.DeriveNodePend

/-!
# Derivation of the cell decomposition, XIX: the cells of a layout

A `Setup` is a layout with its attachment data and its core. Its **nodes** are the spine pieces `sp i` (`Z (i+1)`,
`i < r`), the copy cell `cp` (only for a (P-b) attachment) and the pendant pieces `pd k` (`Y k`, `k < s`). Each node
has its regions (`Xin`, `XoM`, `XoB`) and its placed cell (`pair_exists`, `core_exists`, `copy_exists`); the pair
nodes are enumerated by `pairEq`, and `cnode`/`cellOf` translate between nodes and cells.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Chart

open Finset VineParamContract Struct

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {S : Finset V} {a b : V}

/-- The cells as nodes of the gluing tree. -/
inductive Node
  | sp (i : ℕ)
  | cp
  | pd (k : ℕ)
  deriving DecidableEq

/-- The input label offset. -/
def Node.rin : Node → ℤ
  | .pd _ => 0
  | _ => 1

/-- The exit label offset. -/
def Node.rM : Node → ℤ
  | .pd _ => 0
  | _ => 1

namespace Lay

variable {L : Lay M S a b} {att : Att}

theorem AttData.case_none (A : L.AttData att) (h : att = .none) :
    L.s = 0 ∧ ∃ i, 1 ≤ i ∧ i ≤ L.r ∧ IsCoreBC M (L.Z i) := by
  subst h; exact A.case

theorem AttData.case_pa (A : L.AttData att) {j : ℕ} (h : att = .pa j) :
    1 ≤ L.s ∧ 1 ≤ j ∧ j ≤ L.r ∧ A.x ∈ L.Z j ∧ A.x' ∈ L.Z j ∧ IsJunctionPiece M (L.Z j) := by
  subst h; exact A.case

theorem AttData.case_pb (A : L.AttData att) {j : ℕ} (h : att = .pb j) :
    1 ≤ L.s ∧ j ≤ L.r ∧ crossBonds M (L.Z j) (L.Z (j + 1)) = 1 ∧ A.x ∈ L.Z j ∧ A.x' ∈ L.Z (j + 1) := by
  subst h; exact A.case

variable (L) (hB : M.IsBlock S a b) (A : L.AttData att) (hM : M.IsMolecule) (hT : M.IsTVine S a b)
  (hA : AttachInput)
include hB A hM hT hA

/-- A spine piece other than the junction is not a single bond (budget). -/
theorem spine_no_single {i : ℕ} (hi : i < L.r) (hpa : att ≠ .pa (i + 1)) {u w : V} (huw : u ≠ w)
    (hZ : L.Z (i + 1) = {u, w}) : M.bondsBetween u w ≠ 1 := by
  intro h1
  have hu : u ∈ L.Z (i + 1) := by rw [hZ]; simp
  have hw : w ∈ L.Z (i + 1) := by rw [hZ]; simp
  obtain ⟨hua, hub⟩ := L.Z_interior (by omega) (by omega) hu
  have huS := L.Z_sub hB (by omega) hu
  have hwS := L.Z_sub hB (by omega) hw
  obtain ⟨pti⟩ := L.port_reg hB A hM hT hA (i := i) (by omega) (att.he i) (Or.inr rfl)
  obtain ⟨pto⟩ := L.port_reg hB A hM hT hA (i := i + 1) (by omega) (att.hx (i + 1)) (Or.inl rfl)
  obtain ⟨hio, hCi, hCo, hdiff⟩ := L.spine_sandwich hB A hi hpa
  have hsum := budget hio hCi hCo hdiff hu (noLoopAt hT hua hub)
  rw [deg4 hB huS hua hub] at hsum
  have hin : (innerAt (M := M) (S := S) (L.Z (i + 1)) u).card = M.bondsBetween u w := by
    rw [hZ]; exact card_innerAt_pair huw huS hwS (noLoopAt hT hua hub)
  have h1' := portAt_le_one pti hua hub
  have h2' := portAt_le_one pto hua hub
  omega

end Lay

/-- **A setup**: a layout, its attachment, its core node, and the hypotheses. -/
structure Setup (M : Molecule V D) (S : Finset V) (a b : V) where
  hM : M.IsMolecule
  hT : M.IsTVine S a b
  hA : AttachInput
  hPS : PieceShapeInput
  L : Lay M S a b
  att : Att
  A : L.AttData att
  core : Node
  hcore : (att = .none ∧ ∃ i, core = .sp i ∧ i < L.r ∧ IsCoreBC M (L.Z (i + 1))) ∨
    (att ≠ .none ∧ 1 ≤ L.s ∧ core = .pd (L.s - 1) ∧ IsCoreD M (L.Y (L.s - 1)))

theorem setup_exists (hM : M.IsMolecule) (hT : M.IsTVine S a b) (hA : AttachInput) (hPS : PieceShapeInput)
    (L : Lay M S a b) : Nonempty (Setup M S a b) := by
  obtain ⟨att, ⟨A⟩⟩ := L.att_exists hT.1
  by_cases h : att = .none
  · obtain ⟨-, i, h1, h2, hC⟩ := A.case_none h
    exact ⟨⟨hM, hT, hA, hPS, L, att, A, .sp (i - 1),
      Or.inl ⟨h, i - 1, rfl, by omega, by rwa [show i - 1 + 1 = i by omega]⟩⟩⟩
  · have hs : 1 ≤ L.s := by
      cases att with
      | none => exact absurd rfl h
      | pa j => exact (A.case_pa rfl).1
      | pb j => exact (A.case_pb rfl).1
    rcases L.pend with ⟨h0, -⟩ | ⟨-, hD, -⟩
    · omega
    · exact ⟨⟨hM, hT, hA, hPS, L, att, A, .pd (L.s - 1), Or.inr ⟨h, hs, rfl, hD⟩⟩⟩

namespace Setup

variable (G : Setup M S a b)

/-! ## Node data -/

/-- The attachment index. -/
def j : ℕ := match G.att with
  | .none => 0
  | .pa j => j
  | .pb j => j

/-- Whether there is a copy cell. -/
def isPb : Bool := match G.att with
  | .pb _ => true
  | _ => false

/-- The junction node. -/
def jnode : Option Node := match G.att with
  | .pa j => some (.sp (j - 1))
  | _ => none

/-- The nodes of the layout. -/
def Valid : Node → Prop
  | .sp i => i < G.L.r
  | .cp => G.isPb = true
  | .pd k => k < G.L.s

/-- The piece of a node. -/
def piece : Node → Finset V
  | .sp i => G.L.Z (i + 1)
  | .cp => ∅
  | .pd k => G.L.Y k

/-- The input region of a node. -/
def Xin : Node → Finset V
  | .sp i => G.L.reg i (G.att.he i)
  | .cp => G.L.reg G.j false
  | .pd k => S \ G.L.H k

/-- The exit region of a node. -/
def XoM : Node → Option (Finset V)
  | .sp i => some (G.L.reg (i + 1) (G.att.hx (i + 1)))
  | .cp => some (G.L.reg G.j true)
  | .pd k => if k + 1 < G.L.s then some (S \ G.L.H (k + 1)) else none

/-- The pendant region of a node. -/
def XoB : Node → Option (Finset V)
  | .sp i => if G.jnode = some (.sp i) then some (S \ G.L.H 0) else none
  | .cp => some (S \ G.L.H 0)
  | .pd _ => none

/-- The number of local bonds. -/
def nBof (n : Node) : ℕ :=
  if n = G.core then (if G.att = .none then 8 else 7) else if n = .cp then 3 else if G.jnode = some n then 7 else 6

/-- The internal multiplicity of a pair node. -/
def μof (n : Node) : ℕ := if G.jnode = some n then 1 else 2

/-! ## The attachment -/

theorem j_pa {i : ℕ} (h : G.att = .pa i) : G.j = i := by unfold j; rw [h]
theorem j_pb {i : ℕ} (h : G.att = .pb i) : G.j = i := by unfold j; rw [h]

theorem isPb_iff : G.isPb = true ↔ ∃ i, G.att = .pb i := by
  unfold isPb
  cases h : G.att with
  | none => simp
  | pa i => simp
  | pb i => simp

theorem att_eq_pb (h : G.isPb = true) : G.att = .pb G.j := by
  obtain ⟨i, hi⟩ := G.isPb_iff.mp h
  rw [G.j_pb hi]; exact hi

theorem jnode_eq {n : Node} : G.jnode = some n ↔ ∃ i, G.att = .pa i ∧ n = .sp (i - 1) := by
  unfold jnode
  cases h : G.att with
  | none => simp
  | pa i => simp [eq_comm]
  | pb i => simp

theorem jnode_sp (i : ℕ) : G.jnode = some (.sp i) ↔ G.att = .pa (i + 1) := by
  rw [jnode_eq]
  constructor
  · rintro ⟨i', h, hi⟩
    have := (G.A.case_pa h).2.1
    simp only [Node.sp.injEq] at hi
    rw [h]; congr 1; omega
  · intro h; exact ⟨i + 1, h, rfl⟩

theorem att_cases : G.att = .none ∨ (∃ i, G.att = .pa i) ∨ ∃ i, G.att = .pb i := by
  cases G.att with
  | none => exact Or.inl rfl
  | pa i => exact Or.inr (Or.inl ⟨i, rfl⟩)
  | pb i => exact Or.inr (Or.inr ⟨i, rfl⟩)

theorem att_ne_none_of_s (hs : 1 ≤ G.L.s) : G.att ≠ .none := fun h => by
  have := (G.A.case_none h).1; omega

theorem core_of_ne_none (h : G.att ≠ .none) : G.core = .pd (G.L.s - 1) := by
  rcases G.hcore with ⟨h', -⟩ | ⟨-, -, hc, -⟩
  · exact absurd h' h
  · exact hc

theorem core_ne_cp : G.core ≠ .cp := by
  rcases G.hcore with ⟨-, i, hc, -⟩ | ⟨-, -, hc, -⟩ <;> rw [hc] <;> simp

theorem core_valid : G.Valid G.core := by
  rcases G.hcore with ⟨-, i, hc, hi, -⟩ | ⟨-, hs, hc, -⟩ <;> rw [hc]
  · exact hi
  · show G.L.s - 1 < G.L.s; omega

theorem r_pos (h : G.att ≠ .pb G.L.r) : 1 ≤ G.L.r := by
  by_contra hr
  have hr0 : G.L.r = 0 := by omega
  rcases G.att_cases with h' | ⟨i, h'⟩ | ⟨i, h'⟩
  · obtain ⟨-, i, h1, h2, -⟩ := G.A.case_none h'; omega
  · have := G.A.case_pa h'; omega
  · have := (G.A.case_pb h').2.1
    exact h (by rw [h', hr0]; congr 1; omega)

/-! ## Pieces -/

theorem piece_sub {n : Node} (hn : G.Valid n) : G.piece n ⊆ S := by
  cases n with
  | sp i => exact G.L.Z_sub G.hT.1 (show i + 1 ≤ G.L.r + 1 by have : i < G.L.r := hn; omega)
  | cp => exact empty_subset _
  | pd k => exact G.L.Y_sub G.hT.1 hn

theorem piece_interior {n : Node} (hn : G.Valid n) {v : V} (hv : v ∈ G.piece n) : v ≠ a ∧ v ≠ b := by
  cases n with
  | sp i => exact G.L.Z_interior (by omega) (show i + 1 ≤ G.L.r by have : i < G.L.r := hn; omega) hv
  | cp => exact absurd hv (Finset.notMem_empty v)
  | pd k => exact G.L.Y_interior hn hv

theorem piece_disj {n n' : Node} (hn : G.Valid n) (hn' : G.Valid n') {v : V} (hv : v ∈ G.piece n)
    (hv' : v ∈ G.piece n') : n = n' := by
  have hB := G.hT.1
  cases n with
  | sp i =>
    have hi : i < G.L.r := hn
    cases n' with
    | sp i' =>
      have hi' : i' < G.L.r := hn'
      have := G.L.Z_unique hB (by omega) (by omega) hv hv'
      rw [show i = i' by omega]
    | cp => exact absurd hv' (Finset.notMem_empty v)
    | pd k' => exact (G.L.ZY_disj hB (by omega) hn' hv hv').elim
  | cp => exact absurd hv (Finset.notMem_empty v)
  | pd k =>
    cases n' with
    | sp i' =>
      have hi' : i' < G.L.r := hn'
      exact (G.L.ZY_disj hB (by omega) hn hv' hv).elim
    | cp => exact absurd hv' (Finset.notMem_empty v)
    | pd k' => rw [G.L.Y_unique hB hn hn' hv hv']

theorem piece_mem {n : Node} (hn : G.Valid n) (hcp : n ≠ .cp) : G.piece n ∈ M.pieces S a b := by
  cases n with
  | sp i => exact G.L.Z_piece (i + 1) (by omega) (show i + 1 ≤ G.L.r by have : i < G.L.r := hn; omega)
  | cp => exact absurd rfl hcp
  | pd k => exact G.L.Y_piece k hn

theorem piece_nonempty {n : Node} (hn : G.Valid n) (hcp : n ≠ .cp) : (G.piece n).Nonempty := by
  classical
  obtain ⟨u, hu, hP⟩ := mem_pieces.mp (G.piece_mem hn hcp)
  rw [hP]
  exact ⟨u, mem_filter.mpr ⟨hu, samePiece_refl u⟩⟩

theorem piece_inj {n n' : Node} (hn : G.Valid n) (hn' : G.Valid n') (hcp : n ≠ .cp)
    (h : G.piece n = G.piece n') : n = n' := by
  obtain ⟨v, hv⟩ := G.piece_nonempty hn hcp
  exact G.piece_disj hn hn' hv (h ▸ hv)

theorem core_card : (G.piece G.core).card = 3 := by
  rcases G.hcore with ⟨-, i, hc, -, x, y, z, hxy, hyz, hxz, hZ, -⟩ | ⟨-, -, hc, x, y, z, hxy, hyz, hxz, hY, -⟩ <;>
    rw [hc]
  · show (G.L.Z (i + 1)).card = 3
    rw [hZ]; exact Finset.card_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩
  · show (G.L.Y (G.L.s - 1)).card = 3
    rw [hY]; exact Finset.card_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩

/-- **Every non-core piece has two atoms** (N2 Prop 1.17(b)). -/
theorem twoAtom {n : Node} (hn : G.Valid n) (hc : n ≠ G.core) (hcp : n ≠ .cp) : TwoAtomPiece M (G.piece n) := by
  obtain ⟨core', hcore', -, htwo, -⟩ := G.hPS M S a b G.hT
  apply htwo _ (G.piece_mem hn hcp)
  intro h
  have hcc : G.piece G.core ≠ core' := by
    intro h'
    exact hc (G.piece_inj hn G.core_valid hcp (h.trans h'.symm))
  obtain ⟨u, w, huw, hP, -⟩ := htwo _ (G.piece_mem G.core_valid G.core_ne_cp) hcc
  have := G.core_card
  rw [hP, card_pair huw] at this
  omega

theorem rung_pend {k : ℕ} (hk : k + 1 < G.L.s) : IsRungPiece M (G.L.Y k) := by
  rcases G.L.pend with ⟨h0, -⟩ | ⟨-, -, hR, -⟩
  · omega
  · exact hR k hk

/-! ## The enumeration of the cells -/

/-- The pair nodes. -/
def pairsF : Finset Node :=
  (((Finset.range G.L.r).image Node.sp) ∪ ((Finset.range G.L.s).image Node.pd)).filter (· ≠ G.core)

theorem mem_pairsF {n : Node} : n ∈ G.pairsF ↔ G.Valid n ∧ n ≠ G.core ∧ n ≠ .cp := by
  unfold pairsF
  cases n <;> simp [Valid] <;> tauto

/-- The number of pair cells. -/
def m : ℕ := G.pairsF.card

/-- The number of copy cells. -/
def kk : ℕ := if G.isPb then 1 else 0

/-- The enumeration of the pair nodes. -/
noncomputable def pairEq : {n // n ∈ G.pairsF} ≃ Fin G.m := G.pairsF.equivFin

/-- The node of a cell. -/
noncomputable def cnode : Cell G.m G.kk → Node
  | .inl j => (G.pairEq.symm j).1
  | .inr (.inl _) => G.core
  | .inr (.inr _) => .cp

/-- The cell of a node. -/
noncomputable def cellOf (n : Node) : Cell G.m G.kk :=
  if n = G.core then Cell.core
  else if h : n ∈ G.pairsF then .inl (G.pairEq ⟨n, h⟩)
  else if hk : 0 < G.kk then .inr (.inr ⟨0, hk⟩) else Cell.core

theorem cnode_mem (j : Fin G.m) : G.cnode (.inl j) ∈ G.pairsF := (G.pairEq.symm j).2

theorem isPb_of_copy (ι : Fin G.kk) : G.isPb = true := by
  have h := ι.2
  unfold kk at h
  by_contra h'
  simp [h'] at h

theorem valid_cnode (c : Cell G.m G.kk) : G.Valid (G.cnode c) := by
  rcases c with j | (u | ι)
  · exact (G.mem_pairsF.mp (G.cnode_mem j)).1
  · exact G.core_valid
  · exact G.isPb_of_copy ι

theorem cellOf_cnode (c : Cell G.m G.kk) : G.cellOf (G.cnode c) = c := by
  rcases c with j | (u | ι)
  · have hm := G.cnode_mem j
    obtain ⟨-, hc, -⟩ := G.mem_pairsF.mp hm
    unfold cellOf
    rw [if_neg hc, dif_pos hm]
    congr 1
    have : (⟨G.cnode (.inl j), hm⟩ : {n // n ∈ G.pairsF}) = G.pairEq.symm j := Subtype.ext rfl
    rw [this, Equiv.apply_symm_apply]
  · show G.cellOf G.core = _
    unfold cellOf
    rw [if_pos rfl]
  · have hcp : G.cnode (.inr (.inr ι)) = .cp := rfl
    rw [hcp]
    unfold cellOf
    have hk : 0 < G.kk := lt_of_le_of_lt (Nat.zero_le _) ι.2
    rw [if_neg (Ne.symm G.core_ne_cp), dif_neg (fun h => (G.mem_pairsF.mp h).2.2 rfl), dif_pos hk]
    have : G.kk = 1 := by unfold kk; rw [G.isPb_of_copy ι]; rfl
    congr 2
    apply Fin.ext
    have := ι.2
    show 0 = ι.val
    omega

theorem cnode_cellOf {n : Node} (hn : G.Valid n) : G.cnode (G.cellOf n) = n := by
  unfold cellOf
  by_cases hc : n = G.core
  · rw [if_pos hc]; exact hc.symm
  rw [if_neg hc]
  by_cases hm : n ∈ G.pairsF
  · rw [dif_pos hm]
    show (G.pairEq.symm (G.pairEq ⟨n, hm⟩)).1 = n
    rw [Equiv.symm_apply_apply]
  · rw [dif_neg hm]
    have hcp : n = .cp := by
      by_contra h
      exact hm (G.mem_pairsF.mpr ⟨hn, hc, h⟩)
    subst hcp
    have hk : 0 < G.kk := by unfold kk; rw [show G.isPb = true from hn]; decide
    rw [dif_pos hk]
    rfl

/-! ## The placed cells -/

theorem pair_exists {n : Node} (hn : n ∈ G.pairsF) :
    Nonempty (PCell M S a b 2 2 (fun _ c => PairOK c ∧ c.mu = G.μof n) (G.piece n) (G.Xin n) (G.XoM n)
      (G.XoB n) (Node.rin n) (Node.rM n) (G.nBof n)) := by
  have hB := G.hT.1
  obtain ⟨hv, hc, hcp⟩ := G.mem_pairsF.mp hn
  cases n with
  | sp i =>
    have hi : i < G.L.r := hv
    by_cases hj : G.jnode = some (.sp i)
    · have hpa := (G.jnode_sp i).mp hj
      have hμ : G.μof (.sp i) = 1 := by simp [μof, hj]
      have hXB : G.XoB (.sp i) = some (S \ G.L.H 0) := by simp [XoB, hj]
      have hnB : G.nBof (.sp i) = 7 := by simp [nBof, hc, hj]
      rw [hμ, hXB, hnB]
      exact G.L.pc_spineJunction hB G.A G.hM G.hT G.hA hi hpa
    · have hpa : G.att ≠ .pa (i + 1) := fun h => hj ((G.jnode_sp i).mpr h)
      have hμ : G.μof (.sp i) = 2 := by simp [μof, hj]
      have hXB : G.XoB (.sp i) = none := by simp [XoB, hj]
      have hnB : G.nBof (.sp i) = 6 := by simp [nBof, hc, hj]
      rw [hμ, hXB, hnB]
      obtain ⟨u, w, huw, hZ, h12⟩ := G.twoAtom hv hc hcp
      rcases h12 with h1 | h2
      · exact absurd h1 (G.L.spine_no_single hB G.A G.hM G.hT G.hA hi hpa huw hZ)
      · exact G.L.pc_spineRung hB G.A G.hM G.hT G.hA hi huw hZ h2
  | cp => exact absurd rfl hcp
  | pd k =>
    have hk : k < G.L.s := hv
    have hcore := G.core_of_ne_none (G.att_ne_none_of_s (by omega))
    have hk1 : k + 1 < G.L.s := by
      by_contra h
      exact hc (by rw [hcore]; congr 1; omega)
    have hjn : G.jnode ≠ some (.pd k) := fun h => by
      obtain ⟨i, -, h'⟩ := G.jnode_eq.mp h; cases h'
    have hμ : G.μof (.pd k) = 2 := by simp [μof, hjn]
    have hXM : G.XoM (.pd k) = some (S \ G.L.H (k + 1)) := by simp [XoM, hk1]
    have hnB : G.nBof (.pd k) = 6 := by simp [nBof, hc, hjn]
    rw [hμ, hXM, hnB]
    exact G.L.pc_pendRung hB G.hM G.hT G.hA hk1 (G.rung_pend hk1)

theorem core_exists :
    Nonempty (PCell M S a b 3 3 (fun _ c => CoreOK c) (G.piece G.core) (G.Xin G.core) (G.XoM G.core)
      (G.XoB G.core) (Node.rin G.core) (Node.rM G.core) (G.nBof G.core)) := by
  have hB := G.hT.1
  have hnB : G.nBof G.core = if G.att = .none then 8 else 7 := by simp [nBof]
  rw [hnB]
  rcases G.hcore with ⟨hnone, i, hci, hi, hC⟩ | ⟨hnn, hs, hcd, hD⟩
  · have hjn : G.jnode = none := by unfold jnode; rw [hnone]
    have hXB : G.XoB (.sp i) = none := by simp [XoB, hjn]
    rw [if_pos hnone, hci, hXB]
    exact G.L.pc_spineCore hB G.A G.hM G.hT G.hA hi hnone hC
  · have hXM : G.XoM (.pd (G.L.s - 1)) = none := by
      simp only [XoM]; rw [if_neg (by omega)]
    have hXB : G.XoB (.pd (G.L.s - 1)) = none := rfl
    rw [if_neg hnn, hcd, hXM, hXB]
    exact G.L.pc_pendCore hB G.hM G.hT G.hA hs hD

theorem copy_exists (h : G.isPb = true) :
    Nonempty (PCell M S a b 0 0 (fun _ _ => True) (G.piece .cp) (G.Xin .cp) (G.XoM .cp) (G.XoB .cp)
      (Node.rin .cp) (Node.rM .cp) (G.nBof .cp)) := by
  have hnB : G.nBof .cp = 3 := by simp [nBof, Ne.symm G.core_ne_cp]
  rw [hnB]
  exact G.L.pc_copy G.hT.1 G.hM G.hT G.hA G.A (G.att_eq_pb h)

/-- The cell conditions. -/
def Qof : (c : Cell G.m G.kk) → (nB : ℕ) → LocalChart (nAof c) (nCof c) nB → Prop
  | .inl j => fun _ ch => PairOK ch ∧ ch.mu = G.μof (G.cnode (.inl j))
  | .inr (.inl _) => fun _ ch => CoreOK ch
  | .inr (.inr _) => fun _ _ => True

/-- **The placed cell of a cell.** -/
noncomputable def cellPC : (c : Cell G.m G.kk) → PCell M S a b (nAof c) (nCof c) (G.Qof c) (G.piece (G.cnode c))
    (G.Xin (G.cnode c)) (G.XoM (G.cnode c)) (G.XoB (G.cnode c)) (Node.rin (G.cnode c)) (Node.rM (G.cnode c))
    (G.nBof (G.cnode c))
  | .inl j => Classical.choice (G.pair_exists (G.cnode_mem j))
  | .inr (.inl _) => Classical.choice G.core_exists
  | .inr (.inr ι) => Classical.choice (G.copy_exists (G.isPb_of_copy ι))

end Setup

end WaveTurbulence.TVine.Chart
