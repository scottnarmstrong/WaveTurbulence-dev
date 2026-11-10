/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.DeriveSetup
public import WaveTurbulence.Foundations.TVine.Chart.Main

/-!
# Derivation of the cell decomposition, XX: the assembly (M4 Theorem C from the piece structure)

The gluing tree of a setup: the spine cells in order from `b` to `a` (with the copy cell between `Z j` and `Z (j+1)`
for a (P-b) attachment at `j`), and the pendant chain hanging from the junction (P-a) or the copy cell (P-b). Each
cell's input region is its parent's output region (`npar_spec`), so the input pair of a cell is its parent's output
pair (uniqueness of the bonds of a 2-cut). The bond count `Σ (nB − 2) + 2 = 2|S| − 2` gives the ownership
(`PreDecomp.toDecomp`).

**`decompExists_of_inputs`**: the named inputs (N2 Prop 1.17(b), N3 Thm 6, M4 Lemma A; L3's exact statements) give
`DecompExists`, hence M4 Theorem C (`tvineChart_of_inputs`) and the `𝒱_γ` chart contract.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Chart

open Finset VineParamContract Struct

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {S : Finset V} {a b : V}

namespace Setup

variable (G : Setup M S a b)

/-! ## The gluing tree -/

/-- The parent of a node and the output pair (`false` exit, `true` pendant) it hangs from. -/
def npar : Node → Option (Node × Bool)
  | .sp i => if G.att = .pb i then some (.cp, false) else if i = 0 then none else some (.sp (i - 1), false)
  | .cp => if G.j = 0 then none else some (.sp (G.j - 1), false)
  | .pd k => if k = 0 then (if G.isPb then some (.cp, true) else some (.sp (G.j - 1), true))
      else some (.pd (k - 1), false)

/-- The rank of a node. -/
def nrank : Node → ℕ
  | .sp i => 2 * i + 2
  | .cp => 2 * G.j + 1
  | .pd k => 2 * G.L.r + 3 + k

theorem npar_spec {n n' : Node} {w : Bool} (hn : G.Valid n) (h : G.npar n = some (n', w)) :
    G.Valid n' ∧ G.nrank n' < G.nrank n ∧ (if w then G.XoB n' else G.XoM n') = some (G.Xin n) ∧
      n.rin = (if w then 0 else n'.rM) := by
  cases n with
  | sp i =>
    have hi : i < G.L.r := hn
    simp only [npar] at h
    by_cases h1 : G.att = .pb i
    · rw [if_pos h1] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨G.isPb_iff.mpr ⟨i, h1⟩, ?_, ?_, rfl⟩
      · show 2 * G.j + 1 < 2 * i + 2
        rw [G.j_pb h1]; omega
      · show some (G.L.reg G.j true) = some (G.L.reg i (G.att.he i))
        rw [G.j_pb h1, h1]; simp [Att.he]
    · rw [if_neg h1] at h
      by_cases h2 : i = 0
      · rw [if_pos h2] at h; simp at h
      · rw [if_neg h2] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨show i - 1 < G.L.r by omega, show 2 * (i - 1) + 2 < 2 * i + 2 by omega, ?_, rfl⟩
        show some (G.L.reg (i - 1 + 1) (G.att.hx (i - 1 + 1))) = some (G.L.reg i (G.att.he i))
        rw [show i - 1 + 1 = i by omega, Att.flag_eq h1]
  | cp =>
    have hpb := G.att_eq_pb hn
    have hjr := (G.A.case_pb hpb).2.1
    simp only [npar] at h
    by_cases h2 : G.j = 0
    · rw [if_pos h2] at h; simp at h
    · rw [if_neg h2] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨show G.j - 1 < G.L.r by omega, show 2 * (G.j - 1) + 2 < 2 * G.j + 1 by omega, ?_, rfl⟩
      show some (G.L.reg (G.j - 1 + 1) (G.att.hx (G.j - 1 + 1))) = some (G.L.reg G.j false)
      rw [show G.j - 1 + 1 = G.j by omega, hpb]; simp [Att.hx]
  | pd k =>
    have hk : k < G.L.s := hn
    simp only [npar] at h
    by_cases h0 : k = 0
    · subst h0
      rw [if_pos rfl] at h
      by_cases hp : G.isPb = true
      · rw [if_pos hp] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hjr := (G.A.case_pb (G.att_eq_pb hp)).2.1
        exact ⟨hp, show 2 * G.j + 1 < 2 * G.L.r + 3 + 0 by omega, rfl, rfl⟩
      · rw [if_neg hp] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hpa : G.att = .pa G.j := by
          rcases G.att_cases with h' | ⟨i, h'⟩ | ⟨i, h'⟩
          · exact absurd h' (G.att_ne_none_of_s (by omega))
          · rw [G.j_pa h']; exact h'
          · exact absurd (G.isPb_iff.mpr ⟨i, h'⟩) hp
        obtain ⟨-, hj1, hjr, -⟩ := G.A.case_pa hpa
        refine ⟨show G.j - 1 < G.L.r by omega, show 2 * (G.j - 1) + 2 < 2 * G.L.r + 3 + 0 by omega, ?_, rfl⟩
        show (if G.jnode = some (.sp (G.j - 1)) then some (S \ G.L.H 0) else none) = some (S \ G.L.H 0)
        rw [if_pos (G.jnode_eq.mpr ⟨G.j, hpa, rfl⟩)]
    · rw [if_neg h0] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨show k - 1 < G.L.s by omega, show 2 * G.L.r + 3 + (k - 1) < 2 * G.L.r + 3 + k by omega, ?_, rfl⟩
      show (if k - 1 + 1 < G.L.s then some (S \ G.L.H (k - 1 + 1)) else none) = some (S \ G.L.H k)
      rw [if_pos (by omega), show k - 1 + 1 = k by omega]

theorem npar_none {n : Node} (hn : G.Valid n) (h : G.npar n = none) :
    G.Xin n = G.L.reg 0 (G.att.hx 0) ∧ n.rin = 1 := by
  cases n with
  | sp i =>
    simp only [npar] at h
    by_cases h1 : G.att = .pb i
    · rw [if_pos h1] at h; simp at h
    · rw [if_neg h1] at h
      by_cases h2 : i = 0
      · subst h2
        refine ⟨?_, rfl⟩
        show G.L.reg 0 (G.att.he 0) = _
        rw [Att.flag_eq h1]
      · rw [if_neg h2] at h; simp at h
  | cp =>
    have hpb := G.att_eq_pb hn
    simp only [npar] at h
    by_cases h2 : G.j = 0
    · refine ⟨?_, rfl⟩
      show G.L.reg G.j false = _
      rw [hpb, h2]; simp [Att.hx]
    · rw [if_neg h2] at h; simp at h
  | pd k =>
    simp only [npar] at h
    split_ifs at h <;> simp at h

/-- The final cell's node. -/
def fnode : Node := if G.att = .pb G.L.r then .cp else .sp (G.L.r - 1)

theorem fnode_spec : G.Valid G.fnode ∧ G.XoM G.fnode = some (G.L.reg G.L.r (G.att.he G.L.r)) ∧ G.fnode.rM = 1 := by
  unfold fnode
  by_cases h : G.att = .pb G.L.r
  · rw [if_pos h]
    refine ⟨G.isPb_iff.mpr ⟨_, h⟩, ?_, rfl⟩
    show some (G.L.reg G.j true) = _
    rw [G.j_pb h, h]; simp [Att.he]
  · rw [if_neg h]
    have hr := G.r_pos h
    refine ⟨show G.L.r - 1 < G.L.r by omega, ?_, rfl⟩
    show some (G.L.reg (G.L.r - 1 + 1) (G.att.hx (G.L.r - 1 + 1))) = _
    rw [show G.L.r - 1 + 1 = G.L.r by omega, Att.flag_eq h]

/-! ## The joints -/

/-- The bonds at `b`. -/
noncomputable def pb0 : Port2 M S (G.L.reg 0 (G.att.hx 0)) a b :=
  Classical.choice (G.L.port_reg G.hT.1 G.A G.hM G.hT G.hA (i := 0) (Nat.zero_le _) _ (Or.inl rfl))

/-- The bonds at `a`. -/
noncomputable def pa0 : Port2 M S (G.L.reg G.L.r (G.att.he G.L.r)) a b :=
  Classical.choice (G.L.port_reg G.hT.1 G.A G.hM G.hT G.hA (i := G.L.r) le_rfl _ (Or.inr rfl))

theorem pb0_ends : tl G.pb0.out = b ∧ hd G.pb0.out ≠ b ∧ hd G.pb0.inn = b ∧ tl G.pb0.inn ≠ b := by
  have hB := G.hT.1
  have hbZ : b ∈ G.L.Z 0 := by rw [G.L.Z_zero]; exact mem_singleton_self b
  have hb : b ∈ G.L.reg 0 (G.att.hx 0) := (G.L.mem_reg_Z hB (by omega) (by omega) hbZ).mpr le_rfl
  obtain ⟨h1, h2⟩ := G.L.exit_ends hB G.A (Nat.zero_le _) G.pb0
  rw [G.L.Z_zero, mem_singleton] at h1 h2
  exact ⟨h1, fun h => G.pb0.out_hd (by rw [h]; exact hb), h2, fun h => G.pb0.inn_tl (by rw [h]; exact hb)⟩

theorem pa0_ends : hd G.pa0.out = a ∧ tl G.pa0.out ≠ a ∧ tl G.pa0.inn = a ∧ hd G.pa0.inn ≠ a := by
  have hB := G.hT.1
  have haZ : a ∈ G.L.Z (G.L.r + 1) := by rw [G.L.Z_last]; exact mem_singleton_self a
  have ha : a ∉ G.L.reg G.L.r (G.att.he G.L.r) := G.L.Z_not_reg hB (by omega) haZ _
  obtain ⟨h1, h2⟩ := G.L.entry_ends hB G.A le_rfl G.pa0
  rw [G.L.Z_last, mem_singleton] at h1 h2
  refine ⟨h1, fun h => ha ?_, h2, fun h => ha ?_⟩
  · have := G.pa0.out_tl; rwa [h] at this
  · have := G.pa0.inn_hd; rwa [h] at this

/-- The joint `b`. -/
noncomputable def jb : LocEmb jointGraph M S :=
  jointEmb b G.pb0.out G.pb0.inn G.pb0_ends.1 G.pb0_ends.2.1 G.pb0_ends.2.2.1 G.pb0_ends.2.2.2 (deg_b G.hT.1).le

/-- The joint `a`. -/
noncomputable def ja : LocEmb jointGraph M S :=
  jointEmb a G.pa0.inn G.pa0.out G.pa0_ends.2.2.1 G.pa0_ends.2.2.2 G.pa0_ends.1 G.pa0_ends.2.1 (deg_a G.hT.1).le

/-! ## The fields of the pre-decomposition -/

/-- The parent cell. -/
noncomputable def cpar (c : Cell G.m G.kk) : Option (Cell G.m G.kk × Bool) :=
  (G.npar (G.cnode c)).map fun p => (G.cellOf p.1, p.2)

theorem cpar_some {c s : Cell G.m G.kk} {w : Bool} (h : G.cpar c = some (s, w)) :
    ∃ n', G.npar (G.cnode c) = some (n', w) ∧ s = G.cellOf n' := by
  unfold cpar at h
  rcases hp : G.npar (G.cnode c) with _ | ⟨n', w'⟩
  · rw [hp] at h; simp at h
  · rw [hp] at h
    have h' : (G.cellOf n', w') = (s, w) := Option.some.inj h
    rw [Prod.mk.injEq] at h'
    obtain ⟨h1, rfl⟩ := h'
    exact ⟨n', rfl, h1.symm⟩

theorem cpar_none {c : Cell G.m G.kk} (h : G.cpar c = none) : G.npar (G.cnode c) = none := by
  unfold cpar at h
  rcases hp : G.npar (G.cnode c) with _ | p
  · rfl
  · rw [hp] at h; simp at h

theorem parent_rank' (c s : Cell G.m G.kk) (w : Bool) (h : G.cpar c = some (s, w)) :
    G.nrank (G.cnode s) < G.nrank (G.cnode c) := by
  obtain ⟨n', hp, rfl⟩ := G.cpar_some h
  have hs := G.npar_spec (G.valid_cnode c) hp
  rw [G.cnode_cellOf hs.1]; exact hs.2.1

theorem wire_base' (c : Cell G.m G.kk) (h : G.cpar c = none) :
    (G.cellPC c).emb.bond (G.cellPC c).cfg.eO = G.jb.bond 0 ∧
      (G.cellPC c).emb.bond (G.cellPC c).cfg.eI = G.jb.bond 1 ∧ (G.cellPC c).cfg.locR (G.cellPC c).cfg.eO = 1 := by
  obtain ⟨hX, hr⟩ := G.npar_none (G.valid_cnode c) (G.cpar_none h)
  refine ⟨?_, ?_, ?_⟩
  · rw [(G.cellPC c).bO]; exact port2_out_eq' hX _ G.pb0
  · rw [(G.cellPC c).bI]; exact port2_inn_eq' hX _ G.pb0
  · rw [(G.cellPC c).rel.1]; exact hr

theorem wire' (c s : Cell G.m G.kk) (w : Bool) (h : G.cpar c = some (s, w)) :
    ∃ p, outPair (G.cellPC s).cfg w = some p ∧
      (G.cellPC c).emb.bond (G.cellPC c).cfg.eO = (G.cellPC s).emb.bond p.1 ∧
      (G.cellPC c).emb.bond (G.cellPC c).cfg.eI = (G.cellPC s).emb.bond p.2 ∧
      (G.cellPC c).cfg.locR (G.cellPC c).cfg.eO = (G.cellPC s).cfg.locR p.1 - (G.cellPC s).cfg.locR p.2 := by
  obtain ⟨n', hp, rfl⟩ := G.cpar_some h
  obtain ⟨hv', -, hX, hr⟩ := G.npar_spec (G.valid_cnode c) hp
  have hc' := G.cnode_cellOf hv'
  apply PCell.wire (G.cellPC c) (G.cellPC (G.cellOf n')) w
  · rw [hc']; exact hX
  · rw [hc']; exact hr

theorem final_out' : ∃ p, (G.cellPC (G.cellOf G.fnode)).cfg.outM = some p ∧
    G.ja.bond 0 = (G.cellPC (G.cellOf G.fnode)).emb.bond p.2 ∧
    G.ja.bond 1 = (G.cellPC (G.cellOf G.fnode)).emb.bond p.1 ∧
    (G.cellPC (G.cellOf G.fnode)).cfg.locR p.1 - (G.cellPC (G.cellOf G.fnode)).cfg.locR p.2 = 1 := by
  obtain ⟨hv, hX, hr⟩ := G.fnode_spec
  have hc := G.cnode_cellOf hv
  obtain ⟨p, hp, h1, h2⟩ := (G.cellPC (G.cellOf G.fnode)).oM _ (by rw [hc]; exact hX) G.pa0
  refine ⟨p, hp, h2.symm, h1.symm, ?_⟩
  rw [(G.cellPC (G.cellOf G.fnode)).rel.2.1 p (by rw [hp]; rfl), hc]
  exact hr

theorem atom_piece (c : Cell G.m G.kk) (u : Fin (nAof c)) : (G.cellPC c).emb.atom u ∈ G.piece (G.cnode c) :=
  ((G.cellPC c).atoms _).mpr ⟨u, rfl⟩

theorem cover' (v : V) (hv : v ∈ S) : v = a ∨ v = b ∨ ∃ c u, (G.cellPC c).emb.atom u = v := by
  have hB := G.hT.1
  have hcell : ∀ n, G.Valid n → v ∈ G.piece n → ∃ c u, (G.cellPC c).emb.atom u = v := by
    intro n hn hvn
    obtain ⟨u, hu⟩ := ((G.cellPC (G.cellOf n)).atoms v).mp (by rw [G.cnode_cellOf hn]; exact hvn)
    exact ⟨_, u, hu⟩
  rcases G.L.atom_cases hB hv with ⟨i, hi, hvi⟩ | ⟨k, hk, hvk⟩
  · rcases Nat.eq_zero_or_pos i with rfl | h0
    · rw [G.L.Z_zero, mem_singleton] at hvi; exact Or.inr (Or.inl hvi)
    · rcases Nat.lt_or_ge i (G.L.r + 1) with h1 | h1
      · right; right
        exact hcell (.sp (i - 1)) (show i - 1 < G.L.r by omega)
          (show v ∈ G.L.Z (i - 1 + 1) by rwa [show i - 1 + 1 = i by omega])
      · have : i = G.L.r + 1 := by omega
        subst this; rw [G.L.Z_last, mem_singleton] at hvi; exact Or.inl hvi
  · right; right; exact hcell (.pd k) hk hvk

theorem atom_inj' (c c' : Cell G.m G.kk) (u : Fin (nAof c)) (u' : Fin (nAof c'))
    (h : (G.cellPC c).emb.atom u = (G.cellPC c').emb.atom u') :
    (⟨c, u⟩ : Σ c : Cell G.m G.kk, Fin (nAof c)) = ⟨c', u'⟩ := by
  have hv := G.atom_piece c u
  have hv' := G.atom_piece c' u'
  rw [← h] at hv'
  have hn := G.piece_disj (G.valid_cnode c) (G.valid_cnode c') hv hv'
  have hcc : c = c' := by rw [← G.cellOf_cnode c, ← G.cellOf_cnode c', hn]
  subst hcc
  rw [(G.cellPC c).emb.atom_inj h]

/-- The junction cell. -/
noncomputable def junc : Option (Fin G.m) :=
  match G.jnode with
  | some n => if h : n ∈ G.pairsF then some (G.pairEq ⟨n, h⟩) else none
  | none => none

theorem junc_iff (j : Fin G.m) : G.junc = some j ↔ G.jnode = some (G.cnode (.inl j)) := by
  unfold junc
  rcases hj : G.jnode with _ | n
  · simp
  · constructor
    · intro h
      by_cases hm : n ∈ G.pairsF
      · simp only [dif_pos hm, Option.some.injEq] at h
        congr 1
        show n = (G.pairEq.symm j).1
        rw [← h, Equiv.symm_apply_apply]
      · simp [dif_neg hm] at h
    · intro h
      obtain rfl := Option.some.inj h
      simp only [dif_pos (G.cnode_mem j), Option.some.injEq]
      have : (⟨G.cnode (.inl j), G.cnode_mem j⟩ : {n // n ∈ G.pairsF}) = G.pairEq.symm j := Subtype.ext rfl
      rw [this, Equiv.apply_symm_apply]

theorem junction_mu' (j : Fin G.m) : (G.cellPC (.inl j)).cfg.mu = if G.junc = some j then 1 else 2 := by
  have hq : PairOK (G.cellPC (.inl j)).cfg ∧ (G.cellPC (.inl j)).cfg.mu = G.μof (G.cnode (.inl j)) :=
    (G.cellPC (.inl j)).ok
  rw [hq.2]
  unfold μof
  exact if_congr (G.junc_iff j).symm rfl rfl

/-! ## The bond count -/

theorem card_S : S.card = 2 * G.m + 5 := by
  classical
  have hB := G.hT.1
  let f : (Σ c : Cell G.m G.kk, Fin (nAof c)) → V := fun x => (G.cellPC x.1).emb.atom x.2
  have hf : Function.Injective f := fun x y h => by
    obtain ⟨c, u⟩ := x; obtain ⟨c', u'⟩ := y
    exact G.atom_inj' c c' u u' h
  have himg : (univ : Finset (Σ c : Cell G.m G.kk, Fin (nAof c))).image f = (S.erase a).erase b := by
    ext v
    simp only [mem_image, mem_univ, true_and, mem_erase]
    constructor
    · rintro ⟨⟨c, u⟩, rfl⟩
      have hp := G.piece_interior (G.valid_cnode c) (G.atom_piece c u)
      exact ⟨hp.2, hp.1, G.piece_sub (G.valid_cnode c) (G.atom_piece c u)⟩
    · rintro ⟨hvb, hva, hv⟩
      rcases G.cover' v hv with h | h | ⟨c, u, h⟩
      · exact absurd h hva
      · exact absurd h hvb
      · exact ⟨⟨c, u⟩, h⟩
  have hcard := card_image_of_injective (univ : Finset (Σ c : Cell G.m G.kk, Fin (nAof c))) hf
  rw [himg, card_univ, Fintype.card_sigma] at hcard
  have hsum : ∑ c : Cell G.m G.kk, Fintype.card (Fin (nAof c)) = 2 * G.m + 3 := by
    simp only [Fintype.card_fin]
    simp only [Fintype.sum_sum_type, nAof, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      Fintype.card_unit]
    omega
  have hb : b ∈ S.erase a := mem_erase.mpr ⟨hB.2.2.2.1.symm, hB.2.2.1⟩
  rw [card_erase_of_mem hb, card_erase_of_mem hB.2.1, hsum] at hcard
  omega

theorem sum_nB : (∑ c : Cell G.m G.kk, (G.nBof (G.cnode c) - 2)) = 4 * G.m + 6 := by
  have hpair : ∀ j : Fin G.m, G.nBof (G.cnode (.inl j)) - 2 = 4 + (if G.junc = some j then 1 else 0) := by
    intro j
    obtain ⟨-, hc, hcp⟩ := G.mem_pairsF.mp (G.cnode_mem j)
    have : G.nBof (G.cnode (.inl j)) = if G.jnode = some (G.cnode (.inl j)) then 7 else 6 := by
      unfold nBof; rw [if_neg hc, if_neg hcp]
    rw [this]
    by_cases h : G.junc = some j
    · rw [if_pos ((G.junc_iff j).mp h), if_pos h]
    · rw [if_neg (fun h' => h ((G.junc_iff j).mpr h')), if_neg h]
  have hcore : G.nBof G.core - 2 = if G.att = .none then 6 else 5 := by
    unfold nBof; rw [if_pos rfl]; split_ifs <;> rfl
  have hcopy : G.nBof .cp - 2 = 1 := by
    unfold nBof; rw [if_neg (Ne.symm G.core_ne_cp), if_pos rfl]
  have hJ : (∑ j : Fin G.m, (4 + if G.junc = some j then 1 else 0)) =
      4 * G.m + (if G.junc.isSome then 1 else 0) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]
    congr 1
    rcases G.junc with _ | j₀
    · simp
    · simp
  have hu : (∑ u : Unit, (G.nBof (G.cnode (.inr (.inl u))) - 2)) = G.nBof G.core - 2 := by
    rw [Fintype.sum_unique]; rfl
  have hι : (∑ ι : Fin G.kk, (G.nBof (G.cnode (.inr (.inr ι))) - 2)) = G.kk := by
    have h1 : ∀ ι : Fin G.kk, G.nBof (G.cnode (.inr (.inr ι))) - 2 = 1 := fun ι => hcopy
    simp only [h1]
    simp
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Finset.sum_congr rfl (fun j _ => hpair j), hJ, hu, hι, hcore]
  rcases G.att_cases with h | ⟨i, h⟩ | ⟨i, h⟩
  · have hjc : G.junc = none := by simp [junc, jnode, h]
    have hk : G.kk = 0 := by simp [kk, isPb, h]
    rw [hjc, hk, if_pos h]; rfl
  · have hjn : G.jnode = some (.sp (i - 1)) := by simp [jnode, h]
    obtain ⟨-, hi1, hir, -⟩ := G.A.case_pa h
    have hcore' := G.core_of_ne_none (by rw [h]; simp)
    have hmem : Node.sp (i - 1) ∈ G.pairsF :=
      G.mem_pairsF.mpr ⟨show i - 1 < G.L.r by omega, by rw [hcore']; simp, by simp⟩
    have hjc : G.junc = some (G.pairEq ⟨_, hmem⟩) := by simp only [junc, hjn, dif_pos hmem]
    have hk : G.kk = 0 := by simp [kk, isPb, h]
    rw [hjc, hk]
    simp [h]
  · have hjc : G.junc = none := by simp [junc, jnode, h]
    have hk : G.kk = 1 := by simp [kk, isPb, h]
    rw [hjc, hk]
    simp [h]

theorem count' : (∑ c : Cell G.m G.kk, (G.nBof (G.cnode c) - 2)) + 2 = Fintype.card (Bond M S) := by
  have h1 := G.sum_nB
  have h2 := G.card_S
  have h3 := bond_count_block G.hT.1
  rw [Fintype.card_coe]
  omega

/-! ## The decomposition -/

/-- **The pre-decomposition of a setup.** -/
noncomputable def toPre : PreDecomp M S a b where
  m := G.m
  k := G.kk
  nB := fun c => G.nBof (G.cnode c)
  cfg := fun c => (G.cellPC c).cfg
  valid := fun c => (G.cellPC c).valid
  pairOK := fun j => (G.cellPC (.inl j)).ok.1
  coreOK := (G.cellPC Cell.core).ok
  emb := fun c => (G.cellPC c).emb
  jb := G.jb
  ja := G.ja
  jb_atom := rfl
  ja_atom := rfl
  rank := fun c => G.nrank (G.cnode c)
  parent := G.cpar
  parent_rank := G.parent_rank'
  wire_base := G.wire_base'
  wire := G.wire'
  final := G.cellOf G.fnode
  final_out := G.final_out'
  atom_mem := fun c u => G.piece_sub (G.valid_cnode c) (G.atom_piece c u)
  cover := G.cover'
  atom_inj := G.atom_inj'
  atom_ne_a := fun c u => (G.piece_interior (G.valid_cnode c) (G.atom_piece c u)).1
  atom_ne_b := fun c u => (G.piece_interior (G.valid_cnode c) (G.atom_piece c u)).2
  extra := fun c => (G.cellPC c).extra
  junction := G.junc
  junction_mu := G.junction_mu'
  count := G.count'

theorem pair_set (j : Fin G.m) :
    ({(G.cellPC (.inl j)).emb.atom ⟨1, by show 1 < 2; omega⟩, (G.cellPC (.inl j)).emb.atom ⟨0, by show 0 < 2; omega⟩} :
      Finset V) = G.piece (G.cnode (.inl j)) := by
  ext v
  rw [(G.cellPC (.inl j)).atoms v, mem_insert, mem_singleton]
  constructor
  · rintro (h | h) <;> exact ⟨_, h.symm⟩
  · rintro ⟨⟨_ | _ | n, hu⟩, h⟩
    · exact Or.inr h.symm
    · exact Or.inl h.symm
    · exfalso; have : n + 1 + 1 < 2 := hu; omega

theorem core_set :
    ({(G.cellPC Cell.core).emb.atom ⟨0, by show 0 < 3; omega⟩, (G.cellPC Cell.core).emb.atom ⟨1, by show 1 < 3; omega⟩,
      (G.cellPC Cell.core).emb.atom ⟨2, by show 2 < 3; omega⟩} : Finset V) = G.piece G.core := by
  ext v
  rw [show G.piece G.core = G.piece (G.cnode Cell.core) from rfl, (G.cellPC Cell.core).atoms v, mem_insert,
    mem_insert, mem_singleton]
  constructor
  · rintro (h | h | h) <;> exact ⟨_, h.symm⟩
  · rintro ⟨⟨_ | _ | _ | n, hu⟩, h⟩
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr h.symm)
    · exfalso; have : n + 1 + 1 + 1 < 3 := hu; omega

/-- **The cells are the pieces.** -/
theorem groups : G.toPre.toDecomp.cellGroups = M.tvineGroups S a b := by
  rw [PreDecomp.toDecomp_cellGroups]
  change (univ.image fun j : Fin G.m =>
      ({(G.cellPC (.inl j)).emb.atom ⟨1, by show 1 < 2; omega⟩,
        (G.cellPC (.inl j)).emb.atom ⟨0, by show 0 < 2; omega⟩} : Finset V)) ∪
    {{(G.cellPC Cell.core).emb.atom ⟨0, by show 0 < 3; omega⟩, (G.cellPC Cell.core).emb.atom ⟨1, by show 1 < 3; omega⟩,
      (G.cellPC Cell.core).emb.atom ⟨2, by show 2 < 3; omega⟩}} = M.pieces S a b
  simp only [G.pair_set, G.core_set]
  ext P
  simp only [mem_union, mem_image, mem_univ, true_and, mem_singleton]
  constructor
  · rintro (⟨j, rfl⟩ | rfl)
    · exact G.piece_mem (G.valid_cnode _) (G.mem_pairsF.mp (G.cnode_mem j)).2.2
    · exact G.piece_mem G.core_valid G.core_ne_cp
  · intro hP
    have hnode : ∃ n, G.Valid n ∧ n ≠ .cp ∧ G.piece n = P := by
      rcases G.L.all P hP with ⟨i, h1, h2, rfl⟩ | ⟨k, hk, rfl⟩
      · refine ⟨.sp (i - 1), show i - 1 < G.L.r by omega, by simp, ?_⟩
        show G.L.Z (i - 1 + 1) = G.L.Z i
        rw [show i - 1 + 1 = i by omega]
      · exact ⟨.pd k, hk, by simp, rfl⟩
    obtain ⟨n, hn, hcp, rfl⟩ := hnode
    by_cases hc : n = G.core
    · right; rw [hc]
    · left
      have hm : n ∈ G.pairsF := G.mem_pairsF.mpr ⟨hn, hc, hcp⟩
      refine ⟨G.pairEq ⟨n, hm⟩, ?_⟩
      show G.piece (G.pairEq.symm (G.pairEq ⟨n, hm⟩)).1 = G.piece n
      rw [Equiv.symm_apply_apply]

end Setup

/-! ## M4 Theorem C from the piece structure -/

/-- **The cell decompositions exist**, from the piece structure (N2 Prop 1.17(b), N3 Thm 6, M4 Lemma A). -/
theorem decompExists_of_inputs (hPS : PieceShapeInput) (hL : LayervineInput) (hA : AttachInput) : DecompExists := by
  intro V D _ _ _ M hM S a b hT
  obtain ⟨L⟩ := lay_of (hL M S a b hT).1
  obtain ⟨G⟩ := setup_exists hM hT hA hPS L
  exact ⟨G.toPre.toDecomp, G.groups⟩

/-- **M4 Theorem C (all sizes)**: every T-vine has a de-indexed full chart whose groups are its pieces. -/
theorem tvineChart_of_inputs (hPS : PieceShapeInput) (hL : LayervineInput) (hA : AttachInput) :
    TVineChartStatement :=
  tvineChart_of_decomp (decompExists_of_inputs hPS hL hA)

end WaveTurbulence.TVine.Chart
