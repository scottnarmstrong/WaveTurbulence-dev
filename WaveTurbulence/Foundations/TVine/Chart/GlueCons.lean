/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.Glue

/-!
# Gluing: conservation, coordinates and uniqueness (M4 Theorem C, (C1)–(C3))

The chart data `Decomp.toChartData` of a cell decomposition: the glued forms are conserved at every atom, each
coordinate is the local opposite difference of its cell's chart, and a homogeneous labelling with zero coordinates
vanishes (induction along the gluing tree; each step is the local uniqueness certificate of `Chart.Configs*`, and
the extra 2-cut equations come from N1 Lemma D).
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Chart

open Finset VineParamContract

namespace Decomp

variable {V D : Type*} [DecidableEq V] [Fintype D] {M : Molecule V D} {S : Finset V} {a b : V}
variable (Dc : Decomp M S a b)

/-- The decoding matrix. -/
noncomputable def F : Matrix (Bond M S) (Fin (nshape Dc.m).n) ℤ := fun e i => (Dc.form e).1 i

/-- The gap coefficients. -/
noncomputable def C : Bond M S → ℤ := fun e => (Dc.form e).2

/-- The first origin of each coordinate (`h` for `x₀`). -/
noncomputable def pO (i : Fin (nshape Dc.m).n) : Bond M S ⊕ Fin 2 :=
  match Dc.slotInv i with
  | none => .inr 1
  | some σ => .inl ((Dc.emb σ.1).bond ((Dc.cfg σ.1).orgP σ.2))

/-- The second origin of each coordinate (`b`'s incoming bond for `x₀`). -/
noncomputable def qO (i : Fin (nshape Dc.m).n) : Bond M S ⊕ Fin 2 :=
  match Dc.slotInv i with
  | none => .inl (Dc.jb.bond 1)
  | some σ => .inl ((Dc.emb σ.1).bond ((Dc.cfg σ.1).orgQ σ.2))

theorem jinc0 : jointGraph.inc 0 0 = 1 := by decide
theorem jinc1 : jointGraph.inc 0 1 = -1 := by decide

theorem sum_joint {β : Type*} [AddCommGroup β] (φ : LocEmb jointGraph M S) (f : ℤ → Bond M S → β)
    (hf : ∀ e, f 0 e = 0) :
    (∑ e : Bond M S, f (incidence M (φ.atom 0) e.1) e) = f 1 (φ.bond 0) + f (-1) (φ.bond 1) := by
  rw [φ.sum_transfer f hf 0, Fin.sum_univ_two, jinc0, jinc1]

/-- Transfer of incidence sums at a cell atom, in the chart's own incidence. -/
theorem emb_sum {β : Type*} [AddCommMonoid β] (c : Cell Dc.m Dc.k) (u : Fin (nAof c)) (f : ℤ → Bond M S → β)
    (hf : ∀ e, f 0 e = 0) :
    (∑ e : Bond M S, f (incidence M ((Dc.emb c).atom u) e.1) e) = ∑ l, f ((Dc.cfg c).inc u l) ((Dc.emb c).bond l) :=
  (Dc.emb c).sum_transfer f hf u

theorem emb_flow {E : Type*} [AddCommGroup E] (c : Cell Dc.m Dc.k) (u : Fin (nAof c)) (d : Bond M S → E) :
    flow M S d ((Dc.emb c).atom u) = ∑ l, (Dc.cfg c).inc u l • d ((Dc.emb c).bond l) :=
  (Dc.emb c).flow_transfer d u

theorem consF_cell (c : Cell Dc.m Dc.k) (u : Fin (nAof c)) (i : Fin (nshape Dc.m).n) :
    (∑ e : Bond M S, incidence M ((Dc.emb c).atom u) e.1 * Dc.F e i) = 0 := by
  rw [Dc.emb_sum c u (fun z e => z * Dc.F e i) (fun e => zero_mul _)]
  simp only [F, Dc.form_emb, locForm, Prod.fst_add, Pi.add_apply, mul_add, Finset.sum_add_distrib,
    ← Finset.sum_mul, LocalChart.sum_inc (Dc.valid c), zero_mul, zero_add]
  rw [lift_linear]
  have : (fun i' => ∑ l, (Dc.cfg c).inc u l * (Dc.cfg c).loc l i') = fun _ => 0 :=
    funext (LocalChart.sum_inc_loc (Dc.valid c) u)
  rw [this, lift_zero]; rfl

theorem consC_cell (c : Cell Dc.m Dc.k) (u : Fin (nAof c)) :
    (∑ e : Bond M S, incidence M ((Dc.emb c).atom u) e.1 * Dc.C e) = 0 := by
  rw [Dc.emb_sum c u (fun z e => z * Dc.C e) (fun e => zero_mul _)]
  simp only [C, Dc.form_emb, locForm, Prod.snd_add, mul_add, Finset.sum_add_distrib,
    ← Finset.sum_mul, LocalChart.sum_inc (Dc.valid c), zero_mul, zero_add]
  exact LocalChart.sum_inc_locR (Dc.valid c) u

theorem final_loc : ∃ p, (Dc.cfg Dc.final).outM = some p ∧ Dc.ja.bond 0 = (Dc.emb Dc.final).bond p.2 ∧
    Dc.ja.bond 1 = (Dc.emb Dc.final).bond p.1 ∧ (Dc.cfg Dc.final).locR p.1 - (Dc.cfg Dc.final).locR p.2 = 1 ∧
    (Dc.cfg Dc.final).loc p.1 = (Dc.cfg Dc.final).loc p.2 := by
  obtain ⟨p, h1, h2, h3, h4⟩ := Dc.final_out
  exact ⟨p, h1, h2, h3, h4, funext (LocalChart.outM_loc (Dc.valid _) h1)⟩

theorem consF (hB : M.IsBlock S a b) : ∀ v ∈ S, ∀ i, (∑ e : Bond M S, incidence M v e.1 * Dc.F e i) = 0 := by
  intro v hv i
  rcases Dc.cover v hv with h | h | ⟨c, u, rfl⟩
  · rw [h.trans Dc.ja_atom.symm, sum_joint Dc.ja (fun z e => z * Dc.F e i) (fun e => zero_mul _)]
    obtain ⟨p, -, h2, h3, -, h5⟩ := Dc.final_loc
    simp only [F, h2, h3, Dc.form_emb, locForm, h5, Prod.fst_add, Pi.add_apply, smul_eq_mul, one_mul,
      neg_one_mul]
    ring
  · rw [h.trans Dc.jb_atom.symm, sum_joint Dc.jb (fun z e => z * Dc.F e i) (fun e => zero_mul _)]
    simp only [F, Dc.form_jb0, Dc.form_jb1, Prod.fst_add, Pi.add_apply, Pi.zero_apply, add_zero,
      one_mul, neg_one_mul, add_neg_cancel]
  · exact Dc.consF_cell c u i

theorem consC (hB : M.IsBlock S a b) : ∀ v ∈ S, (∑ e : Bond M S, incidence M v e.1 * Dc.C e) =
    (if v = b then 1 else 0) - (if v = a then 1 else 0) := by
  intro v hv
  have hab := hB.2.2.2.1
  rcases Dc.cover v hv with h | h | ⟨c, u, rfl⟩
  · rw [h.trans Dc.ja_atom.symm, sum_joint Dc.ja (fun z e => z * Dc.C e) (fun e => zero_mul _)]
    obtain ⟨p, -, h2, h3, h4, -⟩ := Dc.final_loc
    simp only [C, h2, h3, Dc.form_emb, locForm, Prod.snd_add, one_mul, neg_one_mul]
    rw [Dc.ja_atom]
    simp only [hab, ite_false, ite_true]
    linarith
  · rw [h.trans Dc.jb_atom.symm, sum_joint Dc.jb (fun z e => z * Dc.C e) (fun e => zero_mul _)]
    simp only [C, Dc.form_jb0, Dc.form_jb1, Prod.snd_add, one_mul, neg_one_mul]
    rw [Dc.jb_atom]
    simp [Ne.symm hab]
  · rw [Dc.consC_cell c u]
    simp [Dc.atom_ne_b c u, Dc.atom_ne_a c u]

theorem lift_single (c : Cell Dc.m Dc.k) (i' : Fin (nCof c)) (v : Fin (nCof c) → ℤ)
    (hv : ∀ j, v j = if i' = j then 1 else 0) : lift c v = Pi.single (slotOf c i') 1 := by
  funext i
  by_cases hs : ∃ j, slotOf c j = i
  · obtain ⟨j, rfl⟩ := hs
    rw [lift_slot, hv, Pi.single_apply]
    have : slotOf c j = slotOf c i' ↔ i' = j :=
      ⟨fun he => (eq_of_heq (Sigma.mk.inj_iff.mp (@slotS_injective Dc.m Dc.k ⟨c, j⟩ ⟨c, i'⟩ he)).2).symm,
        fun h => h ▸ rfl⟩
    simp only [this]
  · push Not at hs
    rw [lift_of_not_mem c v i hs, Pi.single_apply]
    simp only [show ¬ (i = slotOf c i') from fun h => hs i' h.symm, ite_false]

theorem coord (i : Fin (nshape Dc.m).n) :
    (originForm Dc.F Dc.C (Dc.pO i)).1 - (originForm Dc.F Dc.C (Dc.qO i)).1 = Pi.single i 1 ∧
      (originForm Dc.F Dc.C (Dc.pO i)).2 = (originForm Dc.F Dc.C (Dc.qO i)).2 := by
  rcases h : Dc.slotInv i with _ | σ
  · have hi := Dc.slotInv_eq_none h
    subst hi
    have e1 : Dc.pO (nshape Dc.m).x0 = .inr 1 := by simp [pO, h]
    have e2 : Dc.qO (nshape Dc.m).x0 = .inl (Dc.jb.bond 1) := by simp [qO, h]
    have hF : Dc.F (Dc.jb.bond 1) = fun j => if j = (nshape Dc.m).x0 then -1 else 0 := by
      funext j; simp [F, Dc.form_jb1, baseKap]
    have hC : Dc.C (Dc.jb.bond 1) = -1 := by simp [C, Dc.form_jb1, baseKap]
    rw [e1, e2]
    refine ⟨?_, ?_⟩
    · funext j
      simp only [originForm, Pi.sub_apply, Pi.zero_apply, hF, Pi.single_apply]
      split_ifs <;> simp
    · simp [originForm, hC]
  · have hi := Dc.slotInv_eq_some h
    subst hi
    obtain ⟨c, i'⟩ := σ
    have e1 : Dc.pO (slotS ⟨c, i'⟩) = .inl ((Dc.emb c).bond ((Dc.cfg c).orgP i')) := by
      simp [pO, Dc.slotInv_slotS]
    have e2 : Dc.qO (slotS ⟨c, i'⟩) = .inl ((Dc.emb c).bond ((Dc.cfg c).orgQ i')) := by
      simp [qO, Dc.slotInv_slotS]
    have hF : ∀ l, (Dc.F ((Dc.emb c).bond l) : Fin (nshape Dc.m).n → ℤ) =
        (Dc.kap c).1 + lift c ((Dc.cfg c).loc l) := by
      intro l; funext j; simp [F, Dc.form_emb, locForm]
    have hC : ∀ l, Dc.C ((Dc.emb c).bond l) = (Dc.kap c).2 + (Dc.cfg c).locR l := by
      intro l; simp [C, Dc.form_emb, locForm]
    rw [e1, e2]
    simp only [originForm, hF, hC]
    refine ⟨?_, by rw [LocalChart.coord_locR (Dc.valid c)]⟩
    rw [add_sub_add_left_eq_sub]
    have : lift c ((Dc.cfg c).loc ((Dc.cfg c).orgP i')) - lift c ((Dc.cfg c).loc ((Dc.cfg c).orgQ i')) =
        lift c (fun j => (Dc.cfg c).loc ((Dc.cfg c).orgP i') j - (Dc.cfg c).loc ((Dc.cfg c).orgQ i') j) := by
      funext j; simp only [Pi.sub_apply, lift, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun t _ => ?_); split_ifs <;> simp
    rw [this]
    exact Dc.lift_single c i' _ (fun j => LocalChart.coord_loc (Dc.valid c) i' j)

theorem unique (hM : M.IsMolecule) (hB : M.IsBlock S a b) (E : Type) [AddCommGroup E] (d : Bond M S → E)
    (hflow : ∀ v ∈ S, flow M S d v = 0) (hcoord : ∀ i, origin0 d (Dc.pO i) - origin0 d (Dc.qO i) = 0) :
    d = 0 := by
  have hb1 : d (Dc.jb.bond 1) = 0 := by
    have := hcoord (nshape Dc.m).x0
    simp only [pO, qO, Dc.slotInv_x0, origin0, zero_sub, neg_eq_zero] at this
    exact this
  have hb0 : d (Dc.jb.bond 0) = 0 := by
    have := hflow _ (Dc.jb_atom ▸ hB.2.2.1)
    rw [Dc.jb.flow_transfer, Fin.sum_univ_two, jinc0, jinc1, hb1] at this
    simpa using this
  have hcell : ∀ c l, d ((Dc.emb c).bond l) = 0 := by
    intro c
    induction hr : Dc.rank c using Nat.strong_induction_on generalizing c with
    | _ N ih =>
    have hinp : d ((Dc.emb c).bond (Dc.cfg c).eO) = 0 ∧ d ((Dc.emb c).bond (Dc.cfg c).eI) = 0 := by
      cases hp : Dc.parent c with
      | none =>
        obtain ⟨h1, h2, -⟩ := Dc.wire_base c hp
        rw [h1, h2]; exact ⟨hb0, hb1⟩
      | some sw =>
        obtain ⟨s, w⟩ := sw
        obtain ⟨p, -, h1, h2, -⟩ := Dc.wire c s w hp
        have hrk := Dc.parent_rank c s w hp
        rw [h1, h2]
        exact ⟨ih (Dc.rank s) (hr ▸ hrk) s rfl p.1, ih (Dc.rank s) (hr ▸ hrk) s rfl p.2⟩
    apply LocalChart.unique_local (Dc.valid c) (fun l => d ((Dc.emb c).bond l)) hinp.1 hinp.2
    · intro u
      have := hflow _ (Dc.atom_mem c u)
      rw [Dc.emb_flow] at this
      exact this
    · intro i'
      have := hcoord (slotS ⟨c, i'⟩)
      simp only [pO, qO, Dc.slotInv_slotS, origin0] at this
      exact this
    · intro x
      obtain ⟨hne, Y, hY, hcut⟩ := Dc.extra c x
      rw [lemmaD_homog hM hB hY hne hcut d hflow, sub_self]
  funext e
  rcases ho : Dc.own e with _ | ⟨c, l⟩
  · rcases Dc.own_none e ho with rfl | rfl
    · exact hb0
    · exact hb1
  · obtain ⟨h1, -⟩ := Dc.own_some e c l ho
    rw [← h1]; exact hcell c l

/-- **The chart data of a cell decomposition.** -/
noncomputable def toChartData (hM : M.IsMolecule) (hB : M.IsBlock S a b) : ChartData M false S a b where
  indexing := Dc.indexing hB
  F := Dc.F
  c := Dc.C
  p := Dc.pO
  q := Dc.qO
  unit e i := Dc.form_unit e i
  consF := Dc.consF hB
  consC := Dc.consC hB
  coord := Dc.coord
  unique := Dc.unique hM hB

end Decomp

end WaveTurbulence.TVine.Chart
