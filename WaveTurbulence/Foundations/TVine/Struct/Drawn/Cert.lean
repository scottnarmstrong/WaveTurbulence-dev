/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.Drawn.Push

/-!
# Cuts and T-vine certificates for multigraphs given by bond multisets (packet L3D)

* `crossB X e`: the bond `e` has exactly one end in `X`; `cut_ofMS`: the cut of `X` in `ofMS vs B` is the number of
  bonds of `B` crossing `X`;
* `deg_ofMS`, `nbrs_ofMS`, `connected_ofMS_of_walk`: degrees, neighbours and connectivity of `ofMS vs B` in terms of
  counts in `B`;
* `y2Apply`, `runMoves`: an explicit list of (Y2) moves, sound for `Relation.ReflTransGen Y2Step`
  (adapted from `tvine-defs/TVineCert.lean`, sha256 recorded in `COPIED-SHA256SUMS`);
* `isTVineU_ofMS_of_cert`: a decidable certificate for `IsTVineU (ofMS vs B) j₁ j₂`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct.Drawn

open TVine WaveTurbulence.TVine.Core

variable {V : Type*} [DecidableEq V]

/-! ## Crossing bonds and cuts -/

/-- The bond `e` has exactly one end in `X`. -/
def crossB (X : Finset V) : Sym2 V → Bool :=
  Sym2.lift ⟨fun a b => decide (a ∈ X) != decide (b ∈ X), fun a b => by
    dsimp only; cases decide (a ∈ X) <;> cases decide (b ∈ X) <;> rfl⟩

theorem crossB_mk (X : Finset V) (a b : V) : crossB X s(a, b) = (decide (a ∈ X) != decide (b ∈ X)) := rfl

/-- The number of ordered pairs `(u, w) ∈ X × Y` naming the bond `s(c, d)`, for disjoint `X, Y` covering `c, d`. -/
theorem sum_pairs_eq (X Y : Finset V) (hXY : Disjoint X Y) {c d : V} (hc : c ∈ X ∪ Y) (hd : d ∈ X ∪ Y) :
    (∑ u ∈ X, ∑ w ∈ Y, if s(u, w) = s(c, d) then 1 else 0) = if crossB X s(c, d) then 1 else 0 := by
  have hdis : ∀ {z : V}, z ∈ X → z ∈ Y → False := fun h1 h2 => Finset.disjoint_left.mp hXY h1 h2
  rw [crossB_mk]
  rcases Finset.mem_union.mp hc with hcX | hcY <;> rcases Finset.mem_union.mp hd with hdX | hdY
  · -- both in `X`
    have hb : (decide (c ∈ X) != decide (d ∈ X)) = false := by simp [hcX, hdX]
    rw [hb, if_neg (by simp)]
    apply Finset.sum_eq_zero; intro u _; apply Finset.sum_eq_zero; intro w hw
    rw [if_neg]; intro h
    rcases Sym2.eq_iff.mp h with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact hdis hdX hw
    · exact hdis hcX hw
  · -- `c ∈ X`, `d ∈ Y`
    have hdX : d ∉ X := fun h => hdis h hdY
    have hb : (decide (c ∈ X) != decide (d ∈ X)) = true := by simp [hcX, hdX]
    rw [hb, if_pos rfl]
    rw [Finset.sum_eq_single c]
    · rw [Finset.sum_eq_single d]
      · simp
      · intro w _ hwd; rw [if_neg]; intro h
        rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
        · exact hwd h2
        · exact hdis hcX (h1 ▸ hdY)
      · intro h; exact absurd hdY h
    · intro u hu huc; apply Finset.sum_eq_zero; intro w _; rw [if_neg]; intro h
      rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact huc h1
      · exact hdis (h1 ▸ hu) hdY
    · intro h; exact absurd hcX h
  · -- `c ∈ Y`, `d ∈ X`
    have hcX : c ∉ X := fun h => hdis h hcY
    have hb : (decide (c ∈ X) != decide (d ∈ X)) = true := by simp [hcX, hdX]
    rw [hb, if_pos rfl]
    rw [Finset.sum_eq_single d]
    · rw [Finset.sum_eq_single c]
      · simp [Sym2.eq_swap]
      · intro w _ hwc; rw [if_neg]; intro h
        rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨-, h2⟩
        · exact hdis (h1.symm ▸ hdX) hcY |>.elim
        · exact hwc h2
      · intro h; exact absurd hcY h
    · intro u hu hud; apply Finset.sum_eq_zero; intro w _; rw [if_neg]; intro h
      rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hdis (h1 ▸ hu) hcY
      · exact hud h1
    · intro h; exact absurd hdX h
  · -- both in `Y`
    have hb : (decide (c ∈ X) != decide (d ∈ X)) = false := by
      simp [show c ∉ X from fun h => hdis h hcY, show d ∉ X from fun h => hdis h hdY]
    rw [hb, if_neg (by simp)]
    apply Finset.sum_eq_zero; intro u hu; apply Finset.sum_eq_zero; intro w _
    rw [if_neg]; intro h
    rcases Sym2.eq_iff.mp h with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hdis hu hcY
    · exact hdis hu hdY

theorem cut_ofMS {vs X : Finset V} {B : Multiset (Sym2 V)} (hwf : WF vs B) (hX : X ⊆ vs) :
    cut (ofMS vs B) X = B.countP (fun e => crossB X e = true) := by
  unfold cut
  simp only [ofMS_verts, ofMS_mult_of_wf hwf]
  induction B using Multiset.induction_on with
  | empty => simp
  | cons e B ih =>
    have hwf' : WF vs B := fun x hx => hwf x (Multiset.mem_cons_of_mem hx)
    rw [Multiset.countP_cons, ← ih hwf']
    simp only [Multiset.count_cons, Finset.sum_add_distrib]
    congr 1
    have he := hwf e (Multiset.mem_cons_self e B)
    induction e using Sym2.ind with
    | _ c d =>
      have hc := Finset.mem_sym2_iff.mp he c (Sym2.mem_mk_left c d)
      have hd := Finset.mem_sym2_iff.mp he d (Sym2.mem_mk_right c d)
      have hU : ∀ z ∈ vs, z ∈ X ∪ (vs \ X) := fun z hz => by
        by_cases h : z ∈ X
        · exact Finset.mem_union_left _ h
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hz, h⟩)
      rw [sum_pairs_eq X (vs \ X) Finset.disjoint_sdiff (hU c hc) (hU d hd)]

/-! ## Degrees, neighbours, connectivity of `ofMS` -/

theorem deg_ofMS {vs : Finset V} {B : Multiset (Sym2 V)} (hwf : WF vs B) (v : V) :
    deg (ofMS vs B) v = (∑ w ∈ vs, B.count s(v, w)) + B.count s(v, v) := by
  unfold deg; simp only [ofMS_verts, ofMS_mult_of_wf hwf]

theorem nbrs_ofMS {vs : Finset V} {B : Multiset (Sym2 V)} (hwf : WF vs B) (v : V) :
    nbrs (ofMS vs B) v = (∑ w ∈ vs, Multiset.replicate (B.count s(v, w)) w) +
      Multiset.replicate (B.count s(v, v)) v := by
  unfold nbrs; simp only [ofMS_verts, ofMS_mult_of_wf hwf]

theorem connected_ofMS_of_walk {vs : Finset V} {B : Multiset (Sym2 V)} (hwf : WF vs B) (l : List V)
    (hchain : List.IsChain (fun a b => B.count s(a, b) ≠ 0) l) (hcov : ∀ v ∈ vs, v ∈ l) :
    Connected (ofMS vs B) := by
  have hadj : ∀ a b, B.count s(a, b) ≠ 0 → AdjIn (ofMS vs B) vs a b := by
    intro a b h
    have hm : s(a, b) ∈ vs.sym2 := hwf _ (Multiset.count_ne_zero.mp h)
    refine ⟨Finset.mem_sym2_iff.mp hm a (Sym2.mem_mk_left a b), Finset.mem_sym2_iff.mp hm b (Sym2.mem_mk_right a b),
      ?_⟩
    rw [ofMS_mult_of_wf hwf]; exact h
  have hsymm : ∀ {a b : V}, AdjIn (ofMS vs B) vs a b → AdjIn (ofMS vs B) vs b a := by
    intro a b ⟨ha, hb, h⟩; exact ⟨hb, ha, by rw [Sym2.eq_swap]; exact h⟩
  have hsymm' : ∀ {a b : V}, Relation.ReflTransGen (AdjIn (ofMS vs B) vs) a b →
      Relation.ReflTransGen (AdjIn (ofMS vs B) vs) b a := by
    intro a b h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact Relation.ReflTransGen.head (hsymm hbc) ih
  have key : ∀ (l : List V) (a : V), List.IsChain (fun a b => B.count s(a, b) ≠ 0) (a :: l) →
      ∀ v ∈ a :: l, Relation.ReflTransGen (AdjIn (ofMS vs B) vs) a v := by
    intro l
    induction l with
    | nil => intro a _ v hv; simp only [List.mem_singleton] at hv; subst hv; exact Relation.ReflTransGen.refl
    | cons b l ih =>
      intro a hc v hv
      rw [List.isChain_cons_cons] at hc
      rcases List.mem_cons.mp hv with rfl | hv
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.head (hadj a b hc.1) (ih b hc.2 v hv)
  intro u hu w hw
  cases l with
  | nil => exact absurd (hcov u hu) (by simp)
  | cons a l =>
    exact (hsymm' (key l a hchain u (hcov u hu))).trans (key l a hchain w (hcov w hw))

/-! ## (Y2) move certificates -/

/-- The result of the (Y2) move `(a, b, c, d)` on `(vs, B)`, if its hypotheses hold. -/
def y2Apply (vs : Finset V) (B : Multiset (Sym2 V)) (m : V × V × V × V) :
    Option (Finset V × Multiset (Sym2 V)) :=
  if m.1 ≠ m.2.1 ∧ m.2.2.1 ≠ m.2.2.2 ∧ m.2.2.1 ≠ m.1 ∧ m.2.2.1 ≠ m.2.1 ∧ m.2.2.2 ≠ m.1 ∧
      m.2.2.2 ≠ m.2.1 ∧ B.count s(m.1, m.2.1) = 3 ∧ B.count s(m.1, m.2.2.1) = 1 ∧
      B.count s(m.2.1, m.2.2.2) = 1 ∧
      (∀ x ∈ vs, x ≠ m.2.1 → x ≠ m.2.2.1 → B.count s(m.1, x) = 0) ∧
      (∀ x ∈ vs, x ≠ m.1 → x ≠ m.2.2.2 → B.count s(m.2.1, x) = 0)
  then some ((vs.erase m.1).erase m.2.1, B.filter (fun e => m.1 ∉ e ∧ m.2.1 ∉ e) + {s(m.2.2.1, m.2.2.2)})
  else none

theorem y2Apply_sound {vs : Finset V} {B : Multiset (Sym2 V)} (h : WF vs B) {m : V × V × V × V}
    {vs' : Finset V} {B' : Multiset (Sym2 V)} (hm : y2Apply vs B m = some (vs', B')) :
    WF vs' B' ∧ Y2Step (ofMS vs B) (ofMS vs' B') := by
  obtain ⟨a, b, c, d⟩ := m
  unfold y2Apply at hm
  split_ifs at hm with hc
  obtain ⟨hab, hcd, hca, hcb, hda, hdb, h3, hc1, hd1, hax, hbx⟩ := hc
  simp only [Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  dsimp only at hab hcd hca hcb hda hdb h3 hc1 hd1 hax hbx
  have hcv : c ∈ vs := Finset.mem_sym2_iff.mp (h _ (Multiset.count_ne_zero.mp (by omega))) c (Sym2.mem_mk_right a c)
  have hdv : d ∈ vs := Finset.mem_sym2_iff.mp (h _ (Multiset.count_ne_zero.mp (by omega))) d (Sym2.mem_mk_right b d)
  have h' : WF ((vs.erase a).erase b) (B.filter (fun e => a ∉ e ∧ b ∉ e) + {s(c, d)}) := by
    intro e he
    rw [Multiset.mem_add, Multiset.mem_filter, Multiset.mem_singleton] at he
    rw [Finset.mem_sym2_iff]
    intro x hx
    rcases he with ⟨heB, ha, hb⟩ | rfl
    · have hxv := Finset.mem_sym2_iff.mp (h e heB) x hx
      have hxa : x ≠ a := fun hh => ha (hh ▸ hx)
      have hxb : x ≠ b := fun hh => hb (hh ▸ hx)
      simp [Finset.mem_erase, hxa, hxb, hxv]
    · rcases Sym2.mem_iff.mp hx with rfl | rfl
      · simp [Finset.mem_erase, hca, hcb, hcv]
      · simp [Finset.mem_erase, hda, hdb, hdv]
  refine ⟨h', a, b, c, d, hab, hcd, hca, hcb, hda, hdb, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · rw [ofMS_mult_of_wf h]; exact h3
  · rw [ofMS_mult_of_wf h]; exact hc1
  · rw [ofMS_mult_of_wf h]; exact hd1
  · intro x hxb hxc
    rw [ofMS_mult_of_wf h]
    by_cases hx : x ∈ vs
    · exact hax x hx hxb hxc
    · exact Multiset.count_eq_zero.mpr fun hmem => hx (Finset.mem_sym2_iff.mp (h _ hmem) x (Sym2.mem_mk_right a x))
  · intro x hxa hxd
    rw [ofMS_mult_of_wf h]
    by_cases hx : x ∈ vs
    · exact hbx x hx hxa hxd
    · exact Multiset.count_eq_zero.mpr fun hmem => hx (Finset.mem_sym2_iff.mp (h _ hmem) x (Sym2.mem_mk_right b x))
  · intro e
    rw [ofMS_mult_of_wf h', ofMS_mult_of_wf h, Multiset.count_add, Multiset.count_filter, Multiset.count_singleton]
    by_cases hab' : a ∈ e ∨ b ∈ e
    · have : ¬ (a ∉ e ∧ b ∉ e) := by tauto
      have hne : e ≠ s(c, d) := by
        rintro rfl
        rcases hab' with h1 | h1 <;> rcases Sym2.mem_iff.mp h1 with h2 | h2
        · exact hca h2.symm
        · exact hda h2.symm
        · exact hcb h2.symm
        · exact hdb h2.symm
      simp [this, hab', hne]
    · have : (a ∉ e ∧ b ∉ e) := by tauto
      simp [this, hab']

/-- Run a list of (Y2) moves. -/
def runMoves : Finset V → Multiset (Sym2 V) → List (V × V × V × V) → Option (Finset V × Multiset (Sym2 V))
  | vs, B, [] => some (vs, B)
  | vs, B, m :: ms => (y2Apply vs B m).bind fun p => runMoves p.1 p.2 ms

theorem rtg_of_runMoves : ∀ (ms : List (V × V × V × V)) {vs : Finset V} {B : Multiset (Sym2 V)} (_h : WF vs B)
    {vs' : Finset V} {B' : Multiset (Sym2 V)}, runMoves vs B ms = some (vs', B') →
    WF vs' B' ∧ Relation.ReflTransGen Y2Step (ofMS vs B) (ofMS vs' B')
  | [], vs, B, h, vs', B', hr => by
      simp only [runMoves, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨h, Relation.ReflTransGen.refl⟩
  | m :: ms, vs, B, h, vs', B', hr => by
      simp only [runMoves, Option.bind_eq_some_iff] at hr
      obtain ⟨⟨vs1, B1⟩, h1, h2⟩ := hr
      obtain ⟨hw, hstep⟩ := y2Apply_sound h h1
      obtain ⟨hw', hrt⟩ := rtg_of_runMoves ms hw h2
      exact ⟨hw', Relation.ReflTransGen.head hstep hrt⟩

theorem isDoubledTriangle_ofMS {vs : Finset V} {B : Multiset (Sym2 V)} (a b c : V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hv : vs = {a, b, c})
    (hB : B = {s(a, b), s(a, b), s(b, c), s(b, c), s(a, c), s(a, c)}) : IsDoubledTriangle (ofMS vs B) := by
  have hwf : WF vs B := by
    rw [hv, hB]; intro e he
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  refine ⟨a, b, c, hab, hac, hbc, hv, fun e => ?_⟩
  rw [ofMS_mult_of_wf hwf, hB]
  have h1 : s(a, b) ≠ s(b, c) := by simp [Sym2.eq_iff, hab, hac, hbc.symm, hab.symm]
  have h2 : s(a, b) ≠ s(a, c) := by simp [Sym2.eq_iff, hbc, hac, hab]
  have h3 : s(b, c) ≠ s(a, c) := by simp [Sym2.eq_iff, hab.symm, hac, hbc]
  by_cases e1 : e = s(a, b)
  · subst e1; simp [Multiset.count_cons, h1, h2]
  by_cases e2 : e = s(b, c)
  · subst e2; simp [Multiset.count_cons, e1, h3]
  by_cases e3 : e = s(a, c)
  · subst e3; simp [Multiset.count_cons, e1, e2]
  simp [Multiset.count_cons, e1, e2, e3]

/-! ## The certificate -/

/-- **A decidable certificate for `IsTVineU (ofMS vs B) j₁ j₂`** (σ = 0 or 1): degrees, a covering walk, the
multiplicity bound, the closure data and an explicit (Y2) path ending at a doubled triangle. -/
theorem isTVineU_ofMS_of_cert (vs : Finset V) (B : Multiset (Sym2 V)) (j₁ j₂ : V) (hwf : WF vs B)
    (hj : j₁ ∈ vs ∧ j₂ ∈ vs ∧ j₁ ≠ j₂)
    (hdeg : ∀ v ∈ vs, (∑ w ∈ vs, B.count s(v, w)) + B.count s(v, v) = if v = j₁ ∨ v = j₂ then 2 else 4)
    (l : List V) (hchain : List.IsChain (fun a b => B.count s(a, b) ≠ 0) l) (hcov : ∀ v ∈ vs, v ∈ l)
    (hm2 : ∀ u ∈ vs, ∀ v ∈ vs, u ≠ v → B.count s(u, v) ≤ 2)
    (added : Multiset (Sym2 V)) (hσ : B.count s(j₁, j₂) < 2)
    (hadd : (B.count s(j₁, j₂) = 0 ∧ ∃ a b c d : V,
          (∑ w ∈ vs, Multiset.replicate (B.count s(j₁, w)) w) + Multiset.replicate (B.count s(j₁, j₁)) j₁ = {a, b} ∧
          (∑ w ∈ vs, Multiset.replicate (B.count s(j₂, w)) w) + Multiset.replicate (B.count s(j₂, j₂)) j₂ = {c, d} ∧
          added = {s(a, b), s(c, d)}) ∨
       (B.count s(j₁, j₂) = 1 ∧ ∃ x y : V,
          (∑ w ∈ vs, Multiset.replicate (B.count s(j₁, w)) w) + Multiset.replicate (B.count s(j₁, j₁)) j₁ = {j₂, x} ∧
          (∑ w ∈ vs, Multiset.replicate (B.count s(j₂, w)) w) + Multiset.replicate (B.count s(j₂, j₂)) j₂ = {j₁, y} ∧
          added = {s(x, y)}))
    (hwf₀ : WF ((vs.erase j₁).erase j₂) (B.filter (fun e => j₁ ∉ e ∧ j₂ ∉ e) + added))
    (hloop : ∀ e ∈ B.filter (fun e => j₁ ∉ e ∧ j₂ ∉ e) + added, ¬ e.IsDiag)
    (ms : List (V × V × V × V)) (vs' : Finset V) (B' : Multiset (Sym2 V))
    (hrun : runMoves ((vs.erase j₁).erase j₂) (B.filter (fun e => j₁ ∉ e ∧ j₂ ∉ e) + added) ms = some (vs', B'))
    (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hv : vs' = {a, b, c})
    (hB : B' = {s(a, b), s(a, b), s(b, c), s(b, c), s(a, c), s(a, c)}) :
    IsTVineU (ofMS vs B) j₁ j₂ := by
  obtain ⟨h₁, h₂, h12⟩ := hj
  have hdeg' : ∀ v ∈ vs, deg (ofMS vs B) v = if v = j₁ ∨ v = j₂ then 2 else 4 := fun v hv => by
    rw [deg_ofMS hwf]; exact hdeg v hv
  refine ⟨⟨h₁, h₂, h12, by rw [hdeg' j₁ h₁]; simp, by rw [hdeg' j₂ h₂]; simp, fun v hv hv1 hv2 => by
    rw [hdeg' v hv]; simp [hv1, hv2], connected_ofMS_of_walk hwf l hchain hcov⟩, ?_, ?_⟩
  · intro u hu v hv huv; rw [ofMS_mult_of_wf hwf]; exact hm2 u hu v hv huv
  · refine ⟨ofMS ((vs.erase j₁).erase j₂) (B.filter (fun e => j₁ ∉ e ∧ j₂ ∉ e) + added),
      ⟨by rw [ofMS_mult_of_wf hwf]; exact hσ, rfl, fun x => ?_, added, ?_, fun e => ?_⟩, ?_⟩
    · rw [ofMS_mult_of_wf hwf₀]
      exact Multiset.count_eq_zero.mpr fun hm => hloop _ hm (Sym2.mk_isDiag_iff.mpr rfl)
    · rw [nbrs_ofMS hwf, nbrs_ofMS hwf, ofMS_mult_of_wf hwf]; exact hadd
    · rw [ofMS_mult_of_wf hwf₀, ofMS_mult_of_wf hwf, Multiset.count_add, Multiset.count_filter]
      congr 1
      by_cases h : j₁ ∈ e ∨ j₂ ∈ e
      · rw [if_neg (by tauto), if_pos h]
      · rw [if_pos (by tauto), if_neg h]
    · obtain ⟨hw', hrt⟩ := rtg_of_runMoves ms hwf₀ hrun
      exact ⟨_, hrt, isDoubledTriangle_ofMS a b c hab hac hbc hv hB⟩

end WaveTurbulence.TVine.Struct.Drawn
