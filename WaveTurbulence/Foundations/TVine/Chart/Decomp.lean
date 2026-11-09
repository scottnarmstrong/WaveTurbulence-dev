/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.Assemble
public import WaveTurbulence.Foundations.TVine.Chart.Phases

/-!
# Cell decompositions and their global forms (M4 Theorem C, Step 2: gluing)

A **cell decomposition** of a block `S` with upper joint `a` and lower joint `b` is the data of M4 §3.2 Step 2:
* `m` **pair cells** (the 2-atom pieces: rungs and the junction), one **core cell** and `k` **copy cells** (the
  triangle of an attachment (P-b), which carries no atom), each with a local chart (`LocalChart`, Prop L) and a local
  embedding into `S`;
* the **joint embeddings** of `b` (its outgoing and incoming bond) and of `a`;
* the **gluing tree**: every cell's input pair is the output pair (exit pair `false`, pendant pair `true`) of its
  parent cell, or the bonds of `b`; parents have smaller rank (the block-cut order from `b`);
* the final spine cell, whose exit pair is the pair of bonds at `a`;
* ownership of every bond (by `b` or by exactly one cell), the atom partition, and for every extra equation of a
  local chart a 2-edge cut realizing it (N1 Lemma D).

The global decoding forms are defined by gluing: `κ_c` is the label form of the parent's output bond, and every local
bond of `c` has form `κ_c + Σ_i loc(l, i) x_{slot(c,i)} + locR(l) r` (`form_emb`).
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Chart

open Finset VineParamContract

/-- The cells: `m` pair cells, one core cell, `k` copy cells. -/
abbrev Cell (m k : ℕ) := Fin m ⊕ Unit ⊕ Fin k

/-- The core cell. -/
abbrev Cell.core {m k : ℕ} : Cell m k := .inr (.inl ())

/-- Atoms per cell. -/
def nAof {m k : ℕ} : Cell m k → ℕ
  | .inl _ => 2
  | .inr (.inl _) => 3
  | .inr (.inr _) => 0

/-- Coordinates per cell. -/
def nCof {m k : ℕ} : Cell m k → ℕ
  | .inl _ => 2
  | .inr (.inl _) => 3
  | .inr (.inr _) => 0

/-- A joint: one atom with one outgoing (`0`) and one incoming (`1`) stub. -/
abbrev jointGraph : LocalGraph := ⟨1, 2, ![some 0, none], ![none, some 0]⟩

/-- The output pair of a local chart: `false` the exit pair, `true` the pendant pair. -/
def outPair {nA nC nB : ℕ} (c : LocalChart nA nC nB) (w : Bool) : Option (Fin nB × Fin nB) :=
  if w then c.outB else c.outM

/-- The normal shape with `m` pairs. -/
abbrev nshape (m : ℕ) : Shape false := ⟨m⟩

/-- The global slots of the local coordinates of a cell: a pair cell `j` has `(x, y) ↦ (xSlot j, ySlot j)`, the core
`(u₁, u₂, u₃) ↦ uSlot`. -/
def slotOf {m k : ℕ} : (c : Cell m k) → Fin (nCof c) → Fin (nshape m).n
  | .inl j, i => ![(nshape m).xSlot j, (nshape m).ySlot j] i
  | .inr (.inl _), i => (nshape m).uSlot rfl i
  | .inr (.inr _), i => i.elim0

/-- The global slot map on all local coordinates. -/
def slotS {m k : ℕ} (σ : Σ c : Cell m k, Fin (nCof c)) : Fin (nshape m).n := slotOf σ.1 σ.2

theorem slotS_val {m k : ℕ} (σ : Σ c : Cell m k, Fin (nCof c)) :
    (slotS σ : ℕ) = match σ with
      | ⟨.inl j, i⟩ => if (i : ℕ) = 0 then j + 1 else m + 1 + j
      | ⟨.inr (.inl _), i⟩ => 2 * m + 1 + i
      | ⟨.inr (.inr _), i⟩ => i.elim0 := by
  rcases σ with ⟨(j | _ | j), i⟩
  · simp only [slotS, slotOf]
    have : (i : ℕ) < 2 := i.2
    rcases i with ⟨_ | _ | i, hi⟩
    · rfl
    · rfl
    · exfalso; have : i + 1 + 1 < 2 := hi; omega
  · rfl
  · exact i.elim0

theorem slotS_injective {m k : ℕ} : Function.Injective (slotS (m := m) (k := k)) := by
  intro σ τ h
  have hv := congrArg Fin.val h
  rw [slotS_val, slotS_val] at hv
  rcases σ with ⟨(j | _ | j), i⟩ <;> rcases τ with ⟨(j' | _ | j'), i'⟩
  all_goals try (first | exact i.elim0 | exact i'.elim0)
  · have hi : (i : ℕ) < 2 := i.2
    have hi' : (i' : ℕ) < 2 := i'.2
    have hj := j.2; have hj' := j'.2
    simp only at hv
    have : j = j' ∧ i = i' := by
      split_ifs at hv with h1 h2 h2 <;> constructor <;> (try apply Fin.ext) <;> omega
    rcases this with ⟨rfl, rfl⟩; rfl
  · have hi : (i : ℕ) < 2 := i.2; have hj := j.2; have hi' : (i' : ℕ) < 3 := i'.2
    simp only at hv; split_ifs at hv <;> omega
  · have hi' : (i' : ℕ) < 2 := i'.2; have hj' := j'.2; have hi : (i : ℕ) < 3 := i.2
    simp only at hv; split_ifs at hv <;> omega
  · simp only at hv
    have : i = i' := Fin.ext (by omega)
    subst this; rfl

theorem slotS_ne_x0 {m k : ℕ} (σ : Σ c : Cell m k, Fin (nCof c)) : slotS σ ≠ (nshape m).x0 := by
  intro h
  have hv := congrArg Fin.val h
  rw [slotS_val] at hv
  rcases σ with ⟨(j | _ | j), i⟩
  · simp only [Shape.x0] at hv; split_ifs at hv <;> omega
  · simp only [Shape.x0] at hv; omega
  · exact i.elim0

theorem slotS_surj {m k : ℕ} (i : Fin (nshape m).n) (hi : i ≠ (nshape m).x0) :
    ∃ σ : Σ c : Cell m k, Fin (nCof c), slotS σ = i := by
  have hn : (i : ℕ) < 2 * m + 4 := by
    have := i.2; simp only [Shape.n, nshape, Bool.false_eq_true, ite_false] at this; omega
  have h0 : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
  by_cases h1 : (i : ℕ) ≤ m
  · refine ⟨⟨.inl ⟨i - 1, by omega⟩, ⟨0, by simp [nCof]⟩⟩, Fin.ext ?_⟩
    rw [slotS_val]; simp; omega
  by_cases h2 : (i : ℕ) ≤ 2 * m
  · refine ⟨⟨.inl ⟨i - m - 1, by omega⟩, ⟨1, by simp [nCof]⟩⟩, Fin.ext ?_⟩
    rw [slotS_val]; simp; omega
  · refine ⟨⟨Cell.core, ⟨i - 2 * m - 1, by simp [nCof]; omega⟩⟩, Fin.ext ?_⟩
    rw [slotS_val]; simp; omega

/-- The push-forward of a local coefficient vector to the global slots. -/
def lift {m k : ℕ} (c : Cell m k) (v : Fin (nCof c) → ℤ) : Fin (nshape m).n → ℤ :=
  fun i => ∑ i', if slotOf c i' = i then v i' else 0

theorem lift_slot {m k : ℕ} (c : Cell m k) (v : Fin (nCof c) → ℤ) (i' : Fin (nCof c)) :
    lift c v (slotOf c i') = v i' := by
  unfold lift
  rw [Finset.sum_eq_single i']
  · simp
  · intro j _ hj
    have : slotOf c j ≠ slotOf c i' := fun h => hj (by
      have := @slotS_injective m k ⟨c, j⟩ ⟨c, i'⟩ h
      exact eq_of_heq (Sigma.mk.inj_iff.mp this).2)
    simp [this]
  · simp

theorem lift_of_not_mem {m k : ℕ} (c : Cell m k) (v : Fin (nCof c) → ℤ) (i : Fin (nshape m).n)
    (hi : ∀ i', slotOf c i' ≠ i) : lift c v i = 0 := by
  unfold lift
  exact Finset.sum_eq_zero (fun j _ => by simp [hi j])

theorem lift_zero {m k : ℕ} (c : Cell m k) : lift c (fun _ => 0) = 0 := by
  funext i; simp [lift]

theorem lift_linear {m k : ℕ} (c : Cell m k) {ι : Type*} (s : Finset ι) (a : ι → ℤ)
    (v : ι → Fin (nCof c) → ℤ) (i : Fin (nshape m).n) :
    (∑ t ∈ s, a t * lift c (v t) i) = lift c (fun i' => ∑ t ∈ s, a t * v t i') i := by
  unfold lift
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i' _ => ?_)
  split_ifs <;> simp

/-- **A cell decomposition** of a normal block (M4 Theorem C, Step 2). -/
structure Decomp {V D : Type*} [DecidableEq V] [Fintype D] (M : Molecule V D) (S : Finset V) (a b : V) where
  m : ℕ
  k : ℕ
  nB : Cell m k → ℕ
  cfg : (c : Cell m k) → LocalChart (nAof c) (nCof c) (nB c)
  valid : ∀ c, (cfg c).Valid
  pairOK : ∀ j, PairOK (cfg (.inl j))
  coreOK : CoreOK (cfg Cell.core)
  emb : (c : Cell m k) → LocEmb (cfg c).graph M S
  jb : LocEmb jointGraph M S
  ja : LocEmb jointGraph M S
  jb_atom : jb.atom 0 = b
  ja_atom : ja.atom 0 = a
  rank : Cell m k → ℕ
  parent : Cell m k → Option (Cell m k × Bool)
  parent_rank : ∀ c s w, parent c = some (s, w) → rank s < rank c
  wire_base : ∀ c, parent c = none → (emb c).bond (cfg c).eO = jb.bond 0 ∧
    (emb c).bond (cfg c).eI = jb.bond 1 ∧ (cfg c).locR (cfg c).eO = 1
  wire : ∀ c s w, parent c = some (s, w) → ∃ p, outPair (cfg s) w = some p ∧
    (emb c).bond (cfg c).eO = (emb s).bond p.1 ∧ (emb c).bond (cfg c).eI = (emb s).bond p.2 ∧
    (cfg c).locR (cfg c).eO = (cfg s).locR p.1 - (cfg s).locR p.2
  final : Cell m k
  final_out : ∃ p, (cfg final).outM = some p ∧ ja.bond 0 = (emb final).bond p.2 ∧
    ja.bond 1 = (emb final).bond p.1 ∧ (cfg final).locR p.1 - (cfg final).locR p.2 = 1
  own : Bond M S → Option (Σ c : Cell m k, Fin (nB c))
  own_none : ∀ e, own e = none → e = jb.bond 0 ∨ e = jb.bond 1
  own_some : ∀ e c l, own e = some ⟨c, l⟩ → (emb c).bond l = e ∧ ¬ (cfg c).IsInput l
  own_emb : ∀ c l, ¬ (cfg c).IsInput l → own ((emb c).bond l) = some ⟨c, l⟩
  own_jb : ∀ i, own (jb.bond i) = none
  atom_mem : ∀ c u, (emb c).atom u ∈ S
  cover : ∀ v ∈ S, v = a ∨ v = b ∨ ∃ c u, (emb c).atom u = v
  atom_inj : ∀ c c' u u', (emb c).atom u = (emb c').atom u' →
    (⟨c, u⟩ : Σ c : Cell m k, Fin (nAof c)) = ⟨c', u'⟩
  atom_ne_a : ∀ c u, (emb c).atom u ≠ a
  atom_ne_b : ∀ c u, (emb c).atom u ≠ b
  extra : ∀ c x, (emb c).bond ((cfg c).X₁ x) ≠ (emb c).bond ((cfg c).X₂ x) ∧
    ∃ Y ⊆ S, ∀ e, Crosses Y e ↔ e = (emb c).bond ((cfg c).X₁ x) ∨ e = (emb c).bond ((cfg c).X₂ x)
  junction : Option (Fin m)
  junction_mu : ∀ j, (cfg (.inl j)).mu = if junction = some j then 1 else 2

namespace Decomp

variable {V D : Type*} [DecidableEq V] [Fintype D] {M : Molecule V D} {S : Finset V} {a b : V}
variable (Dc : Decomp M S a b)

/-- The transfer form of an output pair (the form of its incoming bond relative to `κ`). -/
def transfer (s : Cell Dc.m Dc.k) (w : Bool) : (Fin (nshape Dc.m).n → ℤ) × ℤ :=
  match outPair (Dc.cfg s) w with
  | some p => (lift s ((Dc.cfg s).loc p.2), (Dc.cfg s).locR p.2)
  | none => 0

/-- The form of `b`'s incoming bond: `g − r − x₀`. -/
def baseKap : (Fin (nshape Dc.m).n → ℤ) × ℤ := (fun i => if i = (nshape Dc.m).x0 then -1 else 0, -1)

/-- **`κ_c`**: the label form of the incoming bond of `c`'s input pair, by gluing along the tree. -/
def kap (c : Cell Dc.m Dc.k) : (Fin (nshape Dc.m).n → ℤ) × ℤ :=
  match h : Dc.parent c with
  | none => Dc.baseKap
  | some (s, w) => kap s + Dc.transfer s w
termination_by Dc.rank c
decreasing_by exact Dc.parent_rank c s w h

theorem kap_none {c : Cell Dc.m Dc.k} (h : Dc.parent c = none) : Dc.kap c = Dc.baseKap := by
  rw [kap]; split <;> simp_all

theorem kap_some {c s : Cell Dc.m Dc.k} {w : Bool} (h : Dc.parent c = some (s, w)) :
    Dc.kap c = Dc.kap s + Dc.transfer s w := by
  rw [kap]; split <;> simp_all

/-- The local form of a local bond of a cell. -/
def locForm (c : Cell Dc.m Dc.k) (l : Fin (Dc.nB c)) : (Fin (nshape Dc.m).n → ℤ) × ℤ :=
  (lift c ((Dc.cfg c).loc l), (Dc.cfg c).locR l)

open Classical in
/-- **The global decoding form** of a bond (anchor coefficient `1` implicit). -/
noncomputable def form (e : Bond M S) : (Fin (nshape Dc.m).n → ℤ) × ℤ :=
  match Dc.own e with
  | none => if e = Dc.jb.bond 0 then Dc.baseKap + (0, 1) else Dc.baseKap
  | some ⟨c, l⟩ => Dc.kap c + Dc.locForm c l

theorem jb_ne : Dc.jb.bond 0 ≠ Dc.jb.bond 1 := fun h => by
  have := Dc.jb.bond_inj h
  exact absurd this (by decide)

theorem form_jb0 : Dc.form (Dc.jb.bond 0) = Dc.baseKap + (0, 1) := by
  unfold form; rw [Dc.own_jb 0]; simp

theorem form_jb1 : Dc.form (Dc.jb.bond 1) = Dc.baseKap := by
  unfold form; rw [Dc.own_jb 1]; simp [Dc.jb_ne.symm]

theorem locForm_eI (c : Cell Dc.m Dc.k) : Dc.locForm c (Dc.cfg c).eI = 0 := by
  unfold locForm
  have h1 : (Dc.cfg c).loc (Dc.cfg c).eI = fun _ => 0 := funext (LocalChart.loc_eI (Dc.valid c))
  rw [h1, lift_zero, LocalChart.locR_eI (Dc.valid c)]; rfl

/-- **The local-form invariant**: every local bond of every cell, input or owned, has the glued form
`κ_c + locForm c l`. -/
theorem form_emb : ∀ (c : Cell Dc.m Dc.k) (l : Fin (Dc.nB c)), Dc.form ((Dc.emb c).bond l) = Dc.kap c + Dc.locForm c l := by
  intro c
  induction hr : Dc.rank c using Nat.strong_induction_on generalizing c with
  | _ N ih =>
  intro l
  by_cases hl : (Dc.cfg c).IsInput l
  · rcases hl with rfl | rfl
    · -- the incoming input bond eO
      cases hp : Dc.parent c with
      | none =>
        obtain ⟨h1, -, h3⟩ := Dc.wire_base c hp
        rw [h1, Dc.form_jb0, Dc.kap_none hp]
        unfold locForm
        have h0 : (Dc.cfg c).loc (Dc.cfg c).eO = fun _ => 0 := funext (LocalChart.loc_eO (Dc.valid c))
        rw [h0, lift_zero, h3]
      | some sw =>
        obtain ⟨s, w⟩ := sw
        obtain ⟨p, hp1, h1, -, h3⟩ := Dc.wire c s w hp
        have hrk := Dc.parent_rank c s w hp
        rw [h1, ih (Dc.rank s) (hr ▸ hrk) s rfl, Dc.kap_some hp]
        unfold transfer locForm
        rw [hp1]
        have hloc : (Dc.cfg s).loc p.1 = (Dc.cfg s).loc p.2 := by
          funext i
          by_cases hw : w
          · subst hw; exact LocalChart.outB_loc (Dc.valid s) (by simpa [outPair] using hp1) i
          · simp only [Bool.not_eq_true] at hw; subst hw
            exact LocalChart.outM_loc (Dc.valid s) (by simpa [outPair] using hp1) i
        have h0 : (Dc.cfg c).loc (Dc.cfg c).eO = fun _ => 0 := funext (LocalChart.loc_eO (Dc.valid c))
        rw [h0, lift_zero, h3, hloc]
        ext i
        · simp
        · simp
    · -- the outgoing input bond eI
      rw [Dc.locForm_eI, add_zero]
      cases hp : Dc.parent c with
      | none =>
        obtain ⟨-, h2, -⟩ := Dc.wire_base c hp
        rw [h2, Dc.form_jb1, Dc.kap_none hp]
      | some sw =>
        obtain ⟨s, w⟩ := sw
        obtain ⟨p, hp1, -, h2, -⟩ := Dc.wire c s w hp
        have hrk := Dc.parent_rank c s w hp
        rw [h2, ih (Dc.rank s) (hr ▸ hrk) s rfl, Dc.kap_some hp]
        unfold transfer locForm
        rw [hp1]
  · unfold form
    rw [Dc.own_emb c l hl]

end Decomp

end WaveTurbulence.TVine.Chart
