/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.ClassCount.Layout
public import WaveTurbulence.Foundations.Stage1.ClassCount.M1
public import WaveTurbulence.Foundations.Stage1.ClassCount.UnitDecode6
import Mathlib.Tactic

/-!
# CLASSCOUNT (LAB): arcs of a molecule with spliced-out units

Abstract statement (`SpliceData`) of the relation between the molecule `M` of a skeleton and the molecule `M'` of
its spliced garden: `ob`, `od` embeddings, units `U 0 … U (q-1)` with representatives, classes `cl`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open Finset WaveTurbulence

/-- The relation between a molecule `M` (the skeleton) and the molecule `M'` obtained by splicing the units
`U 0, …, U (q-1)` (disjoint atom sets with representatives `rep i ∈ U i`; `cl` is the class representative). -/
structure SpliceData {V D V' D' : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    [DecidableEq V'] [Fintype D'] [DecidableEq D'] (M : Molecule V D) (M' : Molecule V' D') where
  ob : V' → V
  od : D' → D
  q : ℕ
  U : ℕ → Finset V
  rep : ℕ → V
  cl : V → V
  ob_inj : Function.Injective ob
  od_inj : Function.Injective od
  od_mate : ∀ y, od (M'.mate y) = M.mate (od y)
  od_out : ∀ y, M.out (od y) = M'.out y
  U_disj : ∀ i j, i < q → j < q → i ≠ j → Disjoint (U i) (U j)
  rep_mem : ∀ i, i < q → rep i ∈ U i
  cl_unit : ∀ i, i < q → ∀ v ∈ U i, cl v = rep i
  cl_free : ∀ v, (∀ i, i < q → v ∉ U i) → cl v = v
  ob_atom : ∀ y, ob (M'.atom y) = cl (M.atom (od y))
  ob_range : ∀ v, (∃ c, ob c = v) ↔ cl v = v
  od_range : ∀ x, (∃ y, od y = x) ↔ ¬ ∃ i, i < q ∧ M.atom x ∈ U i ∧ M.atom (M.mate x) ∈ U i


namespace SpliceData
variable {V D V' D' : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
  [DecidableEq V'] [Fintype D'] [DecidableEq D'] {M : Molecule V D} {M' : Molecule V' D'}
  (SD : SpliceData M M')

/-- The fixed atoms: unclassed atoms and unit representatives. -/
def fixed [Fintype V] : Finset V := Finset.univ.filter (fun v => SD.cl v = SD.cl v ∧ SD.cl v = v)

theorem mem_fixed [Fintype V] (v : V) : v ∈ SD.fixed ↔ SD.cl v = v := by
  simp [fixed]

/-- The labelling of the fixed atoms through `ob`: `e v = ℓ' (ob⁻¹ v)`. -/
noncomputable def lab0 [Fintype V'] (ℓ' : V' ≃ Fin (Fintype.card V')) : V → ℕ := fun v =>
  if h : ∃ c, SD.ob c = v then ((ℓ' (Classical.choose h) : Fin _) : ℕ) else 0

theorem lab0_ob [Fintype V'] (ℓ' : V' ≃ Fin (Fintype.card V')) (c : V') :
    SD.lab0 ℓ' (SD.ob c) = ((ℓ' c : Fin _) : ℕ) := by
  have h : ∃ c', SD.ob c' = SD.ob c := ⟨c, rfl⟩
  have hc : Classical.choose h = c := SD.ob_inj (Classical.choose_spec h)
  simp only [lab0, dif_pos h, hc]

theorem lab0_inj [Fintype V] [Fintype V'] (ℓ' : V' ≃ Fin (Fintype.card V')) :
    Set.InjOn (SD.lab0 ℓ') (SD.fixed : Finset V) := by
  intro v hv v' hv' h
  obtain ⟨c, rfl⟩ := (SD.ob_range v).mpr ((SD.mem_fixed v).mp (Finset.mem_coe.mp hv))
  obtain ⟨c', rfl⟩ := (SD.ob_range v').mpr ((SD.mem_fixed v').mp (Finset.mem_coe.mp hv'))
  rw [lab0_ob, lab0_ob] at h
  rw [ℓ'.injective (Fin.ext h)]

theorem lab0_image [Fintype V] [Fintype V'] (ℓ' : V' ≃ Fin (Fintype.card V')) :
    SD.fixed.image (SD.lab0 ℓ') = Finset.range (Fintype.card V') := by
  ext y
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨c, rfl⟩ := (SD.ob_range v).mpr ((SD.mem_fixed v).mp hv)
    rw [lab0_ob]; exact (ℓ' c).2
  · intro hy
    refine ⟨SD.ob (ℓ'.symm ⟨y, hy⟩), (SD.mem_fixed _).mpr ((SD.ob_range _).mp ⟨_, rfl⟩), ?_⟩
    rw [lab0_ob]; simp

end SpliceData


theorem equiv_of_layout {V : Type*} [Fintype V] [DecidableEq V] (pos : V → ℕ) (n : ℕ)
    (hinj : Set.InjOn pos Set.univ) (himg : (Finset.univ : Finset V).image pos = Finset.range n) :
    Fintype.card V = n ∧ ∃ ℓ : V ≃ Fin (Fintype.card V), ∀ v, ((ℓ v : Fin (Fintype.card V)) : ℕ) = pos v := by
  have hcard : Fintype.card V = n := by
    have := Finset.card_image_of_injOn (s := (Finset.univ : Finset V)) (f := pos) (by simpa using hinj)
    rw [himg, Finset.card_range, Finset.card_univ] at this
    exact this.symm
  have hlt : ∀ v, pos v < Fintype.card V := fun v => by
    have : pos v ∈ (Finset.univ : Finset V).image pos := Finset.mem_image_of_mem _ (Finset.mem_univ v)
    rw [himg, Finset.mem_range, ← hcard] at this; exact this
  have hbij : Function.Bijective (fun v => (⟨pos v, hlt v⟩ : Fin (Fintype.card V))) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun a b h => hinj (Set.mem_univ a) (Set.mem_univ b) (by simpa using congrArg Fin.val h), by simp⟩
  exact ⟨hcard, Equiv.ofBijective _ hbij, fun v => rfl⟩

theorem count_allArcs (P : ℕ → ℕ) (data : ℕ → UnitData) (W : ℕ → ℕ) (hW : ∀ i, (data i).W = W i)
    (z : ℕ × ℕ) : ∀ (len idx base : ℕ),
    (allArcs P idx base ((List.range' idx len).map data)).count z =
      ∑ i ∈ Finset.Ico idx (idx + len),
        (globArcs (data i) (P i) (base + ∑ j ∈ Finset.Ico idx i, W j)).count z
  | 0, idx, base => by simp [allArcs]
  | len + 1, idx, base => by
    rw [List.range'_succ, List.map_cons]
    simp only [allArcs]
    rw [List.count_append, count_allArcs P data W hW z len (idx + 1) (base + (data idx).W)]
    rw [show idx + (len + 1) = (idx + 1) + len by ring]
    conv_rhs => rw [Finset.sum_eq_sum_Ico_succ_bot (show idx < idx + 1 + len by omega)]
    simp only [Finset.Ico_self, Finset.sum_empty, add_zero]
    refine congrArg₂ (· + ·) rfl ?_
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := (Finset.mem_Ico.mp hi).1
    rw [hW idx]
    have : ∑ j ∈ Finset.Ico idx i, W j = W idx + ∑ j ∈ Finset.Ico (idx + 1) i, W j :=
      Finset.sum_eq_sum_Ico_succ_bot (show idx < i by omega) _
    rw [this, add_assoc]


theorem range'_mem_wlists {α : Type*} [DecidableEq α] (F : ℕ → Finset α) (data : ℕ → α) (W : ℕ → ℕ) (N : ℕ)
    (h : ∀ i, i < N → 1 ≤ W i ∧ data i ∈ F (W i)) :
    ∀ (len idx : ℕ), idx + len ≤ N →
      (List.range' idx len).map data ∈ wlists F (∑ i ∈ Finset.Ico idx (idx + len), W i)
  | 0, idx, _ => by simpa using nil_mem_wlists F
  | len + 1, idx, hle => by
    rw [List.range'_succ, List.map_cons, show idx + (len + 1) = (idx + 1) + len by ring,
      Finset.sum_eq_sum_Ico_succ_bot (show idx < idx + 1 + len by omega)]
    exact mem_wlists_cons F (h idx (by omega)).1 (h idx (by omega)).2
      (range'_mem_wlists F data W N h len (idx + 1) (by omega))


namespace SpliceData
variable {V D V' D' : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
  [DecidableEq V'] [Fintype D'] [DecidableEq D'] {M : Molecule V D} {M' : Molecule V' D'}
  (SD : SpliceData M M')

theorem cl_rep {i : ℕ} (hi : i < SD.q) : SD.cl (SD.rep i) = SD.rep i :=
  SD.cl_unit i hi _ (SD.rep_mem i hi)

theorem layout [Fintype V] [Fintype V'] (ℓ' : V' ≃ Fin (Fintype.card V')) (W : ℕ → ℕ) (lab : ℕ → V → ℕ)
    (hlabInj : ∀ i, i < SD.q → Set.InjOn (lab i) (SD.U i))
    (hlabImg : ∀ i, i < SD.q → (SD.U i).image (lab i) = Finset.range (W i + 1)) :
    ∃ pos : V → ℕ, Set.InjOn pos Set.univ ∧
      (Finset.univ : Finset V).image pos = Finset.range (Fintype.card V' + ∑ j ∈ Finset.range SD.q, W j) ∧
      (∀ v, SD.cl v = v → pos v = SD.lab0 ℓ' v) ∧
      ∀ i, i < SD.q → ∀ v ∈ SD.U i, pos v = glob (lab i (SD.rep i)) (SD.lab0 ℓ' (SD.rep i))
        (Fintype.card V' + ∑ j ∈ Finset.range i, W j) (lab i v) := by
  classical
  obtain ⟨pos, hinj, himg, hfix, hunit⟩ := exists_layout SD.q (Fintype.card V') SD.fixed (SD.lab0 ℓ')
    (SD.lab0_inj ℓ') (SD.lab0_image ℓ') SD.U SD.U_disj SD.rep SD.rep_mem
    (fun i hi => (SD.mem_fixed _).mpr (SD.cl_rep hi))
    (fun i hi v hv hfx => by
      have h1 := SD.cl_unit i hi v hv
      have h2 := (SD.mem_fixed v).mp hfx
      rw [← h2, h1])
    (fun v => by
      by_cases h : ∃ i, i < SD.q ∧ v ∈ SD.U i
      · exact Or.inr h
      · left
        push Not at h
        exact (SD.mem_fixed v).mpr (SD.cl_free v h))
    W lab hlabInj hlabImg
  exact ⟨pos, hinj, himg, fun v hv => hfix v ((SD.mem_fixed v).mpr hv), hunit⟩

end SpliceData


theorem card_B_filter {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
    (p : D → Prop) [DecidablePred p] :
    ((Finset.univ : Finset {x : D // M.out x = true}).filter (fun b => p b.1)).card =
      ((Finset.univ : Finset D).filter (fun x => M.out x = true ∧ p x)).card := by
  refine Finset.card_bij (fun b _ => b.1) ?_ (fun a _ b _ h => Subtype.ext h) ?_
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact ⟨b.2, hb⟩
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact ⟨⟨x, hx.1⟩, by simpa using hx.2, rfl⟩


theorem groupArcs_glob {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
    (S : Finset V) (lab : V → ℕ) (g : ℕ → ℕ) :
    groupArcs M S (fun v => g (lab v)) = (groupArcs M S lab).map (fun a => (g a.1, g a.2)) := by
  classical
  unfold groupArcs
  rw [Multiset.map_map]; rfl

theorem count_groupArcs {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
    (S : Finset V) (lab : V → ℕ) (z : ℕ × ℕ) :
    (groupArcs M S lab).count z =
      ((Finset.univ : Finset D).filter (fun d =>
        M.out d = true ∧ M.InGroup S d ∧ (lab (M.atom d), lab (M.atom (M.mate d))) = z)).card := by
  classical
  unfold groupArcs
  rw [Multiset.count_map, Finset.card_def, Finset.filter_val]
  congr 1
  rw [Multiset.filter_filter]
  apply Multiset.filter_congr
  intro d _
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h3, h1.symm⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h3.symm, h1, h2⟩

/-- The out-darts with an end in a set `H` of atoms number at most `4 |H|`. -/
theorem card_hinge_darts_le {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
    (hM : M.IsMolecule) (hatoms : ∀ v, v ∈ M.atoms) (H : Finset V) :
    ((Finset.univ : Finset D).filter
      (fun y => M.out y = true ∧ (M.atom y ∈ H ∨ M.atom (M.mate y) ∈ H))).card ≤ 4 * H.card := by
  classical
  let g : D → D := fun y => if M.atom y ∈ H then y else M.mate y
  have hmaps : ∀ y ∈ (Finset.univ : Finset D).filter
      (fun y => M.out y = true ∧ (M.atom y ∈ H ∨ M.atom (M.mate y) ∈ H)),
      g y ∈ H.biUnion (fun h => M.dartsAt h) := by
    intro y hy
    obtain ⟨ho, hh⟩ := (Finset.mem_filter.mp hy).2
    simp only [g]
    split_ifs with h
    · exact Finset.mem_biUnion.mpr ⟨_, h, (Mole.mem_dartsAt M _ _).mpr rfl⟩
    · have : M.atom (M.mate y) ∈ H := hh.resolve_left h
      exact Finset.mem_biUnion.mpr ⟨_, this, (Mole.mem_dartsAt M _ _).mpr rfl⟩
  have hinj : Set.InjOn g ((Finset.univ : Finset D).filter
      (fun y => M.out y = true ∧ (M.atom y ∈ H ∨ M.atom (M.mate y) ∈ H))) := by
    intro y1 h1 y2 h2 h
    have o1 : M.out y1 = true := by have := (Finset.mem_filter.mp (Finset.mem_coe.mp h1)).2; exact this.1
    have o2 : M.out y2 = true := by have := (Finset.mem_filter.mp (Finset.mem_coe.mp h2)).2; exact this.1
    simp only [g] at h
    split_ifs at h with a1 a2 a2
    · exact h
    · exfalso
      have := congrArg M.out h
      rw [M.out_mate, o2] at this
      simp [o1] at this
    · exfalso
      have := congrArg M.out h
      rw [M.out_mate, o1] at this
      simp [o2] at this
    · exact Mole.mate_injective M h
  calc ((Finset.univ : Finset D).filter
        (fun y => M.out y = true ∧ (M.atom y ∈ H ∨ M.atom (M.mate y) ∈ H))).card
      ≤ (H.biUnion (fun h => M.dartsAt h)).card := Finset.card_le_card_of_injOn g hmaps hinj
    _ ≤ ∑ h ∈ H, (M.dartsAt h).card := Finset.card_biUnion_le
    _ ≤ ∑ _h ∈ H, 4 := Finset.sum_le_sum (fun h _ => Mole.deg_le_four M hM (hatoms h))
    _ = 4 * H.card := by simp [mul_comm]

namespace SpliceData
variable {V D V' D' : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
  [DecidableEq V'] [Fintype D'] [DecidableEq D'] {M : Molecule V D} {M' : Molecule V' D'}
  (SD : SpliceData M M')

open Classical in
/-- **LAB (abstract)**: the arc multiset of the skeleton molecule `M` is realized by `arcLists`. -/
theorem lab_arcs [Fintype V] [Fintype V'] (hM : M.IsMolecule) (hM' : M'.IsMolecule)
    (hatoms' : ∀ v, v ∈ M'.atoms)
    {ι : Type} [Fintype ι] [DecidableEq ι] (F : LadderFam M' ι)
    (hdisj : ∀ i j, i ≠ j → Disjoint (F.atomsOf i) (F.atomsOf j))
    (Hset : Finset V') (hH : ∀ c, (∃ i, i < SD.q ∧ SD.ob c = SD.rep i) → c ∈ Hset)
    (cs : ℕ → List IngCode) (W : ℕ → ℕ) (lab : ℕ → V → ℕ)
    (hwf : ∀ i, i < SD.q → ∀ c ∈ cs i, c.Wf) (hW : ∀ i, i < SD.q → W i = unitWeight (cs i) ∧ 1 ≤ W i)
    (hlabInj : ∀ i, i < SD.q → Set.InjOn (lab i) (SD.U i))
    (hlabImg : ∀ i, i < SD.q → (SD.U i).image (lab i) = Finset.range (W i + 1))
    (harcs : ∀ i, i < SD.q → groupArcs M (SD.U i) (lab i) =
      ((unitArcs (cs i) : List (ℕ × ℕ)) : Multiset (ℕ × ℕ))) :
    ∃ nsb : ℕ, nsb ≤ Fintype.card V ∧ ∃ ℓ : V ≃ Fin (Fintype.card V),
      ∃ L ∈ arcLists (Fintype.card V)
          (4 * ((M'.atoms.filter (fun a => ∀ i, a ∉ F.atomsOf i)).card + Fintype.card ι + Hset.card))
          (unitFamily (Fintype.card V) nsb
            ((M'.atoms.filter (fun a => ∀ i, a ∉ F.atomsOf i)).card + Fintype.card ι + Hset.card)
            (Fintype.card V - nsb)),
        ∀ z : Fin (Fintype.card V) × Fin (Fintype.card V),
          Fintype.card {b : {x : D // M.out x = true} //
            (ℓ (M.atom b.1), ℓ (M.atom (M.mate b.1))) = z} = L.count z := by
  obtain ⟨ℓ', hℓ'⟩ := F.exists_labelling hdisj
  obtain ⟨pos, hinj, himg, hfixpos, hunitpos⟩ := SD.layout ℓ' W lab hlabInj hlabImg
  obtain ⟨hcard, ℓ, hℓ⟩ := equiv_of_layout pos _ hinj himg
  set r := (M'.atoms.filter (fun a => ∀ i, a ∉ F.atomsOf i)).card + Fintype.card ι + Hset.card with hr
  let B := {x : D // M.out x = true}
  let arc : B → Fin (Fintype.card V) × Fin (Fintype.card V) :=
    fun b => (ℓ (M.atom b.1), ℓ (M.atom (M.mate b.1)))
  let Un : B → Prop := fun b => ∃ i, i < SD.q ∧ M.atom b.1 ∈ SD.U i ∧ M.atom (M.mate b.1) ∈ SD.U i
  let Free : V → Prop := fun v => ∀ i, i < SD.q → v ∉ SD.U i
  let Rg : B → Prop := fun b => ¬ Un b ∧ Free (M.atom b.1) ∧ Free (M.atom (M.mate b.1)) ∧
    ∃ y, SD.od y = b.1 ∧ F.Reg (M'.atom y) (M'.atom (M'.mate y))
  have hkey : ∀ (b : B) (y : D'), SD.od y = b.1 → Free (M.atom b.1) → Free (M.atom (M.mate b.1)) →
      ((ℓ (M.atom b.1) : Fin _) : ℕ) = (ℓ' (M'.atom y) : Fin _) ∧
      ((ℓ (M.atom (M.mate b.1)) : Fin _) : ℕ) = (ℓ' (M'.atom (M'.mate y)) : Fin _) := by
    intro b y hy hf1 hf2
    have e1 : SD.ob (M'.atom y) = M.atom b.1 := by
      rw [SD.ob_atom, hy]; exact SD.cl_free _ hf1
    have e2 : SD.ob (M'.atom (M'.mate y)) = M.atom (M.mate b.1) := by
      rw [SD.ob_atom, SD.od_mate, hy]; exact SD.cl_free _ hf2
    constructor
    · rw [hℓ, hfixpos _ (SD.cl_free _ hf1), ← e1, SD.lab0_ob]
    · rw [hℓ, hfixpos _ (SD.cl_free _ hf2), ← e2, SD.lab0_ob]
  have h1 : ∀ b, Rg b → nearPair (Fintype.card V) (arc b) := by
    rintro b ⟨-, hf1, hf2, y, hy, hreg⟩
    obtain ⟨k1, k2⟩ := hkey b y hy hf1 hf2
    obtain ⟨hne, hn1, hn2⟩ := hℓ' _ _ hreg
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have := congrArg Fin.val h
      simp only [arc] at this
      rw [k1, k2] at this
      exact hne (ℓ'.injective (Fin.ext this))
    · show ((ℓ (M.atom b.1) : Fin _) : ℕ) ≤ ((ℓ (M.atom (M.mate b.1)) : Fin _) : ℕ) + 2
      rw [k1, k2]; exact hn1
    · show ((ℓ (M.atom (M.mate b.1)) : Fin _) : ℕ) ≤ ((ℓ (M.atom b.1) : Fin _) : ℕ) + 2
      rw [k1, k2]; exact hn2
  have h2 : ∀ z, (Finset.univ.filter (fun b : B => Rg b ∧ arc b = z)).card ≤ 2 := by
    intro z
    rcases (Finset.univ.filter (fun b : B => Rg b ∧ arc b = z)).eq_empty_or_nonempty with he | ⟨b0, hb0⟩
    · rw [he]; simp
    · have hb0' := (Finset.mem_filter.mp hb0).2
      obtain ⟨-, hf1, hf2, y0, hy0, hreg0⟩ := hb0'.1
      have hne : M'.atom y0 ≠ M'.atom (M'.mate y0) := (hℓ' _ _ hreg0).1
      have hbb : M'.bondsBetween (M'.atom y0) (M'.atom (M'.mate y0)) ≤ 2 := F.bb_le_two hreg0
      have hsub : (Finset.univ.filter (fun b : B => Rg b ∧ arc b = z)).card ≤
          ((M'.dartsAt (M'.atom y0)).filter (fun y => M'.atom (M'.mate y) = M'.atom (M'.mate y0))).card := by
        refine Finset.card_le_card_of_injOn
          (fun b => if h : ∃ y, SD.od y = b.1 then Classical.choose h else y0) ?_ ?_
        · intro b hb
          have hb' := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
          obtain ⟨-, hg1, hg2, y, hy, hreg⟩ := hb'.1
          have hex : ∃ y, SD.od y = b.1 := ⟨y, hy⟩
          have hc : Classical.choose hex = y := SD.od_inj ((Classical.choose_spec hex).trans hy.symm)
          simp only [dif_pos hex, hc]
          obtain ⟨k1, k2⟩ := hkey b y hy hg1 hg2
          obtain ⟨k1', k2'⟩ := hkey b0 y0 hy0 hf1 hf2
          have hz : arc b = arc b0 := hb'.2.trans hb0'.2.symm
          have e1 : ((ℓ (M.atom b.1) : Fin _) : ℕ) = ((ℓ (M.atom b0.1) : Fin _) : ℕ) :=
            congrArg (fun p => ((p.1 : Fin _) : ℕ)) hz
          have e2 : ((ℓ (M.atom (M.mate b.1)) : Fin _) : ℕ) = ((ℓ (M.atom (M.mate b0.1)) : Fin _) : ℕ) :=
            congrArg (fun p => ((p.2 : Fin _) : ℕ)) hz
          rw [k1, k1'] at e1
          rw [k2, k2'] at e2
          rw [Finset.mem_coe, Finset.mem_filter, Mole.mem_dartsAt]
          exact ⟨ℓ'.injective (Fin.ext e1), ℓ'.injective (Fin.ext e2)⟩
        · intro b hb b' hb' h
          have hb1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2.1
          have hb2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hb')).2.1
          obtain ⟨-, -, -, y, hy, -⟩ := hb1
          obtain ⟨-, -, -, y', hy', -⟩ := hb2
          have hex : ∃ y, SD.od y = b.1 := ⟨y, hy⟩
          have hex' : ∃ y, SD.od y = b'.1 := ⟨y', hy'⟩
          simp only [dif_pos hex, dif_pos hex'] at h
          exact Subtype.ext ((Classical.choose_spec hex).symm.trans ((congrArg SD.od h).trans (Classical.choose_spec hex')))
      rw [card_darts_to M' _ _ hne] at hsub
      omega
  have h3 : ∀ b, ¬ (Rg b ∧ Un b) := fun b h => h.1.1 h.2
  have h5 : (Finset.univ.filter (fun b : B => ¬ Rg b ∧ ¬ Un b)).card ≤ 4 * r := by
    rcases (Finset.univ.filter (fun b : B => ¬ Rg b ∧ ¬ Un b)).eq_empty_or_nonempty with he | ⟨b0, hb0⟩
    · rw [he]; simp
    · have hb0' := (Finset.mem_filter.mp hb0).2
      obtain ⟨y0, hy0⟩ : ∃ y, SD.od y = b0.1 :=
        (SD.od_range _).mpr (fun ⟨i, hi, h1, h2⟩ => hb0'.2 ⟨i, hi, h1, h2⟩)
      let Y1 : Finset D' := Finset.univ.filter
        (fun y => M'.out y = true ∧ ¬ F.Reg (M'.atom y) (M'.atom (M'.mate y)))
      let Y2 : Finset D' := Finset.univ.filter
        (fun y => M'.out y = true ∧ (M'.atom y ∈ Hset ∨ M'.atom (M'.mate y) ∈ Hset))
      have hmap : (Finset.univ.filter (fun b : B => ¬ Rg b ∧ ¬ Un b)).card ≤ (Y1 ∪ Y2).card := by
        refine Finset.card_le_card_of_injOn
          (fun b => if h : ∃ y, SD.od y = b.1 then Classical.choose h else y0) ?_ ?_
        · intro b hb
          have hb' := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
          have hex : ∃ y, SD.od y = b.1 :=
            (SD.od_range _).mpr (fun ⟨i, hi, h1, h2⟩ => hb'.2 ⟨i, hi, h1, h2⟩)
          have hyspec := Classical.choose_spec hex
          simp only [dif_pos hex]
          set y := Classical.choose hex with hyd
          have hout : M'.out y = true := by rw [← SD.od_out, hyspec]; exact b.2
          rw [Finset.mem_coe, Finset.mem_union]
          by_cases hfree : Free (M.atom b.1) ∧ Free (M.atom (M.mate b.1))
          · left
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hout, fun hreg => hb'.1 ?_⟩
            exact ⟨hb'.2, hfree.1, hfree.2, y, hyspec, hreg⟩
          · right
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hout, ?_⟩
            by_cases h1 : Free (M.atom b.1)
            · have h2 : ¬ Free (M.atom (M.mate b.1)) := fun h2 => hfree ⟨h1, h2⟩
              simp only [Free] at h2
              push Not at h2
              obtain ⟨j, hj, hjU⟩ := h2
              right
              apply hH
              refine ⟨j, hj, ?_⟩
              rw [SD.ob_atom, SD.od_mate, hyspec]
              exact SD.cl_unit j hj _ hjU
            · simp only [Free] at h1
              push Not at h1
              obtain ⟨j, hj, hjU⟩ := h1
              left
              apply hH
              refine ⟨j, hj, ?_⟩
              rw [SD.ob_atom, hyspec]
              exact SD.cl_unit j hj _ hjU
        · intro b hb b' hb' h
          have hb1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2.2
          have hb2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hb')).2.2
          obtain ⟨y, hy⟩ : ∃ y, SD.od y = b.1 :=
            (SD.od_range _).mpr (fun ⟨i, hi, h1, h2⟩ => hb1 ⟨i, hi, h1, h2⟩)
          obtain ⟨y', hy'⟩ : ∃ y, SD.od y = b'.1 :=
            (SD.od_range _).mpr (fun ⟨i, hi, h1, h2⟩ => hb2 ⟨i, hi, h1, h2⟩)
          have hex : ∃ y, SD.od y = b.1 := ⟨y, hy⟩
          have hex' : ∃ y, SD.od y = b'.1 := ⟨y', hy'⟩
          simp only [dif_pos hex, dif_pos hex'] at h
          exact Subtype.ext ((Classical.choose_spec hex).symm.trans
            ((congrArg SD.od h).trans (Classical.choose_spec hex')))
      have hY1 : Y1.card ≤ 4 * (M'.atoms.filter (fun a => ∀ i, a ∉ F.atomsOf i)).card + 4 * Fintype.card ι := by
        convert F.card_irrBonds_le hM' hdisj
      have hY2 : Y2.card ≤ 4 * Hset.card := by
        convert card_hinge_darts_le M' hM' hatoms' Hset
      calc (Finset.univ.filter (fun b : B => ¬ Rg b ∧ ¬ Un b)).card ≤ (Y1 ∪ Y2).card := hmap
        _ ≤ Y1.card + Y2.card := Finset.card_union_le _ _
        _ ≤ 4 * r := by rw [hr]; omega
  have hqr : SD.q ≤ r := by
    have h1 : SD.q ≤ Hset.card := by
      let idx : V' → ℕ := fun c => if h : ∃ i, i < SD.q ∧ SD.ob c = SD.rep i then Classical.choose h else 0
      have key : (Finset.range SD.q).card ≤
          (Hset.filter (fun c => ∃ i, i < SD.q ∧ SD.ob c = SD.rep i)).card := by
        refine Finset.card_le_card_of_surjOn idx ?_
        intro i hi
        have hi' := Finset.mem_range.mp (Finset.mem_coe.mp hi)
        obtain ⟨c, hc⟩ := (SD.ob_range (SD.rep i)).mpr (SD.cl_rep hi')
        have hex : ∃ i', i' < SD.q ∧ SD.ob c = SD.rep i' := ⟨i, hi', hc⟩
        refine ⟨c, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hH c hex, hex⟩), ?_⟩
        simp only [idx, dif_pos hex]
        obtain ⟨hs1, hs2⟩ := Classical.choose_spec hex
        by_contra hne
        have e : SD.rep i = SD.rep (Classical.choose hex) := hc.symm.trans hs2
        have hm1 : SD.rep i ∈ SD.U i := SD.rep_mem i hi'
        have hm2 : SD.rep i ∈ SD.U (Classical.choose hex) := by
          rw [e]; exact SD.rep_mem _ hs1
        exact Finset.disjoint_left.mp (SD.U_disj i _ hi' hs1 (Ne.symm hne)) hm1 hm2
      simpa using key.trans (Finset.card_le_card (Finset.filter_subset _ _))
    rw [hr]; omega
  have h4 : (fun x => (Finset.univ.filter (fun b : B => Un b ∧ arc b = x)).card) ∈
      unitFamily (Fintype.card V) (Fintype.card V') r (Fintype.card V - Fintype.card V') := by
    let W' : ℕ → ℕ := fun i => if i < SD.q then W i else 0
    let data : ℕ → UnitData := fun i => if i < SD.q then ⟨cs i, lab i (SD.rep i)⟩ else ⟨[], 0⟩
    have hdW : ∀ i, (data i).W = W' i := by
      intro i
      simp only [data, W']
      split_ifs with h
      · exact (hW i h).1.symm
      · simp [UnitData.W, unitWeight]
    have hdata : ∀ i, i < SD.q → 1 ≤ W' i ∧ data i ∈ unitDataAt (W' i) := by
      intro i hi
      simp only [W', data, if_pos hi]
      refine ⟨(hW i hi).2, ?_⟩
      unfold unitDataAt
      refine Finset.mem_image.mpr ⟨(cs i, lab i (SD.rep i)), Finset.mem_product.mpr ⟨?_, ?_⟩, rfl⟩
      · rw [(hW i hi).1]; exact mem_unitCodes (cs i) (hwf i hi)
      · rw [Finset.mem_range]
        have : lab i (SD.rep i) ∈ (SD.U i).image (lab i) := Finset.mem_image_of_mem _ (SD.rep_mem i hi)
        rw [hlabImg i hi, Finset.mem_range] at this; exact this
    have hsumW : ∑ i ∈ Finset.Ico 0 (0 + SD.q), W' i = ∑ j ∈ Finset.range SD.q, W j := by
      rw [zero_add, ← Finset.range_eq_Ico]
      exact Finset.sum_congr rfl (fun i hi => by simp [W', Finset.mem_range.mp hi])
    have hE : Fintype.card V - Fintype.card V' = ∑ j ∈ Finset.range SD.q, W j := by omega
    have hus : (List.range' 0 SD.q).map data ∈ unitLists (Fintype.card V - Fintype.card V') := by
      have := range'_mem_wlists unitDataAt data W' SD.q hdata SD.q 0 (by omega)
      rw [hsumW] at this
      rw [hE]; exact this
    let p : Fin r → Fin (Fintype.card V) := fun i => ℓ (SD.rep i.1)
    have hmem := mem_unitFamily (n := Fintype.card V) (nsb := Fintype.card V') (r := r) hus p
    have hfun : (fun x : Fin (Fintype.card V) × Fin (Fintype.card V) =>
        (Finset.univ.filter (fun b : B => Un b ∧ arc b = x)).card) =
        fun x => (allArcs (fun i => if h : i < r then ((p ⟨i, h⟩ : Fin (Fintype.card V)) : ℕ) else 0) 0
          (Fintype.card V') ((List.range' 0 SD.q).map data)).count (x.1.1, x.2.1) := by
      funext x
      set P : ℕ → ℕ := fun i => if h : i < r then ((p ⟨i, h⟩ : Fin (Fintype.card V)) : ℕ) else 0 with hP
      rw [count_allArcs P data W' hdW (x.1.1, x.2.1) SD.q 0 (Fintype.card V')]
      have hpart : (Finset.univ.filter (fun b : B => Un b ∧ arc b = x)) =
          (Finset.range SD.q).biUnion (fun i => Finset.univ.filter
            (fun b : B => (M.atom b.1 ∈ SD.U i ∧ M.atom (M.mate b.1) ∈ SD.U i) ∧ arc b = x)) := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_range, Un]
        constructor
        · rintro ⟨⟨i, hi, h1, h2⟩, h3⟩; exact ⟨i, hi, ⟨h1, h2⟩, h3⟩
        · rintro ⟨i, hi, ⟨h1, h2⟩, h3⟩; exact ⟨⟨i, hi, h1, h2⟩, h3⟩
      have hdj : ((Finset.range SD.q : Finset ℕ) : Set ℕ).PairwiseDisjoint (fun i => Finset.univ.filter
            (fun b : B => (M.atom b.1 ∈ SD.U i ∧ M.atom (M.mate b.1) ∈ SD.U i) ∧ arc b = x)) := by
        intro i hi j hj hij
        rw [Function.onFun, Finset.disjoint_left]
        intro b hb1 hb2
        have h1 := (Finset.mem_filter.mp hb1).2.1.1
        have h2 := (Finset.mem_filter.mp hb2).2.1.1
        exact Finset.disjoint_left.mp
          (SD.U_disj i j (Finset.mem_range.mp (Finset.mem_coe.mp hi)) (Finset.mem_range.mp (Finset.mem_coe.mp hj)) hij) h1 h2
      have hterm : ∀ i, i < SD.q → (Finset.univ.filter
            (fun b : B => (M.atom b.1 ∈ SD.U i ∧ M.atom (M.mate b.1) ∈ SD.U i) ∧ arc b = x)).card =
          (globArcs (data i) (P i) (Fintype.card V' + ∑ j ∈ Finset.Ico 0 i, W' j)).count (x.1.1, x.2.1) := by
        intro i hi
        have hir : i < r := lt_of_lt_of_le hi hqr
        have e1 := card_B_filter M (fun d => (M.atom d ∈ SD.U i ∧ M.atom (M.mate d) ∈ SD.U i) ∧
          (ℓ (M.atom d), ℓ (M.atom (M.mate d))) = x)
        have hPi : P i = SD.lab0 ℓ' (SD.rep i) := by
          have h1 : P i = pos (SD.rep i) := by
            simp only [hP, dif_pos hir, p]; exact hℓ (SD.rep i)
          rw [h1]; exact hfixpos _ (SD.cl_rep hi)
        have hbase : ∑ j ∈ Finset.Ico 0 i, W' j = ∑ j ∈ Finset.range i, W j := by
          rw [← Finset.range_eq_Ico]
          exact Finset.sum_congr rfl (fun j hj => by
            have := Finset.mem_range.mp hj
            simp only [W', if_pos (show j < SD.q by omega)])
        have hd : data i = ⟨cs i, lab i (SD.rep i)⟩ := by simp [data, hi]
        have hG : groupArcs M (SD.U i) pos =
            ((unitArcs (cs i) : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)).map
              (fun a => (glob (lab i (SD.rep i)) (SD.lab0 ℓ' (SD.rep i))
                  (Fintype.card V' + ∑ j ∈ Finset.range i, W j) a.1,
                glob (lab i (SD.rep i)) (SD.lab0 ℓ' (SD.rep i))
                  (Fintype.card V' + ∑ j ∈ Finset.range i, W j) a.2)) := by
          rw [groupArcs_congr M (SD.U i)
            (l' := fun v => glob (lab i (SD.rep i)) (SD.lab0 ℓ' (SD.rep i))
              (Fintype.card V' + ∑ j ∈ Finset.range i, W j) (lab i v)) (fun v hv => hunitpos i hi v hv)]
          rw [groupArcs_glob M (SD.U i) (lab i)
            (glob (lab i (SD.rep i)) (SD.lab0 ℓ' (SD.rep i)) (Fintype.card V' + ∑ j ∈ Finset.range i, W j)),
            harcs i hi]
        have hcnt : (globArcs (data i) (P i) (Fintype.card V' + ∑ j ∈ Finset.Ico 0 i, W' j)).count
            (x.1.1, x.2.1) = (groupArcs M (SD.U i) pos).count (x.1.1, x.2.1) := by
          rw [hG, hd, hPi, hbase, ← Multiset.coe_count, globArcs, Multiset.map_coe]
        rw [hcnt, count_groupArcs, e1]
        refine congrArg Finset.card (Finset.filter_congr (fun d _ => ?_))
        have hlab : ∀ v, pos v = ((ℓ v : Fin (Fintype.card V)) : ℕ) := fun v => (hℓ v).symm
        simp only [Molecule.InGroup, hlab, Prod.ext_iff, arc, Fin.ext_iff]
      rw [hpart, Finset.card_biUnion hdj, zero_add, ← Finset.range_eq_Ico]
      exact Finset.sum_congr rfl (fun i hi => hterm i (Finset.mem_range.mp hi))
    rw [hfun]; exact hmem
  obtain ⟨L, hL, hcount⟩ := exists_arcList arc Rg Un
    (unitFamily (Fintype.card V) (Fintype.card V') r (Fintype.card V - Fintype.card V')) h1 h2 h3 h4 h5
  refine ⟨Fintype.card V', by omega, ℓ, L, hL, fun z => ?_⟩
  rw [Fintype.card_subtype]
  exact hcount z

end SpliceData

end WaveTurbulence.ClassCount
