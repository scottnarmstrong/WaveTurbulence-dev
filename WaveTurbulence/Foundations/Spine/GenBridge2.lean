/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.GenBridge1
import Mathlib.Tactic
/-! The literal class time domain on `ι → ℝ` agrees a.e. with the product model `Mset` (limits
`loF`, `hiF` from the `X`-neighbours; `Ioc` and `≤` versus `Icc` and `<` differ on null sets). -/
@[expose] public section
open MeasureTheory Set Finset Function
open scoped ENNReal
namespace WaveTurbulence.Ladder
open scoped Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k m : ℕ}

/-- The limits of a `Y` vertex from its `X` neighbours. -/
noncomputable def loF (lsY : Fin m → ℝ) (LB : Fin m → Finset (Fin k)) (tx : Fin k → ℝ) (j : Fin m) : ℝ :=
  (LB j).fold max (lsY j) tx

noncomputable def hiF (lsY capY : Fin m → ℝ) (UB : Fin m → Finset (Fin k)) (tx : Fin k → ℝ) (j : Fin m) : ℝ :=
  (UB j).fold min (min (lsY j + 1) (capY j)) tx

theorem le_loF (lsY : Fin m → ℝ) (LB : Fin m → Finset (Fin k)) (tx : Fin k → ℝ) (j : Fin m) :
    lsY j ≤ loF lsY LB tx j := by
  unfold loF
  rw [Finset.le_fold_max]; exact Or.inl le_rfl

theorem hiF_le (lsY capY : Fin m → ℝ) (UB : Fin m → Finset (Fin k)) (tx : Fin k → ℝ) (j : Fin m) :
    hiF lsY capY UB tx j ≤ lsY j + 1 := by
  unfold hiF
  rw [Finset.fold_min_le]; exact Or.inl (min_le_left _ _)

theorem loF_lt_iff (lsY : Fin m → ℝ) (LB : Fin m → Finset (Fin k)) (tx : Fin k → ℝ) (j : Fin m) (y : ℝ) :
    loF lsY LB tx j < y ↔ lsY j < y ∧ ∀ i ∈ LB j, tx i < y := by
  unfold loF; rw [Finset.fold_max_lt]

theorem le_hiF_iff (lsY capY : Fin m → ℝ) (UB : Fin m → Finset (Fin k)) (tx : Fin k → ℝ) (j : Fin m) (y : ℝ) :
    y ≤ hiF lsY capY UB tx j ↔ (y ≤ lsY j + 1 ∧ y ≤ capY j) ∧ ∀ i ∈ UB j, y ≤ tx i := by
  unfold hiF; rw [Finset.le_fold_min, le_min_iff]

/-- The class time domain on `ι → ℝ`. -/
def OmegaC (ls cap : ι → ℝ) (lt le : ι → ι → Prop) (xv : Fin k → ι) (Rv : Set (Fin k → ℝ)) :
    Set (ι → ℝ) :=
  {t | (∀ v, t v ∈ Icc (ls v) (ls v + 1)) ∧ (∀ v, t v < cap v) ∧ (∀ a b, lt a b → t a < t b) ∧
    (∀ a b, le a b → t a ≤ t b) ∧ (fun i => t (xv i)) ∈ Rv}

/-- The `X`-region of the model. -/
def Rmod (ls cap : ι → ℝ) (lt le : ι → ι → Prop) (xv : Fin k → ι) (Rv : Set (Fin k → ℝ)) :
    Set (Fin k → ℝ) :=
  Rv ∩ {tx | (∀ i, tx i ∈ Icc (ls (xv i)) (ls (xv i) + 1)) ∧ (∀ i, tx i < cap (xv i)) ∧
    (∀ i i', lt (xv i) (xv i') → tx i < tx i') ∧ (∀ i i', le (xv i) (xv i') → tx i ≤ tx i')}

noncomputable def LBf (lt le : ι → ι → Prop) (xv : Fin k → ι) (yv : Fin m → ι) (j : Fin m) :
    Finset (Fin k) := univ.filter (fun i => lt (xv i) (yv j) ∨ le (xv i) (yv j))

noncomputable def UBf (lt le : ι → ι → Prop) (xv : Fin k → ι) (yv : Fin m → ι) (j : Fin m) :
    Finset (Fin k) := univ.filter (fun i => lt (yv j) (xv i) ∨ le (yv j) (xv i))

/-- The product model domain. -/
def Mset (ls cap : ι → ℝ) (lt le : ι → ι → Prop) (xv : Fin k → ι) (yv : Fin m → ι)
    (Rv : Set (Fin k → ℝ)) (par : Par m) : Set ((Fin k → ℝ) × (Fin m → ℝ)) :=
  {p | p.1 ∈ Rmod ls cap lt le xv Rv ∧
    (∀ j, p.2 j ∈ Ioc (loF (fun j => ls (yv j)) (LBf lt le xv yv) p.1 j)
      (hiF (fun j => ls (yv j)) (fun j => cap (yv j)) (UBf lt le xv yv) p.1 j)) ∧
    ∀ j j', par j = some j' → p.2 j < p.2 j'}

/-- The null set of boundary coincidences. -/
def NullBd (ls cap : ι → ℝ) : Set (ι → ℝ) :=
  (⋃ v, {t | t v = ls v}) ∪ (⋃ v, {t | t v = cap v}) ∪ ⋃ a, ⋃ b, ⋃ (_ : a ≠ b), {t | t a = t b}

theorem volume_NullBd (ls cap : ι → ℝ) : volume (NullBd ls cap) = 0 := by
  unfold NullBd
  refine measure_union_null (measure_union_null (measure_iUnion_null (fun v => volume_eval_eq v _))
    (measure_iUnion_null (fun v => volume_eval_eq v _))) ?_
  refine measure_iUnion_null (fun a => measure_iUnion_null (fun b => measure_iUnion_null
    (fun hab => volume_diag_eq hab)))

section Equiv
variable (e : ι ≃ Fin k ⊕ Fin m) (ls cap : ι → ℝ) (lt le : ι → ι → Prop) (Rv : Set (Fin k → ℝ))
  (par : Par m)

theorem cases_v (v : ι) : (∃ i, v = e.symm (Sum.inl i)) ∨ ∃ j, v = e.symm (Sum.inr j) := by
  rcases h : e v with i | j
  · exact Or.inl ⟨i, by rw [← h]; simp⟩
  · exact Or.inr ⟨j, by rw [← h]; simp⟩

theorem mem_iff_of_not_null
    (hpar : ∀ j j', par j = some j' ↔ lt (e.symm (Sum.inr j)) (e.symm (Sum.inr j')))
    (hle : ∀ j j', ¬ le (e.symm (Sum.inr j)) (e.symm (Sum.inr j')))
    (t : ι → ℝ) (ht : t ∉ NullBd ls cap) :
    t ∈ OmegaC ls cap lt le (fun i => e.symm (Sum.inl i)) Rv ↔
      Th e t ∈ Mset ls cap lt le (fun i => e.symm (Sum.inl i)) (fun j => e.symm (Sum.inr j)) Rv par := by
  have hne1 : ∀ v, t v ≠ ls v := by
    intro v hv; apply ht; left; left; simp only [mem_iUnion]; exact ⟨v, hv⟩
  have hne3 : ∀ v, t v ≠ cap v := by
    intro v hv; apply ht; left; right; simp only [mem_iUnion]; exact ⟨v, hv⟩
  have hne2 : ∀ a b, a ≠ b → t a ≠ t b := by
    intro a b hab hv; apply ht; right; simp only [mem_iUnion]; exact ⟨a, b, hab, hv⟩
  have hxy : ∀ i j, e.symm (Sum.inl i) ≠ e.symm (Sum.inr j) := fun i j h => by
    have := e.symm.injective h; simp at this
  rw [Th_apply]
  constructor
  · rintro ⟨h1, hc, h2, h3, h4⟩
    refine ⟨⟨h4, fun i => h1 _, fun i => hc _, fun i i' h => h2 _ _ h, fun i i' h => h3 _ _ h⟩, fun j => ⟨?_, ?_⟩, ?_⟩
    · show loF _ _ _ j < t (e.symm (Sum.inr j))
      rw [loF_lt_iff]
      refine ⟨lt_of_le_of_ne (h1 _).1 (Ne.symm (hne1 _)), fun i hi => ?_⟩
      simp only [LBf, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rcases hi with hi | hi
      · exact h2 _ _ hi
      · exact lt_of_le_of_ne (h3 _ _ hi) (hne2 _ _ (hxy i j))
    · show t (e.symm (Sum.inr j)) ≤ hiF _ _ _ _ j
      rw [le_hiF_iff]
      refine ⟨⟨(h1 _).2, (hc _).le⟩, fun i hi => ?_⟩
      simp only [UBf, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rcases hi with hi | hi
      · exact (h2 _ _ hi).le
      · exact h3 _ _ hi
    · intro j j' hj
      exact h2 _ _ ((hpar j j').1 hj)
  · rintro ⟨⟨hR1, hRl, hRc, hRlt, hRle⟩, hY, hP⟩
    have hlayer : ∀ v, t v ∈ Icc (ls v) (ls v + 1) := by
      intro v
      rcases cases_v e v with ⟨i, rfl⟩ | ⟨j, rfl⟩
      · exact hRl i
      · have := hY j
        have h1 := le_loF (fun j => ls (e.symm (Sum.inr j))) (LBf lt le (fun i => e.symm (Sum.inl i))
          (fun j => e.symm (Sum.inr j))) (fun i => t (e.symm (Sum.inl i))) j
        have h2 := hiF_le (fun j => ls (e.symm (Sum.inr j))) (fun j => cap (e.symm (Sum.inr j))) (UBf lt le (fun i => e.symm (Sum.inl i))
          (fun j => e.symm (Sum.inr j))) (fun i => t (e.symm (Sum.inl i))) j
        exact ⟨h1.trans this.1.le, this.2.trans h2⟩
    have hcap : ∀ v, t v < cap v := by
      intro v
      rcases cases_v e v with ⟨i, rfl⟩ | ⟨j, rfl⟩
      · exact hRc i
      · have := hY j
        have h2 := ((le_hiF_iff _ _ _ _ _ _).1 this.2).1.2
        exact lt_of_le_of_ne h2 (hne3 _)
    refine ⟨hlayer, hcap, ?_, ?_, hR1⟩
    · intro a b hab
      rcases cases_v e a with ⟨i, rfl⟩ | ⟨j, rfl⟩ <;> rcases cases_v e b with ⟨i', rfl⟩ | ⟨j', rfl⟩
      · exact hRlt i i' hab
      · have := ((loF_lt_iff _ _ _ j' _).1 (hY j').1).2 i
        simpa [LBf, hab] using this
      · have := ((le_hiF_iff _ _ _ _ j _).1 (hY j).2).2 i'
        have h' : i' ∈ UBf lt le (fun i => e.symm (Sum.inl i)) (fun j => e.symm (Sum.inr j)) j := by
          simp [UBf, hab]
        exact lt_of_le_of_ne (this h') (hne2 _ _ (hxy i' j).symm)
      · exact hP j j' ((hpar j j').2 hab)
    · intro a b hab
      rcases cases_v e a with ⟨i, rfl⟩ | ⟨j, rfl⟩ <;> rcases cases_v e b with ⟨i', rfl⟩ | ⟨j', rfl⟩
      · exact hRle i i' hab
      · have := ((loF_lt_iff _ _ _ j' _).1 (hY j').1).2 i
        exact (by simpa [LBf, hab] using this : _ < _).le
      · have := ((le_hiF_iff _ _ _ _ j _).1 (hY j).2).2 i'
        exact this (by simp [UBf, hab])
      · exact absurd hab (hle j j')

theorem ae_eq_Mset
    (hpar : ∀ j j', par j = some j' ↔ lt (e.symm (Sum.inr j)) (e.symm (Sum.inr j')))
    (hle : ∀ j j', ¬ le (e.symm (Sum.inr j)) (e.symm (Sum.inr j'))) :
    OmegaC ls cap lt le (fun i => e.symm (Sum.inl i)) Rv =ᵐ[volume]
      (Th e) ⁻¹' Mset ls cap lt le (fun i => e.symm (Sum.inl i)) (fun j => e.symm (Sum.inr j)) Rv par := by
  have : ∀ᵐ t ∂(volume : Measure (ι → ℝ)), t ∉ NullBd ls cap := by
    rw [ae_iff]; simpa using volume_NullBd ls cap
  filter_upwards [this] with t ht
  exact propext (mem_iff_of_not_null e ls cap lt le Rv par hpar hle t ht)

end Equiv
end WaveTurbulence.Ladder
