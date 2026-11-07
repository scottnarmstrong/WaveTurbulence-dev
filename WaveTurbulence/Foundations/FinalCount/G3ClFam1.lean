/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3ClDev7
public import WaveTurbulence.Foundations.FinalCount.G3ClAdd
public import WaveTurbulence.Foundations.FinalCount.G3Iso
/-! **FINALCOUNT-G3 (R29 item 4, chain combinator, part 1): transfer lemmas.**  Erasing a cluster `E` from `M` leaves the degrees, the
`e`-counts and the internal connectivity of every other cluster `K'` (disjoint from `E`, no bond between them) unchanged; and the restriction
closure `resAdm Adm E` of an admissibility predicate is compatible with `iterIso`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u v
variable {V : Type u} [DecidableEq V] {D : Type v} [Fintype D] [DecidableEq D] {d : ℕ}

/-- The restriction closure of an admissibility predicate to the darts of `M - E`. -/
def resAdm (Adm : (D → (Fin d → ℤ)) → Prop) (M : Molecule V D) (E : Finset V) :
    (EDartS M E → (Fin d → ℤ)) → Prop :=
  fun κ' => ∃ κ, Adm κ ∧ ∀ x, κ' x = κ x.1

theorem resAdm_intro {Adm : (D → (Fin d → ℤ)) → Prop} {M : Molecule V D} {E : Finset V} {κ : D → (Fin d → ℤ)}
    (h : Adm κ) : resAdm Adm M E (fun x : EDartS M E => κ x.1) := ⟨κ, h, fun _ => rfl⟩

/-- `Res (Res Adm K) K' κ ↔ Res Adm (K ∪ K') (κ ∘ e)` (the iff for `DartIso.countA_eq`). -/
theorem resAdm_iter (Adm : (D → (Fin d → ℤ)) → Prop) (M : Molecule V D) (K₁ K₂ : Finset V)
    (κ' : EDartS M (K₁ ∪ K₂) → (Fin d → ℤ)) :
    resAdm Adm M (K₁ ∪ K₂) κ' ↔
      resAdm (resAdm Adm M K₁) (eraseSet M K₁) K₂ (fun x => κ' ((iterIso M K₁ K₂).e x)) := by
  constructor
  · rintro ⟨κ, hκ, hk⟩
    exact ⟨fun x => κ x.1, resAdm_intro hκ, fun x => hk _⟩
  · rintro ⟨κ₁, ⟨κ, hκ, hk1⟩, hk⟩
    refine ⟨κ, hκ, fun y => ?_⟩
    have this : κ' ((iterIso M K₁ K₂).e ((iterIso M K₁ K₂).symm.e y)) = κ₁ ((iterIso M K₁ K₂).symm.e y).1 :=
      hk ((iterIso M K₁ K₂).symm.e y)
    have h2 : (iterIso M K₁ K₂).e ((iterIso M K₁ K₂).symm.e y) = y := Equiv.apply_symm_apply _ _
    rw [h2] at this
    rw [this, hk1]; rfl

theorem iter_countA (L γ δ C₁ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (M : Molecule V D)
    (K₁ K₂ : Finset V) (P : Finset V → ℝ) :
    (eraseSet (eraseSet M K₁) K₂).countA L γ δ C₁ w (resAdm (resAdm Adm M K₁) (eraseSet M K₁) K₂) P =
      (eraseSet M (K₁ ∪ K₂)).countA L γ δ C₁ w (resAdm Adm M (K₁ ∪ K₂)) P :=
  (iterIso M K₁ K₂).countA_eq L γ δ C₁ w _ _ (fun κ' => resAdm_iter Adm M K₁ K₂ κ') P

section transfer
variable {M : Molecule V D} {E K : Finset V}

theorem multS_eq_zero (hnb : ∀ x, M.atom x ∈ K → M.atom (M.mate x) ∉ E) {a : V} (ha : a ∈ K) :
    multS M E a = 0 := by
  unfold multS
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx
  have : M.atom x = a := by simpa [Molecule.dartsAt] using hx
  exact hnb x (this ▸ ha)

theorem deg_erase_eq (hnb : ∀ x, M.atom x ∈ K → M.atom (M.mate x) ∉ E) (hKE : Disjoint K E) {a : V} (ha : a ∈ K) :
    (eraseSet M E).deg a = M.deg a := by
  have h1 := eraseSet_deg_card M E (Finset.disjoint_left.1 hKE ha)
  rw [multS_eq_zero hnb ha] at h1
  omega

theorem deg_erase_le {a : V} (ha : a ∉ E) : (eraseSet M E).deg a ≤ M.deg a := by
  have := eraseSet_deg_card M E ha; omega

theorem eDart_erase_eq (hnb : ∀ x, M.atom x ∈ K → M.atom (M.mate x) ∉ E) (hKE : Disjoint K E) :
    eDart (eraseSet M E) K = eDart M K := by
  unfold eDart
  refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx
  · intro x _ y _ e; exact Subtype.ext e
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have h1 : M.atom x ∉ E := Finset.disjoint_left.1 hKE hx.1
    exact ⟨⟨x, h1, hnb x hx.1⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hx, rfl⟩

theorem induced_sc {a b : V} (h : (eraseSet M (M.atoms \ K)).SameComponent a b) : M.SameComponent a b := by
  unfold Molecule.SameComponent at h ⊢
  refine Relation.EqvGen.mono (fun u w hu => ?_) _ _ h
  obtain ⟨y, h1, h2⟩ := hu
  exact ⟨y.1, h1, h2⟩

theorem induced_transfer (hKE : Disjoint K E) {a b : V}
    (h : (eraseSet M (M.atoms \ K)).SameComponent a b) :
    (eraseSet (eraseSet M E) ((eraseSet M E).atoms \ K)).SameComponent a b := by
  unfold Molecule.SameComponent at h ⊢
  refine Relation.EqvGen.mono (fun u w hu => ?_) _ _ h
  obtain ⟨y, h1, h2⟩ := hu
  have hk1 : M.atom y.1 ∈ K := by
    by_contra hn
    exact y.2.1 (Finset.mem_sdiff.2 ⟨M.atom_mem _, hn⟩)
  have hk2 : M.atom (M.mate y.1) ∈ K := by
    by_contra hn
    exact y.2.2 (Finset.mem_sdiff.2 ⟨M.atom_mem _, hn⟩)
  have e1 : M.atom y.1 ∉ E := Finset.disjoint_left.1 hKE hk1
  have e2 : M.atom (M.mate y.1) ∉ E := Finset.disjoint_left.1 hKE hk2
  refine ⟨⟨⟨y.1, e1, e2⟩, ?_, ?_⟩, h1, h2⟩
  · intro hh
    exact (Finset.mem_sdiff.1 hh).2 hk1
  · intro hh
    exact (Finset.mem_sdiff.1 hh).2 hk2

end transfer
end WaveTurbulence.FinalCountG3
