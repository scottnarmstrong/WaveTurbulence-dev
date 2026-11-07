/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.G8R.Prop104Two
public import WaveTurbulence.Foundations.CountLemmas.A23HalfReparam
import Mathlib.Tactic

/-! # Theorem A, Step 4: `T` minus one bond (case-4 note Step 4)

`T` is the triangle of three double bonds. Remove one bond `ℓ*`, between `p` and `q`, and let `r` be the third atom.
In `T ∖ ℓ*`, `p` and `q` have degree 3 and are joined by one bond `m`; each has two bonds to `r`. The vectors of the
five bonds solve the atom systems at `p` and `q`, a system `{(1,2,3),(1,4,5)}` with the shared bond `m`, and no tuple
has three equal signs (in/out caps). `system12345_bound` (DH23 Lemma A.3(4), `γ > 1/2`, the A23-HALF packet) gives
`#{decorations} ≤ C δ⁻² L^{3(d−γ) − γ₀ − κ(γ)}`. With `χ(T ∖ ℓ*) = 3` and no ladder cell, `𝔄(T ∖ ℓ*) ≤ C C₁⁻³
δ^{−1/2} L^{−γ₀−κ(γ)}`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The unit sign of a dart. -/
def dartUnit (M : Molecule V D) (x : D) : ℤˣ := if M.out x = true then 1 else -1

omit [DecidableEq V] [Fintype D] [DecidableEq D] in
theorem dartSign_eq_unit (M : Molecule V D) (x : D) : M.dartSign x = ((dartUnit M x : ℤ) : ℝ) := by
  unfold Molecule.dartSign dartUnit
  split_ifs <;> simp

/-- **The darts of `T ∖ ℓ*` at the two ends `p, q` of `ℓ*`**: `x₀` (the other bond `p – q`), `x₁, x₂` (to `r`) at
`p`; `mate x₀`, `x₃, x₄` (to `r`) at `q`; every dart at `r` goes to `p` or `q`. -/
theorem tMinus_darts {M : Molecule V D} (hT : IsT M) (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z)) (e : D) :
    ∃ (x₀ x₁ x₂ x₃ x₄ : MoleProp.WithoutBondDart M e),
      (MoleProp.eraseBond M e).dartsAt (M.atom e) = {x₀, x₁, x₂} ∧ x₀ ∉ ({x₁, x₂} : Finset _) ∧ x₁ ≠ x₂ ∧
      (MoleProp.eraseBond M e).dartsAt (M.atom (M.mate e)) = {(MoleProp.eraseBond M e).mate x₀, x₃, x₄} ∧
      (MoleProp.eraseBond M e).mate x₀ ∉ ({x₃, x₄} : Finset _) ∧ x₃ ≠ x₄ ∧
      (∀ z : MoleProp.WithoutBondDart M e, M.atom z.val ≠ M.atom e → M.atom z.val ≠ M.atom (M.mate e) →
        M.atom (M.mate z.val) = M.atom e ∨ M.atom (M.mate z.val) = M.atom (M.mate e)) := by
  classical
  obtain ⟨a, b, c, hab, hbc, hac, hs, h1, h2, h3, _⟩ := hT
  have hpq : M.atom e ≠ M.atom (M.mate e) := hloop e
  have hp : M.atom e ∈ M.atoms := M.atom_mem e
  have hq : M.atom (M.mate e) ∈ M.atoms := M.atom_mem _
  have hbb : ∀ u w, u ∈ M.atoms → w ∈ M.atoms → u ≠ w → M.bondsBetween u w = 2 := by
    intro u w hu hw huw
    rw [hs] at hu hw
    simp only [mem_insert, mem_singleton] at hu hw
    rcases hu with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
      first | exact absurd rfl huw | assumption | (rw [bondsBetween_symm]; assumption)
  have hc3 : M.atoms.card = 3 := by
    rw [hs, card_insert_of_notMem (by simp [hab, hac]), card_insert_of_notMem (by simp [hbc]), card_singleton]
  -- the third atom
  obtain ⟨r, hr, hrp, hrq⟩ : ∃ r ∈ M.atoms, r ≠ M.atom e ∧ r ≠ M.atom (M.mate e) := by
    by_contra h
    push Not at h
    have hsub : M.atoms ⊆ {M.atom e, M.atom (M.mate e)} := fun x hx => by
      by_cases hxp : x = M.atom e
      · rw [hxp]; exact mem_insert_self _ _
      · rw [h x hx hxp]; exact mem_insert_of_mem (mem_singleton_self _)
    have := card_le_card hsub
    rw [card_pair hpq] at this
    omega
  have hatoms : ∀ x ∈ M.atoms, x = M.atom e ∨ x = M.atom (M.mate e) ∨ x = r := by
    intro x hx
    by_contra h
    push Not at h
    have hsub : ({x, M.atom e, M.atom (M.mate e), r} : Finset V) ⊆ M.atoms := by
      intro y hy; simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> assumption
    have := card_le_card hsub
    rw [card_insert_of_notMem (by simp [h.1, h.2.1, h.2.2]), card_insert_of_notMem (by simp [hpq, hrp.symm]),
      card_pair hrq.symm] at this
    omega
  -- bond counts in `𝕄 ∖ ℓ*`
  have hends : M.ends e = s(M.atom e, M.atom (M.mate e)) := rfl
  have hNpq : (MoleProp.eraseBond M e).bondsBetween (M.atom e) (M.atom (M.mate e)) = 1 := by
    have := bondsBetween_eraseBond_of_ends M e hends (M.atom e) (M.atom (M.mate e))
    rw [ite_of_pos rfl, hbb _ _ hp hq hpq] at this; omega
  have hNpr : (MoleProp.eraseBond M e).bondsBetween (M.atom e) r = 2 := by
    rw [bondsBetween_eraseBond_of_ne M e (by
      rw [hends]; intro h'; rcases Sym2.eq_iff.mp h' with ⟨_, h⟩ | ⟨h, _⟩
      · exact hrq h.symm
      · exact hrp h.symm)]
    exact hbb _ _ hp hr hrp.symm
  have hNqr : (MoleProp.eraseBond M e).bondsBetween (M.atom (M.mate e)) r = 2 := by
    rw [bondsBetween_eraseBond_of_ne M e (by
      rw [hends]; intro h'; rcases Sym2.eq_iff.mp h' with ⟨h, _⟩ | ⟨h, _⟩
      · exact hpq h
      · exact hrp h.symm)]
    exact hbb _ _ hq hr hrq.symm
  set N := MoleProp.eraseBond M e
  have hcd := fun {u w : V} (huw : u ≠ w) => card_darts_between N huw
  obtain ⟨x₀, hx₀⟩ := card_eq_one.mp ((hcd hpq).trans hNpq)
  obtain ⟨x₁, x₂, hx12, hx₁₂⟩ := card_eq_two.mp ((hcd hrp.symm).trans hNpr)
  obtain ⟨x₃, x₄, hx34, hx₃₄⟩ := card_eq_two.mp ((hcd hrq.symm).trans hNqr)
  have hqp : (univ.filter fun x => N.atom x = M.atom (M.mate e) ∧ N.atom (N.mate x) = M.atom e) = {N.mate x₀} := by
    have hcard := (hcd hpq.symm).trans
      (show N.bondsBetween (M.atom (M.mate e)) (M.atom e) = 1 by rw [bondsBetween_symm]; exact hNpq)
    obtain ⟨y, hy⟩ := card_eq_one.mp hcard
    have hmem : N.mate x₀ ∈ univ.filter fun x => N.atom x = M.atom (M.mate e) ∧ N.atom (N.mate x) = M.atom e := by
      have h0 : x₀ ∈ univ.filter fun x => N.atom x = M.atom e ∧ N.atom (N.mate x) = M.atom (M.mate e) := by
        rw [hx₀]; exact mem_singleton_self _
      obtain ⟨_, h01, h02⟩ := mem_filter.mp h0
      exact mem_filter.mpr ⟨mem_univ _, h02, by rw [N.mate_mate]; exact h01⟩
    rw [hy] at hmem ⊢
    rw [mem_singleton.mp hmem]
  -- the darts at an end of `ℓ*` split by the other end
  have hsplit : ∀ u, u = M.atom e ∨ u = M.atom (M.mate e) → ∀ z : MoleProp.WithoutBondDart M e, N.atom z = u →
      N.atom (N.mate z) ≠ u ∧ (N.atom (N.mate z) = M.atom e ∨ N.atom (N.mate z) = M.atom (M.mate e) ∨
        N.atom (N.mate z) = r) := fun u _ z hz =>
    ⟨fun h => hloop z.val (hz.trans h.symm), hatoms _ (M.atom_mem _)⟩
  have hmemf : ∀ (u w : V) (z : MoleProp.WithoutBondDart M e), N.atom z = u → N.atom (N.mate z) = w →
      z ∈ univ.filter fun x => N.atom x = u ∧ N.atom (N.mate x) = w := fun u w z h1 h2 =>
    mem_filter.mpr ⟨mem_univ _, h1, h2⟩
  have hdiff : ∀ {u w w' : V} (y y' : MoleProp.WithoutBondDart M e), w ≠ w' →
      y ∈ (univ.filter fun x => N.atom x = u ∧ N.atom (N.mate x) = w) →
      y' ∈ (univ.filter fun x => N.atom x = u ∧ N.atom (N.mate x) = w') → y ≠ y' := by
    intro u w w' y y' hww hy hy' h
    rw [h] at hy
    exact hww ((mem_filter.mp hy).2.2.symm.trans (mem_filter.mp hy').2.2)
  have m0 : x₀ ∈ univ.filter fun x => N.atom x = M.atom e ∧ N.atom (N.mate x) = M.atom (M.mate e) := by
    rw [hx₀]; exact mem_singleton_self _
  have m1 : x₁ ∈ univ.filter fun x => N.atom x = M.atom e ∧ N.atom (N.mate x) = r := by
    rw [hx₁₂]; exact mem_insert_self _ _
  have m2 : x₂ ∈ univ.filter fun x => N.atom x = M.atom e ∧ N.atom (N.mate x) = r := by
    rw [hx₁₂]; exact mem_insert_of_mem (mem_singleton_self _)
  have m0' : N.mate x₀ ∈ univ.filter fun x => N.atom x = M.atom (M.mate e) ∧ N.atom (N.mate x) = M.atom e := by
    rw [hqp]; exact mem_singleton_self _
  have m3 : x₃ ∈ univ.filter fun x => N.atom x = M.atom (M.mate e) ∧ N.atom (N.mate x) = r := by
    rw [hx₃₄]; exact mem_insert_self _ _
  have m4 : x₄ ∈ univ.filter fun x => N.atom x = M.atom (M.mate e) ∧ N.atom (N.mate x) = r := by
    rw [hx₃₄]; exact mem_insert_of_mem (mem_singleton_self _)
  have hx01 : x₀ ≠ x₁ ∧ x₀ ≠ x₂ := ⟨hdiff _ _ (Ne.symm hrq) m0 m1, hdiff _ _ (Ne.symm hrq) m0 m2⟩
  have hm34 : N.mate x₀ ≠ x₃ ∧ N.mate x₀ ≠ x₄ := ⟨hdiff _ _ (Ne.symm hrp) m0' m3, hdiff _ _ (Ne.symm hrp) m0' m4⟩
  refine ⟨x₀, x₁, x₂, x₃, x₄, ?_, by simp [hx01.1, hx01.2], hx12, ?_, by simp [hm34.1, hm34.2], hx34, ?_⟩
  · ext z
    simp only [Molecule.dartsAt, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · intro hz
      obtain ⟨hne, h | h | h⟩ := hsplit _ (Or.inl rfl) z hz
      · exact absurd (h ▸ rfl) hne
      · left; exact mem_singleton.mp (hx₀ ▸ hmemf _ _ z hz h)
      · right; have := hx₁₂ ▸ hmemf _ _ z hz h; simpa using this
    · rintro (h | h | h) <;> rw [h]
      · exact (mem_filter.mp m0).2.1
      · exact (mem_filter.mp m1).2.1
      · exact (mem_filter.mp m2).2.1
  · ext z
    simp only [Molecule.dartsAt, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · intro hz
      obtain ⟨hne, h | h | h⟩ := hsplit _ (Or.inr rfl) z hz
      · left; exact mem_singleton.mp (hqp ▸ hmemf _ _ z hz h)
      · exact absurd (h ▸ rfl) hne
      · right; have := hx₃₄ ▸ hmemf _ _ z hz h; simpa using this
    · rintro (h | h | h) <;> rw [h]
      · exact (mem_filter.mp m0').2.1
      · exact (mem_filter.mp m3).2.1
      · exact (mem_filter.mp m4).2.1
  · intro z hzp hzq
    have hzr : M.atom z.val = r := by
      rcases hatoms _ (M.atom_mem z.val) with h | h | h
      · exact absurd h hzp
      · exact absurd h hzq
      · exact h
    rcases hatoms _ (M.atom_mem (M.mate z.val)) with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (hzr.trans h.symm) (hloop z.val)

omit [DecidableEq V] [Fintype D] [DecidableEq D] in
/-- A decoration's conservation sum at three darts, in integer coordinates. -/
theorem lattice_sum_three {N : Molecule V D} {d : ℕ} (L : ℝ) (κ : D → (Fin d → ℤ)) (y₀ y₁ y₂ : D) :
    N.dartSign y₀ • Molecule.kvec L (0 : Mom d) κ y₀ + (N.dartSign y₁ • Molecule.kvec L (0 : Mom d) κ y₁ +
      N.dartSign y₂ • Molecule.kvec L (0 : Mom d) κ y₂) =
      latticePoint L ((dartUnit N y₀ : ℤ) • κ y₀ + (dartUnit N y₁ : ℤ) • κ y₁ + (dartUnit N y₂ : ℤ) • κ y₂) := by
  have hadd : ∀ m n : Fin d → ℤ, latticePoint L (m + n) = latticePoint L m + latticePoint L n :=
    fun m n => (MoleProp.latticePointHom L).map_add m n
  simp only [Molecule.kvec, zero_add, dartSign_eq_unit]
  rw [hadd, hadd, MoleProp.latticePoint_zsmul, MoleProp.latticePoint_zsmul, MoleProp.latticePoint_zsmul]
  simp only [Int.cast_smul_eq_zsmul]
  abel

/-- No three equal unit signs at an atom with in/out caps. -/
theorem not_three_equal_units {N : Molecule V D} {v : V} (hcap : N.outdeg v ≤ 2 ∧ N.indeg v ≤ 2)
    {y₀ y₁ y₂ : D} (hd : N.dartsAt v = {y₀, y₁, y₂}) (h0 : y₀ ∉ ({y₁, y₂} : Finset D)) (h12 : y₁ ≠ y₂) :
    ¬ (![dartUnit N y₀, dartUnit N y₁, dartUnit N y₂] 0 = ![dartUnit N y₀, dartUnit N y₁, dartUnit N y₂] 1 ∧
      ![dartUnit N y₀, dartUnit N y₁, dartUnit N y₂] 1 = ![dartUnit N y₀, dartUnit N y₁, dartUnit N y₂] 2) := by
  classical
  rintro ⟨h01, h12'⟩
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h01 h12'
  have h3 : ({y₀, y₁, y₂} : Finset D).card = 3 := by
    rw [card_insert_of_notMem h0, card_pair h12]
  unfold dartUnit at h01 h12'
  by_cases ho : N.out y₀ = true
  · have ho1 : N.out y₁ = true := by by_contra h; rw [ite_of_pos ho, ite_of_not h] at h01; exact absurd h01 (by decide)
    have ho2 : N.out y₂ = true := by
      by_contra h; rw [ite_of_pos ho1, ite_of_not h] at h12'; exact absurd h12' (by decide)
    have : ((N.dartsAt v).filter fun x => N.out x = true) = N.dartsAt v := by
      rw [filter_eq_self, hd]; intro x hx; simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have hc := hcap.1
    unfold Molecule.outdeg at hc
    rw [this, hd, h3] at hc; omega
  · have ho1 : N.out y₁ = false := by
      by_contra h; simp only [Bool.not_eq_false] at h; rw [ite_of_not ho, ite_of_pos h] at h01
      exact absurd h01 (by decide)
    have ho2 : N.out y₂ = false := by
      by_contra h; simp only [Bool.not_eq_false] at h
      rw [ite_of_not (by simp [ho1]), ite_of_pos h] at h12'; exact absurd h12' (by decide)
    have ho0 : N.out y₀ = false := by simpa using ho
    have : ((N.dartsAt v).filter fun x => N.out x = false) = N.dartsAt v := by
      rw [filter_eq_self, hd]; intro x hx; simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have hc := hcap.2
    unfold Molecule.indeg at hc
    rw [this, hd, h3] at hc; omega

/-- **The decorations of `T ∖ ℓ*` are counted by DH23 Lemma A.3(4), `γ > 1/2`** (`system12345_bound`). -/
theorem tMinus_countE (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, ∀ L ≥ L₀,
      ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D), IsT M →
        (∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) → (∀ z, M.atom z ≠ M.atom (M.mate z)) → ∀ (e : D)
        (Adm : (MoleProp.WithoutBondDart M e → (Fin d → ℤ)) → Prop),
        (MoleProp.countEFree (MoleProp.eraseBond M e) L γ δ (0 : Mom d) Adm : ℝ≥0∞) ≤
          ENNReal.ofReal (C * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ) - (1 - γ) - CountLemmas.kappaHalf γ)) := by
  obtain ⟨C, hC, hb⟩ := CountLemmas.system12345_bound d hd γ hγ
  refine ⟨C, hC, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀⟩ := hb δ hδ
  refine ⟨max L₀ 1, fun L hL V D _ _ _ M hT hcap hloop e Adm => ?_⟩
  classical
  have hLp : 0 < L := zero_lt_one.trans_le ((le_max_right _ _).trans hL)
  have hLL : L ≥ L₀ := (le_max_left _ _).trans hL
  set X := C * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ) - (1 - γ) - CountLemmas.kappaHalf γ) with hX
  have hX0 : 0 ≤ X := by positivity
  obtain ⟨x₀, x₁, x₂, x₃, x₄, hP, hP0, hP12, hQ, hQ0, hQ34, hR⟩ := tMinus_darts hT hloop e
  have hcapN := caps_eraseBond M e hcap
  have hpN : M.atom e ∈ (MoleProp.eraseBond M e).atoms := M.atom_mem e
  have hqN : M.atom (M.mate e) ∈ (MoleProp.eraseBond M e).atoms := M.atom_mem _
  have hinjL : Function.Injective (fun n : Fin d → ℤ => latticePoint L n) := by
    intro n n' h
    exact MoleProp.latticePointHom_injective hLp.ne' (by simpa using h)
  have key : ∀ (c : V → Mom d) (β : V → ℝ) (k0 : MoleProp.WithoutBondDart M e → Mom d),
      {κ | (MoleProp.eraseBond M e).IsDecoration L 0 c κ ∧
        (MoleProp.eraseBond M e).IsRestricted L γ δ 0 β k0 κ ∧ Adm κ}.encard ≤ (⌊X⌋₊ : ℕ∞) := by
    intro c β k0
    set N := MoleProp.eraseBond M e
    set A := {κ | N.IsDecoration L 0 c κ ∧ N.IsRestricted L γ δ 0 β k0 κ ∧ Adm κ}
    by_cases hne : A.Nonempty
    swap
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, Set.encard_empty]; exact bot_le
    obtain ⟨κ₀, hκ₀⟩ := hne
    let f : (MoleProp.WithoutBondDart M e → (Fin d → ℤ)) → (Fin 5 → Fin d → ℤ) :=
      fun κ => ![κ x₀, κ x₁, κ x₂, κ x₃, κ x₄]
    let a : Fin 5 → Mom d := ![k0 x₀, k0 x₁, k0 x₂, k0 x₃, k0 x₄]
    let εA : Fin 3 → ℤˣ := ![dartUnit N x₀, dartUnit N x₁, dartUnit N x₂]
    let εB : Fin 3 → ℤˣ := ![dartUnit N (N.mate x₀), dartUnit N x₃, dartUnit N x₄]
    let sA : (MoleProp.WithoutBondDart M e → (Fin d → ℤ)) → (Fin d → ℤ) := fun κ =>
      (dartUnit N x₀ : ℤ) • κ x₀ + (dartUnit N x₁ : ℤ) • κ x₁ + (dartUnit N x₂ : ℤ) • κ x₂
    let sB : (MoleProp.WithoutBondDart M e → (Fin d → ℤ)) → (Fin d → ℤ) := fun κ =>
      (dartUnit N (N.mate x₀) : ℤ) • κ (N.mate x₀) + (dartUnit N x₃ : ℤ) • κ x₃ + (dartUnit N x₄ : ℤ) • κ x₄
    let S := CountLemmas.system12345Set L a εA εB (sA κ₀) (sB κ₀) (β (M.atom e)) (β (M.atom (M.mate e)))
      (δ⁻¹ * L ^ (-2 * γ))
    have hconsP : ∀ κ ∈ A, latticePoint L (sA κ) = c (M.atom e) := by
      intro κ hκ
      have h := hκ.1.2 (M.atom e) hpN
      rw [hP, sum_insert hP0, sum_insert (by simpa using hP12), sum_singleton, lattice_sum_three] at h
      exact h
    have hconsQ : ∀ κ ∈ A, latticePoint L (sB κ) = c (M.atom (M.mate e)) := by
      intro κ hκ
      have h := hκ.1.2 (M.atom (M.mate e)) hqN
      rw [hQ, sum_insert hQ0, sum_insert (by simpa using hQ34), sum_singleton, lattice_sum_three] at h
      exact h
    have hwinP : ∀ κ ∈ A, |(N.dartSign x₀ * ‖Molecule.kvec L (0 : Mom d) κ x₀‖ ^ 2 +
        (N.dartSign x₁ * ‖Molecule.kvec L (0 : Mom d) κ x₁‖ ^ 2 + N.dartSign x₂ * ‖Molecule.kvec L (0 : Mom d) κ x₂‖ ^ 2))
          - β (M.atom e)| ≤ δ⁻¹ * L ^ (-2 * γ) := by
      intro κ hκ
      have h := hκ.2.1.1 (M.atom e) hpN
      unfold Molecule.Gamma at h
      rwa [hP, sum_insert hP0, sum_insert (by simpa using hP12), sum_singleton] at h
    have hwinQ : ∀ κ ∈ A, |(N.dartSign (N.mate x₀) * ‖Molecule.kvec L (0 : Mom d) κ (N.mate x₀)‖ ^ 2 +
        (N.dartSign x₃ * ‖Molecule.kvec L (0 : Mom d) κ x₃‖ ^ 2 + N.dartSign x₄ * ‖Molecule.kvec L (0 : Mom d) κ x₄‖ ^ 2))
          - β (M.atom (M.mate e))| ≤ δ⁻¹ * L ^ (-2 * γ) := by
      intro κ hκ
      have h := hκ.2.1.1 (M.atom (M.mate e)) hqN
      unfold Molecule.Gamma at h
      rwa [hQ, sum_insert hQ0, sum_insert (by simpa using hQ34), sum_singleton] at h
    have hmaps : Set.MapsTo f A S := by
      intro κ hκ
      have hm0 : κ (N.mate x₀) = κ x₀ := hκ.1.1 x₀
      refine ⟨fun t => ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · have hr := hκ.2.1.2
        fin_cases t <;> simpa [f, a, CountLemmas.NearLattice, Molecule.kvec] using hr _
      · show ∑ i, ((εA i : ℤ)) • f κ (![0, 1, 2] i) = sA κ₀
        apply hinjL
        beta_reduce
        rw [hconsP κ₀ hκ₀, ← hconsP κ hκ, Fin.sum_univ_three]
        simp [f, εA, sA, add_assoc]
      · have h := hwinP κ hκ
        rw [Fin.sum_univ_three]
        show |((dartUnit N x₀ : ℤ) : ℝ) * ‖latticePoint L (κ x₀)‖ ^ 2 +
          ((dartUnit N x₁ : ℤ) : ℝ) * ‖latticePoint L (κ x₁)‖ ^ 2 +
            ((dartUnit N x₂ : ℤ) : ℝ) * ‖latticePoint L (κ x₂)‖ ^ 2 - β (M.atom e)| ≤ δ⁻¹ * L ^ (-2 * γ)
        simp only [Molecule.kvec, zero_add, dartSign_eq_unit] at h
        rwa [add_assoc]
      · show ∑ i, ((εB i : ℤ)) • f κ (![0, 3, 4] i) = sB κ₀
        apply hinjL
        beta_reduce
        rw [hconsQ κ₀ hκ₀, ← hconsQ κ hκ, Fin.sum_univ_three]
        simp [f, εB, sB, add_assoc, hm0]
      · have h := hwinQ κ hκ
        rw [Fin.sum_univ_three]
        show |((dartUnit N (N.mate x₀) : ℤ) : ℝ) * ‖latticePoint L (κ x₀)‖ ^ 2 +
          ((dartUnit N x₃ : ℤ) : ℝ) * ‖latticePoint L (κ x₃)‖ ^ 2 +
            ((dartUnit N x₄ : ℤ) : ℝ) * ‖latticePoint L (κ x₄)‖ ^ 2 - β (M.atom (M.mate e))| ≤ δ⁻¹ * L ^ (-2 * γ)
        simp only [Molecule.kvec, zero_add, dartSign_eq_unit, hm0] at h
        rwa [add_assoc]
    have hinj : Set.InjOn f A := by
      intro κ hκ κ' hκ' hf
      have hc : ∀ t, f κ t = f κ' t := fun t => congrFun hf t
      have e0 : κ x₀ = κ' x₀ := hc 0
      have e1 : κ x₁ = κ' x₁ := hc 1
      have e2 : κ x₂ = κ' x₂ := hc 2
      have e3 : κ x₃ = κ' x₃ := hc 3
      have e4 : κ x₄ = κ' x₄ := hc 4
      have hcase : ∀ y, N.atom y = M.atom e ∨ N.atom y = M.atom (M.mate e) → κ y = κ' y := by
        intro y hy
        rcases hy with hy | hy
        · have : y ∈ N.dartsAt (M.atom e) := by simp [Molecule.dartsAt, hy]
          rw [hP] at this
          simp only [mem_insert, mem_singleton] at this
          rcases this with rfl | rfl | rfl <;> assumption
        · have : y ∈ N.dartsAt (M.atom (M.mate e)) := by simp [Molecule.dartsAt, hy]
          rw [hQ] at this
          simp only [mem_insert, mem_singleton] at this
          rcases this with rfl | rfl | rfl
          · rw [hκ.1.1 x₀, hκ'.1.1 x₀]; exact e0
          · exact e3
          · exact e4
      funext z
      by_cases hzp : N.atom z = M.atom e
      · exact hcase z (Or.inl hzp)
      by_cases hzq : N.atom z = M.atom (M.mate e)
      · exact hcase z (Or.inr hzq)
      rw [← hκ.1.1 z, ← hκ'.1.1 z]
      exact hcase (N.mate z) (hR z hzp hzq)
    have hfin : S.Finite := by
      refine (Set.Finite.pi (t := fun t => {n | CountLemmas.NearLattice L (a t) n})
        (fun t => CountLemmas.finite_nearLattice hLp (a t))).subset fun n hn => ?_
      simpa using hn.1
    have hcard := hL₀ L hLL a εA εB (not_three_equal_units (hcapN _ hpN) hP hP0 hP12)
      (not_three_equal_units (hcapN _ hqN) hQ hQ0 hQ34) (sA κ₀) (sB κ₀) (β (M.atom e)) (β (M.atom (M.mate e)))
    calc A.encard ≤ S.encard := Set.encard_le_encard_of_injOn hmaps hinj
      _ = (S.ncard : ℕ∞) := hfin.cast_ncard_eq.symm
      _ ≤ (⌊X⌋₊ : ℕ∞) := (Nat.cast_le (α := ℕ∞)).mpr (Nat.le_floor hcard)
  have hE : MoleProp.countEFree (MoleProp.eraseBond M e) L γ δ (0 : Mom d) Adm ≤ (⌊X⌋₊ : ℕ∞) := by
    unfold MoleProp.countEFree
    exact iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun _ => key c β k0
  calc (MoleProp.countEFree (MoleProp.eraseBond M e) L γ δ (0 : Mom d) Adm : ℝ≥0∞)
      ≤ ((⌊X⌋₊ : ℕ∞) : ℝ≥0∞) := ENat.toENNReal_mono hE
    _ = ENNReal.ofReal (⌊X⌋₊ : ℝ) := by rw [ENNReal.ofReal_natCast]; rfl
    _ ≤ ENNReal.ofReal X := ENNReal.ofReal_le_ofReal (Nat.floor_le hX0)

end WaveTurbulence.MoleProp4
