/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3EraseDev3
/-! **FINALCOUNT-G3: the flux identity and the value counts of an erasure** (R27, research-remtame-i L1).

For a decoration with all bonds at `v` equal to `k`, a component `C` of `M - v` satisfies
`∑_{b ∈ C} c_b = sgnC C • (w + k/L)`.  Hence a pinned `v` has its value `k` determined by `c`; in general `k` lies in a box of
`(⌊2L⌋ + 1)^d` lattice points around `k⁰`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}
variable {M : Molecule V D} {v : V}

theorem mate_atom_cmp (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) {a : V} {x : D} (hx : M.atom x ∈ cmp M v a)
    (hy : M.atom (M.mate x) ≠ v) : M.atom (M.mate x) ∈ cmp M v a := by
  obtain ⟨hxm, hsc⟩ := mem_cmp.1 hx
  refine mem_cmp.2 ⟨Finset.mem_erase.2 ⟨hy, M.atom_mem _⟩, ?_⟩
  have hxv : M.atom x ≠ v := Finset.ne_of_mem_erase hxm
  exact Relation.EqvGen.trans _ _ _ hsc (Relation.EqvGen.rel _ _ (eraseAt_adj_iff.2 ⟨⟨x, rfl, rfl⟩, hxv, hy⟩))

/-- **The flux identity.** -/
theorem flux_identity (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) {L : ℝ} {w : Mom d} {κ : D → (Fin d → ℤ)}
    {c : V → Mom d} {k : Fin d → ℤ} (hdec : M.IsDecoration L w c κ) (hk : ∀ x ∈ M.dartsAt v, κ x = k) (a : V) :
    ∑ b ∈ cmp M v a, c b = sgnC M v (cmp M v a) • (w + latticePoint L k) := by
  set C := cmp M v a with hC
  set f : D → Mom d := fun x => M.dartSign x • Molecule.kvec L w κ x with hf
  have hCatoms : ∀ b ∈ C, b ∈ M.atoms := fun b hb => Finset.mem_of_mem_erase (mem_cmp.1 hb).1
  have h1 : ∑ b ∈ C, c b = ∑ b ∈ C, ∑ x ∈ M.dartsAt b, f x :=
    Finset.sum_congr rfl fun b hb => (hdec.2 b (hCatoms b hb)).symm
  have h2 : ∑ b ∈ C, ∑ x ∈ M.dartsAt b, f x = ∑ x ∈ Finset.univ.filter (fun x => M.atom x ∈ C), f x := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun x => M.atom x ∈ C)) (t := C)
      (g := M.atom) (fun x hx => (Finset.mem_filter.1 hx).2)]
    refine Finset.sum_congr rfl fun b hb => ?_
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext x
    simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact ⟨h ▸ hb, h⟩
    · intro h; exact h.2
  have h3 := Finset.sum_filter_add_sum_filter_not (Finset.univ.filter (fun x => M.atom x ∈ C))
    (fun x => M.atom (M.mate x) ∈ C) f
  -- the internal bonds cancel
  have h4 : ∑ x ∈ (Finset.univ.filter (fun x => M.atom x ∈ C)).filter (fun x => M.atom (M.mate x) ∈ C), f x = 0 := by
    refine Finset.sum_involution (fun x _ => M.mate x) (fun x hx => ?_) (fun x hx hne => ?_) (fun x hx => ?_)
      (fun x hx => M.mate_mate x)
    · have hm : κ (M.mate x) = κ x := hdec.1 x
      simp only [hf, Molecule.kvec, hm, dartSign_mate, neg_smul]
      abel
    · exact fun e => M.mate_ne x e
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact ⟨hx.2, by rw [M.mate_mate]; exact hx.1⟩
  -- the bonds to `v`
  have h5 : ∑ x ∈ (Finset.univ.filter (fun x => M.atom x ∈ C)).filter (fun x => ¬ M.atom (M.mate x) ∈ C), f x =
      sgnC M v C • (w + latticePoint L k) := by
    have hset : (Finset.univ.filter (fun x => M.atom x ∈ C)).filter (fun x => ¬ M.atom (M.mate x) ∈ C) =
        crossD M v C := by
      ext x
      simp only [crossD, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        by_contra hne
        exact h2 (mate_atom_cmp hnl h1 hne)
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun hmem => ?_⟩
        have := Finset.ne_of_mem_erase (mem_cmp.1 hmem).1
        exact this h2
    rw [hset]
    unfold sgnC
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxv : M.atom (M.mate x) = v := (Finset.mem_filter.1 hx).2.2
    have hm : κ (M.mate x) = k := hk _ (by simp [Molecule.dartsAt, hxv])
    have : κ x = k := by rw [← hm]; exact (hdec.1 x).symm
    simp only [hf, Molecule.kvec, this]
  rw [h1, h2, ← h3, h4, h5, zero_add]


/-- The lattice points `k` with `‖w + k/L - r‖ ≤ 1` lie in a box of at most `(⌊2L⌋ + 1)^d` points. -/
theorem exists_box {L : ℝ} (hL : 0 < L) (w r : Mom d) :
    ∃ I : Finset (Fin d → ℤ), I.card ≤ (⌊2 * L⌋₊ + 1) ^ d ∧
      ∀ k : Fin d → ℤ, ‖w + latticePoint L k - r‖ ≤ 1 → k ∈ I := by
  let a : Fin d → ℤ := fun i => ⌈L * (r i - w i) - L⌉
  let b : Fin d → ℤ := fun i => ⌊L * (r i - w i) + L⌋
  refine ⟨Fintype.piFinset fun i => Finset.Icc (a i) (b i), ?_, ?_⟩
  · rw [Fintype.card_piFinset]
    calc ∏ i, (Finset.Icc (a i) (b i)).card ≤ ∏ _i : Fin d, (⌊2 * L⌋₊ + 1) := by
          refine Finset.prod_le_prod' fun i _ => ?_
          rw [Int.card_Icc]
          have h1 : (b i : ℝ) ≤ L * (r i - w i) + L := Int.floor_le _
          have h2 : L * (r i - w i) - L ≤ (a i : ℝ) := Int.le_ceil _
          have h3 : ((b i - a i : ℤ) : ℝ) ≤ 2 * L := by push_cast; linarith
          have h4 : b i - a i ≤ ⌊2 * L⌋ := Int.le_floor.2 h3
          have h5 : ⌊2 * L⌋ = (⌊2 * L⌋₊ : ℤ) := (Int.natCast_floor_eq_floor (by linarith)).symm
          omega
      _ = (⌊2 * L⌋₊ + 1) ^ d := by simp
  · intro k hk
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have hi : |(w + latticePoint L k - r) i| ≤ 1 := by
      have := PiLp.norm_apply_le (w + latticePoint L k - r) i
      rw [Real.norm_eq_abs] at this
      exact this.trans hk
    have hi' : (w + latticePoint L k - r) i = w i + (k i : ℝ) / L - r i := by
      simp [latticePoint]
    rw [hi', abs_le] at hi
    have e1 : L * (r i - w i) - L ≤ (k i : ℝ) := by
      have : (k i : ℝ) / L ≥ r i - w i - 1 := by linarith [hi.1]
      rw [ge_iff_le, le_div_iff₀ hL] at this
      nlinarith
    have e2 : (k i : ℝ) ≤ L * (r i - w i) + L := by
      have : (k i : ℝ) / L ≤ r i - w i + 1 := by linarith [hi.2]
      rw [div_le_iff₀ hL] at this
      nlinarith
    exact ⟨Int.ceil_le.2 e1, Int.le_floor.2 e2⟩

/-- Tameness: all the bonds at `v` carry one label (from the zero gaps of the triples at `v`). -/
def TameLabels (M : Molecule V D) (v : V) (κ : D → (Fin d → ℤ)) : Prop := ∀ x ∈ M.dartsAt v, ∀ y ∈ M.dartsAt v, κ x = κ y

theorem countE_erase_le_box {L γ δ : ℝ} (hL : 0 < L) {w : Mom d} (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (EDart M v → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x : EDart M v => κ x.1))
    (hM4 : ∀ a ∈ M.atoms, M.deg a ≤ 4) (hd : 1 ≤ M.deg v) (htame : ∀ κ, Adm κ → TameLabels M v κ) :
    M.countE L γ δ w Adm ≤ (((⌊2 * L⌋₊ + 1) ^ d : ℕ) : ℕ∞) * (eraseAt M v).countE L γ δ w Adm' := by
  obtain ⟨x₀, hx₀⟩ := Finset.card_pos.1 hd
  refine countE_erase_le_of_vals Adm Adm' hAdm' hM4 _ fun c β k0 hp => ?_
  obtain ⟨I, hIc, hIk⟩ := exists_box hL w (k0 x₀)
  refine ⟨I, hIc, fun κ hκ => ⟨κ x₀, hIk _ ?_, fun x hx => htame κ hκ.2.2 x hx x₀ hx₀⟩⟩
  exact hκ.2.1.2 x₀

theorem countE_erase_le_pinned {L γ δ : ℝ} (hL : 0 < L) {w : Mom d} (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (EDart M v → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x : EDart M v => κ x.1))
    (hM4 : ∀ a ∈ M.atoms, M.deg a ≤ 4) (hd : 1 ≤ M.deg v) (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x))
    (htame : ∀ κ, Adm κ → TameLabels M v κ) (hP : Pinned M v) :
    M.countE L γ δ w Adm ≤ ((1 : ℕ) : ℕ∞) * (eraseAt M v).countE L γ δ w Adm' := by
  obtain ⟨x₀, hx₀⟩ := Finset.card_pos.1 hd
  obtain ⟨a, ha, hsg⟩ := hP
  refine countE_erase_le_of_vals Adm Adm' hAdm' hM4 _ fun c β k0 hp => ?_
  by_cases hex : ∃ κ, κ ∈ decSet M L γ δ w Adm c β k0
  · obtain ⟨κ₀, hκ₀⟩ := hex
    refine ⟨{κ₀ x₀}, by simp, fun κ hκ => ⟨κ x₀, ?_, fun x hx => htame κ hκ.2.2 x hx x₀ hx₀⟩⟩
    have e1 := flux_identity hnl hκ.1 (fun x hx => htame κ hκ.2.2 x hx x₀ hx₀) a
    have e2 := flux_identity hnl hκ₀.1 (fun x hx => htame κ₀ hκ₀.2.2 x hx x₀ hx₀) a
    rw [e1] at e2
    have e3 : w + latticePoint L (κ x₀) = w + latticePoint L (κ₀ x₀) := by
      have := smul_right_injective (Mom d) hsg e2
      exact this
    have e4 : latticePoint L (κ x₀) = latticePoint L (κ₀ x₀) := add_left_cancel e3
    have hinj : Function.Injective (latticePoint (d := d) L) := by
      intro z z' h
      funext i
      have h' := congrArg (fun v : Mom d => v i) h
      have h'' : ((z i : ℤ) : ℝ) / L = ((z' i : ℤ) : ℝ) / L := by simpa [latticePoint] using h'
      have : ((z i : ℤ) : ℝ) = ((z' i : ℤ) : ℝ) := by
        field_simp at h''; exact h''
      exact_mod_cast this
    simp [hinj e4]
  · exact ⟨∅, by simp, fun κ hκ => absurd ⟨κ, hκ⟩ hex⟩

end WaveTurbulence.FinalCountG3
