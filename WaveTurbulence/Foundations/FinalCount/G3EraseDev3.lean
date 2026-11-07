/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3EraseDev2
/-! **FINALCOUNT-G3: the erasure count** (R27, research-remtame-i L4): `𝔈(M) ≤ N · 𝔈(M - v)` when all the bonds at `v` carry one
label `k` (tame), `N` bounding the number of values `k` that occur.  The labels of `M - v` are the restrictions; the parameters
`(c, β)` of `M - v` are those of `M` shifted by the (known) contribution `k` of the bonds to `v`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}
variable {M : Molecule V D} {v : V}

/-- The net sign of the bonds from `a` to `v`. -/
noncomputable def mw (M : Molecule V D) (v a : V) : ℝ :=
  ∑ x ∈ (M.dartsAt a).filter (fun x => M.atom (M.mate x) = v), M.dartSign x

theorem erase_sum_split {E : Type*} [AddCommMonoid E] (g : D → E) {a : V} :
    ∑ x ∈ M.dartsAt a, g x = ∑ x ∈ (M.dartsAt a).filter (fun x => M.atom (M.mate x) = v), g x +
      ∑ x ∈ (M.dartsAt a).filter (fun x => ¬ M.atom (M.mate x) = v), g x :=
  (Finset.sum_filter_add_sum_filter_not _ _ _).symm

theorem erase_dec_sum {L : ℝ} {w : Mom d} {κ : D → (Fin d → ℤ)} {c : V → Mom d} {k : Fin d → ℤ}
    (hdec : M.IsDecoration L w c κ) (hk : ∀ x ∈ M.dartsAt v, κ x = k) {a : V} (haM : a ∈ M.atoms) (hav : a ≠ v) :
    ∑ x ∈ (eraseAt M v).dartsAt a, (eraseAt M v).dartSign x •
        Molecule.kvec L w (fun y : EDart M v => κ y.1) x = c a - mw M v a • (w + latticePoint L k) := by
  have h1 := eraseAt_sum M v hav (fun z => M.dartSign z • Molecule.kvec L w κ z)
  have h2 := erase_sum_split (M := M) (v := v) (a := a) (fun z => M.dartSign z • Molecule.kvec L w κ z)
  have h3 : ∑ x ∈ (M.dartsAt a).filter (fun x => M.atom (M.mate x) = v), M.dartSign x • Molecule.kvec L w κ x =
      mw M v a • (w + latticePoint L k) := by
    unfold mw
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxv : M.atom (M.mate x) = v := (Finset.mem_filter.1 hx).2
    have hm : κ (M.mate x) = k := hk _ (by simp [Molecule.dartsAt, hxv])
    have : κ x = k := by rw [← hm]; exact (hdec.1 x).symm
    unfold Molecule.kvec; rw [this]
  have h4 := hdec.2 a haM
  show _ = _
  have : ∑ x ∈ (eraseAt M v).dartsAt a, (eraseAt M v).dartSign x •
        Molecule.kvec L w (fun y : EDart M v => κ y.1) x =
      ∑ x ∈ (eraseAt M v).dartsAt a, (fun z => M.dartSign z • Molecule.kvec L w κ z) x.1 := rfl
  rw [this, h1]
  rw [h2, h3] at h4
  rw [← h4]; abel

theorem erase_gamma {L : ℝ} {w : Mom d} {κ : D → (Fin d → ℤ)} {k : Fin d → ℤ}
    (hmate : ∀ x, κ (M.mate x) = κ x) (hk : ∀ x ∈ M.dartsAt v, κ x = k) {a : V} (hav : a ≠ v) :
    (eraseAt M v).Gamma L w (fun y : EDart M v => κ y.1) a = M.Gamma L w κ a - mw M v a * ‖w + latticePoint L k‖ ^ 2 := by
  have h1 := eraseAt_sum M v hav (fun z => M.dartSign z * ‖Molecule.kvec L w κ z‖ ^ 2)
  have h2 := erase_sum_split (M := M) (v := v) (a := a) (fun z => M.dartSign z * ‖Molecule.kvec L w κ z‖ ^ 2)
  have h3 : ∑ x ∈ (M.dartsAt a).filter (fun x => M.atom (M.mate x) = v), M.dartSign x * ‖Molecule.kvec L w κ x‖ ^ 2 =
      mw M v a * ‖w + latticePoint L k‖ ^ 2 := by
    unfold mw
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxv : M.atom (M.mate x) = v := (Finset.mem_filter.1 hx).2
    have hm : κ (M.mate x) = k := hk _ (by simp [Molecule.dartsAt, hxv])
    have : κ x = k := by rw [← hm]; exact (hmate x).symm
    unfold Molecule.kvec; rw [this]
  unfold Molecule.Gamma
  have : ∑ x ∈ (eraseAt M v).dartsAt a, (eraseAt M v).dartSign x *
        ‖Molecule.kvec L w (fun y : EDart M v => κ y.1) x‖ ^ 2 =
      ∑ x ∈ (eraseAt M v).dartsAt a, (fun z => M.dartSign z * ‖Molecule.kvec L w κ z‖ ^ 2) x.1 := rfl
  rw [this, h1, h2, h3]; ring


theorem mw_eq_zero_of_mult {a : V} (h : mult M v a = 0) : mw M v a = 0 := by
  unfold mult at h
  rw [Finset.card_eq_zero] at h
  unfold mw; rw [h]; simp

/-- **The erasure count.** -/
theorem countE_erase_le_of_vals {L γ δ : ℝ} {w : Mom d} (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (EDart M v → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x : EDart M v => κ x.1))
    (hM4 : ∀ a ∈ M.atoms, M.deg a ≤ 4) (N : ℕ)
    (hI : ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      ∃ I : Finset (Fin d → ℤ), I.card ≤ N ∧
        ∀ κ ∈ decSet M L γ δ w Adm c β k0, ∃ k ∈ I, ∀ x ∈ M.dartsAt v, κ x = k) :
    M.countE L γ δ w Adm ≤ (N : ℕ∞) * (eraseAt M v).countE L γ δ w Adm' := by
  refine countE_le_mul_of_cover_proj M (eraseAt M v) L γ δ w Adm Adm' (fun κ x => κ x.1) N ?_
  intro c β k0 hp
  obtain ⟨I, hIc, hIk⟩ := hI c β k0 hp
  refine ⟨Fin d → ℤ, I, fun k => {κ | ∀ x ∈ M.dartsAt v, κ x = k},
    fun k => (fun a => c a - mw M v a • (w + latticePoint L k),
      fun a => β a - mw M v a * ‖w + latticePoint L k‖ ^ 2, fun x => k0 x.1), hIc, ?_, ?_, ?_⟩
  · intro k _
    refine ⟨fun a ha h4 => ?_, fun x => hp.2 x.1⟩
    have haM : a ∈ M.atoms := Finset.mem_of_mem_erase ha
    have hav : a ≠ v := Finset.ne_of_mem_erase ha
    have hsum := eraseAt_dartsAt_card M v hav
    have hle := hM4 a haM
    have hm : mult M v a = 0 := by
      have h4' : (eraseAt M v).deg a = 4 := h4
      omega
    have hdeg : M.deg a = 4 := by
      have h4' : (eraseAt M v).deg a = 4 := h4
      omega
    show c a - mw M v a • (w + latticePoint L k) = 0
    rw [mw_eq_zero_of_mult hm, zero_smul, sub_zero]
    exact hp.1 a haM hdeg
  · intro κ hκ
    obtain ⟨k, hkI, hk⟩ := hIk κ hκ
    exact Set.mem_iUnion₂.2 ⟨k, hkI, hk⟩
  · intro k _
    refine ⟨?_, ?_⟩
    · rintro κ ⟨hκG, hκ⟩ κ' ⟨hκ'G, hκ'⟩ e
      funext y
      by_cases h1 : M.atom y = v
      · rw [hκG y (by simp [Molecule.dartsAt, h1]), hκ'G y (by simp [Molecule.dartsAt, h1])]
      · by_cases h2 : M.atom (M.mate y) = v
        · have e1 : κ y = κ (M.mate y) := (hκ.1.1 y).symm
          have e2 : κ' y = κ' (M.mate y) := (hκ'.1.1 y).symm
          rw [e1, e2, hκG _ (by simp [Molecule.dartsAt, h2]), hκ'G _ (by simp [Molecule.dartsAt, h2])]
        · exact congrFun e ⟨y, h1, h2⟩
    · rintro _ ⟨κ, ⟨hκG, hdec, hres, hA⟩, rfl⟩
      refine ⟨⟨fun x => hdec.1 x.1, fun a ha => ?_⟩, ⟨fun a ha => ?_, fun x => hres.2 x.1⟩, hAdm' κ hA⟩
      · have haM : a ∈ M.atoms := Finset.mem_of_mem_erase ha
        exact erase_dec_sum hdec hκG haM (Finset.ne_of_mem_erase ha)
      · have haM : a ∈ M.atoms := Finset.mem_of_mem_erase ha
        have hav : a ≠ v := Finset.ne_of_mem_erase ha
        have := hres.1 a haM
        show |(eraseAt M v).Gamma L w (fun y : EDart M v => κ y.1) a -
          (β a - mw M v a * ‖w + latticePoint L k‖ ^ 2)| ≤ _
        rw [erase_gamma hdec.1 hκG hav]
        have e : M.Gamma L w κ a - mw M v a * ‖w + latticePoint L k‖ ^ 2 -
            (β a - mw M v a * ‖w + latticePoint L k‖ ^ 2) = M.Gamma L w κ a - β a := by ring
        rw [e]; exact this

end WaveTurbulence.FinalCountG3
