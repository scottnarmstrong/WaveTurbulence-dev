/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3ClDev2
public import WaveTurbulence.Foundations.FinalCount.G3EraseDev4
/-! **FINALCOUNT-G3 (R29 item 4, step 4): the cluster erasure count** (set version of `G3EraseDev3`, `G3EraseDev4`).

`𝔈(M) ≤ N · 𝔈(M - K)` when all the darts at the atoms of `K` carry one label `k` (tame cluster), `N` bounding the number of values
of `k`: `N = 1` for pinned `K` (`countE_eraseSet_le_pinned`; the value is determined by the flux identity or fixed by subpro (3)),
`N = (⌊2L⌋+1)^d` otherwise (`countE_eraseSet_le_box`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}
variable {M : Molecule V D} {K : Finset V}

/-- The net sign of the bonds from `a` into `K`. -/
noncomputable def mwS (M : Molecule V D) (K : Finset V) (a : V) : ℝ :=
  ∑ x ∈ (M.dartsAt a).filter (fun x => M.atom (M.mate x) ∈ K), M.dartSign x

theorem eraseSet_sum {a : V} (ha : a ∉ K) {E : Type*} [AddCommMonoid E] (g : D → E) :
    ∑ x ∈ (eraseSet M K).dartsAt a, g x.1 = ∑ x ∈ (M.dartsAt a).filter (fun x => ¬ M.atom (M.mate x) ∈ K), g x := by
  have h : (eraseSet M K).dartsAt a =
      ((M.dartsAt a).filter (fun x => ¬ M.atom (M.mate x) ∈ K)).subtype
        (fun x => M.atom x ∉ K ∧ M.atom (M.mate x) ∉ K) := by
    ext x
    simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_subtype]
    constructor
    · intro hx; exact ⟨hx, x.2.2⟩
    · intro hx; exact hx.1
  rw [h, Finset.sum_subtype_eq_sum_filter, Finset.filter_true_of_mem]
  intro x hx
  simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  exact ⟨hx.1 ▸ ha, hx.2⟩

theorem eraseS_sum_split {E : Type*} [AddCommMonoid E] (g : D → E) {a : V} :
    ∑ x ∈ M.dartsAt a, g x = ∑ x ∈ (M.dartsAt a).filter (fun x => M.atom (M.mate x) ∈ K), g x +
      ∑ x ∈ (M.dartsAt a).filter (fun x => ¬ M.atom (M.mate x) ∈ K), g x :=
  (Finset.sum_filter_add_sum_filter_not _ _ _).symm

theorem eraseS_dec_sum {L : ℝ} {w : Mom d} {κ : D → (Fin d → ℤ)} {c : V → Mom d} {k : Fin d → ℤ}
    (hdec : M.IsDecoration L w c κ) (hk : ∀ x, M.atom x ∈ K → κ x = k) {a : V} (haM : a ∈ M.atoms) (hav : a ∉ K) :
    ∑ x ∈ (eraseSet M K).dartsAt a, (eraseSet M K).dartSign x •
        Molecule.kvec L w (fun y : EDartS M K => κ y.1) x = c a - mwS M K a • (w + latticePoint L k) := by
  have h1 := eraseSet_sum (M := M) (K := K) hav (fun z => M.dartSign z • Molecule.kvec L w κ z)
  have h2 := eraseS_sum_split (M := M) (K := K) (a := a) (fun z => M.dartSign z • Molecule.kvec L w κ z)
  have h3 : ∑ x ∈ (M.dartsAt a).filter (fun x => M.atom (M.mate x) ∈ K), M.dartSign x • Molecule.kvec L w κ x =
      mwS M K a • (w + latticePoint L k) := by
    unfold mwS
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxv : M.atom (M.mate x) ∈ K := (Finset.mem_filter.1 hx).2
    have hm : κ (M.mate x) = k := hk _ hxv
    have : κ x = k := by rw [← hm]; exact (hdec.1 x).symm
    unfold Molecule.kvec; rw [this]
  have h4 := hdec.2 a haM
  show _ = _
  have : ∑ x ∈ (eraseSet M K).dartsAt a, (eraseSet M K).dartSign x •
        Molecule.kvec L w (fun y : EDartS M K => κ y.1) x =
      ∑ x ∈ (eraseSet M K).dartsAt a, (fun z => M.dartSign z • Molecule.kvec L w κ z) x.1 := rfl
  rw [this, h1]
  rw [h2, h3] at h4
  rw [← h4]; abel

theorem eraseS_gamma {L : ℝ} {w : Mom d} {κ : D → (Fin d → ℤ)} {k : Fin d → ℤ}
    (hmate : ∀ x, κ (M.mate x) = κ x) (hk : ∀ x, M.atom x ∈ K → κ x = k) {a : V} (hav : a ∉ K) :
    (eraseSet M K).Gamma L w (fun y : EDartS M K => κ y.1) a =
      M.Gamma L w κ a - mwS M K a * ‖w + latticePoint L k‖ ^ 2 := by
  have h1 := eraseSet_sum (M := M) (K := K) hav (fun z => M.dartSign z * ‖Molecule.kvec L w κ z‖ ^ 2)
  have h2 := eraseS_sum_split (M := M) (K := K) (a := a) (fun z => M.dartSign z * ‖Molecule.kvec L w κ z‖ ^ 2)
  have h3 : ∑ x ∈ (M.dartsAt a).filter (fun x => M.atom (M.mate x) ∈ K), M.dartSign x * ‖Molecule.kvec L w κ x‖ ^ 2 =
      mwS M K a * ‖w + latticePoint L k‖ ^ 2 := by
    unfold mwS
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxv : M.atom (M.mate x) ∈ K := (Finset.mem_filter.1 hx).2
    have hm : κ (M.mate x) = k := hk _ hxv
    have : κ x = k := by rw [← hm]; exact (hmate x).symm
    unfold Molecule.kvec; rw [this]
  unfold Molecule.Gamma
  have : ∑ x ∈ (eraseSet M K).dartsAt a, (eraseSet M K).dartSign x *
        ‖Molecule.kvec L w (fun y : EDartS M K => κ y.1) x‖ ^ 2 =
      ∑ x ∈ (eraseSet M K).dartsAt a, (fun z => M.dartSign z * ‖Molecule.kvec L w κ z‖ ^ 2) x.1 := rfl
  rw [this, h1, h2, h3]; ring

theorem mwS_eq_zero_of_multS {a : V} (h : multS M K a = 0) : mwS M K a = 0 := by
  unfold multS at h
  rw [Finset.card_eq_zero] at h
  unfold mwS; rw [h]; simp

/-- **The cluster erasure count.** -/
theorem countE_eraseSet_le_of_vals {L γ δ : ℝ} {w : Mom d} (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (EDartS M K → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x : EDartS M K => κ x.1))
    (hM4 : ∀ a ∈ M.atoms, M.deg a ≤ 4) (N : ℕ)
    (hI : ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      ∃ I : Finset (Fin d → ℤ), I.card ≤ N ∧
        ∀ κ ∈ decSet M L γ δ w Adm c β k0, ∃ k ∈ I, ∀ x, M.atom x ∈ K → κ x = k) :
    M.countE L γ δ w Adm ≤ (N : ℕ∞) * (eraseSet M K).countE L γ δ w Adm' := by
  refine countE_le_mul_of_cover_proj M (eraseSet M K) L γ δ w Adm Adm' (fun κ x => κ x.1) N ?_
  intro c β k0 hp
  obtain ⟨I, hIc, hIk⟩ := hI c β k0 hp
  refine ⟨Fin d → ℤ, I, fun k => {κ | ∀ x, M.atom x ∈ K → κ x = k},
    fun k => (fun a => c a - mwS M K a • (w + latticePoint L k),
      fun a => β a - mwS M K a * ‖w + latticePoint L k‖ ^ 2, fun x => k0 x.1), hIc, ?_, ?_, ?_⟩
  · intro k _
    refine ⟨fun a ha h4 => ?_, fun x => hp.2 x.1⟩
    have haM : a ∈ M.atoms := (Finset.mem_sdiff.1 ha).1
    have hav : a ∉ K := (Finset.mem_sdiff.1 ha).2
    have hsum := eraseSet_deg_card (M := M) (E := K) hav
    have hle := hM4 a haM
    have hm : multS M K a = 0 := by
      have h4' : (eraseSet M K).deg a = 4 := h4
      omega
    have hdeg : M.deg a = 4 := by
      have h4' : (eraseSet M K).deg a = 4 := h4
      omega
    show c a - mwS M K a • (w + latticePoint L k) = 0
    rw [mwS_eq_zero_of_multS hm, zero_smul, sub_zero]
    exact hp.1 a haM hdeg
  · intro κ hκ
    obtain ⟨k, hkI, hk⟩ := hIk κ hκ
    exact Set.mem_iUnion₂.2 ⟨k, hkI, hk⟩
  · intro k _
    refine ⟨?_, ?_⟩
    · rintro κ ⟨hκG, hκ⟩ κ' ⟨hκ'G, hκ'⟩ e
      funext y
      by_cases h1 : M.atom y ∈ K
      · rw [hκG y h1, hκ'G y h1]
      · by_cases h2 : M.atom (M.mate y) ∈ K
        · have e1 : κ y = κ (M.mate y) := (hκ.1.1 y).symm
          have e2 : κ' y = κ' (M.mate y) := (hκ'.1.1 y).symm
          rw [e1, e2, hκG _ h2, hκ'G _ h2]
        · exact congrFun e ⟨y, h1, h2⟩
    · rintro _ ⟨κ, ⟨hκG, hdec, hres, hA⟩, rfl⟩
      refine ⟨⟨fun x => hdec.1 x.1, fun a ha => ?_⟩, ⟨fun a ha => ?_, fun x => hres.2 x.1⟩, hAdm' κ hA⟩
      · have haM : a ∈ M.atoms := (Finset.mem_sdiff.1 ha).1
        exact eraseS_dec_sum hdec hκG haM (Finset.mem_sdiff.1 ha).2
      · have haM : a ∈ M.atoms := (Finset.mem_sdiff.1 ha).1
        have hav : a ∉ K := (Finset.mem_sdiff.1 ha).2
        have := hres.1 a haM
        show |(eraseSet M K).Gamma L w (fun y : EDartS M K => κ y.1) a -
          (β a - mwS M K a * ‖w + latticePoint L k‖ ^ 2)| ≤ _
        rw [eraseS_gamma hdec.1 hκG hav]
        have e : M.Gamma L w κ a - mwS M K a * ‖w + latticePoint L k‖ ^ 2 -
            (β a - mwS M K a * ‖w + latticePoint L k‖ ^ 2) = M.Gamma L w κ a - β a := by ring
        rw [e]; exact this

/-- Tameness of a cluster: all the darts at atoms of `K` carry one label. -/
def TameLabelsS (M : Molecule V D) (K : Finset V) (κ : D → (Fin d → ℤ)) : Prop :=
  ∀ x y, M.atom x ∈ K → M.atom y ∈ K → κ x = κ y

theorem countE_eraseSet_le_box {L γ δ : ℝ} (hL : 0 < L) {w : Mom d} (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (EDartS M K → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x : EDartS M K => κ x.1))
    (hM4 : ∀ a ∈ M.atoms, M.deg a ≤ 4) {x₀ : D} (hx₀ : M.atom x₀ ∈ K) (htame : ∀ κ, Adm κ → TameLabelsS M K κ) :
    M.countE L γ δ w Adm ≤ (((⌊2 * L⌋₊ + 1) ^ d : ℕ) : ℕ∞) * (eraseSet M K).countE L γ δ w Adm' := by
  refine countE_eraseSet_le_of_vals Adm Adm' hAdm' hM4 _ fun c β k0 hp => ?_
  obtain ⟨I, hIc, hIk⟩ := exists_box hL w (k0 x₀)
  refine ⟨I, hIc, fun κ hκ => ⟨κ x₀, hIk _ ?_, fun x hx => htame κ hκ.2.2 x x₀ hx hx₀⟩⟩
  exact hκ.2.1.2 x₀

end WaveTurbulence.FinalCountG3
