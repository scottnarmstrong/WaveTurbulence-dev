/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3ClDev1
public import WaveTurbulence.Foundations.FinalCount.G3EraseDev2
/-! **FINALCOUNT-G3 (R29 item 4, step 4): the flux dichotomy and the rank drop of a cluster erasure** (set version of
`G3EraseDev2`, `G3EraseDev5`).

`crossDS M K C` are the darts of `C` whose bond goes into `K`; `sgnCS` their net sign.  `PinnedS M K` is A3: some atom of `K` is
unbalanced, or some component of `M - K` adjacent to `K` receives nonzero net flux, or some atom of `K` has degree `< 4`.
`cEs = F(M - K) - F(M) + 1`; `circuitRank_eraseSet : χ(M) = χ(M-K) + e + ib - |K| + 1 - c`.
Not pinned (all degrees `4`, all fluxes `0`) gives `m + 1 ≤ e + ib - m + 1 - c`; always (connected `K`) `0 ≤ e + ib - m + 1 - c`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) (K : Finset V)

/-- The darts of `C` whose bond goes into `K`. -/
noncomputable def crossDS (C : Finset V) : Finset D :=
  Finset.univ.filter (fun x => M.atom x ∈ C ∧ M.atom (M.mate x) ∈ K)

/-- The net sign of the bonds between `K` and `C`. -/
noncomputable def sgnCS (C : Finset V) : ℝ := ∑ x ∈ crossDS M K C, M.dartSign x

/-- **`K` is pinned** (A3 of R29). -/
def PinnedS : Prop :=
  (∃ a ∈ K, M.outdeg a ≠ M.indeg a) ∨ (∃ a ∈ nbrS M K, sgnCS M K (cmpS M K a) ≠ 0) ∨ (∃ a ∈ K, M.deg a < 4)

/-- `F(M - K) - F(M) + 1`. -/
noncomputable def cEs : ℤ := ((eraseSet M K).numComponents : ℤ) - M.numComponents + 1

variable {M K}

theorem crossDS_ne_empty {a : V} (ha : a ∈ nbrS M K) : 1 ≤ (crossDS M K (cmpS M K a)).card := by
  obtain ⟨hmem, k, hk, x, hx1, hx2⟩ := mem_nbrS.1 ha
  refine Finset.card_pos.2 ⟨M.mate x, ?_⟩
  unfold crossDS
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, ?_⟩
  · rw [hx2]; exact mem_cmpS.2 ⟨hmem, Relation.EqvGen.refl _⟩
  · rw [M.mate_mate, hx1]; exact hk

theorem mem_crossDS_nbr {x : D} (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) (hx : M.atom (M.mate x) ∈ K)
    (hx' : M.atom x ∉ K) : M.atom x ∈ nbrS M K :=
  mem_nbrS.2 ⟨Finset.mem_sdiff.2 ⟨M.atom_mem _, hx'⟩, M.atom (M.mate x), hx, ⟨M.mate x, rfl, by rw [M.mate_mate]⟩⟩

theorem crossDS_disjoint {C C' : Finset V} (hC : C ∈ CsS M K) (hC' : C' ∈ CsS M K) (hne : C ≠ C') :
    Disjoint (crossDS M K C) (crossDS M K C') := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  unfold crossDS at hx hx'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
  unfold CsS at hC hC'
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hC
  obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hC'
  have h1 := (mem_cmpS.1 hx.1).2
  have h2 := (mem_cmpS.1 hx'.1).2
  exact hne ((cmpS_eq_of_sc h1).trans (cmpS_eq_of_sc h2).symm)

theorem biUnion_crossDS (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) :
    (CsS M K).biUnion (crossDS M K) =
      Finset.univ.filter (fun x => M.atom x ∉ K ∧ M.atom (M.mate x) ∈ K) := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨C, hC, hx⟩
    unfold crossDS at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    unfold CsS at hC
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hC
    exact ⟨(Finset.mem_sdiff.1 (mem_cmpS.1 hx.1).1).2, hx.2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨cmpS M K (M.atom x), ?_, ?_⟩
    · unfold CsS; exact Finset.mem_image.2 ⟨_, mem_crossDS_nbr hnl h2 h1, rfl⟩
    · unfold crossDS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨mem_cmpS.2 ⟨Finset.mem_sdiff.2 ⟨M.atom_mem _, h1⟩, Relation.EqvGen.refl _⟩, h2⟩

theorem card_cross_out (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) :
    (Finset.univ.filter (fun x : D => M.atom x ∉ K ∧ M.atom (M.mate x) ∈ K)).card = eDart M K := by
  unfold eDart
  refine Finset.card_bij (fun x _ => M.mate x) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [M.mate_mate]; exact ⟨hx.2, hx.1⟩
  · intro x _ y _ e; simpa [M.mate_mate] using congrArg M.mate e
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    refine ⟨M.mate y, ?_, M.mate_mate y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [M.mate_mate]; exact ⟨hy.2, hy.1⟩

theorem sum_csS_card (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) :
    ∑ C ∈ CsS M K, (crossDS M K C).card = eDart M K := by
  rw [← Finset.card_biUnion (fun C hC C' hC' hne => crossDS_disjoint hC hC' hne), biUnion_crossDS hnl]
  exact card_cross_out hnl

theorem card_crossS_even {C : Finset V} (h : sgnCS M K C = 0) : Even (crossDS M K C).card := by
  unfold sgnCS at h
  set T := crossDS M K C
  have hpn := Finset.card_filter_add_card_filter_not (s := T) (fun x => M.dartSign x = 1)
  have e1 : ∑ x ∈ T.filter (fun x => M.dartSign x = 1), M.dartSign x = ((T.filter fun x => M.dartSign x = 1).card : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    exact Finset.sum_congr rfl fun x hx => by simpa using (Finset.mem_filter.1 hx).2
  have e2 : ∑ x ∈ T.filter (fun x => ¬ M.dartSign x = 1), M.dartSign x = -((T.filter fun x => ¬ M.dartSign x = 1).card : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    have := (Finset.mem_filter.1 hx).2
    rcases dartSign_cases (M := M) x with h1 | h1
    · exact absurd h1 this
    · simp [h1]
  have h2 := Finset.sum_filter_add_sum_filter_not T (fun x => M.dartSign x = 1) (fun x => M.dartSign x)
  rw [e1, e2, h] at h2
  have : (T.filter fun x => M.dartSign x = 1).card = (T.filter fun x => ¬ M.dartSign x = 1).card := by
    exact_mod_cast (by linarith : ((T.filter fun x => M.dartSign x = 1).card : ℝ) = (T.filter fun x => ¬ M.dartSign x = 1).card)
  exact ⟨(T.filter fun x => M.dartSign x = 1).card, by omega⟩

/-- Without flux, every adjacent component of `M - K` receives at least two bonds. -/
theorem two_csS_le (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x))
    (h0 : ∀ a ∈ nbrS M K, sgnCS M K (cmpS M K a) = 0) : 2 * (CsS M K).card ≤ eDart M K := by
  have h2 : ∀ C ∈ CsS M K, 2 ≤ (crossDS M K C).card := by
    intro C hC
    unfold CsS at hC
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hC
    have hev := card_crossS_even (h0 a ha)
    have := crossDS_ne_empty ha
    obtain ⟨k, hk⟩ := hev
    omega
  have := Finset.card_nsmul_le_sum (CsS M K) (fun C => (crossDS M K C).card) 2 h2
  rw [sum_csS_card hnl] at this
  simpa [mul_comm] using this

theorem csS_card_le_eDart (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) : (CsS M K).card ≤ eDart M K := by
  have h1 : ∀ C ∈ CsS M K, 1 ≤ (crossDS M K C).card := by
    intro C hC
    unfold CsS at hC
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hC
    exact crossDS_ne_empty ha
  have := Finset.card_nsmul_le_sum (CsS M K) (fun C => (crossDS M K C).card) 1 h1
  rw [sum_csS_card hnl] at this
  simpa using this

/-- The degrees of the atoms of `K`: `e_K + 2 ib_K`. -/
theorem sum_deg_K (hK : K ⊆ M.atoms) : ∑ a ∈ K, M.deg a = eDart M K + intDart M K := by
  have key := Finset.card_eq_sum_card_fiberwise (f := M.atom)
    (s := Finset.univ.filter fun x : D => M.atom x ∈ K) (t := K) (fun x hx => by simpa using hx)
  have e1 : ∑ a ∈ K, M.deg a = (Finset.univ.filter fun x : D => M.atom x ∈ K).card := by
    rw [key]
    refine Finset.sum_congr rfl fun a ha => ?_
    unfold Molecule.deg Molecule.dartsAt
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact ⟨h ▸ ha, h⟩
    · intro h; exact h.2
  rw [e1]
  have := Finset.card_filter_add_card_filter_not (s := Finset.univ.filter fun x : D => M.atom x ∈ K)
    (fun x => M.atom (M.mate x) ∈ K)
  unfold eDart intDart
  rw [Finset.filter_filter, Finset.filter_filter] at this
  have h1 : (Finset.univ.filter fun x : D => M.atom x ∈ K ∧ M.atom (M.mate x) ∈ K) =
      Finset.univ.filter fun x : D => M.atom x ∈ K ∧ M.atom (M.mate x) ∈ K := rfl
  omega

theorem circuitRank_eraseSet (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) (hK : K ⊆ M.atoms) :
    ∃ ib : ℕ, intDart M K = 2 * ib ∧
      M.circuitRank = (eraseSet M K).circuitRank + (eDart M K : ℤ) + ib - K.card + 1 - cEs M K := by
  have h1 := card_darts_eq_two_bonds M
  have h2 := card_darts_eq_two_bonds (eraseSet M K)
  have h3 := card_edartS M K
  have h4 := tch_eq M K
  have h5 : (eraseSet M K).atoms.card + K.card = M.atoms.card := by
    show (M.atoms \ K).card + K.card = _
    rw [Finset.card_sdiff_of_subset hK]
    have := Finset.card_le_card hK
    omega
  have h6 : Fintype.card (EDartS M K) = Fintype.card (EDartS M K) := rfl
  have hev : Even (intDart M K) := by
    have : intDart M K + 2 * eDart M K + Fintype.card (EDartS M K) = Fintype.card D := by
      have := h3; rw [h4] at this; omega
    refine ⟨M.bonds.card - (eraseSet M K).bonds.card - eDart M K, ?_⟩
    have h2' : Fintype.card (EDartS M K) = 2 * (eraseSet M K).bonds.card := h2
    omega
  obtain ⟨ib, hib⟩ := hev
  refine ⟨ib, by omega, ?_⟩
  unfold Molecule.circuitRank cEs
  have h2' : Fintype.card (EDartS M K) = 2 * (eraseSet M K).bonds.card := h2
  have hb : (M.bonds.card : ℤ) = (eraseSet M K).bonds.card + eDart M K + ib := by
    have : intDart M K + 2 * eDart M K + Fintype.card (EDartS M K) = Fintype.card D := by
      have := h3; rw [h4] at this; omega
    omega
  have h5' : ((eraseSet M K).atoms.card : ℤ) + K.card = M.atoms.card := by exact_mod_cast h5
  omega

/-- If `K` is not pinned and the degrees are `≤ 4`: `m + 1 ≤ e + ib - m + 1 - c`. -/
theorem unpinned_rank (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) (hK : K ⊆ M.atoms) (hM4 : ∀ a ∈ M.atoms, M.deg a ≤ 4)
    {k₀ : V} (hk₀ : k₀ ∈ K) (hKc : ∀ k ∈ K, M.SameComponent k k₀) (hP : ¬ PinnedS M K) :
    ∃ ib : ℕ, intDart M K = 2 * ib ∧ (eDart M K : ℤ) + 2 * ib = 4 * K.card ∧
      (K.card : ℤ) + 1 ≤ (eDart M K : ℤ) + ib - K.card + 1 - cEs M K := by
  unfold PinnedS at hP
  push Not at hP
  obtain ⟨-, hflux, hdeg⟩ := hP
  obtain ⟨ib, hib, -⟩ := circuitRank_eraseSet hnl hK
  refine ⟨ib, hib, ?_, ?_⟩
  · have hs := sum_deg_K hK
    have : ∑ a ∈ K, M.deg a = ∑ _a ∈ K, 4 :=
      Finset.sum_congr rfl fun a ha => le_antisymm (hM4 a (hK ha)) (hdeg a ha)
    rw [this] at hs
    simp at hs
    omega
  · have hs := sum_deg_K hK
    have : ∑ a ∈ K, M.deg a = ∑ _a ∈ K, 4 :=
      Finset.sum_congr rfl fun a ha => le_antisymm (hM4 a (hK ha)) (hdeg a ha)
    rw [this] at hs
    simp at hs
    have h2 := two_csS_le hnl hflux
    have h3 := numComponents_eraseSet_le hK hk₀ hKc
    unfold cEs
    omega

/-- Connected `K` (`m ≤ ib + 1`): the rank drop is `≥ 0`. -/
theorem rank_drop_nonneg (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) (hK : K ⊆ M.atoms)
    {k₀ : V} (hk₀ : k₀ ∈ K) (hKc : ∀ k ∈ K, M.SameComponent k k₀) {ib : ℕ} (hconn : K.card ≤ ib + 1) :
    0 ≤ (eDart M K : ℤ) + ib - K.card + 1 - cEs M K := by
  have h1 := csS_card_le_eDart (M := M) (K := K) hnl
  have h3 := numComponents_eraseSet_le hK hk₀ hKc
  unfold cEs
  omega

end WaveTurbulence.FinalCountG3
