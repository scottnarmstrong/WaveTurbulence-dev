/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.ExitsTwo
public import WaveTurbulence.Foundations.FinalCount.BetaCutCount
public import WaveTurbulence.Foundations.CountLemmas.DotStrip
public import WaveTurbulence.Foundations.Counting.LatticeBox
import Mathlib.Tactic

/-! # Counting for a set attached by two bonds of opposite directions (DH23 L1967, DH21 Lemma 9.14)

Labels on the darts touching `Y` are the labels of the induced piece `N[Y]` together with the labels `k_x, k_y` of
the two exit bonds. `k_x - k_y` is fixed by the charges (boundary identity) and `|k_x|² - |k_y|²` lies in a window of
length `|Y| δ⁻¹ L^{-2γ}`; for `k_x ≠ k_y` the number of choices of `k_x` is a strip count in the unit ball.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **Slab count in the unit ball** (DH23 Lemma A.3(1) shape, for one vector): `K` lattice points in a unit ball
whose dot product with a vector of norm `≥ L⁻¹` lies in a window of half-width `τ''`. -/
theorem card_slab_le {d : ℕ} (hd : 0 < d) (K : Finset (Fin d → ℤ)) {L τ'' : ℝ} (hL : 1 ≤ L) (hτ : 0 ≤ τ'')
    (a r : Mom d) (β : ℝ) (hr : K.Nonempty → L⁻¹ ≤ ‖r‖)
    (hball : ∀ n ∈ K, ‖latticePoint L n - a‖ ≤ 1)
    (hstrip : ∀ n ∈ K, |inner ℝ r (latticePoint L n) - β| ≤ τ'') :
    (K.card : ℝ) ≤ min ((2 * L + 1) ^ d) ((2 * L + 1) ^ (d - 1) * (2 * d * τ'' * L ^ 2 + 1)) := by
  have hLp : 0 < L := by linarith
  refine le_min ?_ ?_
  · have h := Counting.card_le_of_coordinate_bounds K (fun i => L * a i) (L := L * 1) (by positivity)
      (fun n hn i => CountLemmas.coordinate_bound_of_ball hLp a n (hball n hn) i)
    simpa using h
  · rcases K.eq_empty_or_nonempty with rfl | hK
    · simp only [card_empty, Nat.cast_zero]; positivity
    · have h := CountLemmas.card_dot_strip_ball_norm_le hd K hLp (zero_le_one) hτ (inv_pos.mpr hLp) a r β
        (hr hK) hball hstrip
      have e : 2 * (d : ℝ) * τ'' * L / L⁻¹ = 2 * d * τ'' * L ^ 2 := by
        field_simp
      simpa [e] using h

namespace Exits2
variable {N : Molecule V D} (T : Exits2 N)

theorem sign_y (hout : N.out T.x ≠ N.out T.y) : N.dartSign T.y = -N.dartSign T.x := by
  unfold Molecule.dartSign
  cases hx : N.out T.x <;> cases hy : N.out T.y <;> simp_all

omit [DecidableEq D] in
theorem sign_sq (z : D) : N.dartSign z * N.dartSign z = 1 := by
  unfold Molecule.dartSign; split_ifs <;> norm_num

omit [DecidableEq D] in
theorem sign_ne_zero (z : D) : N.dartSign z ≠ 0 := by
  unfold Molecule.dartSign; split_ifs <;> norm_num

theorem charge_eq (hout : N.out T.x ≠ N.out T.y) {d : ℕ} {L : ℝ} {c : V → Mom d} {κ : D → (Fin d → ℤ)}
    (hκ : N.IsDecoration L 0 c κ) :
    ∑ v ∈ T.Y, c v = N.dartSign T.x • (Molecule.kvec L 0 κ T.x - Molecule.kvec L 0 κ T.y) := by
  rw [sum_charges_eq_cross hκ T.sub, T.cross, sum_pair T.ne, T.sign_y hout, smul_sub, neg_smul, sub_eq_add_neg]

theorem energy_eq (hout : N.out T.x ≠ N.out T.y) {d : ℕ} {L : ℝ} {κ : D → (Fin d → ℤ)}
    (hκ : ∀ z, κ (N.mate z) = κ z) :
    ∑ v ∈ T.Y, N.Gamma L 0 κ v =
      N.dartSign T.x * (‖Molecule.kvec L 0 κ T.x‖ ^ 2 - ‖Molecule.kvec L 0 κ T.y‖ ^ 2) := by
  rw [sum_gamma_eq_cross N L 0 hκ T.Y, T.cross, sum_pair T.ne, T.sign_y hout]
  ring

/-- Labels of the two exits are determined by one of them and the charges. -/
theorem label_y_eq (hout : N.out T.x ≠ N.out T.y) {d : ℕ} {L : ℝ} (hL : L ≠ 0) {c : V → Mom d}
    {κ κ' : D → (Fin d → ℤ)} (hκ : N.IsDecoration L 0 c κ) (hκ' : N.IsDecoration L 0 c κ')
    (hx : κ T.x = κ' T.x) : κ T.y = κ' T.y := by
  have h := (T.charge_eq hout hκ).symm.trans (T.charge_eq hout hκ')
  have hs : N.dartSign T.x ≠ 0 := sign_ne_zero T.x
  have h2 := smul_right_injective (Mom d) hs h
  have hxx : Molecule.kvec L 0 κ T.x = Molecule.kvec L 0 κ' T.x := by simp [Molecule.kvec, hx]
  rw [hxx] at h2
  have h3 := sub_right_injective h2
  simp only [Molecule.kvec, zero_add] at h3
  exact latticePoint_injective hL h3

/-- The exit darts are the only removed darts at an atom of `Y`. -/
theorem residual_eq {d : ℕ} {L : ℝ} {c : V → Mom d} {β : V → ℝ} {κ κ' : D → (Fin d → ℤ)}
    (hx : κ T.x = κ' T.x) (hy : κ T.y = κ' T.y) {v : V} (hv : v ∈ T.Y) :
    Degen.residualMomentum N (N.atoms \ T.Y) L 0 c κ v = Degen.residualMomentum N (N.atoms \ T.Y) L 0 c κ' v ∧
      Degen.residualEnergy N (N.atoms \ T.Y) L 0 β κ v = Degen.residualEnergy N (N.atoms \ T.Y) L 0 β κ' v := by
  have hz : ∀ z ∈ Degen.removedDartsAt N (N.atoms \ T.Y) v, κ z = κ' z := by
    intro z hz
    simp only [Degen.removedDartsAt, Molecule.dartsAt, mem_filter, mem_univ, true_and, mem_sdiff] at hz
    rcases T.eq_of_cross (z := z) (hz.1 ▸ hv) hz.2.2 with rfl | rfl
    · exact hx
    · exact hy
  constructor
  · unfold Degen.residualMomentum
    congr 1
    exact sum_congr rfl fun z h => by simp only [Molecule.kvec, hz z h]
  · unfold Degen.residualEnergy
    congr 1
    exact sum_congr rfl fun z h => by simp only [Molecule.kvec, hz z h]


theorem kvec_sub_norm_ge {d : ℕ} {L : ℝ} (hL : 0 < L) {κ : D → (Fin d → ℤ)} (h : κ T.x ≠ κ T.y) :
    L⁻¹ ≤ ‖Molecule.kvec L 0 κ T.x - Molecule.kvec L 0 κ T.y‖ := by
  simp only [Molecule.kvec, zero_add]
  rw [← latticePoint_sub']
  exact inv_le_norm_latticePoint hL (sub_ne_zero.mpr h)

/-- **Counting inequality** for a set attached by two bonds of opposite directions, with `κ_x ≠ κ_y`. -/
theorem countEFree_le_bi (hout : N.out T.x ≠ N.out T.y) {d : ℕ} (hd : 0 < d) {L γ δ η : ℝ} (hL : 1 ≤ L)
    (hδ : 0 < δ) (P : Finset V → ℝ) (Adm : (D → (Fin d → ℤ)) → Prop)
    (hAdm : ∀ κ, Adm κ → lgAdm N L γ η P κ ∧ κ T.x ≠ κ T.y) :
    ∃ n : ℕ, (n : ℝ) ≤ min ((2 * L + 1) ^ d)
        ((2 * L + 1) ^ (d - 1) * (d * T.Y.card * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2 + 1)) ∧
      MoleProp.countEFree N L γ δ (0 : Mom d) Adm ≤ (n : ℕ∞) *
        MoleProp.countEFree (piece N T.Y) L γ δ (0 : Mom d) (lgAdm (piece N T.Y) L γ η P) *
        MoleProp.countEFree (Degen.eraseAtoms N T.Y) L γ δ (0 : Mom d)
          (MoleProp.erasedFreeAdmissibility N T.Y Adm) := by
  classical
  have hLp : 0 < L := by linarith
  set τ := δ⁻¹ * L ^ (-2 * γ) with hτdef
  have hτ : 0 < τ := by positivity
  set B := min ((2 * L + 1) ^ d) ((2 * L + 1) ^ (d - 1) * (d * T.Y.card * τ * L ^ 2 + 1)) with hB
  have hB0 : 0 ≤ B := le_min (by positivity) (by positivity)
  refine ⟨⌊B⌋₊, Nat.floor_le hB0, ?_⟩
  conv_lhs => rw [MoleProp.countEFree]
  refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  set A := {κ : D → (Fin d → ℤ) | N.IsDecoration L 0 c κ ∧ N.IsRestricted L γ δ 0 β k0 κ ∧ Adm κ} with hA
  have hAfin : A.Finite := (Mole.finite_restricted N hLp γ δ 0 β k0).subset fun _ h => h.2.1
  have hmain := MoleProp.encard_le_deletedImage_mul_post N T.Y hLp γ δ 0 Adm c β k0 hk0
  refine hmain.trans (mul_le_mul' ?_ le_rfl)
  rcases A.eq_empty_or_nonempty with hA0 | ⟨κ₀, hκ₀⟩
  · show ((MoleProp.deletedLabels N T.Y '' A).ncard : ℕ∞) ≤ _
    rw [hA0, Set.image_empty, Set.ncard_empty, Nat.cast_zero]
    exact bot_le
  -- the exit labels
  set K1 : Finset (Fin d → ℤ) := hAfin.toFinset.image (fun κ => κ T.x) with hK1
  have hK1mem : ∀ k ∈ K1, ∃ κ ∈ A, κ T.x = k := by
    intro k hk
    obtain ⟨κ, hκ, rfl⟩ := mem_image.mp hk
    exact ⟨κ, hAfin.mem_toFinset.mp hκ, rfl⟩
  -- the strip data
  set ζ := N.dartSign T.x with hζ
  have hζ2 : ζ * ζ = 1 := sign_sq T.x
  set r' : Mom d := ζ • ∑ v ∈ T.Y, c v with hr'
  set β' : ℝ := (‖r'‖ ^ 2 + ζ * ∑ v ∈ T.Y, β v) / 2 with hβ'
  have hr'eq : ∀ κ ∈ A, r' = Molecule.kvec L 0 κ T.x - Molecule.kvec L 0 κ T.y := by
    intro κ hκ
    rw [hr', T.charge_eq hout hκ.1, smul_smul, hζ2, one_smul]
  have hK1strip : ∀ n ∈ K1, |inner ℝ r' (latticePoint L n) - β'| ≤ T.Y.card * τ / 2 := by
    intro n hn
    obtain ⟨κ, hκ, rfl⟩ := hK1mem n hn
    have hr := hr'eq κ hκ
    have hkx : Molecule.kvec L 0 κ T.x = latticePoint L (κ T.x) := by simp [Molecule.kvec]
    have hky : Molecule.kvec L 0 κ T.y = Molecule.kvec L 0 κ T.x - r' := by rw [hr]; abel
    have hΓ := T.energy_eq (L := L) hout hκ.1.1
    have hnorm : ‖Molecule.kvec L 0 κ T.x‖ ^ 2 - ‖Molecule.kvec L 0 κ T.y‖ ^ 2 =
        2 * inner ℝ r' (Molecule.kvec L 0 κ T.x) - ‖r'‖ ^ 2 := by
      rw [hky, norm_sub_sq_real, real_inner_comm]; ring
    have hwin : |∑ v ∈ T.Y, N.Gamma L 0 κ v - ∑ v ∈ T.Y, β v| ≤ T.Y.card * τ := by
      rw [← sum_sub_distrib]
      refine (abs_sum_le_sum_abs _ _).trans ?_
      rw [← nsmul_eq_mul]
      exact sum_le_card_nsmul _ _ _ fun v hv => hκ.2.1.1 v (T.sub hv)
    rw [hΓ, hnorm] at hwin
    have h2 : |2 * inner ℝ r' (Molecule.kvec L 0 κ T.x) - ‖r'‖ ^ 2 - ζ * ∑ v ∈ T.Y, β v| ≤ T.Y.card * τ := by
      have hs : ζ * (ζ * (2 * inner ℝ r' (Molecule.kvec L 0 κ T.x) - ‖r'‖ ^ 2) - ∑ v ∈ T.Y, β v) =
          2 * inner ℝ r' (Molecule.kvec L 0 κ T.x) - ‖r'‖ ^ 2 - ζ * ∑ v ∈ T.Y, β v := by
        have : ζ * ζ = 1 := hζ2
        linear_combination (2 * inner ℝ r' (Molecule.kvec L 0 κ T.x) - ‖r'‖ ^ 2) * this
      have habs : |ζ| = 1 := by
        have : |ζ| * |ζ| = 1 := by rw [← abs_mul, hζ2]; simp
        nlinarith [abs_nonneg ζ]
      rw [← hs, abs_mul, habs, one_mul]
      exact hwin
    rw [hkx] at h2
    have : inner ℝ r' (latticePoint L (κ T.x)) - β' =
        (2 * inner ℝ r' (latticePoint L (κ T.x)) - ‖r'‖ ^ 2 - ζ * ∑ v ∈ T.Y, β v) / 2 := by
      rw [hβ']; ring
    rw [this, abs_div, abs_two]
    linarith
  have hK1ball : ∀ n ∈ K1, ‖latticePoint L n - k0 T.x‖ ≤ 1 := by
    intro n hn
    obtain ⟨κ, hκ, rfl⟩ := hK1mem n hn
    have := hκ.2.1.2 T.x
    simpa [Molecule.kvec] using this
  have hK1nz : K1.Nonempty → L⁻¹ ≤ ‖r'‖ := by
    rintro ⟨n, hn⟩
    obtain ⟨κ, hκ, rfl⟩ := hK1mem n hn
    rw [hr'eq κ hκ]
    exact T.kvec_sub_norm_ge hLp (hAdm κ hκ.2.2).2
  have hK1card : (K1.card : ℝ) ≤ B := by
    have h := card_slab_le hd K1 hL (by positivity : (0 : ℝ) ≤ T.Y.card * τ / 2) (k0 T.x) r' β' hK1nz
      hK1ball hK1strip
    refine h.trans (le_of_eq ?_)
    rw [hB]
    congr 2
    ring
  have hK1nat : K1.card ≤ ⌊B⌋₊ := Nat.le_floor hK1card
  let refk : (Fin d → ℤ) → (D → (Fin d → ℤ)) := fun k =>
    if h : ∃ κ ∈ A, κ T.x = k then h.choose else κ₀
  have hrefk : ∀ k ∈ K1, refk k ∈ A ∧ refk k T.x = k := by
    intro k hk
    have h := hK1mem k hk
    simp only [refk, dif_pos h]
    exact h.choose_spec
  let pr1 : (D → (Fin d → ℤ)) → (Fin d → ℤ) × (Degen.RetainedDart N (N.atoms \ T.Y) → (Fin d → ℤ)) :=
    fun κ => (κ T.x, fun z => κ z.val)
  let Φ : (Fin d → ℤ) × (Degen.RetainedDart N (N.atoms \ T.Y) → (Fin d → ℤ)) →
      (MoleProp.DeletedDart N T.Y → (Fin d → ℤ)) := fun q z =>
    if h : N.atom z.val ∈ T.Y ∧ N.atom (N.mate z.val) ∈ T.Y then q.2 (pieceDart N T.Y z.val h)
    else if z.val = T.x ∨ z.val = N.mate T.x then q.1 else (refk q.1) T.y
  have himg : MoleProp.deletedLabels N T.Y '' A = Φ '' (pr1 '' A) := by
    rw [Set.image_image]
    refine Set.image_congr fun κ hκ => ?_
    funext ⟨z, hz⟩
    simp only [Φ, pr1, MoleProp.deletedLabels]
    split_ifs with h h2
    · rfl
    · rcases h2 with rfl | rfl
      · rfl
      · exact hκ.1.1 T.x
    · have hk : κ T.x ∈ K1 := mem_image.mpr ⟨κ, hAfin.mem_toFinset.mpr hκ, rfl⟩
      obtain ⟨hrA, hrx⟩ := hrefk _ hk
      have hy := T.label_y_eq hout hLp.ne' hκ.1 hrA.1 hrx.symm
      rcases T.dart_cases z with h3 | h3 | rfl | rfl | rfl | rfl
      · exact absurd h3 h
      · exact absurd h3 (by simpa [not_and_or] using hz)
      · exact absurd (Or.inl rfl) h2
      · exact hy
      · exact absurd (Or.inr rfl) h2
      · rw [hκ.1.1 T.y]; exact hy
  let E : (Fin d → ℤ) → Set (Degen.RetainedDart N (N.atoms \ T.Y) → (Fin d → ℤ)) := fun k =>
    {p | (piece N T.Y).IsDecoration L 0 (Degen.residualMomentum N (N.atoms \ T.Y) L 0 c (refk k)) p ∧
      (piece N T.Y).IsRestricted L γ δ 0 (Degen.residualEnergy N (N.atoms \ T.Y) L 0 β (refk k))
        (fun z => k0 z.val) p ∧ lgAdm (piece N T.Y) L γ η P p}
  have hsub : pr1 '' A ⊆ ⋃ k ∈ K1, (fun p => (k, p)) '' E k := by
    rintro _ ⟨κ, hκ, rfl⟩
    have hk : κ T.x ∈ K1 := mem_image.mpr ⟨κ, hAfin.mem_toFinset.mpr hκ, rfl⟩
    obtain ⟨hrA, hrx⟩ := hrefk _ hk
    have hy := T.label_y_eq hout hLp.ne' hκ.1 hrA.1 hrx.symm
    have hres := fun (v : V) (hv : v ∈ T.Y) =>
      T.residual_eq (c := c) (β := β) (L := L) (κ := κ) (κ' := refk (κ T.x)) hrx.symm hy hv
    have hdec := Degen.isDecoration_eraseAtoms N (N.atoms \ T.Y) hκ.1
    have hrst := Degen.isRestricted_eraseAtoms N (N.atoms \ T.Y) hκ.2.1
    refine Set.mem_biUnion hk ⟨fun z => κ z.val, ⟨⟨hdec.1, fun v hv => ?_⟩, ⟨fun v hv => ?_, hrst.2⟩, ?_⟩, rfl⟩
    · have hvY : v ∈ T.Y := by rw [← piece_atoms T.sub]; exact hv
      rw [← (hres v hvY).1]; exact hdec.2 v hv
    · have hvY : v ∈ T.Y := by rw [← piece_atoms T.sub]; exact hv
      rw [← (hres v hvY).2]; exact hrst.1 v hv
    · exact ⟨MoleProp.largeGap_erase N L γ η 0 _ (hAdm κ hκ.2.2).1.1,
        MoleProp.cellGapRestriction_erase N L 0 _ P _ (hAdm κ hκ.2.2).1.2⟩
  rw [himg]
  have hSfin : (pr1 '' A).Finite := hAfin.image pr1
  calc ((Φ '' (pr1 '' A)).ncard : ℕ∞) ≤ ((pr1 '' A).ncard : ℕ∞) := by
        exact_mod_cast Set.ncard_image_le hSfin
    _ = (pr1 '' A).encard := hSfin.cast_ncard_eq
    _ ≤ (⋃ k ∈ K1, (fun p => (k, p)) '' E k).encard := Set.encard_mono hsub
    _ ≤ ∑ k ∈ K1, ((fun p => (k, p)) '' E k).encard := encard_biUnion_le _ _
    _ = ∑ k ∈ K1, (E k).encard := by
        refine sum_congr rfl fun k _ => ?_
        exact (Prod.mk_right_injective k).injOn.encard_image
    _ ≤ ∑ _k ∈ K1, MoleProp.countEFree (piece N T.Y) L γ δ (0 : Mom d) (lgAdm (piece N T.Y) L γ η P) :=
        sum_le_sum fun k hk => by
          obtain ⟨hrA, _⟩ := hrefk k hk
          exact MoleProp.encard_le_countEFree (piece N T.Y) L γ δ 0 _ _ _ (fun z => k0 z.val)
            (fun z => hk0 z.val) |> fun h => le_trans (le_of_eq rfl) h
    _ = (K1.card : ℕ∞) * MoleProp.countEFree (piece N T.Y) L γ δ (0 : Mom d) (lgAdm (piece N T.Y) L γ η P) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul' (by exact_mod_cast hK1nat) le_rfl

end Exits2

end WaveTurbulence.FinalCountG8
