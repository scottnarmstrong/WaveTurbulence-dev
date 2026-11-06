/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Assembly3
/-! # The number of classes (S3c) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.CoarseSpliced
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDecay Finset
open scoped Classical

variable {w d : ℕ} {G : Garden w} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The lattice points of a coset in a unit ball form a finite set of at most `(2L+1)^d` points. -/
theorem card_coset_ball_le {L : ℝ} (hL : 0 < L) (base center : Mom d) :
    ((finite_coset_unit_ball hL base center).toFinset.card : ℝ) ≤ (2 * L + 1) ^ d := by
  have hsub : (finite_coset_unit_ball hL base center).toFinset ⊆
      Fintype.piFinset (fun j : Fin d => Finset.Icc ⌈L * (center j - base j - 1)⌉ ⌊L * (center j - base j + 1)⌋) := by
    intro n hn
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hn
    rw [Fintype.mem_piFinset]
    intro j
    have hj : |base j + (n j : ℝ) / L - center j| ≤ 1 := by
      have hh := (PiLp.norm_apply_le (base + latticePoint L n - center) j).trans hn
      simpa only [PiLp.sub_apply, PiLp.add_apply, latticePoint, Real.norm_eq_abs] using hh
    rw [abs_le] at hj
    rw [Finset.mem_Icc]
    constructor
    · rw [Int.ceil_le]
      have : (-1 : ℝ) ≤ base j + (n j : ℝ) / L - center j := hj.1
      have h2 : L * (center j - base j - 1) ≤ n j := by
        have := mul_le_mul_of_nonneg_left this hL.le
        have e : L * (base j + (n j : ℝ) / L - center j) = L * (base j - center j) + n j := by
          field_simp
          ring
        nlinarith
      exact h2
    · rw [Int.le_floor]
      have : base j + (n j : ℝ) / L - center j ≤ 1 := hj.2
      have h2 : (n j : ℝ) ≤ L * (center j - base j + 1) := by
        have := mul_le_mul_of_nonneg_left this hL.le
        have e : L * (base j + (n j : ℝ) / L - center j) = L * (base j - center j) + n j := by
          field_simp
          ring
        nlinarith
      exact h2
  have h1 := Finset.card_le_card hsub
  rw [Fintype.card_piFinset] at h1
  have h2 : ((∏ j : Fin d, (Finset.Icc ⌈L * (center j - base j - 1)⌉ ⌊L * (center j - base j + 1)⌋).card : ℕ) : ℝ)
      ≤ (2 * L + 1) ^ d := by
    push_cast
    calc ∏ j : Fin d, (((Finset.Icc ⌈L * (center j - base j - 1)⌉ ⌊L * (center j - base j + 1)⌋).card : ℕ) : ℝ)
        ≤ ∏ _j : Fin d, (2 * L + 1) := by
          refine Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg _) (fun j _ => ?_)
          rw [Int.card_Icc]
          have hc := Int.ceil_lt_add_one (L * (center j - base j - 1))
          have hf := Int.floor_le (L * (center j - base j + 1))
          have h3 : ((⌊L * (center j - base j + 1)⌋ + 1 - ⌈L * (center j - base j - 1)⌉ : ℤ) : ℝ) ≤ 2 * L + 1 := by
            push_cast
            have := Int.le_ceil (L * (center j - base j - 1))
            nlinarith
          have h4 : (((⌊L * (center j - base j + 1)⌋ + 1 - ⌈L * (center j - base j - 1)⌉).toNat : ℕ) : ℝ) ≤ 2 * L + 1 := by
            by_cases hnn : 0 ≤ (⌊L * (center j - base j + 1)⌋ + 1 - ⌈L * (center j - base j - 1)⌉)
            · have : (((⌊L * (center j - base j + 1)⌋ + 1 - ⌈L * (center j - base j - 1)⌉).toNat : ℕ) : ℤ) =
                  ⌊L * (center j - base j + 1)⌋ + 1 - ⌈L * (center j - base j - 1)⌉ := Int.toNat_of_nonneg hnn
              have h5 : (((⌊L * (center j - base j + 1)⌋ + 1 - ⌈L * (center j - base j - 1)⌉).toNat : ℕ) : ℝ) =
                  ((⌊L * (center j - base j + 1)⌋ + 1 - ⌈L * (center j - base j - 1)⌉ : ℤ) : ℝ) := by
                exact_mod_cast this
              rw [h5]; exact h3
            · rw [Int.toNat_of_nonpos (not_le.mp hnn).le]
              simp; linarith
          exact h4
      _ = (2 * L + 1) ^ d := by simp
  calc ((finite_coset_unit_ball hL base center).toFinset.card : ℝ) ≤ ((∏ j : Fin d, (Finset.Icc ⌈L * (center j - base j - 1)⌉ ⌊L * (center j - base j + 1)⌋).card : ℕ) : ℝ) := by
        exact_mod_cast h1
    _ ≤ _ := h2


omit [Fintype ι] [DecidableEq ι] in
lemma intDart_mate (S : ι → Finset (GBranch G.tree)) (x : GardenDart G) :
    IntDart S (G.molecule.mate x) ↔ IntDart S x := by
  have key : ∀ y, IntDart S y → IntDart S (G.molecule.mate y) := by
    rintro y ⟨i, hi⟩
    have hi' : G.molecule.atom y ∈ S i ∧ G.molecule.atom (G.molecule.mate y) ∈ S i := hi
    exact ⟨i, ⟨hi'.2, by rw [G.molecule.mate_mate]; exact hi'.1⟩⟩
  constructor
  · intro h
    have := key _ h
    rwa [G.molecule.mate_mate] at this
  · exact key x

lemma mate_mem_bonds_of_notMem (x : GardenDart G) (hx : x ∉ G.molecule.bonds) :
    G.molecule.mate x ∈ G.molecule.bonds := by
  simp only [Molecule.bonds, Finset.mem_filter, Finset.mem_univ, true_and, G.molecule.out_mate] at hx ⊢
  simpa using hx

theorem card_intDart_bonds (S : ι → Finset (GBranch G.tree)) (hS : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (k : ι → ℕ) (hk : ∀ i, (G.molecule.bonds.filter (G.molecule.InGroup (S i))).card = k i) :
    (G.molecule.bonds.filter (IntDart S)).card = ∑ i, k i := by
  have : G.molecule.bonds.filter (IntDart S) =
      univ.biUnion (fun i => G.molecule.bonds.filter (G.molecule.InGroup (S i))) := by
    ext x
    simp only [mem_filter, mem_biUnion, mem_univ, true_and, IntDart]
    constructor
    · rintro ⟨hb, i, hi⟩; exact ⟨i, hb, hi⟩
    · rintro ⟨i, hb, hi⟩; exact ⟨hb, i, hi⟩
  rw [this, Finset.card_biUnion]
  · exact Finset.sum_congr rfl (fun i _ => hk i)
  · intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    simp only [mem_filter] at hx hx'
    exact hij (inGroup_unique S hS i j x hx.2 hx'.2)

theorem card_classes_le (hP : G.IsPlain) (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D)
    (S : ι → Finset (GBranch G.tree)) (hS : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    {L : ℝ} (hL : 0 < L) (γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (k : ι → ℕ) (hk : ∀ i, (G.molecule.bonds.filter (G.molecule.InGroup (S i))).card = k i) :
    ((((finite_momAmp_support G hP D hD hL γ η base roots).toFinset.image (kappa S)).card : ℕ) : ℝ) ≤
      (2 * L + 1) ^ (d * (G.molecule.bonds.card - ∑ i, k i)) := by
  set Zsupp := (finite_momAmp_support G hP D hD hL γ η base roots).toFinset with hZs
  have hrc : (G.molecule.bonds.filter (fun x => ¬ IntDart S x)).card =
      G.molecule.bonds.card - ∑ i, k i := by
    rw [← card_intDart_bonds S hS k hk]
    have := Finset.card_filter_add_card_filter_not (s := G.molecule.bonds) (IntDart S)
    omega
  set restB := G.molecule.bonds.filter (fun x => ¬ IntDart S x) with hrestB
  let ball : GardenDart G → Finset (Fin d → ℤ) :=
    fun x => (finite_coset_unit_ball hL base (D.center x)).toFinset
  let ψ : (GardenDart G → (Fin d → ℤ)) → (∀ x : restB, Fin d → ℤ) := fun c x => c x.1
  have hmaps : ∀ c ∈ Zsupp.image (kappa S), ψ c ∈ Fintype.piFinset (fun x : restB => ball x.1) := by
    intro c hc
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc
    rw [Fintype.mem_piFinset]
    intro x
    have hxb := (Finset.mem_filter.mp x.2)
    have hm : splicedMomentumAmplitude G D L γ η base z.1 ≠ 0 := (Set.Finite.mem_toFinset _).mp hz
    have hball := (splicedMomentumAmplitude_support G D hD L γ η base z.1 hm).2.2 x.1 hxb.1
    simp only [ψ, kappa, ite_eq_right hxb.2, ball, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact hball
  have hinj : Set.InjOn ψ (Zsupp.image (kappa S) : Set (GardenDart G → (Fin d → ℤ))) := by
    intro c hc c' hc' h
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hc)
    obtain ⟨z', -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hc')
    funext x
    by_cases hx : IntDart S x
    · simp [kappa, hx]
    · by_cases hxb : x ∈ G.molecule.bonds
      · exact congrFun h ⟨x, Finset.mem_filter.mpr ⟨hxb, hx⟩⟩
      · have hmb := mate_mem_bonds_of_notMem x hxb
        have hmx : ¬ IntDart S (G.molecule.mate x) := fun hh => hx ((intDart_mate S x).mp hh)
        have h1 := congrFun h ⟨G.molecule.mate x, Finset.mem_filter.mpr ⟨hmb, hmx⟩⟩
        simp only [ψ, kappa, ite_eq_right hmx] at h1
        simp only [kappa, ite_eq_right hx]
        rw [← bondIndex_mate z x, ← bondIndex_mate z' x]
        exact h1
  have hcard := Finset.card_le_card_of_injOn ψ hmaps hinj
  rw [Fintype.card_piFinset] at hcard
  have hr : (((Zsupp.image (kappa S)).card : ℕ) : ℝ) ≤ ∏ x : restB, ((ball x.1).card : ℝ) := by
    exact_mod_cast hcard
  refine hr.trans ?_
  calc ∏ x : restB, ((ball x.1).card : ℝ) ≤ ∏ _x : restB, (2 * L + 1) ^ d :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
          (fun x _ => card_coset_ball_le hL base (D.center x.1))
    _ = (2 * L + 1) ^ (d * (G.molecule.bonds.card - ∑ i, k i)) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe, hrc, ← pow_mul, mul_comm]

end WaveTurbulence.CoarseSpliced
