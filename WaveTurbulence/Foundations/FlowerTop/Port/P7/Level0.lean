/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.Level1Est
/-! FLOWER-P7: the irreducible width-six piece (minimal closed block of tree `0` is everything). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset LGSpine

/-- The irreducible width-six carrier. -/
def Irr6 (P : WTParams) (p N : ℕ) (kind : TreeKind) : Set (LayeredGarden (2 * 3)) :=
  {y | y ∈ Y6Set P p N kind ∧ IrrAt y.garden 0}

theorem Irr6_finite (P : WTParams) (p N : ℕ) (kind : TreeKind) : (Irr6 P p N kind).Finite :=
  (Y6Set_finite P p N kind).subset fun _ h => h.1

theorem minimalAt_univ_iff (G : Garden (2 * 3)) (hG : G.IsPlain) : MinimalAt G 0 Finset.univ ↔ IrrAt G 0 := by
  constructor
  · rintro ⟨-, -, h⟩ T hT hi
    exact h T hT hi (Finset.subset_univ _)
  · intro h
    exact ⟨Finset.mem_univ _, closedTrees_univ G hG, fun T hT hi _ => h T hT hi⟩

open scoped Classical in
theorem Irr6_slice_eq (P : WTParams) (p N : ℕ) (kind : TreeKind) (d : ℕ × (Fin (2 * 3) → ℕ))
    (hd : d.1 + 2 = N) (hv : VecKindOK (P.N (p + 1)) kind d.2) (hvle : ∀ i, d.2 i ≤ P.N (p + 1)) :
    (Irr6_finite P p N kind).toFinset.filter (fun y => compData p y = d) =
      (gardenSet P p d.1 3 (fun i => childSig i)).filter (fun LG => ∀ j, LG.topOrder p j = d.2 j) := by
  ext LA
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, gardenSet, Irr6, Y6Set, Set.mem_ofPred_eq, compData,
    Prod.ext_iff]
  simp only [Nat.add_sub_cancel]
  constructor
  · rintro ⟨⟨⟨hs, ⟨hpl, hcr, hat, hord, hvk⟩⟩, hirr⟩, hord', hvec⟩
    refine ⟨⟨⟨hpl, Or.inl ⟨by omega, (irreducible_iff_irrAt LA.garden hpl 0).2 hirr⟩, hcr⟩,
      ⟨fun j => ?_, hat⟩, funext hs, hord'⟩, fun j => congrFun hvec j⟩
    rw [congrFun hvec j]; exact hvle j
  · rintro ⟨⟨⟨hpl, hir, hcr⟩, htr, hs, hord⟩, hvec⟩
    rcases hir with ⟨-, hirr⟩ | ⟨h2, -⟩
    · refine ⟨⟨⟨fun c => congrFun hs c, ⟨hpl, hcr, htr.2, by omega, ?_⟩⟩,
        (irreducible_iff_irrAt LA.garden hpl 0).1 hirr⟩, hord, funext hvec⟩
      have : (fun i => LA.topOrder p i) = d.2 := funext hvec
      rw [this]; exact hv
    · omega

theorem VecKindOK.le {Ntr : ℕ} {kind : TreeKind} {v : Fin (2 * 3) → ℕ} (h : VecKindOK Ntr kind v)
    (c : Fin (2 * 3)) : v c ≤ Ntr := by
  rw [← idx_jOf_iOf c]
  cases kind with
  | tr =>
    have h1 := h (jOf c)
    have : v (idx (jOf c) (iOf c)) ≤ ∑ i : Fin 3, v (idx (jOf c) i) :=
      Finset.single_le_sum (f := fun i : Fin 3 => v (idx (jOf c) i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    omega
  | L0 => exact (h (jOf c)).2 (iOf c)

open scoped Classical in
/-- **Bound for the irreducible width-six piece.** -/
theorem piece0_norm_le (C₀ : ℕ) (P : WTParams) (G : LGContext C₀ P) {p N : ℕ} (hp : p < P.D)
    (hN : N ≤ P.N (p + 1) ^ 4) (kind : TreeKind) (Rr : ℕ → Mom P.d → ℝ) (hRr : RemainderBound P Rr p)
    (hmmax : 3 ≤ 10 * P.R (p + 1)) (n : Fin (2 * 3) → (Fin P.d → ℤ)) (k : Mom P.d) (tt : Fin (2 * 3) → ℝ)
    (htt : ∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1))
    (hnum : ∀ N' ≤ P.N (p + 1) ^ 4, ((P.d : ℝ) + 1) ^ (4 * 3 * P.Lambda (p + 1)) *
      gardenT P G.Cφ p 3 N' ^ (8 * 3 * P.Lambda (p + 1)) * (2 * P.C₁) ^ (N' + 3) * P.δ ^ (6 * P.ν * N') *
      P.L ^ (-P.η ^ 7) * P.L ^ (-((3 : ℕ) - 1 : ℝ) / 70) ≤ 1) :
    ‖∑ᶠ y ∈ Irr6 P p N kind,
        kernelKgen P.L P.γ P.δ (inputsF P Rr) y (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k n 0‖ ≤
      ∑ d ∈ (Irr6_finite P p N kind).toFinset.image (compData p),
        jbrProdAt P.L k n ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (-(((3 : ℕ) : ℝ) - 1) / 4) *
          P.δ ^ (2 * P.ν * d.1) := by
  rw [finsum_mem_eq_finite_toFinset_sum _ (Irr6_finite P p N kind)]
  rw [← Finset.sum_fiberwise_of_maps_to (s := (Irr6_finite P p N kind).toFinset)
    (t := (Irr6_finite P p N kind).toFinset.image (compData p)) (g := compData p)
    (fun y hy => Finset.mem_image_of_mem _ hy)]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd => ?_)
  obtain ⟨y0, hy0, rfl⟩ := Finset.mem_image.1 hd
  have hy0' := (Irr6_finite P p N kind).mem_toFinset.1 hy0
  have hcond := hy0'.1.2
  have hord : (compData p y0).1 + 2 = N := hcond.2.2.2.1
  have hvk : VecKindOK (P.N (p + 1)) kind (compData p y0).2 := hcond.2.2.2.2
  have hvle : ∀ i, (compData p y0).2 i ≤ P.N (p + 1) := fun i => hvk.le i
  rw [Irr6_slice_eq P p N kind _ hord hvk hvle]
  have hbal : IsBalancedSig (fun i : Fin (2 * 3) => childSig i) := by
    have hpl : y0.garden.IsPlain := hy0'.1.2.1
    have := Comb.balanced_of_plain hpl
    have hs : y0.garden.sig = fun i => childSig i := funext hy0'.1.1
    rw [← hs]; exact this
  have hle : (compData p y0).1 ≤ P.N (p + 1) ^ 4 := by
    have : (compData p y0).1 ≤ N := by omega
    exact this.trans hN
  have := garden_slice_kernelKgen C₀ P G hp Rr hRr (m := 3) (by norm_num) hmmax _ hbal n k hle tt htt
    (compData p y0).2 (hnum _ hle)
  simpa using this

end WaveTurbulence.FlowerP7
