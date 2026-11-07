/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.Level2
/-! FLOWER-P7: slice bound for the plain width-four second component of a first-level piece
(shapes `σ1 … σ3`): irreducible part plus two second-level pieces. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset LGSpine

/-- The explicit bound of a second-level piece (the right-hand side of `piece2_bound`). -/
noncomputable def PieceBound2 (P : WTParams) (p N : ℕ) (τ : Fin 2 ⊕ Fin 2 ≃ Fin 4) (ζ : Fin 4 → ℤˣ)
    (e : ℕ × (Fin 4 → ℕ)) (Creg : ℕ → ℝ) (nB : Fin 4 → (Fin P.d → ℤ)) (k : Mom P.d) : ℝ :=
  open scoped Classical in
  ∑ c ∈ (Ccomp2_finite P p N (fun i => ζ (τ (.inl i)))).toFinset.image (compData p),
    ∑ c' ∈ (Dcomp2_finite P p N (fun i => ζ (τ (.inr i)))).toFinset.image (compData p),
      if Joint2 τ e c c' then
        (if nB (τ (.inl 0)) = nB (τ (.inl 1)) then
          jbr (k + latticePoint P.L (nB (τ (.inl 0)))) ^ (-(4 * P.Lambda (p + 1) : ℝ)) *
            (P.δ ^ (2 * P.ν * c.1) * P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)) +
              Creg c.1 * P.δ ^ ((c.1 : ℝ) / 4)) else 0) *
        (if nB (τ (.inr 0)) = nB (τ (.inr 1)) then
          jbr (k + latticePoint P.L (nB (τ (.inr 0)))) ^ (-(4 * P.Lambda (p + 1) : ℝ)) *
            (P.δ ^ (2 * P.ν * c'.1) * P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)) +
              Creg c'.1 * P.δ ^ ((c'.1 : ℝ) / 4)) else 0)
      else 0

theorem minimalAt_univ_iff4 (G : Garden 4) (hG : G.IsPlain) : MinimalAt G 0 Finset.univ ↔ IrrAt G 0 := by
  constructor
  · rintro ⟨-, -, h⟩ T hT hi
    exact h T hT hi (Finset.subset_univ _)
  · intro h
    exact ⟨Finset.mem_univ _, closedTrees_univ G hG, fun T hT hi _ => h T hT hi⟩

open scoped Classical in
/-- The irreducible part of a plain width-four slice is an LG-SPINE garden slice. -/
theorem Bplain4_irr_eq (P : WTParams) (p N : ℕ) {a : ℕ} (σ : Fin a ⊕ Fin (2 * 2) ≃ Fin (2 * 3))
    (e : ℕ × (Fin (2 * 2) → ℕ)) (he : e.1 ≤ N) (hev : ∀ i, e.2 i ≤ P.N (p + 1)) :
    ((Bcomp1_finite P p N (a := a) σ).toFinset.filter (fun LB => compData p LB = e)).filter
        (fun LB => MinimalAt LB.garden 0 Finset.univ) =
      (gardenSet P p e.1 2 (fun i => childSig (σ (.inr i)))).filter (fun LG => ∀ j, LG.topOrder p j = e.2 j) := by
  ext LB
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, gardenSet, Bcomp1, Set.mem_ofPred_eq, compData,
    Prod.ext_iff]
  simp only [Nat.add_sub_cancel]
  constructor
  · rintro ⟨⟨⟨hs, ⟨hpl, hcr, hat⟩, hle⟩, hord, hvec⟩, hmin⟩
    have hirr := (minimalAt_univ_iff4 LB.garden hpl).1 hmin
    refine ⟨⟨⟨hpl, Or.inl ⟨by omega, (irreducible_iff_irrAt LB.garden hpl 0).2 hirr⟩, hcr⟩,
      ⟨fun j => ?_, hat⟩, hs, hord⟩, fun j => congrFun hvec j⟩
    rw [congrFun hvec j]; exact hev j
  · rintro ⟨⟨⟨hpl, hir, hcr⟩, htr, hs, hord⟩, hvec⟩
    rcases hir with ⟨-, hirr⟩ | ⟨h2, -⟩
    · exact ⟨⟨⟨hs, ⟨hpl, hcr, htr.2⟩, hord ▸ he⟩, hord, funext hvec⟩,
        (minimalAt_univ_iff4 LB.garden hpl).2 ((irreducible_iff_irrAt LB.garden hpl 0).1 hirr)⟩
    · omega

theorem τ1_inl0 : τ1 (.inl 0) = 0 := by simp [τ1]
theorem τ2_inl0 : τ2 (.inl 0) = 0 := by simp [τ2]

theorem τ1_image : (Finset.univ.image fun i => τ1 (.inl i)) = ({0, 1} : Finset (Fin 4)) := by
  ext x; fin_cases x <;> simp [τ1, Fin.exists_fin_two]

theorem τ2_image : (Finset.univ.image fun i => τ2 (.inl i)) = ({0, 3} : Finset (Fin 4)) := by
  ext x; fin_cases x <;> simp [τ2, Fin.exists_fin_two]

open scoped Classical in
theorem Bplain4_piece_set_eq (P : WTParams) (p N : ℕ) {a : ℕ} (σ : Fin a ⊕ Fin (2 * 2) ≃ Fin (2 * 3))
    (e : ℕ × (Fin (2 * 2) → ℕ)) (he : e.1 ≤ N) (τ : Fin 2 ⊕ Fin 2 ≃ Fin 4) (S : Finset (Fin 4))
    (hS : S = Finset.univ.image fun i => τ (.inl i)) (h0 : τ (.inl 0) = 0) :
    ((((Bcomp1_finite P p N (a := a) σ).toFinset.filter (fun LB => compData p LB = e)).filter
        (fun LB => MinimalAt LB.garden 0 S) : Finset (LayeredGarden 4)) : Set (LayeredGarden 4)) =
      {LB : LayeredGarden 4 | LB.garden.sig = (fun i => childSig (σ (.inr i))) ∧
        (CompCond P p LB ∧ compData p LB = e) ∧
        MinimalAt LB.garden (τ (.inl 0)) (Finset.univ.image fun i => τ (.inl i))} := by
  ext LB
  simp only [Finset.coe_filter, Finset.mem_filter, Set.Finite.mem_toFinset, Bcomp1, Set.mem_ofPred_eq,
    Set.mem_setOf_eq, h0, ← hS]
  constructor
  · rintro ⟨⟨⟨hs, hc, hle⟩, hd⟩, hm⟩
    exact ⟨hs, ⟨hc, hd⟩, hm⟩
  · rintro ⟨hs, ⟨hc, hd⟩, hm⟩
    refine ⟨⟨⟨hs, hc, ?_⟩, hd⟩, hm⟩
    have : LB.garden.order = e.1 := by simpa [compData] using congrArg Prod.fst hd
    omega

open scoped Classical in
/-- **Plain width-four second component of a first-level piece: slice bound.** -/
theorem Bplain4_slice_bound (C₀ : ℕ) (P : WTParams) (G : LGContext C₀ P) {p N : ℕ} (hp : p < P.D)
    (hN : N ≤ P.N (p + 1) ^ 4) (Rr : ℕ → Mom P.d → ℝ) (hRr : RemainderBound P Rr p)
    (hR1 : 1 ≤ P.R (p + 1)) (hmmax : 2 ≤ 10 * P.R (p + 1)) {a : ℕ} (σ : Fin a ⊕ Fin (2 * 2) ≃ Fin (2 * 3))
    (hs4 : (fun i => childSig (σ (.inr i))) = ![1, -1, 1, -1]) (e : ℕ × (Fin (2 * 2) → ℕ)) (he : e.1 ≤ N)
    (hev : ∀ i, e.2 i ≤ P.N (p + 1)) (nB : Fin (2 * 2) → (Fin P.d → ℤ)) (k : Mom P.d) (tt : Fin (2 * 2) → ℝ)
    (htt : ∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1))
    (hF : ∀ q : ℕ, Summable fun m : Fin P.d → ℤ => |inputsF P Rr q (k + latticePoint P.L m)|)
    (hnumA : ∀ N' ≤ P.N (p + 1) ^ 4, ((P.d : ℝ) + 1) ^ (4 * 2 * P.Lambda (p + 1)) *
      gardenT P G.Cφ p 2 N' ^ (8 * 2 * P.Lambda (p + 1)) * (2 * P.C₁) ^ (N' + 2) * P.δ ^ (6 * P.ν * N') *
      P.L ^ (-P.η ^ 7) * P.L ^ (-((2 : ℕ) - 1 : ℝ) / 70) ≤ 1)
    (hnumC : ∀ N' ≤ P.N (p + 1) ^ 4, ((P.d : ℝ) + 1) ^ (2 * P.Lambda (p + 1)) *
      coupleT P G.Cφ p N' ^ (8 * P.Lambda (p + 1)) * (2 * P.C₁) ^ (N' + 1) * P.δ ^ (6 * P.ν * N') *
      P.L ^ (-P.η ^ 7) ≤ P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)))
    (Creg : ℕ → ℝ) (hreg : RegularFamilyBound P (inputsF P Rr) p Creg) :
    ‖∑ LB ∈ (Bcomp1_finite P p N (a := a) σ).toFinset.filter (fun LB => compData p LB = e),
        kernelKgen P.L P.γ P.δ (inputsF P Rr) LB (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k nB 0‖ ≤
      PieceBound2 P p N τ1 (fun i => childSig (σ (.inr i))) e Creg nB k +
        PieceBound2 P p N τ2 (fun i => childSig (σ (.inr i))) e Creg nB k +
        jbrProdAt P.L k nB ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (-(((2 : ℕ) : ℝ) - 1) / 4) *
          P.δ ^ (2 * P.ν * e.1) := by
  set T := (Bcomp1_finite P p N (a := a) σ).toFinset.filter (fun LB => compData p LB = e) with hT
  have hTpl : ∀ LB ∈ T, LB.garden.IsPlain ∧ LB.garden.sig = ![1, -1, 1, -1] := by
    intro LB hLB
    simp only [hT, Finset.mem_filter, Set.Finite.mem_toFinset, Bcomp1, Set.mem_ofPred_eq] at hLB
    exact ⟨hLB.1.2.1.1, hLB.1.1.trans hs4⟩
  rw [sum_partition4 T hTpl]
  refine (norm_add₃_le).trans (add_le_add (add_le_add ?_ ?_) ?_)
  · -- `τ1`
    rw [← finsum_mem_coe_finset, Bplain4_piece_set_eq P p N σ e he τ1 {0, 1} τ1_image.symm τ1_inl0]
    exact piece2_bound C₀ P G hp hN Rr hRr hR1 τ1 (fun i => childSig (σ (.inr i)))
      (by funext i; fin_cases i <;> simp [τ1, congrFun hs4])
      (by funext i; fin_cases i <;> simp [τ1, congrFun hs4]) e he hev nB k tt htt hF hnumC Creg hreg
  · -- `τ2`
    rw [← finsum_mem_coe_finset, Bplain4_piece_set_eq P p N σ e he τ2 {0, 3} τ2_image.symm τ2_inl0]
    exact piece2_bound C₀ P G hp hN Rr hRr hR1 τ2 (fun i => childSig (σ (.inr i)))
      (by funext i; fin_cases i <;> simp [τ2, congrFun hs4])
      (by funext i; fin_cases i <;> simp [τ2, congrFun hs4]) e he hev nB k tt htt hF hnumC Creg hreg
  · -- irreducible
    rw [Bplain4_irr_eq P p N σ e he hev]
    have hbal : IsBalancedSig (fun i : Fin (2 * 2) => childSig (σ (.inr i))) := by
      rw [hs4]; simp [IsBalancedSig, Fin.sum_univ_four]
    exact garden_slice_kernelKgen C₀ P G hp Rr hRr (m := 2) (by norm_num) hmmax _ hbal nB k (he.trans hN) tt htt e.2
      (hnumA e.1 (he.trans hN))

end WaveTurbulence.FlowerP7
