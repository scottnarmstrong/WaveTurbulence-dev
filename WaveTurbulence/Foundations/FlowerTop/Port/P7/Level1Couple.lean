/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.Level0
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.Shift
public import WaveTurbulence.Foundations.XChain.SNormPointwise
/-! FLOWER-P7: slice bounds for a couple component with equal root labels `(m, m)` at base `k`:
the nonregular part from LG-SPINE's couple estimate, the regular part from a named interface (the shape of
FLOWER-REG's `regular_family_pointwise`). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset LGSpine

theorem kernelKgen_eq_KQstar {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 2) (hP : LG.garden.IsPlain)
    (tt : Fin 2 → ℝ) (k : Mom d) :
    kernelKgen L γ δ F LG (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k (fun _ => 0) 0 =
      KQstar L γ δ F LG (tt 0) (tt 1) k := by
  rw [kernelKgen_noFix L γ δ F LG hP (fun x => tt x.1.1) 0 k (fun _ => 0) 0]
  unfold KQstar
  congr 1
  funext b
  rcases b with ⟨⟨j, _⟩, _⟩
  fin_cases j <;> rfl

/-- **Interface (two times).**  The pointwise bound for a finite family of regular canonical
couples of order `N'` (for `N' = 2n` this is the conclusion of `FlowerReg.regular_family_pointwise` with decay
`jbr k ^ (-4Λ(p+1))` and `δ^{n/2} = δ^{N'/4}`; for odd `N'` the family is empty because regular couples have even
order -- this parity fact is not proved here and is part of the interface). -/
def RegularFamilyBound (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p : ℕ) (Creg : ℕ → ℝ) : Prop :=
  ∀ (N' : ℕ), N' ≤ P.N (p + 1) ^ 4 → ∀ (t s : ℝ), t ∈ Set.Icc (p : ℝ) (p + 1) → s ∈ Set.Icc (p : ℝ) (p + 1) →
    ∀ (k : Mom P.d) (V : Finset (LayeredGarden 2)),
    (∀ LG ∈ V, IsCanonC (p + 1) LG ∧ LG.garden.order = N' ∧ IsRegularCouple LG.garden) →
    ‖∑ LG ∈ V, KQstar P.L P.γ P.δ F LG t s k‖ ≤
      jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * Creg N' * P.δ ^ ((N' : ℝ) / 4)

theorem norm_le_of_SNorm_le' {d A B : ℕ} (F : Mom d → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (h : SNorm A B F ≤ ENNReal.ofReal C) (k : Mom d) :
    ‖F k‖ ≤ jbr k ^ (-(B : ℝ)) * C := by
  have hb := WaveTurbulence.Induct.SNorm_pointwise F C hC h k
  have hpos : 0 < jbr k ^ B := pow_pos (WaveTurbulence.Induct.jbr_pos k) B
  have hd : ‖F k‖ ≤ C / (jbr k ^ B) :=
    (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hb)
  simpa only [Real.rpow_neg (WaveTurbulence.Induct.jbr_pos k).le, Real.rpow_natCast, div_eq_mul_inv, mul_comm] using hd

open scoped Classical in
theorem Bcomp1_couple_mem_iff (P : WTParams) (p N : ℕ) {a : ℕ} (σ : Fin a ⊕ Fin 2 ≃ Fin (2 * 3))
    (hs2 : (fun i => childSig (σ (.inr i))) = ![1, -1]) (e : ℕ × (Fin 2 → ℕ)) (he : e.1 ≤ N)
    (hv : ∀ i, e.2 i ≤ P.N (p + 1)) (LB : LayeredGarden 2) :
    LB ∈ (Bcomp1_finite P p N (a := a) σ).toFinset.filter (fun LB => compData p LB = e) ↔
      (IsCanonC (p + 1) LB ∧ LB.IsTrunc (p + 1 - 1) (P.N (p + 1)) (P.N (p + 1 - 1)) ∧ LB.garden.order = e.1) ∧
        ∀ j, LB.topOrder p j = e.2 j := by
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Bcomp1, Set.mem_ofPred_eq, compData, Prod.ext_iff,
    IsCanonC, IsCouple, Nat.add_sub_cancel]
  constructor
  · rintro ⟨⟨hs, ⟨hpl, hcr, hat⟩, hle⟩, hord, hvec⟩
    refine ⟨⟨⟨⟨hpl, hs.trans hs2⟩, hcr⟩, ⟨fun j => ?_, hat⟩, hord⟩, fun j => congrFun hvec j⟩
    rw [congrFun hvec j]; exact hv j
  · rintro ⟨⟨⟨⟨hpl, hs⟩, hcr⟩, htr, hord⟩, hvec⟩
    exact ⟨⟨hs.trans hs2.symm, ⟨hpl, hcr, htr.2⟩, hord ▸ he⟩, hord, funext hvec⟩

open scoped Classical in
/-- Nonregular couples of a top-order slice, pointwise (from LG-SPINE's couple estimate). -/
theorem couple_nonreg_slice_pointwise (C₀ : ℕ) (P : WTParams) (G : LGContext C₀ P) {p : ℕ} (hp : p < P.D)
    (Rr : ℕ → Mom P.d → ℝ) (hRr : RemainderBound P Rr p) (hR1 : 1 ≤ P.R (p + 1)) {N' : ℕ}
    (hN' : N' ≤ P.N (p + 1) ^ 4) (k : Mom P.d) {t s : ℝ} (ht : t ∈ Set.Icc (p : ℝ) (p + 1))
    (hts : s ∈ Set.Icc (p : ℝ) (p + 1)) (v : Fin 2 → ℕ)
    (hnum : ((P.d : ℝ) + 1) ^ (2 * P.Lambda (p + 1)) * coupleT P G.Cφ p N' ^ (8 * P.Lambda (p + 1)) *
      (2 * P.C₁) ^ (N' + 1) * P.δ ^ (6 * P.ν * N') * P.L ^ (-P.η ^ 7) ≤
      P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5))) :
    ‖∑ LG ∈ (coupleSet P p N').filter (fun LG => ∀ j, LG.topOrder p j = v j),
        KQstar P.L P.γ P.δ (inputsF P Rr) LG t s k‖ ≤
      jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) *
        (P.δ ^ (2 * P.ν * N') * P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5))) := by
  have hmemA : ∀ LG ∈ (coupleSet P p N').filter (fun LG => ∀ j, LG.topOrder p j = v j),
      IsCanonC (p + 1) LG ∧ LG.IsTrunc (p + 1 - 1) (P.N (p + 1)) (P.N (p + 1 - 1)) ∧
        LG.garden.order = N' ∧ ¬ IsRegularCouple LG.garden := by
    intro LG hLG
    obtain ⟨h1, -⟩ := Finset.mem_filter.1 hLG
    simp only [coupleSet, coupleCarrier, Finset.mem_filter, Set.Finite.mem_toFinset] at h1
    exact ⟨h1.1.1, h1.1.2.1, h1.1.2.2, h1.2⟩
  have hSN := couple_estimate_slice_of_gate_tt C₀ P G.hs G.hcoarse G.hfourier G.hcount G.habs G.hlog G.hgate G.hd
    G.hlowP G.htime G.hCφ G.hφ hp Rr hRr hR1 hN' ht hts _ hmemA
    (twistClosed_topFilter p _ (twistClosed_coupleSet P G.hd hp hN') v) hnum
  have hδ : 0 < P.δ := G.hs.delta_pos
  have hL : 0 < P.L := by linarith [G.hs.L_ge]
  have hC : 0 ≤ P.δ ^ (2 * P.ν * (N' : ℝ)) * P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)) :=
    mul_nonneg (Real.rpow_nonneg hδ.le _) (Real.rpow_nonneg hL.le _)
  set C : ℝ := P.δ ^ (2 * P.ν * (N' : ℝ)) * P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)) with hCdef
  have hnr : ‖(fun k => ∑ LG ∈ (coupleSet P p N').filter (fun LG => ∀ j, LG.topOrder p j = v j),
      KQstar P.L P.γ P.δ (inputsF P Rr) LG t s k) k‖ ≤ jbr k ^ (-((4 * P.Lambda (p + 1) : ℕ) : ℝ)) * C :=
    norm_le_of_SNorm_le' (A := 4 * P.Lambda (p + 1)) (B := 4 * P.Lambda (p + 1)) _ C hC hSN k
  have hcast : ((4 * P.Lambda (p + 1) : ℕ) : ℝ) = 4 * (P.Lambda (p + 1) : ℝ) := by norm_num
  rw [hcast] at hnr
  exact hnr

open scoped Classical in
/-- A finset of canonical truncated couples of one order and one top-order vector: pointwise bound of the sum of
the couple kernels (nonregular part by LG-SPINE, regular part by the interface). -/
theorem couple_family_pointwise (C₀ : ℕ) (P : WTParams) (G : LGContext C₀ P) {p : ℕ} (hp : p < P.D)
    (Rr : ℕ → Mom P.d → ℝ) (hRr : RemainderBound P Rr p) (hR1 : 1 ≤ P.R (p + 1)) {N' : ℕ}
    (hN' : N' ≤ P.N (p + 1) ^ 4) (k : Mom P.d) {t s : ℝ} (ht : t ∈ Set.Icc (p : ℝ) (p + 1))
    (hts : s ∈ Set.Icc (p : ℝ) (p + 1)) (v : Fin 2 → ℕ)
    (hnum : ((P.d : ℝ) + 1) ^ (2 * P.Lambda (p + 1)) * coupleT P G.Cφ p N' ^ (8 * P.Lambda (p + 1)) *
      (2 * P.C₁) ^ (N' + 1) * P.δ ^ (6 * P.ν * N') * P.L ^ (-P.η ^ 7) ≤
      P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)))
    (Creg : ℕ → ℝ) (hreg : RegularFamilyBound P (inputsF P Rr) p Creg)
    (S : Finset (LayeredGarden 2))
    (hS : ∀ LB ∈ S, (IsCanonC (p + 1) LB ∧ LB.IsTrunc (p + 1 - 1) (P.N (p + 1)) (P.N (p + 1 - 1)) ∧
      LB.garden.order = N') ∧ ∀ j, LB.topOrder p j = v j)
    (hSfull : ∀ LB, ((IsCanonC (p + 1) LB ∧ LB.IsTrunc (p + 1 - 1) (P.N (p + 1)) (P.N (p + 1 - 1)) ∧
      LB.garden.order = N') ∧ ∀ j, LB.topOrder p j = v j) → LB ∈ S) :
    ‖∑ LB ∈ S, KQstar P.L P.γ P.δ (inputsF P Rr) LB t s k‖ ≤
      jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) *
        (P.δ ^ (2 * P.ν * N') * P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)) +
          Creg N' * P.δ ^ ((N' : ℝ) / 4)) := by
  rw [← Finset.sum_filter_add_sum_filter_not S (fun LB => IsRegularCouple LB.garden)]
  refine (norm_add_le _ _).trans ?_
  have hreg' := hreg N' hN' t s ht hts k (S.filter fun LB => IsRegularCouple LB.garden) (fun LB hLB => by
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hLB
    exact ⟨(hS LB h1).1.1, (hS LB h1).1.2.2, h2⟩)
  have hA1 : S.filter (fun LB => ¬ IsRegularCouple LB.garden) =
      (coupleSet P p N').filter (fun LG => ∀ j, LG.topOrder p j = v j) := by
    ext LB
    simp only [Finset.mem_filter, coupleSet, coupleCarrier, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨⟨hc, htr, hord⟩, hvec⟩ := hS LB h1
      exact ⟨⟨⟨hc, htr, hord⟩, h2⟩, hvec⟩
    · rintro ⟨⟨⟨hc, htr, hord⟩, h2⟩, hvec⟩
      exact ⟨hSfull LB ⟨⟨hc, htr, hord⟩, hvec⟩, h2⟩
  have hnr := couple_nonreg_slice_pointwise C₀ P G hp Rr hRr hR1 hN' k ht hts v hnum
  rw [← hA1] at hnr
  calc _ ≤ jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * Creg N' * P.δ ^ ((N' : ℝ) / 4) +
        jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * (P.δ ^ (2 * P.ν * N') *
          P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5))) := add_le_add hreg' hnr
    _ = _ := by ring

open scoped Classical in
/-- **Couple component of a first-level piece: slice bound** (root labels `nB`, base `k`, caps `t`). -/
theorem couple_slice_bound (C₀ : ℕ) (P : WTParams) (G : LGContext C₀ P) {p N : ℕ} (hp : p < P.D)
    (hN : N ≤ P.N (p + 1) ^ 4) (Rr : ℕ → Mom P.d → ℝ) (hRr : RemainderBound P Rr p)
    (hR1 : 1 ≤ P.R (p + 1)) {a : ℕ} (σ : Fin a ⊕ Fin 2 ≃ Fin (2 * 3))
    (hs2 : (fun i => childSig (σ (.inr i))) = ![1, -1]) (nB : Fin 2 → (Fin P.d → ℤ)) (k : Mom P.d) (tt : Fin 2 → ℝ)
    (htt : ∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) (e : ℕ × (Fin 2 → ℕ)) (he : e.1 ≤ N) (hv : ∀ i, e.2 i ≤ P.N (p + 1))
    (hnum : ((P.d : ℝ) + 1) ^ (2 * P.Lambda (p + 1)) * coupleT P G.Cφ p e.1 ^ (8 * P.Lambda (p + 1)) *
      (2 * P.C₁) ^ (e.1 + 1) * P.δ ^ (6 * P.ν * e.1) * P.L ^ (-P.η ^ 7) ≤
      P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)))
    (Creg : ℕ → ℝ) (hreg : RegularFamilyBound P (inputsF P Rr) p Creg) :
    ‖∑ LB ∈ (Bcomp1_finite P p N (a := a) σ).toFinset.filter (fun LB => compData p LB = e),
        kernelKgen P.L P.γ P.δ (inputsF P Rr) LB (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k nB 0‖ ≤
      if nB 0 = nB 1 then
        jbr (k + latticePoint P.L (nB 0)) ^ (-(4 * P.Lambda (p + 1) : ℝ)) *
          (P.δ ^ (2 * P.ν * e.1) * P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)) +
            Creg e.1 * P.δ ^ ((e.1 : ℝ) / 4))
      else 0 := by
  have hmem := Bcomp1_couple_mem_iff P p N σ hs2 e he hv
  have hplain : ∀ LB ∈ (Bcomp1_finite P p N (a := a) σ).toFinset.filter (fun LB => compData p LB = e),
      LB.garden.IsPlain := fun LB h => ((hmem LB).1 h).1.1.1.1
  have hsig : ∀ LB ∈ (Bcomp1_finite P p N (a := a) σ).toFinset.filter (fun LB => compData p LB = e),
      LB.garden.sig = ![1, -1] := fun LB h => ((hmem LB).1 h).1.1.1.2
  by_cases hn : nB 0 = nB 1
  · rw [if_pos hn]
    have hnB : nB = fun _ => nB 0 := by
      funext i; fin_cases i
      · rfl
      · exact hn.symm
    have hK : ∀ LB ∈ (Bcomp1_finite P p N (a := a) σ).toFinset.filter (fun LB => compData p LB = e),
        kernelKgen P.L P.γ P.δ (inputsF P Rr) LB (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k nB 0 =
          KQstar P.L P.γ P.δ (inputsF P Rr) LB (tt 0) (tt 1) (k + latticePoint P.L (nB 0)) := by
      intro LB hLB
      rw [hnB, kernelKgen_shift P.L P.γ P.δ (inputsF P Rr) LB (hplain LB hLB) (fun x => tt x.1.1) k (nB 0),
        kernelKgen_eq_KQstar P.L P.γ P.δ (inputsF P Rr) LB (hplain LB hLB)]
    rw [Finset.sum_congr rfl hK]
    exact couple_family_pointwise C₀ P G hp Rr hRr hR1 (he.trans hN) _ (htt 0) (htt 1) e.2 hnum Creg hreg _
      (fun LB h => (hmem LB).1 h) (fun LB h => (hmem LB).2 h)
  · rw [if_neg hn]
    rw [Finset.sum_eq_zero fun LB hLB => couple_kernel_offdiag P.L P.γ P.δ _ LB (hplain LB hLB)
      (hsig LB hLB) (fun x => tt x.1.1) k nB hn, norm_zero]

end WaveTurbulence.FlowerP7
