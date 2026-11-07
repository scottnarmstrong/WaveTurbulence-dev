/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.Piece42
/-! FLOWER-P7: second-level split of a plain width-four block with alternating signs into an irreducible
block or two couples. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset LGSpine

theorem shape4_classify : ∀ S : Finset (Fin 4), 0 ∈ S →
    (∑ j ∈ S, (if j.val % 2 = 0 then (1 : ℤ) else -1)) = 0 →
      S = {0, 1} ∨ S = {0, 3} ∨ S = Finset.univ := by
  decide

theorem exists_shape4 (G : Garden 4) (hplain : G.IsPlain) (hsig : G.sig = ![1, -1, 1, -1]) :
    ∃ S : Finset (Fin 4), (S = {0, 1} ∨ S = {0, 3} ∨ S = Finset.univ) ∧ MinimalAt G 0 S := by
  obtain ⟨S, hS⟩ := exists_minimal_closed G hplain 0
  refine ⟨S, shape4_classify S hS.1 ?_, hS⟩
  have := balanced_of_closed G S hS.2.1
  rw [← this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hsig]
  fin_cases j <;> simp

open scoped Classical in
/-- The sum over a family of plain alternating width-four gardens splits by the minimal closed block of tree `0`. -/
theorem sum_partition4 (T : Finset (LayeredGarden 4))
    (hT : ∀ LB ∈ T, LB.garden.IsPlain ∧ LB.garden.sig = ![1, -1, 1, -1]) (f : LayeredGarden 4 → ℂ) :
    ∑ LB ∈ T, f LB =
      ∑ LB ∈ T.filter (fun LB => MinimalAt LB.garden 0 {0, 1}), f LB +
      ∑ LB ∈ T.filter (fun LB => MinimalAt LB.garden 0 {0, 3}), f LB +
      ∑ LB ∈ T.filter (fun LB => MinimalAt LB.garden 0 Finset.univ), f LB := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun LB hLB => ?_
  obtain ⟨hpl, hsig⟩ := hT LB hLB
  obtain ⟨S, hS, hmin⟩ := exists_shape4 LB.garden hpl hsig
  have hne1 : ({0, 1} : Finset (Fin 4)) ≠ {0, 3} := by decide
  have hne2 : ({0, 1} : Finset (Fin 4)) ≠ Finset.univ := by decide
  have hne3 : ({0, 3} : Finset (Fin 4)) ≠ Finset.univ := by decide
  rcases hS with rfl | rfl | rfl
  · have h2 : ¬ MinimalAt LB.garden 0 {0, 3} := fun h =>
      hne1 (minimal_closed_unique LB.garden hpl 0 hmin h)
    have h3 : ¬ MinimalAt LB.garden 0 Finset.univ := fun h =>
      hne2 (minimal_closed_unique LB.garden hpl 0 hmin h)
    simp [hmin, h2, h3]
  · have h1 : ¬ MinimalAt LB.garden 0 {0, 1} := fun h =>
      hne1 (minimal_closed_unique LB.garden hpl 0 h hmin)
    have h3 : ¬ MinimalAt LB.garden 0 Finset.univ := fun h =>
      hne3 (minimal_closed_unique LB.garden hpl 0 hmin h)
    simp [hmin, h1, h3]
  · have h1 : ¬ MinimalAt LB.garden 0 {0, 1} := fun h =>
      hne2 (minimal_closed_unique LB.garden hpl 0 h hmin)
    have h2 : ¬ MinimalAt LB.garden 0 {0, 3} := fun h =>
      hne3 (minimal_closed_unique LB.garden hpl 0 h hmin)
    simp [hmin, h1, h2]

theorem glue_CompCond_iff {a b w : ℕ} (P : WTParams) (p : ℕ) (σ : Fin a ⊕ Fin b ≃ Fin w) (LA : LayeredGarden a)
    (LB : LayeredGarden b) :
    CompCond P p (glueLayered σ LA LB) ↔ CompCond P p LA ∧ CompCond P p LB := by
  unfold CompCond
  rw [glue_isPlain_iff, glue_canonCriterion_iff, glue_attach_cond]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩⟩
    exact ⟨⟨h1, h3, h5⟩, ⟨h2, h4, h6⟩⟩
  · rintro ⟨⟨h1, h3, h5⟩, ⟨h2, h4, h6⟩⟩
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩⟩

/-- The pairs of couples of a second-level piece (fiber `e` of the data of the width-four block). -/
def Pairs2 (P : WTParams) (p : ℕ) (τ : Fin 2 ⊕ Fin 2 ≃ Fin 4) (ζ : Fin 4 → ℤˣ) (e : ℕ × (Fin 4 → ℕ)) :
    Set (LayeredGarden 2 × LayeredGarden 2) :=
  {x | x.1.garden.sig = (fun i => ζ (τ (.inl i))) ∧ x.2.garden.sig = (fun i => ζ (τ (.inr i))) ∧
    CompCond P p x.1 ∧ IrrAt x.1.garden 0 ∧ CompCond P p x.2 ∧
    x.1.garden.order + x.2.garden.order = e.1 ∧
    glueVec τ (fun i => x.1.topOrder p i) (fun i => x.2.topOrder p i) = e.2}

theorem piece2_eq_image (P : WTParams) (p : ℕ) (τ : Fin 2 ⊕ Fin 2 ≃ Fin 4) (ζ : Fin 4 → ℤˣ)
    (e : ℕ × (Fin 4 → ℕ)) :
    {LB : LayeredGarden 4 | LB.garden.sig = ζ ∧ (CompCond P p LB ∧ compData p LB = e) ∧
        MinimalAt LB.garden (τ (.inl 0)) (Finset.univ.image fun i => τ (.inl i))} =
      (fun x : LayeredGarden 2 × LayeredGarden 2 => glueLayered τ x.1 x.2) '' Pairs2 P p τ ζ e := by
  have h := piece_eq_image τ 0 ζ (fun LB => CompCond P p LB ∧ compData p LB = e) (CompCond P p) (CompCond P p)
    (fun LC LD => LC.garden.order + LD.garden.order = e.1 ∧
      glueVec τ (fun i => LC.topOrder p i) (fun i => LD.topOrder p i) = e.2)
    (fun LC LD => by
      have : compData p (glueLayered τ LC LD) = e ↔ LC.garden.order + LD.garden.order = e.1 ∧
          glueVec τ (fun i => LC.topOrder p i) (fun i => LD.topOrder p i) = e.2 := by
        unfold compData
        rw [glue_order, glue_topVec, Prod.ext_iff]
      rw [glue_CompCond_iff, and_assoc, this])
    (fun y hy => hy.1.1) (fun LA hA => hA.1)
  rw [h]
  rfl

/-- First couples of second-level pieces. -/
def Ccomp2 (P : WTParams) (p N : ℕ) (ζC : Fin 2 → ℤˣ) : Set (LayeredGarden 2) :=
  {LA | LA.garden.sig = ζC ∧ CompCond P p LA ∧ IrrAt LA.garden 0 ∧ LA.garden.order ≤ N}

/-- Second couples of second-level pieces. -/
def Dcomp2 (P : WTParams) (p N : ℕ) (ζD : Fin 2 → ℤˣ) : Set (LayeredGarden 2) :=
  {LB | LB.garden.sig = ζD ∧ CompCond P p LB ∧ LB.garden.order ≤ N}

theorem Ccomp2_finite (P : WTParams) (p N : ℕ) (ζC : Fin 2 → ℤˣ) : (Ccomp2 P p N ζC).Finite :=
  (Canon.finite_layeredGardens 2 N p).subset fun LA h => ⟨h.2.2.2, h.2.1.2.1.1⟩

theorem Dcomp2_finite (P : WTParams) (p N : ℕ) (ζD : Fin 2 → ℤˣ) : (Dcomp2 P p N ζD).Finite :=
  (Canon.finite_layeredGardens 2 N p).subset fun LB h => ⟨h.2.2, h.2.1.2.1.1⟩

/-- The joint condition of a second-level piece. -/
def Joint2 (τ : Fin 2 ⊕ Fin 2 ≃ Fin 4) (e : ℕ × (Fin 4 → ℕ)) (c c' : ℕ × (Fin 2 → ℕ)) : Prop :=
  c.1 + c'.1 = e.1 ∧ glueVec τ c.2 c'.2 = e.2

theorem Pairs2_eq (P : WTParams) (p N : ℕ) (τ : Fin 2 ⊕ Fin 2 ≃ Fin 4) (ζ : Fin 4 → ℤˣ) (e : ℕ × (Fin 4 → ℕ))
    (he : e.1 ≤ N) :
    Pairs2 P p τ ζ e =
      {x | x ∈ Ccomp2 P p N (fun i => ζ (τ (.inl i))) ×ˢ Dcomp2 P p N (fun i => ζ (τ (.inr i))) ∧
        Joint2 τ e (compData p x.1) (compData p x.2)} := by
  ext x
  simp only [Pairs2, Ccomp2, Dcomp2, Joint2, compData, Set.mem_ofPred_eq, Set.mem_prod]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨⟨⟨h1, h3, h4, by omega⟩, h2, h5, by omega⟩, h6, h7⟩
  · rintro ⟨⟨⟨h1, h3, h4, -⟩, h2, h5, -⟩, h6, h7⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

open scoped Classical in
/-- **Norm bound for a second-level piece** from bounds on the slice sums of the two couples. -/
theorem piece2_norm_le (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) (τ : Fin 2 ⊕ Fin 2 ≃ Fin 4)
    (ζ : Fin 4 → ℤˣ) (e : ℕ × (Fin 4 → ℕ)) (he : e.1 ≤ N) (tt : Fin 4 → ℝ) (k : Mom P.d)
    (nB : Fin 4 → (Fin P.d → ℤ))
    (hF : ∀ q : ℕ, Summable fun m : Fin P.d → ℤ => |F q (k + latticePoint P.L m)|)
    (RA : ℕ × (Fin 2 → ℕ) → Prop) (RB : ℕ × (Fin 2 → ℕ) → Prop)
    (hJ : ∀ c c', Joint2 τ e c c' → RA c ∧ RB c')
    (bC : ℕ × (Fin 2 → ℕ) → ℝ) (bD : ℕ × (Fin 2 → ℕ) → ℝ)
    (hC : ∀ c ∈ (Ccomp2_finite P p N (fun i => ζ (τ (.inl i)))).toFinset.image (compData p), RA c →
      ‖∑ LA ∈ (Ccomp2_finite P p N (fun i => ζ (τ (.inl i)))).toFinset.filter (fun LA => compData p LA = c),
        kernelKgen P.L P.γ P.δ F LA (fun _ => none) ∅ (fun _ => 1) (fun x => tt (τ (.inl x.1.1))) k (fun i => nB (τ (.inl i))) 0‖ ≤ bC c)
    (hD : ∀ c ∈ (Dcomp2_finite P p N (fun i => ζ (τ (.inr i)))).toFinset.image (compData p), RB c →
      ‖∑ LB ∈ (Dcomp2_finite P p N (fun i => ζ (τ (.inr i)))).toFinset.filter (fun LB => compData p LB = c),
        kernelKgen P.L P.γ P.δ F LB (fun _ => none) ∅ (fun _ => 1) (fun x => tt (τ (.inr x.1.1))) k (fun i => nB (τ (.inr i))) 0‖ ≤ bD c) :
    ‖∑ᶠ LB ∈ {LB : LayeredGarden 4 | LB.garden.sig = ζ ∧ (CompCond P p LB ∧ compData p LB = e) ∧
        MinimalAt LB.garden (τ (.inl 0)) (Finset.univ.image fun i => τ (.inl i))},
        kernelKgen P.L P.γ P.δ F LB (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k nB 0‖ ≤
      ∑ c ∈ (Ccomp2_finite P p N (fun i => ζ (τ (.inl i)))).toFinset.image (compData p),
        ∑ c' ∈ (Dcomp2_finite P p N (fun i => ζ (τ (.inr i)))).toFinset.image (compData p),
          if Joint2 τ e c c' then bC c * bD c' else 0 := by
  rw [piece2_eq_image]
  rw [finsum_glue_image P.L P.γ P.δ F τ (Pairs2 P p τ ζ e)
    (fun x hx => ⟨hx.2.2.1.1, hx.2.2.2.2.1.1⟩) tt k nB hF]
  rw [Pairs2_eq P p N τ ζ e he]
  have hfin : {x : LayeredGarden 2 × LayeredGarden 2 | x ∈ Ccomp2 P p N (fun i => ζ (τ (.inl i))) ×ˢ
      Dcomp2 P p N (fun i => ζ (τ (.inr i))) ∧ Joint2 τ e (compData p x.1) (compData p x.2)}.Finite :=
    ((Ccomp2_finite P p N _).prod (Dcomp2_finite P p N _)).subset fun x hx => hx.1
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hset : hfin.toFinset = ((Ccomp2_finite P p N (fun i => ζ (τ (.inl i)))).toFinset ×ˢ
      (Dcomp2_finite P p N (fun i => ζ (τ (.inr i)))).toFinset).filter
      (fun x => Joint2 τ e (compData p x.1) (compData p x.2)) := by
    ext x
    simp [Set.Finite.mem_toFinset, Finset.mem_product]
  rw [hset]
  exact norm_pairs_le _ _ (compData p) (compData p) (Joint2 τ e) _ _ RA RB hJ bC bD hC hD

theorem irrAt_of_couple (G : Garden 2) (hsig : G.sig = ![1, -1]) : IrrAt G 0 := by
  intro T hT hi
  by_contra hne
  have h1 : (1 : Fin 2) ∉ T := fun h1 => hne (by
    apply Finset.eq_univ_of_forall
    intro j; fin_cases j
    · exact hi
    · exact h1)
  have hT0 : T = {0} := by
    ext j; fin_cases j
    · simp [hi]
    · simp [h1]
  have := balanced_of_closed G T hT
  rw [hT0, Finset.sum_singleton, hsig] at this
  simp at this

theorem Ccomp2_mem_iff (P : WTParams) (p N : ℕ) (ζ : Fin 4 → ℤˣ) (τ : Fin 2 ⊕ Fin 2 ≃ Fin 4)
    (hC : (fun i => ζ (τ (.inl i))) = ![1, -1]) (c : ℕ × (Fin 2 → ℕ)) (hc : c.1 ≤ N)
    (hv : ∀ i, c.2 i ≤ P.N (p + 1)) (LA : LayeredGarden 2) :
    LA ∈ (Ccomp2_finite P p N (fun i => ζ (τ (.inl i)))).toFinset.filter (fun LA => compData p LA = c) ↔
      (IsCanonC (p + 1) LA ∧ LA.IsTrunc (p + 1 - 1) (P.N (p + 1)) (P.N (p + 1 - 1)) ∧ LA.garden.order = c.1) ∧
        ∀ j, LA.topOrder p j = c.2 j := by
  classical
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Ccomp2, Set.mem_ofPred_eq, compData, Prod.ext_iff,
    IsCanonC, IsCouple, Nat.add_sub_cancel]
  constructor
  · rintro ⟨⟨hs, ⟨hpl, hcr, hat⟩, hirr, hle⟩, hord, hvec⟩
    refine ⟨⟨⟨⟨hpl, hs.trans hC⟩, hcr⟩, ⟨fun j => ?_, hat⟩, hord⟩, fun j => congrFun hvec j⟩
    rw [congrFun hvec j]; exact hv j
  · rintro ⟨⟨⟨⟨hpl, hs⟩, hcr⟩, htr, hord⟩, hvec⟩
    exact ⟨⟨hs.trans hC.symm, ⟨hpl, hcr, htr.2⟩, irrAt_of_couple LA.garden hs, hord ▸ hc⟩, hord, funext hvec⟩

theorem Dcomp2_mem_iff (P : WTParams) (p N : ℕ) (ζ : Fin 4 → ℤˣ) (τ : Fin 2 ⊕ Fin 2 ≃ Fin 4)
    (hD : (fun i => ζ (τ (.inr i))) = ![1, -1]) (c : ℕ × (Fin 2 → ℕ)) (hc : c.1 ≤ N)
    (hv : ∀ i, c.2 i ≤ P.N (p + 1)) (LB : LayeredGarden 2) :
    LB ∈ (Dcomp2_finite P p N (fun i => ζ (τ (.inr i)))).toFinset.filter (fun LB => compData p LB = c) ↔
      (IsCanonC (p + 1) LB ∧ LB.IsTrunc (p + 1 - 1) (P.N (p + 1)) (P.N (p + 1 - 1)) ∧ LB.garden.order = c.1) ∧
        ∀ j, LB.topOrder p j = c.2 j := by
  classical
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Dcomp2, Set.mem_ofPred_eq, compData, Prod.ext_iff,
    IsCanonC, IsCouple, Nat.add_sub_cancel]
  constructor
  · rintro ⟨⟨hs, ⟨hpl, hcr, hat⟩, hle⟩, hord, hvec⟩
    refine ⟨⟨⟨⟨hpl, hs.trans hD⟩, hcr⟩, ⟨fun j => ?_, hat⟩, hord⟩, fun j => congrFun hvec j⟩
    rw [congrFun hvec j]; exact hv j
  · rintro ⟨⟨⟨⟨hpl, hs⟩, hcr⟩, htr, hord⟩, hvec⟩
    exact ⟨⟨hs.trans hD.symm, ⟨hpl, hcr, htr.2⟩, hord ▸ hc⟩, hord, funext hvec⟩

open scoped Classical in
/-- **Slice bound for a finite set of canonical truncated couples with root labels `nB`** (diagonal: pointwise at
`k + nB 0 / L`; off the diagonal: `0`). -/
theorem couple_set_bound (C₀ : ℕ) (P : WTParams) (G : LGContext C₀ P) {p : ℕ} (hp : p < P.D)
    (Rr : ℕ → Mom P.d → ℝ) (hRr : RemainderBound P Rr p) (hR1 : 1 ≤ P.R (p + 1)) {N' : ℕ}
    (hN' : N' ≤ P.N (p + 1) ^ 4) (nB : Fin 2 → (Fin P.d → ℤ)) (k : Mom P.d) (tt : Fin 2 → ℝ)
    (htt : ∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) (v : Fin 2 → ℕ)
    (hnum : ((P.d : ℝ) + 1) ^ (2 * P.Lambda (p + 1)) * coupleT P G.Cφ p N' ^ (8 * P.Lambda (p + 1)) *
      (2 * P.C₁) ^ (N' + 1) * P.δ ^ (6 * P.ν * N') * P.L ^ (-P.η ^ 7) ≤
      P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)))
    (Creg : ℕ → ℝ) (hreg : RegularFamilyBound P (inputsF P Rr) p Creg) (S : Finset (LayeredGarden 2))
    (hS : ∀ LB ∈ S, (IsCanonC (p + 1) LB ∧ LB.IsTrunc (p + 1 - 1) (P.N (p + 1)) (P.N (p + 1 - 1)) ∧
      LB.garden.order = N') ∧ ∀ j, LB.topOrder p j = v j)
    (hSfull : ∀ LB, ((IsCanonC (p + 1) LB ∧ LB.IsTrunc (p + 1 - 1) (P.N (p + 1)) (P.N (p + 1 - 1)) ∧
      LB.garden.order = N') ∧ ∀ j, LB.topOrder p j = v j) → LB ∈ S) :
    ‖∑ LB ∈ S, kernelKgen P.L P.γ P.δ (inputsF P Rr) LB (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k nB 0‖ ≤
      if nB 0 = nB 1 then
        jbr (k + latticePoint P.L (nB 0)) ^ (-(4 * P.Lambda (p + 1) : ℝ)) *
          (P.δ ^ (2 * P.ν * N') * P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)) +
            Creg N' * P.δ ^ ((N' : ℝ) / 4))
      else 0 := by
  have hplain : ∀ LB ∈ S, LB.garden.IsPlain := fun LB h => (hS LB h).1.1.1.1
  have hsig : ∀ LB ∈ S, LB.garden.sig = ![1, -1] := fun LB h => (hS LB h).1.1.1.2
  by_cases hn : nB 0 = nB 1
  · rw [if_pos hn]
    have hnB : nB = fun _ => nB 0 := by
      funext i; fin_cases i
      · rfl
      · exact hn.symm
    have hK : ∀ LB ∈ S,
        kernelKgen P.L P.γ P.δ (inputsF P Rr) LB (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k nB 0 =
          KQstar P.L P.γ P.δ (inputsF P Rr) LB (tt 0) (tt 1) (k + latticePoint P.L (nB 0)) := by
      intro LB hLB
      rw [hnB, kernelKgen_shift P.L P.γ P.δ (inputsF P Rr) LB (hplain LB hLB) (fun x => tt x.1.1) k (nB 0),
        kernelKgen_eq_KQstar P.L P.γ P.δ (inputsF P Rr) LB (hplain LB hLB)]
    rw [Finset.sum_congr rfl hK]
    exact couple_family_pointwise C₀ P G hp Rr hRr hR1 hN' _ (htt 0) (htt 1) v hnum Creg hreg S hS hSfull
  · rw [if_neg hn]
    rw [Finset.sum_eq_zero fun LB hLB => couple_kernel_offdiag P.L P.γ P.δ _ LB (hplain LB hLB)
      (hsig LB hLB) (fun x => tt x.1.1) k nB hn, norm_zero]

theorem joint2_allowed (P : WTParams) (p N : ℕ) (τ : Fin 2 ⊕ Fin 2 ≃ Fin 4) (e : ℕ × (Fin 4 → ℕ)) (he : e.1 ≤ N)
    (hev : ∀ i, e.2 i ≤ P.N (p + 1)) (c c' : ℕ × (Fin 2 → ℕ)) (h : Joint2 τ e c c') :
    (c.1 ≤ N ∧ ∀ i, c.2 i ≤ P.N (p + 1)) ∧ (c'.1 ≤ N ∧ ∀ i, c'.2 i ≤ P.N (p + 1)) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨⟨by omega, fun i => ?_⟩, ⟨by omega, fun i => ?_⟩⟩
  · have := hev (τ (.inl i))
    rw [← h2] at this
    simpa [glueVec] using this
  · have := hev (τ (.inr i))
    rw [← h2] at this
    simpa [glueVec] using this

open scoped Classical in
/-- **A second-level piece: explicit bound.** -/
theorem piece2_bound (C₀ : ℕ) (P : WTParams) (G : LGContext C₀ P) {p N : ℕ} (hp : p < P.D)
    (hN : N ≤ P.N (p + 1) ^ 4) (Rr : ℕ → Mom P.d → ℝ) (hRr : RemainderBound P Rr p) (hR1 : 1 ≤ P.R (p + 1))
    (τ : Fin 2 ⊕ Fin 2 ≃ Fin 4) (ζ : Fin 4 → ℤˣ) (hC : (fun i => ζ (τ (.inl i))) = ![1, -1])
    (hD : (fun i => ζ (τ (.inr i))) = ![1, -1]) (e : ℕ × (Fin 4 → ℕ)) (he : e.1 ≤ N)
    (hev : ∀ i, e.2 i ≤ P.N (p + 1)) (nB : Fin 4 → (Fin P.d → ℤ)) (k : Mom P.d) (tt : Fin 4 → ℝ)
    (htt : ∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1))
    (hF : ∀ q : ℕ, Summable fun m : Fin P.d → ℤ => |inputsF P Rr q (k + latticePoint P.L m)|)
    (hnumC : ∀ N' ≤ P.N (p + 1) ^ 4, ((P.d : ℝ) + 1) ^ (2 * P.Lambda (p + 1)) *
      coupleT P G.Cφ p N' ^ (8 * P.Lambda (p + 1)) * (2 * P.C₁) ^ (N' + 1) * P.δ ^ (6 * P.ν * N') *
      P.L ^ (-P.η ^ 7) ≤ P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)))
    (Creg : ℕ → ℝ) (hreg : RegularFamilyBound P (inputsF P Rr) p Creg) :
    ‖∑ᶠ LB ∈ {LB : LayeredGarden 4 | LB.garden.sig = ζ ∧ (CompCond P p LB ∧ compData p LB = e) ∧
        MinimalAt LB.garden (τ (.inl 0)) (Finset.univ.image fun i => τ (.inl i))},
        kernelKgen P.L P.γ P.δ (inputsF P Rr) LB (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k nB 0‖ ≤
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
          else 0 := by
  refine piece2_norm_le P (inputsF P Rr) p N τ ζ e he tt k nB hF
    (fun c => c.1 ≤ N ∧ ∀ i, c.2 i ≤ P.N (p + 1)) (fun c => c.1 ≤ N ∧ ∀ i, c.2 i ≤ P.N (p + 1))
    (fun c c' h => joint2_allowed P p N τ e he hev c c' h) _ _ ?_ ?_
  · intro c _ ⟨hc, hv⟩
    exact couple_set_bound C₀ P G hp Rr hRr hR1 (hc.trans hN) (fun i => nB (τ (.inl i))) k (fun i => tt (τ (.inl i))) (fun i => htt _) c.2
      (hnumC c.1 (hc.trans hN)) Creg hreg _
      (fun LB h => (Ccomp2_mem_iff P p N ζ τ hC c hc hv LB).1 h)
      (fun LB h => (Ccomp2_mem_iff P p N ζ τ hC c hc hv LB).2 h)
  · intro c _ ⟨hc, hv⟩
    exact couple_set_bound C₀ P G hp Rr hRr hR1 (hc.trans hN) (fun i => nB (τ (.inr i))) k (fun i => tt (τ (.inr i))) (fun i => htt _) c.2
      (hnumC c.1 (hc.trans hN)) Creg hreg _
      (fun LB h => (Dcomp2_mem_iff P p N ζ τ hD c hc hv LB).1 h)
      (fun LB h => (Dcomp2_mem_iff P p N ζ τ hD c hc hv LB).2 h)

end WaveTurbulence.FlowerP7
