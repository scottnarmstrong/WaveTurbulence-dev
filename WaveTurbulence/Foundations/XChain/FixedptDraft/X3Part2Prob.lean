/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3Part2Det
public import WaveTurbulence.Foundations.XChain.FlowerDraft.X2Est
public import WaveTurbulence.Foundations.XChain.WaveBDraft.CoreProbes

/-!
# X3 Part2Prob: the probability of the Part 2 event

**Statement** (`prob_not_part2Event`). Assume `X2Body Pm P` (moments of `flowerest1`). Fix a sample space with
the ansatz up to `p`, a kind, `ζ`, and parameters `π` with `q = 2Pm`, `B > 0`, `v > 0`. Then
`μ(F_p ∩ {a(p) ∉ part2Event}) ≤ probSum`, where `probSum` is the explicit sum over the test points of
`2^{q−1}(J^q C + h^{q−1} C') / λ^q`. Here `C`, `C'` are the `flowerest1` bounds
`3 x2Bound · kindGain` of the plain and `dRoot` pieces.

Proof:
- union over the test points (countable);
- Chebyshev in `q`;
- the moments of the time-sup functional (`timeSup_moment`), fed by `X2Body` at interior times. On `F_p` the
  data are summable, so the masked kernels are the kernels of `flowerest1`.

Also here: `leafMax_le`, i.e. the trees of a kind have at most `6 N + 3` leaves.
-/

@[expose] public section

open WaveTurbulence.X2E
namespace WaveTurbulence.Fixedpt

open MeasureTheory Set SysAPI FTree
open scoped ENNReal

variable {d : ℕ}

/-! ## Leaf counts -/

theorem order_toTree : ∀ F : FTree, F.toTree.order = F.order
  | flower => rfl
  | node i F T₁ T₂ => by
    have ih := order_toTree F
    unfold FTree.toTree
    split_ifs <;> simp only [TTree.order, FTree.order, ih] <;> omega

theorem card_gleaf_single (T : TTree) : Fintype.card (GLeaf (single T)) = 2 * T.order + 1 := by
  rw [← WaveBProbes.card_leaves T]
  let e : GLeaf (single T) ≃ {x // x ∈ T.leaves} :=
    { toFun := fun a => ⟨a.1.2, a.2⟩
      invFun := fun x => ⟨(0, x.1), x.2⟩
      left_inv := fun a => by
        obtain ⟨⟨i, x⟩, hx⟩ := a
        have : i = 0 := Subsingleton.elim _ _
        subst this
        rfl
      right_inv := fun x => rfl }
  rw [Fintype.card_congr e, Fintype.card_coe]

theorem order_le_of_mem_kindTrees {Ntr : ℕ} {kind : FlowerKind} {F : FTree} (hF : F ∈ kindTrees Ntr kind) :
    F.order ≤ 3 * Ntr + 1 := by
  cases kind with
  | X =>
    have := (Finset.mem_filter.1 hF).1
    rw [mem_ftreesLE] at this
    omega
  | Y =>
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hF
    have hx' := (Finset.mem_filter.1 hx).1
    simp only [Rind, Finset.mem_product, Finset.mem_univ, true_and, mem_ftreesLE, mem_treesLE] at hx'
    simp only [rootOf, FTree.order]
    omega
  | W =>
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hF
    have hx' := (Finset.mem_filter.1 hx).1
    simp only [Wind', Finset.mem_product, Finset.mem_univ, true_and, mem_ftreesLE, mem_treesLE] at hx'
    rw [order_bottomOf]
    omega

/-- **The trees of a kind have at most `6N + 3` leaves.** -/
theorem leafMax_le (Ntr : ℕ) (kind : FlowerKind) : leafMax Ntr kind ≤ 6 * Ntr + 3 := by
  unfold leafMax
  refine Finset.sup_le fun F hF => ?_
  rw [card_gleaf_single, order_toTree]
  have := order_le_of_mem_kindTrees hF
  omega

/-! ## One piece: Chebyshev and the time-sup moments -/

section Piece

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]

theorem prob_PhiT_le (p : ℕ) {F : Set Ω} (hF : MeasurableSet F) {q h : ℝ} (hq : 1 < q) {J : ℕ}
    {K K' : Ω → ℝ → ℝ → ℂ} (hKm : Measurable fun z : Ω × ℝ × ℝ => K z.1 z.2.1 z.2.2)
    (hK'm : Measurable fun z : Ω × ℝ × ℝ => K' z.1 z.2.1 z.2.2) {C C' : ℝ≥0∞}
    (hC : ∀ s ∈ Ioo (p : ℝ) (p + 1), ∀ t ∈ Ioo s (p + 1), ∫⁻ ω in F, ‖K ω t s‖ₑ ^ q ∂μ ≤ C)
    (hC' : ∀ s ∈ Ioo (p : ℝ) (p + 1), ∀ u ∈ Ioo s (p + 1), ∫⁻ ω in F, ‖K' ω u s‖ₑ ^ q ∂μ ≤ C')
    {lam : ℝ≥0∞} (hlam : lam ≠ 0) (hlam' : lam ≠ ⊤) :
    μ (F ∩ {ω | lam < PhiT p q h J (K ω) (K' ω)}) ≤
      2 ^ (q - 1) * ((J : ℝ≥0∞) ^ q * C + ENNReal.ofReal h ^ (q - 1) * C') / lam ^ q := by
  have hq0 : 0 < q := by linarith
  have hΦm : Measurable fun ω => PhiT p q h J (K ω) (K' ω) := measurable_PhiT p q h J hKm hK'm
  have hsub : F ∩ {ω | lam < PhiT p q h J (K ω) (K' ω)} ⊆
      {ω | lam ^ q ≤ PhiT p q h J (K ω) (K' ω) ^ q} ∩ F := fun ω hω =>
    ⟨ENNReal.rpow_le_rpow hω.2.le hq0.le, hω.1⟩
  calc μ (F ∩ {ω | lam < PhiT p q h J (K ω) (K' ω)})
      ≤ μ ({ω | lam ^ q ≤ PhiT p q h J (K ω) (K' ω) ^ q} ∩ F) := measure_mono hsub
    _ = μ.restrict F {ω | lam ^ q ≤ PhiT p q h J (K ω) (K' ω) ^ q} := (Measure.restrict_apply' hF).symm
    _ ≤ (∫⁻ ω in F, PhiT p q h J (K ω) (K' ω) ^ q ∂μ) / lam ^ q :=
        meas_ge_le_lintegral_div (hΦm.pow_const q).aemeasurable
          (ENNReal.rpow_pos (pos_iff_ne_zero.2 hlam) hlam').ne' (ENNReal.rpow_ne_top_of_nonneg hq0.le hlam')
    _ ≤ 2 ^ (q - 1) * ((J : ℝ≥0∞) ^ q * C + ENNReal.ofReal h ^ (q - 1) * C') / lam ^ q := by
        gcongr
        exact timeSup_moment μ hq hKm hK'm hC hC'

end Piece

/-! ## The moments of the masked kernels -/

universe u_1

section Moments

variable (P : WTParams) (Pm : ℕ) {Ω : Type u_1} [MeasurableSpace Ω] (μ : Measure Ω)

theorem enorm_rpow_natCast (z : ℂ) (n : ℕ) : ‖z‖ₑ ^ ((n : ℕ) : ℝ) = ENNReal.ofReal (‖z‖ ^ n) := by
  rw [ENNReal.rpow_natCast, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]

/-- **A moment of `flowerest1`, for a function equal to the kernel on `F_p`.** -/
theorem lintegral_rpow_le_x2 (hX2 : X2Body.{u_1} Pm P) [IsProbabilityMeasure μ] {g : (Fin P.d → ℤ) → Ω → ℂ}
    (hg : IsGaussianData μ g) {p : ℕ} (hp : p < P.D) {a : Ω → ℝ → (Fin P.d → ℤ) → ℂ} {Fev : ℕ → Set Ω}
    {R : ℕ → Mom P.d → ℝ} {E : ℕ → (Fin P.d → ℤ) → ℝ}
    {Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ}
    (hA : ∀ q ≤ p, AnsatzAt P μ g a Fev R E Et q) (kind : FlowerKind) (pat : FixPat)
    (hpat : pat = .plain ∨ pat = .dRoot) (dagger : Option (Fin 3 → Mom P.d)) (cut1 cut2 : Option ℕ)
    (k k' : Fin P.d → ℤ) (hcut : ∀ j₂ ∈ cut2, ∃ j₁ ∈ cut1, ((2 : ℝ) ^ j₁ * P.L) ^ 10 ≤ ‖latticePoint P.L k‖)
    (ζ : ℤˣ) {t s : ℝ} (ht : t ∈ Ioo (p : ℝ) (p + 1)) (hs : s ∈ Ioo (p : ℝ) t) {G : Ω → ℂ}
    (hG : ∀ ω ∈ Fev p, G ω = randK P a p kind pat dagger cut1 cut2 ζ t s k k' ω) :
    ∫⁻ ω in Fev p, ‖G ω‖ₑ ^ ((2 * Pm : ℕ) : ℝ) ∂μ ≤
      ENNReal.ofReal (3 * x2Bound P Pm p ζ k k' (fun _ : Fin (2 * Pm) => pat) cut1 cut2 *
        kindGain (P.N (p + 1)) kind) := by
  have hFm : MeasurableSet (Fev p) := SysAPI.AnsatzAt.measurableSet (hA p le_rfl)
  obtain ⟨hint, hbd⟩ := hX2 Ω μ g hg p hp a Fev R E Et hA t ht s hs k k' ζ kind pat dagger cut1 cut2 hpat hcut
  calc ∫⁻ ω in Fev p, ‖G ω‖ₑ ^ ((2 * Pm : ℕ) : ℝ) ∂μ
      = ∫⁻ ω in Fev p, ENNReal.ofReal (‖randK P a p kind pat dagger cut1 cut2 ζ t s k k' ω‖ ^ (2 * Pm)) ∂μ := by
        refine setLIntegral_congr_fun hFm fun ω hω => ?_
        rw [hG ω hω, enorm_rpow_natCast]
    _ = ENNReal.ofReal (∫ ω in Fev p, ‖randK P a p kind pat dagger cut1 cut2 ζ t s k k' ω‖ ^ (2 * Pm) ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => by positivity)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hbd

end Moments

/-! ## The probability of the event -/

section Prob

variable (P : WTParams) (Pm : ℕ) (p : ℕ) (kind : FlowerKind) (ζ : ℤˣ) (π : P2Par)

theorem mem_testB_ge {j₁ j₂ : ℕ} {k : Fin P.d → ℤ} (hk : k ∈ testB P.L (P.N (p + 1)) kind j₁ j₂)
    (hL : 1 ≤ P.L) : ((2 : ℝ) ^ j₁ * P.L) ^ 10 ≤ ‖latticePoint P.L k‖ := by
  rcases Finset.mem_union.1 hk with h | h
  · exact (Finset.mem_filter.1 h).2
  · have hL0 : 0 < P.L := by linarith
    exact ((repSet_spec hL (Mrep_nonneg P.L _ kind hL0 j₁ j₂) _).1 h).1

/-- The term of a regime-A test point. -/
noncomputable def termA (j : ℕ) (k k' : Fin P.d → ℤ) : ℝ≥0∞ :=
  2 ^ (π.q - 1) * ((π.JA : ℝ≥0∞) ^ π.q *
      ENNReal.ofReal (3 * x2Bound P Pm p ζ k k' (fun _ : Fin (2 * Pm) => FixPat.plain) (some j) none *
        kindGain (P.N (p + 1)) kind) +
    ENNReal.ofReal π.hA ^ (π.q - 1) *
      ENNReal.ofReal (3 * x2Bound P Pm p ζ k k' (fun _ : Fin (2 * Pm) => FixPat.dRoot) (some j) none *
        kindGain (P.N (p + 1)) kind)) / ENNReal.ofReal (lamA P.L ζ π j k k') ^ π.q

/-- The term of a regime-B test point. -/
noncomputable def termB (j₁ j₂ : ℕ) (k k' : Fin P.d → ℤ) : ℝ≥0∞ :=
  2 ^ (π.q - 1) * ((π.JB j₂ : ℝ≥0∞) ^ π.q *
      ENNReal.ofReal (3 * x2Bound P Pm p ζ k k' (fun _ : Fin (2 * Pm) => FixPat.plain) (some j₁) (some j₂) *
        kindGain (P.N (p + 1)) kind) +
    ENNReal.ofReal (π.hB j₂) ^ (π.q - 1) *
      ENNReal.ofReal (3 * x2Bound P Pm p ζ k k' (fun _ : Fin (2 * Pm) => FixPat.dRoot) (some j₁) (some j₂) *
        kindGain (P.N (p + 1)) kind)) /
    ENNReal.ofReal (lamB P.L (P.N (p + 1)) kind ζ π j₁ j₂ k k') ^ π.q

/-- The bound of the probability of the complement of the event. -/
noncomputable def probSum : ℝ≥0∞ :=
  (∑' j, ∑ k ∈ testA P.L j, ∑' k', termA P Pm p kind ζ π j k k') +
    ∑' j₁, ∑' j₂, ∑ _x ∈ dagBoxK (d := P.d) P.L (P.N (p + 1)) kind j₁,
      ∑ k ∈ testB P.L (P.N (p + 1)) kind j₁ j₂, ∑' k', termB P Pm p kind ζ π j₁ j₂ k k'

/-- **The probability of the complement of the Part 2 event.** -/
theorem prob_not_part2Event (hX2 : X2Body.{u_1} Pm P) (hπq : π.q = (2 * Pm : ℕ))
    (hπ : π.Valid) (hB : 0 < π.B) (hv : ∀ j, 0 < π.v j) (hL : 1 ≤ P.L)
    {Ω : Type u_1} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {g : (Fin P.d → ℤ) → Ω → ℂ}
    (hg : IsGaussianData μ g) (hp : p < P.D) {a : Ω → ℝ → (Fin P.d → ℤ) → ℂ} {Fev : ℕ → Set Ω}
    {R : ℕ → Mom P.d → ℝ} {E : ℕ → (Fin P.d → ℤ) → ℝ}
    {Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ}
    (hA : ∀ q ≤ p, AnsatzAt P μ g a Fev R E Et q) :
    μ (Fev p ∩ {ω | a ω p ∉ part2Event P.L P.γ P.δ p (P.N (p + 1)) kind ζ π}) ≤
      probSum P Pm p kind ζ π := by
  set N := P.N (p + 1)
  have hL0 : 0 < P.L := by linarith
  have hAp := hA p le_rfl
  have hFm : MeasurableSet (Fev p) := SysAPI.AnsatzAt.measurableSet hAp
  have hpI : (p : ℝ) ∈ Icc (0 : ℝ) p := ⟨Nat.cast_nonneg p, le_rfl⟩
  have haP : Measurable fun ω => a ω p :=
    measurable_pi_iff.mpr fun k => SysAPI.AnsatzAt.measurable hAp hpI k
  have hsum : ∀ ω ∈ Fev p, Summable fun k => ‖a ω p k‖ := fun ω hω =>
    SysAPI.IsASolution.summable_norm hL0 (SysAPI.AnsatzAt.isASolution hAp hω) hpI
  have hmap : Measurable fun z : Ω × ℝ × ℝ => ((a z.1 p, z.2.1, z.2.2) : ((Fin P.d → ℤ) → ℂ) × ℝ × ℝ) :=
    (haP.comp measurable_fst).prodMk ((measurable_fst.comp measurable_snd).prodMk
      (measurable_snd.comp measurable_snd))
  have hq : 1 < π.q := hπ.hq
  have hq' : ((2 * Pm : ℕ) : ℝ) = π.q := hπq.symm
  -- the moments of one piece, plain and `dRoot`
  have hmomPl : ∀ (dagger : Option (Fin 3 → Mom P.d)) (cut1 cut2 : Option ℕ) (k k' : Fin P.d → ℤ),
      (∀ j₂ ∈ cut2, ∃ j₁ ∈ cut1, ((2 : ℝ) ^ j₁ * P.L) ^ 10 ≤ ‖latticePoint P.L k‖) →
      ∀ s ∈ Ioo (p : ℝ) (p + 1), ∀ t ∈ Ioo s (p + 1),
        ∫⁻ ω in Fev p, ‖Kpl P.L P.γ P.δ p N kind dagger cut1 cut2 ζ k k' (a ω p) t s‖ₑ ^ π.q ∂μ ≤
          ENNReal.ofReal (3 * x2Bound P Pm p ζ k k' (fun _ : Fin (2 * Pm) => FixPat.plain) cut1 cut2 *
            kindGain N kind) := by
    intro dagger cut1 cut2 k k' hcut s hs t ht
    rw [← hq']
    exact lintegral_rpow_le_x2 P Pm μ hX2 hg hp hA kind .plain (Or.inl rfl) dagger cut1 cut2 k k' hcut ζ
      ⟨hs.1.trans ht.1, ht.2⟩ ⟨hs.1, ht.1⟩ fun ω hω =>
        Kpl_of_summable P.L P.γ P.δ p N kind dagger cut1 cut2 ζ k k' (hsum ω hω) ⟨hs.1, ht.1, ht.2.le⟩
  have hmomDr : ∀ (dagger : Option (Fin 3 → Mom P.d)) (cut1 cut2 : Option ℕ) (k k' : Fin P.d → ℤ),
      (∀ j₂ ∈ cut2, ∃ j₁ ∈ cut1, ((2 : ℝ) ^ j₁ * P.L) ^ 10 ≤ ‖latticePoint P.L k‖) →
      ∀ s ∈ Ioo (p : ℝ) (p + 1), ∀ u ∈ Ioo s (p + 1),
        ∫⁻ ω in Fev p, ‖Kdr P.L P.γ P.δ p N kind dagger cut1 cut2 ζ k k' (a ω p) u s‖ₑ ^ π.q ∂μ ≤
          ENNReal.ofReal (3 * x2Bound P Pm p ζ k k' (fun _ : Fin (2 * Pm) => FixPat.dRoot) cut1 cut2 *
            kindGain N kind) := by
    intro dagger cut1 cut2 k k' hcut s hs u hu
    rw [← hq']
    exact lintegral_rpow_le_x2 P Pm μ hX2 hg hp hA kind .dRoot (Or.inr rfl) dagger cut1 cut2 k k' hcut ζ
      ⟨hs.1.trans hu.1, hu.2⟩ ⟨hs.1, hu.1⟩ fun ω hω =>
        Kdr_of_summable P.L P.γ P.δ p N kind dagger cut1 cut2 ζ k k' (hsum ω hω) ⟨hs.1, hu.1, hu.2⟩
  have hmK : ∀ (dagger : Option (Fin 3 → Mom P.d)) (cut1 cut2 : Option ℕ) (k k' : Fin P.d → ℤ),
      Measurable fun z : Ω × ℝ × ℝ => Kpl P.L P.γ P.δ p N kind dagger cut1 cut2 ζ k k' (a z.1 p) z.2.1 z.2.2 :=
    fun dagger cut1 cut2 k k' => (measurable_Kpl_fst P.L P.γ P.δ p N kind ζ dagger cut1 cut2 k k').comp hmap
  have hmK' : ∀ (dagger : Option (Fin 3 → Mom P.d)) (cut1 cut2 : Option ℕ) (k k' : Fin P.d → ℤ),
      Measurable fun z : Ω × ℝ × ℝ => Kdr P.L P.γ P.δ p N kind dagger cut1 cut2 ζ k k' (a z.1 p) z.2.1 z.2.2 :=
    fun dagger cut1 cut2 k k' => (measurable_Kdr_fst P.L P.γ P.δ p N kind ζ dagger cut1 cut2 k k').comp hmap
  -- the pieces
  have hW : ∀ k k' : Fin P.d → ℤ, 0 < wtm P.L ζ π.A k k' := fun k k' =>
    Real.rpow_pos_of_pos (jbr_pos'' _) _
  have hpA : ∀ j (k k' : Fin P.d → ℤ), μ (Fev p ∩ {ω | ENNReal.ofReal (lamA P.L ζ π j k k') <
      PhiA P.L P.γ P.δ p N kind ζ π j k k' (a ω p)}) ≤ termA P Pm p kind ζ π j k k' := by
    intro j k k'
    have hlam : 0 < lamA P.L ζ π j k k' := mul_pos (mul_pos hB (by positivity)) (hW k k')
    exact prob_PhiT_le μ p hFm hq (hmK _ _ _ k k') (hmK' _ _ _ k k')
      (hmomPl none (some j) none k k' (by simp)) (hmomDr none (some j) none k k' (by simp))
      (ENNReal.ofReal_pos.2 hlam).ne' ENNReal.ofReal_ne_top
  have hpB : ∀ j₁ j₂, ∀ x ∈ dagBoxK (d := P.d) P.L N kind j₁, ∀ k ∈ testB P.L N kind j₁ j₂, ∀ k',
      μ (Fev p ∩ {ω | ENNReal.ofReal (lamB P.L N kind ζ π j₁ j₂ k k') <
        PhiB P.L P.γ P.δ p N kind ζ π j₁ j₂ x k k' (a ω p)}) ≤ termB P Pm p kind ζ π j₁ j₂ k k' := by
    intro j₁ j₂ x hx k hk k'
    have hcard : (0 : ℝ) < (dagBoxK (d := P.d) P.L N kind j₁).card := by
      exact_mod_cast Finset.card_pos.2 ⟨x, hx⟩
    have hlam : 0 < lamB P.L N kind ζ π j₁ j₂ k k' :=
      mul_pos (mul_pos (mul_pos hB (by positivity)) (div_pos (hv j₂) hcard)) (hW k k')
    have hcut : ∀ j₂' ∈ some j₂, ∃ j₁' ∈ some j₁, ((2 : ℝ) ^ j₁' * P.L) ^ 10 ≤ ‖latticePoint P.L k‖ :=
      fun _ _ => ⟨j₁, rfl, mem_testB_ge P p kind hk hL⟩
    exact prob_PhiT_le μ p hFm hq (hmK _ _ _ k k') (hmK' _ _ _ k k')
      (hmomPl _ (some j₁) (some j₂) k k' hcut) (hmomDr _ (some j₁) (some j₂) k k' hcut)
      (ENNReal.ofReal_pos.2 hlam).ne' ENNReal.ofReal_ne_top
  -- the union
  have hsub : Fev p ∩ {ω | a ω p ∉ part2Event P.L P.γ P.δ p N kind ζ π} ⊆
      (⋃ j, ⋃ k ∈ testA P.L j, ⋃ k', Fev p ∩ {ω | ENNReal.ofReal (lamA P.L ζ π j k k') <
        PhiA P.L P.γ P.δ p N kind ζ π j k k' (a ω p)}) ∪
      ⋃ j₁, ⋃ j₂, ⋃ x ∈ dagBoxK (d := P.d) P.L N kind j₁, ⋃ k ∈ testB P.L N kind j₁ j₂, ⋃ k',
        Fev p ∩ {ω | ENNReal.ofReal (lamB P.L N kind ζ π j₁ j₂ k k') <
          PhiB P.L P.γ P.δ p N kind ζ π j₁ j₂ x k k' (a ω p)} := by
    rintro ω ⟨hω, hnot⟩
    simp only [part2Event, mem_ofPred_eq, not_and_or, not_forall, not_le, exists_prop] at hnot
    rcases hnot with ⟨j, k, hk, k', h⟩ | ⟨j₁, j₂, x, hx, k, hk, k', h⟩
    · exact Or.inl (mem_iUnion.2 ⟨j, mem_iUnion₂.2 ⟨k, hk, mem_iUnion.2 ⟨k', hω, h⟩⟩⟩)
    · exact Or.inr (mem_iUnion.2 ⟨j₁, mem_iUnion.2 ⟨j₂, mem_iUnion₂.2 ⟨x, hx, mem_iUnion₂.2 ⟨k, hk,
        mem_iUnion.2 ⟨k', hω, h⟩⟩⟩⟩⟩)
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add ?_ ?_))
  · refine (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun j => ?_)
    refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
    exact (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun k' => hpA j k k')
  · refine (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun j₁ => ?_)
    refine (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun j₂ => ?_)
    refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun x hx => ?_)
    refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
    exact (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun k' => hpB j₁ j₂ x hx k hk k')

end Prob

end WaveTurbulence.Fixedpt
