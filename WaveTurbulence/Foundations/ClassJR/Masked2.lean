/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.Masked

/-!
# Composition and sandwich of masked class `J`/`R` operators

The two operator steps of DH21 Lemma 5.9 for operators on disjoint subsets of a global variable set
(all over a common parameter space `P`):

* `MJR.comp` (concatenation, Lemmas 5.3–5.5): `(J + R) ∘ (J + R)` is of class `J` in `S₁ ∪ S₂`
  when `S₁`, `S₂` are disjoint, with norm `≤ Ccp θ N₁ N₂`;
* `MJR.sandwich` (enclosure, Lemmas 5.6–5.7): `I_{εα_v} T I_{μ-εα_v}` is class `J` plus class `R`
  (special variable `v`) in `insert v S`, for a new variable `v ∉ S` and a measurable parameter
  function `μ = μf p`, with norm `≤ Csw θ N`.
-/

public section

open MeasureTheory Filter Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

section Zero

theorem keqOn_kcomp_zero_right {K L : ℝ → ℝ → ℂ} (hL : KEqOn L fun _ _ => 0) :
    KEqOn (kcomp K L) fun _ _ => 0 := by
  intro t s h0 h1 h2
  rw [KEqOn.kcomp (KEqOn.refl K) hL t s h0 h1 h2]
  simp [kcomp]

theorem keqOn_kcomp_zero_left {K L : ℝ → ℝ → ℂ} (hK : KEqOn K fun _ _ => 0) :
    KEqOn (kcomp K L) fun _ _ => 0 := by
  intro t s h0 h1 h2
  rw [KEqOn.kcomp hK (KEqOn.refl L) t s h0 h1 h2]
  simp [kcomp]

theorem keqOn_sandwich_zero {A B K : ℝ → ℝ → ℂ} (hK : KEqOn K fun _ _ => 0) :
    KEqOn (kcomp (kcomp A K) B) fun _ _ => 0 :=
  keqOn_kcomp_zero_left (keqOn_kcomp_zero_right hK)

end Zero

section Embed

variable {V : Type}

theorem injective_sumElim_of_disjoint {ι₁ ι₂ : Type} {f₁ : ι₁ → V} {f₂ : ι₂ → V}
    (hf₁ : Function.Injective f₁) (hf₂ : Function.Injective f₂)
    (hd : Disjoint (Set.range f₁) (Set.range f₂)) : Function.Injective (Sum.elim f₁ f₂) :=
  hf₁.sumElim hf₂ fun a b hab =>
    Set.disjoint_left.1 hd (Set.mem_range_self a) (hab ▸ Set.mem_range_self b)

theorem injective_optionElim {ι : Type} {f : ι → V} (hf : Function.Injective f) {v : V}
    (hv : v ∉ Set.range f) : Function.Injective fun o : Option ι => o.elim v f := by
  intro a b hab
  rcases a with _ | a <;> rcases b with _ | b
  · rfl
  · exact absurd ⟨b, hab.symm⟩ hv
  · exact absurd ⟨a, hab⟩ hv
  · exact congrArg some (hf hab)

end Embed

section Comp

variable {P : Type*} [MeasurableSpace P] {V : Type} {θ A N₁ N₂ : ℝ} {S₁ S₂ : Set V}
variable {T₁ T₂ : P → (V → ℝ) → ℝ → ℝ → ℂ}

theorem measurable_diag' : Measurable fun p : P => (p, p) := measurable_id.prodMk measurable_id

/-- **Masked Lemma 5.3.** -/
theorem MJ.comp (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hA : A0 ≤ A) (h₁ : MJ θ A N₁ S₁ T₁)
    (h₂ : MJ θ A N₂ S₂ T₂) (hd : Disjoint S₁ S₂) :
    MJ θ A (CJJ * N₁ * N₂) (S₁ ∪ S₂) fun p α => kcomp (T₁ p α) (T₂ p α) := by
  obtain ⟨ι₁, _, f₁, hf₁, hr₁, U₁, hU₁, he₁⟩ := h₁
  obtain ⟨ι₂, _, f₂, hf₂, hr₂, U₂, hU₂, he₂⟩ := h₂
  refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim f₁ f₂,
    injective_sumElim_of_disjoint hf₁ hf₂ (by rw [hr₁, hr₂]; exact hd),
    by rw [Set.Sum.elim_range, hr₁, hr₂], _,
    (ClassJP.comp h0 h1 hA hU₁ hU₂).comap measurable_diag', fun p α => ?_⟩
  exact KEqOn.kcomp (he₁ p α) (he₂ p α)

/-- **Masked Lemma 5.4, `J R`.** -/
theorem MJ.comp_R (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) {v₂ : V} (h₁ : MJ θ A N₁ S₁ T₁)
    (h₂ : MR θ A N₂ S₂ v₂ T₂) (hd : Disjoint S₁ S₂) :
    MJ θ A (CJR θ * N₁ * N₂) (S₁ ∪ S₂) fun p α => kcomp (T₁ p α) (T₂ p α) := by
  obtain ⟨ι₁, _, f₁, hf₁, hr₁, U₁, hU₁, he₁⟩ := h₁
  obtain ⟨ι₂, _, f₂, hf₂, hr₂, -, U₂, hU₂, he₂⟩ := h₂
  refine ⟨ι₁ ⊕ Option ι₂, inferInstance, Sum.elim f₁ f₂,
    injective_sumElim_of_disjoint hf₁ hf₂ (by rw [hr₁, hr₂]; exact hd),
    by rw [Set.Sum.elim_range, hr₁, hr₂], _,
    (ClassJP.comp_R h0 h1 hA hU₁ hU₂).comap measurable_diag', fun p α => ?_⟩
  exact KEqOn.kcomp (he₁ p α) (he₂ p α)

/-- **Masked Lemma 5.4, `R J`.** -/
theorem MR.comp_J (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) {v₁ : V} (h₁ : MR θ A N₁ S₁ v₁ T₁)
    (h₂ : MJ θ A N₂ S₂ T₂) (hd : Disjoint S₁ S₂) :
    MJ θ A (CJR θ * N₁ * N₂) (S₁ ∪ S₂) fun p α => kcomp (T₁ p α) (T₂ p α) := by
  obtain ⟨ι₁, _, f₁, hf₁, hr₁, -, U₁, hU₁, he₁⟩ := h₁
  obtain ⟨ι₂, _, f₂, hf₂, hr₂, U₂, hU₂, he₂⟩ := h₂
  refine ⟨Option ι₁ ⊕ ι₂, inferInstance, Sum.elim f₁ f₂,
    injective_sumElim_of_disjoint hf₁ hf₂ (by rw [hr₁, hr₂]; exact hd),
    by rw [Set.Sum.elim_range, hr₁, hr₂], _,
    (ClassRP.comp_J h0 h1 hA hU₁ hU₂).comap measurable_diag', fun p α => ?_⟩
  exact KEqOn.kcomp (he₁ p α) (he₂ p α)

/-- **Masked Lemma 5.5.** -/
theorem MR.comp_R (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) {v₁ v₂ : V}
    (h₁ : MR θ A N₁ S₁ v₁ T₁) (h₂ : MR θ A N₂ S₂ v₂ T₂) (hd : Disjoint S₁ S₂) :
    MJ θ A (CRR θ * N₁ * N₂) (S₁ ∪ S₂) fun p α => kcomp (T₁ p α) (T₂ p α) := by
  obtain ⟨ι₁, _, f₁, hf₁, hr₁, -, U₁, hU₁, he₁⟩ := h₁
  obtain ⟨ι₂, _, f₂, hf₂, hr₂, -, U₂, hU₂, he₂⟩ := h₂
  refine ⟨Option ι₁ ⊕ Option ι₂, inferInstance, Sum.elim f₁ f₂,
    injective_sumElim_of_disjoint hf₁ hf₂ (by rw [hr₁, hr₂]; exact hd),
    by rw [Set.Sum.elim_range, hr₁, hr₂], _,
    (ClassRP.comp_R h0 h1 hA hU₁ hU₂).comap measurable_diag', fun p α => ?_⟩
  exact KEqOn.kcomp (he₁ p α) (he₂ p α)

/-- **The concatenation step of DH21 Lemma 5.9, masked**: `(J + R) ∘ (J + R)` is of class `J`. -/
theorem MJR.comp (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (h₁ : MJR θ A N₁ S₁ T₁)
    (h₂ : MJR θ A N₂ S₂ T₂) (hd : Disjoint S₁ S₂) :
    MJ θ A (Ccp θ * N₁ * N₂) (S₁ ∪ S₂) fun p α => kcomp (T₁ p α) (T₂ p α) := by
  obtain ⟨NJ₁, NR₁, TJ₁, TR₁, hJ₁, hR₁, hN₁, he₁⟩ := h₁
  obtain ⟨NJ₂, NR₂, TJ₂, TR₂, hJ₂, hR₂, hN₂, he₂⟩ := h₂
  have a1 := hJ₁.nonneg; have a2 := hR₁.nonneg; have a3 := hJ₂.nonneg; have a4 := hR₂.nonneg
  have hC1 := CJJ_nonneg; have hC2 := CJR_nonneg h0 h1; have hC3 := CRR_nonneg θ
  have hJJ := MJ.comp h0 h1.le hA hJ₁ hJ₂ hd
  have hJR : MJ θ A (CJR θ * NJ₁ * NR₂) (S₁ ∪ S₂) fun p α => kcomp (TJ₁ p α) (TR₂ p α) := by
    rcases hR₂ with ⟨v₂, hR₂⟩ | ⟨-, hz⟩
    · exact MJ.comp_R h0 h1 hA hJ₁ hR₂ hd
    · exact (hJJ.zero_of.mono (by positivity)).congr fun p α => keqOn_kcomp_zero_right (hz p α)
  have hRJ : MJ θ A (CJR θ * NR₁ * NJ₂) (S₁ ∪ S₂) fun p α => kcomp (TR₁ p α) (TJ₂ p α) := by
    rcases hR₁ with ⟨v₁, hR₁⟩ | ⟨-, hz⟩
    · exact MR.comp_J h0 h1 hA hR₁ hJ₂ hd
    · exact (hJJ.zero_of.mono (by positivity)).congr fun p α => keqOn_kcomp_zero_left (hz p α)
  have hRR : MJ θ A (CRR θ * NR₁ * NR₂) (S₁ ∪ S₂) fun p α => kcomp (TR₁ p α) (TR₂ p α) := by
    rcases hR₁ with ⟨v₁, hR₁⟩ | ⟨-, hz⟩
    · rcases hR₂ with ⟨v₂, hR₂⟩ | ⟨-, hz₂⟩
      · exact MR.comp_R h0 h1 hA hR₁ hR₂ hd
      · exact (hJJ.zero_of.mono (by positivity)).congr fun p α =>
          keqOn_kcomp_zero_right (hz₂ p α)
    · exact (hJJ.zero_of.mono (by positivity)).congr fun p α => keqOn_kcomp_zero_left (hz p α)
  have hsum := ((hJJ.add hJR).add hRJ).add hRR
  have hCc : 0 ≤ Ccp θ := by unfold Ccp; positivity
  refine (hsum.mono ?_).congr fun p α => ?_
  · have e1 : CJJ ≤ Ccp θ := by unfold Ccp; linarith
    have e2 : CJR θ ≤ Ccp θ := by unfold Ccp; linarith
    have e3 : CRR θ ≤ Ccp θ := by unfold Ccp; linarith
    calc CJJ * NJ₁ * NJ₂ + CJR θ * NJ₁ * NR₂ + CJR θ * NR₁ * NJ₂ + CRR θ * NR₁ * NR₂
        ≤ Ccp θ * NJ₁ * NJ₂ + Ccp θ * NJ₁ * NR₂ + Ccp θ * NR₁ * NJ₂ + Ccp θ * NR₁ * NR₂ := by
          gcongr
      _ = Ccp θ * (NJ₁ + NR₁) * (NJ₂ + NR₂) := by ring
      _ ≤ Ccp θ * N₁ * N₂ :=
          mul_le_mul (mul_le_mul_of_nonneg_left hN₁ hCc) hN₂ (by positivity)
            (mul_nonneg hCc ((add_nonneg a1 a2).trans hN₁))
  · obtain ⟨KJ₁, cJ₁, hKJ₁⟩ := hJ₁.exists_rep p α
    obtain ⟨KR₁, cR₁, hKR₁⟩ := hR₁.exists_rep p α
    obtain ⟨KJ₂, cJ₂, hKJ₂⟩ := hJ₂.exists_rep p α
    obtain ⟨KR₂, cR₂, hKR₂⟩ := hR₂.exists_rep p α
    exact (KEqOn.kcomp (he₁ p α) (he₂ p α)).trans
      (kcomp_add_add_KEqOn hKJ₁ hKR₁ hKJ₂ hKR₂ cJ₁ cR₁ cJ₂ cR₂)

end Comp

section Sandwich

variable {P : Type*} [MeasurableSpace P] {V : Type} {θ A N : ℝ} {S : Set V}
variable {T : P → (V → ℝ) → ℝ → ℝ → ℂ}

/-- The sandwich `I_{εα_v} T I_{μ-εα_v}` with `μ = μf p`. -/
@[expose] noncomputable def sandw (ε : ℤ) (v : V) (μf : P → ℝ) (T : P → (V → ℝ) → ℝ → ℝ → ℂ) :
    P → (V → ℝ) → ℝ → ℝ → ℂ :=
  fun p α => kcomp (kcomp (iker (ε * α v)) (T p α)) (iker (μf p - ε * α v))

/-- **The enclosure step of DH21 Lemma 5.9, masked** (Lemmas 5.6–5.7): for a new variable
`v ∉ S`, `I_{εα_v} T I_{μf p - εα_v}` is class `J` plus class `R` with special variable `v`. -/
theorem MJR.sandwich (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hT : MJR θ A N S T) {v : V} (hv : v ∉ S) {μf : P → ℝ} (hμ : Measurable μf) :
    MJR θ A (Csw θ * N) (insert v S) (sandw ε v μf T) := by
  obtain ⟨NJ, NR, TJ, TR, hJ, hR, hN, he⟩ := hT
  have hNJ := hJ.nonneg
  have hNR := hR.nonneg
  have hg : Measurable fun p : P => (p, μf p) := measurable_id.prodMk hμ
  have hC1 := C56J_nonneg h0 h1; have hC2 := C56R_nonneg; have hC3 := C57J_nonneg θ
  have hC4 := C57R_nonneg h0 h1
  have hrepJ := hJ.exists_rep
  have hrepR := hR.exists_rep
  obtain ⟨ι, _, f, hf, hr, U, hU, heU⟩ := hJ
  obtain ⟨TJ₁, TR₁, hJ₁, hR₁, he₁⟩ := ClassJP.iker_comp_iker h0 h1 hA hε hU
  have hvf : v ∉ Set.range f := hr ▸ hv
  have hF := injective_optionElim hf hvf
  have hFr : Set.range (fun o : Option ι => o.elim v f) = insert v S := by
    rw [Option.range_elim, hr]
  have mJ₁ : MJ θ A (C56J θ * NJ) (insert v S)
      fun p α => TJ₁ (p, μf p) (α ∘ fun o : Option ι => o.elim v f) :=
    ⟨Option ι, inferInstance, _, hF, hFr, _, hJ₁.comap hg, fun _ _ => KEqOn.refl _⟩
  have mR₁ : MR θ A (C56R * NJ) (insert v S) v
      fun p α => TR₁ (p, μf p) (α ∘ fun o : Option ι => o.elim v f) :=
    ⟨ι, inferInstance, _, hF, hFr, rfl, _, hR₁.comap hg, fun _ _ => KEqOn.refl _⟩
  have eJ : ∀ p α, KEqOn (sandw ε v μf TJ p α) fun t s =>
      TJ₁ (p, μf p) (α ∘ fun o : Option ι => o.elim v f) t s +
        TR₁ (p, μf p) (α ∘ fun o : Option ι => o.elim v f) t s := fun p α =>
    (KEqOn.kcomp (KEqOn.kcomp (KEqOn.refl _) (heU p α)) (KEqOn.refl _)).trans
      (he₁ (p, μf p) (α ∘ fun o : Option ι => o.elim v f))
  have hlin : ∀ p α, KEqOn (sandw ε v μf T p α) fun t s =>
      sandw ε v μf TJ p α t s + sandw ε v μf TR p α t s := fun p α => by
    obtain ⟨KJ, cJ, hKJ⟩ := hrepJ p α
    obtain ⟨KR, cR, hKR⟩ := hrepR p α
    exact (KEqOn.kcomp (KEqOn.kcomp (KEqOn.refl _) (he p α)) (KEqOn.refl _)).trans
      (kcomp_kcomp_add_KEqOn hKJ hKR (continuous_iker _) (continuous_iker _) cJ cR)
  rcases hR with ⟨v₀, ι₂, _, f₂, hf₂, hr₂, -, U₂, hU₂, heU₂⟩ | ⟨-, hz⟩
  · obtain ⟨TJ₂, TR₂, hJ₂, hR₂, he₂⟩ := ClassRP.iker_comp_iker h0 h1 hA hε hU₂
    have hvf₂ : v ∉ Set.range f₂ := hr₂ ▸ hv
    have hF₂ := injective_optionElim hf₂ hvf₂
    have hFr₂ : Set.range (fun o : Option (Option ι₂) => o.elim v f₂) = insert v S := by
      rw [Option.range_elim, hr₂]
    have mJ₂ : MJ θ A (C57J θ * NR) (insert v S)
        fun p α => TJ₂ (p, μf p) (α ∘ fun o : Option (Option ι₂) => o.elim v f₂) :=
      ⟨Option (Option ι₂), inferInstance, _, hF₂, hFr₂, _, hJ₂.comap hg, fun _ _ => KEqOn.refl _⟩
    have mR₂ : MR θ A (C57R θ * NR) (insert v S) v
        fun p α => TR₂ (p, μf p) (α ∘ fun o : Option (Option ι₂) => o.elim v f₂) :=
      ⟨Option ι₂, inferInstance, _, hF₂, hFr₂, rfl, _, hR₂.comap hg, fun _ _ => KEqOn.refl _⟩
    have eR : ∀ p α, KEqOn (sandw ε v μf TR p α) fun t s =>
        TJ₂ (p, μf p) (α ∘ fun o : Option (Option ι₂) => o.elim v f₂) t s +
          TR₂ (p, μf p) (α ∘ fun o : Option (Option ι₂) => o.elim v f₂) t s := fun p α =>
      (KEqOn.kcomp (KEqOn.kcomp (KEqOn.refl _) (heU₂ p α)) (KEqOn.refl _)).trans
        (he₂ (p, μf p) (α ∘ fun o : Option (Option ι₂) => o.elim v f₂))
    refine ⟨C56J θ * NJ + C57J θ * NR, C56R * NJ + C57R θ * NR, _, _, mJ₁.add mJ₂,
      Or.inl ⟨v, mR₁.add mR₂⟩, ?_, fun p α => ?_⟩
    · calc C56J θ * NJ + C57J θ * NR + (C56R * NJ + C57R θ * NR)
          ≤ Csw θ * NJ + Csw θ * NR := by unfold Csw; nlinarith
        _ = Csw θ * (NJ + NR) := by ring
        _ ≤ Csw θ * N := mul_le_mul_of_nonneg_left hN (Csw_nonneg h0 h1)
    · intro t s hs0 hst ht1
      rw [hlin p α t s hs0 hst ht1]
      beta_reduce
      rw [eJ p α t s hs0 hst ht1, eR p α t s hs0 hst ht1]
      ring
  · refine ⟨C56J θ * NJ, C56R * NJ, _, _, mJ₁, Or.inl ⟨v, mR₁⟩, ?_, fun p α => ?_⟩
    · calc C56J θ * NJ + C56R * NJ ≤ Csw θ * NJ := by unfold Csw; nlinarith
        _ ≤ Csw θ * N := mul_le_mul_of_nonneg_left (by linarith) (Csw_nonneg h0 h1)
    · intro t s hs0 hst ht1
      rw [hlin p α t s hs0 hst ht1]
      beta_reduce
      have hz' : sandw ε v μf TR p α t s = 0 := keqOn_sandwich_zero (hz p α) t s hs0 hst ht1
      rw [eJ p α t s hs0 hst ht1, hz']
      ring

end Sandwich

end WaveTurbulence.ClassJR
