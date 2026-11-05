/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.TreeGate
public import WaveTurbulence.Foundations.Spine.WeightedSmoothMultiplier

/-!
# Separated representations (Prop 6.1, third conjunct)

`SepRep θ δ A W n T f cJ cM`: on `T`, `f = Σ_{i < m} δ^n J_i(t) M_i(k)` with `m ≤ 2^n` terms, continuous time
factors with `‖J_i‖_{𝔛^{θ,0,0}(T)} ≤ cJ`, and real momentum factors with `‖M_i‖_{𝔖^{A,W}} ≤ cM`.

* `restr_one_le`, `restr_const_le`: a constant on a unit box has restriction norm `≤ |c| K_tr(θ)`;
* `SNorm_mul_le`: the weighted Leibniz bound `‖fg‖_{𝔖^{A,W}} ≤ 2^A d^A ‖f‖_{𝔖^{A,0}} ‖g‖_{𝔖^{A,W}}`;
* `SepRep.mul`: products multiply the term counts, the powers of `δ` and the bounds;
* `sepRep_tree`, `sepRep_couple`: the single-layer leading terms, at any continuous time arguments;
* `leafwiseSeparated_of_sepRep`: the spine form `LeafwiseSeparated`.
-/

@[expose] public section

open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

/-! ### Constants on a unit box -/

theorem restr_one_le {V : Type*} {θ : ℝ} (hθ : 0 ≤ θ) (T : Set (Fin 2 → ℝ)) (K : Set V)
    (b : Fin 2 → ℝ) (hT : ∀ t ∈ T, t + b ∈ (Layered.unitBox : Set (Fin 2 → ℝ))) :
    R00 θ T K (fun _ _ => (1 : ℂ)) ≤ ENNReal.ofReal (Ktr θ) := by
  have h1 := Layered.mixedRestrictionNorm00_translate_le θ (B := T) (B' := Layered.unitBox) K
    (fun _ _ => (1 : ℂ)) b hT
  refine h1.trans ?_
  refine (mixedRestrictionNorm00_le_extension (B := (Layered.unitBox : Set (Fin 2 → ℝ))) (K := K)
    (fun t (_ : V) => coordinateCutoff (r := 2) Layered.chiUnit t)
    fun t _ => Layered.coordinateCutoff_chiUnit_eq_one t.2).trans ?_
  have hfin := timeFourierNorm_lt_top_of_smooth_compact θ
    (coordinateCutoff_hasCompactSupport (r := 2) Layered.chiUnit_hasCompactSupport)
    (coordinateCutoff_contDiff (r := 2) Layered.chiUnit_contDiff)
  have hint := integrable_of_timeFourierNorm_lt_top hfin
  rw [mixedFourierNorm00_eq_lintegral (fun _ => hint), ← traceConst_eq_ofReal]
  have h2 : ∫⁻ ξ, timeWeight θ ξ * mixedFourierEnvelope00
      (fun t (_ : V) => coordinateCutoff (r := 2) Layered.chiUnit t) ξ ≤
      timeFourierNorm θ (coordinateCutoff (r := 2) Layered.chiUnit) := by
    rw [timeFourierNorm_eq_lintegral hint]
    exact lintegral_mono fun ξ => mul_le_mul_right (iSup_le fun _ => le_rfl) _
  refine h2.trans ?_
  unfold Regref.traceConst
  have h3 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 ^ θ) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_rpow (by norm_num) hθ)
  calc timeFourierNorm θ (coordinateCutoff (r := 2) Layered.chiUnit)
      = 1 * timeFourierNorm θ (coordinateCutoff (r := 2) Layered.chiUnit) := (one_mul _).symm
    _ ≤ _ := mul_le_mul_left h3 _

theorem restr_const_le {V : Type*} {θ : ℝ} (hθ : 0 ≤ θ) (T : Set (Fin 2 → ℝ)) (K : Set V)
    (b : Fin 2 → ℝ) (hT : ∀ t ∈ T, t + b ∈ (Layered.unitBox : Set (Fin 2 → ℝ))) (c : ℂ) :
    R00 θ T K (fun _ _ => c) ≤ ENNReal.ofReal (‖c‖ * Ktr θ) := by
  have h := Layered.mixedRestrictionNorm00_mul_momentum_le θ T K (fun _ => c) (norm_nonneg c)
    (fun _ _ => le_rfl) (fun _ _ => (1 : ℂ))
  have e : R00 θ T K (fun _ _ => c) = R00 θ T K (fun _ v => (fun _ => c) v * (fun _ _ => (1 : ℂ)) () v) := by
    simp only [mul_one]
  rw [e, ENNReal.ofReal_mul (norm_nonneg c)]
  exact h.trans (mul_le_mul_right (restr_one_le hθ T K b hT) _)

/-! ### The weighted Leibniz bound -/

theorem contDiff_of_SNorm_le {d A B : ℕ} (hA : A ≠ 0) (f : Mom d → ℂ) (C : ℝ)
    (h : SNorm A B f ≤ ENNReal.ofReal C) : ContDiff ℝ A f := by
  have ht : SNorm A B f < ⊤ := h.trans_lt ENNReal.ofReal_lt_top
  unfold SNorm at ht
  split_ifs at ht with hf
  · exact hf.resolve_left hA
  · exact absurd ht (by simp)

theorem SNorm_mul_le {d A B : ℕ} (hd : 1 ≤ d) (f g : Mom d → ℂ) (hf : ContDiff ℝ A f)
    (hg : ContDiff ℝ A g) {Cf Cg : ℝ} (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg) (hF : SNorm A 0 f ≤ ENNReal.ofReal Cf)
    (hG : SNorm A B g ≤ ENNReal.ofReal Cg) :
    SNorm A B (fun x => f x * g x) ≤ ENNReal.ofReal ((2 : ℝ) ^ A * (d : ℝ) ^ A * Cf * Cg) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  apply WaveTurbulence.Induct.SNorm_le_of_momentum_bounds _ (hf.mul hg)
  intro n hn ρ x
  apply (mul_le_mul_of_nonneg_left (norm_momentumDerivative_le_frechet _ ρ x)
    (pow_nonneg (WaveTurbulence.Induct.jbr_pos x).le B)).trans
  apply (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_mul_le hf hg x (by exact_mod_cast hn))
    (pow_nonneg (WaveTurbulence.Induct.jbr_pos x).le B)).trans
  rw [mul_sum]
  have hterm (i : ℕ) (hi : i ∈ range (n + 1)) :
      jbr x ^ B * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖) ≤
      (n.choose i : ℝ) * ((d : ℝ) ^ A * Cf * Cg) := by
    have hiA : i ≤ A := (Nat.lt_succ_iff.mp (mem_range.mp hi)).trans hn
    have hni : n - i ≤ A := (Nat.sub_le _ _).trans hn
    have hin : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hf0 := SNorm_frechet_pointwise f hf Cf hCf hF hiA x
    rw [pow_zero, one_mul] at hf0
    have hg0 := SNorm_frechet_pointwise g hg Cg hCg hG hni x
    have hdn : (d : ℝ) ^ i * (d : ℝ) ^ (n - i) ≤ (d : ℝ) ^ A := by
      rw [← pow_add]
      exact pow_le_pow_right₀ hd1 (by omega)
    have hch : (0 : ℝ) ≤ n.choose i := Nat.cast_nonneg _
    calc jbr x ^ B * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖)
        = (n.choose i : ℝ) * (‖iteratedFDeriv ℝ i f x‖ * (jbr x ^ B * ‖iteratedFDeriv ℝ (n - i) g x‖)) := by
          ring
      _ ≤ (n.choose i : ℝ) * (((d : ℝ) ^ i * Cf) * ((d : ℝ) ^ (n - i) * Cg)) := by
          apply mul_le_mul_of_nonneg_left _ hch
          exact mul_le_mul hf0 hg0 (mul_nonneg (pow_nonneg (WaveTurbulence.Induct.jbr_pos x).le B) (norm_nonneg _))
            (mul_nonneg (pow_nonneg (by linarith) i) hCf)
      _ = (n.choose i : ℝ) * (((d : ℝ) ^ i * (d : ℝ) ^ (n - i)) * Cf * Cg) := by ring
      _ ≤ (n.choose i : ℝ) * ((d : ℝ) ^ A * Cf * Cg) := by
          apply mul_le_mul_of_nonneg_left _ hch
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdn hCf) hCg
  apply (sum_le_sum hterm).trans
  rw [← sum_mul]
  have hsum : (∑ i ∈ range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
    simpa only [one_pow, one_mul, one_add_one_eq_two] using (add_pow (1 : ℝ) 1 n).symm
  rw [hsum]
  have hc : 0 ≤ (d : ℝ) ^ A * Cf * Cg := by positivity
  have hh := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn) hc
  calc (2 : ℝ) ^ n * ((d : ℝ) ^ A * Cf * Cg) ≤ 2 ^ A * ((d : ℝ) ^ A * Cf * Cg) := hh
    _ = _ := by ring

theorem SNormR_mul_le {d A B : ℕ} (hd : 1 ≤ d) (hA : A ≠ 0) (f g : Mom d → ℝ) {Cf Cg : ℝ} (hCf : 0 ≤ Cf)
    (hCg : 0 ≤ Cg) (hF : SNormR A 0 f ≤ ENNReal.ofReal Cf) (hG : SNormR A B g ≤ ENNReal.ofReal Cg) :
    SNormR A B (fun x => f x * g x) ≤ ENNReal.ofReal ((2 : ℝ) ^ A * (d : ℝ) ^ A * Cf * Cg) := by
  unfold SNormR at hF hG ⊢
  have e : (fun k => (((f k * g k : ℝ)) : ℂ)) = fun k => (f k : ℂ) * (g k : ℂ) := by
    funext k
    push_cast
    rfl
  rw [e]
  exact SNorm_mul_le hd _ _ (contDiff_of_SNorm_le hA _ Cf hF) (contDiff_of_SNorm_le hA _ Cg hG)
    hCf hCg hF hG

/-! ### Separated representations -/

/-- **A separated representation** of `f` on `T`. -/
def SepRep {d : ℕ} (θ δ : ℝ) (A W n : ℕ) (T : Set (Fin 2 → ℝ)) (f : (Fin 2 → ℝ) → Mom d → ℂ)
    (cJ cM : ℝ) : Prop :=
  ∃ (m : ℕ) (J : Fin m → (Fin 2 → ℝ) → ℂ) (M : Fin m → Mom d → ℝ),
    m ≤ 2 ^ n ∧
    (∀ ts ∈ T, ∀ k, f ts k = ∑ i, (δ : ℂ) ^ n * J i ts * (M i k : ℂ)) ∧
    (∀ i, Continuous (J i)) ∧
    (∀ i, R00 (V := Unit) θ T Set.univ (fun ts _ => J i ts) ≤ ENNReal.ofReal cJ) ∧
    (∀ i, SNormR A W (M i) ≤ ENNReal.ofReal cM)

section SepRep

variable {d : ℕ} {θ δ : ℝ} {A W n : ℕ} {T : Set (Fin 2 → ℝ)}

theorem SepRep.zero (cJ cM : ℝ) : SepRep (d := d) θ δ A W n T (fun _ _ => 0) cJ cM :=
  ⟨0, fun i => i.elim0, fun i => i.elim0, Nat.zero_le _, fun _ _ _ => by simp, fun i => i.elim0,
    fun i => i.elim0, fun i => i.elim0⟩

theorem SepRep.congr {f g : (Fin 2 → ℝ) → Mom d → ℂ} {cJ cM : ℝ} (h : SepRep θ δ A W n T g cJ cM)
    (hfg : ∀ ts ∈ T, ∀ k, f ts k = g ts k) : SepRep θ δ A W n T f cJ cM := by
  obtain ⟨m, J, M, hm, hf, hc, hJ, hM⟩ := h
  exact ⟨m, J, M, hm, fun ts hts k => (hfg ts hts k).trans (hf ts hts k), hc, hJ, hM⟩

theorem SepRep.mono {f : (Fin 2 → ℝ) → Mom d → ℂ} {cJ cM cJ' cM' : ℝ} (h : SepRep θ δ A W n T f cJ cM)
    (hJ' : cJ ≤ cJ') (hM' : cM ≤ cM') : SepRep θ δ A W n T f cJ' cM' := by
  obtain ⟨m, J, M, hm, hf, hc, hJ, hM⟩ := h
  exact ⟨m, J, M, hm, hf, hc, fun i => (hJ i).trans (ENNReal.ofReal_le_ofReal hJ'),
    fun i => (hM i).trans (ENNReal.ofReal_le_ofReal hM')⟩

/-- **Products of separated representations.** -/
theorem SepRep.mul (hθ : 0 ≤ θ) (hT : ∀ t ∈ T, t ∈ closure (interior T)) (hd : 1 ≤ d) (hA : A ≠ 0)
    {n₁ n₂ : ℕ} {f₁ f₂ : (Fin 2 → ℝ) → Mom d → ℂ} {cJ₁ cM₁ cJ₂ cM₂ : ℝ} (hcJ₁ : 0 ≤ cJ₁)
    (hcM₁ : 0 ≤ cM₁) (hcM₂ : 0 ≤ cM₂)
    (h₁ : SepRep θ δ A 0 n₁ T f₁ cJ₁ cM₁) (h₂ : SepRep θ δ A W n₂ T f₂ cJ₂ cM₂) :
    SepRep θ δ A W (n₁ + n₂) T (fun ts k => f₁ ts k * f₂ ts k) (2 ^ θ * cJ₁ * cJ₂)
      ((2 : ℝ) ^ A * (d : ℝ) ^ A * cM₁ * cM₂) := by
  obtain ⟨m₁, J₁, M₁, hm₁, hf₁, hc₁, hJ₁, hM₁⟩ := h₁
  obtain ⟨m₂, J₂, M₂, hm₂, hf₂, hc₂, hJ₂, hM₂⟩ := h₂
  set e : Fin m₁ × Fin m₂ ≃ Fin (m₁ * m₂) := finProdFinEquiv with he
  refine ⟨m₁ * m₂, fun i ts => J₁ (e.symm i).1 ts * J₂ (e.symm i).2 ts,
    fun i k => M₁ (e.symm i).1 k * M₂ (e.symm i).2 k, ?_, ?_, ?_, ?_, ?_⟩
  · calc m₁ * m₂ ≤ 2 ^ n₁ * 2 ^ n₂ := Nat.mul_le_mul hm₁ hm₂
      _ = 2 ^ (n₁ + n₂) := (pow_add _ _ _).symm
  · intro ts hts k
    beta_reduce
    rw [hf₁ ts hts k, hf₂ ts hts k, Finset.sum_mul_sum]
    symm
    rw [← e.sum_comp]
    simp only [Equiv.symm_apply_apply]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    push_cast
    ring
  · exact fun i => (hc₁ _).mul (hc₂ _)
  · intro i
    have hfin₁ : R00 (V := Unit) θ T Set.univ (fun ts _ => J₁ (e.symm i).1 ts) < ⊤ :=
      (hJ₁ _).trans_lt ENNReal.ofReal_lt_top
    have hfin₂ : R00 (V := Unit) θ T Set.univ (fun ts _ => J₂ (e.symm i).2 ts) < ⊤ :=
      (hJ₂ _).trans_lt ENNReal.ofReal_lt_top
    have h := Layered.mixedRestrictionNorm00_mul_le hθ hT (Set.univ : Set Unit)
      (fun ts _ => J₁ (e.symm i).1 ts) (fun ts _ => J₂ (e.symm i).2 ts) (fun _ _ => hc₂ _) hfin₁ hfin₂
    refine h.trans ?_
    have h2 : (0 : ℝ) ≤ 2 ^ θ := Real.rpow_nonneg (by norm_num) θ
    rw [ENNReal.ofReal_mul (mul_nonneg h2 hcJ₁), ENNReal.ofReal_mul h2]
    exact mul_le_mul' (mul_le_mul_right (hJ₁ _) _) (hJ₂ _)
  · intro i
    exact SNormR_mul_le hd hA _ _ hcM₁ hcM₂ (hM₁ _) (hM₂ _)

end SepRep

/-! ### Single-layer leading terms -/

theorem norm_treeCoef_le (X : RegChain) (ζ : ℤˣ) (Z : Finset (Fin 1 × Path)) :
    ‖(2 : ℂ)⁻¹ ^ X.size * zetaOfTrees ![ζ] ![X.plug ζ .leaf] * specialWeight ![ζ] Z‖ ≤ 1 := by
  rw [norm_mul, norm_mul, norm_zetaOfTrees, mul_one, norm_pow, norm_inv]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  have h1 : (2⁻¹ : ℝ) ^ X.size ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  calc (2⁻¹ : ℝ) ^ X.size * ‖specialWeight ![ζ] Z‖ ≤ 1 * 1 :=
        mul_le_mul h1 (norm_specialWeight_le _ Z) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem norm_cplCoef_le (Q : RegCpl) (Z : Finset (Fin 2 × Path)) :
    ‖(2 : ℂ)⁻¹ ^ Q.size * zetaOfTrees ![1, -1] ![Q.trees.1, Q.trees.2] * specialWeight ![1, -1] Z‖ ≤ 1 := by
  rw [norm_mul, norm_mul, norm_zetaOfTrees, mul_one, norm_pow, norm_inv]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  have h1 : (2⁻¹ : ℝ) ^ Q.size ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  calc (2⁻¹ : ℝ) ^ Q.size * ‖specialWeight ![1, -1] Z‖ ≤ 1 * 1 :=
        mul_le_mul h1 (norm_specialWeight_le _ Z) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- **A single tree factor** at continuous time arguments. -/
theorem sepRep_tree {d : ℕ} {θ δ : ℝ} {A n : ℕ} {T : Set (Fin 2 → ℝ)} (r : ℝ) (H : LeafProfiles 1 d)
    (X : RegChain) (ζ : ℤˣ) (hsize : X.size = 2 * n) (τ σ : (Fin 2 → ℝ) → ℝ) (hτ : Continuous τ)
    (hσ : Continuous σ) {cJ cM : ℝ}
    (hJ : X.dominant = true → R00 (V := Unit) θ T Set.univ (fun ts _ => (X.JBtree r (τ ts) (σ ts) : ℂ)) ≤
      ENNReal.ofReal cJ)
    (hM : X.dominant = true → ∀ Z ∈ specialSets (X.treeLinks ζ),
      SNormR A 0 (LeafApp.chainNstar H Z X ζ (0, [])) ≤ ENNReal.ofReal cM) :
    SepRep θ δ A 0 n T (fun ts k => LeafApp.tree δ r H X ζ (τ ts) (σ ts) k) cJ cM := by
  by_cases hdom : X.dominant = true
  · set S := specialSets (X.treeLinks ζ) with hS
    set e := S.equivFin with he
    set c₀ : ℂ := (2 : ℂ)⁻¹ ^ X.size * zetaOfTrees ![ζ] ![X.plug ζ .leaf] with hc₀
    have hn2 : X.size / 2 = n := by omega
    refine ⟨S.card, fun i ts => c₀ * specialWeight ![ζ] (e.symm i).1 * (X.JBtree r (τ ts) (σ ts) : ℂ),
      fun i k => LeafApp.chainNstar H (e.symm i).1 X ζ (0, []) k, card_specialSets_tree_le hsize ζ, ?_, ?_, ?_,
      ?_⟩
    · intro ts _ k
      unfold LeafApp.tree
      beta_reduce
      rw [ite_eq_left hdom, hn2, Finset.mul_sum, ← Finset.sum_coe_sort S, ← e.symm.sum_comp]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hc₀]
      ring
    · exact fun i => continuous_const.mul (Complex.continuous_ofReal.comp
        ((continuous_RegChain_JBtree r X).comp (hτ.prodMk hσ)))
    · intro i
      have h := Layered.mixedRestrictionNorm00_mul_momentum_le (V := Unit) θ T Set.univ
        (fun _ => c₀ * specialWeight ![ζ] (e.symm i).1) zero_le_one
        (fun _ _ => by rw [hc₀]; exact norm_treeCoef_le X ζ _)
        (fun ts _ => (X.JBtree r (τ ts) (σ ts) : ℂ))
      refine h.trans ?_
      rw [ENNReal.ofReal_one, one_mul]
      exact hJ hdom
    · exact fun i => hM hdom _ (e.symm i).2
  · refine (SepRep.zero cJ cM).congr fun ts _ k => ?_
    unfold LeafApp.tree
    rw [ite_eq_right (by simpa using hdom)]

/-- **A single couple factor** at continuous time arguments. -/
theorem sepRep_couple {d : ℕ} {θ δ : ℝ} {A n : ℕ} {T : Set (Fin 2 → ℝ)} (r : ℝ) (H : LeafProfiles 2 d)
    (Q : RegCpl) (hsize : Q.size = 2 * n) (τ σ : (Fin 2 → ℝ) → ℝ) (hτ : Continuous τ)
    (hσ : Continuous σ) {cJ cM : ℝ}
    (hJ : Q.dominant = true → R00 (V := Unit) θ T Set.univ (fun ts _ => (Q.JB r (τ ts) (σ ts) : ℂ)) ≤
      ENNReal.ofReal cJ)
    (hM : Q.dominant = true → ∀ Z ∈ specialSets Q.links,
      SNormR A A (LeafApp.cplMstar H Z Q (0, []) (1, [])) ≤ ENNReal.ofReal cM) :
    SepRep θ δ A A n T (fun ts k => LeafApp.couple δ r H Q (τ ts) (σ ts) k) cJ cM := by
  by_cases hdom : Q.dominant = true
  · set S := specialSets Q.links with hS
    set e := S.equivFin with he
    set c₀ : ℂ := (2 : ℂ)⁻¹ ^ Q.size * zetaOfTrees ![1, -1] ![Q.trees.1, Q.trees.2] with hc₀
    have hn2 : Q.size / 2 = n := by omega
    refine ⟨S.card, fun i ts => c₀ * specialWeight ![1, -1] (e.symm i).1 * (Q.JB r (τ ts) (σ ts) : ℂ),
      fun i k => LeafApp.cplMstar H (e.symm i).1 Q (0, []) (1, []) k, card_specialSets_couple_le hsize, ?_, ?_,
      ?_, ?_⟩
    · intro ts _ k
      unfold LeafApp.couple
      beta_reduce
      rw [ite_eq_left hdom, hn2, Finset.mul_sum, ← Finset.sum_coe_sort S, ← e.symm.sum_comp]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hc₀]
      ring
    · exact fun i => continuous_const.mul (Complex.continuous_ofReal.comp
        ((continuous_RegCpl_JB r Q).comp (hτ.prodMk hσ)))
    · intro i
      have h := Layered.mixedRestrictionNorm00_mul_momentum_le (V := Unit) θ T Set.univ
        (fun _ => c₀ * specialWeight ![1, -1] (e.symm i).1) zero_le_one
        (fun _ _ => by rw [hc₀]; exact norm_cplCoef_le Q _)
        (fun ts _ => (Q.JB r (τ ts) (σ ts) : ℂ))
      refine h.trans ?_
      rw [ENNReal.ofReal_one, one_mul]
      exact hJ hdom
    · exact fun i => hM hdom _ (e.symm i).2
  · refine (SepRep.zero cJ cM).congr fun ts _ k => ?_
    unfold LeafApp.couple
    rw [ite_eq_right (by simpa using hdom)]

/-- **The spine form.** -/
theorem leafwiseSeparated_of_sepRep (P : WTParams) {n W : ℕ} {T : Set (Fin 2 → ℝ)}
    {f : (Fin 2 → ℝ) → Mom P.d → ℂ} {cost cJ cM : ℝ}
    (h : SepRep (1 - P.η) P.δ (30 * P.d) W n T f cJ cM) (hJ : cJ ≤ P.C₁ * P.C₁ ^ n)
    (hM : cM ≤ P.C₁ * P.C₁ ^ n * cost) : LeafwiseSeparated P n W T f cost := by
  obtain ⟨m, J, M, hm, hf, -, hJ', hM'⟩ := h
  refine ⟨m, J, M, hm, hf, fun i => ?_, fun i => (hM' i).trans (ENNReal.ofReal_le_ofReal hM)⟩
  rw [NormBridgeScratch.XNorm00Restr_eq_mixedRestrictionNorm00 (1 - P.η) T Set.univ (fun ts _ => J i ts)]
  exact (hJ' i).trans (ENNReal.ofReal_le_ofReal hJ)

end WaveTurbulence.PL234
