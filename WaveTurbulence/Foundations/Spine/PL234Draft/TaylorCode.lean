/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.TaylorPointwise
public import WaveTurbulence.Foundations.Spine.InputLeafCount

/-!
# TARGET Prop 6.2: the input perturbation of one couple code

TARGET's proof of Prop 6.2 (L1247): replacing the input `φ_p` by `F_p = φ_p + 𝓡_p` in the leading term
of one couple code changes it by the terms containing at least one `𝓡_p` input. For a code `𝒬` of size
`2n` decoding a single-layer couple carrier,
`𝒜_𝒬[F] − 𝒜_𝒬[φ] = (𝒜 − K)[F] − (𝒜 − K)[φ] + ∑_{S ≠ ∅} ((K − 𝒜)[H_S] + 𝒜[H_S])`,
where `H_S` is the leaf profile `𝓡` on the leaves of `S` and `φ` elsewhere (`kernelLeaves_add`). Each
term is estimated by the single-layer bounds of B2.1, in their leafwise form for `H_S`, with the leaf
bound `ρ = ‖𝓡‖` on `S` and `β ≥ ‖φ‖` elsewhere (`norm_app_add_sub_app_le`).
-/

@[expose] public section

open MeasureTheory Set Finset
open scoped ENNReal

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine

variable {w d : ℕ}

/-- The leaf bounds `ρ` on the leaves of `S`, `β` elsewhere. -/
noncomputable def mixBound (LG : LayeredGarden w) (S : Finset (GLeaf LG.garden.tree))
    (ρ β : NNReal) : (Fin w × Path) → NNReal := by
  classical
  exact fun a => if a ∈ S.map (leafEmb LG.garden.tree) then ρ else β

theorem mixBound_mem (LG : LayeredGarden w) {S : Finset (GLeaf LG.garden.tree)} (ρ β : NNReal)
    {ℓ : GLeaf LG.garden.tree} (h : ℓ ∈ S) : mixBound LG S ρ β ℓ.1 = ρ := by
  classical
  unfold mixBound
  exact ite_eq_left (Finset.mem_map_of_mem (leafEmb LG.garden.tree) h)

theorem mixBound_not_mem (LG : LayeredGarden w) {S : Finset (GLeaf LG.garden.tree)} (ρ β : NNReal)
    {ℓ : GLeaf LG.garden.tree} (h : ℓ ∉ S) : mixBound LG S ρ β ℓ.1 = β := by
  classical
  unfold mixBound
  refine ite_eq_right fun hm => h ?_
  obtain ⟨ℓ', hℓ', he⟩ := Finset.mem_map.mp hm
  have : ℓ' = ℓ := Subtype.ext he
  rwa [← this]

/-- At least one leaf carries `ρ ≤ β`, the others at most `β`. -/
theorem leafSizeProduct_mixBound_le (LG : LayeredGarden w) {S : Finset (GLeaf LG.garden.tree)}
    (hS : S ⊆ inputLeaves LG.garden) (hne : S.Nonempty) {ρ β : NNReal} (hρβ : ρ ≤ β)
    (hβ : 1 ≤ β) :
    leafSizeProduct LG (mixBound LG S ρ β) ≤ ρ * β ^ (inputLeaves LG.garden).card := by
  classical
  obtain ⟨ℓ₀, hℓ₀⟩ := hne
  unfold leafSizeProduct
  rw [← Finset.mul_prod_erase _ _ (hS hℓ₀), mixBound_mem LG ρ β hℓ₀]
  have hle : ∏ ℓ ∈ (inputLeaves LG.garden).erase ℓ₀, ((mixBound LG S ρ β ℓ.1 : NNReal) : ℝ) ≤
      ∏ _ℓ ∈ (inputLeaves LG.garden).erase ℓ₀, (β : ℝ) := by
    apply Finset.prod_le_prod₀ (fun _ _ => NNReal.coe_nonneg _)
    intro ℓ _
    by_cases h : ℓ ∈ S
    · rw [mixBound_mem LG ρ β h]
      exact_mod_cast hρβ
    · rw [mixBound_not_mem LG ρ β h]
  rw [Finset.prod_const] at hle
  have hβ' : (1 : ℝ) ≤ β := by exact_mod_cast hβ
  have hpow : (β : ℝ) ^ ((inputLeaves LG.garden).erase ℓ₀).card ≤
      (β : ℝ) ^ (inputLeaves LG.garden).card :=
    pow_le_pow_right₀ hβ' (Finset.card_erase_le)
  exact mul_le_mul_of_nonneg_left (hle.trans hpow) ρ.2

/-- The mixed profile is leafwise controlled by the mixed bounds. -/
theorem leafwiseControlled_mix (LG : LayeredGarden w) (S : Finset (GLeaf LG.garden.tree))
    (F₀ R : Mom d → ℝ) (ρ β : NNReal)
    (hF₀ : SNormR (40 * d) (40 * d) F₀ ≤ ENNReal.ofReal β)
    (hR : SNormR (40 * d) (40 * d) R ≤ ENNReal.ofReal ρ) :
    LeafwiseControlled LG (mixProfile LG S (fun _ => F₀) (fun _ => R)) (mixBound LG S ρ β) := by
  intro ℓ _
  by_cases h : ℓ ∈ S
  · rw [mixProfile_mem LG _ _ h, mixBound_mem LG ρ β h]
    exact hR
  · rw [mixProfile_not_mem LG _ _ h, mixBound_not_mem LG ρ β h]
    exact hF₀

theorem mixProfile_empty (LG : LayeredGarden w) (H₀ H₁ : LeafProfiles w d) :
    mixProfile LG ∅ H₀ H₁ = H₀ := by
  classical
  funext a
  unfold mixProfile
  simp

/-- **Pointwise error of a leafwise single-layer estimate** at a point of the closed box. -/
theorem norm_coupleLeaves_sub_le (P : WTParams) (hη : 0 ≤ P.η) (LG : LayeredGarden 2)
    (hplain : LG.garden.IsPlain) (H : LeafProfiles 2 P.d) (k : Mom P.d)
    (hsum : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun m : Fin P.d → ℤ => |H ℓ.1 (k + latticePoint P.L m)|)
    (r : ℕ) (Q : RegCpl) {e : ℝ} (he : 0 ≤ e)
    (hX : XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox r r) Set.univ
      (fun ts k => coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
        LeafApp.couple P.δ r H Q (ts 0) (ts 1) k) ≤ ENNReal.ofReal e)
    {t s : ℝ} (ht : t ∈ Icc (r : ℝ) (r + 1)) (hs : s ∈ Icc (r : ℝ) (r + 1)) :
    ‖coupleLeaves P.L P.γ P.δ LG H t s k - LeafApp.couple P.δ r H Q t s k‖ ≤
      e * jbr k ^ (-(30 * P.d : ℝ)) := by
  have hK := continuous_coupleLeaves_time P.L P.γ P.δ H LG hplain k hsum
  have hu : Continuous (fun ts : Fin 2 → ℝ => (ts 0, ts 1)) :=
    (continuous_apply 0).prodMk (continuous_apply 1)
  have hA0 := (continuous_LeafApp_couple P.δ r H Q k).comp hu
  have hA : Continuous (fun ts : Fin 2 → ℝ => LeafApp.couple P.δ r H Q (ts 0) (ts 1) k) := by
    simpa only [Function.comp_def] using hA0
  have htime : ![t, s] ∈ closure (interior (timeBox (r : ℝ) r)) := by
    rw [closure_interior_timeBox]
    exact ⟨ht, hs⟩
  have h := norm_le_of_XNormRestr hη (30 * P.d) (30 * P.d) (timeBox (r : ℝ) r)
    (fun ts k => coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
      LeafApp.couple P.δ r H Q (ts 0) (ts 1) k) ![t, s] k htime (hK.sub hA) he hX
  have hcast : (((30 * P.d : ℕ) : ℝ)) = 30 * (P.d : ℝ) := by push_cast; ring
  rw [hcast] at h
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using h

/-- **The leafwise kernel of the perturbed constant profile** is the sum over the subsets of the input
leaves of the kernels of the mixed profiles. -/
theorem coupleLeaves_add (L γ δ : ℝ) (LG : LayeredGarden 2) (hplain : LG.garden.IsPlain)
    (F₀ R : Mom d → ℝ) (t s : ℝ) (k : Mom d)
    (hsum : ∀ S ∈ (inputLeaves LG.garden).powerset, ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun m : Fin d → ℤ =>
        |mixProfile LG S (fun _ => F₀) (fun _ => R) ℓ.1 (k + latticePoint L m)|) :
    coupleLeaves L γ δ LG (fun _ x => F₀ x + R x) t s k =
      ∑ S ∈ (inputLeaves LG.garden).powerset,
        coupleLeaves L γ δ LG (mixProfile LG S (fun _ => F₀) (fun _ => R)) t s k := by
  unfold coupleLeaves
  exact kernelLeaves_add L γ δ LG (fun _ => F₀) (fun _ => R) _ 0 k (fun _ => 0) 0
    fun S hS => (summable_norm_leavesSummand L γ δ LG _ _ 0 k _ _
      (fun j => card_lone_le_of_plain hplain j) (hsum S hS)).of_norm

/-- **The input perturbation of one couple code.** -/
theorem norm_app_add_sub_app_le (P : WTParams) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη : 0 ≤ P.η)
    (hδ : 0 ≤ P.δ) {r n : ℕ} (Q : RegCpl) (hsize : Q.size = 2 * n) (LG : LayeredGarden 2)
    (hQ : Q.Decodes LG.garden) (F₀ R : Mom P.d → ℝ) {ρ β : NNReal} (hρβ : ρ ≤ β) (hβ : 1 ≤ β)
    (hF₀ : SNormR (40 * P.d) (40 * P.d) F₀ ≤ ENNReal.ofReal β)
    (hR : SNormR (40 * P.d) (40 * P.d) R ≤ ENNReal.ofReal ρ)
    {eA eB cJ cM : ℝ} (heA : 0 ≤ eA) (heB : 0 ≤ eB) (hcJ : 0 ≤ cJ) (hcM : 0 ≤ cM)
    (hA₀ : XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox r r) Set.univ
      (fun ts k => coupleLeaves P.L P.γ P.δ LG (fun _ => F₀) (ts 0) (ts 1) k -
        LeafApp.couple P.δ r (fun _ => F₀) Q (ts 0) (ts 1) k) ≤ ENNReal.ofReal eA)
    (hA₁ : XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox r r) Set.univ
      (fun ts k => coupleLeaves P.L P.γ P.δ LG (fun _ x => F₀ x + R x) (ts 0) (ts 1) k -
        LeafApp.couple P.δ r (fun _ x => F₀ x + R x) Q (ts 0) (ts 1) k) ≤ ENNReal.ofReal eA)
    (hB : ∀ (H : LeafProfiles 2 P.d) (B : (Fin 2 × Path) → NNReal), LeafwiseControlled LG H B →
      XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox r r) Set.univ
        (fun ts k => coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
          LeafApp.couple P.δ r H Q (ts 0) (ts 1) k) ≤
        ENNReal.ofReal eB * ENNReal.ofReal (leafSizeProduct LG B) ∧
      (Q.dominant = true → ∀ Z ∈ specialSets Q.links,
        SNormR (30 * P.d) (30 * P.d) (LeafApp.cplMstar H Z Q (0, []) (1, [])) ≤
          ENNReal.ofReal (cM * leafSizeProduct LG B)))
    {t s : ℝ} (ht : t ∈ Icc (r : ℝ) (r + 1)) (hs : s ∈ Icc (r : ℝ) (r + 1))
    (hJ : Q.dominant = true → |Q.JB r t s| ≤ cJ) (k : Mom P.d) :
    ‖LeafApp.couple P.δ r (fun _ x => F₀ x + R x) Q t s k -
        LeafApp.couple P.δ r (fun _ => F₀) Q t s k‖ ≤
      (2 * eA + 2 ^ (2 * n + 1) * (eB + P.δ ^ n * 2 ^ n * cJ * cM) * (ρ * β ^ (2 * n + 1))) *
        jbr k ^ (-(30 * P.d : ℝ)) := by
  classical
  have hplain : LG.garden.IsPlain := hQ.1.1
  have hcard : (inputLeaves LG.garden).card = 2 * n + 1 :=
    card_inputLeaves_couple LG.garden hplain ((RegCpl.size_eq_order Q hQ).trans hsize)
  have hj : 0 ≤ jbr k ^ (-(30 * P.d : ℝ)) := Real.rpow_nonneg (WaveTurbulence.Induct.jbr_pos k).le _
  have hd1 : P.d + 1 ≤ 40 * P.d := by omega
  have hsF₀ : Summable fun m : Fin P.d → ℤ => |F₀ (k + latticePoint P.L m)| :=
    summable_abs_coset_of_SNormR hL hd1 (NNReal.coe_nonneg β) F₀ hF₀ k
  have hsR : Summable fun m : Fin P.d → ℤ => |R (k + latticePoint P.L m)| :=
    summable_abs_coset_of_SNormR hL hd1 (NNReal.coe_nonneg ρ) R hR k
  have hctrl : ∀ S : Finset (GLeaf LG.garden.tree),
      LeafwiseControlled LG (mixProfile LG S (fun _ => F₀) (fun _ => R)) (mixBound LG S ρ β) :=
    fun S => leafwiseControlled_mix LG S F₀ R ρ β hF₀ hR
  have hsumS : ∀ S ∈ (inputLeaves LG.garden).powerset, ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun m : Fin P.d → ℤ =>
        |mixProfile LG S (fun _ => F₀) (fun _ => R) ℓ.1 (k + latticePoint P.L m)| :=
    fun S _ => (hctrl S).summable_coset hd hL k
  -- the constant-profile errors
  have hE₀ := norm_coupleLeaves_sub_le P hη LG hplain (fun _ => F₀) k (fun _ _ => hsF₀) r Q heA
    hA₀ ht hs
  have hsF : Summable fun m : Fin P.d → ℤ => |F₀ (k + latticePoint P.L m) + R (k + latticePoint P.L m)| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun _ => abs_add_le _ _) (hsF₀.add hsR)
  have hE₁ := norm_coupleLeaves_sub_le P hη LG hplain (fun _ x => F₀ x + R x) k (fun _ _ => hsF) r Q
    heA hA₁ ht hs
  -- the mixed terms
  have hmix : ∀ S ∈ ((inputLeaves LG.garden).powerset).erase ∅,
      ‖coupleLeaves P.L P.γ P.δ LG (mixProfile LG S (fun _ => F₀) (fun _ => R)) t s k‖ ≤
        (eB + P.δ ^ n * 2 ^ n * cJ * cM) * (ρ * β ^ (2 * n + 1)) * jbr k ^ (-(30 * P.d : ℝ)) := by
    intro S hS
    obtain ⟨hne, hSP⟩ := Finset.mem_erase.mp hS
    have hsub : S ⊆ inputLeaves LG.garden := Finset.mem_powerset.mp hSP
    have hprod := leafSizeProduct_mixBound_le LG hsub (Finset.nonempty_iff_ne_empty.mpr hne) hρβ hβ
    rw [hcard] at hprod
    have hπ : 0 ≤ leafSizeProduct LG (mixBound LG S ρ β) :=
      Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    obtain ⟨hX, hM⟩ := hB _ _ (hctrl S)
    rw [← ENNReal.ofReal_mul heB] at hX
    have hE := norm_coupleLeaves_sub_le P hη LG hplain _ k (hsumS S hSP) r Q (mul_nonneg heB hπ)
      hX ht hs
    have hApp := norm_LeafApp_couple_le hδ r (mixProfile LG S (fun _ => F₀) (fun _ => R)) Q hsize
      t s k hcJ (mul_nonneg hcM hπ) hJ hM
    calc ‖coupleLeaves P.L P.γ P.δ LG (mixProfile LG S (fun _ => F₀) (fun _ => R)) t s k‖
        ≤ ‖coupleLeaves P.L P.γ P.δ LG (mixProfile LG S (fun _ => F₀) (fun _ => R)) t s k -
            LeafApp.couple P.δ r (mixProfile LG S (fun _ => F₀) (fun _ => R)) Q t s k‖ +
          ‖LeafApp.couple P.δ r (mixProfile LG S (fun _ => F₀) (fun _ => R)) Q t s k‖ :=
          norm_le_norm_sub_add _ _
      _ ≤ eB * leafSizeProduct LG (mixBound LG S ρ β) * jbr k ^ (-(30 * P.d : ℝ)) +
          P.δ ^ n * 2 ^ n * cJ * (cM * leafSizeProduct LG (mixBound LG S ρ β)) *
            jbr k ^ (-(30 * P.d : ℝ)) := add_le_add hE hApp
      _ = (eB + P.δ ^ n * 2 ^ n * cJ * cM) * leafSizeProduct LG (mixBound LG S ρ β) *
            jbr k ^ (-(30 * P.d : ℝ)) := by ring
      _ ≤ (eB + P.δ ^ n * 2 ^ n * cJ * cM) * (ρ * β ^ (2 * n + 1)) * jbr k ^ (-(30 * P.d : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ hj
          exact mul_le_mul_of_nonneg_left hprod (by positivity)
  -- the expansion
  have hexp := coupleLeaves_add P.L P.γ P.δ LG hplain F₀ R t s k hsumS
  rw [← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset _), mixProfile_empty] at hexp
  have hid : LeafApp.couple P.δ r (fun _ x => F₀ x + R x) Q t s k -
        LeafApp.couple P.δ r (fun _ => F₀) Q t s k =
      -(coupleLeaves P.L P.γ P.δ LG (fun _ x => F₀ x + R x) t s k -
          LeafApp.couple P.δ r (fun _ x => F₀ x + R x) Q t s k) +
        (coupleLeaves P.L P.γ P.δ LG (fun _ => F₀) t s k -
          LeafApp.couple P.δ r (fun _ => F₀) Q t s k) +
        ∑ S ∈ ((inputLeaves LG.garden).powerset).erase ∅,
          coupleLeaves P.L P.γ P.δ LG (mixProfile LG S (fun _ => F₀) (fun _ => R)) t s k := by
    rw [hexp]
    ring
  have hcardP : (((inputLeaves LG.garden).powerset).erase ∅).card ≤ 2 ^ (2 * n + 1) := by
    refine (Finset.card_erase_le).trans ?_
    rw [Finset.card_powerset, hcard]
  rw [hid]
  have hS := (norm_sum_le _ _).trans (Finset.sum_le_card_nsmul _ _ _ hmix)
  rw [nsmul_eq_mul] at hS
  have hS' : ‖∑ S ∈ ((inputLeaves LG.garden).powerset).erase ∅,
      coupleLeaves P.L P.γ P.δ LG (mixProfile LG S (fun _ => F₀) (fun _ => R)) t s k‖ ≤
      2 ^ (2 * n + 1) * ((eB + P.δ ^ n * 2 ^ n * cJ * cM) * (ρ * β ^ (2 * n + 1)) *
        jbr k ^ (-(30 * P.d : ℝ))) := by
    refine hS.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact_mod_cast hcardP
  calc _ ≤ ‖-(coupleLeaves P.L P.γ P.δ LG (fun _ x => F₀ x + R x) t s k -
          LeafApp.couple P.δ r (fun _ x => F₀ x + R x) Q t s k)‖ +
        ‖coupleLeaves P.L P.γ P.δ LG (fun _ => F₀) t s k -
          LeafApp.couple P.δ r (fun _ => F₀) Q t s k‖ +
        ‖∑ S ∈ ((inputLeaves LG.garden).powerset).erase ∅,
          coupleLeaves P.L P.γ P.δ LG (mixProfile LG S (fun _ => F₀) (fun _ => R)) t s k‖ :=
        norm_add₃_le
    _ ≤ eA * jbr k ^ (-(30 * P.d : ℝ)) + eA * jbr k ^ (-(30 * P.d : ℝ)) +
        2 ^ (2 * n + 1) * ((eB + P.δ ^ n * 2 ^ n * cJ * cM) * (ρ * β ^ (2 * n + 1)) *
          jbr k ^ (-(30 * P.d : ℝ))) := by
        rw [norm_neg]
        exact add_le_add (add_le_add hE₁ hE₀) hS'
    _ = _ := by ring

end WaveTurbulence.PL234
