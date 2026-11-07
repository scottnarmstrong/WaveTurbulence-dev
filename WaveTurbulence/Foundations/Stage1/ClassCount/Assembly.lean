/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.ClassCountStmt
public import WaveTurbulence.Foundations.Stage1.Shared.SourceReconstructionExponentialCount
import Mathlib.Tactic

/-!
# CLASSCOUNT: the final assembly from three legs

`classCount_of_legs` derives `ClassCountStmt` (TARGET L2241-L2252) from three garden-level legs, each stated as a
named proposition (never a source result):
* `DecodeSizeLeg`: a decoded skeleton has order and replacement size at most the order of the garden;
* `SkeletonLeg` (TARGET L2241-L2247, `propcplmol` + ladder/unit molecule counts): the number of plain skeletons of order
  `≤ N` having a prescription with `ρ̄ = r` is at most `C₀^N (C₀ r)! (C₀ R)!`;
* `LayeringLeg` (TARGET L2248-L2252): for fixed skeleton `S` and replacement data `D`, the number of canonical
  layered gardens carrying a piece of data `(g, r)` is at most `C₀^N C₂^{g+r}`.
The replacement data count is `source_reconstruction_data_exponential` (propstructure2).
-/

@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RedSplice WaveTurbulence.Reg.Skeleton

/-- `ρ̄` of the pair `(S, σ)`: `ρ_sb + #hinges` (TARGET L2237). -/
noncomputable def rbarOf {R : ℕ} (S : Garden (2 * R)) (σ : Prescription S) : ℕ :=
  (stSt S σ).G.molecule.rho + (collectionChoices S σ).hinges.card

theorem rbar_stage1PieceOf {R : ℕ} (d : ℕ) {S : Garden (2 * R)} {D : ReconstructionData S}
    (hS : S.IsPlain) (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden) (σ : Prescription S) :
    (stage1PieceOf d hS LG hd σ).rbar = rbarOf S σ := rfl

/-- Leg 0: a decoded skeleton and its replacements fit in the order of the garden. -/
def DecodeSizeLeg : Prop :=
  ∀ {R : ℕ} (S : Garden (2 * R)) (D : ReconstructionData S) (hS : S.IsPlain) (G : Garden (2 * R)),
    D.Decodes hS G → S.order ≤ G.order ∧ D.size ≤ G.order

/-- Leg 1: the number of skeletons. -/
def SkeletonLeg : Prop :=
  ∃ C₀ : ℕ, 2 ≤ C₀ ∧ ∀ R N r : ℕ, 1 ≤ R → 1 ≤ N → ∀ T : Finset (Garden (2 * R)),
    (∀ S ∈ T, S.IsPlain ∧ S.order ≤ N ∧ ∃ σ : Prescription S, rbarOf S σ = r) →
    (T.card : ℝ) ≤ (C₀ : ℝ) ^ N * (((C₀ * r).factorial : ℕ) : ℝ) * (((C₀ * R).factorial : ℕ) : ℝ)

/-- Leg 2: the number of layered gardens over one skeleton and one replacement datum. -/
def LayeringLeg : Prop :=
  ∃ C₀ K : ℕ, 1 ≤ C₀ ∧ ∀ P : WTParams, K ^ (P.D + 1) ≤ P.C₂ → ∀ p, p < P.D →
    ∀ R, 1 ≤ R → ∀ N, 1 ≤ N → ∀ g r : ℕ, ∀ (S : Garden (2 * R)) (D : ReconstructionData S),
    ∀ A' : Finset (LayeredGarden (2 * R)), S.IsPlain → S.order ≤ N →
    (∀ LG ∈ A', Stage1Carries P p N LG ∧ ∃ (hS : S.IsPlain) (hd : D.Decodes hS LG.garden)
      (σ : Prescription S), rbarOf S σ = r ∧ (stage1PieceOf P.d hS LG hd σ).gbar = g) →
    (A'.card : ℝ) ≤ (C₀ : ℝ) ^ N * P.C₂ ^ (g + r)

theorem finite_data_le {w : ℕ} (S : Garden w) (m : ℕ) : Finite {D : ReconstructionData S // D.size ≤ m} := by
  classical
  let f : {D : ReconstructionData S // D.size ≤ m} →
      {D : ReplacementFamily (Fintype.card (GBranch S.tree)) (Fintype.card (SourcePair S)) // D.size ≤ m} :=
    fun D => ⟨D.1.family, by rw [ReconstructionData.family_size]; exact D.2⟩
  have hf : Function.Injective f := by
    intro D E he
    exact Subtype.ext (ReconstructionData.family_injective S (congrArg Subtype.val he))
  exact Finite.of_injective f hf


/-- A finite set of pairs `(S', D)` with first component `S` and `D.size ≤ n` has at most `(12^18)^n` elements. -/
theorem card_sigma_fiber_le {R : ℕ} (S : Garden (2 * R)) (hS : S.IsPlain) (n : ℕ) (hn : 1 ≤ n)
    (hord : S.order ≤ n) (hR : R ≤ n + 1)
    (T : Finset (Σ S' : Garden (2 * R), ReconstructionData S'))
    (h : ∀ t ∈ T, t.1 = S ∧ t.2.size ≤ n) : T.card ≤ (12 ^ 18) ^ n := by
  classical
  haveI := finite_data_le S n
  have hmem : ∀ t : T, t.1.1 = S ∧ t.1.2.size ≤ n := fun t => h t.1 t.2
  let g : T → {D : ReconstructionData S // D.size ≤ n} := fun t =>
    ⟨(hmem t).1 ▸ t.1.2, by
      obtain ⟨⟨S', D⟩, ht⟩ := t
      obtain ⟨h1, h2⟩ := h _ ht
      subst h1
      exact h2⟩
  have hg : Function.Injective g := by
    rintro ⟨⟨S1, D1⟩, ht1⟩ ⟨⟨S2, D2⟩, ht2⟩ he
    obtain ⟨h1, -⟩ := h _ ht1
    obtain ⟨h2, -⟩ := h _ ht2
    simp only at h1 h2
    subst h1
    subst h2
    simp only [g] at he
    have := congrArg Subtype.val he
    simp only at this
    subst this
    rfl
  have := Nat.card_le_card_of_injective g hg
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at this
  exact this.trans (source_reconstruction_data_exponential S hS hn hord hR)


theorem fact_mul_pow_le (a R c : ℕ) (ha : 1 ≤ a) (hR : 1 ≤ R) :
    (a * R).factorial * (2 ^ c) ^ R ≤ ((a + c) * R).factorial := by
  have h := @Nat.factorial_mul_pow_le_factorial (a * R) (c * R)
  have h2 : (2 ^ c) ^ R ≤ (a * R + 1) ^ (c * R) := by
    rw [← pow_mul, mul_comm c R]
    exact Nat.pow_le_pow_left (by nlinarith) _
  calc (a * R).factorial * (2 ^ c) ^ R ≤ (a * R).factorial * (a * R + 1) ^ (c * R) :=
        Nat.mul_le_mul_left _ h2
    _ ≤ (a * R + c * R).factorial := h
    _ = ((a + c) * R).factorial := by rw [add_mul]

/-- **Assembly**: the three legs give the class count. -/
theorem classCount_of_legs (h0 : DecodeSizeLeg) (h1 : SkeletonLeg) (h2 : LayeringLeg) :
    ClassCountStmt := by
  classical
  obtain ⟨C₁, hC₁, hsk⟩ := h1
  obtain ⟨C₃, K, hC₃, hlay⟩ := h2
  have h12 : 12 ^ 18 ≤ 2 ^ 65 := by norm_num
  have hC₀a : C₁ + 65 ≤ C₁ * 12 ^ 18 * C₃ := by
    have : C₁ * 12 ^ 18 ≤ C₁ * 12 ^ 18 * C₃ := Nat.le_mul_of_pos_right _ hC₃
    have h3 : 65 + C₁ ≤ C₁ * 12 ^ 18 := by nlinarith
    omega
  refine ⟨C₁ * 12 ^ 18 * C₃, K + 1, by nlinarith, ?_⟩
  intro P hK' p hp R hR N hN g r A hA
  have hK : K ^ (P.D + 1) ≤ P.C₂ :=
    le_trans (by exact_mod_cast Nat.pow_le_pow_left (Nat.le_succ K) _) hK'
  have hC2one : (1 : ℝ) ≤ P.C₂ :=
    le_trans (by exact_mod_cast Nat.one_le_pow _ _ (Nat.succ_pos K)) hK'
  set C₀ : ℕ := C₁ * 12 ^ 18 * C₃ with hC₀
  have hex : ∀ LG : A, ∃ t : (Σ S : Garden (2 * R), ReconstructionData S),
      ∃ (hS : t.1.IsPlain) (hd : t.2.Decodes hS LG.1.garden) (σ : Prescription t.1),
        rbarOf t.1 σ = r ∧ (stage1PieceOf P.d hS LG.1 hd σ).gbar = g := by
    intro LG
    obtain ⟨-, S, D, hS, hd, σ, hg, hr⟩ := hA LG.1 LG.2
    exact ⟨⟨S, D⟩, hS, hd, σ, hr, hg⟩
  choose pick hpick using hex
  have hord : ∀ LG : A, (pick LG).1.order ≤ N ∧ (pick LG).2.size ≤ N := by
    intro LG
    obtain ⟨hS, hd, -⟩ := hpick LG
    have := h0 (pick LG).1 (pick LG).2 hS LG.1.garden hd
    have hN' : LG.1.garden.order = N := (hA LG.1 LG.2).1.2.2.1
    omega
  set T : Finset (Σ S : Garden (2 * R), ReconstructionData S) := A.attach.image pick with hT
  -- fibers over layered gardens
  have hfib : ∀ t ∈ T, ((A.attach.filter (fun LG => pick LG = t)).card : ℝ) ≤
      (C₃ : ℝ) ^ N * P.C₂ ^ (g + r) := by
    intro t ht
    obtain ⟨LG0, -, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hS0, -, -⟩ := hpick LG0
    have hcard : (A.attach.filter (fun LG => pick LG = pick LG0)).card =
        ((A.attach.filter (fun LG => pick LG = pick LG0)).map
          ⟨Subtype.val, Subtype.val_injective⟩).card := by rw [Finset.card_map]
    rw [hcard]
    refine hlay P hK p hp R hR N hN g r (pick LG0).1 (pick LG0).2 _ hS0 (hord LG0).1 ?_
    intro LG' hLG'
    obtain ⟨LG, hLG, rfl⟩ := Finset.mem_map.mp hLG'
    have hLGeq : pick LG = pick LG0 := (Finset.mem_filter.mp hLG).2
    have h := hpick LG
    rw [hLGeq] at h
    exact ⟨(hA LG.1 LG.2).1, h⟩
  -- the skeleton count
  have hskel : ∀ S ∈ T.image Sigma.fst, S.IsPlain ∧ S.order ≤ N ∧ ∃ σ : Prescription S, rbarOf S σ = r := by
    intro S hSm
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hSm
    obtain ⟨LG, -, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hS, hd, σ, hr, -⟩ := hpick LG
    exact ⟨hS, (hord LG).1, σ, hr⟩
  have hTS := hsk R N r hR hN (T.image Sigma.fst) hskel
  have hdat : ∀ S ∈ T.image Sigma.fst, (T.filter (fun t => t.1 = S)).card ≤ (12 ^ 18) ^ (N + R) := by
    intro S hSm
    obtain ⟨hSp, hSo, -⟩ := hskel S hSm
    refine card_sigma_fiber_le S hSp (N + R) (by omega) (by omega) (by omega) _ ?_
    intro t ht
    obtain ⟨ht1, ht2⟩ := Finset.mem_filter.mp ht
    obtain ⟨LG, -, rfl⟩ := Finset.mem_image.mp ht1
    exact ⟨ht2, by have := (hord LG).2; omega⟩
  have hTcard : (T.card : ℝ) ≤ ((C₁ : ℝ) ^ N * (((C₁ * r).factorial : ℕ) : ℝ) * (((C₁ * R).factorial : ℕ) : ℝ)) *
      (((12 : ℝ) ^ 18) ^ (N + R)) := by
    have h1 : T.card = ∑ S ∈ T.image Sigma.fst, (T.filter (fun t => t.1 = S)).card :=
      Finset.card_eq_sum_card_image _ _
    have h2 : T.card ≤ (T.image Sigma.fst).card * (12 ^ 18) ^ (N + R) := by
      rw [h1]
      calc ∑ S ∈ T.image Sigma.fst, (T.filter (fun t => t.1 = S)).card
          ≤ ∑ S ∈ T.image Sigma.fst, (12 ^ 18) ^ (N + R) := Finset.sum_le_sum hdat
        _ = _ := by simp
    have h3 : (T.card : ℝ) ≤ ((T.image Sigma.fst).card : ℝ) * (((12 : ℝ) ^ 18) ^ (N + R)) := by
      exact_mod_cast h2
    refine h3.trans ?_
    exact mul_le_mul_of_nonneg_right hTS (by positivity)
  -- total
  have hA1 : A.card = ∑ t ∈ T, (A.attach.filter (fun LG => pick LG = t)).card := by
    rw [← Finset.card_attach (s := A)]
    exact Finset.card_eq_sum_card_image _ _
  have hAcard : (A.card : ℝ) ≤ (T.card : ℝ) * ((C₃ : ℝ) ^ N * P.C₂ ^ (g + r)) := by
    rw [hA1]; push_cast
    calc ∑ t ∈ T, ((A.attach.filter (fun LG => pick LG = t)).card : ℝ)
        ≤ ∑ t ∈ T, ((C₃ : ℝ) ^ N * P.C₂ ^ (g + r)) := Finset.sum_le_sum hfib
      _ = _ := by simp
  have hC2 : (0 : ℝ) ≤ P.C₂ ^ (g + r) := by positivity
  -- arithmetic
  have hfact1 : ((C₁ * r).factorial : ℝ) ≤ ((C₀ * r).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.mul_le_mul_right _ (by omega))
  have hfact2 : ((C₁ * R).factorial : ℝ) * ((12 : ℝ) ^ 18) ^ R ≤ ((C₀ * R).factorial : ℝ) := by
    have h := fact_mul_pow_le C₁ R 65 (by omega) hR
    have h' : (C₁ * R).factorial * (12 ^ 18) ^ R ≤ (C₀ * R).factorial := by
      refine le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h12 R)) ?_
      exact h.trans (Nat.factorial_le (Nat.mul_le_mul_right _ hC₀a))
    exact_mod_cast h'
  have hC0N : (C₀ : ℝ) ^ N = (C₁ : ℝ) ^ N * ((12 : ℝ) ^ 18) ^ N * (C₃ : ℝ) ^ N := by
    rw [hC₀]; push_cast; rw [mul_pow, mul_pow]; norm_num
  calc (A.card : ℝ) ≤ (T.card : ℝ) * ((C₃ : ℝ) ^ N * P.C₂ ^ (g + r)) := hAcard
    _ ≤ ((C₁ : ℝ) ^ N * (((C₁ * r).factorial : ℕ) : ℝ) * (((C₁ * R).factorial : ℕ) : ℝ)) *
          (((12 : ℝ) ^ 18) ^ (N + R)) * ((C₃ : ℝ) ^ N * P.C₂ ^ (g + r)) :=
        mul_le_mul_of_nonneg_right hTcard (by positivity)
    _ = ((C₁ : ℝ) ^ N * ((12 : ℝ) ^ 18) ^ N * (C₃ : ℝ) ^ N) * ((C₁ * r).factorial : ℝ) *
          (((C₁ * R).factorial : ℝ) * ((12 : ℝ) ^ 18) ^ R) * P.C₂ ^ (g + r) := by
        rw [pow_add]; ring
    _ ≤ (C₀ : ℝ) ^ N * ((C₀ * r).factorial : ℝ) * ((C₀ * R).factorial : ℝ) * P.C₂ ^ (g + r) := by
        rw [hC0N]
        gcongr


/-- **Leg 0 is proved**: `G.order = S.order + D.size` (`decoded_order`). -/
theorem decodeSizeLeg : DecodeSizeLeg := by
  intro R S D hS G hd
  have := D.decoded_order hS hd
  omega

end WaveTurbulence.ClassCount
