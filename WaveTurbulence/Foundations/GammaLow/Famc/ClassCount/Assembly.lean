/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.Statement
public import WaveTurbulence.Foundations.Stage1.ClassCount.Assembly
/-! # CLASSCOUNT over `𝒱_γ`: the assembly from three legs (packet L5c, item I)

L5c port of main `WaveTurbulence.Foundations.Stage1.ClassCount.Assembly` (sha256 in COPIED-SHA256SUMS), the
`ClassCountStmt` part only (the `W`/`Mk` variants are not consumed by L5a's assembly). Over `𝒱_γ` (`γ ≤ 1/2`):
* `rbarOfG γ S σ` (main `rbarOf`) is `ρ̄` of L5a's piece `Fama.stage1PieceOf γ d hS LG hd σ` (`rbar_stage1PieceOfG`);
* `SkeletonLegG` (main `SkeletonLeg`) and `LayeringLegG` (main `LayeringLeg`) with `rbarOfG` / `Fama.stage1PieceOf`,
  the constants uniform in `γ ≤ 1/2`;
* main's `DecodeSizeLeg` is family-free and is used as is (main's `decodeSizeLeg`).
`classCountG_of_legs` is main's `classCount_of_legs`, verbatim up to these replacements. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famc.ClassCount
open WaveTurbulence.Induct
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RedSplice WaveTurbulence.Reg.Skeleton

variable [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput]

/-- `ρ̄` of `(S, σ)` over `𝒱_γ` (main `ClassCount.rbarOf`): `ρ(G_sb) + |hinges|` of L5a's construction. -/
noncomputable def rbarOfG (γ : ℝ) [Fact (γ ≤ 1 / 2)] {R : ℕ} (S : Garden (2 * R)) (σ : Prescription S) : ℕ :=
  (Fama.stSt γ S σ).G.molecule.rho + (Fama.collectionChoices γ S σ).hinges.card

/-- `ρ̄` at a marked set over `𝒱_γ` (main `rbarOfMk`); at `Mk = ∅` it is `rbarOfG` (`rfl`). -/
noncomputable def rbarOfMkG (γ : ℝ) [Fact (γ ≤ 1 / 2)] {R : ℕ} (S : Garden (2 * R)) (σ : Prescription S)
    (Mk : Set (Fama.CLVineG γ S)) : ℕ :=
  (Fama.stSt γ S σ Mk).G.molecule.rho + (Fama.collectionChoices γ S σ Mk).hinges.card

theorem rbarOfG_eq_rbarOfMkG (γ : ℝ) [Fact (γ ≤ 1 / 2)] {R : ℕ} (S : Garden (2 * R)) (σ : Prescription S) :
    rbarOfG γ S σ = rbarOfMkG γ S σ ∅ := rfl

theorem rbar_stage1PieceOfG (γ : ℝ) [Fact (γ ≤ 1 / 2)] {R : ℕ} (d : ℕ) {S : Garden (2 * R)}
    {D : ReconstructionData S} (hS : S.IsPlain) (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden)
    (σ : Prescription S) : (Fama.stage1PieceOf γ d hS LG hd σ).rbar = rbarOfG γ S σ := rfl

/-- **Leg 1 over `𝒱_γ`** (main `SkeletonLeg`): plain skeletons of order `≤ N` having a prescription with `ρ̄ = r`
number at most `C₀^N (C₀ r)! (C₀ R)!`, uniformly in `γ ≤ 1/2`. -/
def SkeletonLegG : Prop :=
  ∃ C₀ : ℕ, 2 ≤ C₀ ∧ ∀ (γ : ℝ) (hγ : γ ≤ 1 / 2), ∀ R N r : ℕ, 1 ≤ R → 1 ≤ N → ∀ T : Finset (Garden (2 * R)),
    (∀ S ∈ T, S.IsPlain ∧ S.order ≤ N ∧ ∃ σ : Prescription S, haveI : Fact (γ ≤ 1 / 2) := ⟨hγ⟩; rbarOfG γ S σ = r) →
    (T.card : ℝ) ≤ (C₀ : ℝ) ^ N * (((C₀ * r).factorial : ℕ) : ℝ) * (((C₀ * R).factorial : ℕ) : ℝ)

/-- **Leg 2 over `𝒱_γ`** (main `LayeringLeg`): over a fixed skeleton and replacement datum, the layered gardens
carrying a `𝒱_γ` piece with data `(g, r)` number at most `C₀^N C₂^{g+r}`. -/
def LayeringLegG : Prop :=
  ∃ C₀ K : ℕ, 1 ≤ C₀ ∧ ∀ P : WTParams, ∀ hγ : P.γ ≤ 1 / 2, K ^ (P.D + 1) ≤ P.C₂ → ∀ p, p < P.D →
    ∀ R, 1 ≤ R → ∀ N, 1 ≤ N → ∀ g r : ℕ, ∀ (S : Garden (2 * R)) (D : ReconstructionData S),
    ∀ A' : Finset (LayeredGarden (2 * R)), S.IsPlain → S.order ≤ N →
    (∀ LG ∈ A', Stage1Carries P p N LG ∧ haveI : Fact (P.γ ≤ 1 / 2) := ⟨hγ⟩;
      ∃ (hS : S.IsPlain) (hd : D.Decodes hS LG.garden) (σ : Prescription S),
        rbarOfG P.γ S σ = r ∧ (Fama.stage1PieceOf P.γ P.d hS LG hd σ).gbar = g) →
    (A'.card : ℝ) ≤ (C₀ : ℝ) ^ N * P.C₂ ^ (g + r)

/-- **The class count over `𝒱_γ` from the legs** (main `classCount_of_legs`). -/
theorem classCountG_of_legs (h0 : ClassCount.DecodeSizeLeg) (h1 : SkeletonLegG) (h2 : LayeringLegG) :
    ClassCountStmtG := by
  classical
  obtain ⟨C₁, hC₁, hsk⟩ := h1
  obtain ⟨C₃, K, hC₃, hlay⟩ := h2
  have h12 : 12 ^ 18 ≤ 2 ^ 65 := by norm_num
  have hC₀a : C₁ + 65 ≤ C₁ * 12 ^ 18 * C₃ := by
    have : C₁ * 12 ^ 18 ≤ C₁ * 12 ^ 18 * C₃ := Nat.le_mul_of_pos_right _ hC₃
    have h3 : 65 + C₁ ≤ C₁ * 12 ^ 18 := by nlinarith
    omega
  refine ⟨C₁ * 12 ^ 18 * C₃, K + 1, by nlinarith, ?_⟩
  intro P hγ hK' p hp R hR N hN g r A hA
  have : Fact (P.γ ≤ 1 / 2) := ⟨hγ⟩
  have hK : K ^ (P.D + 1) ≤ P.C₂ :=
    le_trans (by exact_mod_cast Nat.pow_le_pow_left (Nat.le_succ K) _) hK'
  have hC2one : (1 : ℝ) ≤ P.C₂ :=
    le_trans (by exact_mod_cast Nat.one_le_pow _ _ (Nat.succ_pos K)) hK'
  set C₀ : ℕ := C₁ * 12 ^ 18 * C₃ with hC₀
  have hex : ∀ LG : A, ∃ t : (Σ S : Garden (2 * R), ReconstructionData S),
      ∃ (hS : t.1.IsPlain) (hd : t.2.Decodes hS LG.1.garden) (σ : Prescription t.1),
        rbarOfG P.γ t.1 σ = r ∧ (Fama.stage1PieceOf P.γ P.d hS LG.1 hd σ).gbar = g := by
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
    refine hlay P hγ hK p hp R hR N hN g r (pick LG0).1 (pick LG0).2 _ hS0 (hord LG0).1 ?_
    intro LG' hLG'
    obtain ⟨LG, hLG, rfl⟩ := Finset.mem_map.mp hLG'
    have hLGeq : pick LG = pick LG0 := (Finset.mem_filter.mp hLG).2
    have h := hpick LG
    rw [hLGeq] at h
    exact ⟨(hA LG.1 LG.2).1, h⟩
  -- the skeleton count
  have hskel : ∀ S ∈ T.image Sigma.fst, S.IsPlain ∧ S.order ≤ N ∧ ∃ σ : Prescription S, rbarOfG P.γ S σ = r := by
    intro S hSm
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hSm
    obtain ⟨LG, -, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hS, hd, σ, hr, -⟩ := hpick LG
    exact ⟨hS, (hord LG).1, σ, hr⟩
  have hTS := hsk P.γ hγ R N r hR hN (T.image Sigma.fst) hskel
  have hdat : ∀ S ∈ T.image Sigma.fst, (T.filter (fun t => t.1 = S)).card ≤ (12 ^ 18) ^ (N + R) := by
    intro S hSm
    obtain ⟨hSp, hSo, -⟩ := hskel S hSm
    refine ClassCount.card_sigma_fiber_le S hSp (N + R) (by omega) (by omega) (by omega) _ ?_
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
    have h := ClassCount.fact_mul_pow_le C₁ R 65 (by omega) hR
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

end WaveTurbulence.GammaLow.Famc.ClassCount
