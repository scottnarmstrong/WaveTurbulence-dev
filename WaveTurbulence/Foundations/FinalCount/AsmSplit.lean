/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmCountAlg
public import WaveTurbulence.Foundations.FinalCount.G3Ghost
public import WaveTurbulence.Foundations.FinalCount.RestrictRank
/-! **FINALCOUNT-ASSEMBLY, A3: splitting off a union of components.**

For a closed predicate `P` of a molecule `N`: `𝔈(N) ≤ 𝔈(N|P) · 𝔈(N|¬P)` for the classes `projAdm` (projections of `Adm` to the
darts of `P`, `¬P`), and the same for `𝔄` (rank and ladder products are additive). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- The projection of a class of labellings to the darts at the atoms satisfying `P`. -/
def projAdm (N : Molecule V D) (P : V → Prop) (Adm : (D → (Fin d → ℤ)) → Prop) :
    (PDart N P → (Fin d → ℤ)) → Prop :=
  fun κ' => ∃ κ, Adm κ ∧ κ' = fun x => κ x.1

variable (N : Molecule V D) (P : V → Prop) [DecidablePred P] (h : PClosed N P)

theorem projAdm_mem {Adm : (D → (Fin d → ℤ)) → Prop} {κ : D → (Fin d → ℤ)} (hκ : Adm κ) :
    projAdm N P Adm (fun x => κ x.1) := ⟨κ, hκ, rfl⟩

include h in
theorem decSet_restrict (L γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (c : V → Mom d) (β : V → ℝ)
    (k0 : D → Mom d) {κ : D → (Fin d → ℤ)} (hκ : κ ∈ decSet N L γ δ w Adm c β k0) :
    (fun x : PDart N P => κ x.1) ∈ decSet (restrictP N P h) L γ δ w (projAdm N P Adm) c β (fun x => k0 x.1) := by
  obtain ⟨⟨hmate, hsum⟩, ⟨hG, hk⟩, hA⟩ := hκ
  refine ⟨⟨fun x => hmate x.1, fun v hv => ?_⟩, ⟨fun v hv => ?_, fun x => hk x.1⟩, projAdm_mem N P hA⟩
  · have hv' := Finset.mem_filter.1 hv
    have := hsum v hv'.1
    show ∑ x ∈ (restrictP N P h).dartsAt v, N.dartSign x.1 • Molecule.kvec L w κ x.1 = c v
    rw [sum_dartsAt_restrict N P h hv'.2 (fun x => N.dartSign x • Molecule.kvec L w κ x)]
    exact this
  · have hv' := Finset.mem_filter.1 hv
    have := hG v hv'.1
    unfold Molecule.Gamma at this
    show |(restrictP N P h).Gamma L w (fun x => κ x.1) v - β v| ≤ _
    unfold Molecule.Gamma
    rw [show ∑ x ∈ (restrictP N P h).dartsAt v, (restrictP N P h).dartSign x *
        ‖Molecule.kvec L w (fun x : PDart N P => κ x.1) x‖ ^ 2 =
        ∑ x ∈ (restrictP N P h).dartsAt v, N.dartSign x.1 * ‖Molecule.kvec L w κ x.1‖ ^ 2 from rfl,
      sum_dartsAt_restrict N P h hv'.2 (fun x => N.dartSign x * ‖Molecule.kvec L w κ x‖ ^ 2)]
    exact this

include h in
theorem paramOK_restrict (c : V → Mom d) (k0 : D → Mom d) (hp : ParamOK N c k0) :
    ParamOK (restrictP N P h) c (fun x => k0 x.1) :=
  ⟨fun v hv hv4 => hp.1 v (Finset.mem_filter.1 hv).1 (by rw [← restrictP_deg N P h (Finset.mem_filter.1 hv).2]; exact hv4),
    fun x => hp.2 x.1⟩

include h in
/-- **Splitting `𝔈`.** -/
theorem countE_split_le (L γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) :
    N.countE L γ δ w Adm ≤ (restrictP N P h).countE L γ δ w (projAdm N P Adm) *
      (restrictP N (fun a => ¬ P a) h.neg).countE L γ δ w (projAdm N (fun a => ¬ P a) Adm) := by
  unfold Molecule.countE
  refine iSup_le fun c => iSup_le fun hc => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk => ?_
  set S := decSet N L γ δ w Adm c β k0 with hS
  let ρ : (D → (Fin d → ℤ)) → (PDart N P → (Fin d → ℤ)) × (PDart N (fun a => ¬ P a) → (Fin d → ℤ)) :=
    fun κ => (fun x => κ x.1, fun x => κ x.1)
  have hinj : Set.InjOn ρ S := by
    intro κ _ κ' _ e
    funext x
    by_cases hx : P (N.atom x)
    · exact congrFun (congrArg Prod.fst e) ⟨x, hx⟩
    · exact congrFun (congrArg Prod.snd e) ⟨x, hx⟩
  have hp : ParamOK N c k0 := ⟨hc, hk⟩
  have hsub : ρ '' S ⊆ decSet (restrictP N P h) L γ δ w (projAdm N P Adm) c β (fun x => k0 x.1) ×ˢ
      decSet (restrictP N (fun a => ¬ P a) h.neg) L γ δ w (projAdm N (fun a => ¬ P a) Adm) c β (fun x => k0 x.1) := by
    rintro _ ⟨κ, hκ, rfl⟩
    exact ⟨decSet_restrict N P h L γ δ w Adm c β k0 hκ, decSet_restrict N (fun a => ¬ P a) h.neg L γ δ w Adm c β k0 hκ⟩
  have p1 := paramOK_restrict N P h c k0 hp
  have p2 := paramOK_restrict N (fun a => ¬ P a) h.neg c k0 hp
  calc S.encard = (ρ '' S).encard := (hinj.encard_image).symm
    _ ≤ _ := Set.encard_le_encard hsub
    _ = _ := Set.encard_prod
    _ ≤ _ := mul_le_mul' (decSet_encard_le_countE _ L γ δ w _ c p1.1 β _ p1.2)
        (decSet_encard_le_countE _ L γ δ w _ c p2.1 β _ p2.2)

include h in
/-- **Splitting `𝔄`.** -/
theorem countA_split_le (L γ δ C₁ : ℝ) (w : Mom d) (hL : 0 < L) (hδ : 0 < δ) (hC : 0 < C₁)
    (Adm : (D → (Fin d → ℤ)) → Prop) (Pl : Finset V → ℝ) (hX : ∀ S, 0 ≤ Molecule.ladderWeight L γ δ (Pl S)) :
    N.countA L γ δ C₁ w Adm Pl ≤ (restrictP N P h).countA L γ δ C₁ w (projAdm N P Adm) Pl *
      (restrictP N (fun a => ¬ P a) h.neg).countA L γ δ C₁ w (projAdm N (fun a => ¬ P a) Adm) Pl := by
  rw [countA_eq, countA_eq, countA_eq]
  have hrk := circuitRank_restrictP_add N P h
  have hrf : rankFactor d L γ δ C₁ N.circuitRank =
      rankFactor d L γ δ C₁ (restrictP N P h).circuitRank *
        rankFactor d L γ δ C₁ (restrictP N (fun a => ¬ P a) h.neg).circuitRank := by
    rw [← rankFactor_add d hL hδ hC.ne', hrk]
  have hlad := ladderProd_restrictP N P h (fun S => Molecule.ladderWeight L γ δ (Pl S) ^ Molecule.ladderLength S)
  have n1 : 0 ≤ rankFactor d L γ δ C₁ (restrictP N P h).circuitRank := rankFactor_nonneg d hL.le hδ.le hC.le _
  have n2 : 0 ≤ rankFactor d L γ δ C₁ (restrictP N (fun a => ¬ P a) h.neg).circuitRank :=
    rankFactor_nonneg d hL.le hδ.le hC.le _
  have l1 : 0 ≤ ∏ S ∈ (restrictP N P h).maximalLadders, Molecule.ladderWeight L γ δ (Pl S) ^ Molecule.ladderLength S :=
    Finset.prod_nonneg fun S _ => pow_nonneg (hX S) _
  have l2 : 0 ≤ ∏ S ∈ (restrictP N (fun a => ¬ P a) h.neg).maximalLadders,
      Molecule.ladderWeight L γ δ (Pl S) ^ Molecule.ladderLength S := Finset.prod_nonneg fun S _ => pow_nonneg (hX S) _
  have hE : ((N.countE L γ δ w Adm : ℕ∞) : ℝ≥0∞) ≤ ((restrictP N P h).countE L γ δ w (projAdm N P Adm) : ℕ∞) *
      ((restrictP N (fun a => ¬ P a) h.neg).countE L γ δ w (projAdm N (fun a => ¬ P a) Adm) : ℕ∞) := by
    rw [← ENat.toENNReal_mul]; exact ENat.toENNReal_le.2 (countE_split_le N P h L γ δ w Adm)
  rw [hrf, hlad]
  set r1 := rankFactor d L γ δ C₁ (restrictP N P h).circuitRank
  set r2 := rankFactor d L γ δ C₁ (restrictP N (fun a => ¬ P a) h.neg).circuitRank
  set l1' := ∏ S ∈ (restrictP N P h).maximalLadders, Molecule.ladderWeight L γ δ (Pl S) ^ Molecule.ladderLength S
  set l2' := ∏ S ∈ (restrictP N (fun a => ¬ P a) h.neg).maximalLadders,
      Molecule.ladderWeight L γ δ (Pl S) ^ Molecule.ladderLength S
  have e : r1 * r2 * (l1' * l2') = (r1 * l1') * (r2 * l2') := by ring
  rw [e, ENNReal.ofReal_mul (mul_nonneg n1 l1)]
  calc _ ≤ (((restrictP N P h).countE L γ δ w (projAdm N P Adm) : ℕ∞) : ℝ≥0∞) *
        (((restrictP N (fun a => ¬ P a) h.neg).countE L γ δ w (projAdm N (fun a => ¬ P a) Adm) : ℕ∞) : ℝ≥0∞) *
        (ENNReal.ofReal (r1 * l1') * ENNReal.ofReal (r2 * l2')) := by gcongr
    _ = _ := by ring

end WaveTurbulence.FinalCountAsm
