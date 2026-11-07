/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.PieceRem
public import WaveTurbulence.Foundations.VineEst.VineEstS3.BoxFacts
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.KCont

/-! # P2: the gate data as separated families and remainders (step 7 (1)-(2)); `SepFam`

`SepFam P Wm B q CJ CM f`: the separated expansion of an approximant `f(t,s,k)` on the time box `B` into `m` terms `c · J(t,s) · M(k)`
(`SepT`, the shape of `sepTerm`).  `sepFam_of_leafwise`: a `LeafwiseSeparated` approximant has such an expansion with `m ≤ 2^n`, `c = δ^n`,
`CJ = 2 C₁^{n+1}`, `CM = C₁^{n+1} · cost`.  `RemT.of_gate`: the gate remainder `K* - app` is a `RemT` (a.e. time-continuous representative,
the continuity of `K*` from `KCont`). -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P2
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.PL234 TTree WaveTurbulence.Reg WaveTurbulence.Links
  WaveTurbulence.VineEstS3.FS MeasureTheory
open scoped ENNReal ComplexConjugate

variable {P : WTParams}

/-- The separated expansion of the approximant `f` on the time box `B`. -/
structure SepFam (P : WTParams) (Wm : ℕ) (B : Set (Fin 2 → ℝ)) (q : Fin 2 → ℝ) (CJ CM : ℝ) (f : ℝ → ℝ → Mom P.d → ℂ) where
  m : ℕ
  term : Fin m → SepT P Wm B q CJ CM
  expand : ∀ t0 s0 : ℝ, ![t0, s0] ∈ B → ∀ k, f t0 s0 k = ∑ i, sepTerm (term i).c (term i).J (term i).M t0 s0 k

/-- Conjugate of a separated term (`J ↦ conj J`). -/
def SepT.conj {Wm : ℕ} {B : Set (Fin 2 → ℝ)} {q : Fin 2 → ℝ} {CJ CM : ℝ} (s : SepT P Wm B q CJ CM) : SepT P Wm B q CJ CM where
  c := s.c
  J := cJ s.J
  M := s.M
  hcell := s.hcell
  hint := s.hint
  hCJ := s.hCJ
  hCM := s.hCM
  hJ := s.hJc
  hM := s.hM

/-- **A `LeafwiseSeparated` approximant has a separated expansion** with the constants of the gate (one factor `2` of slack in `J`
for the strict inequality). -/
theorem sepFam_of_leafwise {n W : ℕ} {T : Set (Fin 2 → ℝ)} {q : Fin 2 → ℝ} (hc : T ⊆ cell q) (hi : T ⊆ closure (interior T))
    (hC1 : 1 ≤ P.C₁) {cost : ℝ} (hcost : 0 ≤ cost) {F : (Fin 2 → ℝ) → Mom P.d → ℂ}
    (h : LeafwiseSeparated P n W T F cost) :
    ∃ sf : SepFam P W T q (2 * (P.C₁ * P.C₁ ^ n)) (P.C₁ * P.C₁ ^ n * cost) (fun t s k => F ![t, s] k),
      sf.m ≤ 2 ^ n ∧ ∀ i, (sf.term i).c = P.δ ^ n := by
  obtain ⟨m, J, M, hm, hexp, hJ, hM⟩ := h
  have hpos : 0 < P.C₁ * P.C₁ ^ n := by have := pow_pos (lt_of_lt_of_le one_pos hC1) n; positivity
  refine ⟨⟨m, fun i => ⟨P.δ ^ n, J i, M i, hc, hi, by linarith, by positivity, ?_, hM i⟩, ?_⟩, hm, fun i => rfl⟩
  · exact lt_of_le_of_lt (hJ i) ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith))
  · intro t0 s0 hts k
    rw [hexp ![t0, s0] hts k]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [sepTerm]

/-- **The gate remainder is a `RemT`**: `K* - app` is a.e. equal to a time-continuous kernel (`remainder_ae_cont`, continuity of `K*` from `KCont`,
the separated expansion of `app`), with the restriction norm of the gate (slack: `CR0 < CR`). -/
theorem RemT.of_gate {Λ₂ : ℕ} {B : Set (Fin 2 → ℝ)} {q : Fin 2 → ℝ} (hc : B ⊆ cell q) (hi : B ⊆ closure (interior B))
    {Kst app : (Fin 2 → ℝ) → Mom P.d → ℂ} (hKc : ∀ k, Continuous fun ts => Kst ts k) {CR0 CR : ℝ} (hCR0 : CR0 < CR)
    (hCR : 0 < CR) (hθ : 6 * P.η ^ 6 ≤ P.η) (hη1 : P.η ≤ 1) {n W : ℕ} {cost : ℝ} (hsep : LeafwiseSeparated P n W B app cost)
    (hX : XNormRestr P.η (30 * P.d) Λ₂ B Set.univ (fun ts k => Kst ts k - app ts k) ≤ ENNReal.ofReal CR0) :
    ∃ R : RemT P Λ₂ B q CR, R.f = fun ts k => Kst ts k - app ts k := by
  obtain ⟨m, J, M, hm, hexp, hJ, hM⟩ := hsep
  have hJfin : ∀ i, XNorm00Restr (V := Unit) (1 - P.η) B Set.univ (fun ts _ => J i ts) < ⊤ := fun i =>
    lt_of_le_of_lt (hJ i) ENNReal.ofReal_lt_top
  obtain ⟨f', hcont, hae⟩ := remainder_ae_cont (θ := 1 - P.η) (by linarith) ((P.δ : ℂ) ^ n) Kst
    (fun ts k => Kst ts k - app ts k) J M hKc hJfin
    (fun t ht k => by rw [hexp t ht k])
  refine ⟨⟨fun ts k => Kst ts k - app ts k, f', hc, hi, hcont, hae, hCR.le, ?_⟩, rfl⟩
  exact lt_of_le_of_lt ((VineEstS3.XNormRestr_mono_theta hθ _ _ B _ _).trans hX) ((ENNReal.ofReal_lt_ofReal_iff hCR).2 hCR0)

theorem regBound_mul_cost (hδ : 0 < P.δ) (hC1 : 1 ≤ P.C₁) (hL : 1 ≤ P.L) (n : ℕ) {cost : ℝ} (hcost : 0 ≤ cost) :
    regBound P n 1 * ENNReal.ofReal cost =
      ENNReal.ofReal (P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (1 : ℕ)) * cost) := by
  unfold regBound
  rw [← ENNReal.ofReal_mul]
  have h0 : 0 ≤ P.C₁ := by linarith
  exact mul_nonneg (mul_nonneg h0 (pow_nonneg (mul_nonneg h0 hδ.le) _)) (Real.rpow_nonneg (by linarith) _)

section Gate
variable {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ} {p : ℕ}

/-- **Gate data of a coherent couple** (TARGET Prop 6.1 / `CoherentGateH`): the separated expansion of the approximant
`SourceApp.couple` on `timeBox q q'` and the `RemT` of the remainder `K* - SourceApp.couple`. -/
theorem couple_gate_data (hg : CoherentGateH P) (hB : ProfileBound P h Bh p) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hC1 : 1 ≤ P.C₁)
    (hδ : 0 < P.δ) (hη : P.η ≤ 1) (hθ : 6 * P.η ^ 6 ≤ P.η) (hp : p < P.D) {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4) {Q : RegCpl} {LG : LayeredGarden 2}
    {q q' : ℕ} (hqq : q' ≤ q) (hqp : q ≤ p) (hsize : Q.size = 2 * n) (hcoh : IsCoherentCoupleAt p q q' Q LG)
    {CR : ℝ} (hCR : P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (1 : ℕ)) * layerCost Bh LG < CR) :
    ∃ sf : SepFam P (30 * P.d) (timeBox q q') ![(q : ℝ), q'] (2 * (P.C₁ * P.C₁ ^ n)) (P.C₁ * P.C₁ ^ n * layerCost Bh LG)
        (fun t s k => SourceApp.couple P.δ h LG Q q q' t s k),
      sf.m ≤ 2 ^ n ∧ (∀ i, (sf.term i).c = P.δ ^ n) ∧
      ∃ R : RemT P (30 * P.d) (timeBox q q') ![(q : ℝ), q'] CR,
        R.f = fun ts k => KQstar P.L P.γ P.δ h LG (ts 0) (ts 1) k - SourceApp.couple P.δ h LG Q q q' (ts 0) (ts 1) k := by
  obtain ⟨hE, -, hSp⟩ := (hg h Bh p hp hB n hn).1 Q LG q q' hqq hqp hsize hcoh
  have hcost : 0 ≤ layerCost Bh LG := layerCost_nonneg LG fun x => (hB _ (coherentCouple_layer_le hqq hqp hcoh x)).1
  have hcell := VineEstS3.timeBox_subset_cell (q : ℝ) q'
  have hint := VineEstS3.timeBox_subset_closure_interior (q : ℝ) q'
  obtain ⟨sf, hm, hc⟩ := sepFam_of_leafwise (P := P) hcell hint hC1 hcost hSp
  refine ⟨sf, hm, hc, ?_⟩
  have hCR0 : 0 < CR := lt_of_le_of_lt (by
    have h0 : 0 ≤ P.C₁ := by linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg h0 (pow_nonneg (mul_nonneg h0 hδ.le) _)) (Real.rpow_nonneg (by linarith) _)) hcost) hCR
  refine RemT.of_gate hcell hint (fun k => ?_) hCR hCR0 hθ hη hSp ?_
  · exact continuous_KQstar_of_coherent hB hd hL hqq hqp hcoh k
  · rw [regBound_mul_cost hδ hC1 hL n hcost] at hE
    exact hE

/-- **Gate data of a coherent tree** (order `0` in the momentum weight; the box is `timeBoxGt q q'`). -/
theorem tree_gate_data (hg : CoherentGateH P) (hB : ProfileBound P h Bh p) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hC1 : 1 ≤ P.C₁)
    (hδ : 0 < P.δ) (hη : P.η ≤ 1) (hθ : 6 * P.η ^ 6 ≤ P.η) (hp : p < P.D) {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4) {X : RegChain} {LG : LayeredGarden 1}
    {q q' : ℕ} (hqq : q' ≤ q) (hqp : q ≤ p) (hsize : X.size = 2 * n) (hcoh : IsCoherentTreeAt p q q' X LG)
    {CR : ℝ} (hCR : P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (1 : ℕ)) * layerCost Bh LG < CR) :
    ∃ sf : SepFam P 0 (timeBoxGt q q') ![(q : ℝ), q'] (2 * (P.C₁ * P.C₁ ^ n)) (P.C₁ * P.C₁ ^ n * layerCost Bh LG)
        (fun t s k => SourceApp.tree P.δ h LG X q q' t s k),
      sf.m ≤ 2 ^ n ∧ (∀ i, (sf.term i).c = P.δ ^ n) ∧
      ∃ R : RemT P 0 (timeBoxGt q q') ![(q : ℝ), q'] CR,
        R.f = fun ts k => KTstar P.L P.γ P.δ h LG (ts 0) (ts 1) k - SourceApp.tree P.δ h LG X q q' (ts 0) (ts 1) k := by
  obtain ⟨hE, -, hSp⟩ := (hg h Bh p hp hB n hn).2 X LG q q' hqq hqp hsize hcoh
  have hcost : 0 ≤ layerCost Bh LG := layerCost_nonneg LG fun x =>
    (hB _ ((coherentTree_layer_le hqq hcoh x).trans hqp)).1
  have hcell := VineEstS3.timeBoxGt_subset_cell (q : ℝ) q'
  have hint := VineEstS3.timeBoxGt_subset_closure_interior (q := (q : ℝ)) (q' := (q' : ℝ)) (by exact_mod_cast hqq)
  obtain ⟨sf, hm, hc⟩ := sepFam_of_leafwise (P := P) hcell hint hC1 hcost hSp
  refine ⟨sf, hm, hc, ?_⟩
  have hCR0 : 0 < CR := lt_of_le_of_lt (by
    have h0 : 0 ≤ P.C₁ := by linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg h0 (pow_nonneg (mul_nonneg h0 hδ.le) _)) (Real.rpow_nonneg (by linarith) _)) hcost) hCR
  refine RemT.of_gate hcell hint (fun k => ?_) hCR hCR0 hθ hη hSp ?_
  · exact continuous_KTstar_of_coherent hB hd hL hqq hqp hcoh k
  · rw [regBound_mul_cost hδ hC1 hL n hcost] at hE
    exact hE

end Gate

end WaveTurbulence.VineEstS5C.P2
