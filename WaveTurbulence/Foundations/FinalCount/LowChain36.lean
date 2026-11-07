/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain35
public import WaveTurbulence.Foundations.FinalCount.AsmFamU
/-! **FINALCOUNT LOW-CHAIN, session 6 (10): the weighted terminal family** (R79).  `terminal_familyLU`: at a state `hf` of a run, with the loop atoms
`B ⊆ tameSet hf Tm` (degree `≤ 2` in `M₀`, effective fixedness), the Operation-5 chain gives
`rankFactor(|B|) · QS ≤ ∏_K clusterRHSs(m_K, e_K, j_K + k_K) · ∏_a 𝔄(component a)` with `Σ_K k_K = |B|`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u v
variable {V : Type v} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem famTameE_state {M₀ : Molecule V D₀} {s : St.{u} V D₀} (hc : LCtx M₀ s) (Tm : V → Prop) (A : Set (D₀ → (Fin d → ℤ)))
    (hTame : ∀ k0 ∈ A, ∀ v ∈ M₀.atoms, Tm v → ∀ x y, M₀.atom x = v → M₀.atom y = v → k0 x = k0 y)
    (hmate : ∀ k0 ∈ A, ∀ x, k0 (M₀.mate x) = k0 x)
    (B : Finset V) (hB₀ : ∀ b ∈ B, M₀.deg b ≤ 2)
    (hfix : ∀ v ∈ M₀.atoms, Tm v → M₀.deg v + (if v ∈ B then 2 else 0) < 4 → ∃ k, ∀ k0 ∈ A, ∀ x, M₀.atom x = v → k0 x = k)
    (𝒦 : Finset (Finset V))
    (hK : ∀ K ∈ 𝒦, (∀ a ∈ K, a ∈ s.M.atoms ∧ s.cls a = .eps ∧ Tm a) ∧ (∀ a ∈ K, 1 ≤ s.M.deg a) ∧
      ∀ a ∈ K, ∀ b ∈ K, (eraseSet s.M (s.M.atoms \ K)).SameComponent a b) :
    FamTameE s.M B 𝒦 (AdmS (fun k => k ∈ A) s) := by
  obtain ⟨an, han⟩ := hc.anc
  have hrel := hc.rel
  intro K hKm
  obtain ⟨hK1, hK2, hK3⟩ := hK K hKm
  -- values at darts of the state at atoms of `K`
  have hat : ∀ x : s.D, s.M.atom x ∈ K → M₀.atom (s.down x) = s.M.atom x := fun x hx =>
    hrel.eps x (hK1 _ hx).2.1
  refine ⟨?_, ?_, ?_⟩
  · rintro κ ⟨k0, hk0, rfl⟩
    -- same atom
    have same : ∀ x y : s.D, s.M.atom x = s.M.atom y → s.M.atom x ∈ K → k0 (s.down x) = k0 (s.down y) := by
      intro x y hxy hx
      have h1 := hat x hx
      have h2 := hat y (hxy ▸ hx)
      exact hTame k0 hk0 _ (h1 ▸ M₀.atom_mem _) (hK1 _ hx).2.2 _ _ h1 (h2.trans hxy.symm)
    -- along a bond
    have bond : ∀ x : s.D, s.M.atom x ∈ K → k0 (s.down (s.M.mate x)) = k0 (s.down x) := by
      intro x _
      rw [← hrel.mate x]; exact hmate k0 hk0 _
    have conn : ∀ u v, (eraseSet s.M (s.M.atoms \ K)).SameComponent u v →
        (u ∈ K ↔ v ∈ K) ∧ (u ∈ K → ∀ x y : s.D, s.M.atom x = u → s.M.atom y = v → k0 (s.down x) = k0 (s.down y)) := by
      intro u v huv
      induction huv with
      | rel u v hr =>
        obtain ⟨hadj, huK, hvK⟩ := (eraseSet_compl_adj_iff s.M K).1 hr
        obtain ⟨z, hz1, hz2⟩ := hadj
        refine ⟨iff_of_true huK hvK, fun hu x y hx hy => ?_⟩
        have e1 : k0 (s.down x) = k0 (s.down z) := same x z (hx.trans hz1.symm) (hx ▸ hu)
        have e2 : k0 (s.down (s.M.mate z)) = k0 (s.down y) := same _ y (hz2.trans hy.symm) (hz2 ▸ hvK)
        rw [e1, ← e2, bond z (hz1 ▸ hu)]
      | refl u =>
        exact ⟨Iff.rfl, fun hu x y hx hy => same x y (hx.trans hy.symm) (hx ▸ hu)⟩
      | symm u v _ ih =>
        refine ⟨ih.1.symm, fun hv x y hx hy => ?_⟩
        exact (ih.2 (ih.1.2 hv) y x hy hx).symm
      | trans u v w _ _ ih1 ih2 =>
        refine ⟨ih1.1.trans ih2.1, fun hu x y hx hy => ?_⟩
        have hv := ih1.1.1 hu
        obtain ⟨z, hz⟩ : ∃ z : s.D, s.M.atom z = v := by
          have := hK2 v hv
          obtain ⟨z, hz⟩ := Finset.card_pos.1 (lt_of_lt_of_le Nat.zero_lt_one this)
          exact ⟨z, by simpa [Molecule.dartsAt] using hz⟩
        exact (ih1.2 hu x z hx hz).trans (ih2.2 hv z y hz hy)
    intro x y hx hy
    exact (conn _ _ (hK3 _ hx _ hy)).2 hx x y rfl rfl
  · intro a ha hdeg
    have hae := hK1 a ha
    unfold effD at hdeg
    rw [deg_eq_of_eps han hae.1 hae.2.1] at hdeg
    have haM : a ∈ M₀.atoms := by
      have := han.mem a hae.1
      rwa [han.eps a hae.1 hae.2.1] at this
    obtain ⟨k, hk⟩ := hfix a haM hae.2.2 hdeg
    refine ⟨k, ?_⟩
    rintro κ ⟨k0, hk0, rfl⟩ x hx
    have hxa : s.M.atom x = a := by simpa [Molecule.dartsAt] using hx
    exact hk k0 hk0 (s.down x) ((hrel.eps x (by rw [hxa]; exact hae.2.1)).trans hxa)
  · intro a ha haB
    have hae := hK1 a ha
    rw [deg_eq_of_eps han hae.1 hae.2.1]
    exact hB₀ a haB


/-- From a weighted deviation to a plain one. -/
theorem isDev_of_wdev {A A' I : ℝ≥0∞} {c : ℝ} (hc : 0 < c) (h : ENNReal.ofReal c * A ≤ I * A') :
    IsDeviation A A' (ENNReal.ofReal c⁻¹ * I) := by
  unfold IsDeviation
  have h1 : ENNReal.ofReal c⁻¹ * ENNReal.ofReal c = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hc.le), inv_mul_cancel₀ hc.ne', ENNReal.ofReal_one]
  calc A = (ENNReal.ofReal c⁻¹ * ENNReal.ofReal c) * A := by rw [h1, one_mul]
    _ = ENNReal.ofReal c⁻¹ * (ENNReal.ofReal c * A) := by ring
    _ ≤ ENNReal.ofReal c⁻¹ * (I * A') := by gcongr
    _ = _ := by ring

theorem sum_filter_card_eq {𝒦 : Finset (Finset V)} (hdisj : (↑𝒦 : Set (Finset V)).PairwiseDisjoint id) {B : Finset V}
    (hB : B ⊆ 𝒦.biUnion id) : ∑ K ∈ 𝒦, (K.filter fun a => a ∈ B).card = B.card := by
  have e : B = 𝒦.biUnion (fun K => K.filter fun a => a ∈ B) := by
    ext a
    simp only [Finset.mem_biUnion, Finset.mem_filter, id]
    constructor
    · intro ha
      obtain ⟨K, hK, haK⟩ := Finset.mem_biUnion.1 (hB ha)
      exact ⟨K, hK, haK, ha⟩
    · rintro ⟨K, -, -, ha⟩; exact ha
  conv_rhs => rw [e]
  rw [Finset.card_biUnion]
  intro K hK K' hK' hne
  exact Finset.disjoint_filter_filter (hdisj hK hK' hne)

theorem terminal_familyLU (hd : 3 ≤ d) {γ η C₀ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η)
    (hη1 : η ≤ gam0 γ / 1000) (hC0 : 0 ≤ C₀) (hC0η : C₀ * η ^ 4 ≤ 1) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∀ C₁ δ : ℝ, 1 ≤ C₁ → 0 < δ → δ ≤ 1 →
    ∀ {V : Type v} [DecidableEq V] [Nonempty V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀]
    {M₀ : Molecule V D₀} {hf : HSt V D₀} {Tm : V → Prop} {A : Set (D₀ → (Fin d → ℤ))} {P : Finset V → ℝ} {B : Finset V},
      LadderHered M₀ P → (∀ S, 0 ≤ P S) → LCtx M₀ hf.s →
      (∀ k0 ∈ A, ∀ v ∈ M₀.atoms, Tm v → ∀ x y, M₀.atom x = v → M₀.atom y = v → k0 x = k0 y) →
      (∀ k0 ∈ A, ∀ x, k0 (M₀.mate x) = k0 x) →
      (∀ b ∈ B, M₀.deg b ≤ 2) →
      (∀ v ∈ M₀.atoms, Tm v → M₀.deg v + (if v ∈ B then 2 else 0) < 4 → ∃ k, ∀ k0 ∈ A, ∀ x, M₀.atom x = v → k0 x = k) →
      (∀ b ∈ B, b ∈ tameSet hf Tm) →
      (∀ x, hf.s.M.atom x ≠ hf.s.M.atom (hf.s.M.mate x)) → (∀ a ∈ hf.s.M.atoms, hf.s.M.deg a ≤ 4) →
      (∀ a ∈ hf.s.M.atoms, 1 ≤ hf.s.M.deg a) →
      ∃ (𝒦 : Finset (Finset V)) (j : Finset V → ℤ) (Rs : Finset V),
        𝒦.biUnion id = tameSet hf Tm ∧ Clusters hf.s.M 𝒦 ∧
        hf.s.M.circuitRank = (eraseSet hf.s.M (tameSet hf Tm)).circuitRank + ∑ K ∈ 𝒦, j K ∧
        (∑ K ∈ 𝒦, (K.filter fun a => a ∈ B).card = B.card) ∧
        CompRep (hf.op5 Tm).s.M Rs ∧
        ENNReal.ofReal (rankFactor d L γ δ C₁ (B.card : ℤ)) * QS L γ δ C₁ (0 : Mom d) P hf A ≤
          (∏ K ∈ 𝒦, ENNReal.ofReal (clusterRHSs L γ η C₀ K.card (eDart hf.s.M K) (j K + ((K.filter fun a => a ∈ B).card : ℤ)))) *
          ∏ a ∈ Rs, (compMol (hf.op5 Tm).s.M a).countA L γ δ C₁ (0 : Mom d)
            (projAdm (hf.op5 Tm).s.M (compP (hf.op5 Tm).s.M a) (adm5 (AdmS (fun k => k ∈ A) hf.s) hf.s.M (tameSet hf Tm))) P := by
  obtain ⟨L₀, hL₀, hfam⟩ := erase_family_deviation_wtU.{v, u} hd hγ0 hγ1 hη hη1 hC0 hC0η 4
  refine ⟨max L₀ (Real.exp 1), le_trans hL₀ (le_max_left _ _), fun L hL C₁ δ hC₁ hδ hδ1 V _ _ D₀ _ _ M₀ hf Tm A P B hP hP0 hc hTame hmate hB₀
    hfix hBt hnl hm4 hdpos => ?_⟩
  have hL' : L₀ ≤ L := le_trans (le_max_left _ _) hL
  have hLe : Real.exp 1 ≤ L := le_trans (le_max_right _ _) hL
  have hTsub : tameSet hf Tm ⊆ hf.s.M.atoms := fun v hv => (tameSet_mem.1 hv).1
  obtain ⟨𝒦, h1, hD⟩ := exists_famData hf.s.M (tameSet hf Tm) hTsub hnl hm4 (fun a ha => hdpos a (hTsub ha))
  obtain ⟨j, hrk, hdev⟩ := hfam V B 𝒦 hf.s.M hD
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hLe
  have hX : ∀ S, 0 ≤ Molecule.ladderWeight L γ δ (P S) := fun S => by
    have := hP0 S
    unfold Molecule.ladderWeight
    exact le_min (by positivity) (by positivity)
  have hKfacts : ∀ K ∈ 𝒦, (∀ a ∈ K, a ∈ hf.s.M.atoms ∧ hf.s.cls a = .eps ∧ Tm a) ∧ (∀ a ∈ K, 1 ≤ hf.s.M.deg a) ∧
      ∀ a ∈ K, ∀ b ∈ K, (eraseSet hf.s.M (hf.s.M.atoms \ K)).SameComponent a b := by
    intro K hK
    refine ⟨fun a ha => ?_, hD.dpos K hK, hD.int K hK⟩
    have : a ∈ tameSet hf Tm := by rw [← h1]; exact Finset.mem_biUnion.2 ⟨K, hK, ha⟩
    exact tameSet_mem.1 this
  have hFT : FamTameE hf.s.M B 𝒦 (AdmS (fun k => k ∈ A) hf.s) :=
    famTameE_state hc Tm A hTame hmate B hB₀ hfix 𝒦 hKfacts
  have hFL : FamLad L γ δ P 4 hf.s.M 𝒦 := famLad_state hP hc hLe hδ hP0 le_rfl hm4 𝒦
  have hdev' := hdev L hL' C₁ δ hC₁ hδ hδ1 (w := (0 : Mom d)) (AdmS (fun k => k ∈ A) hf.s) P hX hFT hFL
  rw [h1] at hdev' hrk
  have hkB : ∑ K ∈ 𝒦, (K.filter fun a => a ∈ B).card = B.card :=
    sum_filter_card_eq hD.cl.disj (by rw [h1]; exact fun b hb => hBt b hb)
  rw [hkB] at hdev'
  have hcpos : 0 < rankFactor d L γ δ C₁ (B.card : ℤ) := by
    unfold rankFactor
    have : 0 < C₁⁻¹ * δ ^ (1 / 2 : ℝ) := mul_pos (inv_pos.2 (by linarith)) (Real.rpow_pos_of_pos hδ _)
    positivity
  obtain ⟨Rs, hR, hbd⟩ := terminal_chain hf.s.M (tameSet hf Tm) L γ δ C₁ (0 : Mom d) hL0 hδ (by linarith)
    (AdmS (fun k => k ∈ A) hf.s) P hX (isDev_of_wdev hcpos hdev')
  refine ⟨𝒦, j, Rs, h1, hD.cl, hrk, hkB, hR, ?_⟩
  have h1' : ENNReal.ofReal (rankFactor d L γ δ C₁ (B.card : ℤ)) * ENNReal.ofReal (rankFactor d L γ δ C₁ (B.card : ℤ))⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hcpos.le, mul_inv_cancel₀ hcpos.ne', ENNReal.ofReal_one]
  show ENNReal.ofReal _ * hf.s.M.countA L γ δ C₁ (0 : Mom d) (AdmS (fun k => k ∈ A) hf.s) P ≤ _
  calc ENNReal.ofReal (rankFactor d L γ δ C₁ (B.card : ℤ)) * hf.s.M.countA L γ δ C₁ (0 : Mom d) (AdmS (fun k => k ∈ A) hf.s) P
      ≤ ENNReal.ofReal (rankFactor d L γ δ C₁ (B.card : ℤ)) * ((ENNReal.ofReal (rankFactor d L γ δ C₁ (B.card : ℤ))⁻¹ *
          (∏ K ∈ 𝒦, ENNReal.ofReal (clusterRHSs L γ η C₀ K.card (eDart hf.s.M K) (j K + ((K.filter fun a => a ∈ B).card : ℤ))))) *
          ∏ a ∈ Rs, (compMol (hf.op5 Tm).s.M a).countA L γ δ C₁ (0 : Mom d)
            (projAdm (hf.op5 Tm).s.M (compP (hf.op5 Tm).s.M a) (adm5 (AdmS (fun k => k ∈ A) hf.s) hf.s.M (tameSet hf Tm))) P) := by
        gcongr
        exact hbd
    _ = _ := by
        rw [← mul_assoc, ← mul_assoc, h1', one_mul]

end WaveTurbulence.FinalCountAsm
