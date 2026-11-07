/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmInputs
public import WaveTurbulence.Foundations.FinalCount.AsmPhaseQ
/-! **FINALCOUNT-ASSEMBLY, C: the potential bookkeeping of a cut.**  `vBeta`, `apProd` along `cutSt`, and the translation of the G3
step deviation `StepDev` (`excessprop1` (1)) into the potential form `stepRHS`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem cutSt_atoms (s : St.{u} V D₀) (v v₂ : V) (x₁ x₂ : s.D) (c₁ c₂ : Cls) :
    (s.cutSt v v₂ x₁ x₂ c₁ c₂).M.atoms = insert v₂ s.M.atoms := rfl

theorem cutSt_cls (s : St.{u} V D₀) (v v₂ : V) (x₁ x₂ : s.D) (c₁ c₂ : Cls) :
    (s.cutSt v v₂ x₁ x₂ c₁ c₂).cls = Function.update (Function.update s.cls v c₁) v₂ c₂ := rfl

/-- A cut of an `ε` atom into two `β` atoms adds two `β` atoms. -/
theorem vBeta_cutSt_beta (s : St.{u} V D₀) {v v₂ : V} {x₁ x₂ : s.D} (hc : s.M.IsCutData v v₂ x₁ x₂)
    (hε : s.cls v = .eps) : vBeta (s.cutSt v v₂ x₁ x₂ .beta .beta) = vBeta s + 2 := by
  obtain ⟨hv, hv₂, -⟩ := hc
  have hne : v₂ ≠ v := fun e => hv₂ (e ▸ hv)
  unfold vBeta
  rw [cutSt_atoms, cutSt_cls]
  have e : (insert v₂ s.M.atoms).filter (fun a => Function.update (Function.update s.cls v Cls.beta) v₂ Cls.beta a = .beta) =
      insert v₂ (insert v ((s.M.atoms.filter (fun a => s.cls a = .beta)))) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_insert]
    by_cases h1 : a = v₂
    · subst h1; simp
    · by_cases h2 : a = v
      · subst h2; simp [hv, h1]
      · simp [Function.update_of_ne h1, Function.update_of_ne h2, h1, h2]
  rw [e, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem]
  · intro hm; have := (Finset.mem_filter.1 hm).2; rw [hε] at this; cases this
  · simp only [Finset.mem_insert, Finset.mem_filter, not_or, not_and]
    exact ⟨hne, fun h => absurd h hv₂⟩

theorem apProd_cutSt_beta (s : St.{u} V D₀) (L γ η : ℝ) {v v₂ : V} {x₁ x₂ : s.D} (hc : s.M.IsCutData v v₂ x₁ x₂)
    (hε : s.cls v = .eps) : apProd L γ η (s.cutSt v v₂ x₁ x₂ .beta .beta) = apProd L γ η s := by
  obtain ⟨hv, hv₂, -⟩ := hc
  unfold apProd
  rw [cutSt_atoms, cutSt_cls, Finset.prod_insert hv₂]
  simp only [Function.update_self, apFactor, one_mul]
  rw [← Finset.mul_prod_erase _ _ hv, ← Finset.mul_prod_erase _ _ hv]
  have hne : ∀ a ∈ s.M.atoms.erase v, Function.update (Function.update s.cls v Cls.beta) v₂ Cls.beta a = s.cls a := by
    intro a ha
    have h1 : a ≠ v₂ := fun e => hv₂ (e ▸ Finset.mem_of_mem_erase ha)
    rw [Function.update_of_ne h1, Function.update_of_ne (Finset.ne_of_mem_erase ha)]
  rw [Finset.prod_congr rfl fun a ha => by rw [hne a ha]]
  have h1 : v ≠ v₂ := fun e => hv₂ (e ▸ hv)
  rw [Function.update_of_ne h1, Function.update_self, hε]

/-- Positivity of the `α` labels of a state (an invariant of the run). -/
def ApPos (s : St.{u} V D₀) : Prop := ∀ a ∈ s.M.atoms, ∀ R kp, s.cls a = .alpha R kp → 0 < R

theorem apFactor_pos {L γ η : ℝ} (hL : 0 < L) {c : Cls} (h : ∀ R kp, c = .alpha R kp → 0 < R) : 0 < apFactor L γ η c := by
  cases c with
  | alpha R kp => simp only [apFactor]; exact mul_pos (Real.rpow_pos_of_pos hL _) (h R kp rfl)
  | _ => simp [apFactor]

theorem apProd_pos {L γ η : ℝ} (hL : 0 < L) {s : St.{u} V D₀} (hs : ApPos s) : 0 < apProd L γ η s :=
  Finset.prod_pos fun a ha => apFactor_pos hL (hs a ha)

theorem stepRHS_beta {L γ η : ℝ} (hL : 0 < L) {h h' : HSt V D₀} (hAp : 0 < apProd L γ η h.s)
    (hF : h'.s.M.numComponents = h.s.M.numComponents + 1) (hB : vBeta h'.s = vBeta h.s + 2)
    (hA : apProd L γ η h'.s = apProd L γ η h.s) : stepRHS L γ η h h' = excessRHS L γ η [] 1 2 := by
  unfold stepRHS excessRHS
  rw [hF, hB, hA, div_self hAp.ne']
  simp only [List.map_nil, List.prod_nil, mul_one, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_sub_cancel_left, Int.cast_one, Int.cast_ofNat]

/-- The explicit constant of a `β`-cut (`excessprop1`, G3 `UStep4.excess`). -/
noncomputable def cBeta (η : ℝ) (c : ℕ) : ℝ := 10 * (((c + 4 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (c + 4)

theorem UStep4.dev_pot {L γ η δ C₁ : ℝ} {w : Mom d} {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} (H : TriReal d L γ η δ C₁)
    {Rn : ℕ} {h h' : HSt V D₀} (hs : UStep4 L w Adm0 h h') (hI : Inv Rn h.s) (hAp : 0 < apProd L γ η h.s)
    (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S)
    (hPinh : ∀ S' ∈ h'.s.M.maximalLadders, ∀ S ∈ h.s.M.maximalLadders, S' ⊆ S → P S' = P S) (c : ℕ)
    (hn : (h.s.M.atoms.card : ℝ) ≤ Real.log L ^ c) :
    IsDeviation (h.s.M.countA L γ δ C₁ w (AdmS Adm0 h.s) P) (h'.s.M.countA L γ δ C₁ w (AdmS Adm0 h'.s) P)
      (ENNReal.ofReal (cBeta η c * stepRHS L γ η h h')) := by
  have hL : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) H.hL
  cases hs with
  | cut v v₂ x₁ x₂ hc hε hβ hnz h3 =>
    have hM : ∀ a ∈ h.s.M.atoms, h.s.M.deg a ≤ 4 := fun a ha => deg_le_four _ (hI.bounds a ha)
    have hF : (h.cut4Post v v₂ x₁ x₂).s.M.numComponents = h.s.M.numComponents + 1 :=
      numComponents_cut_of_not_same h.s.M hc (fun hs => hβ ((isAlphaCut_iff h.s.M hc).2 hs))
    have hB : vBeta (h.cut4Post v v₂ x₁ x₂).s = vBeta h.s + 2 := vBeta_cutSt_beta h.s hc hε
    have hA : apProd L γ η (h.cut4Post v v₂ x₁ x₂).s = apProd L γ η h.s := apProd_cutSt_beta h.s L γ η hc hε
    rw [stepRHS_beta hL hAp hF hB hA]
    exact betaCut_excess h.s.M hc (hM v hc.1) hM hβ L γ η δ C₁ H.hη (triReal_eta_lt_one H) c hn w (AdmS Adm0 h.s) P
        H.hL H.hδ0 (by linarith [H.hC]) hP0 hPinh

end WaveTurbulence.FinalCountAsm
