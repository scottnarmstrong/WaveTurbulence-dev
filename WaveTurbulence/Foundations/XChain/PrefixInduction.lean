/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.PrefixNextAnsatz
/-! Finite induction of the complete source ansatz, preserving the proved internal invariants. -/
@[expose] public section
namespace WaveTurbulence.Induct
open MeasureTheory Set
universe u

noncomputable def extendPrefix {P : WTParams} (H : InductContext.{u} P)
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : (Fin P.d → ℤ) → Ω → ℂ) (hG : IsGaussianData μ g)
    {p : ℕ} (hp : p < P.D) (S : AnsatzPrefixData P μ g p) (T : PrefixExtension S) :
    AnsatzPrefixData P μ g (p + 1) where
  a := T.a
  Fev := T.nextFev
  R := T.nextR
  E := T.nextE
  Et := T.nextEt
  ansatz := by
    intro q hq
    by_cases heq : q = p + 1
    · subst q
      exact prefix_next_ansatz H μ g hG hp S T
    · have hqp : q ≤ p := by omega
      exact ansatz_congr_history P μ g S.a T.a S.Fev T.nextFev S.R T.nextR S.E T.nextE S.Et T.nextEt
        q (S.ansatz q hqp) (fun ω t ht => T.history ω t (ht.trans (by exact_mod_cast hqp)))
        (fun r hr => T.nextFev_old (hr.trans hqp)) (fun r hr => T.nextR_old (hr.trans hqp))
        (T.nextE_old hqp) (T.nextEt_old hqp)
  rapid := by
    intro ω hω
    rw [T.nextFev_old (Nat.zero_le p)] at hω
    exact S.rapid ω hω
  future_zero := fun q hq => T.nextR_future hq
  l1_moments := by
    intro q hq r hr
    by_cases heq : q = p + 1
    · subst q
      rw [T.nextFev_new]
      simpa only [Nat.cast_add, Nat.cast_one] using
        T.l1_moments ((p : ℝ) + 1) ⟨by linarith, le_rfl⟩ r hr
    · have hqp : q ≤ p := by omega
      have he (ω : Ω) : T.a ω q = S.a ω q := T.history ω q (by exact_mod_cast hqp)
      simpa only [he, T.nextFev_old hqp] using S.l1_moments q hqp r hr

theorem propansatz_body_of_context {P : WTParams} (H : InductContext.{u} P) : PropansatzBody.{u} P := by
  intro Ω _ μ _ g hG
  have hex : ∀ p, p ≤ P.D → Nonempty (AnsatzPrefixData P μ g p) := by
    intro p
    induction p with
    | zero =>
      intro _
      exact ⟨basePrefixData P μ g hG (zero_lt_one.trans_le H.L_ge_one) H.delta_pos.le
        H.initial_nonneg H.wke.2.1⟩
    | succ p ih =>
      intro hp
      obtain ⟨S⟩ := ih (by omega)
      obtain ⟨T⟩ := exists_prefix_extension P H.fixedpoint H.dimension H.L_ge_exp_two H.initial_nonneg
        μ g hG (by omega : p < P.D) S
      exact ⟨extendPrefix H μ g hG (by omega) S T⟩
  obtain ⟨S⟩ := hex P.D le_rfl
  exact ⟨S.a, S.Fev, S.R, S.E, S.Et, S.ansatz⟩

end WaveTurbulence.Induct
