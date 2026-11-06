/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Stage1TypeBound
public import WaveTurbulence.Foundations.Spine.EvalConcrete
/-! AMEND6' (design P*): the Stage 1 gate applied to ONE evaluation `evalV g` (a one-element pair-type family
with sign 1 and bound `B₀`): `‖V g (base)‖ <= B₀^(N+R) * (gate gain)`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open MeasureTheory Set Finset
open scoped Classical ENNReal

/-- The one-element pair-type family `g` with bound `b`. -/
noncomputable def oneFamily (P : WTParams) {w : ℕ} (g : TProf P.d w) (b : NNReal) : TypeFamily P w where
  ι := Unit
  fin := inferInstanceAs (Fintype Unit)
  sign _ := 1
  h _ := g
  b _ := b
  sign_abs_le _ := by simp

theorem univ_unit_eq (inst : Fintype Unit) : (@Finset.univ Unit inst) = {()} := by
  ext x; simp

theorem evalV_gate_bound (C₀ : ℕ) (P : WTParams) (hs : PieceSmall P)
    (hcoarse : CoarseSplicedAt P) (hfourier : LadderFourierAt P) (hcount : FinalCountAt P)
    (habs : FinalAbsorptionAt (6 * C₀) P) (hlog : 1 ≤ Real.log P.L) (hd : 1 ≤ P.d)
    (hgate : Stage1ReductionAt C₀ P)
    {p R N : ℕ} (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1)) (hN1 : 1 ≤ N)
    (hN : N ≤ P.N (p + 1) ^ 4) (A : Finset (LayeredGarden (2 * R)))
    (hA : ∀ LG ∈ A, Stage1Carries P p N LG) (hcl : TwistClosed p A) (tt : Fin (2 * R) → ℝ)
    (htt : ∀ j, tt j ∈ Icc (p : ℝ) (p + 1)) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hplain : ∀ LG ∈ A, LG.garden.IsPlain)
    (g : TProf P.d (2 * R)) (B₀ : NNReal) (hB₀ : 0 < (B₀ : ℝ))
    (hg : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (g q j j') ≤ ENNReal.ofReal (B₀ : ℝ)) :
    ‖evalV P A tt roots g base‖ ≤ (B₀ : ℝ) ^ (N + R) *
      (P.δ ^ (8 * P.ν * N) * (P.L ^ (-P.η ^ 7) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 70)))) := by
  have hcard : ∀ LG ∈ A, (inputLeaves LG.garden).card = N + R := by
    intro LG hLG
    have h1 := twice_card_inputLeaves LG.garden (hplain LG hLG)
    have h2 : LG.garden.order = N := (hA LG hLG).2.2.1
    omega
  have := stage1_type_bound C₀ P hs hcoarse hfourier hcount habs hlog hd hgate hp hR hRmax hN1 hN A hA hcl tt htt
    base roots (oneFamily P g B₀) ((B₀ : ℝ) ^ (N + R)) (pow_pos hB₀ _) (fun i q j j' hq => hg q hq j j')
    (fun LG hLG => by
      have : Unique (oneFamily P g B₀).ι := inferInstanceAs (Unique Unit)
      rw [TypeFamilyD.size_eq]
      change (∑ _i : (oneFamily P g B₀).ι, (B₀ : ℝ) ^ (inputLeaves LG.garden).card) ≤ _
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_unique, one_smul, hcard LG hLG])
  convert this using 2
  unfold evalV
  refine Finset.sum_congr rfl fun LG _ => ?_
  have : ∀ LG : LayeredGarden (2 * R), Unique ((oneFamily P g B₀).toLF.ι LG) := fun _ => inferInstanceAs (Unique Unit)
  rw [LeafFamily.value, Finset.univ_unique, Finset.sum_singleton]
  change _ = ((1 : ℝ) : ℂ) * kernelLeaves P.L P.γ P.δ LG (typeProfiles LG g) (fun b => tt b.1.1) 0 base roots 0
  simp

end WaveTurbulence.LGSpine
