/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.T1Summand

/-! # D2c-3 PROT-CUT: o104 Prop 7.4 (b) on `kernelProt` — the root trace of a type-1 couple

For a couple `LG` decoded by `type1 c Q₁ Q₂ Q₃` (`T1Data`, sub-couples `LG₁ LG₂ LG₃` with the layers of `LG`), upper
clocks `U` of its two trees, and the root of tree `j` designated at `σ ≤ U j` (`trFix j σ`):

    kernelProt LG H M (U ·) s (trFix j σ) k = c² Σ'_{y ∈ T1E} Mc(stars) ε_y ∫_{t1U} e^{πiB_y(σ−u)}
        Q₁(σ_·(u)) Q₂(σ_·(u)) Q₃(σ_·(u)) du          (**`T1Data.kernelProt_t1Trace`**)

* `u` is the time of the partner root `ρ' = (t1sw j, [])`, `t1U = {𝔏_{ρ'} < u < 𝔏_{ρ'} + 1, 0 < u, u < U (t1sw j)}`
  (o104 (b): `u ∈ (𝔏_{ρ'}, min(σ⁻, 𝔏_{ρ'}+1))`, `σ⁻ = U (t1sw j)`);
* `B_y = ζ_j δ L^{2γ} Ω(k + y₁/L, k + y₂/L, k + y₃/L, k)` (`t1Ph`): the linked phase of the pair `{ρ, ρ'}`;
* each tree of a sub-couple carries the clock of the root it hangs under (`t1Clock j σ u`: `σ` under `ρ`, `u`
  under `ρ'`); the outputs `k + y_i/L` are affine in `(k, y)`; `c = coupling d L γ δ`, the root factors
  `(iζ₀)(iζ₁) = 1`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

namespace T1Data

variable {c : MiniCplCode} {Q₁ Q₂ Q₃ : RegCpl} {LG LG₁ LG₂ LG₃ : LayeredGarden 2}
variable (h : T1Data c Q₁ Q₂ Q₃ LG.garden LG₁.garden LG₂.garden LG₃.garden)
include h

theorem zeta_t1' : LG.garden.zeta = LG₁.garden.zeta * (LG₂.garden.zeta * LG₃.garden.zeta) := by
  rw [h.zeta_t1, h.sig]
  have e : (Complex.I * (((1 : ℤˣ) : ℤ) : ℂ)) * (Complex.I * (((-1 : ℤˣ) : ℤ) : ℂ)) = 1 := by
    push_cast
    rw [mul_one, mul_neg_one, mul_neg, Complex.I_mul_I, neg_neg]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [e, one_mul]

section Leaves

variable {d : ℕ} (L : ℝ) (H : LeafProfiles 2 d)
  (hH : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom d, Summable fun n : Fin d → ℤ => |H ℓ.1 (k' + latticePoint L n)|)
include hH

theorem hH_A (k' : Mom d) : ∀ ℓ ∈ inputLeaves LG₁.garden,
    Summable fun n : Fin d → ℤ => |t1HA c H ℓ.1 (k' + latticePoint L n)| :=
  fun ℓ hℓ => hH (h.lfA ℓ) (h.lfA_input ℓ hℓ) k'

theorem hH_B (k' : Mom d) : ∀ ℓ ∈ inputLeaves LG₂.garden,
    Summable fun n : Fin d → ℤ => |t1HB H ℓ.1 (k' + latticePoint L n)| :=
  fun ℓ hℓ => hH (h.lfB ℓ) (h.lfB_input ℓ hℓ) k'

theorem hH_C (k' : Mom d) : ∀ ℓ ∈ inputLeaves LG₃.garden,
    Summable fun n : Fin d → ℤ => |t1HC c H ℓ.1 (k' + latticePoint L n)| :=
  fun ℓ hℓ => hH (h.lfC ℓ) (h.lfC_input ℓ hℓ) k'

end Leaves

/-- **o104 Prop 7.4 (b) on `kernelProt`: the root trace of a type-1 couple.** -/
theorem kernelProt_t1Trace (L γ δ : ℝ) {d : ℕ} (H : LeafProfiles 2 d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom d, Summable fun n : Fin d → ℤ => |H ℓ.1 (k' + latticePoint L n)|)
    (M : (GNode LG.garden.tree → Mom d) → ℂ) (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ)
    (M₁ : (GNode LG₁.garden.tree → Mom d) → ℂ) (M₂ : (GNode LG₂.garden.tree → Mom d) → ℂ)
    (M₃ : (GNode LG₃.garden.tree → Mom d) → ℂ) (hM : h.MultFactors M Mc M₁ M₂ M₃) (CM : ℝ)
    (hMc : ∀ A B, ‖Mc A B‖ ≤ CM) (hM₁ : ∀ K, ‖M₁ K‖ ≤ CM) (hM₂ : ∀ K, ‖M₂ K‖ ≤ CM) (hM₃ : ∀ K, ‖M₃ K‖ ≤ CM)
    (U : Fin 2 → ℝ) (s : ℝ) (j : Fin 2) (σ : ℝ) (hσ : σ ≤ U j)
    (hlA : ∀ z, LG₁.layer z = LG.layer (h.ιA z)) (hlB : ∀ z, LG₂.layer z = LG.layer (h.ιB z))
    (hlC : ∀ z, LG₃.layer z = LG.layer (h.ιC z)) (k : Mom d) :
    kernelProt L γ δ LG H M (fun b => U b.1.1) s (trFix j σ) k (fun _ => 0) 0 =
      (coupling d L γ δ : ℂ) ^ 2 *
        ∑' e : T1E d, Mc (t1Star c L k e 0) (t1Star c L k e 1) * (t1Eps c e : ℂ) *
          ∫ u in t1U LG (t1sw j) (U (t1sw j)), t1Ph (LG.garden.sig j) L γ δ k e σ u *
            (kernelProt L γ δ LG₁ (t1HA c H) M₁ (fun x => t1Clock j σ u x.1.1) 0 (fun _ => none)
                (k + latticePoint L e.1.1) (fun _ => 0) 0 *
              (kernelProt L γ δ LG₂ (t1HB H) M₂ (fun x => t1Clock j σ u (t1sw x.1.1)) 0 (fun _ => none)
                  (k + latticePoint L e.1.2.1) (fun _ => 0) 0 *
                kernelProt L γ δ LG₃ (t1HC c H) M₃ (fun x => t1Clock j σ u x.1.1) 0 (fun _ => none)
                  (k + latticePoint L e.1.2.2) (fun _ => 0) 0)) := by
  have hCM : 0 ≤ CM := (norm_nonneg _).trans (hM₁ 0)
  have hMb : ∀ K, ‖M K‖ ≤ CM * (CM * (CM * CM)) := by
    intro K
    rw [hM K, norm_mul, norm_mul, norm_mul]
    gcongr
    · exact hMc _ _
    · exact hM₁ _
    · exact hM₂ _
    · exact hM₃ _
  set Φ := (h.decEquiv d).trans ((Equiv.punitProd _).symm : _ ≃ Unit × _)
  rw [kernelProt_eq_tsum, ← Φ.symm.tsum_eq]
  have hΦ : ∀ q, h.decEquiv d (Φ.symm q) = q.2 := fun q => by
    simp only [Φ, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
    rfl
  have hS : ∀ q, protSummand L γ δ LG H M (fun b => U b.1.1) s (trFix j σ) k (Φ.symm q) =
      (Mc (t1Star c L k q.2.1 0) (t1Star c L k q.2.1 1) * (t1Eps c q.2.1 : ℂ)) *
        ∫ u in t1U LG (t1sw j) (U (t1sw j)), t1Ph (LG.garden.sig j) L γ δ k q.2.1 σ u *
          ((fun (_ : Unit) (_ : ℝ) => (1 : ℂ)) q.1 u *
            (protSummand L γ δ LG₁ (t1HA c H) M₁ (fun x => t1Clock j σ u x.1.1) 0 (fun _ => none)
                (k + latticePoint L q.2.1.1.1) q.2.2.1 *
              (protSummand L γ δ LG₂ (t1HB H) M₂ (fun x => t1Clock j σ u (t1sw x.1.1)) 0 (fun _ => none)
                  (k + latticePoint L q.2.1.1.2.1) q.2.2.2.1 *
                protSummand L γ δ LG₃ (t1HC c H) M₃ (fun x => t1Clock j σ u x.1.1) 0 (fun _ => none)
                  (k + latticePoint L q.2.1.1.2.2) q.2.2.2.2))) := by
    intro q
    have := h.summand_t1Trace (Φ.symm q) L k γ δ H M Mc M₁ M₂ M₃ hM U s j σ hσ hlA hlB hlC
    rw [hΦ] at this
    exact this
  have hsumG := summable_protSummand_norm L γ δ LG H M _ hMb (fun b => U b.1.1) s (trFix j σ) k
    (card_lone_le_of_plain h.plain) (fun ℓ hℓ => hH ℓ hℓ k)
  have hsum : Summable fun q => protSummand L γ δ LG H M (fun b => U b.1.1) s (trFix j σ) k (Φ.symm q) :=
    (Φ.symm.summable_iff).mpr hsumG.of_norm
  rw [tsum_cut_assembly (t1U LG (t1sw j) (U (t1sw j))) (volume_t1U_ne_top LG (t1sw j) (U (t1sw j)))
    (fun e => Mc (t1Star c L k e 0) (t1Star c L k e 1) * (t1Eps c e : ℂ))
    (fun e u => t1Ph (LG.garden.sig j) L γ δ k e σ u)
    (fun e u => (norm_t1Ph _ L γ δ k e σ u).le) (fun e => stronglyMeasurable_t1Ph _ L γ δ k e σ)
    (fun (_ : Unit) (_ : ℝ) => (1 : ℂ))
    (fun e i u => protSummand L γ δ LG₁ (t1HA c H) M₁ (fun x => t1Clock j σ u x.1.1) 0 (fun _ => none)
      (k + latticePoint L e.1.1) i)
    (fun e r u => protSummand L γ δ LG₂ (t1HB H) M₂ (fun x => t1Clock j σ u (t1sw x.1.1)) 0 (fun _ => none)
      (k + latticePoint L e.1.2.1) r)
    (fun e g u => protSummand L γ δ LG₃ (t1HC c H) M₃ (fun x => t1Clock j σ u x.1.1) 0 (fun _ => none)
      (k + latticePoint L e.1.2.2) g)
    (fun _ => 1)
    (fun e i => CM * leafMajorant L LG₁ (t1HA c H) (k + latticePoint L e.1.1) i)
    (fun e r => CM * leafMajorant L LG₂ (t1HB H) (k + latticePoint L e.1.2.1) r)
    (fun e g => CM * leafMajorant L LG₃ (t1HC c H) (k + latticePoint L e.1.2.2) g)
    (fun _ _ => by simp)
    (fun e i u => norm_protSummand_le L γ δ _ _ _ CM hM₁ _ _ _ _ i)
    (fun e r u => norm_protSummand_le L γ δ _ _ _ CM hM₂ _ _ _ _ r)
    (fun e g u => norm_protSummand_le L γ δ _ _ _ CM hM₃ _ _ _ _ g)
    (hasSum_fintype _).summable
    (fun e => (summable_leafMajorant L LG₁ (t1HA c H) (k + latticePoint L e.1.1) (fun _ => 0) 0
      (card_lone_le_of_plain h.dec₁.1.1) (h.hH_A L H hH _)).mul_left CM)
    (fun e => (summable_leafMajorant L LG₂ (t1HB H) (k + latticePoint L e.1.2.1) (fun _ => 0) 0
      (card_lone_le_of_plain h.dec₂.1.1) (h.hH_B L H hH _)).mul_left CM)
    (fun e => (summable_leafMajorant L LG₃ (t1HC c H) (k + latticePoint L e.1.2.2) (fun _ => 0) 0
      (card_lone_le_of_plain h.dec₃.1.1) (h.hH_C L H hH _)).mul_left CM)
    (fun _ => stronglyMeasurable_const)
    (fun e i => stronglyMeasurable_protSummand L γ δ LG₁ _ M₁ (fun u x => t1Clock j σ u x.1.1) (fun _ => 0) _ _
      (fun x => measurable_t1Clock j σ x.1.1) measurable_const i)
    (fun e r => stronglyMeasurable_protSummand L γ δ LG₂ _ M₂ (fun u x => t1Clock j σ u (t1sw x.1.1)) (fun _ => 0)
      _ _ (fun x => measurable_t1Clock j σ (t1sw x.1.1)) measurable_const r)
    (fun e g => stronglyMeasurable_protSummand L γ δ LG₃ _ M₃ (fun u x => t1Clock j σ u x.1.1) (fun _ => 0) _ _
      (fun x => measurable_t1Clock j σ x.1.1) measurable_const g)
    _ hS hsum]
  have h1 : (∑' _ : Unit, (1 : ℂ)) = 1 := by simp
  simp only [h1, one_mul, kernelProt_eq_tsum]
  set cc := (coupling d L γ δ : ℂ)
  set C₀ := cc ^ LG₁.garden.order * LG₁.garden.zeta *
    (cc ^ LG₂.garden.order * LG₂.garden.zeta * (cc ^ LG₃.garden.order * LG₃.garden.zeta))
  have hpull : ∀ e : T1E d,
      Mc (t1Star c L k e 0) (t1Star c L k e 1) * (t1Eps c e : ℂ) *
        ∫ u in t1U LG (t1sw j) (U (t1sw j)), t1Ph (LG.garden.sig j) L γ δ k e σ u *
          ((cc ^ LG₁.garden.order * LG₁.garden.zeta * ∑' i : GenDecoration LG₁.garden d (fun _ => 0) 0,
              protSummand L γ δ LG₁ (t1HA c H) M₁ (fun x => t1Clock j σ u x.1.1) 0 (fun _ => none)
                (k + latticePoint L e.1.1) i) *
            ((cc ^ LG₂.garden.order * LG₂.garden.zeta * ∑' r : GenDecoration LG₂.garden d (fun _ => 0) 0,
              protSummand L γ δ LG₂ (t1HB H) M₂ (fun x => t1Clock j σ u (t1sw x.1.1)) 0 (fun _ => none)
                (k + latticePoint L e.1.2.1) r) *
              (cc ^ LG₃.garden.order * LG₃.garden.zeta * ∑' g : GenDecoration LG₃.garden d (fun _ => 0) 0,
                protSummand L γ δ LG₃ (t1HC c H) M₃ (fun x => t1Clock j σ u x.1.1) 0 (fun _ => none)
                  (k + latticePoint L e.1.2.2) g))) =
        C₀ * (Mc (t1Star c L k e 0) (t1Star c L k e 1) * (t1Eps c e : ℂ) *
          ∫ u in t1U LG (t1sw j) (U (t1sw j)), t1Ph (LG.garden.sig j) L γ δ k e σ u *
            ((∑' i : GenDecoration LG₁.garden d (fun _ => 0) 0,
                protSummand L γ δ LG₁ (t1HA c H) M₁ (fun x => t1Clock j σ u x.1.1) 0 (fun _ => none)
                  (k + latticePoint L e.1.1) i) *
              ((∑' r : GenDecoration LG₂.garden d (fun _ => 0) 0,
                protSummand L γ δ LG₂ (t1HB H) M₂ (fun x => t1Clock j σ u (t1sw x.1.1)) 0 (fun _ => none)
                  (k + latticePoint L e.1.2.1) r) *
                ∑' g : GenDecoration LG₃.garden d (fun _ => 0) 0,
                  protSummand L γ δ LG₃ (t1HC c H) M₃ (fun x => t1Clock j σ u x.1.1) 0 (fun _ => none)
                    (k + latticePoint L e.1.2.2) g))) := by
    intro e
    have hu : ∀ u, t1Ph (LG.garden.sig j) L γ δ k e σ u *
          ((cc ^ LG₁.garden.order * LG₁.garden.zeta * ∑' i : GenDecoration LG₁.garden d (fun _ => 0) 0,
              protSummand L γ δ LG₁ (t1HA c H) M₁ (fun x => t1Clock j σ u x.1.1) 0 (fun _ => none)
                (k + latticePoint L e.1.1) i) *
            ((cc ^ LG₂.garden.order * LG₂.garden.zeta * ∑' r : GenDecoration LG₂.garden d (fun _ => 0) 0,
              protSummand L γ δ LG₂ (t1HB H) M₂ (fun x => t1Clock j σ u (t1sw x.1.1)) 0 (fun _ => none)
                (k + latticePoint L e.1.2.1) r) *
              (cc ^ LG₃.garden.order * LG₃.garden.zeta * ∑' g : GenDecoration LG₃.garden d (fun _ => 0) 0,
                protSummand L γ δ LG₃ (t1HC c H) M₃ (fun x => t1Clock j σ u x.1.1) 0 (fun _ => none)
                  (k + latticePoint L e.1.2.2) g))) =
        C₀ * (t1Ph (LG.garden.sig j) L γ δ k e σ u *
            ((∑' i : GenDecoration LG₁.garden d (fun _ => 0) 0,
                protSummand L γ δ LG₁ (t1HA c H) M₁ (fun x => t1Clock j σ u x.1.1) 0 (fun _ => none)
                  (k + latticePoint L e.1.1) i) *
              ((∑' r : GenDecoration LG₂.garden d (fun _ => 0) 0,
                protSummand L γ δ LG₂ (t1HB H) M₂ (fun x => t1Clock j σ u (t1sw x.1.1)) 0 (fun _ => none)
                  (k + latticePoint L e.1.2.1) r) *
                ∑' g : GenDecoration LG₃.garden d (fun _ => 0) 0,
                  protSummand L γ δ LG₃ (t1HC c H) M₃ (fun x => t1Clock j σ u x.1.1) 0 (fun _ => none)
                    (k + latticePoint L e.1.2.2) g))) := fun u => by ring
    simp_rw [hu, integral_const_mul]
    ring
  rw [tsum_congr hpull, tsum_mul_left, h.order_t1, h.zeta_t1', pow_add, pow_add, pow_add]
  ring

end T1Data

end WaveTurbulence.Flower.ProtCut
