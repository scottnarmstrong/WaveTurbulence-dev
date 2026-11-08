/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.T1Leaves

/-! # D2c-3 PROT-CUT: the root trace of a type-1 couple at one decoration (o104 Prop 7.4 (b))

At a decoration `κ ↔ (y, κ₁, κ₂, κ₃)` (`T1Data.decEquiv`), with output `k`:
* the stars of the two roots are `t1Star c L k y t` (the root momentum `k`, the children `k + y_·/L` in the order of
  the slots of root `t`), the `ε` factors of the roots are `t1Eps c y`;
* the two root frequencies are equal (`Ω` is symmetric in its first and third arguments) and the root signs are
  opposite, so the two root phases combine into the linked phase `t1Ph ζ_j … σ u = e^{πiB(σ-u)}`,
  `B = ζ_j δ L^{2γ} Ω` (`phase_t1`, the linked cancellation `ζ₀Ω₀ + ζ₁Ω₁ = 0`);
* **`T1Data.summand_t1Trace`**: the summand of `kernelProt` with the root of tree `j` designated at `σ` is
  `Mc(stars) ε_y ∫_{t1U} e^{πiB(σ−u)} · Q₁ Q₂ Q₃(clocks σ_·(u))` at the shifted outputs `k + y_i/L`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

variable {d : ℕ}

/-- The value at the child `i` of root `t` (slots of `Q₁`, `Q₂`, `Q₃`). -/
def t1Val (c : MiniCplCode) {V : Type*} (y : V × V × V) (t : Fin 2) (i : Fin 3) : V :=
  if i = slotA c t then y.1 else if i = 1 then y.2.1 else y.2.2

/-- **The star momenta of root `t`** for the exceptional data `e` (output `k`). -/
def t1Star (c : MiniCplCode) (L : ℝ) (k : Mom d) (e : T1E d) (t : Fin 2) : Fin 4 → Mom d :=
  Fin.cases k fun i => k + latticePoint L (t1Val c e.1 t i)

/-- The `ε` factors of the two roots. -/
def t1Eps (c : MiniCplCode) (e : T1E d) : ℝ :=
  epsCoef (t1Val c e.1 0 0) (t1Val c e.1 0 1) (t1Val c e.1 0 2) *
    epsCoef (t1Val c e.1 1 0) (t1Val c e.1 1 1) (t1Val c e.1 1 2)

/-- The resonance factor of the roots, times `δ L^{2γ}`. -/
def t1Freq (L γ δ : ℝ) (k : Mom d) (e : T1E d) : ℝ :=
  δ * L ^ (2 * γ) * resFactor (k + latticePoint L e.1.1) (k + latticePoint L e.1.2.1) (k + latticePoint L e.1.2.2) k

/-- **The linked phase** `e^{πiB(σ−u)}`, `B = ζ δ L^{2γ} Ω` (`ζ` the sign of the designated root). -/
def t1Ph (ζ : ℤˣ) (L γ δ : ℝ) (k : Mom d) (e : T1E d) (σ u : ℝ) : ℂ :=
  Complex.exp (((Real.pi * ((ζ : ℤ) : ℝ) * t1Freq L γ δ k e * (σ - u) : ℝ) : ℂ) * Complex.I)

theorem norm_t1Ph (ζ : ℤˣ) (L γ δ : ℝ) (k : Mom d) (e : T1E d) (σ u : ℝ) : ‖t1Ph ζ L γ δ k e σ u‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem stronglyMeasurable_t1Ph (ζ : ℤˣ) (L γ δ : ℝ) (k : Mom d) (e : T1E d) (σ : ℝ) :
    StronglyMeasurable fun u => t1Ph ζ L γ δ k e σ u := by
  unfold t1Ph
  refine Continuous.stronglyMeasurable ?_
  fun_prop

theorem measurable_t1Clock (j : Fin 2) (σ : ℝ) (t : Fin 2) : Measurable fun u => t1Clock j σ u t := by
  unfold t1Clock; split_ifs
  · exact measurable_const
  · exact measurable_id

theorem volume_t1U_ne_top (LG : LayeredGarden 2) (t : Fin 2) (T : ℝ) : volume (t1U LG t T) ≠ ⊤ := by
  refine ne_top_of_le_ne_top (b := volume (Ioo (layerAt LG (t, []) : ℝ) (layerAt LG (t, []) + 1))) ?_
    (measure_mono fun u hu => ⟨hu.1, hu.2.1⟩)
  rw [Real.volume_Ioo]
  exact ENNReal.ofReal_ne_top

/-- The profiles of the three sub-couples. -/
def t1HA (c : MiniCplCode) (H : LeafProfiles 2 d) : LeafProfiles 2 d := fun a => H (t1A c a)
def t1HB (H : LeafProfiles 2 d) : LeafProfiles 2 d := fun a => H (t1B a)
def t1HC (c : MiniCplCode) (H : LeafProfiles 2 d) : LeafProfiles 2 d := fun a => H (t1C c a)

namespace T1Data

variable {c : MiniCplCode} {Q₁ Q₂ Q₃ : RegCpl} {LG LG₁ LG₂ LG₃ : LayeredGarden 2}
variable (h : T1Data c Q₁ Q₂ Q₃ LG.garden LG₁.garden LG₂.garden LG₃.garden)
include h

/-- **The multiplier factors at the two roots**: `M K = Mc (star of ρ₀) (star of ρ₁) · M₁ · M₂ · M₃`. -/
def MultFactors (M : (GNode LG.garden.tree → Mom d) → ℂ) (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ)
    (M₁ : (GNode LG₁.garden.tree → Mom d) → ℂ) (M₂ : (GNode LG₂.garden.tree → Mom d) → ℂ)
    (M₃ : (GNode LG₃.garden.tree → Mom d) → ℂ) : Prop :=
  ∀ K : GNode LG.garden.tree → Mom d,
    M K = Mc (bstar K (h.rt 0)) (bstar K (h.rt 1)) * (M₁ (K ∘ h.ιA) * (M₂ (K ∘ h.ιB) * M₃ (K ∘ h.ιC)))

variable (κ : GenDecoration LG.garden d (fun _ => 0) 0)

theorem κ_child (t : Fin 2) (i : Fin 3) : κ.1 ((h.rt t).child i) = t1Val c (h.decEquiv d κ).1.1 t i := by
  rw [← extend_node κ.1, decEquiv_fst]
  show extend κ.1 (t, [i]) = _
  unfold t1Val
  rcases slot_cases_t1 c t i with rfl | rfl | rfl
  · rw [if_pos rfl]; exact h.extA κ.2.1 t
  · rw [if_neg (fun e => slotA_ne_one c t e.symm), if_pos rfl]
    have e : ((t, [(1 : Fin 3)]) : Fin 2 × Path) = t1B (t1sw t, []) := by simp [t1B, t1sw_t1sw]
    rw [e]; exact h.extB κ.2.1 _
  · rw [if_neg (slotC_ne_slotA c t), if_neg (slotC_ne_one c t)]; exact h.extC κ.2.1 t

theorem κ_rt (t : Fin 2) : κ.1 (h.rt t).toNode = 0 := κ.2.2.1 t

variable (L : ℝ) (k : Mom d)

theorem coset_child (t : Fin 2) (i : Fin 3) :
    cosetDecoration LG.garden L k κ.1 ((h.rt t).child i) = k + latticePoint L (t1Val c (h.decEquiv d κ).1.1 t i) := by
  show k + latticePoint L (κ.1 ((h.rt t).child i)) = _
  rw [h.κ_child κ t i]

theorem coset_rt (t : Fin 2) : cosetDecoration LG.garden L k κ.1 (h.rt t).toNode = k := by
  show k + latticePoint L (κ.1 (h.rt t).toNode) = k
  rw [h.κ_rt κ t, latticePoint_zero, add_zero]

theorem bstar_rt (t : Fin 2) :
    bstar (cosetDecoration LG.garden L k κ.1) (h.rt t) = t1Star c L k (h.decEquiv d κ).1 t := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact h.coset_rt κ L k t
  · exact h.coset_child κ L k t j

theorem coset_A : cosetDecoration LG.garden L k κ.1 ∘ h.ιA =
    cosetDecoration LG₁.garden L (k + latticePoint L (h.decEquiv d κ).1.1.1) ((h.decEquiv d κ).2.1).1 := by
  rw [← cosetDecoration_add_const]
  funext z
  show k + latticePoint L (κ.1 (h.ιA z)) = k + latticePoint L ((κ.1 (h.ιA z) -
    extend κ.1 (t1A c (0, []))) + extend κ.1 (t1A c (0, [])))
  rw [sub_add_cancel]

theorem coset_B : cosetDecoration LG.garden L k κ.1 ∘ h.ιB =
    cosetDecoration LG₂.garden L (k + latticePoint L (h.decEquiv d κ).1.1.2.1) ((h.decEquiv d κ).2.2.1).1 := by
  rw [← cosetDecoration_add_const]
  funext z
  show k + latticePoint L (κ.1 (h.ιB z)) = k + latticePoint L ((κ.1 (h.ιB z) -
    extend κ.1 (t1B (0, []))) + extend κ.1 (t1B (0, [])))
  rw [sub_add_cancel]

theorem coset_C : cosetDecoration LG.garden L k κ.1 ∘ h.ιC =
    cosetDecoration LG₃.garden L (k + latticePoint L (h.decEquiv d κ).1.1.2.2) ((h.decEquiv d κ).2.2.2).1 := by
  rw [← cosetDecoration_add_const]
  funext z
  show k + latticePoint L (κ.1 (h.ιC z)) = k + latticePoint L ((κ.1 (h.ιC z) -
    extend κ.1 (t1C c (0, []))) + extend κ.1 (t1C c (0, [])))
  rw [sub_add_cancel]

omit L k in
theorem epsDec_t1' : epsDec LG.garden κ.1 = t1Eps c (h.decEquiv d κ).1 *
    (epsDec LG₁.garden ((h.decEquiv d κ).2.1).1 *
      (epsDec LG₂.garden ((h.decEquiv d κ).2.2.1).1 * epsDec LG₃.garden ((h.decEquiv d κ).2.2.2).1)) := by
  rw [h.epsDec_t1]
  have hA : epsDec LG₁.garden (κ.1 ∘ h.ιA) = epsDec LG₁.garden ((h.decEquiv d κ).2.1).1 := by
    symm
    rw [← epsDec_add_const LG₁.garden _ (extend κ.1 (t1A c (0, [])))]
    congr 1
    funext z
    show κ.1 (h.ιA z) - extend κ.1 (t1A c (0, [])) + extend κ.1 (t1A c (0, [])) = _
    rw [sub_add_cancel]; rfl
  have hB : epsDec LG₂.garden (κ.1 ∘ h.ιB) = epsDec LG₂.garden ((h.decEquiv d κ).2.2.1).1 := by
    symm
    rw [← epsDec_add_const LG₂.garden _ (extend κ.1 (t1B (0, [])))]
    congr 1
    funext z
    show κ.1 (h.ιB z) - extend κ.1 (t1B (0, [])) + extend κ.1 (t1B (0, [])) = _
    rw [sub_add_cancel]; rfl
  have hC : epsDec LG₃.garden (κ.1 ∘ h.ιC) = epsDec LG₃.garden ((h.decEquiv d κ).2.2.2).1 := by
    symm
    rw [← epsDec_add_const LG₃.garden _ (extend κ.1 (t1C c (0, [])))]
    congr 1
    funext z
    show κ.1 (h.ιC z) - extend κ.1 (t1C c (0, [])) + extend κ.1 (t1C c (0, [])) = _
    rw [sub_add_cancel]; rfl
  rw [hA, hB, hC, h.κ_child κ 0 0, h.κ_child κ 0 1, h.κ_child κ 0 2, h.κ_child κ 1 0, h.κ_child κ 1 1,
    h.κ_child κ 1 2]
  rfl

theorem prodH_t1 (H : LeafProfiles 2 d) :
    ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k κ.1 ℓ.toNode) : ℂ) =
      (∏ ℓ ∈ inputLeaves LG₁.garden, (t1HA c H ℓ.1 (cosetDecoration LG₁.garden L
          (k + latticePoint L (h.decEquiv d κ).1.1.1) ((h.decEquiv d κ).2.1).1 ℓ.toNode) : ℂ)) *
        ((∏ ℓ ∈ inputLeaves LG₂.garden, (t1HB H ℓ.1 (cosetDecoration LG₂.garden L
            (k + latticePoint L (h.decEquiv d κ).1.1.2.1) ((h.decEquiv d κ).2.2.1).1 ℓ.toNode) : ℂ)) *
          ∏ ℓ ∈ inputLeaves LG₃.garden, (t1HC c H ℓ.1 (cosetDecoration LG₃.garden L
            (k + latticePoint L (h.decEquiv d κ).1.1.2.2) ((h.decEquiv d κ).2.2.2).1 ℓ.toNode) : ℂ)) := by
  set f : Fin 2 × Path → ℂ := fun z => (H z (k + latticePoint L (extend κ.1 z)) : ℂ) with hf
  have e0 : ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k κ.1 ℓ.toNode) : ℂ) =
      ∏ ℓ ∈ inputLeaves LG.garden, f ℓ.1 := by
    refine Finset.prod_congr rfl fun ℓ _ => ?_
    rw [hf]
    simp only
    rw [show ℓ.1 = ℓ.toNode.1 from rfl, extend_node]
    rfl
  rw [e0, h.prod_inputLeaves_t1 f]
  have hcA := h.coset_A κ L k
  have hcB := h.coset_B κ L k
  have hcC := h.coset_C κ L k
  congr 1
  · refine Finset.prod_congr rfl fun ℓ _ => ?_
    rw [hf]
    simp only
    rw [show t1A c ℓ.1 = (h.ιA ℓ.toNode).1 from rfl, extend_node, ← congrFun hcA ℓ.toNode]
    rfl
  congr 1
  · refine Finset.prod_congr rfl fun ℓ _ => ?_
    rw [hf]
    simp only
    rw [show t1B ℓ.1 = (h.ιB ℓ.toNode).1 from rfl, extend_node, ← congrFun hcB ℓ.toNode]
    rfl
  · refine Finset.prod_congr rfl fun ℓ _ => ?_
    rw [hf]
    simp only
    rw [show t1C c ℓ.1 = (h.ιC ℓ.toNode).1 from rfl, extend_node, ← congrFun hcC ℓ.toNode]
    rfl

omit h in
theorem resFactor_swap13 (a b c' k' : Mom d) : resFactor c' b a k' = resFactor a b c' k' := by
  unfold resFactor; ring

theorem omega_rt (t : Fin 2) :
    omegaNode LG.garden (cosetDecoration LG.garden L k κ.1) (h.rt t) =
      resFactor (k + latticePoint L (h.decEquiv d κ).1.1.1) (k + latticePoint L (h.decEquiv d κ).1.1.2.1)
        (k + latticePoint L (h.decEquiv d κ).1.1.2.2) k := by
  unfold omegaNode
  rw [h.coset_child κ L k t 0, h.coset_child κ L k t 1, h.coset_child κ L k t 2, h.coset_rt κ L k t]
  unfold t1Val
  fin_cases c <;> fin_cases t <;> simp [slotA, MiniCplCode.partner, resFactor_swap13]

/-- **The linked cancellation at the two roots**: the two root phases are `e^{πiB(σ−u)}`. -/
theorem phase_t1 (γ δ : ℝ) (j : Fin 2) (σ u : ℝ) :
    Complex.exp ((Real.pi * ((LG.garden.sig 0 : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
        omegaNode LG.garden (cosetDecoration LG.garden L k κ.1) (h.rt 0) * t1Clock j σ u 0 : ℝ) * Complex.I) *
      Complex.exp ((Real.pi * ((LG.garden.sig 1 : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
        omegaNode LG.garden (cosetDecoration LG.garden L k κ.1) (h.rt 1) * t1Clock j σ u 1 : ℝ) * Complex.I) =
      t1Ph (LG.garden.sig j) L γ δ k (h.decEquiv d κ).1 σ u := by
  rw [h.omega_rt κ L k 0, h.omega_rt κ L k 1, h.sig]
  unfold t1Ph t1Freq t1Clock
  rw [← Complex.exp_add, ← add_mul, ← Complex.ofReal_add]
  congr 3
  fin_cases j <;> simp <;> ring

/-! ### The summand -/

/-- **The root trace of a type-1 couple at one decoration** (o104 Prop 7.4 (b)). -/
theorem summand_t1Trace (γ δ : ℝ) (H : LeafProfiles 2 d) (M : (GNode LG.garden.tree → Mom d) → ℂ)
    (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ) (M₁ : (GNode LG₁.garden.tree → Mom d) → ℂ)
    (M₂ : (GNode LG₂.garden.tree → Mom d) → ℂ) (M₃ : (GNode LG₃.garden.tree → Mom d) → ℂ)
    (hM : h.MultFactors M Mc M₁ M₂ M₃) (U : Fin 2 → ℝ) (s : ℝ) (j : Fin 2) (σ : ℝ) (hσ : σ ≤ U j)
    (hlA : ∀ z, LG₁.layer z = LG.layer (h.ιA z)) (hlB : ∀ z, LG₂.layer z = LG.layer (h.ιB z))
    (hlC : ∀ z, LG₃.layer z = LG.layer (h.ιC z)) :
    protSummand L γ δ LG H M (fun b => U b.1.1) s (trFix j σ) k κ =
      (Mc (t1Star c L k (h.decEquiv d κ).1 0) (t1Star c L k (h.decEquiv d κ).1 1) *
          (t1Eps c (h.decEquiv d κ).1 : ℂ)) *
        ∫ u in t1U LG (t1sw j) (U (t1sw j)), t1Ph (LG.garden.sig j) L γ δ k (h.decEquiv d κ).1 σ u *
          ((1 : ℂ) * (protSummand L γ δ LG₁ (t1HA c H) M₁ (fun x => t1Clock j σ u x.1.1) 0 (fun _ => none)
              (k + latticePoint L (h.decEquiv d κ).1.1.1) (h.decEquiv d κ).2.1 *
            (protSummand L γ δ LG₂ (t1HB H) M₂ (fun x => t1Clock j σ u (t1sw x.1.1)) 0 (fun _ => none)
                (k + latticePoint L (h.decEquiv d κ).1.1.2.1) (h.decEquiv d κ).2.2.1 *
              protSummand L γ δ LG₃ (t1HC c H) M₃ (fun x => t1Clock j σ u x.1.1) 0 (fun _ => none)
                (k + latticePoint L (h.decEquiv d κ).1.1.2.2) (h.decEquiv d κ).2.2.2))) := by
  unfold protSummand
  rw [hM, h.bstar_rt κ L k 0, h.bstar_rt κ L k 1, h.coset_A κ L k, h.coset_B κ L k, h.coset_C κ L k,
    h.epsDec_t1' κ, h.protTime_t1Trace L γ δ U s j σ hσ hlA hlB hlC, h.prodH_t1 κ L k H]
  simp only [h.coset_A κ L k, h.coset_B κ L k, h.coset_C κ L k, h.phase_t1 κ L k γ δ j σ]
  rw [show ∀ (a b c J : ℂ), a * (b * J * c) = (a * b * c) * J from fun a b c J => by ring]
  conv_lhs => rw [← integral_const_mul]
  conv_rhs => rw [← integral_const_mul]
  congr 1
  funext u
  push_cast
  ring

end T1Data

end WaveTurbulence.Flower.ProtCut
