/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.T1Dom

/-! # D2c-2 PROT-CUT: the root trace of a type-1 couple at one decoration (o104 Prop 7.4 (b), time level)

The root `ρ = (j, [])` of a type-1 couple designated at `σ ≤ U j` (`trFix j σ`); its linked partner
`ρ' = (t1sw j, [])` is integrated (`u = τ_{ρ'}`). **`T1Data.protTime_t1Trace`**:

`protTime (trFix j σ) = ∫_{u ∈ t1U} e^{πiζ₀δL^{2γ}Ω₀ σ₀(u)} e^{πiζ₁δL^{2γ}Ω₁ σ₁(u)} · Q₁ Q₂ Q₃ (clocks σ_·(u))`,

`σ_t(u) = σ` for `t = j` and `u` otherwise, `t1U = {𝔏_{ρ'} < u < 𝔏_{ρ'} + 1, 0 < u, u < U (t1sw j)}` (o104 (b):
`u ∈ (𝔏_{ρ'}, min(σ⁻, 𝔏_{ρ'}+1))`, `σ⁻ = U (t1sw j)`); each sub-couple tree carries the clock of the root it hangs
under. The two root phases combine into `e^{πiB(σ-u)}` by the linked cancellation (the decoration level). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

/-- The range of the partner time. -/
def t1U (LG : LayeredGarden 2) (t : Fin 2) (T : ℝ) : Set ℝ :=
  {u | (layerAt LG (t, []) : ℝ) < u ∧ u < layerAt LG (t, []) + 1 ∧ 0 < u ∧ u < T}

theorem measurableSet_t1U (LG : LayeredGarden 2) (t : Fin 2) (T : ℝ) : MeasurableSet (t1U LG t T) := by
  unfold t1U
  simp only [Set.ofPred_and]
  exact (measurableSet_lt measurable_const measurable_id).inter
    ((measurableSet_lt measurable_id measurable_const).inter
      ((measurableSet_lt measurable_const measurable_id).inter (measurableSet_lt measurable_id measurable_const)))

/-- The clocks of the two roots: `σ` at the designated root, `u` at its partner. -/
def t1Clock (j : Fin 2) (σ u : ℝ) (t : Fin 2) : ℝ := if t = j then σ else u

theorem t1sw_ne (j : Fin 2) : t1sw j ≠ j := by fin_cases j <;> decide

theorem trFix_rt_ne {G : Garden 2} (j : Fin 2) (σ : ℝ) (b : GBranch G.tree) (hb : b.1.2 ≠ []) :
    trFix j σ b = none := by
  unfold trFix; rw [if_neg (fun h => hb h.2)]

namespace T1Data

variable {c : MiniCplCode} {Q₁ Q₂ Q₃ : RegCpl} {LG LG₁ LG₂ LG₃ : LayeredGarden 2}
variable (h : T1Data c Q₁ Q₂ Q₃ LG.garden LG₁.garden LG₂.garden LG₃.garden)
include h

theorem βA_path_ne (x : GBranch LG₁.garden.tree) : (h.βA x).1.2 ≠ [] := by simp [βA, t1A]
theorem βB_path_ne (x : GBranch LG₂.garden.tree) : (h.βB x).1.2 ≠ [] := by simp [βB, t1B]
theorem βC_path_ne (x : GBranch LG₃.garden.tree) : (h.βC x).1.2 ≠ [] := by simp [βC, t1C]

theorem pinSet_t1 (U : Fin 2 → ℝ) (s : ℝ) (j : Fin 2) (σ : ℝ) :
    pinSet LG (fun b => U b.1.1) s (trFix j σ) (h.rt (t1sw j)) = t1U LG (t1sw j) (U (t1sw j)) := by
  ext u
  have hl : (LG.layer (h.rt (t1sw j)).toNode : ℝ) = layerAt LG (t1sw j, []) := by
    rw [← layerAt_node]; rfl
  constructor
  · rintro ⟨h1, h2, h3, h4, -⟩
    rw [hl] at h1 h2
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by rw [hl]; exact h1, by rw [hl]; exact h2, h3, h4, fun b' hb' v hv => ?_, fun b hb v hv => ?_,
      fun hl' => absurd hl' (not_loneParent_of_plain h.plain _)⟩
    · obtain ⟨-, i, hi⟩ := hb'
      rw [trFix_rt_ne j σ b' (by rw [hi]; simp)] at hv
      simp at hv
    · obtain ⟨-, i, hi⟩ := hb
      have : ([] : Path) = b.1.2 ++ [i] := hi
      simp at this

/-- **The root trace of a type-1 couple, one decoration** (o104 Prop 7.4 (b), time level). -/
theorem protTime_t1Trace (L γ δ : ℝ) {d : ℕ} (U : Fin 2 → ℝ) (s : ℝ) (j : Fin 2) (σ : ℝ) (hσ : σ ≤ U j)
    (hlA : ∀ z, LG₁.layer z = LG.layer (h.ιA z)) (hlB : ∀ z, LG₂.layer z = LG.layer (h.ιB z))
    (hlC : ∀ z, LG₃.layer z = LG.layer (h.ιC z)) (K : GNode LG.garden.tree → Mom d) :
    protTime L γ δ LG (fun b => U b.1.1) s (trFix j σ) K =
      ∫ u in t1U LG (t1sw j) (U (t1sw j)),
        Complex.exp ((Real.pi * ((LG.garden.sig 0 : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
            omegaNode LG.garden K (h.rt 0) * t1Clock j σ u 0 : ℝ) * Complex.I) *
          Complex.exp ((Real.pi * ((LG.garden.sig 1 : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
            omegaNode LG.garden K (h.rt 1) * t1Clock j σ u 1 : ℝ) * Complex.I) *
          (protTime L γ δ LG₁ (fun x => t1Clock j σ u x.1.1) 0 (fun _ => none) (K ∘ h.ιA) *
            (protTime L γ δ LG₂ (fun x => t1Clock j σ u (t1sw x.1.1)) 0 (fun _ => none) (K ∘ h.ιB) *
              protTime L γ δ LG₃ (fun x => t1Clock j σ u x.1.1) 0 (fun _ => none) (K ∘ h.ιC))) := by
  have hfree : trFix j σ (h.rt (t1sw j)) = none := by
    unfold trFix; rw [if_neg (fun h' => t1sw_ne j h'.1)]
  rw [protTime_pin L γ δ LG (fun b => U b.1.1) s (trFix j σ) K (h.rt (t1sw j)) hfree, h.pinSet_t1 U s j σ,
    ← integral_indicator (measurableSet_t1U LG (t1sw j) (U (t1sw j)))]
  congr 1
  funext u
  by_cases hu : u ∈ t1U LG (t1sw j) (U (t1sw j))
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
    set fix' := Function.update (trFix j σ) (h.rt (t1sw j)) (some u) with hfix'
    have hroot : ∀ t, fix' (h.rt t) = some (t1Clock j σ u t) := by
      intro t
      by_cases ht : t = j
      · subst ht
        have hne : h.rt t ≠ h.rt (t1sw t) := fun he =>
          t1sw_ne t (congrArg (fun b : GBranch LG.garden.tree => b.1.1) he).symm
        rw [hfix', Function.update_of_ne hne]
        unfold trFix t1Clock
        rw [if_pos ⟨rfl, rfl⟩, if_pos rfl]
      · have ht' : t = t1sw j := by fin_cases t <;> fin_cases j <;> simp_all [t1sw]
        subst ht'
        rw [hfix', Function.update_self]
        unfold t1Clock
        rw [if_neg ht]
    have hσU : ∀ t, t1Clock j σ u t ≤ U t := by
      intro t
      unfold t1Clock
      by_cases ht : t = j
      · rw [if_pos ht, ht]; exact hσ
      · rw [if_neg ht]
        have ht' : t = t1sw j := by fin_cases t <;> fin_cases j <;> simp_all [t1sw]
        rw [ht']; exact hu.2.2.2.le
    have hnA : (fun x => fix' (h.βA x)) = fun _ => none := funext fun x => by
      rw [hfix', Function.update_of_ne (fun he => h.βA_path_ne x (by rw [he]; rfl)),
        trFix_rt_ne j σ _ (h.βA_path_ne x)]
    have hnB : (fun x => fix' (h.βB x)) = fun _ => none := funext fun x => by
      rw [hfix', Function.update_of_ne (fun he => h.βB_path_ne x (by rw [he]; rfl)),
        trFix_rt_ne j σ _ (h.βB_path_ne x)]
    have hnC : (fun x => fix' (h.βC x)) = fun _ => none := funext fun x => by
      rw [hfix', Function.update_of_ne (fun he => h.βC_path_ne x (by rw [he]; rfl)),
        trFix_rt_ne j σ _ (h.βC_path_ne x)]
    have e := protTime_t1 h L γ δ U s fix' (t1Clock j σ u) hroot hσU hlA hlB hlC
      (fun x v hv => by rw [congrFun hnA x] at hv; simp at hv)
      (fun x v hv => by rw [congrFun hnB x] at hv; simp at hv)
      (fun x v hv => by rw [congrFun hnC x] at hv; simp at hv) K
    rw [hnA, hnB, hnC] at e
    exact e
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu]

end T1Data

end WaveTurbulence.Flower.ProtCut
