/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.PairTime

/-! # D2c PROT-CUT: the closing-pair time domain and free-time integral

* `protDom_pair`: with `𝔫_a` designated at `u ≤ T` and `𝔫_b` at `v ≤ T`, the time domain of a closing pair
  (upper clock `T`) is the product of the domains of the interior (upper clock `u`, lone-port time `v`) and of the
  two side couples (upper clock `u` at `𝔫_a`, `v` at `𝔫_b`), for designation-consistent times, provided every
  designated time of a piece is at most its upper clock.
* **`protTime_pair`**: the free-time integral is the product of the two boundary phases and the three free-time
  integrals of the pieces. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

namespace PairData

variable {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain}
variable {LG LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2}
variable (h : PairData m Qr Qg inner LG.garden LGi.garden LGr.garden LGg.garden)
include h

theorem cupR_le {u v T : ℝ} (hu : u ≤ T) (hv : v ≤ T) (j : Fin 2) :
    cupR m inner (LG.garden.sig 0) u v j ≤ T := by unfold cupR; split_ifs <;> assumption

theorem cupG_le {u v T : ℝ} (hu : u ≤ T) (hv : v ≤ T) (j : Fin 2) :
    cupG m inner (LG.garden.sig 0) u v j ≤ T := by unfold cupG; split_ifs <;> assumption

/-- The time domain of a closing pair restricts to the pieces (no upper-clock comparison needed). -/
theorem protDom_pair_mp (T s u v : ℝ) (fix : GBranch LG.garden.tree → Option ℝ)
    (hfa : fix h.rootB = some u) (hfb : fix h.bB = some v)
    (hli : ∀ z, LGi.layer z = LG.layer (h.ιi z)) (hlr : ∀ z, LGr.layer z = LG.layer (h.ιr z))
    (hlg : ∀ z, LGg.layer z = LG.layer (h.ιg z))
    (hpi : ∀ x σ, fix (h.βi x) = some σ → σ ≤ u)
    (hpr : ∀ y σ, fix (h.βr y) = some σ → σ ≤ cupR m inner (LG.garden.sig 0) u v y.1.1)
    (hpg : ∀ y σ, fix (h.βg y) = some σ → σ ≤ cupG m inner (LG.garden.sig 0) u v y.1.1)
    (τ : GBranch LG.garden.tree → ℝ) (hτ : ∀ b σ, fix b = some σ → τ b = σ) :
    τ ∈ protDom LG (fun _ => T) s fix →
      (fun x => τ (h.βi x)) ∈ protDom LGi (fun _ => u) v (fun x => fix (h.βi x)) ∧
      ((fun y => τ (h.βr y)) ∈ protDom LGr (fun y => cupR m inner (LG.garden.sig 0) u v y.1.1) 0
          (fun y => fix (h.βr y)) ∧
        (fun y => τ (h.βg y)) ∈ protDom LGg (fun y => cupG m inner (LG.garden.sig 0) u v y.1.1) 0
          (fun y => fix (h.βg y))) := by
  have hτa : τ h.rootB = u := hτ _ _ hfa
  have hτb : τ h.bB = v := hτ _ _ hfb
  have hplainR := h.decR.1.1
  have hplainG := h.decG.1.1
  rintro ⟨hD, hL⟩
  -- upper clocks inside the pieces
  have hupI : ∀ x, fix (h.βi x) = none → τ (h.βi x) < u := by
    have := lt_up_of_chain (fun x => fix (h.βi x)) (fun x => τ (h.βi x)) (fun _ => u)
      (fun x x' hc hor => (hD (h.βi x)).2 (h.βi x') ((h.βi_child_iff x x').mpr hc) hor)
      (fun x hx hf => by
        have := (hD h.rootB).2 (h.βi x) (h.βi_child_rootB x hx) (Or.inl hf)
        rwa [hτa] at this)
      (fun x σ hf => ⟨hτ _ _ hf, hpi x σ hf⟩)
    exact this
  have hupR : ∀ y, fix (h.βr y) = none → τ (h.βr y) < cupR m inner (LG.garden.sig 0) u v y.1.1 := by
    have := lt_up_of_chain (fun y => fix (h.βr y)) (fun y => τ (h.βr y))
      (cupR m inner (LG.garden.sig 0) u v)
      (fun y y' hc hor => (hD (h.βr y)).2 (h.βr y') ((h.βr_child_iff y y').mpr hc) hor)
      (fun y hy hf => by
        rcases rBase_cases m inner (LG.garden.sig 0) y.1.1 with ht | ht
        · have := (hD h.rootB).2 (h.βr y) (h.βr_child_root y hy ht) (Or.inl hf)
          rw [hτa] at this
          show _ < _
          rw [cupR_top ht]; exact this
        · have := (hD h.bB).2 (h.βr y) (h.βr_child_bB y hy ht) (Or.inl hf)
          rw [hτb] at this
          show _ < _
          rw [cupR_bot ht]; exact this)
      (fun y σ hf => ⟨hτ _ _ hf, hpr y σ hf⟩)
    exact this
  have hupG : ∀ y, fix (h.βg y) = none → τ (h.βg y) < cupG m inner (LG.garden.sig 0) u v y.1.1 := by
    have := lt_up_of_chain (fun y => fix (h.βg y)) (fun y => τ (h.βg y))
      (cupG m inner (LG.garden.sig 0) u v)
      (fun y y' hc hor => (hD (h.βg y)).2 (h.βg y') ((h.βg_child_iff y y').mpr hc) hor)
      (fun y hy hf => by
        rcases gBase_cases m inner (LG.garden.sig 0) y.1.1 with ht | ht
        · have := (hD h.rootB).2 (h.βg y) (h.βg_child_root y hy ht) (Or.inl hf)
          rw [hτa] at this
          show _ < _
          rw [cupG_top ht]; exact this
        · have := (hD h.bB).2 (h.βg y) (h.βg_child_bB y hy ht) (Or.inl hf)
          rw [hτb] at this
          show _ < _
          rw [cupG_bot ht]; exact this)
      (fun y σ hf => ⟨hτ _ _ hf, hpg y σ hf⟩)
    exact this
  refine ⟨⟨fun x => ⟨fun hx => ?_, fun x' hx' hor => ?_⟩, fun x hx hf => ?_⟩,
    ⟨fun y => ⟨fun hy => ?_, fun y' hy' hor => ?_⟩, fun y hy _ => ?_⟩,
    ⟨fun y => ⟨fun hy => ?_, fun y' hy' hor => ?_⟩, fun y hy _ => ?_⟩⟩
  · obtain ⟨a1, a2, a3, -⟩ := (hD (h.βi x)).1 hx
    rw [hli]
    exact ⟨a1, a2, a3, hupI x hx⟩
  · exact (hD (h.βi x)).2 (h.βi x') ((h.βi_child_iff x x').mpr hx') hor
  · have := (hD (h.βi x)).2 h.bB (h.bB_child_βi x hx) (Or.inr hf)
    rwa [hτb] at this
  · obtain ⟨a1, a2, a3, -⟩ := (hD (h.βr y)).1 hy
    rw [hlr]
    exact ⟨a1, a2, a3, hupR y hy⟩
  · exact (hD (h.βr y)).2 (h.βr y') ((h.βr_child_iff y y').mpr hy') hor
  · exact absurd hy (not_loneParent_of_plain hplainR y)
  · obtain ⟨a1, a2, a3, -⟩ := (hD (h.βg y)).1 hy
    rw [hlg]
    exact ⟨a1, a2, a3, hupG y hy⟩
  · exact (hD (h.βg y)).2 (h.βg y') ((h.βg_child_iff y y').mpr hy') hor
  · exact absurd hy (not_loneParent_of_plain hplainG y)

/-- **The time domain of a closing pair with both partners designated.** -/
theorem protDom_pair (T s u v : ℝ) (fix : GBranch LG.garden.tree → Option ℝ)
    (hfa : fix h.rootB = some u) (hfb : fix h.bB = some v)
    (hli : ∀ z, LGi.layer z = LG.layer (h.ιi z)) (hlr : ∀ z, LGr.layer z = LG.layer (h.ιr z))
    (hlg : ∀ z, LGg.layer z = LG.layer (h.ιg z)) (huT : u ≤ T) (hvT : v ≤ T)
    (hpi : ∀ x σ, fix (h.βi x) = some σ → σ ≤ u)
    (hpr : ∀ y σ, fix (h.βr y) = some σ → σ ≤ cupR m inner (LG.garden.sig 0) u v y.1.1)
    (hpg : ∀ y σ, fix (h.βg y) = some σ → σ ≤ cupG m inner (LG.garden.sig 0) u v y.1.1)
    (τ : GBranch LG.garden.tree → ℝ) (hτ : ∀ b σ, fix b = some σ → τ b = σ) :
    τ ∈ protDom LG (fun _ => T) s fix ↔
      (fun x => τ (h.βi x)) ∈ protDom LGi (fun _ => u) v (fun x => fix (h.βi x)) ∧
      ((fun y => τ (h.βr y)) ∈ protDom LGr (fun y => cupR m inner (LG.garden.sig 0) u v y.1.1) 0
          (fun y => fix (h.βr y)) ∧
        (fun y => τ (h.βg y)) ∈ protDom LGg (fun y => cupG m inner (LG.garden.sig 0) u v y.1.1) 0
          (fun y => fix (h.βg y))) := by
  have hτa : τ h.rootB = u := hτ _ _ hfa
  have hτb : τ h.bB = v := hτ _ _ hfb
  have hplainR := h.decR.1.1
  have hplainG := h.decG.1.1
  constructor
  · exact h.protDom_pair_mp T s u v fix hfa hfb hli hlr hlg hpi hpr hpg τ hτ
  · rintro ⟨⟨hDi, hLi⟩, ⟨hDr, -⟩, ⟨hDg, -⟩⟩
    refine ⟨fun b => ⟨fun hb => ?_, fun b' hb' hor => ?_⟩, fun b hb hf => ?_⟩
    · obtain ⟨z, rfl⟩ := h.pairBranch_surjective b
      rcases z with j | x | y | y
      · fin_cases j
        · exact absurd hb (by simp [pairBranch, hfa])
        · exact absurd hb (by simp [pairBranch, hfb])
      · obtain ⟨a1, a2, a3, a4⟩ := (hDi x).1 hb
        rw [hli] at a1 a2
        exact ⟨a1, a2, a3, a4.trans_le huT⟩
      · obtain ⟨a1, a2, a3, a4⟩ := (hDr y).1 hb
        rw [hlr] at a1 a2
        exact ⟨a1, a2, a3, a4.trans_le (h.cupR_le huT hvT _)⟩
      · obtain ⟨a1, a2, a3, a4⟩ := (hDg y).1 hb
        rw [hlg] at a1 a2
        exact ⟨a1, a2, a3, a4.trans_le (h.cupG_le huT hvT _)⟩
    · rcases h.child_cases b b' hb' with ⟨rfl, hcase⟩ | ⟨x', rfl, hcase⟩ | ⟨y', rfl, hcase⟩ |
        ⟨y', rfl, hcase⟩
      · rcases hcase with rfl | ⟨x, hx, rfl⟩
        · rw [hfa, hfb] at hor; simp at hor
        · rw [hfb] at hor
          have hf : fix (h.βi x) = none := by simpa using hor
          have := hLi x hx hf
          rwa [hτb]
      · rcases hcase with ⟨hx, rfl⟩ | ⟨x, hc, rfl⟩
        · rw [hfa] at hor
          have hf : fix (h.βi x') = none := by simpa using hor
          have := ((hDi x').1 hf).2.2.2
          rwa [hτa]
        · exact (hDi x).2 x' hc hor
      · rcases hcase with ⟨hy, ht, rfl⟩ | ⟨hy, ht, rfl⟩ | ⟨y, hc, rfl⟩
        · rw [hfa] at hor
          have hf : fix (h.βr y') = none := by simpa using hor
          have := ((hDr y').1 hf).2.2.2
          simp only at this
          rw [cupR_top ht] at this
          rwa [hτa]
        · rw [hfb] at hor
          have hf : fix (h.βr y') = none := by simpa using hor
          have := ((hDr y').1 hf).2.2.2
          simp only at this
          rw [cupR_bot ht] at this
          rwa [hτb]
        · exact (hDr y).2 y' hc hor
      · rcases hcase with ⟨hy, ht, rfl⟩ | ⟨hy, ht, rfl⟩ | ⟨y, hc, rfl⟩
        · rw [hfa] at hor
          have hf : fix (h.βg y') = none := by simpa using hor
          have := ((hDg y').1 hf).2.2.2
          simp only at this
          rw [cupG_top ht] at this
          rwa [hτa]
        · rw [hfb] at hor
          have hf : fix (h.βg y') = none := by simpa using hor
          have := ((hDg y').1 hf).2.2.2
          simp only at this
          rw [cupG_bot ht] at this
          rwa [hτb]
        · exact (hDg y).2 y' hc hor
    · rw [h.isLoneParent_G b hb, hfb] at hf
      simp at hf

/-! ### The free branches -/

/-- The free branches of the three pieces, placed in the closing pair. -/
def freePair (fix : GBranch LG.garden.tree → Option ℝ) :
    {x : GBranch LGi.garden.tree // fix (h.βi x) = none} ⊕
      ({y : GBranch LGr.garden.tree // fix (h.βr y) = none} ⊕
        {y : GBranch LGg.garden.tree // fix (h.βg y) = none}) →
      {b : GBranch LG.garden.tree // fix b = none}
  | .inl x => ⟨h.βi x.1, x.2⟩
  | .inr (.inl y) => ⟨h.βr y.1, y.2⟩
  | .inr (.inr y) => ⟨h.βg y.1, y.2⟩

theorem freePair_val (fix : GBranch LG.garden.tree → Option ℝ) (z) :
    (h.freePair fix z).1 = h.pairBranch (match z with
      | .inl x => .inr (.inl x.1) | .inr (.inl y) => .inr (.inr (.inl y.1))
      | .inr (.inr y) => .inr (.inr (.inr y.1))) := by
  rcases z with x | y | y <;> rfl

theorem freePair_bijective (fix : GBranch LG.garden.tree → Option ℝ) (hfa : fix h.rootB ≠ none)
    (hfb : fix h.bB ≠ none) : Function.Bijective (h.freePair fix) := by
  constructor
  · intro z z' he
    have := congrArg Subtype.val he
    rw [h.freePair_val, h.freePair_val] at this
    have := h.pairBranch_injective this
    rcases z with x | y | y <;> rcases z' with x' | y' | y' <;> simp at this
    · exact congrArg Sum.inl (Subtype.ext this)
    · exact congrArg (fun t => Sum.inr (Sum.inl t)) (Subtype.ext this)
    · exact congrArg (fun t => Sum.inr (Sum.inr t)) (Subtype.ext this)
  · rintro ⟨b, hb⟩
    obtain ⟨z, rfl⟩ := h.pairBranch_surjective b
    rcases z with j | x | y | y
    · fin_cases j
      · exact absurd hb hfa
      · exact absurd hb hfb
    · exact ⟨.inl ⟨x, hb⟩, rfl⟩
    · exact ⟨.inr (.inl ⟨y, hb⟩), rfl⟩
    · exact ⟨.inr (.inr ⟨y, hb⟩), rfl⟩

/-- **The free-time integral of a closing pair with both partners designated.** -/
theorem protTime_pair (L γ δ : ℝ) {d : ℕ} (T s u v : ℝ) (fix : GBranch LG.garden.tree → Option ℝ)
    (hfa : fix h.rootB = some u) (hfb : fix h.bB = some v)
    (hli : ∀ z, LGi.layer z = LG.layer (h.ιi z)) (hlr : ∀ z, LGr.layer z = LG.layer (h.ιr z))
    (hlg : ∀ z, LGg.layer z = LG.layer (h.ιg z)) (huT : u ≤ T) (hvT : v ≤ T)
    (hpi : ∀ x σ, fix (h.βi x) = some σ → σ ≤ u)
    (hpr : ∀ y σ, fix (h.βr y) = some σ → σ ≤ cupR m inner (LG.garden.sig 0) u v y.1.1)
    (hpg : ∀ y σ, fix (h.βg y) = some σ → σ ≤ cupG m inner (LG.garden.sig 0) u v y.1.1)
    (K : GNode LG.garden.tree → Mom d) :
    protTime L γ δ LG (fun _ => T) s fix K =
      Complex.exp ((Real.pi * ((LG.garden.sign h.rootB.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
          omegaNode LG.garden K h.rootB * u : ℝ) * Complex.I) *
        Complex.exp ((Real.pi * ((LG.garden.sign h.bB.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
          omegaNode LG.garden K h.bB * v : ℝ) * Complex.I) *
        (protTime L γ δ LGi (fun _ => u) v (fun x => fix (h.βi x)) (K ∘ h.ιi) *
          (protTime L γ δ LGr (fun y => cupR m inner (LG.garden.sig 0) u v y.1.1) 0
              (fun y => fix (h.βr y)) (K ∘ h.ιr) *
            protTime L γ δ LGg (fun y => cupG m inner (LG.garden.sig 0) u v y.1.1) 0
              (fun y => fix (h.βg y)) (K ∘ h.ιg))) := by
  set c : ℂ := Complex.exp ((Real.pi * ((LG.garden.sign h.rootB.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
          omegaNode LG.garden K h.rootB * u : ℝ) * Complex.I) *
        Complex.exp ((Real.pi * ((LG.garden.sign h.bB.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
          omegaNode LG.garden K h.bB * v : ℝ) * Complex.I) with hc
  have hbij := h.freePair_bijective fix (by rw [hfa]; simp) (by rw [hfb]; simp)
  let e := (Equiv.ofBijective _ hbij).symm
  have he : ∀ z, e (h.freePair fix z) = z := fun z => (Equiv.ofBijective _ hbij).symm_apply_apply z
  set Ii := protIntegrand L γ δ LGi (fun _ => u) v (fun x => fix (h.βi x)) (K ∘ h.ιi)
  set Ir := protIntegrand L γ δ LGr (fun y => cupR m inner (LG.garden.sig 0) u v y.1.1) 0
    (fun y => fix (h.βr y)) (K ∘ h.ιr)
  set Ig := protIntegrand L γ δ LGg (fun y => cupG m inner (LG.garden.sig 0) u v y.1.1) 0
    (fun y => fix (h.βg y)) (K ∘ h.ιg)
  rw [protTime_split L γ δ LG (fun _ => T) s fix K e (fun σ => c * Ii σ)
    (fun σ => Ir (fun a => σ (Sum.inl a)) * Ig (fun a => σ (Sum.inr a))) ?_]
  · rw [integral_const_mul, integral_sum_mul, mul_assoc]
    rfl
  intro σ
  set τ := LG.garden.extendFix fix (fun b => σ (e b))
  have hτ : ∀ b σ', fix b = some σ' → τ b = σ' := fun b σ' hf => extendFix_some _ _ _ hf
  have ti : (fun x => τ (h.βi x)) = LGi.garden.extendFix (fun x => fix (h.βi x)) (fun a => σ (Sum.inl a)) := by
    funext x
    cases hx : fix (h.βi x) with
    | some w => rw [hτ _ _ hx, extendFix_some LGi.garden (fun x => fix (h.βi x)) _ hx]
    | none =>
      rw [extendFix_free _ _ _ ⟨x, hx⟩]
      show LG.garden.extendFix fix _ (h.freePair fix (.inl ⟨x, hx⟩)).1 = _
      rw [extendFix_free _ _ _ (h.freePair fix (.inl ⟨x, hx⟩)), he]
  have tr : (fun y => τ (h.βr y)) = LGr.garden.extendFix (fun y => fix (h.βr y))
      (fun a => σ (Sum.inr (Sum.inl a))) := by
    funext y
    cases hy : fix (h.βr y) with
    | some w => rw [hτ _ _ hy, extendFix_some LGr.garden (fun y => fix (h.βr y)) _ hy]
    | none =>
      rw [extendFix_free _ _ _ ⟨y, hy⟩]
      show LG.garden.extendFix fix _ (h.freePair fix (.inr (.inl ⟨y, hy⟩))).1 = _
      rw [extendFix_free _ _ _ (h.freePair fix (.inr (.inl ⟨y, hy⟩))), he]
  have tg : (fun y => τ (h.βg y)) = LGg.garden.extendFix (fun y => fix (h.βg y))
      (fun a => σ (Sum.inr (Sum.inr a))) := by
    funext y
    cases hy : fix (h.βg y) with
    | some w => rw [hτ _ _ hy, extendFix_some LGg.garden (fun y => fix (h.βg y)) _ hy]
    | none =>
      rw [extendFix_free _ _ _ ⟨y, hy⟩]
      show LG.garden.extendFix fix _ (h.freePair fix (.inr (.inr ⟨y, hy⟩))).1 = _
      rw [extendFix_free _ _ _ (h.freePair fix (.inr (.inr ⟨y, hy⟩))), he]
  have hD := h.protDom_pair T s u v fix hfa hfb hli hlr hlg huT hvT hpi hpr hpg τ hτ
  have hph := h.phaseProd_pair L γ δ K τ
  rw [hτ _ _ hfa, hτ _ _ hfb] at hph
  simp only [Ii, Ir, Ig, protIntegrand]
  change (protDom LG (fun _ => T) s fix).indicator (phaseProd L γ δ LG.garden K) τ = _
  rw [← ti, ← tr, ← tg]
  by_cases h1 : (fun x => τ (h.βi x)) ∈ protDom LGi (fun _ => u) v (fun x => fix (h.βi x)) <;>
    by_cases h2 : (fun y => τ (h.βr y)) ∈ protDom LGr
      (fun y : GBranch LGr.garden.tree => cupR m inner (LG.garden.sig 0) u v y.1.1) 0
      (fun y => fix (h.βr y)) <;>
    by_cases h3 : (fun y => τ (h.βg y)) ∈ protDom LGg
      (fun y : GBranch LGg.garden.tree => cupG m inner (LG.garden.sig 0) u v y.1.1) 0
      (fun y => fix (h.βg y))
  · rw [Set.indicator_of_mem (hD.2 ⟨h1, h2, h3⟩), Set.indicator_of_mem h1, Set.indicator_of_mem h2,
      Set.indicator_of_mem h3, hph, hc]
    ring
  all_goals
    first
    | (rw [Set.indicator_of_notMem (fun hm => h1 (hD.1 hm).1), Set.indicator_of_notMem h1]; ring)
    | (rw [Set.indicator_of_notMem (fun hm => h2 (hD.1 hm).2.1), Set.indicator_of_notMem h2]; ring)
    | (rw [Set.indicator_of_notMem (fun hm => h3 (hD.1 hm).2.2), Set.indicator_of_notMem h3]; ring)

end PairData

end WaveTurbulence.Flower.ProtCut
