/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.RootTime

/-! # D2c PROT-CUT: the root pin at one decoration — assembly (`protTime_rootCut`) -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

namespace RootData

variable {LG LGZ LGi LGs : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl}
  {inner rest : RegChain} (D : RootData LG m Qr Qg inner rest LGZ LGi LGs LGr LGg)
include D

/-- With `σ ≤ u` and a nonempty interior, the closing pair has no admissible times. -/
theorem protTime_pairR_zero (L γ δ : ℝ) {d : ℕ} (T s σ u : ℝ) (hσu : σ ≤ u) (hin : inner.lonePath ≠ [])
    (K : GNode LGZ.garden.tree → Mom d) :
    protTime L γ δ LGZ (fun _ => T) s (fun x => D.fixU σ u (D.gd.ofSum (.inl x))) K = 0 := by
  unfold protTime
  refine (integral_congr_ae (Filter.Eventually.of_forall fun σ' => ?_)).trans (integral_zero _ _)
  refine Set.indicator_of_notMem (fun hmem => ?_) _
  have hI := (PairData.protDom_pair_mp (LG := LGZ) D.hp T s σ u _ (D.fixZ_rootB σ u) (D.fixZ_bB σ u)
    D.hli D.hlr D.hlg (fun x τ' hx => by simp only [D.fixZ_βi] at hx; simp at hx)
    (fun y τ' hy => by simp only [D.fixZ_βr] at hy; simp at hy)
    (fun y τ' hy => by simp only [D.fixZ_βg] at hy; simp at hy) _
    (fun b v hv => extendFix_some _ _ _ hv) hmem).1
  obtain ⟨q, k, hq⟩ := (List.eq_nil_or_concat inner.lonePath).resolve_left hin
  have hmem' : q ∈ (LGi.garden.tree 0).branching := by
    rw [D.decI.1]
    refine TTree.branching_of_append_mem _ (i := k) ?_
    rw [← List.concat_eq_append, ← hq]
    exact lonePath_mem_plug inner _ _
  let x₀ : GBranch LGi.garden.tree := ⟨((0 : Fin 1), q), hmem'⟩
  have hx₀ : LGi.garden.IsLoneParent x₀ := (D.hp.isLoneParent_I x₀).mpr ⟨k, by simpa using hq⟩
  have h1 := hI.2 x₀ hx₀ (D.fixZ_βi σ u x₀)
  have h2 := ((hI.1 x₀).1 (D.fixZ_βi σ u x₀)).2.2.2
  simp only at h1 h2
  linarith

theorem layer_bR : LG.layer D.bR.toNode = layerAt LG ((0 : Fin 1), bPath m inner) := by
  rw [← layerAt_node]
  rfl

theorem bR_not_lone : ¬ LG.garden.IsLoneParent D.bR := by
  rw [D.hlone]
  rintro ⟨y, hy, -⟩
  have := D.gd.ofSum_injective hy
  simp at this

theorem rootU_sub (T s σ : ℝ) : rootU LG m inner T σ ⊆ pinSet LG (fun _ => T) s (rootFix σ) D.bR := by
  rintro u ⟨h1, h2, h3, h4, h5⟩
  refine ⟨by rw [D.layer_bR]; exact h1, by rw [D.layer_bR]; exact h2, h3, h4, fun b' hb' σ' hσ' => ?_,
    fun b hb σ' hσ' => ?_, fun hl => absurd hl D.bR_not_lone⟩
  · exfalso
    unfold rootFix at hσ'
    split_ifs at hσ' with hp
    obtain ⟨-, i, hi⟩ := hb'
    rw [hp] at hi
    have := congrArg List.length hi
    simp at this
  · unfold rootFix at hσ'
    split_ifs at hσ' with hp
    rw [← Option.some.inj hσ']
    exact h5

theorem pinSet_lt_root (T s σ u : ℝ) (hu : u ∈ pinSet LG (fun _ => T) s (rootFix σ) D.bR)
    (hnil : inner.lonePath = []) : u < σ := by
  have hchild : D.bR.IsChildOf D.aR := by
    refine ⟨Subsingleton.elim _ _, m.c, ?_⟩
    rw [D.bR_path, D.aR_path]
    simp [bPath, hnil]
  exact hu.2.2.2.2.2.1 _ hchild σ (D.rootFix_aR σ)

/-- **The root pin at one decoration** (o104 Prop 7.4 (a), time level). -/
theorem protTime_rootCut (L γ δ : ℝ) {d : ℕ} (T s σ : ℝ) (hσT : σ ≤ T) (K : GNode LG.garden.tree → Mom d) :
    protTime L γ δ LG (fun _ => T) s (rootFix σ) K =
      ∫ u in rootU LG m inner T σ,
        Complex.exp ((Real.pi * ((LGZ.garden.sign D.hp.rootB.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
            omegaNode LGZ.garden (K ∘ D.gd.ι₁) D.hp.rootB * σ : ℝ) * Complex.I) *
          Complex.exp ((Real.pi * ((LGZ.garden.sign D.hp.bB.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
            omegaNode LGZ.garden (K ∘ D.gd.ι₁) D.hp.bB * u : ℝ) * Complex.I) *
        (protTime L γ δ LGi (fun _ => σ) u (fun _ => none) (K ∘ D.gd.ι₁ ∘ D.hp.ιi) *
          (protTime L γ δ LGr (fun y => cupR m inner (LGZ.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
              (K ∘ D.gd.ι₁ ∘ D.hp.ιr) *
            (protTime L γ δ LGg (fun y => cupG m inner (LGZ.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                (K ∘ D.gd.ι₁ ∘ D.hp.ιg) *
              protTime L γ δ LGs (fun _ => u) s (fun _ => none) (K ∘ D.gd.ι₂)))) := by
  rw [protTime_pin L γ δ LG (fun _ => T) s (rootFix σ) K D.bR (D.rootFix_bR σ),
    ← integral_indicator (measurableSet_rootU LG m inner T σ)]
  congr 1
  funext u
  by_cases hU : u ∈ rootU LG m inner T σ
  · rw [Set.indicator_of_mem (D.rootU_sub T s σ hU), Set.indicator_of_mem hU]
    rw [show Function.update (rootFix σ) D.bR (some u) = D.fixU σ u from rfl,
      D.protTime_glueR L γ δ T s σ u hU.2.2.2.1.le K,
      D.protTime_pairR L γ δ T s σ u hσT hU.2.2.2.1.le]
    simp only [Function.comp_assoc]
    ring
  · rw [Set.indicator_of_notMem hU]
    by_cases hP : u ∈ pinSet LG (fun _ => T) s (rootFix σ) D.bR
    · rw [Set.indicator_of_mem hP]
      have hσu : σ ≤ u := by
        by_contra hlt
        exact hU ⟨by rw [← D.layer_bR]; exact hP.1, by rw [← D.layer_bR]; exact hP.2.1, hP.2.2.1,
          hP.2.2.2.1, lt_of_not_ge hlt⟩
      have hin : inner.lonePath ≠ [] := fun hnil =>
        absurd (D.pinSet_lt_root T s σ u hP hnil) (not_lt.mpr hσu)
      rw [show Function.update (rootFix σ) D.bR (some u) = D.fixU σ u from rfl,
        D.protTime_glueR L γ δ T s σ u hP.2.2.2.1.le K, D.protTime_pairR_zero L γ δ T s σ u hσu hin, zero_mul]
    · rw [Set.indicator_of_notMem hP]

end RootData

end WaveTurbulence.Flower.ProtCut
