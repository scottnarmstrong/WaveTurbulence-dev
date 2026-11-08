/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.Root2

/-! # D2c-3 PROT-CUT: o104 Prop 7.4 (a) for couples at one decoration (`ε = +`)

For `Root2Data` (a type-2 couple `type2 (pair m Qr Qg inner rest) Xm Qlp`, closing pair `LGZ` on the rest couple
`LGB`) and the pieces `PairOnly LGZ m Qr Qg inner LGi LGr LGg` of the closing pair:

* `Root2Data.Φ2`: decorations `κ ↔ (κ_B, e, κ_i, κ_r, κ_g)` (main's `GlueData.decEquiv` for `glueData_couple`, then
  `PairData.decEquiv` on the closing pair);
* `summand_glue2`: the summand of `kernelProt` (root of tree `0` at `σ`) is `∫_{root2U}` of the product of the
  closing-pair summand with both linked nodes designated (`σ`, `u`) and the rest-couple summand (clocks `(u, U 1)`);
* **`Root2Data.summand_root2`**: with (P2) at the decoration level (`PairOnly.summand_both`), the summand is
  `Mc(star_a, star_b) ε_e ∫_{root2U} e^{πiA_e(σ−u)} S_B(u) S_int(σ, u) S_r S_g(σ, u)`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

namespace Root2Data

variable {LG : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain}
  {LGZ : LayeredGarden 1} {LGB : LayeredGarden 2} (D : Root2Data LG m Qr Qg inner LGZ LGB)
  {LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} (P : PairOnly LGZ m Qr Qg inner LGi LGr LGg)
include D

/-- The decoration split of the glue. -/
def gdEquiv (d : ℕ) : GenDecoration LG.garden d (fun _ => 0) 0 ≃
    GenDecoration LGZ.garden d (fun _ => 0) 0 × GenDecoration LGB.garden d (fun _ => 0) 0 :=
  D.gd.decEquiv (D.hs d) (D.hg d)
    (not_flower_of_plain D.plain) (not_flower_of_decodesTree D.decZ) (not_flower_of_plain D.plainB)

include P in
/-- **Decorations of the couple**: rest couple × (exceptional data × interior × red × green). -/
def Φ2 (d : ℕ) : GenDecoration LG.garden d (fun _ => 0) 0 ≃
    GenDecoration LGB.garden d (fun _ => 0) 0 × (PairE m d × (GenDecoration LGi.garden d (fun _ => 0) 0 ×
      (GenDecoration LGr.garden d (fun _ => 0) 0 × GenDecoration LGg.garden d (fun _ => 0) 0))) :=
  ((D.gdEquiv d).trans ((P.hp.decEquiv d).prodCongr (Equiv.refl _))).trans (Equiv.prodComm _ _)

variable {d : ℕ}

include P in
theorem Φ2_apply (κ : GenDecoration LG.garden d (fun _ => 0) 0) :
    D.Φ2 P d κ = ((D.gdEquiv d κ).2, P.hp.decEquiv d (D.gdEquiv d κ).1) := rfl

theorem prodH_glue2 (κ : GenDecoration LG.garden d (fun _ => 0) 0) (L : ℝ) (k : Mom d) (H : LeafProfiles 2 d) :
    ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k κ.1 ℓ.toNode) : ℂ) =
      (∏ ℓ ∈ inputLeaves LGZ.garden, (t2HX H ℓ.1 (cosetDecoration LGZ.garden L k (D.gdEquiv d κ).1.1 ℓ.toNode) : ℂ)) *
        ∏ ℓ ∈ inputLeaves LGB.garden,
          (t2HQ (cpair m Qr Qg inner) H ℓ.1 (cosetDecoration LGB.garden L k (D.gdEquiv d κ).2.1 ℓ.toNode) : ℂ) := by
  set f : Fin 2 × Path → ℂ := fun z => (H z (k + latticePoint L (extend κ.1 z)) : ℂ) with hf
  have e0 : ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k κ.1 ℓ.toNode) : ℂ) =
      ∏ ℓ ∈ inputLeaves LG.garden, f ℓ.1 := by
    refine Finset.prod_congr rfl fun ℓ _ => ?_
    rw [hf]
    simp only
    rw [show ℓ.1 = ℓ.toNode.1 from rfl, extend_node]
    rfl
  rw [e0, D.gd.prod_inputLeaves_glue (fun ℓ => D.decZ.2.1 ℓ) (fun ℓ _ => D.plain ℓ)
    (fun ℓ₂ ℓ _ => by rw [D.plain ℓ, D.plainB ℓ₂]) f]
  congr 1
  · refine Finset.prod_congr rfl fun ℓ _ => ?_
    rw [hf]
    simp only
    rw [show (topAddr ℓ.1 : Fin 2 × Path) = (D.gd.ι₁ ℓ.toNode).1 from rfl, extend_node]
    rfl
  · refine Finset.prod_congr rfl fun ℓ _ => ?_
    rw [hf]
    simp only
    rw [show botAddr (cpair m Qr Qg inner).lonePath ℓ.1 = (D.gd.ι₂ ℓ.toNode).1 from rfl, extend_node]
    rfl

theorem hH_Z (L : ℝ) (H : LeafProfiles 2 d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom d, Summable fun n : Fin d → ℤ => |H ℓ.1 (k' + latticePoint L n)|) :
    ∀ ℓ ∈ inputLeaves LGZ.garden, ∀ k' : Mom d,
      Summable fun n : Fin d → ℤ => |t2HX H ℓ.1 (k' + latticePoint L n)| := by
  intro ℓ hℓ k'
  obtain ⟨ℓ', hℓ', he⟩ := D.gd.inputLeaf_ofTop (fun ℓ => D.decZ.2.1 ℓ) (fun ℓ _ => D.plain ℓ) ℓ hℓ
  have : t2HX H ℓ.1 = H ℓ'.1 := by rw [he]; rfl
  rw [this]
  exact hH ℓ' hℓ' k'

theorem hH_B (L : ℝ) (H : LeafProfiles 2 d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom d, Summable fun n : Fin d → ℤ => |H ℓ.1 (k' + latticePoint L n)|)
    (k' : Mom d) : ∀ ℓ ∈ inputLeaves LGB.garden,
      Summable fun n : Fin d → ℤ => |t2HQ (cpair m Qr Qg inner) H ℓ.1 (k' + latticePoint L n)| := by
  intro ℓ hℓ
  obtain ⟨ℓ', hℓ', he⟩ := D.gd.inputLeaf_ofBot (fun ℓ₂ ℓ _ => by rw [D.plain ℓ, D.plainB ℓ₂]) ℓ hℓ
  have : t2HQ (cpair m Qr Qg inner) H ℓ.1 = H ℓ'.1 := by rw [he]; rfl
  rw [this]
  exact hH ℓ' hℓ' k'

include P in
/-- **The glue at one decoration**: closing pair (both linked nodes designated) × rest couple, under `∫ du`. -/
theorem summand_glue2 (κ : GenDecoration LG.garden d (fun _ => 0) 0) (L γ δ : ℝ) (k : Mom d)
    (H : LeafProfiles 2 d) (M : (GNode LG.garden.tree → Mom d) → ℂ) (MZ : (GNode LGZ.garden.tree → Mom d) → ℂ)
    (MB : (GNode LGB.garden.tree → Mom d) → ℂ) (hMg : ∀ K, M K = MZ (K ∘ D.gd.ι₁) * MB (K ∘ D.gd.ι₂))
    (U : Fin 2 → ℝ) (s σ : ℝ) :
    protSummand L γ δ LG H M (fun b => U b.1.1) s (trFix 0 σ) k κ =
      ∫ u in root2U LG m inner (U 0) σ,
        protSummand L γ δ LGZ (t2HX H) MZ (fun _ => U 0) s (pairFix m inner σ u) k (D.gdEquiv d κ).1 *
          protSummand L γ δ LGB (t2HQ (cpair m Qr Qg inner) H) MB (fun y => bClock U u y.1.1) s (fun _ => none) k
            (D.gdEquiv d κ).2 := by
  have cZ : cosetDecoration LG.garden L k κ.1 ∘ D.gd.ι₁ = cosetDecoration LGZ.garden L k (D.gdEquiv d κ).1.1 := rfl
  have cB : cosetDecoration LG.garden L k κ.1 ∘ D.gd.ι₂ = cosetDecoration LGB.garden L k (D.gdEquiv d κ).2.1 := rfl
  have hε : epsDec LG.garden κ.1 = epsDec LGZ.garden (D.gdEquiv d κ).1.1 * epsDec LGB.garden (D.gdEquiv d κ).2.1 :=
    D.gd.epsDec_glue κ.1
  unfold protSummand
  rw [hMg, cZ, cB, hε, D.protTime_root2 P L γ δ U s σ, cZ, cB, D.prodH_glue2 κ L k H]
  rw [show ∀ (a b c J : ℂ), a * (b * J * c) = (a * b * c) * J from fun a b c J => by ring,
    ← integral_const_mul]
  congr 1
  funext u
  push_cast
  ring

include P in
/-- **o104 Prop 7.4 (a) for couples at one decoration** (`ε = +`). -/
theorem summand_root2 (κ : GenDecoration LG.garden d (fun _ => 0) 0) (L γ δ : ℝ) (k : Mom d)
    (H : LeafProfiles 2 d) (M : (GNode LG.garden.tree → Mom d) → ℂ) (MZ : (GNode LGZ.garden.tree → Mom d) → ℂ)
    (MB : (GNode LGB.garden.tree → Mom d) → ℂ) (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ)
    (Mi : (GNode LGi.garden.tree → Mom d) → ℂ) (Mr : (GNode LGr.garden.tree → Mom d) → ℂ)
    (Mg : (GNode LGg.garden.tree → Mom d) → ℂ)
    (hMg : ∀ K, M K = MZ (K ∘ D.gd.ι₁) * MB (K ∘ D.gd.ι₂)) (hMZ : P.MultFactors MZ Mc Mi Mr Mg)
    (U : Fin 2 → ℝ) (s σ : ℝ) (hσ : σ ≤ U 0) :
    protSummand L γ δ LG H M (fun b => U b.1.1) s (trFix 0 σ) k κ =
      (Mc (starA m L k (D.Φ2 P d κ).2.1) (starB m L k (D.Φ2 P d κ).2.1) * (cutEps m (D.Φ2 P d κ).2.1 : ℂ)) *
        ∫ u in root2U LG m inner (U 0) σ, cutPh m (LGZ.garden.sig 0) L γ δ k u (D.Φ2 P d κ).2.1 σ *
          (protSummand L γ δ LGB (t2HQ (cpair m Qr Qg inner) H) MB (fun y => bClock U u y.1.1) s (fun _ => none) k
              (D.Φ2 P d κ).1 *
            (protSummand L γ δ LGi (cutHi .nil m (t2HX H)) Mi (fun _ => σ) u (fun _ => none)
                (k + latticePoint L (D.Φ2 P d κ).2.1.1.1) (D.Φ2 P d κ).2.2.1 *
              (protSummand L γ δ LGr (cutHr .nil m inner (LGZ.garden.sig 0) (t2HX H)) Mr
                  (fun y => cupR m inner (LGZ.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                  (k + latticePoint L (D.Φ2 P d κ).2.1.1.2.1) (D.Φ2 P d κ).2.2.2.1 *
                protSummand L γ δ LGg (cutHg .nil m inner (LGZ.garden.sig 0) (t2HX H)) Mg
                  (fun y => cupG m inner (LGZ.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                  (k + latticePoint L (D.Φ2 P d κ).2.1.1.2.2) (D.Φ2 P d κ).2.2.2.2))) := by
  rw [D.summand_glue2 P κ L γ δ k H M MZ MB hMg U s σ, D.Φ2_apply P κ, ← integral_const_mul]
  refine setIntegral_congr_fun (measurableSet_root2U LG m inner (U 0) σ) fun u hu => ?_
  simp only
  rw [P.summand_both (D.gdEquiv d κ).1 L γ δ (t2HX H) MZ Mc Mi Mr Mg hMZ (U 0) s σ u hσ hu.2.2.2.1.le k]
  ring

end Root2Data

end WaveTurbulence.Flower.ProtCut
