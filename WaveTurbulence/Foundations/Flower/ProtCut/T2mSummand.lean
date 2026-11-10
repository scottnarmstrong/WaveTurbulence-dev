/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.T2m

/-! # D2c-3 PROT-CUT: o104 Prop 7.4 (c) at one decoration

For `T2mData` (a type-2 couple `type2 Xp nil Q_lp`, `Q_lp = type1 c Q₁ Q₂ Q₃`):

* `protTime_t2m`: the glue/pin step followed by o104 (b) (`T1Data.protTime_t1`) on `Q_lp`, whose roots are
  designated at `u` (tree `0`, the partner) and `σ` (tree `1`, the traced root);
* the decoration split `κ ↔ (κ_X, κ_lp)` (main's `GlueData.decEquiv`, from `decSplit_couple`/`decGlue_couple`)
  followed by `T1Data.decEquiv` on `κ_lp`: `κ ↔ (κ_X, y, κ₁, κ₂, κ₃)` (`T2mData.decEquiv`);
* **`T2mData.summand_t2m`**: the summand of `kernelProt` with the root of tree `1` designated at `σ` is
  `Mc(stars) ε_y ∫_{t2mU} e^{πiB(σ−u)} · K_X(U 0, port u) · Q₁ Q₂ Q₃(clocks σ_·(u))` at the outputs `k`
  (chain) and `k + y_i/L` (sub-couples). The multiplier factors through the glue (`MX`, `MQ`) and the roots of
  `Q_lp` (`T1Data.MultFactors`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

variable {d : ℕ}

/-- The profiles of the chain `Xp` (the top tree). -/
def t2HX (H : LeafProfiles 2 d) : LeafProfiles 1 d := fun a => H (topAddr a)

/-- The profiles of the lone-pair couple (the bottom couple, its tree `0` at `Xp.lonePath`). -/
def t2HQ (Xp : RegChain) (H : LeafProfiles 2 d) : LeafProfiles 2 d := fun a => H (botAddr Xp.lonePath a)

namespace T2mData

variable {LG : LayeredGarden 2} {Xp : RegChain} {c : MiniCplCode} {Q₁ Q₂ Q₃ : RegCpl}
  {LGX : LayeredGarden 1} {LGQ : LayeredGarden 2} (D : T2mData LG Xp LGX LGQ)
  {LG₁ LG₂ LG₃ : LayeredGarden 2} (h : T1Data c Q₁ Q₂ Q₃ LGQ.garden LG₁.garden LG₂.garden LG₃.garden)
include D h

/-- **The root trace of `Q_lp` inside the couple**, one decoration of times (o104 (c) via (b)). -/
theorem protTime_t2mQ (hlA : ∀ z, LG₁.layer z = LGQ.layer (h.ιA z)) (hlB : ∀ z, LG₂.layer z = LGQ.layer (h.ιB z))
    (hlC : ∀ z, LG₃.layer z = LGQ.layer (h.ιC z)) (L γ δ : ℝ) (U : Fin 2 → ℝ) (s σ : ℝ) (hσ : σ ≤ U 1)
    (u : ℝ) (hu : u ∈ t2mU LG Xp (U 0)) (K : GNode LGQ.garden.tree → Mom d) :
    protTime L γ δ LGQ (fun y => U y.1.1) s (rootsFix (t1Clock 1 σ u)) K =
      Complex.exp ((Real.pi * ((LGQ.garden.sig 0 : ℤˣ) : ℤ) * δ * L ^ (2 * γ) * omegaNode LGQ.garden K (h.rt 0) *
          t1Clock 1 σ u 0 : ℝ) * Complex.I) *
        Complex.exp ((Real.pi * ((LGQ.garden.sig 1 : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
          omegaNode LGQ.garden K (h.rt 1) * t1Clock 1 σ u 1 : ℝ) * Complex.I) *
        (protTime L γ δ LG₁ (fun x => t1Clock 1 σ u x.1.1) 0 (fun _ => none) (K ∘ h.ιA) *
          (protTime L γ δ LG₂ (fun x => t1Clock 1 σ u (t1sw x.1.1)) 0 (fun _ => none) (K ∘ h.ιB) *
            protTime L γ δ LG₃ (fun x => t1Clock 1 σ u x.1.1) 0 (fun _ => none) (K ∘ h.ιC))) := by
  have hroot : ∀ t, rootsFix (t1Clock 1 σ u) (h.rt t) = some (t1Clock 1 σ u t) := fun t => by
    unfold rootsFix; rfl
  have hσU : ∀ t, t1Clock 1 σ u t ≤ U t := by
    intro t
    fin_cases t
    · exact hu.2.2.2.le
    · exact hσ
  have nA : (fun x => rootsFix (t1Clock 1 σ u) (h.βA x)) = fun _ => none := funext fun x => by
    unfold rootsFix; rw [if_neg (h.βA_path_ne x)]
  have nB : (fun x => rootsFix (t1Clock 1 σ u) (h.βB x)) = fun _ => none := funext fun x => by
    unfold rootsFix; rw [if_neg (h.βB_path_ne x)]
  have nC : (fun x => rootsFix (t1Clock 1 σ u) (h.βC x)) = fun _ => none := funext fun x => by
    unfold rootsFix; rw [if_neg (h.βC_path_ne x)]
  have e := T1Data.protTime_t1 h L γ δ U s (rootsFix (t1Clock 1 σ u)) (t1Clock 1 σ u) hroot hσU hlA hlB hlC
    (fun x v hv => by rw [congrFun nA x] at hv; simp at hv)
    (fun x v hv => by rw [congrFun nB x] at hv; simp at hv)
    (fun x v hv => by rw [congrFun nC x] at hv; simp at hv) K
  rw [nA, nB, nC] at e
  exact e

/-! ### Decorations -/

omit h in
theorem decSplit : D.gd.DecSplit (Fin d → ℤ) := D.hs d

omit h in
theorem decGlue : GlueData.DecGlue (G := LG.garden) (G₁ := LGX.garden) (G₂ := LGQ.garden) (X := Xp) (Fin d → ℤ) :=
  D.hg d

omit h in
/-- The decoration split of the glue. -/
def gdEquiv (d : ℕ) : GenDecoration LG.garden d (fun _ => 0) 0 ≃
    GenDecoration LGX.garden d (fun _ => 0) 0 × GenDecoration LGQ.garden d (fun _ => 0) 0 :=
  D.gd.decEquiv (D.decSplit (d := d)) (D.decGlue (d := d)) (not_flower_of_plain D.plain)
    (not_flower_of_decodesTree D.decX) (not_flower_of_plain D.plainQ)

/-- **The decorations of the couple**: chain, exceptional data, three sub-couples. -/
def decEquiv (d : ℕ) : GenDecoration LG.garden d (fun _ => 0) 0 ≃
    GenDecoration LGX.garden d (fun _ => 0) 0 × (T1E d × (GenDecoration LG₁.garden d (fun _ => 0) 0 ×
      (GenDecoration LG₂.garden d (fun _ => 0) 0 × GenDecoration LG₃.garden d (fun _ => 0) 0))) :=
  (D.gdEquiv d).trans (Equiv.prodCongr (Equiv.refl _) (h.decEquiv d))

/-! ### Leaves -/

omit h in
theorem hm₁ (ℓ : GLeaf LGX.garden.tree) : LGX.garden.mark ℓ = if ℓ.1.2 = Xp.lonePath then some .lower else none :=
  D.decX.2.1 ℓ

omit h in
theorem hmtop (ℓ : GLeaf LG.garden.tree) (_ : ℓ.1.1 = 0 ∧ ¬ Xp.lonePath <+: ℓ.1.2) : LG.garden.mark ℓ = none :=
  D.plain ℓ

omit h in
theorem hmbot (ℓ₂ : GLeaf LGQ.garden.tree) (ℓ : GLeaf LG.garden.tree) (_ : ℓ.1 = botAddr Xp.lonePath ℓ₂.1) :
    LG.garden.mark ℓ = LGQ.garden.mark ℓ₂ := by
  rw [D.plain ℓ, D.plainQ ℓ₂]

omit h in
theorem prodH_glue (κ : GenDecoration LG.garden d (fun _ => 0) 0) (L : ℝ) (k : Mom d) (H : LeafProfiles 2 d) :
    ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k κ.1 ℓ.toNode) : ℂ) =
      (∏ ℓ ∈ inputLeaves LGX.garden, (t2HX H ℓ.1 (cosetDecoration LGX.garden L k (D.gdEquiv d κ).1.1 ℓ.toNode) : ℂ)) *
        ∏ ℓ ∈ inputLeaves LGQ.garden,
          (t2HQ Xp H ℓ.1 (cosetDecoration LGQ.garden L k (D.gdEquiv d κ).2.1 ℓ.toNode) : ℂ) := by
  set f : Fin 2 × Path → ℂ := fun z => (H z (k + latticePoint L (extend κ.1 z)) : ℂ) with hf
  have e0 : ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k κ.1 ℓ.toNode) : ℂ) =
      ∏ ℓ ∈ inputLeaves LG.garden, f ℓ.1 := by
    refine Finset.prod_congr rfl fun ℓ _ => ?_
    rw [hf]
    simp only
    rw [show ℓ.1 = ℓ.toNode.1 from rfl, extend_node]
    rfl
  rw [e0, D.gd.prod_inputLeaves_glue D.hm₁ D.hmtop D.hmbot f]
  congr 1
  · refine Finset.prod_congr rfl fun ℓ _ => ?_
    rw [hf]
    simp only
    rw [show (topAddr ℓ.1 : Fin 2 × Path) = (D.gd.ι₁ ℓ.toNode).1 from rfl, extend_node]
    rfl
  · refine Finset.prod_congr rfl fun ℓ _ => ?_
    rw [hf]
    simp only
    rw [show botAddr Xp.lonePath ℓ.1 = (D.gd.ι₂ ℓ.toNode).1 from rfl, extend_node]
    rfl

omit h in
theorem hH_X (L : ℝ) (H : LeafProfiles 2 d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom d, Summable fun n : Fin d → ℤ => |H ℓ.1 (k' + latticePoint L n)|)
    (k' : Mom d) : ∀ ℓ ∈ inputLeaves LGX.garden,
      Summable fun n : Fin d → ℤ => |t2HX H ℓ.1 (k' + latticePoint L n)| := by
  intro ℓ hℓ
  obtain ⟨ℓ', hℓ', he⟩ := D.gd.inputLeaf_ofTop D.hm₁ D.hmtop ℓ hℓ
  have : t2HX H ℓ.1 = H ℓ'.1 := by rw [he]; rfl
  rw [this]
  exact hH ℓ' hℓ' k'

omit h in
theorem hH_Q (L : ℝ) (H : LeafProfiles 2 d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom d, Summable fun n : Fin d → ℤ => |H ℓ.1 (k' + latticePoint L n)|) :
    ∀ ℓ ∈ inputLeaves LGQ.garden, ∀ k' : Mom d,
      Summable fun n : Fin d → ℤ => |t2HQ Xp H ℓ.1 (k' + latticePoint L n)| := by
  intro ℓ hℓ k'
  obtain ⟨ℓ', hℓ', he⟩ := D.gd.inputLeaf_ofBot D.hmbot ℓ hℓ
  have : t2HQ Xp H ℓ.1 = H ℓ'.1 := by rw [he]; rfl
  rw [this]
  exact hH ℓ' hℓ' k'

/-! ### Multipliers -/

omit h in
theorem bstar_inl (K : GNode LG.garden.tree → Mom d) (x : GBranch LGX.garden.tree) :
    bstar K (D.gd.ofSum (.inl x)) = bstar (K ∘ D.gd.ι₁) x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · show K ((D.gd.ofSum (.inl x)).child j) = K (D.gd.ι₁ (x.child j))
    rw [D.gd.ofSum_inl_child]

omit h in
theorem bstar_inr (K : GNode LG.garden.tree → Mom d) (y : GBranch LGQ.garden.tree) :
    bstar K (D.gd.ofSum (.inr y)) = bstar (K ∘ D.gd.ι₂) y := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · show K ((D.gd.ofSum (.inr y)).child j) = K (D.gd.ι₂ (y.child j))
    rw [D.gd.ofSum_inr_child]

omit h in
/-- **A branch-local multiplier factors through the glue.** -/
theorem multGlue_local (f : GBranch LG.garden.tree → (Fin 4 → Mom d) → ℂ) (K : GNode LG.garden.tree → Mom d) :
    ∏ b, f b (bstar K b) = (∏ x, f (D.gd.ofSum (.inl x)) (bstar (K ∘ D.gd.ι₁) x)) *
      ∏ y, f (D.gd.ofSum (.inr y)) (bstar (K ∘ D.gd.ι₂) y) := by
  rw [D.gd.prod_branch]
  simp only [D.bstar_inl, D.bstar_inr]

/-! ### The summand -/

/-- **o104 Prop 7.4 (c) at one decoration** (`ε = -`). -/
theorem summand_t2m (hlA : ∀ z, LG₁.layer z = LGQ.layer (h.ιA z)) (hlB : ∀ z, LG₂.layer z = LGQ.layer (h.ιB z))
    (hlC : ∀ z, LG₃.layer z = LGQ.layer (h.ιC z)) (κ : GenDecoration LG.garden d (fun _ => 0) 0) (L γ δ : ℝ)
    (k : Mom d) (H : LeafProfiles 2 d) (M : (GNode LG.garden.tree → Mom d) → ℂ)
    (MX : (GNode LGX.garden.tree → Mom d) → ℂ) (MQ : (GNode LGQ.garden.tree → Mom d) → ℂ)
    (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ) (M₁ : (GNode LG₁.garden.tree → Mom d) → ℂ)
    (M₂ : (GNode LG₂.garden.tree → Mom d) → ℂ) (M₃ : (GNode LG₃.garden.tree → Mom d) → ℂ)
    (hMg : ∀ K, M K = MX (K ∘ D.gd.ι₁) * MQ (K ∘ D.gd.ι₂)) (hMQ : h.MultFactors MQ Mc M₁ M₂ M₃)
    (U : Fin 2 → ℝ) (s σ : ℝ) (hσ : σ ≤ U 1) :
    protSummand L γ δ LG H M (fun b => U b.1.1) s (trFix 1 σ) k κ =
      (Mc (t1Star c L k (D.decEquiv h d κ).2.1 0) (t1Star c L k (D.decEquiv h d κ).2.1 1) *
          (t1Eps c (D.decEquiv h d κ).2.1 : ℂ)) *
        ∫ u in t2mU LG Xp (U 0), t1Ph (LGQ.garden.sig 1) L γ δ k (D.decEquiv h d κ).2.1 σ u *
          (protSummand L γ δ LGX (t2HX H) MX (fun _ => U 0) u (fun _ => none) k (D.decEquiv h d κ).1 *
            (protSummand L γ δ LG₁ (t1HA c (t2HQ Xp H)) M₁ (fun x => t1Clock 1 σ u x.1.1) 0 (fun _ => none)
                (k + latticePoint L (D.decEquiv h d κ).2.1.1.1) (D.decEquiv h d κ).2.2.1 *
              (protSummand L γ δ LG₂ (t1HB (t2HQ Xp H)) M₂ (fun x => t1Clock 1 σ u (t1sw x.1.1)) 0
                  (fun _ => none) (k + latticePoint L (D.decEquiv h d κ).2.1.1.2.1) (D.decEquiv h d κ).2.2.2.1 *
                protSummand L γ δ LG₃ (t1HC c (t2HQ Xp H)) M₃ (fun x => t1Clock 1 σ u x.1.1) 0 (fun _ => none)
                  (k + latticePoint L (D.decEquiv h d κ).2.1.1.2.2) (D.decEquiv h d κ).2.2.2.2))) := by
  set κQ := (D.gdEquiv d κ).2 with hκQ
  set κX := (D.gdEquiv d κ).1 with hκX
  have cX : cosetDecoration LG.garden L k κ.1 ∘ D.gd.ι₁ = cosetDecoration LGX.garden L k κX.1 := rfl
  have cQ : cosetDecoration LG.garden L k κ.1 ∘ D.gd.ι₂ = cosetDecoration LGQ.garden L k κQ.1 := rfl
  have hε : epsDec LG.garden κ.1 = epsDec LGX.garden κX.1 * epsDec LGQ.garden κQ.1 := D.gd.epsDec_glue κ.1
  rw [show D.decEquiv h d κ = (κX, h.decEquiv d κQ) from rfl]
  simp only
  unfold protSummand
  rw [hMg, cX, cQ, hMQ, h.bstar_rt κQ L k 0, h.bstar_rt κQ L k 1, h.coset_A κQ L k, h.coset_B κQ L k,
    h.coset_C κQ L k, hε, h.epsDec_t1' κQ, D.protTime_t2mGlue L γ δ U s σ, cX, cQ, D.prodH_glue κ L k H,
    h.prodH_t1 κQ L k (t2HQ Xp H)]
  rw [show ∀ (a b c J : ℂ), a * (b * J * c) = (a * b * c) * J from fun a b c J => by ring]
  conv_lhs => rw [← integral_const_mul]
  conv_rhs => rw [← integral_const_mul]
  refine setIntegral_congr_fun (measurableSet_t2mU LG Xp (U 0)) fun u hu => ?_
  simp only
  rw [D.protTime_t2mQ h hlA hlB hlC L γ δ U s σ hσ u hu, h.coset_A κQ L k, h.coset_B κQ L k, h.coset_C κQ L k,
    h.phase_t1 κQ L k γ δ 1 σ u]
  push_cast
  ring

end T2mData

end WaveTurbulence.Flower.ProtCut
