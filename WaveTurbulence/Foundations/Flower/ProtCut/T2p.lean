/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.T2mExist
public import WaveTurbulence.Foundations.Flower.ProtCut.SwGlue

/-! # D2c-3 PROT-CUT: o104 Prop 7.4 (c) with `ε = +`, at one decoration

A couple `LG` decoded by `type2 nil Xm Qlp`, `Qlp = type1 c Q₁ Q₂ Q₃` (the `+` chain empty): the root `ρ = (0, [])` of
its tree `0` (the tree `0` of `Q_lp`) is traced; its partner `ρ'` is the root of the tree `1` of `Q_lp`, at
`(1, Xm.lonePath)`, below the chain `Xm` of tree `1`. After relabelling (`SwGlueData` with `X = Xm`, `Y = X₂ = nil`) the
chain is on tree `0` and the generic `T2mData` cut applies (`SwGlueData.toT2m`); the lone-pair couple is the relabelled
`LGQ`, which is read back in the original labelling (`protSummand_sw_back`) and cut by o104 (b) with both roots
designated (`T1Data.summand_t1Both`).

* `T1Data.protTime_roots`, **`T1Data.summand_t1Both`**: a type-1 couple with both roots designated, at one decoration;
* `T2mData.summand_t2mGlue`: the glue and pin step of (c) at one decoration (any bottom couple);
* **`SwGlueData.summand_t2p`**: the summand of the relabelled couple. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

/-- The clocks of the relabelled couple. -/
def swU (U : Fin 2 → ℝ) (t : Fin 2) : ℝ := U (t1sw t)

theorem swU_zero (U : Fin 2 → ℝ) : swU U 0 = U 1 := rfl
theorem swU_one (U : Fin 2 → ℝ) : swU U 1 = U 0 := rfl

theorem t1Clock_le (U : Fin 2 → ℝ) (j : Fin 2) (σ u : ℝ) (hσ : σ ≤ U j) (hu : u ≤ U (t1sw j)) (t : Fin 2) :
    t1Clock j σ u t ≤ U t := by
  unfold t1Clock
  split_ifs with ht
  · rw [ht]; exact hσ
  · have : t = t1sw j := by fin_cases t <;> fin_cases j <;> simp_all [t1sw]
    rw [this]; exact hu

namespace T1Data

variable {c : MiniCplCode} {Q₁ Q₂ Q₃ : RegCpl} {LG LG₁ LG₂ LG₃ : LayeredGarden 2}
variable (h : T1Data c Q₁ Q₂ Q₃ LG.garden LG₁.garden LG₂.garden LG₃.garden)
include h

/-- **Both roots of a type-1 couple designated**, at `σ` (tree `j`) and `u` (the other tree). -/
theorem protTime_roots (hlA : ∀ z, LG₁.layer z = LG.layer (h.ιA z)) (hlB : ∀ z, LG₂.layer z = LG.layer (h.ιB z))
    (hlC : ∀ z, LG₃.layer z = LG.layer (h.ιC z)) (L γ δ : ℝ) {d : ℕ} (U : Fin 2 → ℝ) (s : ℝ) (j : Fin 2)
    (σ u : ℝ) (hσ : σ ≤ U j) (hu : u ≤ U (t1sw j)) (K : GNode LG.garden.tree → Mom d) :
    protTime L γ δ LG (fun y => U y.1.1) s (rootsFix (t1Clock j σ u)) K =
      Complex.exp ((Real.pi * ((LG.garden.sig 0 : ℤˣ) : ℤ) * δ * L ^ (2 * γ) * omegaNode LG.garden K (h.rt 0) *
          t1Clock j σ u 0 : ℝ) * Complex.I) *
        Complex.exp ((Real.pi * ((LG.garden.sig 1 : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
          omegaNode LG.garden K (h.rt 1) * t1Clock j σ u 1 : ℝ) * Complex.I) *
        (protTime L γ δ LG₁ (fun x => t1Clock j σ u x.1.1) 0 (fun _ => none) (K ∘ h.ιA) *
          (protTime L γ δ LG₂ (fun x => t1Clock j σ u (t1sw x.1.1)) 0 (fun _ => none) (K ∘ h.ιB) *
            protTime L γ δ LG₃ (fun x => t1Clock j σ u x.1.1) 0 (fun _ => none) (K ∘ h.ιC))) := by
  have hroot : ∀ t, rootsFix (t1Clock j σ u) (h.rt t) = some (t1Clock j σ u t) := fun t => by
    unfold rootsFix; rfl
  have nA : (fun x => rootsFix (t1Clock j σ u) (h.βA x)) = fun _ => none := funext fun x => by
    unfold rootsFix; rw [if_neg (h.βA_path_ne x)]
  have nB : (fun x => rootsFix (t1Clock j σ u) (h.βB x)) = fun _ => none := funext fun x => by
    unfold rootsFix; rw [if_neg (h.βB_path_ne x)]
  have nC : (fun x => rootsFix (t1Clock j σ u) (h.βC x)) = fun _ => none := funext fun x => by
    unfold rootsFix; rw [if_neg (h.βC_path_ne x)]
  have e := T1Data.protTime_t1 h L γ δ U s (rootsFix (t1Clock j σ u)) (t1Clock j σ u) hroot
    (t1Clock_le U j σ u hσ hu) hlA hlB hlC
    (fun x v hv => by rw [congrFun nA x] at hv; simp at hv)
    (fun x v hv => by rw [congrFun nB x] at hv; simp at hv)
    (fun x v hv => by rw [congrFun nC x] at hv; simp at hv) K
  rw [nA, nB, nC] at e
  exact e

variable {d : ℕ} (κ : GenDecoration LG.garden d (fun _ => 0) 0) (L : ℝ) (k : Mom d)

/-- **Both roots of a type-1 couple designated, at one decoration**: `Mc(stars) ε_y e^{πiB(σ−u)} Q₁ Q₂ Q₃`. -/
theorem summand_t1Both (hlA : ∀ z, LG₁.layer z = LG.layer (h.ιA z)) (hlB : ∀ z, LG₂.layer z = LG.layer (h.ιB z))
    (hlC : ∀ z, LG₃.layer z = LG.layer (h.ιC z)) (γ δ : ℝ) (H : LeafProfiles 2 d)
    (M : (GNode LG.garden.tree → Mom d) → ℂ) (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ)
    (M₁ : (GNode LG₁.garden.tree → Mom d) → ℂ) (M₂ : (GNode LG₂.garden.tree → Mom d) → ℂ)
    (M₃ : (GNode LG₃.garden.tree → Mom d) → ℂ) (hM : h.MultFactors M Mc M₁ M₂ M₃) (U : Fin 2 → ℝ) (s : ℝ)
    (j : Fin 2) (σ u : ℝ) (hσ : σ ≤ U j) (hu : u ≤ U (t1sw j)) :
    protSummand L γ δ LG H M (fun y => U y.1.1) s (rootsFix (t1Clock j σ u)) k κ =
      (Mc (t1Star c L k (h.decEquiv d κ).1 0) (t1Star c L k (h.decEquiv d κ).1 1) *
          (t1Eps c (h.decEquiv d κ).1 : ℂ)) *
        (t1Ph (LG.garden.sig j) L γ δ k (h.decEquiv d κ).1 σ u *
          (protSummand L γ δ LG₁ (t1HA c H) M₁ (fun x => t1Clock j σ u x.1.1) 0 (fun _ => none)
              (k + latticePoint L (h.decEquiv d κ).1.1.1) (h.decEquiv d κ).2.1 *
            (protSummand L γ δ LG₂ (t1HB H) M₂ (fun x => t1Clock j σ u (t1sw x.1.1)) 0 (fun _ => none)
                (k + latticePoint L (h.decEquiv d κ).1.1.2.1) (h.decEquiv d κ).2.2.1 *
              protSummand L γ δ LG₃ (t1HC c H) M₃ (fun x => t1Clock j σ u x.1.1) 0 (fun _ => none)
                (k + latticePoint L (h.decEquiv d κ).1.1.2.2) (h.decEquiv d κ).2.2.2))) := by
  unfold protSummand
  rw [hM, h.bstar_rt κ L k 0, h.bstar_rt κ L k 1, h.coset_A κ L k, h.coset_B κ L k, h.coset_C κ L k,
    h.epsDec_t1' κ, h.protTime_roots hlA hlB hlC L γ δ U s j σ u hσ hu, h.prodH_t1 κ L k H,
    h.coset_A κ L k, h.coset_B κ L k, h.coset_C κ L k, h.phase_t1 κ L k γ δ j σ u]
  push_cast
  ring

end T1Data

/-! ### The glue and pin step at one decoration -/

namespace T2mData

variable {LG : LayeredGarden 2} {Xp : RegChain} {LGX : LayeredGarden 1} {LGQ : LayeredGarden 2}
  (D : T2mData LG Xp LGX LGQ)
include D

/-- **o104 (c), the glue and pin step at one decoration**: chain summand (lone-port time `u`) × couple summand with both
roots designated (`u` at tree `0`, `σ` at tree `1`). -/
theorem summand_t2mGlue {d : ℕ} (κ : GenDecoration LG.garden d (fun _ => 0) 0) (L γ δ : ℝ) (k : Mom d)
    (H : LeafProfiles 2 d) (M : (GNode LG.garden.tree → Mom d) → ℂ) (MX : (GNode LGX.garden.tree → Mom d) → ℂ)
    (MQ : (GNode LGQ.garden.tree → Mom d) → ℂ) (hMg : ∀ K, M K = MX (K ∘ D.gd.ι₁) * MQ (K ∘ D.gd.ι₂))
    (U : Fin 2 → ℝ) (s σ : ℝ) :
    protSummand L γ δ LG H M (fun b => U b.1.1) s (trFix 1 σ) k κ =
      ∫ u in t2mU LG Xp (U 0),
        protSummand L γ δ LGX (t2HX H) MX (fun _ => U 0) u (fun _ => none) k (D.gdEquiv d κ).1 *
          protSummand L γ δ LGQ (t2HQ Xp H) MQ (fun y => U y.1.1) s (rootsFix (t1Clock 1 σ u)) k
            (D.gdEquiv d κ).2 := by
  have cX : cosetDecoration LG.garden L k κ.1 ∘ D.gd.ι₁ = cosetDecoration LGX.garden L k (D.gdEquiv d κ).1.1 := rfl
  have cQ : cosetDecoration LG.garden L k κ.1 ∘ D.gd.ι₂ = cosetDecoration LGQ.garden L k (D.gdEquiv d κ).2.1 := rfl
  have hε : epsDec LG.garden κ.1 = epsDec LGX.garden (D.gdEquiv d κ).1.1 * epsDec LGQ.garden (D.gdEquiv d κ).2.1 :=
    D.gd.epsDec_glue κ.1
  unfold protSummand
  rw [hMg, cX, cQ, hε, D.protTime_t2mGlue L γ δ U s σ, cX, cQ, D.prodH_glue κ L k H]
  rw [show ∀ (a b c J : ℂ), a * (b * J * c) = (a * b * c) * J from fun a b c J => by ring,
    ← integral_const_mul]
  congr 1
  funext u
  push_cast
  ring

end T2mData

/-! ### Reading a summand of the relabelled couple in the original labelling -/

theorem protSummand_sw_back {LG' : LayeredGarden 2} (hp : LG'.garden.IsPlain) (L γ δ : ℝ) {d : ℕ}
    (H' : LeafProfiles 2 d) (M' : (GNode (swLG LG').garden.tree → Mom d) → ℂ)
    (up' : GBranch (swLG LG').garden.tree → ℝ) (s : ℝ) (fix' : GBranch (swLG LG').garden.tree → Option ℝ)
    (k : Mom d) (κ' : GenDecoration (swLG LG').garden d (fun _ => 0) 0) :
    protSummand L γ δ (swLG LG') H' M' up' s fix' k κ' =
      protSummand L γ δ LG' (fun a => H' (t1sw a.1, a.2)) (fun K => M' (K ∘ ndB)) (fun b => up' (brF b)) s
        (fun b => fix' (brF b)) k ((swDec d hp).symm κ') := by
  rw [← protSummand_sw hp L γ δ (fun a => H' (t1sw a.1, a.2)) (fun K => M' (K ∘ ndB)) (fun b => up' (brF b)) s
    (fun b => fix' (brF b)) k ((swDec d hp).symm κ'), Equiv.apply_symm_apply]
  have e1 : swH (fun a => H' (t1sw a.1, a.2)) = H' := by
    funext a
    simp only [swH, t1sw_t1sw]
  have e2 : swM (fun K => M' (K ∘ ndB)) = M' := by
    funext K
    show M' ((K ∘ ndF) ∘ ndB) = M' K
    congr 1
    funext x
    exact congrArg K (ndF_ndB x)
  have e3 : (fun b => (fun b => up' (brF b)) (brB b) : GBranch (swLG LG').garden.tree → ℝ) = up' := by
    funext b
    simp only [brF_brB]
  have e4 : (fun b => (fun b => fix' (brF b)) (brB b) : GBranch (swLG LG').garden.tree → Option ℝ) = fix' := by
    funext b
    simp only [brF_brB]
  rw [e1, e2, e3, e4]

theorem rootsFix_brF (σ u : ℝ) {T : Fin 2 → TTree} (b : GBranch T) :
    rootsFix (t1Clock 1 σ u) (brF b : GBranch (swT T)) = rootsFix (t1Clock 0 σ u) b := by
  unfold rootsFix
  have h2 : (brF b : GBranch (swT T)).1.2 = b.1.2 := rfl
  have h1 : (brF b : GBranch (swT T)).1.1 = t1sw b.1.1 := rfl
  rw [h2, h1]
  by_cases hp : b.1.2 = []
  · rw [if_pos hp, if_pos hp]
    congr 1
    simp only [t1Clock, t1sw_eq_one_iff]
  · rw [if_neg hp, if_neg hp]

theorem trFix_brB0 (σ : ℝ) {T : Fin 2 → TTree} (b : GBranch (swT T)) : trFix 0 σ (brB b) = trFix 1 σ b := by
  unfold trFix
  have : ∀ t : Fin 2, t1sw t = 0 ↔ t = 1 := by intro t; fin_cases t <;> simp [t1sw]
  simp only [brB, this]

/-! ### The relabelled instance -/

namespace SwGlueData

variable {LG : LayeredGarden 2} {Xm : RegChain} {Qlp : RegCpl} {LGX : LayeredGarden 1} {LGB : LayeredGarden 2}
  (D : SwGlueData LG .nil Xm .nil Qlp LGX LGB)
include D

theorem decB' : Qlp.Decodes LGB.garden := by
  have := D.decB
  rwa [closeCouple_nil_nil] at this

/-- **The relabelled couple as a `T2mData`**, when the lone-pair couple has a branching root on tree `1`. -/
theorem toT2m (hroot : ([] : Path) ∈ (LGB.garden.tree 1).branching) : T2mData (swLG LG) Xm LGX (swLG LGB) :=
  ⟨D.gd, D.decX, swGarden_plain D.dec.1.1, swGarden_plain D.decB.1.1, hroot, D.hs, D.hg,
    fun z => by rw [D.layX]; rfl,
    fun z => by
      show LGB.layer (ndB z) = layerAt (swLG LG) (botAddr Xm.lonePath z.1)
      rw [D.layB, layerAt_sw]
      exact congrArg (layerAt LG) (phiB_sw _ z.1)⟩

theorem t2HQ_sw {d : ℕ} (H : LeafProfiles 2 d) :
    (fun a : Fin 2 × Path => t2HQ Xm (swH H) (t1sw a.1, a.2)) = fun a => H (phiB Xm.lonePath a) := by
  funext a
  obtain ⟨t, p⟩ := a
  fin_cases t <;> simp [t2HQ, swH, phiB, botAddr, t1sw]

end SwGlueData

end WaveTurbulence.Flower.ProtCut
