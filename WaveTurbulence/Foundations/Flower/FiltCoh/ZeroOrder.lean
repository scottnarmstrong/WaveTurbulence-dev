/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.SingleLayer
public import WaveTurbulence.Foundations.Spine.PL2330Draft.Step
public import WaveTurbulence.Foundations.Spine.PL234Draft.SliceTransport
public import WaveTurbulence.Foundations.Fourier.Norm00VCutoff
public import WaveTurbulence.Foundations.RegAsymp.SpatialNormMonotone

/-! # FILT-COH: order-zero regular objects at any time weight

At order zero the layer-zero kernels are time independent: the trivial couple is its input profile
(`RA1Leafwise.coupleLeaves_triv`) and the empty tree is `1` (`RA1Leafwise.KTstar_eq_app_of_tree_size_zero`,
`PL234.LeafApp.tree_nil`). Their weighted time norms cost the fixed cutoff norm `‖χ_□‖_{X^θ}`. -/

public section
open WaveTurbulence.Induct
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.RegAsymp MeasureTheory Set TTree WaveTurbulence.Fourier
open WaveTurbulence.RA1Leafwise LGSpine
open scoped ENNReal

variable {d : ℕ}

/-- The weighted time norm of the constant `1` on a subset of the unit square. -/
theorem rN_one_le {θ : ℝ} {Λ : ℕ} (B : Set (Fin 2 → ℝ)) (hB : ∀ t ∈ B, ∀ i, t i ∈ Icc (0:ℝ) 1) :
    PL2330.rN (d := d) θ Λ 0 B (fun _ _ => (1:ℂ)) ≤ timeFourierNorm θ unitSquareCutoff := by
  refine (PL2330.rN_const_param_le (θ := θ) (Λ := Λ) B (fun _ => (1:ℂ))).trans ?_
  refine (mixedRestrictionNorm00_le_extension (fun t (_ : Unit) => (unitSquareCutoff t : ℂ)) ?_).trans ?_
  · intro t v
    rw [unitSquareCutoff_eq_one (hB t.1 t.2)]
  · rw [mixedFourierNorm00_unit]

/-- **Order-zero couples, layer zero.** -/
theorem couple_zero_bound (L γ δ θ : ℝ) (hd : 1 ≤ d) {Q : RegCpl} (hwf : Q.wf = true)
    (hsize : Q.size = 0) (LG : LayeredGarden 2) (h0 : ∀ a, LG.layer a = 0) (hQ : Q.Decodes LG.garden)
    {Binput : ℝ} (hBi : 0 ≤ Binput) (H : LeafProfiles 2 d)
    (hF : ∀ z, spatialNorm (40*d) (40*d) (addrFam H z) ≤ ENNReal.ofReal Binput)
    (T : Set (Fin 2 → ℝ)) (hT : ∀ t ∈ T, ∀ i, t i ∈ Icc (0:ℝ) 1) :
    mixedRestrictionNorm θ (30*d) (30*d) T Set.univ
        (fun ts k => coupleLeaves L γ δ LG H (ts.1 0) (ts.1 1) k.1) ≤
      ENNReal.ofReal (PL2330.cLeib d (30*d) * Binput * (timeFourierNorm θ unitSquareCutoff).toReal) := by
  obtain rfl := RA1Leafwise.regCpl_eq_triv_of_wf_size_zero Q hwf hsize
  have hΛ : 30*d ≠ 0 := by omega
  have he : PL2330.rN (d := d) θ (30*d) (30*d) T
      (fun t k => (H (0,[]) k : ℂ) * (fun _ _ => (1:ℂ)) t k) =
      mixedRestrictionNorm θ (30*d) (30*d) T Set.univ
        (fun ts k => coupleLeaves L γ δ LG H (ts.1 0) (ts.1 1) k.1) := by
    unfold PL2330.rN
    congr 1
    funext t k
    rw [coupleLeaves_triv L γ δ H LG h0 hQ (hT t.1 t.2 0) (hT t.1 t.2 1) k.1]
    simp only [mul_one]
  rw [← he]
  have hS : spatialNorm (30*d) (30*d) (fun k => (H (0,[]) k : ℂ)) ≤ ENNReal.ofReal Binput :=
    (spatialNorm_mono (by omega) (by omega) _).trans (hF (0,[]))
  have h1 : PL2330.rN (d := d) θ (30*d) 0 T (fun _ _ => (1:ℂ)) ≤
      ENNReal.ofReal (timeFourierNorm θ unitSquareCutoff).toReal := by
    rw [ENNReal.ofReal_toReal (timeFourierNorm_unitSquareCutoff_lt_top θ).ne]
    exact rN_one_le T hT
  exact PL2330.restr_mul_w_le hΛ hd (θ := θ) (30*d) T (c := fun k => (H (0,[]) k : ℂ))
    (fun _ _ => (1:ℂ)) hBi hS h1

/-- **Order-zero paired trees, layer zero.** -/
theorem tree_zero_bound (L γ δ θ : ℝ) (hd : 3 ≤ d) {X : RegChain} (hwf : X.wf = true)
    (hsize : X.size = 0) (LG : LayeredGarden 1) (hX : X.DecodesTree LG.garden) (h0 : ∀ a, LG.layer a = 0)
    (hL : 1 ≤ L) (hδ : δ ≠ 0) {Binput : ℝ} (hBi : 0 ≤ Binput) (H : LeafProfiles 1 d)
    (hF : ∀ z, spatialNorm (40*d) (40*d) (addrFam H z) ≤ ENNReal.ofReal Binput) :
    mixedRestrictionNorm θ (30*d) 0 (timeBoxGt 0 0) Set.univ
        (fun ts k => treeLeaves L γ δ LG H (ts.1 0) (ts.1 1) k.1) ≤
      timeFourierNorm θ unitSquareCutoff := by
  have hbox (t : timeBoxGt 0 0) :
      ((t.val 0∈Icc (0:ℝ) 1) ∧ (t.val 1∈Icc (0:ℝ) 1)) ∧ t.val 1<t.val 0 := by
    simpa only [timeBoxGt,timeBox,Set.mem_ofPred_eq,zero_add] using t.property
  have he : PL2330.rN (d := d) θ (30*d) 0 (timeBoxGt 0 0) (fun _ _ => (1:ℂ)) =
      mixedRestrictionNorm θ (30*d) 0 (timeBoxGt 0 0) Set.univ
        (fun ts k => treeLeaves L γ δ LG H (ts.1 0) (ts.1 1) k.1) := by
    unfold PL2330.rN
    congr 1
    funext t k
    rw [KTstar_eq_app_of_tree_size_zero hd hwf hsize LG hX h0 hL δ γ hδ hBi hF (hbox t).1.2.1 (hbox t).2
      (hbox t).1.1.2 k.1]
    have hnil : X = RegChain.nil := by
      cases X with
      | nil => rfl
      | pair m Qr Qg inner rest => simp only [RegChain.size] at hsize; omega
    subst hnil
    rw [PL234.LeafApp.tree_nil]
  rw [← he]
  exact rN_one_le _ (fun t ht i => by
    have hh : ((t 0∈Icc (0:ℝ) 1) ∧ (t 1∈Icc (0:ℝ) 1)) ∧ t 1<t 0 := by
      simpa only [timeBoxGt,timeBox,Set.mem_ofPred_eq,zero_add] using ht
    fin_cases i
    · exact hh.1.1
    · exact hh.1.2)

end WaveTurbulence.Flower.FiltCoh
