/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.FlFace.Expand
/-! # FL-FACE: the phase of a face ("adds `ω_v` to that endpoint's phase")

On a face `F`, a selected `v` sent to its parent `q` (or a child `c`) contributes `e^{iθ_v t_q}` (resp. `e^{iθ_v t_c}`):
its frequency is added to the frequency at `q` (resp. `c`). A selected `v` sent to `top` or `floor` contributes the
constant `e^{iθ_v top_v}` (resp. `e^{iθ_v 𝔏_v}`). `phaseVec_faceSubst` states this for a general frequency vector,
`facePhase_eq` for `phaseProdOff` (`θ = offFreq`, so the added frequency is `ω_v`). -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.FlFace
open Finset

variable {w : ℕ}

/-- The node whose time a parent/child endpoint substitutes (`none` for `top`/`floor`). -/
def FaceEnd.node {T : Fin w → TTree} : FaceEnd T → Option (GBranch T)
  | .top => none
  | .parent q => some q
  | .floor => none
  | .child c => some c

/-- The frequencies of a face: zero at selected nodes; at an unselected `b`, `θ_b` plus the frequencies `θ_v` of the
selected `v` substituted by `t_b`. -/
def faceFreq {T : Fin w → TTree} (θ : GBranch T → ℝ) (S : Finset (GBranch T)) (F : Face T) (b : GBranch T) : ℝ :=
  if b ∈ S then 0 else θ b + ∑ v ∈ S, if (F v).node = some b then θ v else 0

section Layered

variable (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ)

/-- The constant phase of the selected nodes sent to a constant endpoint (`top` or `floor`). -/
def faceConst (θ : GBranch LG.garden.tree → ℝ) (S : Finset (GBranch LG.garden.tree)) (F : Face LG.garden.tree) :
    ℂ :=
  ∏ v ∈ S, if (F v).node = none then Complex.exp (((θ v * endVal LG up v 0 (F v) : ℝ) : ℂ) * Complex.I) else 1

theorem endVal_of_node_none (v : GBranch LG.garden.tree) (E : FaceEnd LG.garden.tree) (h : E.node = none)
    (t : GBranch LG.garden.tree → ℝ) : endVal LG up v t E = endVal LG up v 0 E := by
  cases E <;> simp_all [FaceEnd.node, endVal]

theorem endVal_of_node_some (v : GBranch LG.garden.tree) (E : FaceEnd LG.garden.tree) {q : GBranch LG.garden.tree}
    (h : E.node = some q) (t : GBranch LG.garden.tree → ℝ) : endVal LG up v t E = t q := by
  cases E <;> simp_all [FaceEnd.node, endVal]

theorem node_not_mem {S : Finset (GBranch LG.garden.tree)} (hS : SelOnePerTree S) {v : GBranch LG.garden.tree}
    (hv : v ∈ S) {E : FaceEnd LG.garden.tree} (hE : E ∈ endChoices v) {q : GBranch LG.garden.tree}
    (h : E.node = some q) : q ∉ S := by
  rcases mem_endChoices.1 hE with rfl | ⟨q', hq', rfl⟩ | rfl | ⟨c, hc, rfl⟩
  · simp [FaceEnd.node] at h
  · simp only [FaceEnd.node, Option.some.injEq] at h
    exact h ▸ parent_not_mem hS hv hq'
  · simp [FaceEnd.node] at h
  · simp only [FaceEnd.node, Option.some.injEq] at h
    exact h ▸ child_not_mem hS hv hc

/-- **The phase of a face.** The phase product at the substituted times is the constant phase of the `top`/`floor`
substitutions times the phase product with the face frequencies, in which `θ_v` is added at the parent or child that
`v` is sent to. -/
theorem phaseVec_faceSubst (θ : GBranch LG.garden.tree → ℝ) {S : Finset (GBranch LG.garden.tree)}
    (hS : SelOnePerTree S) {F : Face LG.garden.tree} (hF : F ∈ faces S) (t : GBranch LG.garden.tree → ℝ) :
    phaseVec θ (faceSubst LG up S F t) = faceConst LG up θ S F * phaseVec (faceFreq θ S F) t := by
  set e : ℝ → ℂ := fun x => Complex.exp ((x : ℂ) * Complex.I) with he
  have hsub : ∀ b ∉ S, faceSubst LG up S F t b = t b := fun b hb => by simp only [faceSubst, hb, ↓reduceIte]
  have hsel : ∀ v ∈ S, faceSubst LG up S F t v = endVal LG up v t (F v) := fun v hv => by
    simp only [faceSubst, hv, ↓reduceIte]
  -- the selected factors
  have hA : ∀ v ∈ S, e (θ v * faceSubst LG up S F t v) =
      (if (F v).node = none then e (θ v * endVal LG up v 0 (F v)) else 1) *
        ∏ b ∈ Sᶜ, if (F v).node = some b then e (θ v * t b) else 1 := by
    intro v hv
    rw [hsel v hv]
    rcases hn : (F v).node with _ | q
    · rw [endVal_of_node_none LG up v _ hn t]
      simp
    · have hq : q ∈ Sᶜ := mem_compl.2 (node_not_mem LG hS hv (mem_faces hF hv) hn)
      rw [endVal_of_node_some LG up v _ hn t]
      simp only [reduceCtorEq, ↓reduceIte, one_mul, Option.some.injEq]
      rw [prod_ite_eq _ _ (fun b => e (θ v * t b)), ite_eq_left hq]
  -- the unselected factors
  have hB : ∀ b ∈ Sᶜ, e (faceFreq θ S F b * t b) =
      e (θ b * t b) * ∏ v ∈ S, if (F v).node = some b then e (θ v * t b) else 1 := by
    intro b hb
    have hb' : b ∉ S := mem_compl.1 hb
    simp only [faceFreq, hb', ↓reduceIte, he]
    have : ∀ v ∈ S, (if (F v).node = some b then Complex.exp (((θ v * t b : ℝ) : ℂ) * Complex.I) else 1) =
        Complex.exp (((((if (F v).node = some b then θ v else 0) * t b : ℝ)) : ℂ) * Complex.I) := by
      intro v _
      split_ifs <;> simp
    rw [prod_congr rfl this, ← Complex.exp_sum, ← Complex.exp_add]
    congr 1
    push_cast
    rw [add_mul, add_mul, sum_mul, sum_mul]
  have hS0 : ∀ b ∈ S, e (faceFreq θ S F b * t b) = 1 := fun b hb => by
    simp [he, faceFreq, hb]
  have lhs : phaseVec θ (faceSubst LG up S F t) =
      (∏ v ∈ S, e (θ v * faceSubst LG up S F t v)) * ∏ b ∈ Sᶜ, e (θ b * t b) := by
    rw [phaseVec, ← prod_mul_prod_compl S]
    congr 1
    exact prod_congr rfl fun b hb => by rw [hsub b (mem_compl.1 hb)]
  have rhs : phaseVec (faceFreq θ S F) t =
      (∏ b ∈ Sᶜ, e (θ b * t b)) * ∏ b ∈ Sᶜ, ∏ v ∈ S, if (F v).node = some b then e (θ v * t b) else 1 := by
    rw [phaseVec, ← prod_mul_prod_compl S, prod_congr rfl hS0, prod_const_one, one_mul,
      prod_congr rfl hB, prod_mul_distrib]
  rw [lhs, rhs, prod_congr rfl hA, prod_mul_distrib, prod_comm (s := Sᶜ)]
  unfold faceConst
  ring

/-- **The phase of a face, for `phaseProdOff`**: `ω_v` is added to the frequency at the parent or child that `v` is
sent to (`top`/`floor` substitutions give constant phases). -/
theorem facePhase_eq (L γ δ : ℝ) {d : ℕ} (off : Finset (GBranch LG.garden.tree)) (k : GNode LG.garden.tree → Mom d)
    {S : Finset (GBranch LG.garden.tree)} (hS : SelOnePerTree S) {F : Face LG.garden.tree} (hF : F ∈ faces S)
    (t : GBranch LG.garden.tree → ℝ) :
    facePhase L γ δ LG up off k S F t =
      faceConst LG up (offFreq L γ δ LG.garden off k) S F *
        phaseVec (faceFreq (offFreq L γ δ LG.garden off k) S F) t := by
  rw [facePhase, phaseProdOff_eq_phaseVec, phaseVec_faceSubst LG up _ hS hF]

end Layered

end WaveTurbulence.Flower.FlFace
