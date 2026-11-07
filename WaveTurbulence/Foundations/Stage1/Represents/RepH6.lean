/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepH5
public import WaveTurbulence.Foundations.Stage1.Represents.RepAsm7

/-!
# S2 REPRESENTS, VINE-D (6): the assembly context with vine factors and the assembled kernel data

`AsmCtxH S d` extends the vine-free assembly context `AsmCtx` (slot superpositions `fam`, boxes, gap selection) by the
vine factors of the units `j : J`: the hinges of `G_sb`, the superposition data `H` (with masses `Mh j` uniform in the
centres), the clocks `hclk` and node momenta `hmom` of each unit, the vine factors `Hk` and their superpositions in the
unit balls of the four momenta (`hHk`, valid on the selected decorations and the spliced domain), and the source `src` of
each hinge momentum: a dart at a hinge, or a root (whose momentum is a constant).

For an assembled mode `ξh = ⟨ξ, ζ⟩`:
* `hingeAmp ξh`: the product of the vine amplitudes at the hinge momenta, cut off to the unit balls of the hinge darts
  (TARGET L1966: `K†` supported in the unit balls, bounded by `1`, no derivatives);
* `freqH ξh`: the slot frequencies plus the vine frequencies of the units whose clocks are branches;
* `rootHPhase ξh`: the vine phases at root clocks (constants);
* `DH ξh`: the spliced kernel data (hinges, hinge amplitude, frequencies).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RepAnalytic
  WaveTurbulence.VineEstS3.FS
open scoped ENNReal

variable {w : ℕ}

/-- The assembly context with vine factors. -/
structure AsmCtxH (S : Garden w) (d : ℕ) extends AsmCtx S d where
  hinges : Finset (GBranch S.tree)
  J : Type
  fJ : Fintype J
  dJ : DecidableEq J
  H : HingeFam J d
  hmom : J → Fin 4 → GNode S.tree
  hclk : J → Fin 3 → ClkSrc S
  Hk : J → (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ
  Mh : J → ℝ
  hMh : ∀ j c, ∑' l, H.w j c l ≤ Mh j
  hHk : ∀ κ : GenDecoration S d roots 0, selSk κ → ∀ τ ∈ splicedTimeDomain S layer0 tt, ∀ j c,
    (∀ i, ‖(base + latticePoint L (κ.1 (hmom j i))) - latPt d (c i)‖ ≤ 1) →
    HasSum (fun l => (H.w j c l : ℂ) * H.a j c l (fun i => base + latticePoint L (κ.1 (hmom j i))) *
      fsPhase (H.m j c l) (fun i => clockOf S tt τ (hclk j i)))
      (Hk j (fun i => clockOf S tt τ (hclk j i)) (fun i => base + latticePoint L (κ.1 (hmom j i))))
  src : J → Fin 4 → HingeDarts S hinges ⊕ Fin w
  src_dart : ∀ j i x, src j i = Sum.inl x → ∀ z : GenDecoration S d roots 0,
    bondIndex S z.1 x.1 = z.1 (hmom j i)
  src_root : ∀ j i r, src j i = Sum.inr r → ∀ z : GenDecoration S d roots 0, z.1 (hmom j i) = roots r

namespace AsmCtxH
variable {d : ℕ} {S : Garden w} (A : AsmCtxH S d)

instance : Fintype A.J := A.fJ
instance : DecidableEq A.J := A.dJ

/-- The assembled index. -/
abbrev Xi := XiH A.fam A.hS A.H A.hmom

/-- The hinge momenta of the unit `j` read from the momenta `K` of the hinge darts (roots: constants). -/
noncomputable def hmomOf (j : A.J) (K : HingeDarts S A.hinges → Mom d) : Fin 4 → Mom d := fun i =>
  match A.src j i with
  | Sum.inl x => K x
  | Sum.inr r => A.base + latticePoint A.L (A.roots r)

open scoped Classical in
/-- The hinge amplitude of the assembled mode. -/
noncomputable def hingeAmp (ξh : A.Xi) (K : HingeDarts S A.hinges → Mom d) : ℂ :=
  (∏ j, A.H.a j _ (ξh.2 j) (A.hmomOf j K)) *
    (if ∀ x : HingeDarts S A.hinges, ‖K x - cenS A.fam ξh.1 (slotOfDart A.hS x.1)‖ ≤ 1 then 1 else 0)

/-- The total frequency at a branch: slot modes plus vine modes. -/
noncomputable def freqH (ξh : A.Xi) (u : GBranch S.tree) : ℝ :=
  freqS A.fam A.hS ξh.1 u + ∑ j, ∑ i, if A.hclk j i = Sum.inr u then (A.H.m j _ (ξh.2 j) i : ℝ) else 0

/-- The vine phases at root clocks. -/
noncomputable def rootHPhase (ξh : A.Xi) : ℂ :=
  ∏ y : Fin w, Complex.exp (((Real.pi * (∑ j, ∑ i, if A.hclk j i = Sum.inl y then (A.H.m j _ (ξh.2 j) i : ℝ) else 0) *
    A.tt y : ℝ) : ℂ) * Complex.I)

/-- The constant weight of the assembled mode. -/
noncomputable def constWH (ξh : A.Xi) : ℂ :=
  constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξh.1 * (∏ j, ((A.H.w j _ (ξh.2 j) : ℝ) : ℂ)) * A.rootHPhase ξh

/-- The time dependence of the assembled mode. -/
noncomputable def timeFacH (ξh : A.Xi) (τ : GBranch S.tree → ℝ) : ℂ :=
  ∏ u : GBranch S.tree, Complex.exp (((Real.pi * A.freqH ξh u * τ u : ℝ) : ℂ) * Complex.I)

/-- The spliced kernel data of the assembled mode. -/
noncomputable def DH (ξh : A.Xi) : SplicedKernelData S d where
  layer := A.layer0
  hinges := A.hinges
  center := fun x => cenS A.fam ξh.1 (slotOfDart A.hS x)
  edgeAmplitude := edgeS A.fam A.hS A.Cχ ξh.1
  hingeAmplitude := A.hingeAmp ξh
  gapSpecification := A.gs
  frequency := A.freqH ξh
  rootTime := A.tt

/-- The phases of the slot modes and of the vine modes, regrouped by clocks. -/
theorem timeFac_mul_hinge_phase (ξh : A.Xi) (τ : GBranch S.tree → ℝ) :
    timeFac A.fam A.hS ξh.1 τ * ∏ j, fsPhase (A.H.m j _ (ξh.2 j)) (fun i => clockOf S A.tt τ (A.hclk j i)) =
      A.rootHPhase ξh * A.timeFacH ξh τ := by
  classical
  rw [prod_phase_regroup (fun j => A.H.m j _ (ξh.2 j)) A.hclk (clockOf S A.tt τ), Fintype.prod_sum_type]
  unfold timeFac timeFacH rootHPhase freqH
  simp only [clockOf, Sum.elim_inl, Sum.elim_inr]
  rw [mul_left_comm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun u _ => ?_
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

end AsmCtxH
end WaveTurbulence.Represents
