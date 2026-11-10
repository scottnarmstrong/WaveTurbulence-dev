/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.AbsNative
public import WaveTurbulence.Foundations.VineEst.VineEstS4.AbsLocal

/-! # Native input summability and measurability of the native starred kernels along clocks (V5 Step 4b)

The input hypothesis of the absolute-convergence argument is the source lattice summability of the inputs at the base coset
(`HF`); it transfers to every native couple and tree at every attachment coset (`couple_hF`, `chain_hF`).  The starred kernels are
continuous in their two times (LG-SPINE), hence measurable along any measurable clocks.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

section Native
variable {w d : ℕ} {G : Garden w} (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)

/-- The source input hypothesis: the inputs are absolutely summable on the base coset, at every input leaf of the garden. -/
@[expose] def HF : Prop :=
  ∀ ℓ ∈ inputLeaves (D.garden hG), Summable fun n : Fin d → ℤ => |F (layer ℓ.toNode) (base + latticePoint L n)|

theorem native_couple_plain (p : SourcePair G) : (nativeCoupleLayered D hG layer hLayer p).garden.IsPlain :=
  Comb.RootedSubforest.inducedGarden_plain (G := D.garden hG) (nativeCoupleForest D hG p)
    (nativeCoupleForest_closed D hG p)

theorem native_chain_paired (v : GBranch G.tree) :
    IsPairedTree (nativeChainLayered D hG layer hLayer v).garden :=
  Reg.decodedTree_isPairedTree _ _

theorem native_chain_lone (v : GBranch G.tree) (j : Fin 1) :
    (Finset.univ.filter fun ℓ : GLeaf (nativeChainLayered D hG layer hLayer v).garden.tree =>
      ℓ.1.1 = j ∧ (nativeChainLayered D hG layer hLayer v).garden.IsLone ℓ).card ≤ 1 :=
  card_lone_le_one (fun _ _ h h' => (native_chain_paired D hG layer hLayer v).eq_of_isLone h h') j

theorem native_couple_lone (p : SourcePair G) (j : Fin 2) :
    (Finset.univ.filter fun ℓ : GLeaf (nativeCoupleLayered D hG layer hLayer p).garden.tree =>
      ℓ.1.1 = j ∧ (nativeCoupleLayered D hG layer hLayer p).garden.IsLone ℓ).card ≤ 1 :=
  lone_count_le_one_of_plain _ (native_couple_plain D hG layer hLayer p) j

variable {D hG L F layer hLayer base}

theorem couple_hF (hF : HF D hG L F layer base) (p : SourcePair G) (x : Fin d → ℤ) :
    ∀ ℓ ∈ inputLeaves (nativeCoupleLayered D hG layer hLayer p).garden,
      Summable fun n : Fin d → ℤ => |F ((nativeCoupleLayered D hG layer hLayer p).layer ℓ.toNode)
        (base + latticePoint L x + latticePoint L n)| := fun ℓ hℓ =>
  nativeCouple_input_summable D hG L F layer hLayer base (fun _ => x) hF p ℓ hℓ

theorem chain_hF (hF : HF D hG L F layer base) (v : GBranch G.tree) (x : Fin d → ℤ) :
    ∀ ℓ ∈ inputLeaves (nativeChainLayered D hG layer hLayer v).garden,
      Summable fun n : Fin d → ℤ => |F ((nativeChainLayered D hG layer hLayer v).layer ℓ.toNode)
        (base + latticePoint L x + latticePoint L n)| := fun ℓ hℓ =>
  nativeChain_input_summable D hG L F layer hLayer base (fun _ => x) hF v ℓ hℓ

theorem latticePoint_zero' {d : ℕ} (L : ℝ) : latticePoint (d := d) L 0 = 0 := by
  ext j; simp [latticePoint]

theorem couple_hF_base (hF : HF D hG L F layer base) (p : SourcePair G) :
    ∀ ℓ ∈ inputLeaves (nativeCoupleLayered D hG layer hLayer p).garden,
      Summable fun n : Fin d → ℤ => |F ((nativeCoupleLayered D hG layer hLayer p).layer ℓ.toNode)
        (base + latticePoint L n)| := fun ℓ hℓ => by
  have := couple_hF hF p 0 ℓ hℓ
  simpa only [latticePoint_zero', add_zero] using this

theorem chain_hF_base (hF : HF D hG L F layer base) (v : GBranch G.tree) :
    ∀ ℓ ∈ inputLeaves (nativeChainLayered D hG layer hLayer v).garden,
      Summable fun n : Fin d → ℤ => |F ((nativeChainLayered D hG layer hLayer v).layer ℓ.toNode)
        (base + latticePoint L n)| := fun ℓ hℓ => by
  have := chain_hF hF v 0 ℓ hℓ
  simpa only [latticePoint_zero', add_zero] using this

end Native

section Meas
variable {α : Type*} [MeasurableSpace α] {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)

end Meas

section Clocks
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem measurable_clLocalClock (R : CLRegionData G U a b) (t : Fin 3 → ℝ) (v : GBranch G.tree) :
    Measurable (fun τ : CLInternalTime R => clLocalClock R t τ v) := by
  classical
  by_cases ha : v = a
  · have : (fun τ : CLInternalTime R => clLocalClock R t τ v) = fun _ => t 0 :=
      funext fun τ => by rw [ha]; exact clLocalClock_upper R t τ
    rw [this]; exact measurable_const
  · by_cases hv : v ∈ U
    · have hm : v ∈ clInteriorBranches R := Finset.mem_erase.mpr ⟨ha, hv⟩
      have : (fun τ : CLInternalTime R => clLocalClock R t τ v) = fun τ => τ ⟨v, hm⟩ :=
        funext fun τ => clLocalClock_internal R t τ ⟨v, hm⟩
      rw [this]; exact measurable_pi_apply _
    · have : (fun τ : CLInternalTime R => clLocalClock R t τ v) =
          fun _ => (if v.toNode = b.child R.positive then t 1
            else if v.toNode = b.child R.negative then t 2 else 0) :=
        funext fun τ => by simp [clLocalClock, ha, hv]
      rw [this]; exact measurable_const

theorem measurable_parentClock {α : Type*} [MeasurableSpace α] {tree : Fin w → TTree} (top : ℝ)
    (u : α → GBranch tree → ℝ) (hu : ∀ b, Measurable fun τ => u τ b) (x : GNode tree) :
    Measurable (fun τ => parentClock top (u τ) x) := by
  unfold parentClock
  generalize nodeToSlot x = s
  rcases s with _ | ⟨b, _⟩
  · exact measurable_const
  · exact hu b

end Clocks

end WaveTurbulence.VineEstS4
