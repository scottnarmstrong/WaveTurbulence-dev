/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafFam
public import WaveTurbulence.Foundations.Spine.RA1LW.ActualLeafSingularRepresentation
public import WaveTurbulence.Foundations.RegAsymp.CellSingularBlocks

/-! # Source-level blockwise singular integration from actual input norms -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Links Incoh Function Filter Topology

/-- Every complete nodup list of original source links gives the same
singular integral. The input norm supplies all absolute Fourier mass;
no general principal-value Fubini premise is assumed. -/
theorem appAlong_source_eq_singInt {d : ℕ} (hd : 3 ≤ d)
    {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G) (hn : 0 < Q.links.length)
    {K M : ℕ} {H : LGSpine.LeafProfiles 2 d} {B : ℝ} (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hF : (∀ a, Fourier.spatialNorm K M (leafFam hQ hG H a) ≤ ENNReal.ofReal B))
    (J : Finset (Fin Q.links.length)) (L : List (Fin Q.links.length))
    (hL : L.Nodup) (hcover : ∀ j, j ∈ L) (k : Mom d) (x y : Fin Q.links.length → Mom d) :
    appAlong J L (fun x y => ∏ a, leafFam hQ hG H a ((coupleMomentumData hQ hG).inputMomentum k
      (fun j i => if i=0 then x j else y j) a)) x y =
    singInt J (fun x y => ∏ a, leafFam hQ hG H a ((coupleMomentumData hQ hG).inputMomentum k
      (fun j i => if i=0 then x j else y j) a)) := by
  obtain ⟨Ccover,-,hcoverSource⟩ := actual_source_leaf_singular_representation d hd
  obtain ⟨S,hS,hrep⟩ := hcoverSource G Q hQ hG hn
  obtain ⟨hp,-⟩ := hrep K M B hK hM hB (leafFam hQ hG H) hF
  have he : (fun (x y : Fin Q.links.length → Mom d) =>
      ∏ a, leafFam hQ hG H a ((coupleMomentumData hQ hG).inputMomentum k
        (fun j i => if i=0 then x j else y j) a)) = leafSingularCellKernel hQ hG (leafFam hQ hG H) S k := by
    funext x y
    exact hp k x y
  rw [he]
  have := isFiniteMeasureOnCompacts_pairs (n := Q.links.length) (d := d)
  exact appAlong_eq_singInt_countableCellMixture
    (I := LeafSingularCellIndex S)
    (U := (Fin (2*Q.links.length+1) → Fin d → ℝ) ×
      ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d))) volume hd J
    (fun i j => NTSP.intVec (i.2.2.val j).1) (fun i j => NTSP.intVec (i.2.2.val j).2)
    (fun _ uv => uv.2.1) (fun _ uv => uv.2.2)
    (fun _ => measurable_snd.fst) (fun _ => measurable_snd.snd)
    (leafMaskedSingularCoefficient hQ hG (leafFam hQ hG H) S k)
    (stronglyMeasurable_leafMaskedSingularCoefficient hQ hG (by omega) hB hF S k)
    (integrable_leafMaskedSingularCoefficient hQ hG hn hK hM hB hF S k)
    (summable_integral_norm_leafMaskedSingularCoefficient hQ hG hn hK hM hB hF S hS k)
    L hL hcover x y

/-- Every remaining source pair after an arbitrary nodup integration
block has actual cutoff convergence, derived from the finite input norm. -/
theorem tendsto_pvTrunc_source_block {d : ℕ} (hd : 3 ≤ d)
    {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G) (hn : 0 < Q.links.length)
    {K M : ℕ} {H : LGSpine.LeafProfiles 2 d} {B : ℝ} (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hF : (∀ a, Fourier.spatialNorm K M (leafFam hQ hG H a) ≤ ENNReal.ofReal B))
    (J : Finset (Fin Q.links.length)) (L : List (Fin Q.links.length))
    (hL : L.Nodup) (j : Fin Q.links.length) (hj : j ∉ L) (k : Mom d)
    (x y : Fin Q.links.length → Mom d) :
    Tendsto (fun s : ℝ => pvTrunc s (fun a b =>
      appAlong J L (fun x y => ∏ a, leafFam hQ hG H a ((coupleMomentumData hQ hG).inputMomentum k
        (fun j i => if i=0 then x j else y j) a)) (update x j a) (update y j b))) atTop
      (𝓝 (pvOp (fun a b =>
        appAlong J L (fun x y => ∏ a, leafFam hQ hG H a ((coupleMomentumData hQ hG).inputMomentum k
          (fun j i => if i=0 then x j else y j) a)) (update x j a) (update y j b)))) := by
  obtain ⟨Ccover,-,hcoverSource⟩ := actual_source_leaf_singular_representation d hd
  obtain ⟨S,hS,hrep⟩ := hcoverSource G Q hQ hG hn
  obtain ⟨hp,-⟩ := hrep K M B hK hM hB (leafFam hQ hG H) hF
  have he : (fun (x y : Fin Q.links.length → Mom d) =>
      ∏ a, leafFam hQ hG H a ((coupleMomentumData hQ hG).inputMomentum k
        (fun j i => if i=0 then x j else y j) a)) = leafSingularCellKernel hQ hG (leafFam hQ hG H) S k := by
    funext x y
    exact hp k x y
  rw [he]
  have := isFiniteMeasureOnCompacts_pairs (n := Q.links.length) (d := d)
  exact tendsto_pvTrunc_appAlong_countableCellMixture
    (I := LeafSingularCellIndex S)
    (U := (Fin (2*Q.links.length+1) → Fin d → ℝ) ×
      ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d))) volume hd J
    (fun i j => NTSP.intVec (i.2.2.val j).1) (fun i j => NTSP.intVec (i.2.2.val j).2)
    (fun _ uv => uv.2.1) (fun _ uv => uv.2.2)
    (fun _ => measurable_snd.fst) (fun _ => measurable_snd.snd)
    (leafMaskedSingularCoefficient hQ hG (leafFam hQ hG H) S k)
    (stronglyMeasurable_leafMaskedSingularCoefficient hQ hG (by omega) hB hF S k)
    (integrable_leafMaskedSingularCoefficient hQ hG hn hK hM hB hF S k)
    (summable_integral_norm_leafMaskedSingularCoefficient hQ hG hn hK hM hB hF S hS k)
    L hL j hj x y

end WaveTurbulence.RA1Leafwise
