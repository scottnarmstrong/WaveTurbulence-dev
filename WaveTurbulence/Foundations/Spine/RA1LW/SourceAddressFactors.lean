/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafFam
public import WaveTurbulence.Foundations.Spine.RA1LW.Base
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceAddressPV

/-! # Extracting independent factors from actual source singular blocks -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Links Function

/-- A delta integral admits scalar extraction without an integrability
premise, by the defining Bochner integral convention. -/
theorem deltaInner_const_mul {d : ℕ} (c : ℂ) (H : Mom d → Mom d → ℂ) :
    NTSP.deltaInner (fun x y => c*H x y) = c*NTSP.deltaInner H := by
  simp only [NTSP.deltaInner,integral_const_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  ring

/-- A factor unchanged by the integrated source parameters can be
extracted from their actual singular block. The PV convergence used here
is proved from the original input norm at every remaining source node. -/
theorem addressAppAlong_mul_source_block {d : ℕ} (hd : 3 ≤ d)
    {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G) (hn : 0 < Q.links.length)
    {K M : ℕ} {H : LGSpine.LeafProfiles 2 d} {B : ℝ} (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hF : (∀ a, Fourier.spatialNorm K M (leafFam hQ hG H a) ≤ ENNReal.ofReal B))
    (Z : Finset (Fin 2 × TTree.Path)) (L : List (Fin Q.links.length))
    (hL : L.Nodup) (k : Mom d)
    (g : (Fin 2 × TTree.Path → Mom d × Mom d) → ℂ)
    (hg : ∀ j ∈ L, ∀ θ a b, g (update θ (chosenNode Q j) (a,b)) = g θ)
    (θ : Fin 2 × TTree.Path → Mom d × Mom d) :
    addressAppAlong Z (L.map (chosenNode Q))
      (fun θ => g θ*cplLeafProduct (addrFam H) θ Q (0,[]) (1,[]) k) θ =
    g θ*addressAppAlong Z (L.map (chosenNode Q))
      (fun θ => cplLeafProduct (addrFam H) θ Q (0,[]) (1,[]) k) θ := by
  classical
  induction L generalizing θ with
  | nil => rfl
  | cons j L ih =>
    obtain ⟨hj,hL⟩ := List.nodup_cons.mp hL
    have htail : ∀ θ, addressAppAlong Z (L.map (chosenNode Q))
        (fun θ => g θ*cplLeafProduct (addrFam H) θ Q (0,[]) (1,[]) k) θ =
        g θ*addressAppAlong Z (L.map (chosenNode Q))
          (fun θ => cplLeafProduct (addrFam H) θ Q (0,[]) (1,[]) k) θ := by
      intro θ
      exact ih hL (fun i hi => hg i (List.mem_cons_of_mem _ hi)) θ
    simp only [List.map_cons,addressAppAlong,addressAppStep]
    have he : (fun a b => addressAppAlong Z (L.map (chosenNode Q))
        (fun θ => g θ*cplLeafProduct (addrFam H) θ Q (0,[]) (1,[]) k)
        (update θ (chosenNode Q j) (a,b))) =
        (fun a b => g θ*addressAppAlong Z (L.map (chosenNode Q))
          (fun θ => cplLeafProduct (addrFam H) θ Q (0,[]) (1,[]) k)
          (update θ (chosenNode Q j) (a,b))) := by
      funext a b
      rw [htail,hg j List.mem_cons_self θ a b]
    rw [he]
    split_ifs
    · exact pvOp_const_mul_of_tendsto (g θ)
        (tendsto_pvTrunc_address_source_block_at hd hQ hG hn hK hM hB hF Z L hL j hj k θ)
    · exact deltaInner_const_mul (g θ) _

end WaveTurbulence.RA1Leafwise
