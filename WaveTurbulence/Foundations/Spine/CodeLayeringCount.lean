/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.InducedLayeringFinite
public import WaveTurbulence.Foundations.Spine.CoherentTopLayer
public import WaveTurbulence.Foundations.RegStruct.CarrierUniqueness
/-! Count actual canonical layered couples with a fixed regular code and incoherency.
The map goes into C4's literal induced-layering carrier, rather than all arbitrary layer assignments. -/
@[expose] public section
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Links WaveTurbulence.Reg
open TTree

noncomputable def coupleLayerTrace (Q : RegCpl) (LG : LayeredGarden 2) (z : Fin 2 × Path) : ℕ :=
  if z ∈ cplNodes Q (0, []) (1, []) then layerAt LG z else 0

def codeLayeredCouples (p : ℕ) (Q : RegCpl) (g : ℕ) : Set (LayeredGarden 2) :=
  {LG | IsCanonC (p + 1) LG ∧ Q.Decodes LG.garden ∧ LG.incoherency Q.links = g}

theorem coupleLayerTrace_mem {p g : ℕ} {Q : RegCpl} {LG : LayeredGarden 2}
    (hLG : LG ∈ codeLayeredCouples p Q g) :
    coupleLayerTrace Q LG ∈ inducedLayerings p Q (0, []) (1, []) p p g := by
  refine ⟨LG, hLG.1.2, hLG.1.1.1, Embeds.of_decodes hLG.2.1,
    parAt_root LG p 0, parAt_root LG p 1, ?_, fun _ => rfl⟩
  exact (incoherency_eq_count hLG.2.1).symm.trans hLG.2.2

theorem coupleLayerTrace_injective_of_decodes {Q : RegCpl} {LG LG' : LayeredGarden 2}
    (hQ : Q.Decodes LG.garden) (hQ' : Q.Decodes LG'.garden)
    (he : coupleLayerTrace Q LG = coupleLayerTrace Q LG') : LG = LG' := by
  have hG := carrier_unique hQ hQ'
  rcases LG with ⟨G, l, hl⟩
  rcases LG' with ⟨G', l', hl'⟩
  dsimp only at hG
  subst G'
  have hlayers : l = l' := by
    funext z
    have h := congrFun he z.1
    have hz := cplNodes_covers_node hQ z
    simpa only [coupleLayerTrace, if_pos hz, layerAt_node] using h
  subst l'
  rfl

/-- The actual carrier is finite; no ncard-on-an-infinite-set shortcut is involved. -/
theorem finite_codeLayeredCouples (p : ℕ) (Q : RegCpl) (hwf : Q.wf = true) (g : ℕ) :
    (codeLayeredCouples p Q g).Finite :=
  Set.Finite.of_injOn (fun _ h => coupleLayerTrace_mem h)
    (fun _ h _ h' he => coupleLayerTrace_injective_of_decodes h.2.1 h'.2.1 he)
    (finite_inducedLayerings Q hwf (0, []) (1, []) p p p g)

/-- TARGET L2230–2232: specialize the proved embedded layering bound to whole canonical couples. -/
theorem ncard_codeLayeredCouples_le (p : ℕ) (Q : RegCpl) (hwf : Q.wf = true) (g : ℕ) :
    (codeLayeredCouples p Q g).ncard ≤ (2 ^ (9 * p)) ^ g * 2 ^ Q.size := by
  have hi : Set.InjOn (coupleLayerTrace Q) (codeLayeredCouples p Q g) :=
    fun _ h _ h' he => coupleLayerTrace_injective_of_decodes h.2.1 h'.2.1 he
  have h := Set.ncard_le_ncard_of_injOn (coupleLayerTrace Q)
    (fun _ h => coupleLayerTrace_mem h) hi
    (finite_inducedLayerings Q hwf (0, []) (1, []) p p p g)
  exact h.trans (by simpa only [ldist, Nat.sub_self, zero_add, pow_zero, mul_one] using
      (layerreg2 Q hwf ((0 : Fin 2), []) (1, []) p p p g))

end WaveTurbulence.LGSpine
