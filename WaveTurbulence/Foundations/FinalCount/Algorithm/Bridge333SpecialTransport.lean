/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.BridgeSpecialIncidence
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ErasedSpecialTransport
public import WaveTurbulence.Foundations.FinalCount.Algorithm.BridgeSpecialCharacterization
import Mathlib.Tactic

/-! # BR333 has no newly created special bonds -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem bridge333_retained_special_iff (M : Molecule V D) (hno : AppbNoLoops M)
    (e : D) (hb : Degen.IsBridge M e) (hout : M.out e = true)
    (h1 : M.deg (M.atom e) = 3) (h2 : M.deg (M.atom (M.mate e)) = 3)
    (x : {x : D // x ≠ e ∧ x ≠ M.mate e}) :
    AppbSpecial (eraseBond M e) x ↔ AppbSpecial M x.val := by
  have hd := bridge333_post_degrees M e hb h1 h2
  constructor
  · intro hs
    have hsrc : (eraseBond M e).deg (M.atom x.val) = 3 := hs.2.1
    have htgt : (eraseBond M e).deg (M.atom (M.mate x.val)) = 3 := hs.2.2.1
    have hn (v : V) (hv : (eraseBond M e).deg v = 2) :
        v ≠ M.atom x.val ∧ v ≠ M.atom (M.mate x.val) := by
      constructor
      · intro he
        rw [← he,hv] at hsrc
        omega
      · intro he
        rw [← he,hv] at htgt
        omega
    have ha := hn _ hd.1
    have hb' := hn _ hd.2
    exact (eraseBond_special_iff_of_remote_endpoints M e x ha.1 hb'.1 ha.2 hb'.2).mp hs
  · intro hs
    have h11 : M.atom e ≠ M.atom x.val := by
      intro he
      exact x.property.1 (special_at_bridge_endpoint_eq M hno e hb hout hs (Or.inl (Or.inl he)))
    have h21 : M.atom (M.mate e) ≠ M.atom x.val := by
      intro he
      exact x.property.1 (special_at_bridge_endpoint_eq M hno e hb hout hs (Or.inr (Or.inl he)))
    have h12 : M.atom e ≠ M.atom (M.mate x.val) := by
      intro he
      exact x.property.1 (special_at_bridge_endpoint_eq M hno e hb hout hs (Or.inl (Or.inr he)))
    have h22 : M.atom (M.mate e) ≠ M.atom (M.mate x.val) := by
      intro he
      exact x.property.1 (special_at_bridge_endpoint_eq M hno e hb hout hs (Or.inr (Or.inr he)))
    exact (eraseBond_special_iff_of_remote_endpoints M e x h11 h21 h12 h22).mpr hs

end WaveTurbulence.Mole.AppbAlgorithm
