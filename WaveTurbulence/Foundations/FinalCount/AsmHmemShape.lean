/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmConn2
/-! **FINALCOUNT-ASSEMBLY: `HmemAt` from the shape hypotheses.**  `hmemAt_of_shape`: `hmemAt_of_hard` with `hard` supplied by
`vhard_of_shape` and `hconn0_of_hostConn`.  Class-level inputs: `hsh` (every collected object has three atoms or is an `ObjVine`;
S4-SHAPE for the `C₁` part, `step1_vc_shape'`/`subsetvc_classification` for `C₂`), `hHC` (`HostConn`, S4-SHAPE) and `hcrit`
(no critical interior atom of a collected object; S4-DISJ `not_critical_of_interior_c1/c2`). -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {V : Type*} [DecidableEq V] [Infinite V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem hmemAt_of_shape {M₀ : Molecule V D₀} {Rn : ℕ} {C : CollData M₀}
    {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)} {Fst : Set (Object M₀)} {crit : V → Prop} {L γ η : ℝ} {w : Mom d}
    {A0 : Set (D₀ → (Fin d → ℤ))} (hM₀ : M₀.IsMolecule) (hS : SubHyp Rn M₀) (hLe : Real.exp 1 ≤ L) (hηγ : η ≤ γ)
    (hη : 0 < η) (h2 : 2 / L ≤ L ^ (-γ + η))
    (hmate : ∀ κ ∈ A0, ∀ x, κ (M₀.mate x) = κ x)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (hdisj : ∀ κ ∈ A0, ∀ U U' : Object M₀, Collected C (Un κ) L γ η w κ U → Collected C (Un κ) L γ η w κ U' →
      SameDes U U' ∨ Disjoint U.atoms U'.atoms)
    (hFst : ∀ κ ∈ A0, ∀ U ∈ Fst, Collected C (Un κ) L γ η w κ U)
    (hsgC : ∀ κ ∈ A0, ∀ U, Collected C (Un κ) L γ η w κ U → U.HasGapKind L γ η w κ .SG)
    (hdesC : ∀ κ ∈ A0, ∀ U, Collected C (Un κ) L γ η w κ U → HingeData C U)
    (hsh : ∀ κ ∈ A0, ∀ U, Collected C (Un κ) L γ η w κ U → U.atoms.card = 3 ∨ ObjVine M₀ U)
    (hHC : HostConn M₀ C Un L γ η w A0)
    (hcrit : ∀ κ ∈ A0, ∀ U, Collected C (Un κ) L γ η w κ U → ∀ a ∈ U.atoms, a ≠ U.upper → a ≠ U.lower → ¬ crit a) :
    HmemAt M₀ Rn C L γ η w A0 Un Fst crit := by
  refine hmemAt_of_hard hM₀ hS hLe hηγ hη h2 hmate h0 hdisj hFst hsgC hdesC ?_
  intro A h hinv κ hκ U hU hUint hnd K hKat hKup hKlo hKfa hKfb
  have hL : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hLe
  have hAe : A ≠ ∅ := Set.nonempty_iff_ne_empty.1 ⟨κ, hκ⟩
  obtain ⟨hA0, hctx⟩ := hinv
  obtain ⟨hc, -, hr⟩ := hctx.resolve_left hAe
  have hκ0 : κ ∈ A0 := hA0 hκ
  have hA := hc.anc
  have hD := hc.rel
  have hdeg : ∀ b ∈ h.s.M.atoms, h.s.M.deg b ≤ 4 := fun b hb => by
    have h1 := hc.good.1.bounds b hb
    have h3 := Mole.outdeg_add_indeg h.s.M b
    omega
  have hnl : ∀ x : h.s.D, h.s.M.atom x ≠ h.s.M.atom (h.s.M.mate x) := fun x e => by
    apply hS.noloop (h.s.down x)
    have e1 := hA.atom x
    have e2 := hA.atom (h.s.M.mate x)
    rw [← hD.mate] at e2
    rw [e1, e2, e]
  have hr' : Reach1 C Un Fst L γ η w κ h := hr κ hκ
  have hMol : h.s.M.IsMolecule :=
    isMolecule_of_compBeta hc.good (invE_of_reach hS (h0 κ hκ0) (Reach1.toAny hr')).comp
  rcases reach1_connInv hS (h0 κ hκ0) (hdisj κ hκ0) hr' with hd | hI
  · exact absurd (hd U hU) hnd
  · exact vhard_of_shape hA hD hnl hdeg hMol hUint hKat (hsh κ hκ0 U hU)
      (hconn0_of_hostConn hHC hκ0 hA hD hI hU hUint hKat)
      (fun a ha h1 h2 => hcrit κ hκ0 U hU a (hKat ▸ ha) (hKup ▸ h1) (hKlo ▸ h2))

end WaveTurbulence.FinalCountAsm
