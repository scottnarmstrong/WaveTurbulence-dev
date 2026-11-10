/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain26
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain25
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.LowChain26`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT LOW-CHAIN, session 5 (4): `HendAtL`.**  Along `Reach1L` the number of components of the state stays `≤ 2R - 1`:
first-stage vine removals by `CnBound` on `remMol` (`fst_boundL`, with the isolated joints deleted by Step D1), later old vine steps by
`HostConnFL`, Step D1 never increases the number of components (`K.post.F ≤ F + 1` and a deleted degree-`2` joint), triple cuts do not
increase it.  `hendAtL_of_inputs` is exactly the `hend` hypothesis of `chain_coverL`. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
  WaveTurbulence.VineCount

variable {V : Type} [DecidableEq V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem fst_boundL {M₀ : Molecule V D₀} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)}
    {L γ η : ℝ} {w : Mom d} {A0 : Set (D₀ → (Fin d → ℤ))} {Rn : ℕ} {κ : D₀ → (Fin d → ℤ)}
    (hcn : CnBound M₀ C Un Fst L γ η w A0 Rn) (hκ : κ ∈ A0) {h : HSt V D₀} (hA : AncRel M₀ h.s h.anc) (hD : DartRel M₀ h.s)
    {ps : List (Src.Object Src.γL M₀ × Quad D₀)} (hI : ConnDataL2 M₀ C Un Fst L γ η w κ h ps) (hg : ∃ R', Good R' h.s)
    (hF : ∀ p ∈ ps, p.1 ∈ Fst) : h.s.M.numComponents + 1 ≤ 2 * Rn := by
  obtain ⟨⟨hinj, hps, hpw, hrem, hpres⟩, he1, he2, he3, hfo⟩ := hI
  obtain ⟨E, hE, hdeg⟩ := state_rem_isoE hA hD ps hinj hpres he1 he3
  obtain ⟨h1, h2⟩ := hcn κ hκ ps (fun p hp => ⟨hps p hp, hF p hp⟩) hpw
  rw [hE] at h1 h2
  rcases Nat.lt_or_ge (h.s.M.numComponents + E) (2 * Rn) with hlt | hge
  · omega
  · have heq : h.s.M.numComponents + E = 2 * Rn := le_antisymm h1 hge
    obtain ⟨v, hv, hv0⟩ := h2 heq
    rcases hdeg v hv hv0 with hE1 | ⟨c, hc, hc0⟩
    · omega
    · obtain ⟨R', hg⟩ := hg
      have := good_deg_pos hg c hc
      omega

theorem deg3_of_good_post {b : HSt V D₀} (K : Step1.VineCut Src.γL b.s.M) (R : ℝ) (kp : ℕ) {R' : ℕ}
    (hg : Good R' (b.vinePostL K R kp).s) : 3 ≤ b.s.M.deg K.C.upper ∧ 3 ≤ b.s.M.deg K.C.lower := by
  have hfa : K.fa ∈ K.post.atoms := fa_mem_post K
  have hfb : K.fb ∈ K.post.atoms := fb_mem_post K
  have h1 : 1 ≤ K.post.deg K.fa := good_deg_pos hg K.fa hfa
  have h2 : 1 ≤ K.post.deg K.fb := good_deg_pos hg K.fb hfb
  have e1 : K.post.deg K.fa = K.cutMol.deg K.fa :=
    restrictP_deg K.cutMol (fun a => a ∉ K.C.atoms) K.closed (fun h => K.fa_fresh (Step1.objectAtoms_sub K.C h))
  have e2 : K.post.deg K.fb = K.cutMol.deg K.fb :=
    restrictP_deg K.cutMol (fun a => a ∉ K.C.atoms) K.closed (fun h => K.fb_fresh (Step1.objectAtoms_sub K.C h))
  have d1 := K.deg_fa
  have d2 := K.deg_fb
  omega

end WaveTurbulence.GammaLow.FinalCount.H
