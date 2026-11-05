/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceType1Root

/-! # Empty source link lists, including unnormalized intermediate codes -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links Reg TTree

/-- Every source couple code with no links has just its root input
kernel, including type2 wrappers with two empty chains. -/
theorem cplLeafProduct_eq_input_of_links_nil {d w : ℕ} (F : Mom d → ℂ)
    (θ : Fin w × Path → Mom d × Mom d) (Q : RegCpl) (a b : Fin w × Path)
    (r : Mom d) (hab : Indep a b) (hnil : Q.linksAt a b = []) :
    cplLeafProduct F θ Q a b r = F r := by
  cases Q with
  | triv => exact cplLeafProduct_triv F θ a b r
  | type1 c Q₁ Q₂ Q₃ => simp only [RegCpl.linksAt,List.cons_ne_nil] at hnil
  | type2 Xp Xm Qlp =>
    simp only [RegCpl.linksAt,List.append_eq_nil_iff] at hnil
    obtain ⟨⟨hp,hm⟩,hq⟩ := hnil
    cases Xp with
    | pair m Qr Qg inner rest => simp only [RegChain.linksAt,List.cons_ne_nil] at hp
    | nil =>
      cases Xm with
      | pair m Qr Qg inner rest => simp only [RegChain.linksAt,List.cons_ne_nil] at hm
      | nil =>
        rw [cplLeafProduct_type2 F θ .nil .nil Qlp a b r hab]
        simp only [chainLeafProduct_nil,one_mul,RegChain.lonePath,addrExt_nil] at hq ⊢
        exact cplLeafProduct_eq_input_of_links_nil F θ Qlp a b r hab hq
termination_by structural Q

/-- The literal recursive Mstar also equals the input for every empty
link code, without requiring a normalization convention on the code. -/
theorem Mstar_eq_input_of_links_nil {d w : ℕ} (F : Mom d → ℝ) (Q : RegCpl)
    (Z : Finset (Fin w × Path)) (a b : Fin w × Path) (r : Mom d)
    (hnil : Q.linksAt a b = []) : Q.Mstar F Z a b r = F r := by
  cases Q with
  | triv => rfl
  | type1 c Q₁ Q₂ Q₃ => simp only [RegCpl.linksAt,List.cons_ne_nil] at hnil
  | type2 Xp Xm Qlp =>
    simp only [RegCpl.linksAt,List.append_eq_nil_iff] at hnil
    obtain ⟨⟨hp,hm⟩,hq⟩ := hnil
    cases Xp with
    | pair m Qr Qg inner rest => simp only [RegChain.linksAt,List.cons_ne_nil] at hp
    | nil =>
      cases Xm with
      | pair m Qr Qg inner rest => simp only [RegChain.linksAt,List.cons_ne_nil] at hm
      | nil =>
        simp only [RegCpl.Mstar,RegChain.Nstar,mul_one,RegChain.lonePath,addrExt_nil] at hq ⊢
        exact Mstar_eq_input_of_links_nil F Qlp Z a b r hq
termination_by structural Q

end WaveTurbulence.RegAsymp
