/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourcePairEnumeration
public import WaveTurbulence.Foundations.RegAsymp.SingularRootRecursion

/-! # Exact original source momentum kernel at order zero -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links Reg ApproxNT

/-- The source well-formedness rule excludes a type2 code with two empty
chains; hence a well-formed order-zero couple is literally trivial. -/
theorem regCpl_eq_triv_of_wf_size_zero (Q : RegCpl) (hwf : Q.wf = true) (hs : Q.size = 0) :
    Q = .triv := by
  cases Q with
  | triv => rfl
  | type1 c Q₁ Q₂ Q₃ => simp only [RegCpl.size] at hs; omega
  | type2 Xp Xm Qlp =>
    cases Xp with
    | nil =>
      cases Xm with
      | nil => simp only [RegCpl.wf,RegChain.isNil,Bool.and_true,Bool.not_true,
          Bool.and_false,Bool.false_eq_true] at hwf
      | pair m Qr Qg inner rest =>
        simp only [RegCpl.size,RegChain.size] at hs
        omega
    | pair m Qr Qg inner rest =>
      simp only [RegCpl.size,RegChain.size] at hs
      omega

/-- The original source leaf product of the trivial couple is F(k). -/
theorem source_input_triv {G : Garden 2} (hQ : RegCpl.triv.Decodes G) (hG : IsCouple G)
    {d : ℕ} (F : Mom d → ℂ) (k : Mom d)
    (x : Fin RegCpl.triv.links.length → Fin 2 → Mom d) :
    (∏ a, F ((coupleMomentumData hQ hG).inputMomentum k x a)) = F k := by
  rw [prod_source_input_eq_cplLeafProduct hQ hG,cplLeafProduct_triv]

/-- The original zero-order singular factor agrees with the literal
recursive B2 Mstar factor; no positive-order localization is invoked. -/
theorem singInt_source_triv_eq_Mstar {G : Garden 2} (hQ : RegCpl.triv.Decodes G) (hG : IsCouple G)
    {d : ℕ} (F : Mom d → ℝ) (Z : Finset (Fin 2 × TTree.Path)) (k : Mom d)
    (J : Finset (Fin RegCpl.triv.links.length)) :
    singInt J (fun x y => ∏ a, ((F ((coupleMomentumData hQ hG).inputMomentum k
      (fun j i => if i=0 then x j else y j) a)):ℂ)) = (RegCpl.triv.Mstar F Z (0,[]) (1,[]) k:ℂ) := by
  have he : (fun (x y : Fin RegCpl.triv.links.length → Mom d) =>
      ∏ a, ((F ((coupleMomentumData hQ hG).inputMomentum k
        (fun j i => if i=0 then x j else y j) a)):ℂ)) = fun _ _ => (F k:ℂ) := by
    funext x y
    exact source_input_triv hQ hG (fun k => (F k:ℂ)) k _
  rw [he]
  rfl

end WaveTurbulence.RegAsymp
