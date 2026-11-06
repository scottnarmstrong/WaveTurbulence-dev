/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafFam
public import WaveTurbulence.Foundations.Spine.RA1LW.Base
public import WaveTurbulence.Foundations.Spine.RA1LW.SourcePairEnumeration
public import WaveTurbulence.Foundations.RegAsymp.SingularRootRecursion

/-! # Exact original source momentum kernel at order zero -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
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
    {d : ℕ} (H : LGSpine.LeafProfiles 2 d) (k : Mom d)
    (x : Fin RegCpl.triv.links.length → Fin 2 → Mom d) :
    (∏ a, leafFam hQ hG H a ((coupleMomentumData hQ hG).inputMomentum k x a)) = (H (0,[]) k : ℂ) := by
  change (∏ a, addrFam H (plusLeafEquiv hQ hG a).val.1 ((coupleMomentumData hQ hG).inputMomentum k x a)) = _
  rw [prod_source_input_eq_cplLeafProduct hQ hG (addrFam H),cplLeafProduct_triv]
  rfl

/-- The original zero-order singular factor agrees with the literal
recursive B2 Mstar factor; no positive-order localization is invoked. -/
theorem singInt_source_triv_eq_Mstar {G : Garden 2} (hQ : RegCpl.triv.Decodes G) (hG : IsCouple G)
    {d : ℕ} (H : LGSpine.LeafProfiles 2 d) (Z : Finset (Fin 2 × TTree.Path)) (k : Mom d)
    (J : Finset (Fin RegCpl.triv.links.length)) :
    singInt J (fun x y => ∏ a, leafFam hQ hG H a ((coupleMomentumData hQ hG).inputMomentum k
      (fun j i => if i=0 then x j else y j) a)) =
      (LGSpine.LeafApp.cplMstar H Z RegCpl.triv (0,[]) (1,[]) k:ℂ) := by
  have he : (fun (x y : Fin RegCpl.triv.links.length → Mom d) =>
      ∏ a, leafFam hQ hG H a ((coupleMomentumData hQ hG).inputMomentum k
        (fun j i => if i=0 then x j else y j) a)) = fun _ _ => (H (0,[]) k : ℂ) := by
    funext x y
    exact source_input_triv hQ hG H k _
  rw [he]
  rfl

end WaveTurbulence.RA1Leafwise
