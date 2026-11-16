module

public import MMP.AlgebraicGeometry.Divisor.RestrictOpen

/-!
# Ideals of prime divisors and of supports on an open subscheme

Let `U` be an open of a scheme `X`. The pullback along `U ⟶ X` of the reduced structure on a
closed subset `T ⊆ X` is the reduced structure on `T ∩ U`. Hence the ideal sheaf of a prime
divisor `E` of `U` is the pullback of the ideal sheaf of the prime divisor of `X` with the same
generic point, and the ideal sheaf of the support of the restriction `D|_U` of a divisor `D` of
`X` is the pullback of the ideal sheaf of `Supp D`. On an affine open `O ⊆ U` of `X`, whose trace
on `U` is affine, the restriction `Γ(X, O) → Γ(U, O)` identifies the ideals of `I` and of its
pullback.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.comap_vanishingIdeal_eq`: the pullback of a vanishing
  ideal along an open immersion is the vanishing ideal of the preimage.
* `MMP.FourfoldProofs.FractionalLogComplexProof.comap_idealSheaf_primeDivisorOfOpens`: the ideal sheaf
  of a prime divisor of `U` is the pullback of the ideal sheaf of the corresponding prime divisor
  of `X`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.suppIdeal_restrictDivisor`: the support ideal of `D|_U`
  is the pullback of the support ideal of `D`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.app_mem_ideal_comap_iff`: on an affine open `O ≤ U`,
  restriction `Γ(X, O) → Γ(U, O)` maps exactly the elements of `I.ideal O` into the ideal of the
  pullback.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace MMP.FourfoldProofs.FractionalLogComplexProof

universe u

/-- **The pullback of the reduced structure on a closed subset along an open immersion is the
reduced structure on its preimage.** -/
theorem comap_vanishingIdeal_eq {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] (T : Closeds X) :
    (Scheme.IdealSheafData.vanishingIdeal T).comap f =
      Scheme.IdealSheafData.vanishingIdeal (T.preimage f.continuous) := by
  set I := Scheme.IdealSheafData.vanishingIdeal T
  have : IsReduced I.subscheme := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal T
  have : IsReduced (Limits.pullback f I.subschemeι) :=
    isReduced_of_isOpenImmersion (Limits.pullback.snd f I.subschemeι)
  have : IsReduced (I.comap f).subscheme := isReduced_of_isOpenImmersion (I.comapIso f).hom
  refine (I.comap f).eq_vanishingIdeal_of_isReduced_subscheme _ ?_
  rw [Scheme.IdealSheafData.support_comap,
    show I.support = T from Closeds.ext (Scheme.IdealSheafData.coe_support_vanishingIdeal T)]

variable {X : Scheme.{u}} (U : X.Opens)

/-- **The ideal sheaf of a prime divisor of an open subscheme** is the pullback of the ideal
sheaf of the prime divisor of the ambient scheme with the same generic point. -/
theorem comap_idealSheaf_primeDivisorOfOpens (E : MMP.Mori.PrimeDivisor U) :
    (primeDivisorOfOpens U E).idealSheaf.comap U.ι = E.idealSheaf := by
  have := E.integral
  have := (primeDivisorOfOpens U E).integral
  refine (congrArg (Scheme.IdealSheafData.comap · U.ι)
    ((primeDivisorOfOpens U E).idealSheaf.eq_vanishingIdeal_of_isReduced_subscheme _ rfl)).trans
    ((comap_vanishingIdeal_eq U.ι _).trans ((congrArg _ ?_).trans
      (E.idealSheaf.eq_vanishingIdeal_of_isReduced_subscheme _ rfl).symm))
  exact Closeds.ext (Set.ext fun x => mem_support_primeDivisorOfOpens_iff U E x)

/-- **The ideal sheaf of the support of the restriction** is the pullback of the ideal sheaf of
the support. -/
theorem suppIdeal_restrictDivisor {R : Type*} [Zero R] (D : MMP.Mori.DivisorWithCoeffs R X) :
    (restrictDivisor U D).suppIdeal = D.suppIdeal.comap U.ι := by
  refine Eq.trans ?_ (comap_vanishingIdeal_eq U.ι D.supp).symm
  exact congrArg Scheme.IdealSheafData.vanishingIdeal
    (Closeds.ext (Set.ext fun x => mem_supp_restrictDivisor_iff U D x))

/-- **On an affine open `O ⊆ U`, restriction to `U` identifies the ideals of `I` and of its
pullback.** -/
theorem app_mem_ideal_comap_iff (I : X.IdealSheafData) {O : X.Opens} (hO : IsAffineOpen O)
    (hOU : O ≤ U) (hO' : IsAffineOpen (U.ι ⁻¹ᵁ O)) (g : Γ(X, O)) :
    (U.ι.app O).hom g ∈ (I.comap U.ι).ideal ⟨U.ι ⁻¹ᵁ O, hO'⟩ ↔ g ∈ I.ideal ⟨O, hO⟩ := by
  have hO'' : U.ι ''ᵁ (U.ι ⁻¹ᵁ O) = O := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hOU
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Ideal.mem_comap]
  have e : (U.ι.appIso (U.ι ⁻¹ᵁ O)).inv.hom ((U.ι.app O).hom g) =
      X.presheaf.map (homOfLE hO''.le).op g :=
    congrArg (fun φ => φ.hom g) (Scheme.Hom.app_appIso_inv U.ι O)
  rw [e]
  refine ⟨fun h => ?_, fun h => I.ideal_le_comap_ideal
    (U := ⟨_, hO'.image_of_isOpenImmersion U.ι⟩) (V := ⟨O, hO⟩) hO''.le h⟩
  have h2 := I.ideal_le_comap_ideal (U := ⟨O, hO⟩)
    (V := ⟨_, hO'.image_of_isOpenImmersion U.ι⟩) hO''.ge h
  rwa [Ideal.mem_comap, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    Subsingleton.elim (_ ≫ _) (𝟙 (op O)), CategoryTheory.Functor.map_id,
    ConcreteCategory.id_apply] at h2

end MMP.FourfoldProofs.FractionalLogComplexProof
