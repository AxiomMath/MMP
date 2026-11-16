module

public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.AffineOpenDeRhamSquare
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.HodgeClassShifted
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.SchemeShortExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedModuleFlat
public import StacksFrontier.AlgebraicGeometry.CartierConormal.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionIntegral
public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentKernelOnSite

/-!
# The canonical map on differential forms in degree one

For a commutative square `f ≫ p = p' ≫ g` of schemes, the canonical homomorphism of sheaves of
graded algebras `⋀ Ω_{X/S} ⟶ f_*(⋀ Ω_{X'/S'})` of [Stacks, Tag 07HX] is, in degree one, the
canonical map `Ω_{X/S} ⟶ f_* Ω_{X'/S'}` on relative differentials of [Stacks, Tag 01UV]
(the adjoint transpose of `f^*Ω_{X/S} ⟶ Ω_{X'/S'}`), read through the degree-one generators
`Ω ≅ ⋀¹Ω` of both exterior algebras. In particular a one-form pulls back to zero exactly when
its image under the map on relative differentials is zero. For a closed immersion `i` and
`p' = i ≫ p`, `g = 𝟙`, that map is the right arrow of the conormal sequence
`𝒞_{Z/X} ⟶ i^*Ω_{X/S} ⟶ Ω_{Z/S}` of [Stacks, Tag 01UZ]
(`Stacks.ConormalSequenceRight.conormalShortComplex`).

## Main results

* `MMP.DeRham.deRhamFormsPushforwardSections_one_exteriorGenerator`: the pull-back of the
  one-form attached to a section `s` of `Ω_{X/S}` is the one-form attached to the image of `s`
  under the map on relative differentials.
* `MMP.DeRham.deRhamFormsPushforwardSections_one_eq_zero_iff`: a one-form pulls back to zero
  if and only if its image under the map on relative differentials is zero.
* `MMP.DeRham.unit_app_eq_zero_of_deRhamFormsPushforwardSections_eq_zero`: for an immersion
  `i : Z ⟶ X` with `Z` smooth and no global conormal sections, a one-form pulling back to zero on
  `Z` restricts to zero in `Γ(Z, i^*Ω¹_X)`.
* `MMP.DeRham.subsingleton_conormal_sections_zeroScheme`: the conormal sheaf of the zero scheme
  of a nonzero section `s` of an invertible `M` on an integral scheme is `i^*M^∨`, so it has no
  global sections when `i^*M^∨` has none.

## References

* [Stacks, Tags 01UV, 01UZ, 07HX]
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.AffineOpenDeRham

universe u

namespace MMP.DeRham

variable {X' X S' S : Scheme.{u}} (f : X' ⟶ X) (p : X ⟶ S) (p' : X' ⟶ S') (g : S' ⟶ S)

/-- **The canonical map on forms in degree one is the canonical map on differentials.** The
pull-back of the one-form attached to a local section `s` of `Ω_{X/S}` by the degree-one
generator is the one-form attached to the image of `s` under the adjoint transpose
`Ω_{X/S} ⟶ f_*Ω_{X'/S'}` of the canonical map `f^*Ω_{X/S} ⟶ Ω_{X'/S'}` of Tag 01UV. -/
theorem deRhamFormsPushforwardSections_one_exteriorGenerator (hcomm : f ≫ p = p' ≫ g)
    {U : X.Opens} (s : Γ(Scheme.Hom.relativeDifferentials p, U)) :
    deRhamFormsPushforwardSections f p p' g hcomm 1
        ((Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials p)).val.app (op U)
          s) =
      (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials p')).val.app
        (op (f ⁻¹ᵁ U))
        (((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv _ _
          (Scheme.Hom.relativeDifferentialsMap f p p' g hcomm)).val.app (op U) s) := by
  have hext := SheafOfModules.GradedAlgebra.IsExteriorAlgebra.desc_extends
      (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (Scheme.Hom.relativeDifferentials p))
      (SheafOfModules.GradedAlgebra.pushforwardRingedSpace f.toLRSHom.toShHom
        (Scheme.Hom.relativeDifferentialFormsAlgebra p'))
      (SheafOfModules.GradedAlgebra.pushforwardGenerator f.toLRSHom.toShHom
        (Scheme.Hom.pushforwardFormsGenerator f p p' g hcomm))
      (SheafOfModules.GradedAlgebra.squareZero_pushforwardGenerator _
        (Scheme.Hom.squareZero_pushforwardFormsGenerator f p p' g hcomm))
  refine (congrArg (fun h ↦ h.val.app (op U) s) hext).trans ?_
  refine (SheafOfModules.GradedAlgebra.pushforwardGenerator_val_app f.toLRSHom.toShHom
    (Scheme.Hom.pushforwardFormsGenerator f p p' g hcomm) (op U) _).trans ?_
  rw [SheafOfModules.GradedAlgebra.homEquiv_val_app f.toLRSHom.toShHom
    (Scheme.Hom.relativeDifferentialsMap f p p' g hcomm) (op U) s]
  rfl

/-- **A one-form pulls back to zero exactly when its image in the relative differentials of the
source is zero.** Here `ω` is read as a section of `Ω_{X/S}` through the inverse of the
degree-one generator `Ω_{X/S} ≅ ⋀¹Ω_{X/S}`, and its image is taken under the adjoint transpose
of the canonical map `f^*Ω_{X/S} ⟶ Ω_{X'/S'}` of Tag 01UV. -/
theorem deRhamFormsPushforwardSections_one_eq_zero_iff (hcomm : f ≫ p = p' ≫ g)
    {U : X.Opens} (ω : Γ(Scheme.Hom.relativeDifferentialForms p ((1 : ℕ) : ℤ), U)) :
    deRhamFormsPushforwardSections f p p' g hcomm 1 ω = 0 ↔
      ((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv _ _
          (Scheme.Hom.relativeDifferentialsMap f p p' g hcomm)).val.app (op U)
        ((@inv _ _ _ _ (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials p))
          (Scheme.Hom.isIso_exteriorGenerator_relativeDifferentials p)).val.app (op U) ω) = 0 := by
  have := Scheme.Hom.isIso_exteriorGenerator_relativeDifferentials p
  have := Scheme.Hom.isIso_exteriorGenerator_relativeDifferentials p'
  have hω : (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials p)).val.app (op U)
      ((inv (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials p))).val.app
        (op U) ω) = ω :=
    congrArg (fun h ↦ h.val.app (op U) ω)
      (IsIso.inv_hom_id (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials p)))
  have hinv : ∀ t, (inv (Scheme.Modules.exteriorGenerator
      (Scheme.Hom.relativeDifferentials p'))).val.app (op (f ⁻¹ᵁ U))
        ((Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials p')).val.app
          (op (f ⁻¹ᵁ U)) t) = t := fun t ↦
    congrArg (fun k ↦ k.val.app (op (f ⁻¹ᵁ U)) t)
      (IsIso.hom_inv_id (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials p')))
  rw [(congrArg (deRhamFormsPushforwardSections f p p' g hcomm 1) hω).symm.trans
    (deRhamFormsPushforwardSections_one_exteriorGenerator f p p' g hcomm _)]
  exact ⟨fun h ↦ (hinv _).symm.trans ((congrArg ((inv (Scheme.Modules.exteriorGenerator
      (Scheme.Hom.relativeDifferentials p'))).val.app (op (f ⁻¹ᵁ U))) h).trans (map_zero _)),
    fun h ↦ (congrArg _ h).trans (map_zero _)⟩

/-- **A one-form vanishing on an immersed subscheme with no conormal sections restricts to zero.**
Let `i : Z ⟶ X` be an immersion over `S` with `Z` smooth over `S`, and suppose the conormal sheaf
`𝒞_{Z/X}` (the first term of `Stacks.ConormalSequenceRight.conormalShortComplex`) has no nonzero
global sections. If a global one-form `ω` on `X` pulls back to zero on `Z` (its pull-back, a
section over `i⁻¹X`, read over `Z`), then its restriction
`i^*ω`, a section of `i^*Ω¹_{X/S}`, is zero: the pull-back is the image of `i^*ω` under the right
arrow `i^*Ω_{X/S} ⟶ Ω_{Z/S}` of the conormal sequence, whose kernel is `𝒞_{Z/X}`. -/
theorem unit_app_eq_zero_of_deRhamFormsPushforwardSections_eq_zero {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsImmersion i] (q : Z ⟶ S) (hq : i ≫ p = q) (hcomm : i ≫ p = q ≫ 𝟙 S)
    (hsm : Smooth q)
    (hC : Subsingleton Γ((Stacks.ConormalSequenceRight.conormalShortComplex i p).X₁, ⊤))
    (ω : Γ(Scheme.Hom.relativeDifferentialForms p ((1 : ℕ) : ℤ), ⊤))
    (h : (Scheme.Hom.relativeDifferentialForms q ((1 : ℕ) : ℤ)).presheaf.map
      (homOfLE (fun _ _ ↦ trivial : (⊤ : Z.Opens) ≤ i ⁻¹ᵁ ⊤)).op
        (deRhamFormsPushforwardSections i p q (𝟙 S) hcomm 1 ω) = 0) :
    ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
      (Scheme.Hom.relativeDifferentialForms p ((1 : ℕ) : ℤ))).val.app (op ⊤) ω = 0 := by
  have hid : ∀ (φ : op (i ⁻¹ᵁ ⊤) ⟶ op (i ⁻¹ᵁ ⊤))
      (x : Γ(Scheme.Hom.relativeDifferentialForms q ((1 : ℕ) : ℤ), i ⁻¹ᵁ ⊤)),
      (Scheme.Hom.relativeDifferentialForms q ((1 : ℕ) : ℤ)).presheaf.map φ x = x := fun φ x ↦ by
    rw [Subsingleton.elim φ (𝟙 _), CategoryTheory.Functor.map_id]
    rfl
  replace h : deRhamFormsPushforwardSections i p q (𝟙 S) hcomm 1 ω = 0 := (hid _ _).symm.trans h
  subst hq
  have := Scheme.Hom.isIso_exteriorGenerator_relativeDifferentials p
  rw [deRhamFormsPushforwardSections_one_eq_zero_iff] at h
  have h2 := (SheafOfModules.GradedAlgebra.homEquiv_val_app i.toLRSHom.toShHom
    (Scheme.Hom.relativeDifferentialsMap i p (i ≫ p) (𝟙 S) hcomm) (op ⊤) _).symm.trans h
  obtain ⟨y, hy⟩ := SheafOfModules.exists_of_shortExact_sections
    (Stacks.ConormalSequenceRight.conormalShortComplex_shortExact i p hsm) (op (i ⁻¹ᵁ ⊤)) _ h2
  have hy0 : y = 0 := @Subsingleton.elim _ hC y 0
  rw [hy0, map_zero] at hy
  have hω : (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials p)).val.app
      (op ⊤) ((inv (Scheme.Modules.exteriorGenerator
        (Scheme.Hom.relativeDifferentials p))).val.app (op ⊤) ω) = ω :=
    congrArg (fun h ↦ h.val.app (op ⊤) ω)
      (IsIso.inv_hom_id (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials p)))
  have hnat := congrArg (fun k ↦ k.val.app (op ⊤) ((inv (Scheme.Modules.exteriorGenerator
      (Scheme.Hom.relativeDifferentials p))).val.app (op ⊤) ω))
    ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.naturality
      (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials p)))
  refine (congrArg _ hω).symm.trans ?_
  refine hnat.trans ?_
  exact (congrArg (fun t ↦ ((Scheme.Modules.pullback i ⋙ Scheme.Modules.pushforward i).map
    (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials p))).val.app (op ⊤) t)
      hy.symm).trans (map_zero _)

/-- **The conormal sheaf of the zero scheme of a section has no global sections when the
restricted dual has none.** Let `X` be integral, `M` invertible, `s ≠ 0` a global section of `M`
and `i : Z(s) ⟶ X` its zero scheme. The conormal sheaf `𝒞_{Z/X}` is `i^*ℐ_{Z(s)}` and
`ℐ_{Z(s)} ≅ M^∨` (evaluation at `s`, an isomorphism as `s` is a nonzerodivisor on the integral
scheme `X`), so `𝒞_{Z/X} ≅ i^*N` for any `N ≅ M^∨`. -/
theorem subsingleton_conormal_sections_zeroScheme [IsIntegral X] (M : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M] (s : Γ(M, ⊤))
    (hs : s ≠ 0) (N : X.Modules)
    (eN : N ≅ Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf M)
    (hN : Subsingleton Γ((Scheme.Modules.pullback (zeroScheme X M s).subschemeι).obj N, ⊤)) :
    Subsingleton Γ((Stacks.ConormalSequenceRight.conormalShortComplex
      (zeroScheme X M s).subschemeι p).X₁, ⊤) := by
  have := isIso_zeroSchemeIdealModuleHom M s
    (fun U _ _ h ↦ eq_of_smul_map_le_top_eq_of_isIntegral M s hs U h)
  let i := (zeroScheme X M s).subschemeι
  let eC : (Stacks.ConormalSequenceRight.conormalShortComplex i p).X₁ ≅
      (Scheme.Modules.pullback i).obj N :=
    (RingedSpaceModuleAdjunction.modulePullback i.liftCoborder.toLRSHom.toShHom).mapIso
      (Stacks.SheafOfModules.kernelIsoKerObj _).symm ≪≫
      Stacks.CartierConormal.conormalSheafIsoNegativeTwist (zeroScheme X M s) ≪≫
      (Scheme.Modules.pullback i).mapIso
        ((asIso (zeroSchemeIdealModuleHom M s)).symm ≪≫ eN.symm)
  refine ⟨fun a b ↦ ?_⟩
  have ha : eC.inv.val.app (op ⊤) (eC.hom.val.app (op ⊤) a) = a :=
    congrArg (fun k ↦ k.val.app (op ⊤) a) eC.hom_inv_id
  have hb : eC.inv.val.app (op ⊤) (eC.hom.val.app (op ⊤) b) = b :=
    congrArg (fun k ↦ k.val.app (op ⊤) b) eC.hom_inv_id
  rw [← ha, ← hb, @Subsingleton.elim _ hN (eC.hom.val.app (op ⊤) a) (eC.hom.val.app (op ⊤) b)]

end MMP.DeRham
