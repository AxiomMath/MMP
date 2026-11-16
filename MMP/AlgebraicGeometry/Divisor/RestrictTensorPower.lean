module

public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafTensor
public import MMP.AlgebraicGeometry.Positivity.SemiampleSections
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic

/-!
# Tensor powers of a divisorial sheaf restricted to an open subscheme

Let `X` be a quasi-compact locally Noetherian normal scheme, `W ⊆ X` an open and `L` a Cartier
divisor on `X`. Write `𝒪(D)|_W` for the restriction of the divisorial sheaf of a divisor `D` to
the open subscheme `W`. Multiplication of rational functions gives morphisms
`𝒪(D)|_W ⊗ 𝒪(D')|_W ⟶ 𝒪(D + D')|_W`, isomorphisms when `D` and `D'` are Cartier, and iterating
them identifies the tensor powers `(𝒪(L)|_W)^{⊗ n}` with `𝒪(nL)|_W`. Under this identification
the section ring `⨁_n Γ(W, (𝒪(L)|_W)^{⊗ n})` becomes the ring `⨁_n Γ(W, 𝒪(nL))` of rational
functions: global sections correspond to divisorial sections over `W`, and the product of
sections is the product of rational functions.

## Main definitions

* `MMP.Mori.Divisor.restrictSheaf`: `𝒪(D)|_W`.
* `MMP.Mori.Divisor.restrictTensorMul`: the multiplication `𝒪(D)|_W ⊗ 𝒪(D')|_W ⟶ 𝒪(D'')|_W`
  for `D + D' ≤ D''`.
* `MMP.Mori.Divisor.restrictMulSection`: multiplication by a section of `𝒪(A)` over `W`, as a
  morphism `𝒪(D)|_W ⟶ 𝒪(D')|_W` for `A + D ≤ D'`.
* `MMP.Mori.Divisor.natTensorPowRestrictIso`: `(𝒪(L)|_W)^{⊗ n} ≅ 𝒪(nL)|_W` for Cartier `L`.
* `MMP.Mori.Divisor.powSectionsRestrict`: the divisorial section of `𝒪(nL)` over `W` attached to
  a global section of `(𝒪(L)|_W)^{⊗ n}`.

## Main results

* `MMP.Mori.Divisor.isIso_restrictTensorMul`: the multiplication map is an isomorphism for
  Cartier divisors.
* `MMP.Mori.Divisor.mulMap_natTensorPowRestrictIso`: under the identification, multiplication by
  a section of a tensor power is multiplication by the corresponding rational function.
* `MMP.Mori.Divisor.powSectionsRestrict_mul`, `powSectionsRestrict_one`,
  `powSectionsRestrict_add`, `powSectionsRestrict_unitScalar`, `powSectionsRestrict_surjective`:
  the correspondence of sections is additive, multiplicative, unital, compatible with the
  functions on `W`, and onto.

## Implementation notes

The tensor product in which the section ring is written is the monoidal structure
`Stacks.SheafInternalHom.schemeMonoidalCategory`; the multiplication of sections is built in the
sheafified tensor product `Stacks.SheafOfModules.Tensor.sheafTensor`, from the bilinear product
of sections by the universal properties of the objectwise tensor product and of sheafification,
and the two tensor products are compared by
`MMP.SemiampleSections.tensorRightIsoSheafTensorRight`. That the multiplication is an
isomorphism is not checked on trivializations: near a point where `ψ` is a local equation of `D`
it is locally surjective, and an epimorphism of invertible sheaves is an isomorphism.

## References

* [R. Hartshorne, *Algebraic geometry*][Har77], II.6.13
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace MMP.Mori.Divisor

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] (W : X.Opens)

/-- `𝒪_X(D)` restricted to the open subscheme `W`. -/
noncomputable abbrev restrictSheaf (D : Divisor X) : W.toScheme.Modules :=
    D.divisorialSheaf.restrict W.ι

/-- Multiplication of sections of restricted divisorial sheaves, on the presheaf tensor product. -/
noncomputable def restrictTensorMulPresheaf {D D' D'' : Divisor X} (h : D + D' ≤ D'') :
    PresheafOfModules.tensorObj (O := W.toScheme.presheaf) (restrictSheaf W D).val (restrictSheaf W
        D').val ⟶
    (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
      (𝟙 W.toScheme.ringCatSheaf.obj)).obj (restrictSheaf W D'') :=
  PresheafOfModules.tensorMk
    (fun V φ ψ => (Submodule.inclusion (Divisor.divisorialSubmodule_mono h _)
      (Divisor.divisorialMul (W.ι ''ᵁ V.unop) φ ψ) : D''.divisorialSubmodule (W.ι ''ᵁ V.unop)))
    (fun _ _ _ _ => Subtype.ext (funext fun _ => add_mul _ _ _))
    (fun _ _ _ _ => Subtype.ext (funext fun _ => mul_assoc _ _ _))
    (fun _ _ _ _ => Subtype.ext (funext fun _ => mul_add _ _ _))
    (fun _ _ _ _ => Subtype.ext (funext fun _ => mul_left_comm _ _ _))
    (fun _ _ _ _ _ => rfl)

/-- `𝒪(D)|_W ⊗ 𝒪(D')|_W ⟶ 𝒪(D'')|_W`, for `D + D' ≤ D''`. -/
noncomputable def restrictTensorMul {D D' D'' : Divisor X} (h : D + D' ≤ D'') :
    ((Stacks.SheafOfModules.Tensor.sheafTensor W.toScheme.toRingedSpace.sheaf).obj
      (restrictSheaf W D)).obj (restrictSheaf W D') ⟶ restrictSheaf W D'' :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 _)).homEquiv _ _).symm (restrictTensorMulPresheaf
      W h)

/-- Multiplication by a section `σ` of `𝒪(A)` over `ι(⊤)`, from `𝒪(D)|_W` to `𝒪(D')|_W`. -/
noncomputable def restrictMulSection {A D D' : Divisor X} (h : A + D ≤ D')
    (σ : A.divisorialSubmodule (W.ι ''ᵁ ⊤)) : restrictSheaf W D ⟶ restrictSheaf W D' :=
  ⟨PresheafOfModules.homMk
    { app V := AddCommGrpCat.ofHom
        { toFun φ := (Submodule.inclusion (Divisor.divisorialSubmodule_mono h _)
            (Divisor.divisorialMul (W.ι ''ᵁ V.unop)
              (A.divisorialRestrict (homOfLE (W.ι.image_mono le_top)) σ) φ) :
              D'.divisorialSubmodule (W.ι ''ᵁ V.unop))
          map_zero' := Subtype.ext (funext fun _ => mul_zero _)
          map_add' _ _ := Subtype.ext (funext fun _ => mul_add _ _ _) }
      naturality _ _ _ := by
        ext φ
        exact Subtype.ext (funext fun _ => rfl) }
    fun _ _ _ => Subtype.ext (funext fun _ => mul_left_comm _ _ _)⟩

/-- `restrictTensorMul` on the image of a pure tensor. -/
theorem restrictTensorMul_unit {D D' D'' : Divisor X} (h : D + D' ≤ D'') (V : W.toScheme.Opensᵒᵖ)
    (φ : (restrictSheaf W D).val.obj V) (ψ : (restrictSheaf W D').val.obj V) :
    PresheafOfModules.Hom.app (restrictTensorMul W h).val V
      (PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
        (𝟙 W.toScheme.ringCatSheaf.obj)).unit.app
        (PresheafOfModules.tensorObj (O := W.toScheme.presheaf) (restrictSheaf W D).val
          (restrictSheaf W D').val)) V (φ ⊗ₜ ψ)) =
      (Submodule.inclusion (Divisor.divisorialSubmodule_mono h _)
        (Divisor.divisorialMul (W.ι ''ᵁ V.unop) φ ψ) : D''.divisorialSubmodule (W.ι ''ᵁ V.unop)) :=
  PresheafOfModules.hom_congr_apply'
    (PresheafOfModules.sheafificationAdjunction_unit_comp_homEquiv_symm
      (𝟙 W.toScheme.ringCatSheaf.obj) (restrictTensorMulPresheaf W h)) V (φ ⊗ₜ ψ)

/-- Multiplication by `σ` commutes with the multiplication maps. -/
theorem restrictMulSection_restrictTensorMul {A D D' E E' L : Divisor X} (hσ : A + D ≤ E) (h1 : D +
    L ≤ D')
    (h2 : E + L ≤ E') (h3 : A + D' ≤ E') (σ : A.divisorialSubmodule (W.ι ''ᵁ ⊤)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor W.toScheme.toRingedSpace.sheaf).map
        (restrictMulSection W hσ σ)).app (restrictSheaf W L) ≫ restrictTensorMul W h2 =
            restrictTensorMul W h1 ≫ restrictMulSection W h3 σ := by
  change (PresheafOfModules.sheafification (𝟙 W.toScheme.ringCatSheaf.obj)).map
      (PresheafOfModules.tensorHom (O := W.toScheme.presheaf) (restrictMulSection W hσ σ).val
        (𝟙 (restrictSheaf W L).val)) ≫ restrictTensorMul W h2 = restrictTensorMul W h1 ≫
            restrictMulSection W h3 σ
  have key : PresheafOfModules.tensorHom (O := W.toScheme.presheaf) (restrictMulSection W hσ σ).val
        (𝟙 (restrictSheaf W L).val) ≫ restrictTensorMulPresheaf W h2 =
      restrictTensorMulPresheaf W h1 ≫ (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
        (𝟙 W.toScheme.ringCatSheaf.obj)).map (restrictMulSection W h3 σ) :=
    PresheafOfModules.tensorObj_hom_ext fun V x y => Subtype.ext (funext fun _ => mul_assoc _ _ _)
  exact ((PresheafOfModules.sheafificationAdjunction _).homEquiv_naturality_left_symm _
      _).symm.trans
    ((congrArg _ key).trans
      ((PresheafOfModules.sheafificationAdjunction _).homEquiv_naturality_right_symm _ _))

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- The image of `V ⊓ ι⁻¹ U₀` lies in `U₀`. -/
private theorem image_inf_preimage_le (V : W.toScheme.Opens) (U₀ : X.Opens) :
    W.ι ''ᵁ (V ⊓ W.ι ⁻¹ᵁ U₀) ≤ U₀ := by
  refine (W.ι.image_mono inf_le_right).trans ?_
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
  exact inf_le_right

/-- If `D` is Cartier, the multiplication map is an epimorphism. -/
theorem epi_restrictTensorMul {D D' : Divisor X} (hD : D.IsCartier) :
    Epi (restrictTensorMul W (le_refl (D + D'))) := by
  apply Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective
  refine (TopCat.Presheaf.isLocallySurjective_iff _).mpr fun V s x hx => ?_
  obtain ⟨U₀, hxU, ψ, hψ⟩ := hD (W.ι.base x)
  set V' : W.toScheme.Opens := V ⊓ W.ι ⁻¹ᵁ U₀
  have hU : ∀ E : MMP.Mori.PrimeDivisor X, (E.support ∩ ((W.ι ''ᵁ V' : X.Opens) : Set X)).Nonempty →
      (E.support ∩ (U₀ : Set X)).Nonempty := fun E h =>
    h.mono (Set.inter_subset_inter_right _ (image_inf_preimage_le W V U₀))
  have hV : ∀ E : MMP.Mori.PrimeDivisor X, (E.support ∩ ((W.ι ''ᵁ V' : X.Opens) : Set X)).Nonempty →
      (E.support ∩ ((W.ι ''ᵁ V : X.Opens) : Set X)).Nonempty := fun E h =>
    h.mono (Set.inter_subset_inter_right _ (W.ι.image_mono inf_le_left))
  let s' : (D + D').divisorialSubmodule (W.ι ''ᵁ V) := s
  let a : D.divisorialSubmodule (W.ι ''ᵁ V') :=
    ⟨fun Z => ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1, fun E h =>
      Or.inr (le_of_eq (by
        rw [PrimeDivisor.valuation_component, PrimeDivisor.ord_inv, hψ E (hU E h)]))⟩
  let b : D'.divisorialSubmodule (W.ι ''ᵁ V') :=
    ⟨fun Z => (ψ : RationalFunctions X) Z.1 *
        s'.1 ⟨Z.1, W.ι.image_mono inf_le_left Z.2⟩, fun E h =>
      (PrimeDivisor.OrdGE.mul (Or.inr (E.valuation_component ψ).ge)
        (s'.2 E (hV E h))).mono (le_of_eq (by
          rw [DivisorWithCoeffs.coeff_add, hψ E (hU E h)]; ring))⟩
  refine ⟨V', inf_le_left, ⟨PresheafOfModules.Hom.app
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 W.toScheme.ringCatSheaf.obj)).unit.app
      (PresheafOfModules.tensorObj (O := W.toScheme.presheaf) (restrictSheaf W D).val
        (restrictSheaf W D').val)) (op V')
      ((a : (restrictSheaf W D).val.obj (op V')) ⊗ₜ (b : (restrictSheaf W D').val.obj (op V'))),
          ?_⟩, hx, hxU⟩
  refine (restrictTensorMul_unit W (le_refl (D + D')) (op V') a b).trans (Subtype.ext (funext fun Z
      => ?_))
  change ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1 *
      ((ψ : RationalFunctions X) Z.1 * s'.1 ⟨Z.1, W.ι.image_mono inf_le_left Z.2⟩) =
    s'.1 ⟨Z.1, W.ι.image_mono inf_le_left Z.2⟩
  rw [← mul_assoc, ← Pi.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Pi.one_apply,
    one_mul]

variable [CompactSpace X]

/-- For a Cartier divisor `D`, the restriction `𝒪(D)|_W` is an invertible sheaf on `W`. -/
theorem isInvertibleModule_restrictSheaf {D : Divisor X} (hD : D.IsCartier) :
    Stacks.Ample.IsInvertibleModule W.toScheme (restrictSheaf W D) := by
  haveI := hD.isInvertibleModule_divisorialSheaf
  letI := Stacks.InvertiblePullback.isInvertibleModule_restrict W D.divisorialSheaf
  exact Stacks.AlgebraicGeometry.ProjAmpleTwist.isInvertibleModule_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app _ ≪≫
      (Stacks.ProjectiveBundleQuotients.pullbackIso W.ι).app _).symm

/-- For Cartier divisors `D`, `D'` with `D + D' = D''`, the multiplication
`𝒪(D)|_W ⊗ 𝒪(D')|_W ⟶ 𝒪(D'')|_W` is an isomorphism. -/
theorem isIso_restrictTensorMul {D D' D'' : Divisor X} (hD : D.IsCartier) (hD' : D'.IsCartier)
    (h : D + D' = D'') : IsIso (restrictTensorMul W h.le) := by
  subst h
  haveI := isInvertibleModule_restrictSheaf W hD
  haveI := isInvertibleModule_restrictSheaf W hD'
  haveI := epi_restrictTensorMul W (D' := D') hD
  exact @Stacks.Chow.GenuineChern.isIso_of_epi_of_isInvertible W.toScheme _ _ _
    (epi_restrictTensorMul W (D' := D') hD)
    (Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible W.toScheme.presheaf
      W.toScheme.ringCatSheaf.2 _ _)
    (isInvertibleModule_restrictSheaf W (hD.add hD'))

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

open MonoidalCategory Stacks.TensorPowers Stacks.GradedSections

/-- `𝒪_W ≅ 𝒪(0)|_W`. -/
noncomputable def restrictSheafZeroIso : 𝟙_ W.toScheme.Modules ≅ restrictSheaf W 0 :=
  Stacks.SectionRingGeometric.unitComparison W.toScheme ≪≫
    (Scheme.Modules.restrictUnitIso W.ι).symm ≪≫
    (Scheme.Modules.restrictFunctor W.ι).mapIso Divisor.divisorialSheafZeroIso.symm

/-- A section of `𝒪(D)|_W` over `V`, read as a divisorial section over `ι(V)`. -/
noncomputable def restrictSection {D : Divisor X} {V : W.toScheme.Opens} (x : Γ(restrictSheaf W D,
    V)) :
    D.divisorialSubmodule (W.ι ''ᵁ V) := x

omit [CompactSpace X] in
/-- Sections of `𝒪(D)|_W` with the same underlying rational section are equal. -/
theorem restrictSection_inj {D : Divisor X} {V : W.toScheme.Opens} {x y : Γ(restrictSheaf W D, V)}
    (h : (restrictSection W x).1 = (restrictSection W y).1) : x = y :=
  Subtype.ext h

omit [CompactSpace X] in
/-- Transport along an equality `D = D'` does not change the underlying rational section. -/
theorem restrictSection_eqToHom {D D' : Divisor X} (h : D = D') {V : W.toScheme.Opens}
    (x : Γ(restrictSheaf W D, V)) :
    (restrictSection W ((eqToHom (congrArg (restrictSheaf W) h)).app V x)).1 = (restrictSection W
        x).1 := by
  subst h; rfl

omit [CompactSpace X] in
/-- Under `restrictSheafZeroIso`, the unit global section corresponds to the rational function
`1`. -/
theorem restrictSection_restrictSheafZeroIso :
    (restrictSection W (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv W.toScheme _
      (restrictSheafZeroIso W).hom)).1 = 1 := by
  rw [Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv_apply]
  have h : (Stacks.SectionRingGeometric.unitComparison W.toScheme).inv ≫ (restrictSheafZeroIso
      W).hom =
      (Scheme.Modules.restrictUnitIso W.ι).inv ≫ (Scheme.Modules.restrictFunctor W.ι).map
        (Divisor.structureSheafToDivisorialSheaf (le_refl (0 : Divisor X))) := by
    simp [restrictSheafZeroIso, Divisor.divisorialSheafZeroIso]
    rfl
  rw [h]
  change ((Divisor.structureSheafToDivisorialSheaf (le_refl (0 : Divisor X))).app (W.ι ''ᵁ ⊤)
    ((W.ι.appIso ⊤).inv.hom 1)).1 = 1
  rw [Divisor.coe_structureSheafToDivisorialSheaf_app, map_one, map_one]

/-- The multiplication isomorphism. -/
noncomputable def restrictTensorIso {D D' D'' : Divisor X} (hD : D.IsCartier) (hD' : D'.IsCartier)
    (h : D + D' = D'') :
    ((Stacks.SheafOfModules.Tensor.sheafTensor W.toScheme.toRingedSpace.sheaf).obj
      (restrictSheaf W D)).obj (restrictSheaf W D') ≅ restrictSheaf W D'' :=
  haveI := isIso_restrictTensorMul W hD hD' h
  asIso (restrictTensorMul W h.le)

/-- The comparison of the two tensor products, at a restricted divisorial sheaf. -/
noncomputable def tensorRightRestrictSheafIso (A L : Divisor X) :
    (tensorRight (restrictSheaf W L)).obj (restrictSheaf W A) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor W.toScheme.toRingedSpace.sheaf).obj
        (restrictSheaf W A)).obj (restrictSheaf W L) :=
  (MMP.SemiampleSections.tensorRightIsoSheafTensorRight (restrictSheaf W L)).app (restrictSheaf W A)

omit [CompactSpace X] in
/-- `tensorRightRestrictSheafIso` is natural in morphisms `𝒪(A)|_W ⟶ 𝒪(B)|_W`. -/
@[reassoc]
theorem tensorRightRestrictSheafIso_naturality {A B : Divisor X} (L : Divisor X) (f : restrictSheaf
    W A ⟶ restrictSheaf W B) :
    (tensorRight (restrictSheaf W L)).map f ≫ (tensorRightRestrictSheafIso W B L).hom =
      (tensorRightRestrictSheafIso W A L).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor W.toScheme.toRingedSpace.sheaf).map f).app
          (restrictSheaf W L) :=
  (MMP.SemiampleSections.tensorRightIsoSheafTensorRight (restrictSheaf W L)).hom.naturality f

/-- `(𝒪(L)|_W)^{⊗ n} ≅ 𝒪(nL)|_W`. -/
noncomputable def natTensorPowRestrictIso {L : Divisor X} (hL : L.IsCartier) :
    (n : ℕ) → (natTensorPow (restrictSheaf W L) n ≅ restrictSheaf W (n • L))
  | 0 => restrictSheafZeroIso W ≪≫ eqToIso (congrArg (restrictSheaf W) (zero_nsmul L).symm)
  | n + 1 =>
    let e1 : natTensorPow (restrictSheaf W L) (n + 1) ≅ (tensorRight (restrictSheaf W L)).obj
        (restrictSheaf W (n • L)) :=
      (tensorRight (restrictSheaf W L)).mapIso (natTensorPowRestrictIso hL n)
    e1 ≪≫ tensorRightRestrictSheafIso W (n • L) L ≪≫ restrictTensorIso W (hL.nsmul n) hL
        (succ_nsmul L n).symm

/-- The section of `𝒪(kL)` attached to `s`. -/
noncomputable def powSectionsRestrict {L : Divisor X} (hL : L.IsCartier) {k : ℕ}
    (s : powSections (restrictSheaf W L) k) : (k • L).divisorialSubmodule (W.ι ''ᵁ ⊤) :=
  restrictSection W (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv W.toScheme _
    (s ≫ (natTensorPowRestrictIso W hL k).hom))

/-- The isomorphism `(𝒪(L)|_W)^{⊗ (n + 1)} ≅ 𝒪((n + 1)L)|_W` is the tensor product of the
isomorphism in degree `n` with `𝒪(L)|_W`, followed by the multiplication map. -/
theorem natTensorPowRestrictIso_succ_hom {L : Divisor X} (hL : L.IsCartier) (n : ℕ) :
    (natTensorPowRestrictIso W hL (n + 1)).hom = (tensorRight (restrictSheaf W L)).map
        (natTensorPowRestrictIso W hL n).hom ≫
      (tensorRightRestrictSheafIso W (n • L) L).hom ≫
        restrictTensorMul W (succ_nsmul L n).symm.le := by
  rw [natTensorPowRestrictIso]
  rfl

omit [CompactSpace X] in
private theorem restrictMulSection_step {P Q : W.toScheme.Modules} {L A₀ A B A' B' : Divisor X}
    (m : P ⟶ Q) (eP : P ⟶ restrictSheaf W A) (eQ : Q ⟶ restrictSheaf W B) (hσ : A₀ + A ≤ B)
    (h1 : A + L ≤ A') (h2 : B + L ≤ B') (h3 : A₀ + A' ≤ B')
    (σ : A₀.divisorialSubmodule (W.ι ''ᵁ ⊤)) (ih : m ≫ eQ = eP ≫ restrictMulSection W hσ σ) :
    (tensorRight (restrictSheaf W L)).map m ≫ (tensorRight (restrictSheaf W L)).map eQ ≫
        (tensorRightRestrictSheafIso W B L).hom ≫
        restrictTensorMul W h2 =
      ((tensorRight (restrictSheaf W L)).map eP ≫ (tensorRightRestrictSheafIso W A L).hom ≫
          restrictTensorMul W h1) ≫ restrictMulSection W h3 σ := by
  rw [← Functor.map_comp_assoc, ih, Functor.map_comp_assoc]
  simp only [Category.assoc]
  congr 1
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ restrictTensorMul W h2)
    (tensorRightRestrictSheafIso_naturality W L (restrictMulSection W hσ σ)))).trans
    ((Category.assoc _ _ _).trans (congrArg _ (restrictMulSection_restrictTensorMul W hσ h1 h2 h3
        σ)))

/-- Under `natTensorPowRestrictIso`, multiplication by a section `s` of `(𝒪(L)|_W)^{⊗ k}` is
multiplication by the rational function `powSectionsRestrict W hL s`. -/
theorem mulMap_natTensorPowRestrictIso {L : Divisor X} (hL : L.IsCartier) {k : ℕ} (s : powSections
    (restrictSheaf W L) k) :
    ∀ n : ℕ, mulMap s n ≫ (natTensorPowRestrictIso W hL (k + n)).hom =
      (natTensorPowRestrictIso W hL n).hom ≫ restrictMulSection W (add_nsmul L k n).symm.le
          (powSectionsRestrict W hL s)
  | 0 => by
    apply (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv W.toScheme _).injective
    refine Eq.trans ?_
        (Stacks.AlgebraicGeometry.ProperAmpleCohomology.schemeGlobalSectionsAddEquiv_comp
      W.toScheme (natTensorPowRestrictIso W hL 0).hom _).symm
    apply restrictSection_inj W
    have h0 : (restrictSection W (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv
        W.toScheme _
        (natTensorPowRestrictIso W hL 0).hom)).1 = 1 := by
      change (restrictSection W (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv
          W.toScheme _
        ((restrictSheafZeroIso W).hom ≫ eqToHom (congrArg (restrictSheaf W) (zero_nsmul
            L).symm)))).1 = 1
      rw [Stacks.AlgebraicGeometry.ProperAmpleCohomology.schemeGlobalSectionsAddEquiv_comp,
        restrictSection_eqToHom W (zero_nsmul L).symm, restrictSection_restrictSheafZeroIso]
    funext Z
    change (powSectionsRestrict W hL s).1 Z = (powSectionsRestrict W hL s).1 ⟨Z.1, _⟩ *
      (restrictSection W (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv W.toScheme _
        (natTensorPowRestrictIso W hL 0).hom)).1 Z
    rw [h0]
    exact (mul_one _).symm
  | n + 1 => by
    have h1 : (natTensorPowRestrictIso W hL (k + (n + 1))).hom = (tensorRight (restrictSheaf W
        L)).map (natTensorPowRestrictIso W hL (k + n)).hom ≫
        (tensorRightRestrictSheafIso W ((k + n) • L) L).hom ≫ restrictTensorMul W (succ_nsmul L (k
            + n)).symm.le :=
      natTensorPowRestrictIso_succ_hom W hL (k + n)
    rw [h1, natTensorPowRestrictIso_succ_hom]
    exact restrictMulSection_step W (mulMap s n) _ _ _ _ _ _ _ (mulMap_natTensorPowRestrictIso hL s
        n)

/-- In degree `0`, `natTensorPowRestrictIso` sends the unit section to the rational function
`1`. -/
theorem restrictSection_natTensorPowRestrictIso_zero {L : Divisor X} (hL : L.IsCartier) :
    (restrictSection W (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv W.toScheme _
      (natTensorPowRestrictIso W hL 0).hom)).1 = 1 := by
  change (restrictSection W (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv W.toScheme _
    ((restrictSheafZeroIso W).hom ≫ eqToHom (congrArg (restrictSheaf W) (zero_nsmul L).symm)))).1 =
        1
  rw [Stacks.AlgebraicGeometry.ProperAmpleCohomology.schemeGlobalSectionsAddEquiv_comp,
    restrictSection_eqToHom W (zero_nsmul L).symm, restrictSection_restrictSheafZeroIso]

/-- The unit section in degree `0` corresponds to the rational function `1`. -/
theorem powSectionsRestrict_one {L : Divisor X} (hL : L.IsCartier) :
    (powSectionsRestrict W hL (k := 0) (𝟙 (𝟙_ W.toScheme.Modules))).1 = 1 := by
  change (restrictSection W (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv W.toScheme _
    ((restrictSheafZeroIso W).hom ≫ eqToHom (congrArg (restrictSheaf W) (zero_nsmul L).symm)))).1 =
        1
  rw [Stacks.AlgebraicGeometry.ProperAmpleCohomology.schemeGlobalSectionsAddEquiv_comp,
    restrictSection_eqToHom W (zero_nsmul L).symm, restrictSection_restrictSheafZeroIso]

/-- `powSectionsRestrict` is additive. -/
theorem powSectionsRestrict_add {L : Divisor X} (hL : L.IsCartier) {k : ℕ} (s t : powSections
    (restrictSheaf W L) k) :
    (powSectionsRestrict W hL (s + t)).1 = (powSectionsRestrict W hL s).1 + (powSectionsRestrict W
        hL t).1 := by
  unfold powSectionsRestrict
  rw [Preadditive.add_comp, map_add]
  rfl

/-- The product of sections of tensor powers corresponds to the product of rational functions. -/
theorem powSectionsRestrict_mul {L : Divisor X} (hL : L.IsCartier) {k n : ℕ} (s : powSections
    (restrictSheaf W L) k)
    (t : powSections (restrictSheaf W L) n) :
    (powSectionsRestrict W hL (mul s t)).1 = (powSectionsRestrict W hL s).1 * (powSectionsRestrict
        W hL t).1 := by
  have h : mul s t ≫ (natTensorPowRestrictIso W hL (k + n)).hom =
      (t ≫ (natTensorPowRestrictIso W hL n).hom) ≫ restrictMulSection W (add_nsmul L k n).symm.le
          (powSectionsRestrict W hL s) := by
    rw [mul_def, Category.assoc, mulMap_natTensorPowRestrictIso, Category.assoc]
  unfold powSectionsRestrict
  rw [h, Stacks.AlgebraicGeometry.ProperAmpleCohomology.schemeGlobalSectionsAddEquiv_comp]
  rfl

/-- The degree-`0` section given by a function `c` on `W` corresponds to `c`, viewed as a
rational function. -/
theorem powSectionsRestrict_unitScalar {L : Divisor X} (hL : L.IsCartier) (c : Γ(W.toScheme, ⊤)) :
    (powSectionsRestrict W hL (k := 0)
      ((Stacks.SectionRingGeometric.unitScalarAddEquiv W.toScheme).symm c)).1 = algebraMap Γ(X, W.ι
          ''ᵁ ⊤) _ c := by
  have h := Stacks.SectionRingGeometric.globalSection_unitComp W.toScheme
    ((Stacks.SectionRingGeometric.unitScalarAddEquiv W.toScheme).symm c) (natTensorPowRestrictIso W
        hL 0).hom
  rw [← Stacks.SectionRingGeometric.unitScalarAddEquiv_apply, AddEquiv.apply_symm_apply] at h
  unfold powSectionsRestrict
  refine (congrArg (fun x => (restrictSection W x).1) h).trans ?_
  change (W.ι.appIso ⊤).inv.hom c • (restrictSection W
    (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv W.toScheme _ (natTensorPowRestrictIso
        W hL 0).hom)).1 = _
  rw [restrictSection_natTensorPowRestrictIso_zero, Algebra.smul_def, mul_one,
      Scheme.Opens.ι_appIso]
  rfl

/-- Every section of `𝒪(kL)` over `W` comes from a section of `(𝒪(L)|_W)^{⊗ k}`. -/
theorem powSectionsRestrict_surjective {L : Divisor X} (hL : L.IsCartier) {k : ℕ}
    (φ : (k • L).divisorialSubmodule (W.ι ''ᵁ ⊤)) : ∃ s : powSections (restrictSheaf W L) k,
      powSectionsRestrict W hL s = φ := by
  refine ⟨(Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv W.toScheme
    (restrictSheaf W (k • L))).symm (show Γ(restrictSheaf W (k • L), ⊤) from φ) ≫
    (natTensorPowRestrictIso W hL k).inv, ?_⟩
  unfold powSectionsRestrict
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, AddEquiv.apply_symm_apply]
  rfl

end MMP.Mori.Divisor
