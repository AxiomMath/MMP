module

public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldBadBranchCount
import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChainDifficulty
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction

/-!
# The label normalizations map birationally to a common normal model

Let `Y⁻ → Z ← Y⁺` (by `f^±`) be a threefold step diagram in which both morphisms are small, with
bad loci `Σ ⊆ Z` and `W^± = (f^±)⁻¹(Σ)`, and put `U = Z ∖ Σ`. Let `S⁻` be a prime divisor of `Y⁻`
with strict transform `S⁺` on `Y⁺`, and `ν^± : (S^±)^ν ⟶ S^± ⊆ Y^±` the normalizations. The image
`f⁻(S⁻)` is a prime divisor `D` of `Z`; let `τ : T ⟶ D ⊆ Z` be its normalization. Then
`(S^±)^ν` and `T` are normal projective surfaces, and for each sign `ε` there is a projective
birational morphism `σ^ε : (S^ε)^ν ⟶ T` with `σ^ε ≫ τ = ν^ε ≫ f^ε`, which restricts to an
isomorphism from `O^ε = (S^ε)^ν ∖ (ν^ε)⁻¹(W^ε)` onto `τ⁻¹(U)`. In particular `O⁻ ≅ O⁺`, over
`τ⁻¹(U)`.

The generic point of `S⁻` lies outside the exceptional set of the small morphism `f⁻`, which has
codimension at least two, so `D` is the prime divisor with generic point `f⁻(η_{S⁻})` and that
point lies in `U`. For each sign, `f^ε` maps the reduced subscheme `S^ε` into `D`, and the
induced morphism lifts to the normalizations: the generic point of `S^ε` factors through the
integral morphism `T ×_D S^ε ⟶ S^ε`, and the universal property of the relative normalization
gives `σ^ε`. Over `τ⁻¹(U)` the morphism `σ^ε` is integral (since `ν^ε` is and `f^ε` is an
isomorphism over `U`) and birational (its stalk map at the generic point is a surjection of
fields), with normal target, hence an isomorphism. It is projective because its source is
projective over `ℂ` and its target is separated.

## Main results

* `MMP.Fourfold.exists_normalization_hom_isIso_restrict_commonBiregularLocus`: the morphisms
  `σ^±` from the normalizations of a prime divisor and of its strict transform to the
  normalization of their common image, isomorphisms over `U`.

## Implementation notes

* The normalization of a prime divisor is `MMP.Fourfold.primeDivisorNormalization`, as for the
  bad branch count `MMP.Fourfold.badBranchCount`. The conclusion asserts that `f⁻(S⁻)` is the
  support of a prime divisor `D` of `Z` (determined by its support), and `T` is the
  normalization of `D`.
* The strict transform `S⁺` is a prime divisor with `MMP.Fourfold.flipTransformPrimeDivisor` equal
  to `some S⁺`, as in `MMP.Fourfold.IsBadBranchCountPlus`.
* A normal projective surface is a normal projective variety over `ℂ` of dimension two, with the
  structure morphism `ν ≫ s` induced from the ambient variety.
* "`σ^ε` restricts to an isomorphism `O^ε ≅ τ⁻¹(U)`" is: the preimage of `τ⁻¹(U)` under `σ^ε` is
  the complement of `(ν^ε)⁻¹(W^ε)`, and the restriction `σ^ε ∣_ τ⁻¹(U)` is an isomorphism. The
  isomorphism `O⁻ ≅ O⁺` is the one over `τ⁻¹(U)`.

## References

* [Stacks Project, Tag 035H](https://stacks.math.columbia.edu/tag/035H)
* [Stacks Project, Tag 0AB1](https://stacks.math.columbia.edu/tag/0AB1)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

/-- Cancelling `+ 1` in `WithBot ℕ∞` against a natural number. -/
private theorem withBot_eq_of_add_one_eq {n : ℕ} {d : WithBot ℕ∞}
    (h3 : d + ((1 : ℕ) : WithBot ℕ∞) = ((n + 1 : ℕ) : WithBot ℕ∞)) : d = n := by
  induction d using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.bot_add] at h3
    exact absurd h3 WithBot.bot_ne_coe
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => norm_cast at h3
    | coe d =>
      norm_cast at h3 ⊢
      omega

section Normalization

variable {Y : Scheme.{0}} (P : MMP.Mori.PrimeDivisor Y)

/-- The closed subscheme of a prime divisor of a variety is a variety. -/
private theorem isVariety_subschemeι (s : Y ⟶ Spec (.of ℂ)) [IsVariety ℂ s] :
    IsVariety ℂ (P.idealSheaf.subschemeι ≫ s) := by
  have := P.integral
  have : IsSeparated s := inferInstance
  have : LocallyOfFiniteType s := inferInstance
  have : QuasiCompact s := inferInstance
  exact {}

/-- The normalization of a prime divisor of a variety is finite over the variety. -/
private theorem isFinite_primeDivisorNormalization (s : Y ⟶ Spec (.of ℂ)) [IsVariety ℂ s] :
    IsFinite (primeDivisorNormalization P) := by
  have := P.integral
  have := isVariety_subschemeι P s
  have : IsFinite (Stacks.AlgebraicGeometry.Normalization.normalization P.idealSheaf.subscheme
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)) :=
    isFinite_normalization_of_locallyOfFiniteType _ (P.idealSheaf.subschemeι ≫ s) _
  exact inferInstanceAs (IsFinite (_ ≫ _))

/-- The normalization of a prime divisor of a variety is integral. -/
private theorem isIntegral_primeDivisorNormalizationScheme :
    IsIntegral (primeDivisorNormalizationScheme P) := by
  have := P.integral
  exact Scheme.isIntegral_normalizationScheme _
    (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)

attribute [local instance] isIntegral_primeDivisorNormalizationScheme

/-- The normalization of a prime divisor is normal. -/
private theorem isNormal_primeDivisorNormalizationScheme :
    IsNormal (primeDivisorNormalizationScheme P) := by
  have := P.integral
  exact Scheme.isNormal_normalizationScheme _
    (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)

/-- The normalization of a prime divisor of a variety is a variety. -/
private theorem isVariety_primeDivisorNormalization (s : Y ⟶ Spec (.of ℂ)) [IsVariety ℂ s] :
    IsVariety ℂ (primeDivisorNormalization P ≫ s) := by
  have := isFinite_primeDivisorNormalization P s
  have := isIntegral_primeDivisorNormalizationScheme P
  have : IsSeparated s := inferInstance
  have : LocallyOfFiniteType s := inferInstance
  have : QuasiCompact s := inferInstance
  exact {}

/-- The dimension of the normalization of a prime divisor of a variety of dimension `n + 1`
is `n`. -/
private theorem topologicalKrullDim_primeDivisorNormalizationScheme (s : Y ⟶ Spec (.of ℂ))
    [IsVariety ℂ s] {n : ℕ} (hdim : topologicalKrullDim Y = (n + 1 : ℕ)) :
    topologicalKrullDim (primeDivisorNormalizationScheme P) = n := by
  have := P.integral
  have := isVariety_subschemeι P s
  have h1 : topologicalKrullDim (primeDivisorNormalizationScheme P) =
      topologicalKrullDim P.idealSheaf.subscheme :=
    topologicalKrullDim_normalizationSchemeOverField ℂ (P.idealSheaf.subschemeι ≫ s)
  have h2 : topologicalKrullDim P.idealSheaf.subscheme =
      topologicalKrullDim (closure {P.genericPoint} : Set Y) := by
    have hr : Set.range P.idealSheaf.subschemeι = closure {P.genericPoint} := by
      rw [P.idealSheaf.range_subschemeι]
      exact AlgebraicGeometry.PrimeDivisor.support_eq_closure P
    exact (P.idealSheaf.subschemeι.isClosedEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr hr)).isHomeomorph.topologicalKrullDim_eq
  have : IsIntegral Y := IsVariety.toIsIntegral (f := s)
  have h3 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight s P.genericPoint
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint, hdim] at h3
  rw [h1, h2]
  exact withBot_eq_of_add_one_eq h3

/-- The normalization of a prime divisor of a projective variety over `ℂ` is a projective
variety: it is finite over the variety. -/
private theorem isProjectiveVariety_primeDivisorNormalization (s : Y ⟶ Spec (.of ℂ))
    (hs : AlgebraicGeometry.IsProjectiveVariety ℂ s) :
    AlgebraicGeometry.IsProjectiveVariety ℂ (primeDivisorNormalization P ≫ s) := by
  have := isFinite_primeDivisorNormalization P s
  have := isVariety_primeDivisorNormalization P s
  exact (isProjectiveVariety_iff_isProjective ℂ _).mpr
    ((Stacks.FiniteMorphismProjective.isProjective_of_isFinite _).comp
      hs.isProjective.isProjective)

/-- The normalization `P^ν` of a prime divisor `P` of a normal projective threefold over `ℂ` is
a normal projective surface over `ℂ`. -/
private theorem primeDivisorNormalization_props (s : Y ⟶ Spec (.of ℂ))
    (hs : AlgebraicGeometry.IsProjectiveVariety ℂ s) (hdim : topologicalKrullDim Y = 3) :
    MMP.Mori.IsProjectiveVariety ℂ (primeDivisorNormalization P ≫ s) ∧
      MMP.Mori.IsNormalVariety ℂ (primeDivisorNormalization P ≫ s) ∧
      topologicalKrullDim (primeDivisorNormalizationScheme P) = 2 :=
  ⟨isProjectiveVariety_primeDivisorNormalization P s hs,
    ⟨isVariety_primeDivisorNormalization P s, isNormal_primeDivisorNormalizationScheme P⟩,
    topologicalKrullDim_primeDivisorNormalizationScheme P s (n := 2) hdim⟩

end Normalization

section Descent

attribute [local instance] isIntegral_primeDivisorNormalizationScheme

open Stacks.AlgebraicGeometry.Normalization in
/-- **Normalization is functorial for morphisms preserving generic points.** A morphism
`g : A ⟶ B` of integral schemes sending the generic point to the generic point lifts to a
morphism `σ : A^ν ⟶ B^ν` of normalizations with `σ ≫ ν_B = ν_A ≫ g`: the morphism
`Spec k(A) ⟶ Spec k(B) ⟶ B^ν` together with `Spec k(A) ⟶ A` factors the generic point of `A`
through the integral morphism `B^ν ×_B A ⟶ A`. -/
private theorem exists_normalization_comp_eq {A B : Scheme.{0}} [IsIntegral A] [IsIntegral B]
    (hA : ∀ U : A.Opens, IsCompact (U : Set A) → (irreducibleComponents U).Finite)
    (hB : ∀ U : B.Opens, IsCompact (U : Set B) → (irreducibleComponents U).Finite)
    (g : A ⟶ B) (hg : g (genericPoint A) = genericPoint B) :
    ∃ σ : normalizationScheme A hA ⟶ normalizationScheme B hB,
      σ ≫ normalization B hB = normalization A hA ≫ g := by
  haveI := quasiCompact_fromGenericPointResidueFields A hA
  haveI := quasiCompact_fromGenericPointResidueFields B hB
  have hgen : ∀ η : genericPoints A, g η.1 ∈ genericPoints B := by
    intro η
    have h1 : η.1 = genericPoint A := by
      simpa [genericPoints_eq_singleton] using η.2
    rw [h1, hg, genericPoints_eq_singleton]
    exact Set.mem_singleton _
  let a : genericPointResidueSpectrum A ⟶ normalizationScheme B hB :=
    Limits.Sigma.desc fun η : genericPoints A ↦ Spec.map (g.residueFieldMap η.1) ≫
      Limits.Sigma.ι (fun η' : genericPoints B ↦ Spec (.of (B.residueField η'.1)))
        ⟨g η.1, hgen η⟩ ≫ (fromGenericPointResidueFields B).toNormalization
  have ha : a ≫ normalization B hB = fromGenericPointResidueFields A ≫ g := by
    refine Limits.Sigma.hom_ext _ _ fun η ↦ ?_
    simp only [a, normalization, Limits.Sigma.ι_desc_assoc, Category.assoc,
      Scheme.Hom.toNormalization_fromNormalization, ι_fromGenericPointResidueFields,
      ι_fromGenericPointResidueFields_assoc]
    exact g.SpecMap_residueFieldMap_fromSpecResidueField η.1
  let f₁ : genericPointResidueSpectrum A ⟶
      Limits.pullback (normalization B hB) g :=
    Limits.pullback.lift a (fromGenericPointResidueFields A) ha
  have H : fromGenericPointResidueFields A = f₁ ≫ Limits.pullback.snd _ _ :=
    (Limits.pullback.lift_snd _ _ _).symm
  refine ⟨(fromGenericPointResidueFields A).normalizationDesc f₁ _ H ≫
    Limits.pullback.fst _ _, ?_⟩
  rw [Category.assoc, Limits.pullback.condition, ← Category.assoc,
    Scheme.Hom.normalizationDesc_comp]

/-- **Incomparability.** Over an integral ring map, two comparable primes with the same
contraction are equal. -/
private theorem eq_of_le_of_comap_eq_of_isIntegral {R S : Type*} [CommRing R]
    [CommRing S] (φ : R →+* S) (hφ : φ.IsIntegral) {P Q : Ideal S} [P.IsPrime] (hPQ : P ≤ Q)
    (h : P.comap φ = Q.comap φ) : P = Q := by
  letI := φ.toAlgebra
  haveI : Algebra.IsIntegral R S := ⟨hφ⟩
  by_contra hne
  exact (Ideal.IsIntegral.comap_lt_comap (R := R) (lt_of_le_of_ne hPQ hne)).ne h

/-- Incomparability on spectra: for an integral ring map `φ`, two points of `Spec S` related by
specialization and with the same image under `Spec φ` are equal. -/
private theorem eq_of_specializes_of_isIntegral_specMap {R S : CommRingCat} (φ : R ⟶ S)
    (hφ : φ.hom.IsIntegral) (p q : PrimeSpectrum S) (hpq : p ⤳ q)
    (hc : Spec.map φ p = Spec.map φ q) : p = q := by
  rw [← PrimeSpectrum.le_iff_specializes] at hpq
  exact PrimeSpectrum.ext (eq_of_le_of_comap_eq_of_isIntegral _ hφ hpq
    (congrArg PrimeSpectrum.asIdeal hc))

/-- Incomparability for an integral morphism of affine schemes. -/
private theorem eq_of_specializes_of_isIntegralHom_of_isAffine {X Z : Scheme} [IsAffine X]
    [IsAffine Z] (f : X ⟶ Z) [IsIntegralHom f] {t t' : X} (h : t ⤳ t') (he : f t = f t') :
    t = t' := by
  have hg : (f.appTop).hom.IsIntegral := f.isIntegral_app ⊤ (isAffineOpen_top Z)
  have hc : (Spec.map f.appTop) (X.isoSpec.hom t) = (Spec.map f.appTop) (X.isoSpec.hom t') := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Scheme.isoSpec_hom_naturality,
      Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, he]
  have heq := congrArg X.isoSpec.inv (eq_of_specializes_of_isIntegral_specMap _ hg _ _
    (h.map X.isoSpec.hom.continuous) hc)
  rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Iso.hom_inv_id] at heq

/-- **Incomparability.** The fibres of an integral morphism carry no nontrivial
specializations. -/
private theorem eq_of_specializes_of_isIntegralHom {X Z : Scheme} (f : X ⟶ Z) [IsIntegralHom f]
    {t t' : X} (h : t ⤳ t') (he : f t = f t') : t = t' := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hmem, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f t')) isOpen_univ
  have ht' : t' ∈ f ⁻¹ᵁ U := hmem
  have ht : t ∈ f ⁻¹ᵁ U := h.mem_open (f ⁻¹ᵁ U).isOpen ht'
  haveI : IsAffine U := hU
  haveI : IsAffine (f ⁻¹ᵁ U) := hU.preimage f
  let a : (f ⁻¹ᵁ U).toScheme := ⟨t, ht⟩
  let b : (f ⁻¹ᵁ U).toScheme := ⟨t', ht'⟩
  have hab : a ⤳ b := subtype_specializes_iff _ _ |>.2 h
  have hfab : (f ∣_ U) a = (f ∣_ U) b := Subtype.ext
    ((morphismRestrict_base_coe f U a).trans (he.trans (morphismRestrict_base_coe f U b).symm))
  exact congrArg Subtype.val (eq_of_specializes_of_isIntegralHom_of_isAffine (f ∣_ U) hab hfab)

/-- A ring morphism out of the stalk at the generic point of an integral scheme, at a point
equal to the generic point, is an isomorphism once it is surjective. -/
private theorem isIso_stalkMap_of_surjective {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (h : X ⟶ Y) (x : X) (hx : h x = genericPoint Y)
    (hs : Function.Surjective (h.stalkMap x)) : IsIso (h.stalkMap x) := by
  let e := Y.presheaf.stalkCongr (Inseparable.of_eq hx)
  let φ : Y.functionField ⟶ X.presheaf.stalk x := e.inv ≫ h.stalkMap x
  have hφs : Function.Surjective φ := by
    intro b
    obtain ⟨a, rfl⟩ := hs b
    refine ⟨e.hom a, ?_⟩
    rw [CategoryTheory.comp_apply, Iso.hom_inv_id_apply]
  have : IsIso φ := (ConcreteCategory.isIso_iff_bijective φ).mpr ⟨φ.hom.injective, hφs⟩
  have : h.stalkMap x = e.hom ≫ φ := by simp [φ]
  rw [this]
  infer_instance

/-- A composite of surjective ring morphisms is surjective. -/
private theorem surjective_comp {A B C : CommRingCat} (a : A ⟶ B) (b : B ⟶ C)
    (ha : Function.Surjective a) (hb : Function.Surjective b) : Function.Surjective (a ≫ b) := by
  simpa using hb.comp ha

/-- If a composite of ring morphisms is surjective, so is its second factor. -/
private theorem surjective_of_comp {A B C : CommRingCat} (a : A ⟶ B) (b : B ⟶ C)
    (h : Function.Surjective (a ≫ b)) : Function.Surjective b := by
  simp only [CommRingCat.hom_comp, RingHom.coe_comp] at h
  exact h.of_comp

variable {Y Y' : Scheme.{0}}

/-- The normalization of a prime divisor sends the generic point to the generic point of the
divisor. -/
private theorem primeDivisorNormalization_genericPoint (P : MMP.Mori.PrimeDivisor Y) :
    primeDivisorNormalization P (genericPoint (primeDivisorNormalizationScheme P)) =
      P.genericPoint := by
  have := P.integral
  have := isIntegral_primeDivisorNormalizationScheme P
  have hbir : IsBirational (Stacks.AlgebraicGeometry.Normalization.normalization
      P.idealSheaf.subscheme
        (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)) :=
    Scheme.isBirational_normalization P.idealSheaf.subscheme
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)
  have h1 := hbir.bijOn.mapsTo (show genericPoint (primeDivisorNormalizationScheme P) ∈
    genericPoints (primeDivisorNormalizationScheme P) by
      simp [genericPoints_eq_singleton])
  rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at h1
  change P.idealSheaf.subschemeι (Stacks.AlgebraicGeometry.Normalization.normalization _ _ _) = _
  rw [h1]
  rfl

/-- The normalization of a prime divisor is surjective on the stalk at the generic point. -/
private theorem surjective_stalkMap_primeDivisorNormalization (P : MMP.Mori.PrimeDivisor Y) :
    Function.Surjective ((primeDivisorNormalization P).stalkMap
      (genericPoint (primeDivisorNormalizationScheme P))) := by
  have := P.integral
  have := isIntegral_primeDivisorNormalizationScheme P
  have hbir : IsBirational (Stacks.AlgebraicGeometry.Normalization.normalization
      P.idealSheaf.subscheme
        (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)) :=
    Scheme.isBirational_normalization P.idealSheaf.subscheme
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)
  have : IsIso ((Stacks.AlgebraicGeometry.Normalization.normalization P.idealSheaf.subscheme
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)).stalkMap
        (genericPoint (primeDivisorNormalizationScheme P))) :=
    hbir.isIso_stalkMap _ (by simp [genericPoints_eq_singleton])
  rw [Scheme.Hom.stalkMap_comp]
  exact surjective_comp _ _ (P.idealSheaf.subschemeι.stalkMap_surjective _)
    (ConcreteCategory.bijective_of_isIso _).2

/-- A morphism `σ : P^ν ⟶ Q^ν` with `σ ≫ ν_Q = ν_P ≫ f`, where `f(η_P) = η_Q`, sends the generic
point to the generic point. -/
private theorem primeDivisorNormalization_hom_genericPoint (P : MMP.Mori.PrimeDivisor Y)
    (Q : MMP.Mori.PrimeDivisor Y') (f : Y ⟶ Y') (hf : f P.genericPoint = Q.genericPoint)
    (σ : primeDivisorNormalizationScheme P ⟶ primeDivisorNormalizationScheme Q)
    (hσ : σ ≫ primeDivisorNormalization Q = primeDivisorNormalization P ≫ f) :
    σ (genericPoint (primeDivisorNormalizationScheme P)) =
      genericPoint (primeDivisorNormalizationScheme Q) := by
  have : IsIntegralHom (primeDivisorNormalization Q) := inferInstanceAs (IsIntegralHom (_ ≫ _))
  have h1 : primeDivisorNormalization Q (σ (genericPoint (primeDivisorNormalizationScheme P)))
      = primeDivisorNormalization Q (genericPoint (primeDivisorNormalizationScheme Q)) := by
    rw [← Scheme.Hom.comp_apply, hσ, Scheme.Hom.comp_apply, primeDivisorNormalization_genericPoint,
      hf, primeDivisorNormalization_genericPoint]
  exact (eq_of_specializes_of_isIntegralHom (primeDivisorNormalization Q)
    (genericPoint_specializes _) h1.symm).symm

/-- A morphism which is an isomorphism over an open `U'` has isomorphic stalk maps at the points
of `f ⁻¹ᵁ U'`. -/
private theorem isIso_stalkMap_of_isIso_morphismRestrict {X X' : Scheme.{0}} (f : X ⟶ X')
    (U' : X'.Opens) [IsIso (f ∣_ U')] (x : (f ⁻¹ᵁ U').toScheme) : IsIso (f.stalkMap x.1) :=
  ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff (morphismRestrictStalkMap f U' x)).mp
    (show IsIso ((f ∣_ U').stalkMap x) from inferInstance)

/-- The morphism of normalizations `σ : P^ν ⟶ Q^ν` over `f` is an isomorphism on stalks at the
generic point when `f` is an isomorphism over an open containing `η_Q`. -/
private theorem isIso_stalkMap_genericPoint_of_comp_eq (P : MMP.Mori.PrimeDivisor Y)
    (Q : MMP.Mori.PrimeDivisor Y') (f : Y ⟶ Y') (hf : f P.genericPoint = Q.genericPoint)
    (σ : primeDivisorNormalizationScheme P ⟶ primeDivisorNormalizationScheme Q)
    (hσ : σ ≫ primeDivisorNormalization Q = primeDivisorNormalization P ≫ f)
    (U' : Y'.Opens) (hU' : Q.genericPoint ∈ U') [IsIso (f ∣_ U')] :
    IsIso (σ.stalkMap (genericPoint (primeDivisorNormalizationScheme P))) := by
  refine isIso_stalkMap_of_surjective σ _
    (primeDivisorNormalization_hom_genericPoint P Q f hf σ hσ) ?_
  have : IsIso (f.stalkMap P.genericPoint) :=
    isIso_stalkMap_of_isIso_morphismRestrict f U' ⟨P.genericPoint, by
      change f _ ∈ U'
      rwa [hf]⟩
  have h2 : Function.Surjective ((primeDivisorNormalization P ≫ f).stalkMap
      (genericPoint (primeDivisorNormalizationScheme P))) := by
    rw [Scheme.Hom.stalkMap_comp]
    have key : ∀ y (_ : y = P.genericPoint), Function.Surjective (f.stalkMap y) := by
      rintro _ rfl
      exact (ConcreteCategory.bijective_of_isIso _).2
    exact surjective_comp _ _ (key _ (primeDivisorNormalization_genericPoint P))
      (surjective_stalkMap_primeDivisorNormalization P)
  have h3 : Function.Surjective ((σ ≫ primeDivisorNormalization Q).stalkMap
      (genericPoint (primeDivisorNormalizationScheme P))) :=
    hσ ▸ h2
  rw [Scheme.Hom.stalkMap_comp] at h3
  exact surjective_of_comp _ _ h3

/-- **The morphism of normalizations is an isomorphism over an open where `f` is one.** Let
`σ : P^ν ⟶ Q^ν` with `σ ≫ ν_Q = ν_P ≫ f`, where `f(η_P) = η_Q`, and let `U'` be an open
containing `η_Q` over which `f` is an isomorphism. Then `σ` is an isomorphism over `ν_Q⁻¹(U')`:
it is integral there, since `ν_P` is, and birational, since `f` is a local isomorphism at `η_P`;
its target is normal. -/
private theorem isIso_morphismRestrict_of_comp_eq (P : MMP.Mori.PrimeDivisor Y)
    (Q : MMP.Mori.PrimeDivisor Y') (f : Y ⟶ Y') (hf : f P.genericPoint = Q.genericPoint)
    (σ : primeDivisorNormalizationScheme P ⟶ primeDivisorNormalizationScheme Q)
    (hσ : σ ≫ primeDivisorNormalization Q = primeDivisorNormalization P ≫ f)
    (U' : Y'.Opens) (hU' : Q.genericPoint ∈ U') [IsIso (f ∣_ U')] :
    IsIso (σ ∣_ primeDivisorNormalization Q ⁻¹ᵁ U') := by
  set V := primeDivisorNormalization Q ⁻¹ᵁ U'
  have := isNormal_primeDivisorNormalizationScheme Q
  have hσg := primeDivisorNormalization_hom_genericPoint P Q f hf σ hσ
  have hgQ := primeDivisorNormalization_genericPoint Q
  have hmemP : genericPoint (primeDivisorNormalizationScheme P) ∈ σ ⁻¹ᵁ V := by
    change primeDivisorNormalization Q (σ _) ∈ U'
    rwa [hσg, hgQ]
  have hmemQ : genericPoint (primeDivisorNormalizationScheme Q) ∈ V := by
    change primeDivisorNormalization Q _ ∈ U'
    rwa [hgQ]
  have : Nonempty (σ ⁻¹ᵁ V) := ⟨⟨_, hmemP⟩⟩
  have : Nonempty V := ⟨⟨_, hmemQ⟩⟩
  have : IsIntegralHom (primeDivisorNormalization P) := inferInstanceAs (IsIntegralHom (_ ≫ _))
  have : IsIntegralHom (primeDivisorNormalization Q) := inferInstanceAs (IsIntegralHom (_ ≫ _))
  have h₀ : IsIntegralHom (primeDivisorNormalization P ∣_ f ⁻¹ᵁ U' ≫ f ∣_ U') := inferInstance
  have h₁ : IsIntegralHom ((σ ≫ primeDivisorNormalization Q) ∣_ U') := by
    rw [hσ, morphismRestrict_comp]
    exact h₀
  have : IsIntegralHom (σ ∣_ V ≫ primeDivisorNormalization Q ∣_ U') := by
    rw [← morphismRestrict_comp]
    exact h₁
  have : IsIntegralHom (σ ∣_ V) :=
    IsIntegralHom.of_comp (σ ∣_ V) (primeDivisorNormalization Q ∣_ U')
  have hO : (σ ⁻¹ᵁ V).ι (genericPoint (σ ⁻¹ᵁ V)) =
      genericPoint (primeDivisorNormalizationScheme P) :=
    genericPoint_eq_of_isOpenImmersion _
  have hV : V.ι (genericPoint V) = genericPoint (primeDivisorNormalizationScheme Q) :=
    genericPoint_eq_of_isOpenImmersion _
  have hres : (σ ∣_ V) (genericPoint (σ ⁻¹ᵁ V)) = genericPoint V := by
    apply V.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, hO, hσg, hV]
  have hbir : IsBirational (σ ∣_ V) := by
    refine ⟨?_, fun x hx => ?_⟩
    · rwa [genericPoints_eq_singleton, genericPoints_eq_singleton, Set.bijOn_singleton]
    · rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
      subst hx
      refine ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
        (morphismRestrictStalkMap σ V _)).mpr ?_
      change IsIso (σ.stalkMap ((σ ⁻¹ᵁ V).ι (genericPoint (σ ⁻¹ᵁ V))))
      rw [hO]
      exact isIso_stalkMap_genericPoint_of_comp_eq P Q f hf σ hσ U' hU'
  exact isIso_of_isIntegralHom_of_isBirational_of_isNormal _ hbir

/-- A morphism `f` with `f(η_P) = η_Q` maps the prime divisor `P` into `Q`, so the restriction
of `f` to the reduced subscheme `P` factors through the subscheme `Q`. -/
private theorem exists_subscheme_comp_eq (P : MMP.Mori.PrimeDivisor Y)
    (Q : MMP.Mori.PrimeDivisor Y') (f : Y ⟶ Y') (hf : f P.genericPoint = Q.genericPoint) :
    ∃ g : P.idealSheaf.subscheme ⟶ Q.idealSheaf.subscheme,
      g ≫ Q.idealSheaf.subschemeι = P.idealSheaf.subschemeι ≫ f := by
  have := P.integral
  have := Q.integral
  have hrange : Set.range (P.idealSheaf.subschemeι ≫ f) ⊆ Q.support := by
    rintro _ ⟨x, rfl⟩
    have hx : P.idealSheaf.subschemeι x ∈ P.support := by
      change _ ∈ (P.idealSheaf.support : Set Y)
      rw [← P.idealSheaf.range_subschemeι]
      exact Set.mem_range_self _
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure] at hx
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure]
    convert hx.map f.continuous using 1
    · exact hf.symm
    · exact Scheme.Hom.comp_apply _ _ _
  have H : Q.idealSheaf.subschemeι.ker ≤ (P.idealSheaf.subschemeι ≫ f).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι,
      ← MMP.Positivity.vanishingIdeal_support_of_isReduced Q.idealSheaf,
      ← Scheme.IdealSheafData.map_bot, ← Scheme.nilradical_eq_bot,
      ← Scheme.IdealSheafData.vanishingIdeal_top, Scheme.IdealSheafData.map_vanishingIdeal]
    refine Scheme.IdealSheafData.vanishingIdeal_antimono ?_
    change closure _ ⊆ (Q.idealSheaf.support : Set Y')
    refine closure_minimal ?_ Q.idealSheaf.support.isClosed
    rw [Closeds.coe_top, Set.image_univ]
    exact hrange
  exact ⟨IsClosedImmersion.lift _ _ H, IsClosedImmersion.lift_fac _ _ _⟩

/-- **The morphism of normalizations.** A morphism `f` with `f(η_P) = η_Q` lifts to a morphism
`σ : P^ν ⟶ Q^ν` of the normalizations of the prime divisors with `σ ≫ ν_Q = ν_P ≫ f`. -/
private theorem exists_primeDivisorNormalization_comp_eq (P : MMP.Mori.PrimeDivisor Y)
    (Q : MMP.Mori.PrimeDivisor Y') (f : Y ⟶ Y') (hf : f P.genericPoint = Q.genericPoint) :
    ∃ σ : primeDivisorNormalizationScheme P ⟶ primeDivisorNormalizationScheme Q,
      σ ≫ primeDivisorNormalization Q = primeDivisorNormalization P ≫ f := by
  have := P.integral
  have := Q.integral
  obtain ⟨g, hg⟩ := exists_subscheme_comp_eq P Q f hf
  have hgen : g (genericPoint P.idealSheaf.subscheme) = genericPoint Q.idealSheaf.subscheme := by
    apply Q.idealSheaf.subschemeι.isClosedEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hg, Scheme.Hom.comp_apply]
    exact hf
  obtain ⟨σ, hσ⟩ := exists_normalization_comp_eq
    (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)
    (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U) g hgen
  refine ⟨σ, ?_⟩
  change σ ≫ (Stacks.AlgebraicGeometry.Normalization.normalization _ _ ≫ _) =
    (Stacks.AlgebraicGeometry.Normalization.normalization _ _ ≫ _) ≫ f
  rw [← Category.assoc, hσ, Category.assoc, hg, Category.assoc]

end Descent

section Projective

open Limits in
/-- A morphism `p : X ⟶ X'` over `ℂ` from a projective scheme over `ℂ` to a separated one is
projective: a closed immersion `i : X ⟶ ℙⁿ_ℂ` gives the immersion `(i, p) : X ⟶ ℙⁿ_{X'}`,
closed because `p` is proper. -/
private theorem isProjectiveMorphism_of_comp_eq {X X' : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (sX' : X' ⟶ Spec (.of ℂ)) (hX : IsProjectiveMorphism sX) [IsSeparated sX'] (p : X ⟶ X')
    (hp : p ≫ sX' = sX) : IsProjectiveMorphism p := by
  have : IsProper sX := isProper_of_isProjectiveMorphism sX hX
  have : IsProper (p ≫ sX') := hp ▸ this
  have : IsProper p := IsProper.of_comp p sX'
  obtain ⟨n, i, hi, hcomm⟩ := hX
  have hcomm' : i ≫ (projectiveSpaceOver n (Spec (.of ℂ)) ↘ Spec (.of ℂ)) = p ≫ sX' := by
    rw [hcomm, hp]
  have hfst : IsImmersion (pullback.lift i p hcomm' ≫
      pullback.fst (projectiveSpaceOver n (Spec (.of ℂ)) ↘ Spec (.of ℂ)) sX') := by
    rw [pullback.lift_fst]
    infer_instance
  have hmid : IsImmersion (pullback.lift i p hcomm') :=
    IsImmersion.of_comp _ (pullback.fst (projectiveSpaceOver n (Spec (.of ℂ)) ↘ Spec (.of ℂ)) sX')
  have hover : (pullback.lift i p hcomm' ≫ (projectiveSpaceOverBaseChangeIso n sX').hom) ≫
      (projectiveSpaceOver n X' ↘ X') = p := by
    rw [Category.assoc, projectiveSpaceOverBaseChangeIso_hom_over, pullback.lift_snd]
  exact isProjectiveMorphism_of_isImmersion_projectiveSpaceOver _ hover

end Projective

section OneSide

attribute [local instance] isIntegral_primeDivisorNormalizationScheme

variable {Y Z : Scheme.{0}}

/-- **One side of the common normal model.** Let `f : Y ⟶ Z` be a morphism of projective
varieties over `ℂ` sending the generic point of a prime divisor `P` of `Y` to that of a prime
divisor `D` of `Z`, and let `U ⊆ Z` be an open containing `η_D` over which `f` is an
isomorphism. Then there is a projective birational `σ : P^ν ⟶ D^ν` with `σ ≫ ν_D = ν_P ≫ f`,
the preimage of `ν_D⁻¹(U)` under `σ` is `ν_P⁻¹(f⁻¹(U))`, and `σ` is an isomorphism over
`ν_D⁻¹(U)`. -/
private theorem exists_normalization_hom_of_isIso (s : Y ⟶ Spec (.of ℂ))
    (sZ : Z ⟶ Spec (.of ℂ)) (hs : AlgebraicGeometry.IsProjectiveVariety ℂ s)
    (hsZ : AlgebraicGeometry.IsProjectiveVariety ℂ sZ) (P : MMP.Mori.PrimeDivisor Y)
    (D : MMP.Mori.PrimeDivisor Z) (f : Y ⟶ Z) (hfs : f ≫ sZ = s)
    (hf : f P.genericPoint = D.genericPoint) (U : Z.Opens) (hU : D.genericPoint ∈ U)
    [IsIso (f ∣_ U)] :
    ∃ σ : primeDivisorNormalizationScheme P ⟶ primeDivisorNormalizationScheme D,
      IsProjectiveMorphism σ ∧ MMP.Mori.IsBirationalMorphism σ ∧
        σ ≫ primeDivisorNormalization D = primeDivisorNormalization P ≫ f ∧
        ((σ ⁻¹ᵁ primeDivisorNormalization D ⁻¹ᵁ U : Set _) =
          (primeDivisorNormalization P ⁻¹' ((f ⁻¹ᵁ U).compl : Set Y))ᶜ) ∧
        IsIso (σ ∣_ primeDivisorNormalization D ⁻¹ᵁ U) := by
  obtain ⟨σ, hσ⟩ := exists_primeDivisorNormalization_comp_eq P D f hf
  have hiso := isIso_morphismRestrict_of_comp_eq P D f hf σ hσ U hU
  have hset : ((σ ⁻¹ᵁ primeDivisorNormalization D ⁻¹ᵁ U : Set _) =
      (primeDivisorNormalization P ⁻¹' ((f ⁻¹ᵁ U).compl : Set Y))ᶜ) := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_preimage, Opens.coe_compl, not_not]
    change primeDivisorNormalization D (σ x) ∈ U ↔ f (primeDivisorNormalization P x) ∈ U
    rw [← Scheme.Hom.comp_apply, hσ, Scheme.Hom.comp_apply]
  refine ⟨σ, ?_, ?_, hσ, hset, hiso⟩
  · have := isVariety_primeDivisorNormalization D sZ
    exact isProjectiveMorphism_of_comp_eq _ (primeDivisorNormalization D ≫ sZ)
      (isProjectiveVariety_primeDivisorNormalization P s hs).isProjective σ
      (by rw [← Category.assoc, hσ, Category.assoc, hfs])
  · have hmem : genericPoint (primeDivisorNormalizationScheme P) ∈
        σ ⁻¹ᵁ primeDivisorNormalization D ⁻¹ᵁ U := by
      change primeDivisorNormalization D (σ _) ∈ U
      rwa [← Scheme.Hom.comp_apply, hσ, Scheme.Hom.comp_apply,
        primeDivisorNormalization_genericPoint, hf]
    refine MMP.Flips.isBirationalMorphism_of_isIso_resLE σ _ _ ⟨_, hmem⟩ ⟨_, hmem⟩ le_rfl ?_
    rwa [Scheme.Hom.resLE_eq_morphismRestrict]

end OneSide

open MMP.Mori

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]

/-- **The label normalizations map birationally to a common normal model.** Let
`Y⁻ → Z ← Y⁺` (by `f^±`) be a threefold step diagram with both morphisms small, `S⁻` a prime
divisor of `Y⁻` with strict transform `S⁺` on `Y⁺`, `ν^±` the normalizations of `S^±`, and
`U = Z ∖ Σ` the common biregular locus. Then `f⁻(S⁻)` is the support of a prime divisor `D` of
`Z`; with `τ : T ⟶ Z` the normalization of `D`, `(S^±)^ν` and `T` are normal projective
surfaces over `ℂ`, and there are projective birational morphisms `σ^± : (S^±)^ν ⟶ T` with
`σ^± ≫ τ = ν^± ≫ f^±`, such that `(σ^±)⁻¹(τ⁻¹(U))` is the complement `O^±` of `(ν^±)⁻¹(W^±)`
and `σ^±` restricts to an isomorphism `O^± ≅ τ⁻¹(U)`; in particular there is an isomorphism
`O⁻ ≅ O⁺` over `τ⁻¹(U)`. -/
@[mmp "lem_mmp_indexd_label_normalization_morphism"]
public theorem exists_normalization_hom_isIso_restrict_commonBiregularLocus
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (hdiag : IsThreefoldStepDiagram sXm sZ sXp K B fm fp) (hsmall : IsSmallMorphism sXm sZ fm)
    {S : MMP.Mori.PrimeDivisor Xm} {S' : MMP.Mori.PrimeDivisor Xp}
    (hS' : flipTransformPrimeDivisor fm fp S = some S') :
    (MMP.Mori.IsProjectiveVariety ℂ (primeDivisorNormalization S ≫ sXm) ∧
        MMP.Mori.IsNormalVariety ℂ (primeDivisorNormalization S ≫ sXm) ∧
        topologicalKrullDim (primeDivisorNormalizationScheme S) = 2) ∧
      (MMP.Mori.IsProjectiveVariety ℂ (primeDivisorNormalization S' ≫ sXp) ∧
        MMP.Mori.IsNormalVariety ℂ (primeDivisorNormalization S' ≫ sXp) ∧
        topologicalKrullDim (primeDivisorNormalizationScheme S') = 2) ∧
      ∃ D : MMP.Mori.PrimeDivisor Z, (D.support : Set Z) = fm '' S.support ∧
      (MMP.Mori.IsProjectiveVariety ℂ (primeDivisorNormalization D ≫ sZ) ∧
        MMP.Mori.IsNormalVariety ℂ (primeDivisorNormalization D ≫ sZ) ∧
        topologicalKrullDim (primeDivisorNormalizationScheme D) = 2) ∧
      ∃ (σm : primeDivisorNormalizationScheme S ⟶ primeDivisorNormalizationScheme D)
        (σp : primeDivisorNormalizationScheme S' ⟶ primeDivisorNormalizationScheme D),
        (IsProjectiveMorphism σm ∧ IsBirationalMorphism σm ∧
          σm ≫ primeDivisorNormalization D = primeDivisorNormalization S ≫ fm ∧
          ((σm ⁻¹ᵁ primeDivisorNormalization D ⁻¹ᵁ commonBiregularLocus fm fp : Set _) =
            (primeDivisorNormalization S ⁻¹' badLocusMinus fm fp)ᶜ) ∧
          IsIso (σm ∣_ primeDivisorNormalization D ⁻¹ᵁ commonBiregularLocus fm fp)) ∧
        (IsProjectiveMorphism σp ∧ IsBirationalMorphism σp ∧
          σp ≫ primeDivisorNormalization D = primeDivisorNormalization S' ≫ fp ∧
          ((σp ⁻¹ᵁ primeDivisorNormalization D ⁻¹ᵁ commonBiregularLocus fm fp : Set _) =
            (primeDivisorNormalization S' ⁻¹' badLocusPlus fm fp)ᶜ) ∧
          IsIso (σp ∣_ primeDivisorNormalization D ⁻¹ᵁ commonBiregularLocus fm fp)) ∧
        ∃ e : (σm ⁻¹ᵁ primeDivisorNormalization D ⁻¹ᵁ commonBiregularLocus fm fp).toScheme ≅
            (σp ⁻¹ᵁ primeDivisorNormalization D ⁻¹ᵁ commonBiregularLocus fm fp).toScheme,
          e.hom ≫ (σp ∣_ primeDivisorNormalization D ⁻¹ᵁ commonBiregularLocus fm fp) =
            σm ∣_ primeDivisorNormalization D ⁻¹ᵁ commonBiregularLocus fm fp := by
  obtain ⟨E, hE, hE'⟩ := Option.bind_eq_some_iff.mp hS'
  have hvm : AlgebraicGeometry.IsVariety ℂ sXm := hdiag.isProjectiveVariety_minus.toIsVariety
  have hvp : AlgebraicGeometry.IsVariety ℂ sXp := hdiag.isProjectiveVariety_plus.toIsVariety
  have hvZ : AlgebraicGeometry.IsVariety ℂ sZ := hdiag.isProjectiveVariety_target.toIsVariety
  have hdimZ : topologicalKrullDim Z = 3 :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sXm
      hdiag.isBirationalMorphism_minus).trans hdiag.dim_minus
  have : IsSeparated (Z ↘ Limits.terminal Scheme) := by
    rw [show (Z ↘ Limits.terminal Scheme) = sZ ≫ (Spec (.of ℂ) ↘ Limits.terminal Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have hfm : fm S.genericPoint = E.genericPoint :=
    (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff fm S E).mp hE
  obtain ⟨hfp, hfpV⟩ :=
    MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hE'
  have hfmV : fm S.genericPoint ∈ biregularLocus fm := by
    by_contra hcon
    have hsub : (IrreducibleCloseds.closureSingleton S.genericPoint : Set Xm) ⊆
        (exceptionalSet fm : Set Xm) :=
      closure_minimal (Set.singleton_subset_iff.mpr hcon) (exceptionalSet fm).isClosed
    have h2 := le_closedsCodimension_iff.mp hsmall.two_le_codimension _ hsub
    rw [AlgebraicGeometry.PrimeDivisor.codimension_closureSingleton_genericPoint] at h2
    exact absurd h2 (by decide)
  have hU : E.genericPoint ∈ commonBiregularLocus fm fp :=
    ⟨by rwa [← hfm], by rwa [← hfp]⟩
  have : IsIso (fm ∣_ commonBiregularLocus fm fp) := isBiregular_commonBiregularLocus_left fm fp
  have : IsIso (fp ∣_ commonBiregularLocus fm fp) := isBiregular_commonBiregularLocus_right fm fp
  have hsupp : (E.support : Set Z) = fm '' S.support := by
    have : IsProper fm := hsmall.isProper
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      ← fm.isClosedMap.closure_image_eq_of_continuous fm.continuous, Set.image_singleton, hfm]
  obtain ⟨σm, hpm, hbm, hcm, hsm, him⟩ := exists_normalization_hom_of_isIso sXm sZ
    hdiag.isProjectiveVariety_minus hdiag.isProjectiveVariety_target S E fm hdiag.comp_eq_minus
    hfm _ hU
  obtain ⟨σp, hpp, hbp, hcp, hsp, hip⟩ := exists_normalization_hom_of_isIso sXp sZ
    hdiag.isProjectiveVariety_plus hdiag.isProjectiveVariety_target S' E fp hdiag.comp_eq_plus
    hfp _ hU
  refine ⟨primeDivisorNormalization_props S sXm hdiag.isProjectiveVariety_minus hdiag.dim_minus,
    primeDivisorNormalization_props S' sXp hdiag.isProjectiveVariety_plus hdiag.dim_plus,
    E, hsupp, primeDivisorNormalization_props E sZ hdiag.isProjectiveVariety_target hdimZ,
    σm, σp, ⟨hpm, hbm, hcm, hsm, him⟩, ⟨hpp, hbp, hcp, hsp, hip⟩, ?_⟩
  refine ⟨asIso (σm ∣_ primeDivisorNormalization E ⁻¹ᵁ commonBiregularLocus fm fp) ≪≫
    (asIso (σp ∣_ primeDivisorNormalization E ⁻¹ᵁ commonBiregularLocus fm fp)).symm, ?_⟩
  simp

end MMP.Fourfold
