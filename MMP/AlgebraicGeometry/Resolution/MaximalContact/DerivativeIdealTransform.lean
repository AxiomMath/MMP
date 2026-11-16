module

public import MMP.AlgebraicGeometry.Morphisms.Smooth.SmoothFlagCoordinates
public import MMP.AlgebraicGeometry.Morphisms.Smooth.EtaleCoordinates
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
public import MMP.AlgebraicGeometry.Resolution.MaximalContact.DBalancedLogDerivative
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.OrderMSequenceCosupport
public import MMP.AlgebraicGeometry.Resolution.MaximalContact.MaximalCoefficientPowers
public import MMP.AlgebraicGeometry.Resolution.OrderAlongExceptional
public import MMP.AlgebraicGeometry.Resolution.Surface.SncPointsCompletions

/-!
# Derivative ideals under smooth morphisms, completion and smooth blow-ups

Let `X` be a smooth scheme of finite type over a field `k`. This file collects how the derivative
ideal `D(I)` of an ideal sheaf `I ⊆ 𝒪_X` (and its iterates `D^j(I)`) behaves under the operations
used in Kollár's proof of resolution of singularities.

* A smooth morphism `h : Y ⟶ X`, with `X` closed in an affine `k`-scheme `A`, is locally the base
  change of a smooth surjective morphism onto an open of `A` (Kollár, Lemma 3.41).
* At a closed point `p`, derivatives commute with completion: `D_{𝒪̂/k}(I·𝒪̂) = D(I)·𝒪̂`, hence
  `D^j_{𝒪̂/k}(I·𝒪̂) = D^j(I)·𝒪̂`, the maximal contact ideal completes to
  `D^{m-1}_{𝒪̂/k}(I·𝒪̂)`, and maximal contact invariance passes to `𝒪̂` (Lemma 3.74(5), §3.10).
* Derivatives commute with smooth pull-back: `D(f^*I) = f^*D(I)` (Lemma 3.74(4)).
* For one smooth blow-up `π : B_Z X → X` with exceptional divisor `F` and `ord_Z I ≥ m ≥ 1`,
  `𝒪((m-1)F)·π^*D(I) ⊆ D(π⁻¹_*(I, m))` (3.75); along a smooth blow-up sequence of order `≥ m`
  the transforms of `D^j(I)` are contained in `D^j` of the transforms of `I` (Theorem 3.76), at
  every stage, and the same centres form a sequence of order `≥ m - j` for `D^j(I)`
  (Corollary 3.77).

## Main results

* `MMP.Resolution.exists_isPullback_smooth_surjective_of_isClosedImmersion`
* `MMP.Resolution.derivativeIdealOfRing_completedIdeal`
* `MMP.Resolution.completedIdeal_higherDerivativeIdeal`
* `MMP.Resolution.IsMCInvariant.completedIdeal`
* `MMP.Resolution.derivativeIdeal_comap_of_smooth`
* `MMP.Resolution.comap_derivativeIdeal_le_derivativeIdeal_birationalTransform_mul`
* `MMP.Resolution.ClosedBlowupSequence.derivedTransformJ_le_higherDerivativeIdeal`
* `MMP.Resolution.ClosedBlowupSequence.derivedTransformJ_truncate_le_higherDerivativeIdeal`
* `MMP.Resolution.ClosedBlowupSequence.isOrderGePlainSeq_higherDerivativeIdeal`

## Implementation notes

For Lemma 3.41 the source cuts out `Y` locally by a hypersurface `V(F) ⊆ X × 𝔸^{d+1}` and lifts
the coefficients of `F`; here a submersive presentation of `Γ(Y₀)` over `Γ(X)` plays the role of
`F`, its relations are lifted to `Γ(A)` and the lifted Jacobian is inverted, which makes the
fibre product exact on the nose.

For smooth pull-back, instead of relative coordinates on `Y` we lift `k`-derivations along the
formally smooth ring maps `Γ(X, W') → Γ(Y, W)`, which is the algebraic content of relative
coordinates.

Since `𝒪(-F)` is the invertible ideal `I_F = π⁻¹ I_Z · 𝒪_{B_Z X}`, the inclusion of fractional
ideals `𝒪((m-1)F)·π^*D(I) ⊆ J` is stated in the integral form `π^*D(I) ⊆ J · I_F^{m-1}`. The stage
`X_i` of a blow-up sequence `B` and its ideal `I_i` are read off the truncation `B.truncate i`.

## References

* [J. Kollár, *Lectures on resolution of singularities*][kollar2007], 3.41, 3.74–3.77, §3.10
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing TopologicalSpace
open scoped TensorProduct

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Resolution

/-- A standard smooth algebra over a quotient `R` of `R₀` is the base change of a smooth
`R₀`-algebra: lift the relations of a submersive presentation to `R₀` and invert the Jacobian. -/
private theorem exists_smooth_algEquiv_tensorProduct_of_surjective {R₀ R S : Type u} [CommRing R₀]
    [CommRing R] [CommRing S] [Algebra R₀ R] [Algebra R S]
    (hR : Function.Surjective (algebraMap R₀ R)) [Algebra.IsStandardSmooth R S] :
    ∃ (S₀ : Type u) (_ : CommRing S₀) (_ : Algebra R₀ S₀),
      Algebra.Smooth R₀ S₀ ∧ Nonempty (R ⊗[R₀] S₀ ≃ₐ[R] S) := by
  classical
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := Algebra.IsStandardSmooth.out (R := R) (S := S)
  cases nonempty_fintype σ
  have hmap : Function.Surjective (MvPolynomial.map (σ := ι) (algebraMap R₀ R)) :=
    MvPolynomial.map_surjective _ hR
  choose v hv using fun r : σ => hmap (P.relation r)
  let Q := Algebra.PreSubmersivePresentation.naive (v := v) P.map P.map_inj
  let T := MvPolynomial ι R₀ ⧸ Ideal.span (Set.range v)
  let Δ : T := Q.jacobian
  let S₀ := Localization.Away Δ
  let Q' := (Algebra.PreSubmersivePresentation.localizationAway S₀ Δ).comp Q
  have hQ' : IsUnit Q'.jacobian := by
    rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      Algebra.PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
    exact (IsLocalization.Away.algebraMap_isUnit Δ).mul (IsLocalization.Away.algebraMap_isUnit Δ)
  have : Algebra.IsStandardSmooth R₀ S₀ :=
    (⟨Q', hQ'⟩ : Algebra.SubmersivePresentation R₀ S₀ _ _).isStandardSmooth
  refine ⟨S₀, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
  let Q₁ := Q.baseChange R
  have hker : Q₁.ker = P.ker := by
    rw [← Q₁.span_range_relation_eq_ker, ← P.span_range_relation_eq_ker]
    congr 2
    exact funext hv
  let e₀ : R ⊗[R₀] T ≃ₐ[R] S :=
    ((Q₁.quotientEquiv.restrictScalars R).symm.trans (Ideal.quotientEquivAlgOfEq R hker)).trans
      (P.quotientEquiv.restrictScalars R)
  have he₀ : ∀ p : MvPolynomial ι R, e₀ (algebraMap Q₁.Ring _ p) = algebraMap P.Ring S p := by
    intro p
    have : (Q₁.quotientEquiv.restrictScalars R).symm (algebraMap Q₁.Ring _ p) =
        Ideal.Quotient.mk _ p := by
      rw [AlgEquiv.symm_apply_eq]
      exact (Q₁.quotientEquiv_mk p).symm
    rw [show e₀ (algebraMap Q₁.Ring _ p) = P.quotientEquiv (Ideal.quotientEquivAlgOfEq R hker
      ((Q₁.quotientEquiv.restrictScalars R).symm (algebraMap Q₁.Ring _ p))) from rfl, this,
      Ideal.quotientEquivAlgOfEq_mk]
    exact P.quotientEquiv_mk p
  have hjac : Q₁.jacobiMatrix = P.jacobiMatrix := by
    refine Matrix.ext fun i j => ?_
    rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply,
      Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
    exact congrArg (MvPolynomial.pderiv (P.map i)) (hv j)
  have hunit : IsUnit ((1 : R) ⊗ₜ[R₀] Δ) := by
    have h1 : (1 : R) ⊗ₜ[R₀] Δ = Q₁.jacobian := (Q.baseChange_jacobian R).symm
    rw [h1, ← isUnit_map_iff e₀, Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
      he₀, hjac, ← Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    exact P.jacobian_isUnit
  have H : Submonoid.powers ((1 : R) ⊗ₜ[R₀] Δ) ≤ IsUnit.submonoid _ :=
    Submonoid.powers_le.mpr ((IsUnit.mem_submonoid_iff _).mpr hunit)
  exact (IsLocalization.Away.tensorProductEquivTMulRight R₀ R Δ S₀).trans
    (((IsLocalization.atUnits _ _ (S := Localization.Away ((1 : R) ⊗ₜ[R₀] Δ)) H).symm
      |>.restrictScalars R).trans e₀)

/-- The core of Kollár's Lemma 3.41: around `y`, the smooth morphism `h` is the base change along
the closed immersion `i` of a smooth morphism `g : A_Y ⟶ A` into the affine ambient scheme. -/
private theorem exists_isPullback_smooth_of_isClosedImmersion {X Y A : Scheme.{u}} [IsAffine A]
    (h : Y ⟶ X) [Smooth h] (i : X ⟶ A) [IsClosedImmersion i] (y : Y) :
    ∃ (Y₀ : Y.Opens) (_ : y ∈ Y₀) (AY : Scheme.{u}) (g : AY ⟶ A) (j : Y₀.toScheme ⟶ AY),
      Smooth g ∧ IsClosedImmersion j ∧ IsPullback j (Y₀.ι ≫ h) g i := by
  classical
  obtain ⟨hXaff, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine i
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  have hsm := h.smooth_appLE (isAffineOpen_top X) hV (by simp)
  obtain ⟨s, hs, hst⟩ := RingHom.smooth_iff_locally_isStandardSmooth.mp hsm
  have hyV' : y ∈ ⨆ f : s, Y.basicOpen (f : Γ(Y, V)) := by
    rwa [(hV.iSup_basicOpen_eq_self_iff).mpr hs]
  obtain ⟨⟨t, ht⟩, hyt⟩ := TopologicalSpace.Opens.mem_iSup.mp hyV'
  have hY₀ : IsAffineOpen (Y.basicOpen t) := hV.basicOpen t
  have hle : Y.basicOpen t ≤ h ⁻¹ᵁ ⊤ := by simp
  let φ := h.appLE ⊤ (Y.basicOpen t) hle
  have hφ : φ.hom.IsStandardSmooth := by
    letI := (Y.presheaf.map (homOfLE (Y.basicOpen_le t)).op).hom.toAlgebra
    have := hV.isLocalization_basicOpen t
    have key := RingHom.isStandardSmooth_respectsIso.left _
      (IsLocalization.algEquiv (Submonoid.powers t) (Localization.Away t)
        Γ(Y, Y.basicOpen t)).toRingEquiv (hst t ht)
    convert key using 1
    ext x
    change _ = (IsLocalization.algEquiv (Submonoid.powers t) (Localization.Away t)
      Γ(Y, Y.basicOpen t)) (algebraMap Γ(Y, V) (Localization.Away t) _)
    rw [AlgEquiv.commutes, RingHom.algebraMap_toAlgebra, show φ = h.appLE ⊤ V (by simp) ≫
      Y.presheaf.map (homOfLE (Y.basicOpen_le t)).op from (h.appLE_map _ _).symm]
    rfl
  letI : Algebra Γ(A, ⊤) Γ(X, ⊤) := i.appTop.hom.toAlgebra
  letI : Algebra Γ(X, ⊤) Γ(Y, Y.basicOpen t) := φ.hom.toAlgebra
  haveI : Algebra.IsStandardSmooth Γ(X, ⊤) Γ(Y, Y.basicOpen t) := hφ.toAlgebra
  obtain ⟨S₀, _, _, hS₀, ⟨e⟩⟩ :=
    exists_smooth_algEquiv_tensorProduct_of_surjective (R₀ := Γ(A, ⊤)) (R := Γ(X, ⊤))
      (S := Γ(Y, Y.basicOpen t)) hsurj
  let ψ : CommRingCat.of Γ(Y, Y.basicOpen t) ≅ CommRingCat.of (Γ(X, ⊤) ⊗[Γ(A, ⊤)] S₀) :=
    e.symm.toRingEquiv.toCommRingCatIso
  let e₁ : Spec (.of (Γ(X, ⊤) ⊗[Γ(A, ⊤)] S₀)) ≅ (Y.basicOpen t).toScheme :=
    Scheme.Spec.mapIso ψ.op ≪≫ hY₀.isoSpec.symm
  have hpb := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct Γ(A, ⊤) Γ(X, ⊤) S₀)).flip
  refine ⟨Y.basicOpen t, hyt, Spec (.of S₀),
    Spec.map (CommRingCat.ofHom (algebraMap Γ(A, ⊤) S₀)) ≫ A.isoSpec.inv,
    e₁.inv ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom),
    ?_, ?_, ?_⟩
  · have : Smooth (Spec.map (CommRingCat.ofHom (algebraMap Γ(A, ⊤) S₀))) := by
      rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
      exact RingHom.smooth_algebraMap.mpr hS₀
    infer_instance
  · have : IsClosedImmersion (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := Γ(A, ⊤)) (A := Γ(X, ⊤)) (B := S₀)).toRingHom)) :=
      IsClosedImmersion.spec_of_surjective _ (Algebra.TensorProduct.includeRight_surjective _ hsurj)
    infer_instance
  · refine IsPullback.of_iso hpb e₁ (Iso.refl _) X.isoSpec.symm A.isoSpec.symm ?_ ?_ ?_ ?_
    · simp
    · simp only [Iso.symm_hom, e₁, Iso.trans_hom, Category.assoc]
      rw [hY₀.isoSpec_inv_ι_assoc,
        ← IsAffineOpen.SpecMap_appLE_fromSpec h (isAffineOpen_top X) hY₀ hle,
        IsAffineOpen.fromSpec_top]
      change _ = Spec.map ψ.hom ≫ Spec.map φ ≫ _
      rw [← Spec.map_comp_assoc]
      congr 2
      ext x
      change x ⊗ₜ[Γ(A, ⊤)] (1 : S₀) = e.symm (algebraMap Γ(X, ⊤) Γ(Y, Y.basicOpen t) x)
      rw [AlgEquiv.commutes]
      rfl
    · simp
    · simp only [Iso.symm_hom]
      change Spec.map i.appTop ≫ A.isoSpec.inv = X.isoSpec.inv ≫ i
      rw [Iso.eq_inv_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]

/-- Shrinking the ambient scheme to the (open) image of a smooth morphism makes it surjective
without destroying the cartesian square. -/
private theorem exists_isPullback_smooth_surjective_of_isPullback {X Y A AY : Scheme.{u}}
    (h : Y ⟶ X) (i : X ⟶ A) (y : Y) (Y₀ : Y.Opens) (hy : y ∈ Y₀) (g : AY ⟶ A)
    (j : Y₀.toScheme ⟶ AY) [Smooth g] [IsClosedImmersion j]
    (H : IsPullback j (Y₀.ι ≫ h) g i) :
    ∃ (Y₀ : Y.Opens) (_ : y ∈ Y₀) (A₀ : A.Opens) (_ : i (h y) ∈ A₀)
      (AY₀ : Scheme.{u}) (hA : AY₀ ⟶ A₀.toScheme) (j : Y₀.toScheme ⟶ AY₀)
      (hle : Y₀ ≤ h ⁻¹ᵁ (i ⁻¹ᵁ A₀)),
      Smooth hA ∧ Surjective hA ∧ IsClosedImmersion j ∧
        IsPullback j (h.resLE (i ⁻¹ᵁ A₀) Y₀ hle) hA (i ∣_ A₀) := by
  let A₀ : A.Opens := ⟨Set.range g, g.isOpenMap.isOpen_range⟩
  have hrange : Set.range g ⊆ Set.range A₀.ι := by simp [A₀]
  let hA : AY ⟶ A₀.toScheme := IsOpenImmersion.lift A₀.ι g hrange
  have hfac : hA ≫ A₀.ι = g := IsOpenImmersion.lift_fac _ _ _
  have hmem : ∀ y' : Y₀.toScheme, i (h y'.1) ∈ A₀ := fun y' =>
    ⟨j y', congrArg (fun φ => φ.base y') H.w⟩
  have hle : Y₀ ≤ h ⁻¹ᵁ (i ⁻¹ᵁ A₀) := fun y' hy' => hmem ⟨y', hy'⟩
  have hsmooth : Smooth hA :=
    MorphismProperty.of_isPullback (P := @Smooth)
      (IsOpenImmersion.isPullback_lift_id g A₀.ι hrange).flip inferInstance
  have hsurj : Surjective hA := by
    refine ⟨fun a => ?_⟩
    obtain ⟨b, hb⟩ := a.2
    refine ⟨b, A₀.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hfac, hb]
    rfl
  have hcomm : j ≫ hA = h.resLE (i ⁻¹ᵁ A₀) Y₀ hle ≫ i ∣_ A₀ := by
    rw [← cancel_mono A₀.ι, Category.assoc, hfac, Category.assoc, morphismRestrict_ι,
      Scheme.Hom.resLE_comp_ι_assoc, H.w, Category.assoc]
  refine ⟨Y₀, hy, A₀, hmem ⟨y, hy⟩, AY, hA, j, hle, hsmooth, hsurj, inferInstance, ?_⟩
  refine IsPullback.of_bot ?_ hcomm (isPullback_morphismRestrict i A₀)
  rw [Scheme.Hom.resLE_comp_ι, hfac]
  exact H

/-- **Kollár, Lemma 3.41.** A smooth morphism `h : Y ⟶ X` of `k`-schemes of finite type, with
`X` closed in an affine `k`-scheme `A` of finite type, is locally around any `y : Y` the base
change of a smooth surjective morphism `h_A : A_Y⁰ ⟶ A⁰` onto an open `A⁰ ⊆ A`, along the
restriction `i ∣_ A⁰` of the closed immersion. -/
@[mmp "lem_kr3b_smooth_morphism_lifts_to_ambient"]
public theorem exists_isPullback_smooth_surjective_of_isClosedImmersion
    {k : Type u} [Field k] {X Y A : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [A.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (A ↘ Spec (.of k))] [QuasiCompact (A ↘ Spec (.of k))]
    [IsAffine A]
    (h : Y ⟶ X) [h.IsOver (Spec (.of k))] [Smooth h]
    (i : X ⟶ A) [i.IsOver (Spec (.of k))] [IsClosedImmersion i]
    (y : Y) :
    ∃ (Y₀ : Y.Opens) (_ : y ∈ Y₀) (A₀ : A.Opens) (_ : i (h y) ∈ A₀)
      (AY₀ : Scheme.{u}) (hA : AY₀ ⟶ A₀.toScheme) (j : Y₀.toScheme ⟶ AY₀)
      (hle : Y₀ ≤ h ⁻¹ᵁ (i ⁻¹ᵁ A₀)),
      Smooth hA ∧ Surjective hA ∧ IsClosedImmersion j ∧
        IsPullback j (h.resLE (i ⁻¹ᵁ A₀) Y₀ hle) hA (i ∣_ A₀) := by
  obtain ⟨Y₀, hy, AY, g, j, hg, hj, H⟩ := exists_isPullback_smooth_of_isClosedImmersion h i y
  exact exists_isPullback_smooth_surjective_of_isPullback h i y Y₀ hy g j H

/-! ### Derivative ideals and completion -/

/-- Transport of a derivation `d` of `A` along an algebra isomorphism `e : A ≃ₐ[k] B`. -/
private def transportDerivation {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B) (d : Derivation k A A) : Derivation k B B :=
  Derivation.mk' (e.toLinearMap ∘ₗ d.toLinearMap ∘ₗ e.symm.toLinearMap) fun a b => by
    simp [Derivation.leibniz, smul_eq_mul]

private theorem transportDerivation_apply {k A B : Type*} [CommRing k] [CommRing A]
    [CommRing B] [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B) (d : Derivation k A A) (b : B) :
    transportDerivation e d b = e (d (e.symm b)) := rfl

/-- If `J ≤ K` and every `k`-derivation of `B` carries the image of `J` into the extension of
`K`, then the first derivative of the extension of `J` is contained in the extension of `K`. -/
private theorem derivativeIdealOfRing_map_le_map {k A B : Type*} [CommRing k] [CommRing A]
    [CommRing B] [Algebra k B] [Algebra A B] {J : Ideal A} {K : Ideal A} (hJ : J ≤ K)
    (hδ : ∀ δ : Derivation k B B, ∀ g ∈ J, δ (algebraMap A B g) ∈ K.map (algebraMap A B)) :
    derivativeIdealOfRing k (J.map (algebraMap A B)) ≤ K.map (algebraMap A B) := by
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨δ, b, hb, rfl⟩
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    exact hδ δ g hg
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | smul c x hxmem hx =>
    rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (Ideal.mul_mem_left _ _ hx)
      (Ideal.mul_mem_right _ _ (Ideal.map_mono hJ hxmem))

/-- Along `R → B`, if every `k`-derivation `R → B` expands in the derivations `∂ᵢ` of `R`, then
`D_{B/k}(J·B) ≤ D_{R/k}(J)·B` for every ideal `J ≤ D(J)` of `R`. -/
private theorem derivativeIdealOfRing_map_le {k R B : Type*} [CommRing k] [CommRing R]
    [CommRing B] [Algebra k R] [Algebra k B] [Algebra R B] [IsScalarTower k R B] {n : ℕ}
    (xs : Fin n → R) (d : Fin n → Derivation k R R)
    (hexp : ∀ (δ : Derivation k R B) (g : R), δ g = ∑ i, d i g • δ (xs i))
    (J : Ideal R) (hJ : J ≤ derivativeIdealOfRing k J) :
    derivativeIdealOfRing k (J.map (algebraMap R B)) ≤
      (derivativeIdealOfRing k J).map (algebraMap R B) :=
  derivativeIdealOfRing_map_le_map hJ fun D g hg => by
    rw [← Derivation.compAlgebraMap_apply R, hexp]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨d i, g, hg, rfl⟩))

/-- Along `R → B`, if every `k`-derivation `R → B` expands in derivations `∂ᵢ` of `R` against
`x₁, …, xₙ`, and `B` has `k`-derivations `δ̂ᵢ` dual to the `xⱼ`, then `D_{R/k}(J)·B ≤ D_{B/k}(J·B)`
for every ideal `J` of `R`. -/
private theorem map_derivativeIdealOfRing_le {k R B : Type*} [CommRing k] [CommRing R]
    [CommRing B] [Algebra k R] [Algebra k B] [Algebra R B] [IsScalarTower k R B] {n : ℕ}
    (xs : Fin n → R) (d : Fin n → Derivation k R R)
    (hexp : ∀ (δ : Derivation k R B) (g : R), δ g = ∑ i, d i g • δ (xs i))
    (δ : Fin n → Derivation k B B)
    (hδ : ∀ i j, δ i (algebraMap R B (xs j)) = if i = j then 1 else 0) (J : Ideal R) :
    (derivativeIdealOfRing k J).map (algebraMap R B) ≤
      derivativeIdealOfRing k (J.map (algebraMap R B)) := by
  classical
  rw [derivativeIdealOfRing, Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨D, f, hf, rfl⟩, rfl⟩
  -- `∂ᵢ f = δ̂ᵢ f` in `B`, which lies in `D(J·B)`.
  have hd (i : Fin n) :
      algebraMap R B (d i f) ∈ derivativeIdealOfRing k (J.map (algebraMap R B)) := by
    have h := hexp ((δ i).compAlgebraMap R) f
    simp only [Derivation.compAlgebraMap_apply, hδ, Algebra.smul_def, mul_ite, mul_zero,
      mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
    rw [← h]
    exact Ideal.subset_span ⟨δ i, _, Ideal.mem_map_of_mem _ hf, rfl⟩
  change ((Algebra.linearMap R B).compDer D) f ∈ _
  rw [hexp]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_right _ _ (hd i)

/-- **Derivative ideals and extension of scalars.** Let `R → B` be a map of `k`-algebras and
`x₁, …, xₙ ∈ R` with derivations `∂ᵢ` of `R` such that every `k`-derivation `δ : R → B` expands
as `δ g = ∑ᵢ ∂ᵢ g • δ xᵢ`. Suppose `B` has `k`-derivations `δ̂ᵢ` with `δ̂ᵢ xⱼ = δᵢⱼ`. Then for
every ideal `J ≤ D(J)` of `R`, `D_{B/k}(J·B) = D_{R/k}(J)·B`. -/
private theorem derivativeIdealOfRing_map {k R B : Type*} [CommRing k] [CommRing R]
    [CommRing B] [Algebra k R] [Algebra k B] [Algebra R B] [IsScalarTower k R B] {n : ℕ}
    (xs : Fin n → R) (d : Fin n → Derivation k R R)
    (hexp : ∀ (δ : Derivation k R B) (g : R), δ g = ∑ i, d i g • δ (xs i))
    (δ : Fin n → Derivation k B B)
    (hδ : ∀ i j, δ i (algebraMap R B (xs j)) = if i = j then 1 else 0)
    (J : Ideal R) (hJ : J ≤ derivativeIdealOfRing k J) :
    derivativeIdealOfRing k (J.map (algebraMap R B)) =
      (derivativeIdealOfRing k J).map (algebraMap R B) :=
  le_antisymm (derivativeIdealOfRing_map_le xs d hexp J hJ)
    (map_derivativeIdealOfRing_le xs d hexp δ hδ J)

/-- On a scheme satisfying (ST), the derivative of the completed ideal `I·𝒪̂_{p,X}` at a closed
point `p`, taken over all `k`-derivations of `𝒪̂_{p,X}`, is the completion of the derivative
ideal sheaf `D(I)` (Kollár, Lemma 3.74(5)). -/
@[mmp "lem_kr3d_derivative_ideal_completion"]
public theorem derivativeIdealOfRing_completedIdeal {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] [QuasiCompact sX]
    (hX : TopologicalSpace.Equidimensional X)
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    {p : X} (hp : IsClosed ({p} : Set X)) (I : X.IdealSheafData) :
    letI := completedAlgebra sX p
    derivativeIdealOfRing k (completedIdeal I p) = completedIdeal (derivativeIdeal sX I) p := by
  classical
  haveI := isRegularLocalRing_stalk_of_smooth_over_field sX p
  obtain ⟨n, t, ht⟩ := MMP.Mori.exists_isRegularSystemOfParameters (X.presheaf.stalk p)
  obtain ⟨V, hpV, x, hxt, hx⟩ :=
    MMP.Flips.ResolutionInputs.exists_isLocalCoordinatesAt_of_isRegularSystemOfParameters
      sX p hp t ht
  obtain ⟨W', hW', hpW, hWV⟩ := exists_isAffineOpen_mem_and_subset hpV
  obtain ⟨W, rfl⟩ : ∃ W : X.affineOpens, W.1 = W' := ⟨⟨W', hW'⟩, rfl⟩
  replace hWV : W.1 ≤ V := hWV
  have hsm : MMP.Mori.IsSmoothScheme sX :=
    eq_top_iff.mpr fun q _ => MMP.Mori.mem_smoothLocus_iff.mpr ⟨⊤, trivial, inferInstance⟩
  let := MMP.Mori.stalkAlgebra sX p
  obtain ⟨F₀, hF⟩ := MMP.Resolution.exists_mvPowerSeries_algEquiv_completion sX hsm p hp ht
  let := MMP.Mori.sectionAlgebra sX W.1
  let := completedAlgebra sX p
  let : Algebra Γ(X, W) (X.presheaf.stalk p) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨p, hpW⟩
  have : IsScalarTower k Γ(X, W) (X.presheaf.stalk p) :=
    MMP.Mori.isScalarTower_section_stalk sX W ⟨p, hpW⟩
  let : Algebra Γ(X, W)
      (AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p)) :=
    ((algebraMap (X.presheaf.stalk p)
      (AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p))).comp
        (algebraMap Γ(X, W) (X.presheaf.stalk p))).toAlgebra
  have hST : @IsScalarTower k Γ(X, W)
      (AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p)) _ _
      (@Algebra.toSMul _ _ _ _ (completedAlgebra sX p)) :=
    @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ _ _ (completedAlgebra sX p) fun c => by
      change algebraMap (X.presheaf.stalk p) _ (algebraMap k (X.presheaf.stalk p) c) =
        algebraMap (X.presheaf.stalk p) _ (algebraMap Γ(X, W) (X.presheaf.stalk p) _)
      rw [IsScalarTower.algebraMap_apply k Γ(X, W) (X.presheaf.stalk p) c]
  let F : MvPowerSeries (Fin n) (ResidueField (X.presheaf.stalk p)) ≃ₐ[k]
      AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p) :=
    AlgEquiv.ofRingEquiv (f := F₀.toRingEquiv) fun c => by
      change F₀ (algebraMap k _ c) = _
      rw [F₀.commutes]
      rfl
  have hstalk : ∀ J : X.IdealSheafData, completedIdeal J p =
      (J.ideal W).map (algebraMap Γ(X, W)
        (AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p))) := by
    intro J
    rw [completedIdeal, IdealSheafData.stalk_eq_map_germ J p W hpW, Ideal.map_map]
    rfl
  have hxs : ∀ i, algebraMap Γ(X, W)
      (AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p))
      (restrictSection W hWV (x i)) = F (MvPowerSeries.X i) := by
    intro i
    change _ = F₀ _
    rw [hF, ← hxt i]
    change algebraMap _ _ ((X.presheaf.germ W p hpW).hom
      ((X.presheaf.map (homOfLE hWV).op).hom (x i))) = _
    rw [X.presheaf.germ_res_apply]
  rw [hstalk, hstalk, derivativeIdeal_ideal]
  refine @derivativeIdealOfRing_map k Γ(X, W) _ _ _ _ _ (completedAlgebra sX p) _ hST n
    (fun i => restrictSection W hWV (x i))
    (MMP.Resolution.Bridges.partialDerivation hx.1 W hWV)
    (@MMP.Resolution.Bridges.derivation_eq_sum_partialDerivative_smul _ _ _ _ _ _ _ hx.1 W hWV _ _ _
      (completedAlgebra sX p).toModule hST)
    (fun i => transportDerivation F ((MvPowerSeries.pderiv i).restrictScalars k))
    (fun i j => ?_) _ ?_
  · rw [hxs, transportDerivation_apply]
    simp [MvPowerSeries.pderiv_X, Pi.single_apply, eq_comm]
  · rw [← sectionDerivativeIdeal, ← derivativeIdeal_ideal]
    exact le_derivativeIdeal sX hdim I W

/-- On a scheme satisfying (ST), at a closed point `p`, the completion of the higher derivative
ideal sheaf `D^j(I)` is the `j`-th higher derivative of `I·𝒪̂_{p,X}` over all `k`-derivations of
`𝒪̂_{p,X}`, for every `j`; in particular, when `m = maxord I ≥ 1`, the completion of the maximal
contact ideal is `D^{m-1}_{𝒪̂/k}(I·𝒪̂_{p,X})` (Kollár, Lemma 3.74(5) iterated). -/
@[mmp "lem_kr3d_completion_maximal_contact_ideal"]
public theorem completedIdeal_higherDerivativeIdeal {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] [QuasiCompact sX]
    (hX : TopologicalSpace.Equidimensional X)
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    {p : X} (hp : IsClosed ({p} : Set X)) (I : X.IdealSheafData) :
    letI := completedAlgebra sX p
    (∀ j : ℕ, completedIdeal (higherDerivativeIdeal sX I j) p =
        higherDerivativeIdealOfRing k (completedIdeal I p) j) ∧
      (1 ≤ maxOrder I → completedIdeal (maximalContactIdeal sX I) p =
        higherDerivativeIdealOfRing k (completedIdeal I p) ((maxOrder I).toNat - 1)) := by
  letI := completedAlgebra sX p
  have key : ∀ j : ℕ, completedIdeal (higherDerivativeIdeal sX I j) p =
      higherDerivativeIdealOfRing k (completedIdeal I p) j := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [higherDerivativeIdeal_succ, higherDerivativeIdealOfRing_succ, ← ih,
        derivativeIdealOfRing_completedIdeal sX hX hdim hp]
  exact ⟨key, fun _ => key _⟩

/-- Completion at a point carries an inclusion `J * K ≤ L` of ideal sheaves to the
corresponding inclusion of completed stalk ideals. -/
private lemma completedIdeal_mul_le {X : Scheme.{u}} {J K L : X.IdealSheafData}
    (h : J * K ≤ L) (p : X) :
    completedIdeal J p * completedIdeal K p ≤ completedIdeal L p := by
  rw [completedIdeal, completedIdeal, ← Ideal.map_mul, ← IdealSheafData.stalk_mul]
  exact Ideal.map_mono (stalk_le_stalk_of_le h p)

/-- On a scheme satisfying (ST), at a closed point `p`, a maximal contact invariant ideal sheaf
`I` with `m = maxord I ≥ 1` stays maximal contact invariant after completion:
`D^{m-1}_{𝒪̂/k}(Î)·D_{𝒪̂/k}(Î) ⊆ Î` in `𝒪̂_{p,X}`, where `Î = I·𝒪̂_{p,X}` (Kollár §3.10). -/
@[mmp "lem_kr3d_completion_mc_invariant"]
public theorem IsMCInvariant.completedIdeal {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [Smooth sX] [QuasiCompact sX]
    (hX : TopologicalSpace.Equidimensional X)
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    {p : X} (hp : IsClosed ({p} : Set X)) {I : X.IdealSheafData}
    (hI : IsMCInvariant sX I) (hm : 1 ≤ maxOrder I) :
    letI := completedAlgebra sX p
    higherDerivativeIdealOfRing k (completedIdeal I p) ((maxOrder I).toNat - 1) *
        derivativeIdealOfRing k (completedIdeal I p) ≤ completedIdeal I p := by
  letI := completedAlgebra sX p
  have key := (completedIdeal_higherDerivativeIdeal sX hX hdim hp I).1
  rw [← key, show derivativeIdealOfRing k (Resolution.completedIdeal I p) =
    Resolution.completedIdeal (higherDerivativeIdeal sX I 1) p from (key 1).symm]
  exact completedIdeal_mul_le hI p

/-! ### Derivative ideals and smooth pull-back -/

open KaehlerDifferential TensorProduct in
/-- Along a formally smooth `A`-algebra `B` (over a base `k`), every `k`-derivation of `A` lifts
to a `k`-derivation of `B`: the sequence `0 → B ⊗_A Ω_{A/k} → Ω_{B/k} → Ω_{B/A} → 0` is exact
(the first map is injective since `H¹(L_{B/A}) = 0`) and split (`Ω_{B/A}` is projective). -/
private theorem exists_derivation_algebraMap_of_formallySmooth {k A B : Type*} [CommRing k]
    [CommRing A] [CommRing B] [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    [Algebra.FormallySmooth A B] (δ : Derivation k A A) :
    ∃ δ' : Derivation k B B, ∀ a, δ' (algebraMap A B a) = algebraMap A B (δ a) := by
  have hinj : Function.Injective (mapBaseChange k A B) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange k A B x).mp hx
    rw [Subsingleton.elim y 0, map_zero]
  obtain ⟨l, hl⟩ := Module.projective_lifting_property (KaehlerDifferential.map k A B B)
    LinearMap.id (KaehlerDifferential.map_surjective k A B)
  have hsplit := ((KaehlerDifferential.exact_mapBaseChange_map k A B).split_tfae'.out 1 2).mp
  obtain ⟨-, r, hr⟩ := hsplit ⟨hinj, l, hl⟩
  let φ : B ⊗[A] Ω[A⁄k] →ₗ[B] B :=
    ((Algebra.linearMap A B) ∘ₗ δ.liftKaehlerDifferential).liftBaseChange B
  refine ⟨(φ ∘ₗ r).compDer (D k B), fun a => ?_⟩
  have h : D k B (algebraMap A B a) = mapBaseChange k A B (1 ⊗ₜ D k A a) := by
    rw [mapBaseChange_tmul, one_smul, map_D]
  show φ (r (D k B (algebraMap A B a))) = _
  rw [h, show r _ = _ from LinearMap.congr_fun hr (1 ⊗ₜ D k A a)]
  simp [φ]

/-- Along a formally smooth algebra, the extension of the first derivative of an ideal is
contained in the first derivative of the extended ideal. -/
private theorem map_derivativeIdealOfRing_le_of_formallySmooth {k A B : Type*} [CommRing k]
    [CommRing A] [CommRing B] [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    [Algebra.FormallySmooth A B] (J : Ideal A) :
    (derivativeIdealOfRing k J).map (algebraMap A B) ≤
      derivativeIdealOfRing k (J.map (algebraMap A B)) := by
  rw [derivativeIdealOfRing, Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨δ, g, hg, rfl⟩, rfl⟩
  obtain ⟨δ', hδ'⟩ := exists_derivation_algebraMap_of_formallySmooth (k := k) (B := B) δ
  exact Ideal.subset_span ⟨δ', _, Ideal.mem_map_of_mem _ hg, hδ' g⟩

/-- For `φ : Y ⟶ X` over `Spec k`, the map `φ.appLE` on sections is `k`-linear. -/
private theorem appLE_algebraMap {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} (φ : Y ⟶ X) (hφ : φ ≫ sX = sY)
    {W' : X.Opens} {W : Y.Opens} (hle : W ≤ φ ⁻¹ᵁ W') (c : k) :
    (φ.appLE W' W hle).hom (letI := MMP.Mori.sectionAlgebra sX W'; algebraMap k Γ(X, W') c) =
      (letI := MMP.Mori.sectionAlgebra sY W; algebraMap k Γ(Y, W) c) := by
  subst hφ
  have h := Scheme.Hom.appLE_comp_appLE φ sX ⊤ W' W (by simp) hle
  exact congrArg (fun t => ((Scheme.ΓSpecIso (.of k)).inv ≫ t).hom c) h

/-- The local statement: over an affine open `W ⊆ f⁻¹(W')`, `W'` an affine open contained in an
open carrying local coordinates, the sections of `D(f^*I)` and of `f^*D(I)` agree. -/
private theorem ideal_derivativeIdeal_comap_eq {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [Smooth sX] (f : Y ⟶ X) [Smooth f]
    (hf : f ≫ sX = sY)
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    (I : X.IdealSheafData) {U : X.Opens} {n : ℕ} {x : Fin n → Γ(X, U)}
    (hx : IsLocalCoordinatesOn sX U x) (W' : X.affineOpens) (hW' : W'.1 ≤ U)
    (W : Y.affineOpens) (e : W.1 ≤ f ⁻¹ᵁ W'.1) :
    (derivativeIdeal sY (I.comap f)).ideal W = ((derivativeIdeal sX I).comap f).ideal W := by
  have : Smooth sY := hf ▸ inferInstance
  let := MMP.Mori.sectionAlgebra sX W'.1
  let := MMP.Mori.sectionAlgebra sY W.1
  let : Algebra Γ(X, W') Γ(Y, W) := (f.appLE W' W e).hom.toAlgebra
  have : IsScalarTower k Γ(X, W') Γ(Y, W) := IsScalarTower.of_algebraMap_eq fun c =>
    (appLE_algebraMap f hf e c).symm
  have : Algebra.Smooth Γ(X, W') Γ(Y, W) :=
    HasRingHomProperty.appLE (P := @Smooth) f inferInstance W' W e
  have hJ : I.ideal W' ≤ derivativeIdealOfRing k (I.ideal W') := by
    have := le_derivativeIdeal sX hdim I W'
    rwa [derivativeIdeal_ideal, sectionDerivativeIdeal] at this
  rw [derivativeIdeal_ideal, sectionDerivativeIdeal,
    Stacks.IdealSheaf.ideal_comap_appLE _ f W' W e,
    Stacks.IdealSheaf.ideal_comap_appLE _ f W' W e, derivativeIdeal_ideal,
    sectionDerivativeIdeal]
  refine le_antisymm (derivativeIdealOfRing_map_le_map hJ fun δ g hg => ?_)
    (map_derivativeIdealOfRing_le_of_formallySmooth _)
  change (δ.compAlgebraMap Γ(X, W')) g ∈ _
  rw [Bridges.derivation_eq_sum_partialDerivative_smul hx W' hW' Γ(Y, W)
    (δ.compAlgebraMap Γ(X, W')) g]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.subset_span
    ⟨((hx.basis W' hW').coord i).compDer (KaehlerDifferential.D k _), g, hg, rfl⟩))

/-- **Derivative ideals commute with smooth pull-back.** Let `f : Y ⟶ X` be a smooth morphism
of schemes over a field `k`, `X` smooth over `k` with every irreducible component of positive
dimension. Then for every ideal sheaf `I` on `X`, `D(f^*I) = f^*D(I)`. -/
@[mmp "lem_kr3d_derivative_ideal_smooth_pullback"]
public theorem derivativeIdeal_comap_of_smooth {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [Smooth sX] (f : Y ⟶ X) [Smooth f]
    (hf : f ≫ sX = sY)
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    (I : X.IdealSheafData) :
    derivativeIdeal sY (I.comap f) = (derivativeIdeal sX I).comap f := by
  let ι := {p : X.affineOpens × Y.affineOpens // p.2.1 ≤ f ⁻¹ᵁ p.1.1 ∧
    ∃ (U : X.Opens) (n : ℕ) (x : Fin n → Γ(X, U)), IsLocalCoordinatesOn sX U x ∧ p.1.1 ≤ U}
  have hcover : ⨆ i : ι, i.1.2.1 = ⊤ := by
    refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨U, hU, n, x, hx, -⟩ := MMP.Flips.ResolutionInputs.exists_isLocalCoordinatesOn sX (f y)
    obtain ⟨_, ⟨W₀', hW₀', rfl⟩, hyW', hW'U⟩ :=
      (X.isBasis_affineOpens).exists_subset_of_mem_open hU U.2
    obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hyW, hWW'⟩ :=
      (Y.isBasis_affineOpens).exists_subset_of_mem_open (show y ∈ f ⁻¹ᵁ W₀' from hyW')
        (f ⁻¹ᵁ W₀').2
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨⟨(⟨W₀', hW₀'⟩, ⟨W₀, hW₀⟩), hWW', U, n, x, hx, hW'U⟩, hyW⟩
  have key (i : ι) : (derivativeIdeal sY (I.comap f)).ideal i.1.2 =
      ((derivativeIdeal sX I).comap f).ideal i.1.2 :=
    let ⟨⟨W', W⟩, e, _, _, _, hx, hW'U⟩ := i
    ideal_derivativeIdeal_comap_eq sX sY f hf hdim I hx W' hW'U W e
  exact le_antisymm
    (Scheme.IdealSheafData.le_of_iSup_eq_top (fun i : ι => i.1.2) hcover fun i => (key i).le)
    (Scheme.IdealSheafData.le_of_iSup_eq_top (fun i : ι => i.1.2) hcover fun i => (key i).ge)

/-! ### One smooth blow-up -/

/-- Multiplication by an effective Cartier divisor is cancellative on inclusions. -/
private theorem le_of_mul_le_mul_cartier {X : Scheme.{u}} {A B L : X.IdealSheafData}
    (hL : Stacks.Divisors.IsEffectiveCartierDivisor L) (h : A * L ≤ B * L) : A ≤ B := by
  choose U hU hxU b hb hgen using
    fun x : X => Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor L hL x
  refine Scheme.IdealSheafData.le_of_iSup_eq_top (fun x : X => (⟨U x, hU x⟩ : X.affineOpens))
    (top_unique fun z _ => TopologicalSpace.Opens.mem_iSup.2 ⟨z, hxU z⟩) fun x a ha => ?_
  have h' : A.ideal ⟨U x, hU x⟩ * L.ideal ⟨U x, hU x⟩ ≤
      B.ideal ⟨U x, hU x⟩ * L.ideal ⟨U x, hU x⟩ := h ⟨U x, hU x⟩
  rw [hgen x] at h'
  obtain ⟨c, hc, hcb⟩ := Ideal.mem_mul_span_singleton.1
    (h' (Ideal.mem_mul_span_singleton.2 ⟨a, ha, rfl⟩))
  exact (hb x).right hcb ▸ hc

/-- Being nonzero at the generic points passes to larger ideal sheaves. -/
private theorem isNonzeroAtGenericPoints_mono {X : Scheme} {I J : X.IdealSheafData}
    (hI : IsNonzeroAtGenericPoints I) (h : I ≤ J) : IsNonzeroAtGenericPoints J :=
  fun η hη hbot => hI η hη (eq_bot_iff.2 (hbot ▸ stalk_le_stalk_of_le h η))

/-- The first derivative is monotone in the ideal sheaf. -/
private theorem derivativeIdeal_mono {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) {I J : X.IdealSheafData} (h : I ≤ J) :
    derivativeIdeal sX I ≤ derivativeIdeal sX J := by
  refine sInf_le_sInf fun K hK W => le_trans ?_ (hK W)
  letI := MMP.Mori.sectionAlgebra sX W.1
  exact Ideal.span_mono fun g ⟨δ, f, hf, hg⟩ => ⟨δ, f, h W hf, hg⟩

/-- The irreducible components of the blow-up have positive dimension when those of `X` do. -/
private theorem topologicalKrullDim_pos_blowUp {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (Z : X.IdealSheafData)
    (hdim : ∀ C ∈ irreducibleComponents X, 0 < topologicalKrullDim C) :
    ∀ C ∈ irreducibleComponents (blowUp Z), 0 < topologicalKrullDim C := by
  intro C hC
  obtain ⟨D, hD, h⟩ := exists_topologicalKrullDim_eq_of_mem_irreducibleComponents_blowUp sX Z hC
  exact h ▸ hdim D hD

section OneBlowup

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- An inclusion of ideal sheaves on `Y` is local: if every point of `Y` has an open
neighbourhood `V` with `I(W) ≤ J(W)` for every affine open `W ⊆ V`, then `I ≤ J`. -/
private theorem le_of_forall_exists_nhds {Y : Scheme.{u}} {I J : Y.IdealSheafData}
    (H : ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧
      ∀ W : Y.affineOpens, W.1 ≤ V → I.ideal W ≤ J.ideal W) : I ≤ J := by
  choose V hyV hV using H
  refine Scheme.IdealSheafData.le_of_iSup_eq_top
    (fun W : {W : Y.affineOpens // ∃ y, W.1 ≤ V y} => W.1) ?_ fun W => ?_
  · refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨_, ⟨W, hW', rfl⟩, hyW, hW⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (hyV y) (V y).isOpen
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨W, hW'⟩, y, hW⟩, hyW⟩
  · obtain ⟨y, hy⟩ := W.2
    exact hV y W.1 hy

/-- Over a scheme `X` locally of finite type over a field, an inclusion `I ≤ J` of ideal sheaves
on `Y` with `f : Y ⟶ X` may be checked near the fibre over each closed point of `X`: it suffices
that every closed point `p` has a neighbourhood `U` such that the inclusion holds on affine opens
near every point of `f⁻¹ U`. -/
private theorem le_of_forall_closedPoints {Y : Scheme.{u}} (f : Y ⟶ X)
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] {I J : Y.IdealSheafData}
    (H : ∀ p ∈ closedPoints X, ∃ U : X.Opens, p ∈ U ∧ ∀ q ∈ f ⁻¹ᵁ U, ∃ V : Y.Opens, q ∈ V ∧
      ∀ W : Y.affineOpens, W.1 ≤ V → I.ideal W ≤ J.ideal W) : I ≤ J := by
  let V : X.Opens := sSup {U | ∀ q ∈ f ⁻¹ᵁ U, ∃ V : Y.Opens, q ∈ V ∧
      ∀ W : Y.affineOpens, W.1 ≤ V → I.ideal W ≤ J.ideal W}
  have hV : V = ⊤ := Bridges.eq_top_of_closedPoints_subset sX V fun p hp => by
    obtain ⟨U, hpU, hU⟩ := H p hp
    exact (le_sSup (α := X.Opens) hU : U ≤ V) hpU
  refine le_of_forall_exists_nhds fun q => ?_
  obtain ⟨U, hU, hqU⟩ := TopologicalSpace.Opens.mem_sSup.1 (hV ▸ trivial : f q ∈ V)
  exact hU q hqU

/-- The blow-up of a smooth `k`-scheme along a smooth centre is smooth over `k`. -/
private theorem smooth_blowUpToBase_comp (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (Z : X.IdealSheafData) [Smooth (Z.subschemeι ≫ sX)] : Smooth (blowUpToBase Z ≫ sX) :=
  (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sX Z
    ⟨isSmoothScheme_of_smooth sX, isSmoothScheme_of_smooth _⟩).1

/-- An inclusion of ideal sheaves restricted to an open `V` gives the inclusion of their
sections over every affine open contained in `V`. -/
private theorem ideal_le_of_comap_ι_le {Y : Scheme.{u}} (V : Y.Opens) {I J : Y.IdealSheafData}
    (h : I.comap V.ι ≤ J.comap V.ι) (W : Y.affineOpens) (hW : W.1 ≤ V) :
    I.ideal W ≤ J.ideal W := by
  have hW' : IsAffineOpen (V.ι ⁻¹ᵁ W.1) :=
    W.2.preimage_of_isOpenImmersion _ (by simpa using hW)
  have hh := Scheme.IdealSheafData.ideal_mono h ⟨_, hW'⟩
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Ideal.comap_le_comap_iff_of_surjective _ (ConcreteCategory.bijective_of_isIso
      ((V.ι.appIso (V.ι ⁻¹ᵁ W.1)).inv)).2] at hh
  have he : V.ι ''ᵁ (V.ι ⁻¹ᵁ W.1) = W.1 := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hW
  have he' : (⟨V.ι ''ᵁ (V.ι ⁻¹ᵁ W.1), (hW'.image_of_isOpenImmersion _)⟩ : Y.affineOpens) = W :=
    Subtype.ext he
  exact he' ▸ hh

/-- Off the centre: over `X ∖ Z` the blow-up is an isomorphism with `I_F = 𝒪` and `I₁ = π^*I`,
so the inclusion reads `π^*D(I) ⊆ D(π^*I)`. -/
private theorem off_center
    (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (hdim : ∀ C ∈ irreducibleComponents X, 0 < topologicalKrullDim C)
    (Z : X.IdealSheafData) [Smooth (Z.subschemeι ≫ sX)] (I : X.IdealSheafData) (m : ℕ)
    (W : (blowUp Z).affineOpens)
    (hW : W.1 ≤ blowUpToBase Z ⁻¹ᵁ ⟨(Z.support : Set X)ᶜ, Z.support.isClosed.isOpen_compl⟩) :
    ((derivativeIdeal sX I).comap (blowUpToBase Z)).ideal W ≤
      (derivativeIdeal (blowUpToBase Z ≫ sX) (MarkedIdeal.birationalTransform Z ⟨I, m⟩).I *
        Z.comap (blowUpToBase Z) ^ (m - 1)).ideal W := by
  set π := blowUpToBase Z
  set U : X.Opens := Z.support.compl
  set V : (blowUp Z).Opens := π ⁻¹ᵁ U
  have hiso := isIso_blowUpToBase_restrict_compl_support Z
  have hVπ : V.ι ≫ π = (π ∣_ U) ≫ U.ι := (morphismRestrict_ι π U).symm
  have : Smooth (V.ι ≫ π) := hVπ ▸ inferInstance
  have := smooth_blowUpToBase_comp sX Z
  have hZU : Z.comap U.ι = ⊤ := by
    rw [← Scheme.IdealSheafData.support_eq_bot_iff, Scheme.IdealSheafData.support_comap]
    ext x
    exact ⟨fun h => (x.2 h).elim, fun h => h.elim⟩
  have hF : (Z.comap π).comap V.ι = ⊤ := by
    rw [← Scheme.IdealSheafData.comap_comp, hVπ, Scheme.IdealSheafData.comap_comp, hZU,
      Scheme.IdealSheafData.comap_top]
  refine ideal_le_of_comap_ι_le V ?_ W hW
  rw [Stacks.IdealSheaf.comap_mul, Stacks.IdealSheaf.comap_pow, hF,
    ← Scheme.IdealSheafData.one_eq_top, one_pow, mul_one,
    ← Scheme.IdealSheafData.comap_comp,
    ← derivativeIdeal_comap_of_smooth sX (V.ι ≫ π ≫ sX) (V.ι ≫ π) (by simp) hdim,
    ← derivativeIdeal_comap_of_smooth (π ≫ sX) (V.ι ≫ π ≫ sX) V.ι rfl
      (topologicalKrullDim_pos_blowUp sX Z hdim),
    Scheme.IdealSheafData.comap_comp]
  exact derivativeIdeal_mono _ (Scheme.IdealSheafData.comap_mono _ (le_idealColon _ _))

/-- If `y ∈ J(W)`, then `y^a ∈ (J^a)(W)`. -/
private theorem pow_mem_ideal_pow {Y : Scheme.{u}} {J : Y.IdealSheafData} {W : Y.affineOpens}
    {y : Γ(Y, W)} (hy : y ∈ J.ideal W) (a : ℕ) : y ^ a ∈ (J ^ a).ideal W := by
  induction a with
  | zero => simp [Scheme.IdealSheafData.one_eq_top]
  | succ a ih =>
    rw [pow_succ, pow_succ, Scheme.IdealSheafData.ideal_mul]
    exact Ideal.mul_mem_mul ih hy

open MMP.Flips.ResolutionInputs in
/-- The chart computation (Kollár 3.75): on an affine open `W` of the chart `U_ℓ`, the generators
`π^*f_i` and `π^*(∂_j f_i)` of `π^*D(I)` are `y_ℓ^{m-1}` times elements of `D(I₁)`. -/
private theorem ideal_le_of_le_chart {Z : X.IdealSheafData} (sX : X ⟶ Spec (.of k)) [Smooth sX]
    [Smooth (blowUpToBase Z ≫ sX)]
    (hdim : ∀ C ∈ irreducibleComponents X, 0 < topologicalKrullDim C)
    (c : BlowupChartData Z) (hU : IsAffineOpen c.U) {n : ℕ} (x : Fin n → Γ(X, c.U))
    (hx : IsLocalCoordinates sX c.U x) (hrn : c.r ≤ n) (hcx : ∀ i, c.x i = x (Fin.castLE hrn i))
    (ℓ : Fin c.r) {I : X.IdealSheafData} {m : ℕ} (hm : 1 ≤ m)
    (hIF : I.comap (blowUpToBase Z) ≤ Z.comap (blowUpToBase Z) ^ m)
    {s : ℕ} (f : Fin s → Γ(X, c.U))
    (hf : ∀ (V : X.affineOpens) (h : V.1 ≤ c.U),
      I.ideal V = Ideal.span (Set.range fun i => (X.presheaf.map (homOfLE h).op).hom (f i)))
    (W : (blowUp Z).affineOpens) (hW : W.1 ≤ c.chart ℓ) :
    ((derivativeIdeal sX I).comap (blowUpToBase Z)).ideal W ≤
      (derivativeIdeal (blowUpToBase Z ≫ sX) (MarkedIdeal.birationalTransform Z ⟨I, m⟩).I *
        Z.comap (blowUpToBase Z) ^ (m - 1)).ideal W := by
  have hdimB := topologicalKrullDim_pos_blowUp sX Z hdim
  set π := blowUpToBase Z
  set D := derivativeIdeal (π ≫ sX) (MarkedIdeal.birationalTransform Z ⟨I, m⟩).I
  have hxOn := isLocalCoordinatesOn_of_isLocalCoordinates sX hU hx
  have hU' := isAffineOpen_chart c hU ℓ
  have hz := isLocalCoordinates_chartCoordinates c sX hU x hx hrn hcx ℓ
  have hy := isLocalCoordinatesOn_of_isLocalCoordinates (π ≫ sX) hU' hz
  have hzℓ : chartCoordinates c x ℓ (Fin.castLE hrn ℓ) = c.chartPullback ℓ (c.x ℓ) := by
    have h : ((Fin.castLE hrn ℓ : Fin n) : ℕ) < c.r := ℓ.2
    rw [chartCoordinates, dite_eq_left h]
    have hℓ' : (⟨_, h⟩ : Fin c.r) = ℓ := Fin.ext rfl
    rw [ite_eq_left hℓ', ← hcx]
  have hreg : c.chartPullback ℓ (c.x ℓ) ∈ nonZeroDivisors Γ(blowUp Z, c.chart ℓ) :=
    hzℓ ▸ mem_nonZeroDivisors_of_isLocalCoordinates (π ≫ sX) hU' hz _
  obtain ⟨g, hg, hgen⟩ := c.exists_birationalTransform_ideal_eq_span_chartTransform ℓ ⟨I, m⟩ hIF
    f hf
  have hfg : ∀ i, c.chartPullback ℓ (f i) = c.chartPullback ℓ (c.x ℓ) ^ m * g i := by
    intro i
    have hinj := IsLocalization.injective (Localization.Away (c.chartPullback ℓ (c.x ℓ)))
      ((Submonoid.powers_le).2 hreg)
    apply hinj
    have := hg i
    rw [BlowupChartData.chartTransform, Localization.mk_eq_mk',
      IsLocalization.eq_mk'_iff_mul_eq] at this
    rw [map_mul, ← this, mul_comm]
  set y := restrictSection W hW (c.chartPullback ℓ (c.x ℓ))
  have hWU : W.1 ≤ π ⁻¹ᵁ c.U := hW.trans (c.chart_le ℓ)
  have happ : ∀ t : Γ(X, c.U), (π.appLE c.U W.1 hWU).hom (restrictSection ⟨c.U, hU⟩ le_rfl t) =
      restrictSection W hW (c.chartPullback ℓ t) := by
    intro t
    rw [restrictSection, BlowupChartData.chartPullback, restrictSection, ← CommRingCat.comp_apply,
      ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  have hDgen := derivativeIdeal_ideal_eq_span_partialDerivative (π ≫ sX) hdimB hy
    (MarkedIdeal.birationalTransform Z ⟨I, m⟩).I g hgen W hW
  have hG : ∀ i, restrictSection W hW (g i) ∈ D.ideal W := fun i => by
    rw [hDgen]; exact Ideal.subset_span (Or.inl ⟨i, rfl⟩)
  have hDg : ∀ i j, partialDerivative hy W hW j (restrictSection W hW (g i)) ∈ D.ideal W :=
    fun i j => by rw [hDgen]; exact Ideal.subset_span (Or.inr ⟨(i, j), rfl⟩)
  have hyF : y ∈ (Z.comap π).ideal W := by
    rw [Stacks.IdealSheaf.ideal_comap_appLE Z π ⟨c.U, hU⟩ W hWU, c.generates ⟨c.U, hU⟩ le_rfl]
    have := Ideal.mem_map_of_mem (π.appLE c.U W.1 hWU).hom (Ideal.subset_span
      (Set.mem_range_self (f := fun i => (X.presheaf.map (homOfLE (le_refl c.U)).op).hom (c.x i))
        ℓ))
    have e : y = (π.appLE c.U W.1 hWU).hom
        ((X.presheaf.map (homOfLE (le_refl c.U)).op).hom (c.x ℓ)) := (happ (c.x ℓ)).symm
    rwa [e]
  have key : ∀ t ∈ D.ideal W, y ^ (m - 1) * t ∈ (D * Z.comap π ^ (m - 1)).ideal W := by
    intro t ht
    rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
    exact mul_comm t _ ▸ Ideal.mul_mem_mul ht (pow_mem_ideal_pow hyF _)
  have hym : y ^ m = y ^ (m - 1) * y := by rw [← pow_succ, Nat.sub_add_cancel hm]
  rw [Stacks.IdealSheaf.ideal_comap_appLE _ π ⟨c.U, hU⟩ W hWU,
    derivativeIdeal_ideal_eq_span_partialDerivative sX hdim hxOn I f hf ⟨c.U, hU⟩ le_rfl,
    Ideal.map_span, Ideal.span_le]
  rintro _ ⟨a, ha, rfl⟩
  rcases ha with ⟨i, rfl⟩ | ⟨⟨i, j⟩, rfl⟩
  · change (π.appLE c.U W.1 hWU).hom (restrictSection ⟨c.U, hU⟩ le_rfl (f i)) ∈ _
    rw [happ, hfg, restrictSection, map_mul, map_pow, ← restrictSection, ← restrictSection]
    change y ^ m * _ ∈ _
    rw [hym, mul_assoc]
    exact key _ (Ideal.mul_mem_left _ _ (hG i))
  · change (π.appLE (⟨c.U, hU⟩ : X.affineOpens) W hWU).hom _ ∈ _
    by_cases hj : (j : ℕ) < c.r
    · obtain ⟨j', rfl⟩ : ∃ j' : Fin c.r, Fin.castLE hrn j' = j := ⟨⟨j, hj⟩, Fin.ext rfl⟩
      by_cases hjℓ : j' = ℓ
      · subst hjℓ
        rw [Kollar.appLE_partialDerivative_self_eq_pow_mul c hxOn hrn hcx j' hy
          (by omega) (hfg i) ⟨c.U, hU⟩ le_rfl W hW hWU]
        refine key _ (add_mem (sub_mem (Ideal.mul_mem_left _ _ (hDg i _))
          (sum_mem fun l _ => Ideal.mul_mem_left _ _ (hDg i _))) (Ideal.mul_mem_left _ _ (hG i)))
      · rw [Kollar.appLE_partialDerivative_eq_pow_mul_partialDerivative_of_ne c hxOn hrn hcx ℓ
          hy (by omega) (hfg i) hjℓ ⟨c.U, hU⟩ le_rfl W hW hWU]
        exact key _ (hDg i _)
    · rw [BlowupChartData.appLE_partialDerivative_eq_pow_mul_of_le c hxOn hrn hcx ℓ hy (f i) m
        (g i) (hfg i) ⟨c.U, hU⟩ le_rfl W hW hWU j (not_lt.1 hj), hym, mul_assoc]
      exact key _ (Ideal.mul_mem_left _ _ (hDg i _))

/-- At a closed point `p` of the centre: on a neighbourhood `U` of `p` with coordinates
`Z ∩ U = (x₁ = ⋯ = x_r = 0)` and `I|_U = (f₁, …, f_s)`, the inclusion holds near every point of
`π⁻¹ U`, which the standard charts `U_ℓ` of the blow-up cover (Kollár 3.75). -/
private theorem exists_nhds_of_mem_support
    (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (hdim : ∀ C ∈ irreducibleComponents X, 0 < topologicalKrullDim C)
    (Z : X.IdealSheafData) [Smooth (Z.subschemeι ≫ sX)]
    {I : X.IdealSheafData} {m : ℕ} (hm : 1 ≤ m)
    (hord : OrderAlongGE I (Z.support : Set X) m)
    {p : X} (hpZ : p ∈ (Z.support : Set X)) :
    ∃ U : X.Opens, p ∈ U ∧ ∀ q ∈ blowUpToBase Z ⁻¹ᵁ U, ∃ V : (blowUp Z).Opens, q ∈ V ∧
      ∀ W : (blowUp Z).affineOpens, W.1 ≤ V →
      ((derivativeIdeal sX I).comap (blowUpToBase Z)).ideal W ≤
        (derivativeIdeal (blowUpToBase Z ≫ sX) (MarkedIdeal.birationalTransform Z ⟨I, m⟩).I *
          Z.comap (blowUpToBase Z) ^ (m - 1)).ideal W := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have := smooth_blowUpToBase_comp sX Z
  have hIF : I.comap (blowUpToBase Z) ≤ Z.comap (blowUpToBase Z) ^ m :=
    comap_le_comap_pow_of_stalk_le _ _ _ _ (stalk_le_pow_of_orderAlongGE sX
      (isSmoothScheme_of_smooth sX) Z (isSmoothScheme_of_smooth _) I m hord)
  obtain ⟨z, hz⟩ : p ∈ Set.range Z.subschemeι := by rwa [Z.range_subschemeι]
  obtain ⟨nX, hnX⟩ := Stacks.RelativeAssassin.exists_nat_eq_topologicalKrullDimAt X k sX
    (Z.subschemeι z)
  obtain ⟨nZ, hnZ⟩ := Stacks.RelativeAssassin.exists_nat_eq_topologicalKrullDimAt Z.subscheme k
    (Z.subschemeι ≫ sX) z
  have hle' :=
    Stacks.AlgebraicGeometry.LimitFibreDimensionBound.topologicalKrullDimAt_le_of_isInducing
      Z.subschemeι.isClosedEmbedding.isInducing z
  rw [hnX, hnZ] at hle'
  have hle'' : nZ ≤ nX := by exact_mod_cast hle'
  have hc : topologicalKrullDimAt X (Z.subschemeι z) =
      topologicalKrullDimAt Z.subscheme z + ((nX - nZ : ℕ) : WithBot ℕ∞) := by
    rw [hnX, hnZ, ← Nat.cast_add, Nat.add_sub_cancel' hle'']
  obtain ⟨U, hU, hzU, x, hx, hcut⟩ := Bridges.exists_isLocalCoordinates_adapted sX Z z hc
  -- forget that the number of coordinates is the rank of `Ω` at `z`
  obtain ⟨n, x, hx, hcut⟩ : ∃ (n : ℕ) (x : Fin n → Γ(X, U)), IsLocalCoordinates sX U x ∧
      Bridges.IsCutOutByFirst Z U x (nX - nZ) := ⟨_, x, hx, hcut⟩
  refine ⟨U, hz ▸ hzU, fun q hq => ?_⟩
  have hrn : min (nX - nZ) n ≤ n := min_le_right _ _
  let cd : BlowupChartData Z :=
    { U := U
      r := min (nX - nZ) n
      x := fun i => x (Fin.castLE hrn i)
      generates := fun V hV => by
        rw [hcut V hV]
        congr 1
        ext s
        constructor
        · rintro ⟨i, hi, rfl⟩
          exact ⟨⟨i, lt_min hi i.2⟩, rfl⟩
        · rintro ⟨j, rfl⟩
          exact ⟨Fin.castLE hrn j, lt_of_lt_of_le j.2 (min_le_left _ _), rfl⟩ }
  -- `I(U)` is finitely generated, and its generators generate `I` on every affine `V ⊆ U`.
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨s, f, hfU⟩ := Submodule.fg_iff_exists_fin_generating_family.1
    (IsNoetherian.noetherian (I.ideal ⟨U, hU⟩))
  have hf : ∀ (V : X.affineOpens) (h : V.1 ≤ cd.U),
      I.ideal V = Ideal.span (Set.range fun i => (X.presheaf.map (homOfLE h).op).hom (f i)) := by
    intro V h
    rw [← I.map_ideal (U := V) (V := ⟨U, hU⟩) h, ← hfU, Ideal.map_span, ← Set.range_comp]
    rfl
  have hqU : q ∈ blowUpToBase Z ⁻¹ᵁ cd.U := hq
  rw [← MMP.Flips.ResolutionInputs.iSup_chart_eq_preimage cd] at hqU
  obtain ⟨ℓ, hqℓ⟩ := TopologicalSpace.Opens.mem_iSup.mp hqU
  exact ⟨cd.chart ℓ, hqℓ, ideal_le_of_le_chart sX hdim cd hU x hx hrn (fun _ => rfl) ℓ hm hIF f hf⟩

end OneBlowup

/-- **Kollár 3.75.** Let `X` be smooth, equidimensional and of finite type over a field `k` of
characteristic zero, with irreducible components of positive dimension, `Z` a smooth closed
subscheme with blow-up `π = blowUpToBase Z` and exceptional ideal `I_F = Z.comap π`, and `I` an
ideal sheaf nonzero at the generic points of `X` with `ord_Z I ≥ m ≥ 1`. Then
`π^*D(I) ⊆ D(I₁) · I_F^{m-1}`, i.e. `𝒪((m-1)F) · π^*D(I) ⊆ D(I₁)`, where
`I₁ = 𝒪(mF) · π^*I` is the ideal of the birational transform of the marked ideal `(I, m)`. -/
@[mmp "lem_kr3d_transform_derivative_one_blowup"]
public theorem comap_derivativeIdeal_le_derivativeIdeal_birationalTransform_mul
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [Smooth sX] [QuasiCompact sX]
    (hX : TopologicalSpace.Equidimensional X)
    (hdim : ∀ C ∈ irreducibleComponents X, 0 < topologicalKrullDim C)
    (Z : X.IdealSheafData) (hZ : Smooth (Z.subschemeι ≫ sX))
    {I : X.IdealSheafData} (hI : IsNonzeroAtGenericPoints I) {m : ℕ} (hm : 1 ≤ m)
    (hord : OrderAlongGE I (Z.support : Set X) m) :
    (derivativeIdeal sX I).comap (blowUpToBase Z) ≤
      derivativeIdeal (blowUpToBase Z ≫ sX) (MarkedIdeal.birationalTransform Z ⟨I, m⟩).I *
        Z.comap (blowUpToBase Z) ^ (m - 1) := by
  have := hZ
  refine le_of_forall_closedPoints (blowUpToBase Z) sX fun p _ => ?_
  by_cases hpZ : p ∈ (Z.support : Set X)
  · exact exists_nhds_of_mem_support sX hdim Z hm hord hpZ
  · exact ⟨_, hpZ, fun q hq => ⟨_, hq, off_center sX hdim Z I m⟩⟩

/-! ### Blow-up sequences -/

/-- One blow-up: `π^*D^j(I) ⊆ D^j(I_1) · I_F^{m-j}` for `j ≤ m`, `I_1 = 𝒪(mF)·π^*I`. -/
private theorem comap_higherDerivativeIdeal_le {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] [QuasiCompact sX]
    (hX : Equidimensional X)
    (hdim : ∀ C ∈ irreducibleComponents X, 0 < topologicalKrullDim C)
    (Z : X.IdealSheafData) (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX))
    (hcodim : HasComponentsOfPositiveCodim (Z.support : Set X))
    {I : X.IdealSheafData} (hI : IsNonzeroAtGenericPoints I) {m : ℕ}
    (hord : OrderAlongGE I (Z.support : Set X) m) (j : ℕ) (hj : j ≤ m) :
    (higherDerivativeIdeal sX I j).comap (blowUpToBase Z) ≤
      higherDerivativeIdeal (blowUpToBase Z ≫ sX)
        (MarkedIdeal.birationalTransform Z ⟨I, m⟩).I j *
        Z.comap (blowUpToBase Z) ^ (m - j) := by
  have hXs : MMP.Mori.IsSmoothScheme sX := (MMP.Mori.isSmoothScheme_iff sX).2 inferInstance
  have hZs : Smooth (Z.subschemeι ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).1 hZ
  have hL : Stacks.Divisors.IsEffectiveCartierDivisor (Z.comap (blowUpToBase Z)) :=
    Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal Z
  induction j with
  | zero =>
    simp only [higherDerivativeIdeal_zero, Nat.sub_zero]
    exact (MarkedIdeal.birationalTransform_mul_eq sX hXs Z hZ hcodim ⟨I, m⟩ hord).ge
  | succ j ih =>
    set K := higherDerivativeIdeal sX I j
    have hIK := le_higherDerivativeIdeal_and_multAt sX hX hdim hI j
    have hK : IsNonzeroAtGenericPoints K := fun η hη =>
      isNonzeroAtGenericPoints_mono hI (hIK η).1 η hη
    have hordK : OrderAlongGE K (Z.support : Set X) ((m - j : ℕ) : ℕ∞) := by
      intro W hW
      change _ ≤ multAt K _
      rw [(hIK _).2, ENat.coe_sub]
      exact tsub_le_tsub_right (hord W hW) _
    have h1 := comap_derivativeIdeal_le_derivativeIdeal_birationalTransform_mul sX hX hdim Z hZs
      hK (m := m - j) (by omega) hordK
    have hK1 : (MarkedIdeal.birationalTransform Z ⟨K, m - j⟩).I ≤
        higherDerivativeIdeal (blowUpToBase Z ≫ sX)
          (MarkedIdeal.birationalTransform Z ⟨I, m⟩).I j := by
      refine le_of_mul_le_mul_cartier (Stacks.Divisors.isEffectiveCartierDivisor_pow hL (m - j)) ?_
      rw [MarkedIdeal.birationalTransform_mul_eq sX hXs Z hZ hcodim ⟨K, m - j⟩ hordK]
      exact ih (by omega)
    rw [higherDerivativeIdeal_succ, higherDerivativeIdeal_succ,
      show m - (j + 1) = m - j - 1 by omega]
    exact h1.trans (mul_le_mul' (derivativeIdeal_mono _ hK1) le_rfl)

/-- The induction along the sequence, for every ideal `T ⊆ D^j(I)` in place of `D^j(I)`. -/
private theorem derivedTransform_le {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (B : ClosedBlowupSequence X) (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    [QuasiCompact sX] (hX : Equidimensional X)
    (hdim : ∀ C ∈ irreducibleComponents X, 0 < topologicalKrullDim C)
    (a : MarkedIdeal X) (hB : ClosedBlowupSequence.IsOrderGePlainSeq sX a B)
    (j : ℕ) (hj : j ≤ a.m) (T : X.IdealSheafData) (hT : T ≤ higherDerivativeIdeal sX a.I j) :
    ∃ J, B.derivedTransform (some T) (a.m - j) = some J ∧
      J ≤ higherDerivativeIdeal (B.toBase ≫ sX) (B.markedTransform a).I j := by
  induction B with
  | nil X =>
    refine ⟨T, rfl, ?_⟩
    change T ≤ higherDerivativeIdeal (𝟙 X ≫ sX) a.I j
    rwa [Category.id_comp]
  | @cons X Z B ih =>
    obtain ⟨hsm, hnz, hZsm, hcodim, hord, hB'⟩ := hB
    have : Smooth sX := (MMP.Mori.isSmoothScheme_iff sX).1 hsm
    have hC := comap_higherDerivativeIdeal_le sX hX hdim Z hZsm hcodim hnz (m := a.m) hord j hj
    have hL : Stacks.Divisors.IsEffectiveCartierDivisor (Z.comap (blowUpToBase Z)) :=
      Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal Z
    have hle := (Scheme.IdealSheafData.comap_mono (blowUpToBase Z) hT).trans hC
    obtain ⟨T', hstep⟩ : ∃ T', ClosedBlowupSequence.derivedTransformStep Z (a.m - j) (some T) =
        some T' := by
      classical
      simp only [ClosedBlowupSequence.derivedTransformStep]
      rw [if_pos (hle.trans (mul_le_of_le_one_left' le_top))]
      exact ⟨_, rfl⟩
    have hT' : T' ≤ higherDerivativeIdeal (blowUpToBase Z ≫ sX)
        (a.birationalTransform Z).I j := by
      refine le_of_mul_le_mul_cartier
        (Stacks.Divisors.isEffectiveCartierDivisor_pow hL (a.m - j)) ?_
      rw [ClosedBlowupSequence.derivedTransformStep_mul_eq Z _ T T' hstep hL]
      exact hle
    have : Smooth (blowUpToBase Z ≫ sX) :=
      (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sX Z ⟨hsm, hZsm⟩).1
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    have hX' := equidimensional_blowUp sX Z hX
    have hdim' := topologicalKrullDim_pos_blowUp sX Z hdim
    obtain ⟨J, hJ, hJle⟩ := ih (blowUpToBase Z ≫ sX) hX' hdim' (a.birationalTransform Z) hB'
      hj T' hT'
    refine ⟨J, ?_, ?_⟩
    · change B.derivedTransform (ClosedBlowupSequence.derivedTransformStep Z (a.m - j) (some T))
        (a.m - j) = some J
      rw [hstep]
      exact hJ
    · change J ≤ higherDerivativeIdeal ((B.toBase ≫ blowUpToBase Z) ≫ sX)
        (B.markedTransform (a.birationalTransform Z)).I j
      rwa [Category.assoc]

namespace ClosedBlowupSequence

/-- **Transforms of derivatives are contained in derivatives of transforms** (Kollár Thm. 3.76).
Let `X` be smooth, equidimensional and of finite type over a field `k` of characteristic `0`,
with every irreducible component of positive dimension. Let `a = (I, m)` be a marked ideal
sheaf, with `I` nonzero on every irreducible component, and let `B` be a smooth blow-up sequence
of order `≥ m` starting with `(X, I, m)`. Then for every `j ≤ m` the transform
`T_r(D^j I, m - j)` is an ideal sheaf on the target of `B`, and it is contained in
`D^j(Π⁻¹_*(I, m))`. -/
@[mmp "thm_kr3d_transform_of_derivative_inclusion"]
public theorem derivedTransformJ_le_higherDerivativeIdeal {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [QuasiCompact sX]
    (hX : Equidimensional X)
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    (a : MarkedIdeal X) (ha : IsNonzeroAtGenericPoints a.I)
    (B : ClosedBlowupSequence X) (hB : IsOrderGePlainSeq sX a B)
    (j : ℕ) (hj : j ≤ a.m) :
    ∃ J, derivedTransformJ sX B a j = some J ∧
      J ≤ higherDerivativeIdeal (B.toBase ≫ sX) (B.markedTransform a).I j :=
  derivedTransform_le B sX hX hdim a hB j hj _ le_rfl

/-- A truncation of a smooth blow-up sequence of order `≥ m` is again one. -/
private theorem isOrderGePlainSeq_truncate {k : Type u} [Field k] :
    ∀ {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X) (B : ClosedBlowupSequence X)
      (i : ℕ), IsOrderGePlainSeq s a B → IsOrderGePlainSeq s a (B.truncate i)
  | _, _, _, .nil _, _, h => h
  | _, _, _, .cons _ _, 0, h => ⟨h.1, h.2.1⟩
  | _, s, a, .cons Z B, i + 1, h =>
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
      isOrderGePlainSeq_truncate (blowUpToBase Z ≫ s) (a.birationalTransform Z) B i h.2.2.2.2.2⟩

/-- **Transforms of derivatives at every stage** (Kollár Cor. 3.77). In the setting of
`derivedTransformJ_le_higherDerivativeIdeal`, for every `i ≤ r` and `j ≤ m` the transform
`T_i(D^j I, m - j)` along the first `i` blow-ups of `B` is an ideal sheaf on `X_i`, contained in
`D^j(I_i)`, where `I_i` is the marked transform of `(I, m)` along those blow-ups. -/
@[mmp "lem_kr3d_derived_transform_sequence_containment"]
public theorem derivedTransformJ_truncate_le_higherDerivativeIdeal {k : Type u} [Field k]
    [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    [QuasiCompact sX] (hX : Equidimensional X)
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    (a : MarkedIdeal X) (ha : IsNonzeroAtGenericPoints a.I)
    (B : ClosedBlowupSequence X) (hB : IsOrderGePlainSeq sX a B)
    (i : ℕ) (hi : i ≤ B.length) (j : ℕ) (hj : j ≤ a.m) :
    ∃ J, derivedTransformJ sX (B.truncate i) a j = some J ∧
      J ≤ higherDerivativeIdeal ((B.truncate i).toBase ≫ sX)
        ((B.truncate i).markedTransform a).I j :=
  derivedTransformJ_le_higherDerivativeIdeal sX hX hdim a ha (B.truncate i)
    (isOrderGePlainSeq_truncate sX a B i hB) j hj

/-- The first stage of a smooth blow-up sequence of order `≥ m`: `X` is smooth and `I` is
nonzero at the generic points. -/
private theorem isOrderGePlainSeq_head {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {a : MarkedIdeal X} :
    ∀ {B : ClosedBlowupSequence X}, ClosedBlowupSequence.IsOrderGePlainSeq s a B →
      MMP.Mori.IsSmoothScheme s ∧ IsNonzeroAtGenericPoints a.I
  | .nil _, h => h
  | .cons _ _, h => ⟨h.1, h.2.1⟩

/-- The induction along the sequence, for every ideal `T ⊆ D^j(I)` nonzero at the generic
points in place of `D^j(I)`. -/
private theorem isOrderGePlainSeq_of_le {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (B : ClosedBlowupSequence X) (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    [QuasiCompact sX] (hX : Equidimensional X)
    (hdim : ∀ C ∈ irreducibleComponents X, 0 < topologicalKrullDim C)
    (a : MarkedIdeal X) (hB : ClosedBlowupSequence.IsOrderGePlainSeq sX a B)
    (j : ℕ) (hj : j ≤ a.m) (T : X.IdealSheafData) (hT : T ≤ higherDerivativeIdeal sX a.I j)
    (hTnz : IsNonzeroAtGenericPoints T) :
    ClosedBlowupSequence.IsOrderGePlainSeq sX ⟨T, a.m - j⟩ B ∧
      ∀ i, (B.truncate i).derivedTransform (some T) (a.m - j) =
        some ((B.truncate i).markedTransform ⟨T, a.m - j⟩).I := by
  induction B with
  | nil X => exact ⟨⟨hB.1, hTnz⟩, fun _ => rfl⟩
  | @cons X Z B ih =>
    obtain ⟨hsm, hnz, hZsm, hcodim, hord, hB'⟩ := hB
    have : Smooth sX := (MMP.Mori.isSmoothScheme_iff sX).1 hsm
    have hL : Stacks.Divisors.IsEffectiveCartierDivisor (Z.comap (blowUpToBase Z)) :=
      Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal Z
    -- `ord_{Z} T ≥ ord_{Z} D^j(I) = ord_Z I - j ≥ m - j`.
    have hordT : OrderAlongGE T (Z.support : Set X) ((a.m - j : ℕ) : ℕ∞) := by
      intro W hW
      refine le_trans ?_ (MMP.Resolution.Kollar.multAt_antitone hT _)
      rw [(le_higherDerivativeIdeal_and_multAt sX hX hdim hnz j _).2, ENat.coe_sub]
      exact tsub_le_tsub_right (hord W hW) _
    set T' := (MarkedIdeal.birationalTransform Z ⟨T, a.m - j⟩).I
    have hmul : T' * Z.comap (blowUpToBase Z) ^ (a.m - j) = T.comap (blowUpToBase Z) :=
      MarkedIdeal.birationalTransform_mul_eq sX hsm Z hZsm hcodim ⟨T, a.m - j⟩ hordT
    -- The one-step case of the theorem on transforms of derivatives.
    obtain ⟨J, hJ, hJle⟩ := ClosedBlowupSequence.derivedTransformJ_le_higherDerivativeIdeal sX
      hX hdim a hnz (.cons Z (.nil _))
      ⟨hsm, hnz, hZsm, hcodim, hord, isOrderGePlainSeq_head hB'⟩ j hj
    change ClosedBlowupSequence.derivedTransformStep Z (a.m - j)
      (some (higherDerivativeIdeal sX a.I j)) = some J at hJ
    have hJmul := ClosedBlowupSequence.derivedTransformStep_mul_eq Z _ _ J hJ hL
    have hT' : T' ≤ higherDerivativeIdeal (blowUpToBase Z ≫ sX)
        (a.birationalTransform Z).I j := by
      refine le_of_mul_le_mul_cartier
        (Stacks.Divisors.isEffectiveCartierDivisor_pow hL (a.m - j)) ?_
      rw [hmul]
      exact (Scheme.IdealSheafData.comap_mono (blowUpToBase Z) hT).trans
        (hJmul.ge.trans (mul_le_mul'
          (by rwa [← Category.id_comp (blowUpToBase Z)]) le_rfl))
    have hT'nz : IsNonzeroAtGenericPoints T' :=
      isNonzeroAtGenericPoints_mono (isNonzeroAtGenericPoints_comap_blowUpToBase Z hTnz)
        (hmul.symm.le.trans (mul_le_of_le_one_right' le_top))
    have : Smooth (blowUpToBase Z ≫ sX) :=
      (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sX Z ⟨hsm, hZsm⟩).1
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    have hX' := equidimensional_blowUp sX Z hX
    have hdim' := topologicalKrullDim_pos_blowUp sX Z hdim
    obtain ⟨ih1, ih2⟩ := ih (blowUpToBase Z ≫ sX) hX' hdim' (a.birationalTransform Z) hB'
      hj T' hT' hT'nz
    have hstep : ClosedBlowupSequence.derivedTransformStep Z (a.m - j) (some T) = some T' := by
      classical
      simp only [ClosedBlowupSequence.derivedTransformStep]
      rw [if_pos (hmul.symm.le.trans (mul_le_of_le_one_left' le_top))]
      rfl
    refine ⟨⟨hsm, hTnz, hZsm, hcodim, hordT, ih1⟩, fun i => ?_⟩
    cases i with
    | zero => rfl
    | succ i =>
      change (B.truncate i).derivedTransform
        (ClosedBlowupSequence.derivedTransformStep Z (a.m - j) (some T)) (a.m - j) = _
      rw [hstep]
      exact ih2 i

/-- **The derived transforms form a blow-up sequence of order `≥ m - j`** (Kollár Cor. 3.77).
In the setting of `derivedTransformJ_le_higherDerivativeIdeal`, for `j ≤ m` the blow-up
sequence `B` is a smooth blow-up sequence of order `≥ m - j` starting with
`(X, D^j(I), m - j)`, and for every `i ≤ r` its `i`-th marked ideal is
`(T_i(D^j I, m - j), m - j)`: the transform `derivedTransformJ` along `B.truncate i` is the
ideal sheaf of the iterated birational transform of `(D^j(I), m - j)`. -/
@[mmp "lem_kr3d_derived_transform_sequence_order"]
public theorem isOrderGePlainSeq_higherDerivativeIdeal {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [QuasiCompact sX]
    (hX : Equidimensional X)
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    (a : MarkedIdeal X) (ha : IsNonzeroAtGenericPoints a.I)
    (B : ClosedBlowupSequence X) (hB : IsOrderGePlainSeq sX a B)
    (j : ℕ) (hj : j ≤ a.m) :
    IsOrderGePlainSeq sX ⟨higherDerivativeIdeal sX a.I j, a.m - j⟩ B ∧
      ∀ i ≤ B.length, derivedTransformJ sX (B.truncate i) a j =
        some ((B.truncate i).markedTransform ⟨higherDerivativeIdeal sX a.I j, a.m - j⟩).I := by
  have hsm := (isOrderGePlainSeq_head hB).1
  have : Smooth sX := (MMP.Mori.isSmoothScheme_iff sX).1 hsm
  obtain ⟨h1, h2⟩ := isOrderGePlainSeq_of_le B sX hX hdim a hB j hj _ le_rfl
    (fun η hη => isNonzeroAtGenericPoints_mono ha
      (le_higherDerivativeIdeal_and_multAt sX hX hdim ha j η).1 η hη)
  exact ⟨h1, fun i _ => h2 i⟩

end ClosedBlowupSequence

end MMP.Resolution
