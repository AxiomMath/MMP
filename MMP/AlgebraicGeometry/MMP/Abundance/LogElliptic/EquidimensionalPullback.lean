module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Abundance.Defs
public import MMP.AlgebraicGeometry.Singularities.PairClasses
public import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
public import MMP.AlgebraicGeometry.FiberSpace.NumericallyTrivialDescent
public import MMP.AlgebraicGeometry.Divisor.QCartierFiniteDescent
public import MMP.AlgebraicGeometry.Morphisms.FiniteCoverTrace
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
public import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.MMP.Abundance.Basic
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
public import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
public import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
public import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
public import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.ChowForm.CoreSkeleton
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
public import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
public import MMP.AlgebraicGeometry.MMP.Threefold.SurfaceLocalRings
public import MMP.AlgebraicGeometry.Chow.FieldSituation

universe u

section

/-!
# Equidimensional log elliptic fiber spaces: the log canonical bundle is a pullback

Let `g : (V, Δ_V) ⟶ W` be a log elliptic fiber space all of whose fibers have pure dimension
one, with `(V, Δ_V)` log canonical and `K_V + Δ_V` nef. Write `L = K_V + Δ_V` and let `M = n₀ L`
be Cartier. Then:

1. the restriction of `𝒪_V(M)` to the generic fiber is trivial, so `M` is linearly equivalent to
   a divisor `D` none of whose components dominates `W`;
2. by equidimensionality every prime divisor of `V` maps onto `W` or onto a prime divisor of `W`;
3. along each prime divisor `C` of `W`, nefness on the curves in the fibers forces the part of
   `D` over `C` to be a rational multiple `r_C g^*C` (Zariski's lemma), so that `D = g^*B` for the
   `ℚ`-divisor `B = ∑ r_C C`;
4. `B` is `ℚ`-Cartier: near a point `z` of `W`, a hypersurface section of `V` through a closed
   point of the fiber over `z` is quasi-finite over `W`, and the pull-back of `B` to its normal
   Galois closure over `W` is `ℚ`-Cartier, hence so is `B` by finite descent;
5. with `m B` Cartier, `m D = g^*(m B)`, and `𝒪_V(m M) ≅ 𝒪_V(m D) ≅ g^* 𝒪_W(m B)`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 15.12
-/

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Flips

namespace MMP.FourfoldProofs.Fa15EquidimensionalLogEllipticPullbackProof

section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral normalClosure.algebraOfTower

variable {k : Type u} [Field k] {V W : Scheme.{u}} {sV : V ⟶ Spec (.of k)}
  {sW : W ⟶ Spec (.of k)}

/-- The generic point of an integral scheme has coheight zero. -/
private lemma coheight_genericPoint_eq_zero (X : Scheme.{u}) [IsIntegral X] :
    Order.coheight (genericPoint X) = 0 :=
  Order.coheight_eq_zero.mpr fun b _ => genericPoint_specializes b

/-- A point of coheight zero of an integral scheme is its generic point. -/
private lemma eq_genericPoint_of_coheight_eq_zero {X : Scheme.{u}} [IsIntegral X] {x : X}
    (hx : Order.coheight x = 0) : x = genericPoint X :=
  ((show x ⤳ genericPoint X from
    Order.coheight_eq_zero.mp hx (genericPoint_specializes x)).antisymm
      (genericPoint_specializes x)).eq

/-- A prime divisor whose generic point specializes to that of another prime divisor is that
prime divisor: both generic points have codimension one. -/
private lemma primeDivisor_eq_of_specializes {X : Scheme.{u}} {C C' : MMP.Mori.PrimeDivisor X}
    (h : C'.genericPoint ⤳ C.genericPoint) : C' = C := by
  apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
  by_contra hne
  have hlt : C.genericPoint < C'.genericPoint := lt_of_le_not_ge h fun h2 => hne
    ((show C.genericPoint ⤳ C'.genericPoint from h2).antisymm h).eq.symm
  have := Order.coheight_add_one_le hlt
  rw [C.coheight_genericPoint, C'.coheight_genericPoint] at this
  exact absurd this (by decide)

/-! ### Orders of vanishing along pull-backs -/

/-- The order of vanishing of the image of a unit of the local ring is zero. -/
private theorem ord_algebraMap_eq_zero {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {x : X} (a : X.presheaf.stalk x) (ha : IsUnit a) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField a) x = 0 := by
  by_cases hx : Order.coheight x = 1
  · have hne : algebraMap _ X.functionField a ≠ 0 := (ha.map _).ne_zero
    rw [Scheme.ord_eq_iff hx hne]
    have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    unfold Scheme.ordHom
    simpa using Ring.ordFrac_of_isUnit (K := X.functionField) ha
  · simp [hx]

/-- The order of vanishing of a power. -/
private theorem ord_zpow {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] {x : X}
    {f : X.functionField} (hf : f ≠ 0) (n : ℤ) : X.ord (f ^ n) x = n * X.ord f x := by
  by_cases hx : Order.coheight x = 1
  · rw [Scheme.ord_eq_iff hx (zpow_ne_zero n hf), map_zpow₀, (Scheme.ord_eq_iff hx hf).mp rfl,
      ← WithZero.coe_zpow, ← ofAdd_zsmul, smul_eq_mul]
  · simp [hx]

/-- In the discrete valuation ring `𝒪_{X,x}`, every nonzero rational function is a unit times a
power of a uniformizer `t`. -/
private theorem exists_eq_algebraMap_mul_zpow {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] {x : X} (hx : Order.coheight x = 1)
    [IsDiscreteValuationRing (X.presheaf.stalk x)] {f t : X.functionField}
    (hf : f ≠ 0) (ht : X.ord t x = 1) :
    ∃ u : (X.presheaf.stalk x)ˣ, f =
      algebraMap (X.presheaf.stalk x) X.functionField (u : X.presheaf.stalk x) * t ^ X.ord f x := by
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht
  have h1 : Ring.ordFrac (X.presheaf.stalk x) (t ^ X.ord f x) =
      Ring.ordFrac (X.presheaf.stalk x) f := by
    have e1 := (Scheme.ord_eq_iff hx hf).mp rfl
    have e2 := (Scheme.ord_eq_iff hx ht0).mp ht
    unfold Scheme.ordHom at e1 e2
    rw [map_zpow₀, e1, e2, ← WithZero.coe_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_one]
  obtain ⟨u, hu⟩ := Ring.associated_of_ordFrac_eq _ _ h1
  rw [Units.smul_def, Algebra.smul_def] at hu
  exact ⟨u, hu.symm⟩

/-- On an integral normal scheme every prime divisor `E` has a uniformizer: a rational function
`t` with `ord_E t = 1`. -/
private theorem exists_ord_genericPoint_eq_one {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (E : MMP.Mori.PrimeDivisor X) :
    ∃ t : X.functionField, X.ord t E.genericPoint = 1 := by
  have := E.isDiscreteValuationRing_localRing
  have h1 := E.coheight_genericPoint
  have : Ring.KrullDimLE 1 E.localRing := krullDimLE_of_coheight_le h1.le
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
  have hne : algebraMap E.localRing X.functionField ϖ ≠ 0 :=
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero))
  refine ⟨algebraMap E.localRing X.functionField ϖ, ?_⟩
  rw [Scheme.ord_eq_iff h1 hne]
  exact Ring.ordFrac_irreducible hϖ

/-- **The order of a pull-back over a codimension one point.** Let `g : V ⟶ W` be dominant, `x`
a point of `V` with `g(x)` of codimension one in `W`, and `t` a uniformizer at `g(x)`. Then
`v_x(g^*f) = v_{g(x)}(f) · v_x(g^*t)`. -/
private theorem ord_functionFieldMap_eq_mul [IsIntegral V] [IsIntegral W] [IsLocallyNoetherian V]
    [IsLocallyNoetherian W] (g : V ⟶ W) [IsDominant g] (x : V)
    (hy : Order.coheight (g x) = 1) [IsDiscreteValuationRing (W.presheaf.stalk (g x))]
    {f t : W.functionField} (hf : f ≠ 0) (ht : W.ord t (g x) = 1) :
    V.ord (AlgebraicGeometry.functionFieldMap g f) x =
      W.ord f (g x) * V.ord (AlgebraicGeometry.functionFieldMap g t) x := by
  obtain ⟨u, hu⟩ := exists_eq_algebraMap_mul_zpow hy hf ht
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht
  have hgt : AlgebraicGeometry.functionFieldMap g t ≠ 0 := (map_ne_zero _).mpr ht0
  have hunit : IsUnit ((g.stalkMap x).hom u) := u.isUnit.map _
  calc V.ord (AlgebraicGeometry.functionFieldMap g f) x =
      V.ord (algebraMap _ V.functionField ((g.stalkMap x).hom u) *
        (AlgebraicGeometry.functionFieldMap g t) ^ W.ord f (g x)) x := by
        conv_lhs => rw [hu]
        rw [map_mul, map_zpow₀, MMP.Mori.functionFieldMap_algebraMap_stalk]
    _ = W.ord f (g x) * V.ord (AlgebraicGeometry.functionFieldMap g t) x := by
        rw [Scheme.ord_mul ((hunit.map _).ne_zero) (zpow_ne_zero _ hgt),
          ord_algebraMap_eq_zero _ hunit, zero_add, ord_zpow hgt]

/-- The pull-back of an element of the maximal ideal of `𝒪_{W,g(x)}` has positive order at a
point `x` of codimension one. -/
private theorem ord_functionFieldMap_algebraMap_pos [IsIntegral V] [IsIntegral W]
    [IsLocallyNoetherian V] (g : V ⟶ W) [IsDominant g] (x : V) (hx : Order.coheight x = 1)
    [IsDiscreteValuationRing (V.presheaf.stalk x)] {y : W} (hy : g x = y)
    (ϖ : W.presheaf.stalk y) (hϖ0 : ϖ ≠ 0) (hϖm : ϖ ∈ IsLocalRing.maximalIdeal _) :
    0 < V.ord (AlgebraicGeometry.functionFieldMap g
      (algebraMap (W.presheaf.stalk y) W.functionField ϖ)) x := by
  subst hy
  have hne : AlgebraicGeometry.functionFieldMap g
      (algebraMap (W.presheaf.stalk (g x)) W.functionField ϖ) ≠ 0 :=
    (map_ne_zero _).mpr (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hϖ0))
  rw [MMP.Mori.functionFieldMap_algebraMap_stalk] at hne ⊢
  set a := (g.stalkMap x).hom ϖ
  have ham : a ∈ IsLocalRing.maximalIdeal _ := map_nonunit (g.stalkMap x).hom ϖ hϖm
  have hane : a ≠ 0 := fun h0 => hne (by rw [h0, map_zero])
  have : Ring.KrullDimLE 1 (V.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have e := (Scheme.ord_eq_iff hx hne).mp rfl
  unfold Scheme.ordHom at e
  have h1 := Ring.ordFrac_ge_one_of_ne_zero (K := V.functionField) hane
  have h2 : Ring.ordFrac (V.presheaf.stalk x) (algebraMap _ V.functionField a) ≠ 1 := fun h0 =>
    (IsLocalRing.mem_maximalIdeal a).mp ham
      (Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing.mpr h0)
  rw [e] at h1 h2
  rw [← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le] at h1
  rw [← WithZero.coe_one, Ne, WithZero.coe_inj, ← ofAdd_zero,
    Multiplicative.ofAdd.injective.eq_iff] at h2
  omega

/-- A rational function on `W` pulls back to a unit at every point over the generic point. -/
private theorem ord_functionFieldMap_eq_zero_of_eq_genericPoint [IsIntegral V] [IsIntegral W]
    [IsLocallyNoetherian V] (g : V ⟶ W) [IsDominant g] (x : V) (hy : g x = genericPoint W)
    {f : W.functionField} (hf : f ≠ 0) :
    V.ord (AlgebraicGeometry.functionFieldMap g f) x = 0 := by
  have : ∃ a : W.presheaf.stalk (g x), IsUnit a ∧
      algebraMap (W.presheaf.stalk (g x)) W.functionField a = f := by
    rw [hy]
    have hfield : IsField (W.presheaf.stalk (genericPoint W)) := Field.toIsField W.functionField
    letI : Algebra (W.presheaf.stalk (genericPoint W)) W.functionField :=
      stalkFunctionFieldAlgebra W _
    obtain ⟨a, ha⟩ := (IsFractionRing.surjective_iff_isField
      (R := W.presheaf.stalk (genericPoint W))
      (K := W.functionField)).mpr hfield f
    have ha0 : a ≠ 0 := fun h0 => hf (by rw [← ha, h0, map_zero])
    let := hfield.toField
    exact ⟨a, isUnit_iff_ne_zero.mpr ha0, ha⟩
  obtain ⟨a, ha, rfl⟩ := this
  rw [MMP.Mori.functionFieldMap_algebraMap_stalk]
  exact ord_algebraMap_eq_zero _ (ha.map _)

/-! ### The generic fibre -/

/-- The order of vanishing of an element of the base does not depend on the fraction field in
which it is read. -/
private lemma ordFrac_algebraMap_eq {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] {K K' : Type*} [Field K] [Field K'] [Algebra R K] [Algebra R K']
    [IsFractionRing R K] [IsFractionRing R K'] (x : R) :
    Ring.ordFrac R (algebraMap R K x) = Ring.ordFrac R (algebraMap R K' x) := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Ring.ordFrac_eq_ord (K := K) R hx, Ring.ordFrac_eq_ord (K := K') R hx]

/-- The order of vanishing is invariant under an `R`-algebra map of fraction fields of `R`. -/
private lemma ordFrac_algHom {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] {K K' : Type*} [Field K] [Field K'] [Algebra R K] [Algebra R K']
    [IsFractionRing R K] [IsFractionRing R K'] (σ : K →ₐ[R] K') (k : K) :
    Ring.ordFrac R (σ k) = Ring.ordFrac R k := by
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) k
  dsimp only
  rw [IsFractionRing.mk'_eq_div, map_div₀, AlgHom.commutes, AlgHom.commutes, map_div₀, map_div₀,
    ordFrac_algebraMap_eq (K := K) (K' := K') a,
    ordFrac_algebraMap_eq (K := K) (K' := K') (b : R)]

/-- On an integral normal scheme, the order `E.ord` of a rational function along a prime divisor
`E` is Mathlib's order of vanishing `Scheme.ord` at the generic point `η_E`, read through
`K(X) ≃ X.functionField`. -/
private lemma ord_eq_ord_genericPoint {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (E : MMP.Mori.PrimeDivisor X) (φ : (RationalFunctions X)ˣ) :
    E.ord φ = X.ord (rationalFunctionsEquivFunctionField X φ) E.genericPoint := by
  have hy := E.coheight_genericPoint
  have : Ring.KrullDimLE 1 E.localRing := krullDimLE_of_coheight_le hy.le
  set f := rationalFunctionsEquivFunctionField X (φ : RationalFunctions X) with hfdef
  have hf : f ≠ 0 :=
    (Units.map (rationalFunctionsEquivFunctionField X : RationalFunctions X →* X.functionField)
      φ).ne_zero
  rw [eq_comm, Scheme.ord_eq_iff hy hf]
  change _ = WithZero.exp (E.ord φ)
  rw [← E.valuation_component φ]
  let := E.toComponent.hom.toAlgebra
  have hKc := isFractionRing_stalkToRationalFunctions E.genericPoint_mem_component
  let Kc := X.presheaf.stalk (componentGenericPoint X E.component)
  let ψ : Kc →ₐ[E.localRing] X.functionField :=
    { (X.presheaf.stalkSpecializes (genericPoint_specializes _)).hom with
      commutes' := fun a => by
        exact congrArg (fun h => h.hom a) (TopCat.Presheaf.stalkSpecializes_comp X.presheaf
          (genericPoint_specializes (componentGenericPoint X E.component))
          E.specializes_genericPoint) }
  obtain ⟨V, hV, s, hs⟩ := X.presheaf.exists_germ_eq ((φ : RationalFunctions X) E.component)
  have hVd : Dense (V : Set X) := V.isOpen.dense ⟨_, hV⟩
  have : Subsingleton (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]; infer_instance
  have hψ : ψ ((φ : RationalFunctions X) E.component) = f := by
    rw [← hs]
    change (X.presheaf.germ V _ hV ≫ X.presheaf.stalkSpecializes _).hom s = f
    rw [TopCat.Presheaf.germ_stalkSpecializes]
    have hφ : (φ : RationalFunctions X) =
        (Stacks.Chow.rationalFunctionsEquivStalks X).1 (Stacks.Chow.ofSection X ⟨V, hVd⟩ s) := by
      funext Z
      obtain rfl : Z = E.component := Subsingleton.elim _ _
      rw [(Stacks.Chow.rationalFunctionsEquivStalks X).2 ⟨V, hVd⟩ s E.component hV, ← hs]
    rw [hfdef, hφ]
    change _ = (Stacks.Chow.rationalFunctionsEquivFunctionField X).1
      ((Stacks.Chow.rationalFunctionsEquivStalks X).1.symm
        ((Stacks.Chow.rationalFunctionsEquivStalks X).1 (Stacks.Chow.ofSection X ⟨V, hVd⟩ s)))
    rw [RingEquiv.symm_apply_apply, (Stacks.Chow.rationalFunctionsEquivFunctionField X).2 ⟨V, hVd⟩ s
      ((genericPoint_specializes _).mem_open V.isOpen hV)]
  have hval : E.valuation ((φ : RationalFunctions X) E.component) =
      Ring.ordFrac E.localRing (IsLocalization.algEquiv (nonZeroDivisors E.localRing) Kc
        (FractionRing E.localRing) ((φ : RationalFunctions X) E.component)) := rfl
  rw [hval, ← ordFrac_algHom (ψ.comp (IsLocalization.algEquiv (nonZeroDivisors E.localRing) Kc
    (FractionRing E.localRing)).symm.toAlgHom)]
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply, hψ]
  rfl

/-- The inclusion of the generic fibre of a dominant morphism of integral schemes is dominant:
its image contains the generic point. -/
private theorem isDominant_fiberι (g : V ⟶ W) [IsIntegral V] [IsIntegral W] [IsDominant g] :
    IsDominant (g.fiberι (genericPoint W)) := by
  constructor
  rw [DenseRange, dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro x
  have hη : genericPoint V ∈ Set.range (g.fiberι (genericPoint W)) := by
    rw [Scheme.Hom.range_fiberι]; exact map_genericPoint_of_isDominant g
  exact closure_mono (Set.singleton_subset_iff.mpr hη)
    (specializes_iff_mem_closure.mp ((genericPoint_spec V).specializes trivial))

/-- The function fields of `V` and of its generic fibre agree. -/
private theorem functionFieldMap_fiberι_bijective (g : V ⟶ W) [IsIntegral V] [IsIntegral W]
    [IsIntegral (g.fiber (genericPoint W))] [IsDominant (g.fiberι (genericPoint W))] :
    Function.Bijective (AlgebraicGeometry.functionFieldMap (g.fiberι (genericPoint W))) := by
  have := isIso_stalkMap_fiberι_genericPoint' g (genericPoint (g.fiber (genericPoint W)))
  unfold AlgebraicGeometry.functionFieldMap
  exact (asIso (_ ≫ (g.fiberι (genericPoint W)).stalkMap _)).commRingCatIsoToRingEquiv.bijective

/-! ### Degrees on curves in an open subscheme -/

/-- A point of an open `U` lies in the support of `D|_U` exactly when its image lies in the
support of `D`. -/
private theorem mem_supp_restrictOpen_iff {R : Type*} [Zero R] {X : Scheme.{u}} (U : X.Opens)
    (D : DivisorWithCoeffs R X) (x : U.toScheme) :
    x ∈ (D.restrictOpen U).supp ↔ U.ι x ∈ D.supp := by
  rw [DivisorWithCoeffs.mem_supp_iff, DivisorWithCoeffs.mem_supp_iff]
  constructor
  · rintro ⟨P, hP, hx⟩
    exact ⟨_, hP, (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι P x).mpr
      hx⟩
  · rintro ⟨E, hE, hx⟩
    obtain ⟨P, rfl⟩ :=
      MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support U.ι E x hx
    exact ⟨P, hE, (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι P x).mp
      hx⟩

/-- The restriction to a dense open `U` of a Cartier divisor is its pull-back along `U ⟶ X`. -/
private theorem isPullback_restrictOpen {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (U : X.Opens) [IsIntegral U] [CompactSpace U] [IsDominant U.ι] {N : Divisor X}
    (hN : N.IsCartier) :
    N.IsPullback U.ι (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant U.ι N)
      (N.restrictOpen U) := by
  obtain ⟨N', hN'⟩ := hN.exists_isPullback (f := U.ι)
    (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant U.ι N)
  have hiso : ∀ P : MMP.Mori.PrimeDivisor U, IsIso (U.ι.stalkMap P.genericPoint) := fun P =>
    inferInstanceAs <| IsIso (U.ι.toLRSHom.stalkMap P.genericPoint)
  obtain rfl : N' = N.restrictOpen U := by
    ext P
    change N'.coeff P = (N.restrictOpen U).coeff P
    rw [DivisorWithCoeffs.coeff_restrictOpen]
    exact MMP.Positivity.coeff_eq_of_isPullback P _
      (OpenWeilRestriction.genericPoint_primeDivisorMap U.ι P).symm hN hN'
  exact hN'

/-- **Positivity of an effective divisor near a curve.** Let `G` be a Cartier divisor on `X`
which is effective on an open `U` containing the proper curve `Γ`. If `Γ` meets `Supp G` without
lying in it, then `deg_Γ 𝒪_X(G) > 0`. -/
private theorem degreeOn_pos_of_nonneg_restrictOpen {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [QuasiCompact sX]
    (U : X.Opens) (G : Divisor X) (hG : G.IsCartier) (heff : 0 ≤ G.restrictOpen U)
    (Γ : ProperCurve sX) (hΓU : closure ({Γ.point} : Set X) ⊆ (U : Set X))
    (hne : ∃ x ∈ closure ({Γ.point} : Set X), x ∉ G.supp)
    (hmeet : ∃ x ∈ closure ({Γ.point} : Set X), x ∈ G.supp) :
    0 < G.degreeOn k sX Γ.ι Γ.dim_le hG := by
  have hΓ : Γ.point ∈ U := hΓU (subset_closure rfl)
  haveI : Nonempty U := ⟨⟨_, hΓ⟩⟩
  haveI : IsNoetherian X := {}
  haveI : CompactSpace U.toScheme :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (U : Set X))
  haveI : QuasiCompact U.ι := inferInstance
  haveI : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense ⟨_, hΓ⟩)
  set x0 : U.toScheme := ⟨Γ.point, hΓ⟩
  have hx0 : U.ι x0 = Γ.point := rfl
  have hcl : closure ({U.ι x0} : Set X) ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]; exact hΓU
  obtain ⟨e, he⟩ := MMP.Threefold.Resolution.exists_curveSubschemeAt_iso U.ι x0 rfl hcl
  have hC : IsProperCurve (U.ι ≫ sX) x0 := by
    refine ⟨?_, ?_⟩
    · rw [IsHomeomorph.topologicalKrullDim_eq e.hom e.hom.homeomorph.isHomeomorph]
      exact Γ.dim_eq
    · have hpr : IsProper (curveSubschemeAtι (U.ι x0) ≫ sX) := Γ.isProperCurve.isProper
      have : curveSubschemeAtι x0 ≫ U.ι ≫ sX = e.hom ≫ curveSubschemeAtι (U.ι x0) ≫ sX := by
        rw [← Category.assoc, ← he, Category.assoc]
      rw [this]
      infer_instance
  let C : ProperCurve (U.ι ≫ sX) := ⟨x0, hC⟩
  haveI : IsProper (C.ι ≫ U.ι ≫ sX) := hC.isProper
  haveI : IsIntegral C.scheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure x0
  have hp := isPullback_restrictOpen U hG
  have hGU : Divisor.IsCartier (G.restrictOpen U) := Divisor.IsPullback.isCartier hp hG
  have hdeg : Divisor.degreeOn k (U.ι ≫ sX) C.ι C.dim_le (G.restrictOpen U) hGU =
      G.degreeOn k sX Γ.ι Γ.dim_le hG := by
    have := hG.isInvertibleModule_divisorialSheaf
    have := hGU.isInvertibleModule_divisorialSheaf
    have : IsProper ((C.ι ≫ U.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
    change MMP.Mori.degreeOn k (U.ι ≫ sX) C.ι C.dim_le
        (Divisor.divisorialSheaf (G.restrictOpen U)) =
      MMP.Mori.degreeOn k sX Γ.ι Γ.dim_le G.divisorialSheaf
    rw [degreeOn_eq_of_iso k (U.ι ≫ sX) C.ι C.dim_le
        (Divisor.IsPullback.divisorialSheafIso (hBc := hG) hp),
      degreeOn_pullback_eq_degreeOn_comp (U.ι ≫ sX) sX U.ι C.ι rfl]
    exact MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp k sX (C.ι ≫ U.ι) Γ.ι C.dim_le
      Γ.dim_le e he G.divisorialSheaf
  -- points of `Γ` are images of points of `C`
  have hrange : ∀ x ∈ closure ({Γ.point} : Set X), ∃ c : C.scheme, U.ι (C.ι c) = x := by
    intro x hx
    have hxU : x ∈ U := hΓU hx
    have hx' : (⟨x, hxU⟩ : U.toScheme) ∈ closure ({x0} : Set U.toScheme) := by
      rw [U.ι.isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image, Set.image_singleton]
      exact hx
    have : (⟨x, hxU⟩ : U.toScheme) ∈ Set.range C.ι := by
      change _ ∈ Set.range (curveSubschemeAtι x0)
      rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
        TopologicalSpace.Closeds.coe_closure]
      exact hx'
    obtain ⟨c, hc⟩ := this
    exact ⟨c, by rw [hc]; rfl⟩
  obtain ⟨x, hx, hxS⟩ := hne
  obtain ⟨cx, hcx⟩ := hrange x hx
  obtain ⟨h0, hiff⟩ := MMP.Threefold.Mori.degreeOn_nonneg_and_eq_zero_iff (U.ι ≫ sX) C.ι C.dim_le
    (G.restrictOpen U) hGU heff ⟨cx, by rw [mem_supp_restrictOpen_iff, hcx]; exact hxS⟩
  rw [← hdeg]
  refine lt_of_le_of_ne h0 fun h => ?_
  obtain ⟨y, hy, hyS⟩ := hmeet
  obtain ⟨cy, hcy⟩ := hrange y hy
  exact hiff.mp h.symm cy (by rw [mem_supp_restrictOpen_iff, hcy]; exact hyS)

/-! ### Proper curves in the fibres over closed points -/

/-- The kernel of a quasi-compact morphism `f : X ⟶ Y` from a reduced scheme is the vanishing
ideal of the closure of its image. -/
private theorem ker_eq_vanishingIdeal_closure_range' {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsReduced X] [QuasiCompact f] :
    f.ker = Scheme.IdealSheafData.vanishingIdeal ⟨closure (Set.range f), isClosed_closure⟩ := by
  have hrad : f.ker.radical = f.ker := by
    refine Scheme.IdealSheafData.ext (funext fun U => ?_)
    simp only [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
    refine le_antisymm (fun x ⟨n, hn⟩ => ?_) Ideal.le_radical
    rw [RingHom.mem_ker, map_pow] at hn
    exact RingHom.mem_ker.mpr (IsReduced.eq_zero _ ⟨n, hn⟩)
  rw [← hrad, ← Scheme.IdealSheafData.vanishingIdeal_support]
  congr 1
  exact TopologicalSpace.Closeds.ext (Scheme.Hom.support_ker f)

/-- A point of `X` is the generic point of a proper curve exactly when its image under a closed
immersion `X ⟶ Y` is. -/
private theorem isProperCurve_comp_iff {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    (sY : Y ⟶ Spec (.of k)) (y : X) :
    IsProperCurve (i ≫ sY) y ↔ IsProperCurve sY (i y) := by
  have hrange : closure (Set.range (curveSubschemeAtι y ≫ i)) = closure {i y} := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    change closure (i '' closure {y}) = _
    rw [i.isClosedEmbedding.closure_image_eq, closure_closure, ← Set.image_singleton,
      i.isClosedEmbedding.closure_image_eq]
  have hker : (curveSubschemeAtι y ≫ i).ker = (curveSubschemeAtι (i y)).ker := by
    rw [ker_eq_vanishingIdeal_closure_range', Scheme.IdealSheafData.ker_subschemeι]
    congr 1
    exact TopologicalSpace.Closeds.ext hrange
  haveI := IsClosedImmersion.isIso_of_ker_eq (curveSubschemeAtι y ≫ i)
    (curveSubschemeAtι (i y)) _ (IsClosedImmersion.lift_fac _ _ hker.ge) hker
  set e := IsClosedImmersion.lift (curveSubschemeAtι (i y)) (curveSubschemeAtι y ≫ i) hker.ge
  have hfac : e ≫ curveSubschemeAtι (i y) = curveSubschemeAtι y ≫ i :=
    IsClosedImmersion.lift_fac _ _ _
  have hdim : topologicalKrullDim (curveSubschemeAt y) =
      topologicalKrullDim (curveSubschemeAt (i y)) :=
    IsHomeomorph.topologicalKrullDim_eq _
      (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (asIso e))).isHomeomorph
  have hprop : IsProper (curveSubschemeAtι y ≫ i ≫ sY) ↔
      IsProper (curveSubschemeAtι (i y) ≫ sY) := by
    rw [← Category.assoc, ← hfac, Category.assoc]
    exact MorphismProperty.cancel_left_of_respectsIso @IsProper e _
  exact ⟨fun h => ⟨hdim ▸ h.dim_eq, hprop.mp h.isProper⟩,
    fun h => ⟨hdim ▸ h.dim_eq, hprop.mpr h.isProper⟩⟩

/-- A point of a proper `k`-scheme with no chain of three points below it is closed or the
generic point of a proper curve. -/
private theorem isClosed_or_isProperCurve {G : Scheme.{u}} (sG : G ⟶ Spec (.of k))
    [IsProper sG] (y : G)
    (hno : ∀ w₁ w₂ : G, y ⤳ w₁ → w₁ ⤳ w₂ → y ≠ w₁ → w₁ ≠ w₂ → False) :
    IsClosed ({y} : Set G) ∨ IsProperCurve sG y := by
  by_cases hy : IsClosed ({y} : Set G)
  · exact Or.inl hy
  right
  haveI : CompactSpace G := QuasiCompact.compactSpace_of_compactSpace sG
  obtain ⟨p, hp, hpc⟩ :=
    (isClosed_closure : IsClosed (closure ({y} : Set G))).exists_closed_singleton
      ⟨y, subset_closure rfl⟩
  have hyp : y ⤳ p := specializes_iff_mem_closure.mpr hp
  have hne : y ≠ p := by rintro rfl; exact hy hpc
  refine ⟨MMP.Fourfold.topologicalKrullDim_curveSubschemeAt_eq_one sG hyp hne hpc ?_, ?_⟩
  · intro z hyz hzp
    by_contra hcon
    push Not at hcon
    exact hno z p hyz hzp (Ne.symm hcon.1) hcon.2 |>.elim
  · infer_instance

/-- **Curves in a fibre over a closed point.** Let `g : V ⟶ W` be a proper `k`-morphism, `W`
locally of finite type over `k`, and `c` a closed point of `W` whose fibre has dimension at most
one. Every point of the fibre which is not closed is the generic point of a proper curve. -/
private theorem isProperCurve_of_map_eq (g : V ⟶ W) (hc : g ≫ sW = sV) [IsProper g]
    [LocallyOfFiniteType sW] {c : W} (hcl : IsClosed ({c} : Set W))
    (hdim : topologicalKrullDim (g.base ⁻¹' {c}) ≤ 1) {γ : V} (hγ : g γ = c)
    (hnc : ¬ IsClosed ({γ} : Set V)) : IsProperCurve sV γ := by
  haveI : IsClosedImmersion (W.fromSpecResidueField c) :=
    isClosed_singleton_iff_isClosedImmersion.mp hcl
  haveI : IsClosedImmersion (g.fiberι c) :=
    inferInstanceAs (IsClosedImmersion (Limits.pullback.fst _ _))
  haveI : IsFinite (W.fromSpecResidueField c ≫ sW) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  have hs : g.fiberι c ≫ sV = g.fiberToSpecResidueField c ≫ (W.fromSpecResidueField c ≫ sW) := by
    rw [← hc, ← Category.assoc, Scheme.Hom.fiber_fac, Category.assoc]
  haveI := MMP.Flips.isProper_fiberToSpecResidueField g c
  haveI : IsProper (g.fiberι c ≫ sV) := by rw [hs]; infer_instance
  haveI : LocallyOfFiniteType (g.fiberι c ≫ sV) := by rw [hs]; infer_instance
  obtain ⟨γ', hγ'⟩ : γ ∈ Set.range (g.fiberι c) := by
    rw [Scheme.Hom.range_fiberι]; exact hγ
  have hdimF : topologicalKrullDim (g.fiber c) ≤ 1 := by
    rw [(g.fiberHomeo c).isHomeomorph.topologicalKrullDim_eq]; exact hdim
  rcases isClosed_or_isProperCurve (g.fiberι c ≫ sV) γ' (fun w₁ w₂ h1 h2 h1' h2' =>
      MMP.Chow.DeterminantCurveForm.not_chain_of_topologicalKrullDim_le_one hdimF h1 h2 h1'
        h2') with h | h
  · exfalso
    apply hnc
    have := (g.fiberι c).isClosedEmbedding.isClosedMap _ h
    rwa [Set.image_singleton, hγ'] at this
  · rw [← hγ']
    exact (isProperCurve_comp_iff (g.fiberι c) sV γ').mp h

/-- In a connected Noetherian space, if a closed set `S` contains a point but not every point,
some irreducible component meets `S` without lying in it. -/
private theorem exists_mem_irreducibleComponents_not_subset {T : Type*} [TopologicalSpace T]
    [TopologicalSpace.NoetherianSpace T] [PreconnectedSpace T] (S : Set T) {x y : T}
    (hx : x ∉ S) (hy : y ∈ S) :
    ∃ Z ∈ irreducibleComponents T, ¬ Z ⊆ S ∧ (Z ∩ S).Nonempty := by
  classical
  by_contra hno
  simp only [not_exists, not_and, Set.not_nonempty_iff_eq_empty] at hno
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := T)
  set A := ⋃ Z ∈ {Z ∈ irreducibleComponents T | Z ⊆ S}, Z
  set B := ⋃ Z ∈ {Z ∈ irreducibleComponents T | ¬ Z ⊆ S}, Z
  have hA : IsClosed A := (hfin.subset fun Z hZ => hZ.1).isClosed_biUnion
    fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1
  have hB : IsClosed B := (hfin.subset fun Z hZ => hZ.1).isClosed_biUnion
    fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1
  have hcov : ∀ p : T, p ∈ A ∨ p ∈ B := by
    intro p
    obtain ⟨Z, hZ, hpZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {p}
      isIrreducible_singleton
    by_cases hZS : Z ⊆ S
    · exact Or.inl (Set.mem_biUnion ⟨hZ, hZS⟩ (hpZ rfl))
    · exact Or.inr (Set.mem_biUnion ⟨hZ, hZS⟩ (hpZ rfl))
  have hBS : ∀ p ∈ B, p ∉ S := by
    intro p hp hpS
    obtain ⟨Z, hZ, hpZ⟩ := Set.mem_iUnion₂.mp hp
    exact (Set.eq_empty_iff_forall_notMem.mp (hno Z hZ.1 hZ.2)) p ⟨hpZ, hpS⟩
  have hAS : A ⊆ S := Set.iUnion₂_subset fun Z hZ => hZ.2
  have hyA : y ∈ A := (hcov y).resolve_right fun h => hBS y h hy
  have hxB : x ∈ B := (hcov x).resolve_left fun h => hx (hAS h)
  obtain ⟨p, -, hpA, hpB⟩ := isPreconnected_closed_iff.mp isPreconnected_univ A B hA hB
    (fun p _ => hcov p) ⟨y, trivial, hyA⟩ ⟨x, trivial, hxB⟩
  exact hBS p hpB (hAS hpA)

/-! ### Dimension of the image of a prime divisor -/

/-- A nonempty space has nonnegative dimension. -/
private lemma topologicalKrullDim_nonneg_of_mem {X : Type*} [TopologicalSpace X] (x : X) :
    0 ≤ topologicalKrullDim X := by
  have : Nonempty (TopologicalSpace.IrreducibleCloseds X) :=
    ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  exact Order.krullDim_nonneg

private lemma withBotENat_cases (x : WithBot ℕ∞) :
    x = ⊥ ∨ x = ((⊤ : ℕ∞) : WithBot ℕ∞) ∨ ∃ n : ℕ, x = n := by
  induction x using WithBot.recBotCoe with
  | bot => exact Or.inl rfl
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => exact Or.inr (Or.inl rfl)
    | coe n => exact Or.inr (Or.inr ⟨n, rfl⟩)

/-- The arithmetic of the dimension count: from `d = 1 + dim W`, `dim E + 1 = d`,
`dim E = dim F + dim g(E)` with `dim F ≤ 1`, and `dim g(E) + c = dim W`, the codimension `c` of
`g(E)` is at most one. -/
private lemma le_one_of_dim_eq {d : ℕ} {W A F X : WithBot ℕ∞} {c : ℕ∞}
    (hV : (d : WithBot ℕ∞) = 1 + W) (hx : X + 1 = d) (hE : X = F + A) (hF : F ≤ 1)
    (hF0 : 0 ≤ F) (hA0 : 0 ≤ A) (hw : A + c = W) : c ≤ 1 := by
  subst hE
  rcases withBotENat_cases W with rfl | rfl | ⟨w, rfl⟩
  · simp at hV
  · rw [show (1 : WithBot ℕ∞) = ((1 : ℕ∞) : WithBot ℕ∞) from rfl, ← WithBot.coe_add] at hV
    norm_cast at hV
  rcases withBotENat_cases A with rfl | rfl | ⟨a, rfl⟩
  · exact absurd hA0 (by simp)
  · rw [← WithBot.coe_add] at hw
    norm_cast at hw
  rcases withBotENat_cases F with rfl | rfl | ⟨f, rfl⟩
  · exact absurd hF0 (by simp)
  · exact absurd hF (by norm_cast)
  induction c using ENat.recTopCoe with
  | top =>
    have : ((a : ℕ∞) + ⊤ : ℕ∞) = w := by exact_mod_cast hw
    simp at this
  | coe c =>
    have e1 : d = 1 + w := by exact_mod_cast hV
    have e2 : f + a + 1 = d := by exact_mod_cast hx
    have e3 : a + c = w := by exact_mod_cast hw
    have e4 : f ≤ 1 := by exact_mod_cast hF
    have : c ≤ 1 := by omega
    exact_mod_cast this

/-- **The image of a prime divisor under a morphism with fibres of dimension at most one.** Let
`g : V ⟶ W` be a dominant morphism of integral schemes of finite type over `k` whose generic
fibre is a curve and all of whose fibres have dimension at most one. Then the generic point of a
prime divisor `E` of `V` maps to a point of codimension at most one: `g(E)` is dense in `W` or a
prime divisor of `W`. -/
private theorem coheight_map_genericPoint_le_one [IsIntegral V] [IsIntegral W]
    [LocallyOfFiniteType sV] [LocallyOfFiniteType sW] (g : V ⟶ W) (hc : g ≫ sW = sV)
    [IsDominant g] {d : ℕ} (hd : topologicalKrullDim V = d)
    (h1 : topologicalKrullDim (g.base ⁻¹' {genericPoint W}) = 1)
    (hfib : ∀ w : W, topologicalKrullDim (g.base ⁻¹' {w}) ≤ 1)
    (E : MMP.Mori.PrimeDivisor V) : Order.coheight (g E.genericPoint) ≤ 1 := by
  have hV := MMP.Flips.topologicalKrullDim_eq_fiber_add_closure_range g k sV sW hc
  rw [MMP.Flips.closure_range_eq_closure_genericPoint, map_genericPoint_of_isDominant,
    (g.fiberHomeo _).isHomeomorph.topologicalKrullDim_eq, h1, hd] at hV
  have hWu : topologicalKrullDim (closure ({genericPoint W} : Set W)) = topologicalKrullDim W := by
    rw [(genericPoint_spec W).def]
    exact (Homeomorph.Set.univ W).isHomeomorph.topologicalKrullDim_eq
  rw [hWu] at hV
  have hx := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sV E.genericPoint
  rw [E.coheight_genericPoint, hd] at hx
  have hw := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sW (g E.genericPoint)
  haveI := E.integral
  set I := E.idealSheaf
  have hιg : (I.subschemeι ≫ g) ≫ sW = I.subschemeι ≫ sV := by rw [Category.assoc, hc]
  have hE := MMP.Flips.topologicalKrullDim_eq_fiber_add_closure_range (I.subschemeι ≫ g) k
    (I.subschemeι ≫ sV) sW hιg
  rw [MMP.Flips.closure_range_eq_closure_genericPoint] at hE
  have hgen : (I.subschemeι ≫ g).base (genericPoint I.subscheme) = g E.genericPoint := rfl
  rw [hgen] at hE
  have hdimE : topologicalKrullDim I.subscheme =
      topologicalKrullDim (closure ({E.genericPoint} : Set V)) := by
    rw [I.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq,
      I.range_subschemeι]
    change topologicalKrullDim E.support = _
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  rw [hdimE] at hE
  have hF : topologicalKrullDim ((I.subschemeι ≫ g).fiber (g E.genericPoint)) ≤ 1 := by
    rw [((I.subschemeι ≫ g).fiberHomeo _).isHomeomorph.topologicalKrullDim_eq]
    let f : ((I.subschemeι ≫ g).base ⁻¹' {g E.genericPoint}) → (g.base ⁻¹' {g E.genericPoint}) :=
      fun p => ⟨I.subschemeι p.1, p.2⟩
    have hf : Topology.IsInducing f := by
      rw [← Topology.IsInducing.of_comp_iff Topology.IsInducing.subtypeVal]
      exact I.subschemeι.isClosedEmbedding.isInducing.comp Topology.IsInducing.subtypeVal
    exact hf.topologicalKrullDim_le.trans (hfib _)
  have hF0 : 0 ≤ topologicalKrullDim ((I.subschemeι ≫ g).fiber (g E.genericPoint)) := by
    rw [((I.subschemeι ≫ g).fiberHomeo _).isHomeomorph.topologicalKrullDim_eq]
    exact topologicalKrullDim_nonneg_of_mem
      (⟨genericPoint I.subscheme, hgen⟩ : (I.subschemeι ≫ g).base ⁻¹' {g E.genericPoint})
  have hA0 : 0 ≤ topologicalKrullDim (closure ({g E.genericPoint} : Set W)) :=
    topologicalKrullDim_nonneg_of_mem
      (⟨g E.genericPoint, subset_closure rfl⟩ : closure ({g E.genericPoint} : Set W))
  exact le_one_of_dim_eq hV hx hE hF hF0 hA0 hw

variable [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
  [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]

/-- **Step 1.** Since `𝒪_V(M)` is trivial on the generic fiber, `M` is linearly equivalent to a
divisor none of whose components dominates `W`. -/
private theorem exists_coeff_principalDivisor_add_eq_zero [CharZero k] {d : ℕ} {K : Divisor V}
    {Δ : QDivisor V} {g : V ⟶ W} (h : IsLogEllipticFiberSpace k sV sW d K Δ g)
    [IsDominant g] {n₀ : ℕ} (hn₀ : 0 < n₀) {M : Divisor V}
    (hM : Divisor.toQDivisor M = (n₀ : ℤ) • (Divisor.toQDivisor K + Δ)) (hMc : M.IsCartier) :
    ∃ φ : (RationalFunctions V)ˣ, ∀ E : MMP.Mori.PrimeDivisor V,
      g E.genericPoint = genericPoint W → (M + MMP.Mori.principalDivisor φ).coeff E = 0 := by
  haveI := h.isContraction.isProper
  haveI : IsIntegral (g.fiber (genericPoint W)) := AlgebraicGeometry.isIntegral_fiber_genericPoint g
  haveI : IsProper (g.fiberToSpecResidueField (genericPoint W)) :=
    MMP.Flips.isProper_fiberToSpecResidueField g _
  haveI : IsLocallyNoetherian (g.fiber (genericPoint W)) :=
    LocallyOfFiniteType.isLocallyNoetherian (g.fiberToSpecResidueField (genericPoint W))
  haveI := isNormal_genericFiber g
  haveI : CompactSpace (g.fiber (genericPoint W)) :=
    QuasiCompact.compactSpace_of_compactSpace (g.fiberToSpecResidueField (genericPoint W))
  haveI := isDominant_fiberι g
  set ι := g.fiberι (genericPoint W)
  -- The restriction `M|_{E_g}` and the triviality of its sheaf.
  obtain ⟨DM, hDM⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant ι hMc
  obtain ⟨e⟩ := h.isTrivial_pullback_fiberι_divisorialSheaf hn₀ hM hMc
  let e₀ : (Scheme.Modules.pullback ι).obj M.divisorialSheaf ≅
      SheafOfModules.unit (g.fiber (genericPoint W)).ringCatSheaf := e
  obtain ⟨ψ, hψ⟩ := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso
    (hDM.divisorialSheafIso (hBc := hMc) ≪≫ e₀ ≪≫ Divisor.divisorialSheafZeroIso.symm)
  -- A rational function on `V` restricting to `ψ`.
  obtain ⟨f, hf⟩ := (functionFieldMap_fiberι_bijective g).2
    (rationalFunctionsEquivFunctionField (g.fiber (genericPoint W)) ψ)
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [map_zero] at hf
    exact (ψ.isUnit.map (rationalFunctionsEquivFunctionField (g.fiber (genericPoint W)))).ne_zero
      hf.symm
  let φ : (RationalFunctions V)ˣ :=
    Units.map (rationalFunctionsEquivFunctionField V).symm.toMonoidHom (Units.mk0 f hf0)
  have hφ : rationalFunctionsEquivFunctionField V (φ : RationalFunctions V) = f := by
    simp [φ]
  refine ⟨φ⁻¹, fun P hP => ?_⟩
  obtain ⟨q, hq⟩ : P.genericPoint ∈ Set.range ι := by
    rw [Scheme.Hom.range_fiberι]; exact hP
  have hc : Order.coheight q = 1 := by
    rw [← coheight_fiberι_genericPoint g q]
    change Order.coheight (ι q) = 1
    rw [hq]; exact P.coheight_genericPoint
  set Q : MMP.Mori.PrimeDivisor (g.fiber (genericPoint W)) :=
    AlgebraicGeometry.PrimeDivisor.ofCoheightOne q hc
  have hQ : ι Q.genericPoint = P.genericPoint := by
    change ι (AlgebraicGeometry.PrimeDivisor.genericPoint
      (AlgebraicGeometry.PrimeDivisor.ofCoheightOne q hc)) = _
    rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]; exact hq
  haveI := isIso_stalkMap_fiberι_genericPoint' g Q.genericPoint
  have h1 : DM.coeff Q = M.coeff P := by
    obtain ⟨U, hU, φM, hφM⟩ := hMc P.genericPoint
    rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hDM hφM Q (hQ ▸ hU) P.component,
      MMP.Positivity.ord_functionFieldMap_of_isIso ι Q P hQ,
      ← MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord]
    exact (hφM P ((P.genericPoint_mem_iff U).mp hU)).symm
  have h2 : DM.coeff Q = Q.ord ψ := by
    simpa using congrArg (fun D : Divisor _ => D.coeff Q) hψ
  have h3 : Q.ord ψ = P.ord φ := by
    rw [ord_eq_ord_genericPoint Q ψ, ord_eq_ord_genericPoint P φ, ← hf,
      MMP.Positivity.ord_functionFieldMap_of_isIso ι Q P hQ, hφ]
  rw [DivisorWithCoeffs.coeff_add, coeff_principalDivisor, PrimeDivisor.ord_inv, ← h1, h2, h3,
    add_neg_cancel]

/-- **Step 2.** If every fiber of `g` has pure dimension one, the generic point of every prime
divisor of `V` maps to the generic point of `W` or to that of a prime divisor of `W`. -/
private theorem map_genericPoint_eq {d : ℕ} {K : Divisor V} {Δ : QDivisor V} {g : V ⟶ W}
    (h : IsLogEllipticFiberSpace k sV sW d K Δ g)
    (hfib : ∀ w : W, ∀ Y ∈ irreducibleComponents (g.base ⁻¹' {w}), topologicalKrullDim Y = 1)
    (E : MMP.Mori.PrimeDivisor V) :
    g E.genericPoint = genericPoint W ∨
      ∃ C : MMP.Mori.PrimeDivisor W, g E.genericPoint = C.genericPoint := by
  haveI := h.isContraction.isVariety_source.toLocallyOfFiniteType
  haveI := h.isContraction.isVariety_target.toLocallyOfFiniteType
  haveI : IsDominant g := isDominant_of_forall_isIso_app g h.isContraction.isIso_app
  have hle := coheight_map_genericPoint_le_one g h.isContraction.comp_eq
    h.isCanonicalDivisor.topologicalKrullDim_eq h.dim_genericFiber
    (fun w => MMP.Flips.topologicalKrullDim_le_of_forall_mem_irreducibleComponents
      fun Y hY => (hfib w Y hY).le) E
  by_cases h0 : Order.coheight (g E.genericPoint) = 0
  · exact Or.inl (eq_genericPoint_of_coheight_eq_zero h0)
  · right
    have h1 : Order.coheight (g E.genericPoint) = 1 :=
      le_antisymm hle (ENat.one_le_iff_ne_zero.mpr h0)
    exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h1,
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ h1).symm⟩

/-- **The extremal step of Zariski's lemma.** Let `G` be a Cartier divisor on `V` without
components dominating `W`, of nonpositive degree on every proper curve contracted by `g`, and
effective along the prime divisors over a prime divisor `C` of `W`. Then `G` cannot vanish along
one prime divisor over `C` and be positive along another: at a closed point `c` of `C` near the
generic point of `C`, a component of the connected fibre `g⁻¹(c)` meeting `Supp G` without lying
in it would have positive degree. -/
private theorem false_of_coeff_eq_zero_of_coeff_pos {d : ℕ} {K : Divisor V} {Δ : QDivisor V}
    {g : V ⟶ W} (h : IsLogEllipticFiberSpace k sV sW d K Δ g) [IsDominant g]
    (hfib : ∀ w : W, ∀ Y ∈ irreducibleComponents (g.base ⁻¹' {w}), topologicalKrullDim Y = 1)
    (G : Divisor V) (hGc : G.IsCartier)
    (hG : ∀ Γ : ProperCurve sV, Γ.IsContractedBy g → G.degreeOn k sV Γ.ι Γ.dim_le hGc ≤ 0)
    (hGv : ∀ E : MMP.Mori.PrimeDivisor V, g E.genericPoint = genericPoint W → G.coeff E = 0)
    (C : MMP.Mori.PrimeDivisor W)
    (hGC : ∀ E : MMP.Mori.PrimeDivisor V, g E.genericPoint = C.genericPoint → 0 ≤ G.coeff E)
    {E₀ E₁ : MMP.Mori.PrimeDivisor V} (h₀ : g E₀.genericPoint = C.genericPoint)
    (h₁ : g E₁.genericPoint = C.genericPoint) (hE₀ : G.coeff E₀ = 0) (hE₁ : 0 < G.coeff E₁) :
    False := by
  classical
  haveI := h.isContraction.isProper
  haveI := h.isContraction.isVariety_source.toLocallyOfFiniteType
  haveI := h.isContraction.isVariety_target.toLocallyOfFiniteType
  haveI := h.isContraction.isVariety_source.toQuasiCompact
  have hc := h.isContraction.comp_eq
  have gm : ∀ E : MMP.Mori.PrimeDivisor V, E.genericPoint ∈ E.support := fun E => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have hdim1 : ∀ w : W, topologicalKrullDim (g.base ⁻¹' {w}) ≤ 1 := fun w =>
    MMP.Flips.topologicalKrullDim_le_of_forall_mem_irreducibleComponents
      fun Y hY => (hfib w Y hY).le
  -- The images of the components of `G` not over `C`.
  set S : Finset (MMP.Mori.PrimeDivisor V) :=
    G.support.filter (fun E => g E.genericPoint ≠ C.genericPoint)
  set B₀ : Set W := ⋃ E ∈ S, g '' E.support
  have hB₀ : IsClosed B₀ := S.finite_toSet.isClosed_biUnion fun E _ =>
    g.isClosedMap _ E.idealSheaf.support.isClosed
  have hξ : C.genericPoint ∉ B₀ := by
    intro hm
    obtain ⟨E, hES, z, hz, hzC⟩ := Set.mem_iUnion₂.mp hm
    rw [Finset.mem_filter, Finsupp.mem_support_iff] at hES
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hz
    have hsp : g E.genericPoint ⤳ C.genericPoint :=
      hzC ▸ (specializes_iff_mem_closure.mpr hz).map g.continuous
    rcases map_genericPoint_eq h hfib E with hη | ⟨C', hC'⟩
    · exact hES.1 (hGv E hη)
    · rw [hC'] at hsp
      exact hES.2 (by rw [hC', primeDivisor_eq_of_specializes hsp])
  set U₀ : W.Opens := ⟨B₀ᶜ, hB₀.isOpen_compl⟩
  set U : V.Opens := g ⁻¹ᵁ U₀
  have heff : 0 ≤ G.restrictOpen U := by
    intro P
    change 0 ≤ G.coeff (OpenWeilRestriction.primeDivisorMap U.ι P)
    set E := OpenWeilRestriction.primeDivisorMap U.ι P
    by_cases hEC : g E.genericPoint = C.genericPoint
    · exact hGC E hEC
    · by_contra hneg
      have hEU : E.genericPoint ∈ U := by
        rw [OpenWeilRestriction.genericPoint_primeDivisorMap]; exact P.genericPoint.2
      apply hEU
      refine Set.mem_iUnion₂.mpr ⟨E, ?_, E.genericPoint, ?_, rfl⟩
      · rw [Finset.mem_filter, Finsupp.mem_support_iff]
        exact ⟨fun h0 => hneg (by rw [DivisorWithCoeffs.coeff] at *; rw [h0]), hEC⟩
      · exact gm E
  -- A closed point of `E₀` near the generic point of `C`, outside `Supp G`.
  haveI : JacobsonSpace V := LocallyOfFiniteType.jacobsonSpace sV
  have hE₀U : E₀.genericPoint ∈ U := by
    change g E₀.genericPoint ∈ U₀
    rw [h₀]; exact hξ
  have hE₀G : E₀.genericPoint ∉ G.supp := by
    intro hm
    obtain ⟨E, hE, hmE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hm
    have hEE : E = E₀ := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (PrimeDivisor.eq_genericPoint_of_mem_support E hmE E₀.coheight_genericPoint).symm
    exact hE (hEE ▸ hE₀)
  obtain ⟨x, ⟨hxE, hxU, hxG⟩, hxc⟩ := nonempty_inter_closedPoints
    (Z := E₀.support ∩ ((U : Set V) ∩ (G.supp : Set V)ᶜ))
    ⟨E₀.genericPoint, gm E₀, hE₀U, hE₀G⟩
    (E₀.idealSheaf.support.isClosed.isLocallyClosed.inter
      (U.isOpen.inter G.supp.isClosed.isOpen_compl).isLocallyClosed)
  set c := g x
  have hcl : IsClosed ({c} : Set W) := by
    simpa only [Set.image_singleton] using g.isClosedMap _ hxc
  have hcC : c ∈ closure ({C.genericPoint} : Set W) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxE
    rw [← h₀]
    exact (specializes_iff_mem_closure.mpr hxE).map g.continuous |>.mem_closed isClosed_closure
      (subset_closure rfl)
  obtain ⟨y, hyE, hyc⟩ : c ∈ g '' E₁.support := by
    have hcl₁ : IsClosed (g '' E₁.support) := g.isClosedMap _ E₁.idealSheaf.support.isClosed
    refine closure_minimal ?_ hcl₁ hcC
    rw [Set.singleton_subset_iff, ← h₁]
    exact ⟨_, gm E₁, rfl⟩
  have hyG : y ∈ G.supp := DivisorWithCoeffs.support_subset_supp hE₁.ne' hyE
  -- The connected fibre over `c` and a component meeting `Supp G` without lying in it.
  have hΦ : IsClosed (g.base ⁻¹' {c}) := hcl.preimage g.continuous
  have hconn := g.isConnected_preimage_singleton_of_isIso_app h.isContraction.isIso_app c
  haveI : PreconnectedSpace (g.base ⁻¹' {c}) :=
    isPreconnected_iff_preconnectedSpace.mp hconn.isPreconnected
  haveI : IsNoetherian V := {}
  obtain ⟨Z, hZ, hZS, hZm⟩ := exists_mem_irreducibleComponents_not_subset
    (T := g.base ⁻¹' {c}) (Subtype.val ⁻¹' (G.supp : Set V)) (x := ⟨x, rfl⟩) (y := ⟨y, hyc⟩)
    hxG hyG
  have hZirr : IsIrreducible (Subtype.val '' Z) := hZ.1.image _ continuous_subtype_val.continuousOn
  have hZcl : IsClosed (Subtype.val '' Z) :=
    (hΦ.isClosedEmbedding_subtypeVal).isClosedMap _ (isClosed_of_mem_irreducibleComponents Z hZ)
  set γ := hZirr.genericPoint
  have hγ : closure ({γ} : Set V) = Subtype.val '' Z := by
    rw [(hZirr.isGenericPoint_genericPoint hZcl).def]
  have hγZ : γ ∈ Subtype.val '' Z := hγ ▸ subset_closure rfl
  have hgγ : g γ = c := by
    obtain ⟨z, -, hz⟩ := hγZ
    rw [← hz]; exact z.2
  have hdimZ : topologicalKrullDim (Subtype.val '' Z) = 1 := by
    have hemb : Topology.IsEmbedding (fun z : Z => (z : g.base ⁻¹' {c}).1) :=
      Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
    have hr : Set.range (fun z : Z => (z : g.base ⁻¹' {c}).1) = Subtype.val '' Z := by
      ext p; simp
    rw [← hfib c Z hZ, hemb.toHomeomorph.isHomeomorph.topologicalKrullDim_eq, hr]
  have hnc : ¬ IsClosed ({γ} : Set V) := by
    intro hcl'
    have hZγ : Subtype.val '' Z = {γ} := by rw [← hγ, hcl'.closure_eq]
    rw [hZγ] at hdimZ
    haveI : Subsingleton ({γ} : Set V) := Set.subsingleton_singleton.coe_sort
    have h0 := topologicalKrullDim_zero_of_discreteTopology ({γ} : Set V)
    rw [hdimZ] at h0
    exact absurd h0 (by decide)
  let Γ : ProperCurve sV := ⟨γ, isProperCurve_of_map_eq g hc hcl (hdim1 c) hgγ hnc⟩
  have hfibΓ : ∀ z ∈ closure ({Γ.point} : Set V), g z = c := by
    intro z hz
    change z ∈ closure ({γ} : Set V) at hz
    rw [hγ] at hz
    obtain ⟨w, -, rfl⟩ := hz
    exact w.2
  have hcontr : Γ.IsContractedBy g := fun z hz => (hfibΓ z hz).trans hgγ.symm
  have hsubU : closure ({Γ.point} : Set V) ⊆ (U : Set V) := fun z hz => by
    change g z ∈ U₀
    rw [hfibΓ z hz]
    exact hxU
  have hne : ∃ z ∈ closure ({Γ.point} : Set V), z ∉ G.supp := by
    obtain ⟨w, hwZ, hw⟩ := Set.not_subset.mp hZS
    exact ⟨w.1, by change w.1 ∈ closure ({γ} : Set V); rw [hγ]; exact ⟨w, hwZ, rfl⟩, hw⟩
  have hmeet : ∃ z ∈ closure ({Γ.point} : Set V), z ∈ G.supp := by
    obtain ⟨w, hwZ, hw⟩ := hZm
    exact ⟨w.1, by change w.1 ∈ closure ({γ} : Set V); rw [hγ]; exact ⟨w, hwZ, rfl⟩, hw⟩
  exact absurd (hG Γ hcontr)
    (not_le.mpr (degreeOn_pos_of_nonneg_restrictOpen sV U G hGc heff Γ hsubU hne hmeet))

/-- **Step 3 (Zariski's lemma).** Let `D` be a Cartier divisor on `V` without components
dominating `W`, of nonnegative degree on every proper curve contracted by `g`. Along each prime
divisor `C` of `W`, the components of `D` over `C` have coefficients proportional to their
multiplicities in `g^*C`. -/
private theorem exists_coeff_eq_mul_ord {d : ℕ} {K : Divisor V} {Δ : QDivisor V} {g : V ⟶ W}
    (h : IsLogEllipticFiberSpace k sV sW d K Δ g) [IsDominant g]
    (hfib : ∀ w : W, ∀ Y ∈ irreducibleComponents (g.base ⁻¹' {w}), topologicalKrullDim Y = 1)
    (D : Divisor V) (hDc : D.IsCartier)
    (hD : ∀ Γ : ProperCurve sV, Γ.IsContractedBy g →
      0 ≤ D.degreeOn k sV Γ.ι Γ.dim_le hDc)
    (hDv : ∀ E : MMP.Mori.PrimeDivisor V, g E.genericPoint = genericPoint W → D.coeff E = 0)
    (C : MMP.Mori.PrimeDivisor W) :
    ∃ r : ℚ, ∀ E : MMP.Mori.PrimeDivisor V, g E.genericPoint = C.genericPoint →
      ∀ t : W.functionField, W.ord t C.genericPoint = 1 →
        (D.coeff E : ℚ) = r * V.ord (AlgebraicGeometry.functionFieldMap g t) E.genericPoint := by
  classical
  haveI := C.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible C.localRing
  set t : W.functionField := algebraMap (W.presheaf.stalk C.genericPoint) W.functionField ϖ
  have h1C := C.coheight_genericPoint
  have hKC : Ring.KrullDimLE 1 C.localRing := krullDimLE_of_coheight_le h1C.le
  have ht0 : t ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)
  have ht : W.ord t C.genericPoint = 1 := by
    rw [Scheme.ord_eq_iff h1C ht0]
    exact Ring.ordFrac_irreducible hϖ
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal _ := (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
  -- The multiplicities `ord_E (g^* t)` do not depend on the uniformizer.
  have hindep : ∀ E : MMP.Mori.PrimeDivisor V, g E.genericPoint = C.genericPoint →
      ∀ t' : W.functionField, W.ord t' C.genericPoint = 1 →
        V.ord (AlgebraicGeometry.functionFieldMap g t') E.genericPoint =
          V.ord (AlgebraicGeometry.functionFieldMap g t) E.genericPoint := by
    intro E hE t' ht'
    haveI : IsDiscreteValuationRing (W.presheaf.stalk (g E.genericPoint)) := by
      rw [hE]; exact C.isDiscreteValuationRing_localRing
    rw [ord_functionFieldMap_eq_mul g E.genericPoint (hE ▸ h1C) ht0 (hE ▸ ht'), hE, ht, one_mul]
  suffices H : ∃ r : ℚ, ∀ E : MMP.Mori.PrimeDivisor V, g E.genericPoint = C.genericPoint →
      (D.coeff E : ℚ) = r * V.ord (AlgebraicGeometry.functionFieldMap g t) E.genericPoint by
    obtain ⟨r, hr⟩ := H
    exact ⟨r, fun E hE t' ht' => by rw [hr E hE, hindep E hE t' ht']⟩
  set ft := AlgebraicGeometry.functionFieldMap g t
  have hft0 : ft ≠ 0 := (map_ne_zero _).mpr ht0
  have hfpos : ∀ E : MMP.Mori.PrimeDivisor V, g E.genericPoint = C.genericPoint →
      0 < V.ord ft E.genericPoint := fun E hE => by
    haveI := E.isDiscreteValuationRing_localRing
    exact ord_functionFieldMap_algebraMap_pos g E.genericPoint E.coheight_genericPoint hE ϖ
      hϖ.ne_zero hϖm
  -- The principal divisor `F = div(g^* t)`.
  let φt : (RationalFunctions V)ˣ :=
    Units.map (rationalFunctionsEquivFunctionField V).symm.toMonoidHom (Units.mk0 ft hft0)
  set F := MMP.Mori.principalDivisor φt
  have hF : ∀ E : MMP.Mori.PrimeDivisor V, F.coeff E = V.ord ft E.genericPoint := fun E => by
    rw [coeff_principalDivisor, ord_eq_ord_genericPoint E φt]
    simp [φt]
  have hFc : F.IsCartier := Divisor.isCartier_principalDivisor φt
  set T : Set (MMP.Mori.PrimeDivisor V) := {E | g E.genericPoint = C.genericPoint}
  have hTfin : T.Finite := F.support.finite_toSet.subset fun E hE => by
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    change F.coeff E ≠ 0
    rw [hF E]; exact (hfpos E hE).ne'
  by_cases hT : ∀ E ∈ T, D.coeff E = 0
  · exact ⟨0, fun E hE => by simp [hT E hE]⟩
  push Not at hT
  obtain ⟨E₂, hE₂, -⟩ := hT
  let ρ : MMP.Mori.PrimeDivisor V → ℚ := fun E => (D.coeff E : ℚ) / V.ord ft E.genericPoint
  obtain ⟨E₀, hE₀, hmax⟩ := Set.exists_max_image T ρ hTfin ⟨E₂, hE₂⟩
  refine ⟨ρ E₀, fun E₁ hE₁ => ?_⟩
  have hf₀ : (0 : ℚ) < V.ord ft E₀.genericPoint := by exact_mod_cast hfpos E₀ hE₀
  have hf₁ : (0 : ℚ) < V.ord ft E₁.genericPoint := by exact_mod_cast hfpos E₁ hE₁
  by_contra hne
  have hlt : (D.coeff E₁ : ℚ) < ρ E₀ * V.ord ft E₁.genericPoint :=
    lt_of_le_of_ne ((div_le_iff₀ hf₁).mp (hmax E₁ hE₁)) hne
  -- The divisor `G = a F - b D` with `ρ E₀ = a / b`.
  set r := ρ E₀
  set a : ℤ := r.num
  set b : ℕ := r.den
  have hb : (0 : ℚ) < b := by exact_mod_cast r.den_pos
  have hab : (a : ℚ) = r * b := r.mul_den_eq_num.symm
  set G : Divisor V := a • F + (-(b : ℤ)) • D
  have hGcoeff : ∀ E, (G.coeff E : ℚ) = a * V.ord ft E.genericPoint - b * D.coeff E := by
    intro E
    simp only [G, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, hF, smul_eq_mul]
    push_cast; ring
  have hGc : G.IsCartier := (hFc.zsmul a).add (hDc.zsmul _)
  have hGdeg : ∀ Γ : ProperCurve sV, Γ.IsContractedBy g →
      G.degreeOn k sV Γ.ι Γ.dim_le hGc ≤ 0 := by
    intro Γ hΓ
    rw [Divisor.degreeOn_add k sV Γ.ι Γ.dim_le _ _ (hFc.zsmul a) (hDc.zsmul _),
      Divisor.degreeOn_zsmul' k sV Γ.ι Γ.dim_le F hFc,
      Divisor.degreeOn_zsmul' k sV Γ.ι Γ.dim_le D hDc,
      Divisor.degreeOn_eq_zero_of_linearlyEquivalent sV Γ.ι Γ.dim_le hFc ⟨φt, by simp [F]⟩]
    nlinarith [hD Γ hΓ]
  have hGv : ∀ E : MMP.Mori.PrimeDivisor V, g E.genericPoint = genericPoint W →
      G.coeff E = 0 := by
    intro E hE
    have h1 := hGcoeff E
    rw [ord_functionFieldMap_eq_zero_of_eq_genericPoint g E.genericPoint hE ht0, hDv E hE] at h1
    exact_mod_cast (by simpa using h1 : (G.coeff E : ℚ) = 0)
  have hGC : ∀ E : MMP.Mori.PrimeDivisor V, g E.genericPoint = C.genericPoint →
      0 ≤ G.coeff E := by
    intro E hE
    have hfE : (0 : ℚ) < V.ord ft E.genericPoint := by exact_mod_cast hfpos E hE
    have hρ : (D.coeff E : ℚ) ≤ r * V.ord ft E.genericPoint := (div_le_iff₀ hfE).mp (hmax E hE)
    have : (0 : ℚ) ≤ G.coeff E := by
      rw [hGcoeff, hab]
      nlinarith
    exact_mod_cast this
  have hG₀ : G.coeff E₀ = 0 := by
    have : (G.coeff E₀ : ℚ) = 0 := by
      rw [hGcoeff, hab]
      have : r * V.ord ft E₀.genericPoint = D.coeff E₀ := by
        simp only [r, ρ]
        field_simp
      nlinarith
    exact_mod_cast this
  have hG₁ : 0 < G.coeff E₁ := by
    have : (0 : ℚ) < G.coeff E₁ := by rw [hGcoeff, hab]; nlinarith
    exact_mod_cast this
  exact false_of_coeff_eq_zero_of_coeff_pos h hfib G hGc hGdeg hGv C hGC hE₀ hE₁ hG₀ hG₁

/-! ### Commutative algebra: Zariski's main theorem and Galois conjugacy -/

/-- **Zariski's main theorem, in the form used here.** Let `R` be a finite type `S`-algebra which
is a domain, quasi-finite over `S` at a prime `p`, and `L` a field containing `R`. Then there are
an element `r` of the integral closure `C` of `S` in `L` and a prime `x` of `C` not containing
`r`, lying over the same prime of `S` as `p`, such that `R ⟶ L` factors through `C[1/r]`. -/
private theorem exists_away_of_quasiFiniteAt {S R L : Type*} [CommRing S] [CommRing R]
    [IsDomain R] [Field L] [Algebra S R] [Algebra S L] [Algebra R L] [IsScalarTower S R L]
    [Algebra.FiniteType S R] (hRL : Function.Injective (algebraMap R L)) (p : Ideal R) [p.IsPrime]
    [Algebra.QuasiFiniteAt S p] :
    ∃ (r : integralClosure S L) (hr : IsUnit ((integralClosure S L).val r))
      (x : Ideal (integralClosure S L)), x.IsPrime ∧ r ∉ x ∧
      x.comap (algebraMap S (integralClosure S L)) = p.comap (algebraMap S R) ∧
      ∃ θ : R →+* Localization.Away r,
        θ.comp (algebraMap S R) = algebraMap S (Localization.Away r) ∧
        ∀ a : R, Localization.awayLift (integralClosure S L).val.toRingHom r hr (θ a) =
          algebraMap R L a := by
  obtain ⟨r, hrp, hbij⟩ := Algebra.ZariskisMainProperty.of_finiteType (R := S) p
  set r₁ : R := r.1 with hr₁
  let ι : integralClosure S R →ₐ[S] integralClosure S L :=
    { toFun := fun a => ⟨algebraMap R L a.1, (a.2.map (IsScalarTower.toAlgHom S R L))⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp
      commutes' := fun s => by ext; simp [← IsScalarTower.algebraMap_apply] }
  have hι : ∀ a, ((ι a : integralClosure S L) : L) = algebraMap R L a.1 := fun _ => rfl
  have hιinj : Function.Injective ι := fun a b hab =>
    Subtype.ext (hRL (congrArg Subtype.val hab))
  have hr0 : algebraMap R L r₁ ≠ 0 := fun h0 =>
    hrp <| (map_eq_zero_iff _ hRL).mp h0 ▸ p.zero_mem
  have hr : IsUnit ((integralClosure S L).val (ι r)) := isUnit_iff_ne_zero.mpr hr0
  let e : Localization.Away r ≃+* Localization.Away r₁ := RingEquiv.ofBijective _ hbij
  have he : ∀ s : integralClosure S R, e (algebraMap _ _ s) = algebraMap R _ s.1 := by
    intro s
    change Localization.awayMap (integralClosure S R).val.toRingHom r (algebraMap _ _ s) = _
    exact IsLocalization.map_eq _ _
  let θ : R →+* Localization.Away (ι r) :=
    (Localization.awayMap ι.toRingHom r).comp
      (e.symm.toRingHom.comp (algebraMap R (Localization.Away r₁)))
  let F := Localization.awayLift (integralClosure S L).val.toRingHom (ι r) hr
  let G := Localization.awayLift (algebraMap R L) r₁ (isUnit_iff_ne_zero.mpr hr0)
  have hFG : F.comp (Localization.awayMap ι.toRingHom r) = G.comp e.toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    ext s
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, he]
    simp only [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq, F, G,
      Localization.awayLift, IsLocalization.Away.lift]
    erw [IsLocalization.lift_eq, IsLocalization.lift_eq]
    rfl
  have hFθ : ∀ a : R, F (θ a) = algebraMap R L a := by
    intro a
    have := congrArg (fun φ => φ (e.symm (algebraMap R _ a))) hFG
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply] at this
    change F (Localization.awayMap ι.toRingHom r (e.symm (algebraMap R _ a))) = _
    rw [this]
    simp only [G, Localization.awayLift, IsLocalization.Away.lift]
    erw [IsLocalization.lift_eq]
  have hFinj : Function.Injective F := by
    have hne : ι r ≠ 0 := fun h0 => hr0 (by rw [← hι r, h0]; rfl)
    have hloc : Function.Injective (algebraMap (integralClosure S L) (Localization.Away (ι r))) :=
      IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hne)
    refine (IsLocalization.lift_injective_iff _).mpr fun a b => ?_
    exact ⟨fun h => by rw [hloc h], fun h => by rw [Subtype.val_injective h]⟩
  letI : Algebra (integralClosure S R) (integralClosure S L) := ι.toRingHom.toAlgebra
  haveI : IsScalarTower S (integralClosure S R) (integralClosure S L) :=
    IsScalarTower.of_algebraMap_eq fun s => (ι.commutes s).symm
  haveI : Algebra.IsIntegral (integralClosure S R) (integralClosure S L) :=
    Algebra.IsIntegral.tower_top S
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (p.comap (integralClosure S R).val.toRingHom) (⊥ : Ideal (integralClosure S L))
    (by
      intro a ha
      have : ι a = 0 := ha
      rw [hιinj (this.trans (map_zero ι).symm)]
      exact Ideal.zero_mem _)
  refine ⟨ι r, hr, Q, hQ, fun hrQ => hrp ?_, ?_, θ, ?_, hFθ⟩
  · have : r ∈ Q.comap (algebraMap (integralClosure S R) (integralClosure S L)) := hrQ
    rwa [show Q.comap (algebraMap (integralClosure S R) (integralClosure S L)) = _ from hQc] at this
  · rw [IsScalarTower.algebraMap_eq S (integralClosure S R) (integralClosure S L),
      ← Ideal.comap_comap,
      show Q.comap (algebraMap (integralClosure S R) (integralClosure S L)) = _ from hQc,
      Ideal.comap_comap]
    rfl
  · refine RingHom.ext fun s => hFinj ?_
    rw [RingHom.comp_apply, hFθ, IsScalarTower.algebraMap_apply S (integralClosure S L)
      (Localization.Away (ι r))]
    simp only [F, Localization.awayLift, IsLocalization.Away.lift]
    erw [IsLocalization.lift_eq]
    simp [← IsScalarTower.algebraMap_apply]

open scoped Pointwise in
/-- **Galois conjugacy of primes.** In the integral closure `B` of an integrally closed domain `A`
in a finite Galois extension `L` of its fraction field `K`, two primes over the same prime of `A`
are conjugate under an `A`-automorphism of `B`. -/
private theorem exists_algEquiv_comap_eq {A K L B : Type*} [CommRing A] [CommRing B] [Field K]
    [Field L] [Algebra A K] [Algebra B L] [IsFractionRing A K] [IsFractionRing B L]
    [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [IsIntegrallyClosed A] [IsIntegralClosure B A L] [FiniteDimensional K L] [IsGalois K L]
    (P Q : Ideal B) [P.IsPrime] [Q.IsPrime]
    (h : P.comap (algebraMap A B) = Q.comap (algebraMap A B)) :
    ∃ σ : B ≃ₐ[A] B, Q.comap (σ : B →+* B) = P := by
  letI := IsIntegralClosure.MulSemiringAction A K L B
  haveI := Algebra.isInvariant_of_isGalois A K L B
  haveI : SMulCommClass Gal(L/K) A B := ⟨fun g a b => by
    change galRestrict A K L B g (a • b) = a • galRestrict A K L B g b
    exact map_smul _ _ _⟩
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A B Gal(L/K) P Q h
  refine ⟨galRestrict A K L B g, ?_⟩
  rw [hg, Ideal.pointwise_smul_def]
  change Ideal.comap _ (Ideal.map (galRestrict A K L B g : B →+* B) P) = P
  exact Ideal.comap_map_of_bijective _ (galRestrict A K L B g).bijective

/-- Elements of a finite type `S`-algebra quasi-finite at a prime are algebraic over `Frac S`:
by Zariski's main theorem `r^m a` is integral over `S` for a suitable `r ≠ 0`. -/
private theorem isAlgebraic_of_quasiFiniteAt {S R : Type*} [CommRing S] [IsDomain S] [CommRing R]
    [IsDomain R] [Algebra S R] [Algebra.FiniteType S R] [FaithfulSMul S R] (p : Ideal R)
    [p.IsPrime] [Algebra.QuasiFiniteAt S p] :
    letI : Algebra (FractionRing S) (FractionRing R) := FractionRing.liftAlgebra _ _
    ∀ a : R, IsAlgebraic (FractionRing S) (algebraMap R (FractionRing R) a) := by
  letI : Algebra (FractionRing S) (FractionRing R) := FractionRing.liftAlgebra _ _
  obtain ⟨r, hrp, hr, hint⟩ := (Algebra.zariskisMainProperty_iff (R := S)).mp
    (Algebra.ZariskisMainProperty.of_finiteType (R := S) p)
  set K := FractionRing S
  set KR := FractionRing R
  have hr0 : algebraMap R KR r ≠ 0 := fun h0 =>
    hrp <| (IsFractionRing.injective R KR (h0.trans (map_zero _).symm)) ▸ p.zero_mem
  intro a
  obtain ⟨m, hm⟩ := hint a
  have h1 : IsIntegral K (algebraMap R KR (r ^ m * a)) :=
    (hm.map (IsScalarTower.toAlgHom S R KR)).tower_top
  have h2 : IsIntegral K (algebraMap R KR r) := (hr.map (IsScalarTower.toAlgHom S R KR)).tower_top
  have h3 : IsAlgebraic K ((algebraMap R KR r ^ m)⁻¹) := (h2.isAlgebraic.pow m).inv
  have : algebraMap R KR a = (algebraMap R KR r ^ m)⁻¹ * algebraMap R KR (r ^ m * a) := by
    rw [map_mul, map_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hr0), one_mul]
  rw [this]
  exact h3.mul h1.isAlgebraic

/-- The fraction field of a finite type `S`-algebra all of whose elements are algebraic over
`Frac S` is finite over `Frac S`: it is generated by the images of finitely many generators. -/
private theorem finiteDimensional_fractionRing_of_isAlgebraic {S R : Type*} [CommRing S]
    [IsDomain S] [CommRing R] [IsDomain R] [Algebra S R] [Algebra.FiniteType S R]
    [FaithfulSMul S R]
    (halg : letI : Algebra (FractionRing S) (FractionRing R) := FractionRing.liftAlgebra _ _
      ∀ a : R, IsAlgebraic (FractionRing S) (algebraMap R (FractionRing R) a)) :
    letI : Algebra (FractionRing S) (FractionRing R) := FractionRing.liftAlgebra _ _
    FiniteDimensional (FractionRing S) (FractionRing R) := by
  letI : Algebra (FractionRing S) (FractionRing R) := FractionRing.liftAlgebra _ _
  set K := FractionRing S
  set KR := FractionRing R
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := S) (A := R)
  set F := IntermediateField.adjoin K ((algebraMap R KR) '' (s : Set R))
  have hF : FiniteDimensional K F := by
    refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
    obtain ⟨a, -, rfl⟩ := hx
    exact (halg a).isIntegral
  have hRF : ∀ a : R, algebraMap R KR a ∈ F := by
    intro a
    have ha : a ∈ Algebra.adjoin S (s : Set R) := hs ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
    | algebraMap c =>
      rw [← IsScalarTower.algebraMap_apply S R KR, IsScalarTower.algebraMap_apply S K KR]
      exact F.algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add]; exact F.add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact F.mul_mem hx hy
  have htop : F = ⊤ := by
    rw [_root_.eq_top_iff]
    intro f _
    obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) f
    dsimp only
    rw [IsFractionRing.mk'_eq_div]
    exact F.div_mem (hRF a) (hRF b)
  rw [htop] at hF
  exact (IntermediateField.topEquiv (F := K) (E := KR)).toLinearEquiv.finiteDimensional

/-- **Galois covers of quasi-finite algebras, given the Galois field.** Let `R` be a finite type
algebra over a noetherian integrally closed domain `S`, which is a domain quasi-finite over `S` at
a prime `p`, and let `L ⊇ R` be a finite Galois extension of `Frac S`. Then the integral closure
`C` of `S` in `L` is a finite normal `S`-algebra whose primes over a common prime of `S` are
conjugate, and `R` embeds into a principal localization `C[1/r]` with `r` outside a prime `x` of
`C` lying over the same prime of `S` as `p`. -/
private theorem exists_galoisCover_of_isGalois {S R L : Type u} [CommRing S] [IsDomain S]
    [IsIntegrallyClosed S] [IsNoetherianRing S] [CommRing R] [IsDomain R] [Algebra S R]
    [Algebra.FiniteType S R] [Field L] [Algebra S L] [Algebra R L] [IsScalarTower S R L]
    [Algebra (FractionRing S) L] [IsScalarTower S (FractionRing S) L]
    [FiniteDimensional (FractionRing S) L] [IsGalois (FractionRing S) L]
    (hRL : Function.Injective (algebraMap R L)) (p : Ideal R) [p.IsPrime]
    [Algebra.QuasiFiniteAt S p] :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsDomain C) (_ : Algebra S C) (_ : IsNoetherianRing C)
      (_ : IsIntegrallyClosed C) (_ : Module.Finite S C) (_ : FaithfulSMul S C),
      (∀ P Q : Ideal C, P.IsPrime → Q.IsPrime →
        P.comap (algebraMap S C) = Q.comap (algebraMap S C) →
          ∃ σ : C ≃ₐ[S] C, Q.comap (σ : C →+* C) = P) ∧
      ∃ (r : C) (x : Ideal C), x.IsPrime ∧ r ≠ 0 ∧ r ∉ x ∧
        x.comap (algebraMap S C) = p.comap (algebraMap S R) ∧
        ∃ θ : R →+* Localization.Away r, Function.Injective θ ∧
          θ.comp (algebraMap S R) = algebraMap S (Localization.Away r) := by
  let K := FractionRing S
  let C := integralClosure S L
  obtain ⟨r, hr, x, hx, hrx, hxc, θ, hθS, hθL⟩ := exists_away_of_quasiFiniteAt (S := S) hRL p
  haveI : IsFractionRing C L := integralClosure.isFractionRing_of_finite_extension K L
  haveI : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension K
  haveI : Module.Finite S C := IsIntegralClosure.finite S K L C
  haveI : IsNoetherianRing C := IsIntegralClosure.isNoetherianRing S K L C
  have hSC : Function.Injective (algebraMap S C) := fun a b hab => by
    have : algebraMap S L a = algebraMap S L b := congrArg (fun c : C => (c : L)) hab
    rw [IsScalarTower.algebraMap_apply S K L, IsScalarTower.algebraMap_apply S K L] at this
    exact (IsFractionRing.injective S K) ((algebraMap K L).injective this)
  haveI : FaithfulSMul S C := (faithfulSMul_iff_algebraMap_injective S C).mpr hSC
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, fun P Q hP hQ hPQ => exists_algEquiv_comap_eq (K := K) (L := L)
      P Q hPQ, r, x, hx, ?_, hrx, hxc, θ, ?_, hθS⟩
  · rintro rfl
    rw [map_zero] at hr
    exact not_isUnit_zero hr
  · exact fun a b hab => hRL (by rw [← hθL a, ← hθL b, hab])

/-- **Galois covers of quasi-finite algebras.** The hypotheses of
`exists_galoisCover_of_isGalois` are met by a normal closure of `Frac R / Frac S` when `S` has
characteristic zero and `Frac R` is finite over `Frac S`. -/
private theorem exists_galoisCover {S R : Type u} [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    [IsNoetherianRing S] [CharZero S] [CommRing R] [IsDomain R] [Algebra S R]
    [Algebra.FiniteType S R] [FaithfulSMul S R] (p : Ideal R) [p.IsPrime]
    [Algebra.QuasiFiniteAt S p]
    (hfd : letI : Algebra (FractionRing S) (FractionRing R) := FractionRing.liftAlgebra _ _
      FiniteDimensional (FractionRing S) (FractionRing R)) :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsDomain C) (_ : Algebra S C) (_ : IsNoetherianRing C)
      (_ : IsIntegrallyClosed C) (_ : Module.Finite S C) (_ : FaithfulSMul S C),
      (∀ P Q : Ideal C, P.IsPrime → Q.IsPrime →
        P.comap (algebraMap S C) = Q.comap (algebraMap S C) →
          ∃ σ : C ≃ₐ[S] C, Q.comap (σ : C →+* C) = P) ∧
      ∃ (r : C) (x : Ideal C), x.IsPrime ∧ r ≠ 0 ∧ r ∉ x ∧
        x.comap (algebraMap S C) = p.comap (algebraMap S R) ∧
        ∃ θ : R →+* Localization.Away r, Function.Injective θ ∧
          θ.comp (algebraMap S R) = algebraMap S (Localization.Away r) := by
  letI : Algebra (FractionRing S) (FractionRing R) := FractionRing.liftAlgebra _ _
  haveI : CharZero (FractionRing S) := IsFractionRing.charZero S
  haveI : FiniteDimensional (FractionRing S) (FractionRing R) := hfd
  haveI : Algebra.IsSeparable (FractionRing S) (FractionRing R) := inferInstance
  haveI := IsGalois.normalClosure (FractionRing S) (FractionRing R)
    (AlgebraicClosure (FractionRing R))
  letI : Algebra R (IntermediateField.normalClosure (FractionRing S) (FractionRing R)
      (AlgebraicClosure (FractionRing R))) :=
    ((algebraMap (FractionRing R) _).comp (algebraMap R (FractionRing R))).toAlgebra
  letI : Algebra S (IntermediateField.normalClosure (FractionRing S) (FractionRing R)
      (AlgebraicClosure (FractionRing R))) :=
    ((algebraMap (FractionRing S) _).comp (algebraMap S (FractionRing S))).toAlgebra
  haveI : IsScalarTower S (FractionRing S) (IntermediateField.normalClosure (FractionRing S)
      (FractionRing R) (AlgebraicClosure (FractionRing R))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower S R (IntermediateField.normalClosure (FractionRing S) (FractionRing R)
      (AlgebraicClosure (FractionRing R))) := IsScalarTower.of_algebraMap_eq fun s => by
    change algebraMap (FractionRing S) _ (algebraMap S (FractionRing S) s) =
      algebraMap (FractionRing R) _ (algebraMap R (FractionRing R) (algebraMap S R s))
    rw [← IsScalarTower.algebraMap_apply S R (FractionRing R),
      IsScalarTower.algebraMap_apply S (FractionRing S) (FractionRing R),
      ← IsScalarTower.algebraMap_apply (FractionRing S) (FractionRing R)]
  exact exists_galoisCover_of_isGalois
    (L := IntermediateField.normalClosure (FractionRing S) (FractionRing R)
      (AlgebraicClosure (FractionRing R)))
    (fun a b hab => IsFractionRing.injective R (FractionRing R)
      ((algebraMap (FractionRing R) _).injective hab))
    p

/-- A closed point of `Spec R`, for `R` of finite type over `S`, with no proper generization in
its fibre is open in its fibre. -/
private theorem isOpen_singleton_fiber_of_forall {S R : Type*} [CommRing S] [CommRing R]
    [Algebra S R]
    [Algebra.FiniteType S R] (q : PrimeSpectrum R) (hc : IsClosed ({q} : Set (PrimeSpectrum R)))
    (hg : ∀ q' : PrimeSpectrum R, q' ⤳ q →
      q'.comap (algebraMap S R) = q.comap (algebraMap S R) → q' = q) :
    IsOpen (X := PrimeSpectrum.comap (algebraMap S R) ⁻¹' {q.comap (algebraMap S R)})
      {⟨q, rfl⟩} := by
  let p := q.comap (algebraMap S R)
  let e := PrimeSpectrum.preimageHomeomorphFiber S R p
  rw [← e.isOpen_image, Set.image_singleton]
  have : IsNoetherianRing (p.asIdeal.Fiber R) :=
    Algebra.FiniteType.isNoetherianRing p.asIdeal.ResidueField _
  have : IsJacobsonRing (p.asIdeal.Fiber R) :=
    isJacobsonRing_of_finiteType (A := p.asIdeal.ResidueField)
  have key := (PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing
    (e ⟨q, rfl⟩)).out 3 1
  refine key.mp ⟨?_, ?_⟩
  · rw [← Set.image_singleton, e.isClosed_image]
    convert hc.preimage continuous_subtype_val
    ext ⟨a, ha⟩
    simp [Subtype.ext_iff]
  · intro x y hy hx
    rw [Set.mem_singleton_iff] at hx ⊢
    subst hx
    have h1 : e.symm y ⤳ ⟨q, rfl⟩ := by
      rw [← e.symm_apply_apply ⟨q, rfl⟩]
      exact hy.map e.symm.continuous
    have : e.symm y = ⟨q, rfl⟩ :=
      Subtype.ext (hg _ (h1.map continuous_subtype_val) (e.symm y).2)
    rw [← this, e.apply_symm_apply]

/-- **Hypersurface slices through a closed point.** Let `P` be a Noetherian domain of finite type
over `S`, `m ≠ 0` a maximal ideal and `Ξ` a finite set of primes not containing `m` which contains
every prime strictly inside `m` over the same prime of `S`. By prime avoidance there is `h ∈ m`
outside every member of `Ξ` and outside `0`; a minimal prime `q ⊆ m` of `(h)` has height one, is
contained in no member of `Ξ`, and `P/q` is quasi-finite over `S` at `m/q`, as `m/q` has no proper
generization in its fibre. -/
private theorem exists_slice {S P : Type*} [CommRing S] [CommRing P] [IsDomain P]
    [IsNoetherianRing P]
    [Algebra S P] [Algebra.FiniteType S P] (m : Ideal P) [m.IsMaximal] (hm : m ≠ ⊥)
    (Ξ : Finset (Ideal P)) (hΞ : ∀ 𝔭 ∈ Ξ, 𝔭.IsPrime) (hmΞ : m ∉ Ξ)
    (hgen : ∀ 𝔭 : Ideal P, 𝔭.IsPrime → 𝔭 ≤ m →
      𝔭.comap (algebraMap S P) = m.comap (algebraMap S P) → 𝔭 ≠ m → 𝔭 ∈ Ξ) :
    ∃ (q : Ideal P) (_ : q.IsPrime) (_ : (m.map (Ideal.Quotient.mk q)).IsPrime),
      q ≤ m ∧ q.height = 1 ∧ (∀ 𝔭 ∈ Ξ, ¬ q ≤ 𝔭) ∧
      Algebra.QuasiFiniteAt S (m.map (Ideal.Quotient.mk q)) := by
  classical
  have hpr : ∀ i ∈ insert ⊥ Ξ, (id i : Ideal P).IsPrime := fun i hi => by
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact Ideal.isPrime_bot
    · exact hΞ i hi
  have hp : ∀ i ∈ insert ⊥ Ξ, i ≠ ⊥ → i ≠ ⊥ → (id i : Ideal P).IsPrime :=
    fun i hi _ _ => hpr i hi
  have key := Ideal.subset_union_prime (s := insert ⊥ Ξ) (f := id) (I := m) ⊥ ⊥ hp
  have hs := mt key.mp (by
    rintro ⟨i, hi, hmi⟩
    have : i = m := ((‹m.IsMaximal›.eq_of_le (hpr i hi).ne_top hmi)).symm
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hm this.symm
    · exact hmΞ (this ▸ hi))
  obtain ⟨h, hhm, hh⟩ := Set.not_subset.mp hs
  simp only [Set.mem_iUnion, id, not_exists, Finset.mem_insert] at hh
  have hh0 : h ≠ 0 := fun h0 => hh ⊥ (by simp) (by simp [h0])
  have hhΞ : ∀ 𝔭 ∈ Ξ, h ∉ 𝔭 := fun 𝔭 h𝔭 => hh 𝔭 (by simp [h𝔭])
  obtain ⟨q, hq, hqm⟩ := Ideal.exists_minimalPrimes_le
    (show Ideal.span {h} ≤ m from (Ideal.span_singleton_le_iff_mem _).mpr hhm)
  have hqp : q.IsPrime := hq.1.1
  have hhq : h ∈ q := hq.1.2 (Ideal.mem_span_singleton_self h)
  have hm' : (m.map (Ideal.Quotient.mk q)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  refine ⟨q, hqp, hm'.isPrime, hqm, ?_, fun 𝔭 h𝔭 hq𝔭 => hhΞ 𝔭 h𝔭 (hq𝔭 hhq), ?_⟩
  · refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ q hq) ?_
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    rintro rfl
    exact hh0 hhq
  · let x : PrimeSpectrum (P ⧸ q) := ⟨m.map (Ideal.Quotient.mk q), hm'.isPrime⟩
    refine Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber x
      (isOpen_singleton_fiber_of_forall x
        ((PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mpr hm') fun y hy hyc => ?_)
    have hyx : y.asIdeal ≤ x.asIdeal := (PrimeSpectrum.le_iff_specializes y x).mpr hy
    set 𝔭 := y.asIdeal.comap (Ideal.Quotient.mk q)
    have hcm : x.asIdeal.comap (Ideal.Quotient.mk q) = m := by
      change (m.map (Ideal.Quotient.mk q)).comap (Ideal.Quotient.mk q) = m
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker, sup_eq_left.mpr hqm]
    have h𝔭m : 𝔭 ≤ m := hcm ▸ Ideal.comap_mono hyx
    have h𝔭c : 𝔭.comap (algebraMap S P) = m.comap (algebraMap S P) := by
      have := congrArg PrimeSpectrum.asIdeal hyc
      simp only [PrimeSpectrum.comap_asIdeal] at this
      rw [IsScalarTower.algebraMap_eq S P (P ⧸ q), ← Ideal.comap_comap, ← Ideal.comap_comap,
        Ideal.Quotient.algebraMap_eq] at this
      rw [this, hcm]
    have hq𝔭 : q ≤ 𝔭 := fun a ha => by
      change Ideal.Quotient.mk q a ∈ y.asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      exact y.asIdeal.zero_mem
    by_cases he : 𝔭 = m
    · apply PrimeSpectrum.ext
      change y.asIdeal = m.map (Ideal.Quotient.mk q)
      rw [← he, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    · exact absurd (hq𝔭 hhq) (hhΞ 𝔭 (hgen 𝔭 inferInstance h𝔭m h𝔭c he))

/-- **Zariski's main theorem and residue fields.** If `P ⧸ q` is quasi-finite over `S` at some
prime, the residue field of `q` is algebraic over that of the prime of `S` under `q`: some
`r ≠ 0` and all `r^m a` are integral over `S`. -/
private theorem isAlgebraic_residueField_of_quasiFiniteAt {S P : Type*} [CommRing S] [CommRing P]
    [Algebra S P] [Algebra.FiniteType S P] (𝔮 : Ideal S) [𝔮.IsPrime] (q : Ideal P) [q.IsPrime]
    [q.LiesOver 𝔮] (p : Ideal (P ⧸ q)) [p.IsPrime] [Algebra.QuasiFiniteAt S p] :
    letI : Algebra 𝔮.ResidueField q.ResidueField :=
      (Ideal.ResidueField.map _ _ (algebraMap S P) Ideal.LiesOver.over).toAlgebra
    Algebra.IsAlgebraic 𝔮.ResidueField q.ResidueField := by
  letI : Algebra 𝔮.ResidueField q.ResidueField :=
    (Ideal.ResidueField.map _ _ (algebraMap S P) Ideal.LiesOver.over).toAlgebra
  obtain ⟨r, hrp, hr, hint⟩ := (Algebra.zariskisMainProperty_iff (R := S)).mp
    (Algebra.ZariskisMainProperty.of_finiteType (R := S) p)
  set ι := algebraMap (P ⧸ q) q.ResidueField
  have hsq : (algebraMap 𝔮.ResidueField q.ResidueField).comp (algebraMap S 𝔮.ResidueField) =
      ι.comp (algebraMap S (P ⧸ q)) := by
    ext s
    change Ideal.ResidueField.map _ _ (algebraMap S P) Ideal.LiesOver.over
      (algebraMap S 𝔮.ResidueField s) = _
    rw [Ideal.ResidueField.map_algebraMap, RingHom.comp_apply,
      IsScalarTower.algebraMap_apply S P (P ⧸ q),
      ← IsScalarTower.algebraMap_apply P (P ⧸ q) q.ResidueField]
  have hint' : ∀ b : P ⧸ q, IsIntegral S b → IsIntegral 𝔮.ResidueField (ι b) :=
    fun b hb => IsIntegral.map_of_comp_eq _ ι hsq hb
  have hr0 : ι r ≠ 0 := fun h0 => hrp <|
    (IsFractionRing.injective (P ⧸ q) q.ResidueField (h0.trans (map_zero _).symm)) ▸ p.zero_mem
  have halg : ∀ a : P ⧸ q, IsAlgebraic 𝔮.ResidueField (ι a) := by
    intro a
    obtain ⟨m, hm⟩ := hint a
    rw [show ι a = (ι r ^ m)⁻¹ * ι (r ^ m * a) by
      rw [map_mul, map_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hr0), one_mul]]
    exact ((hint' r hr).isAlgebraic.pow m).inv.mul (hint' _ hm).isAlgebraic
  refine ⟨fun f => ?_⟩
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := P ⧸ q) f
  rw [div_eq_mul_inv]
  exact (halg a).mul (halg b).inv

/-- **Going-down for an integral extension of an integrally closed domain.** The height of a
prime of `C` equals the height of the prime of `S` under it. -/
private theorem height_under_eq {S C : Type*} [CommRing S] [CommRing C] [IsDomain S] [IsDomain C]
    [IsIntegrallyClosed S] [IsNoetherianRing S] [IsNoetherianRing C] [Algebra S C]
    [Algebra.IsIntegral S C]
    [FaithfulSMul S C] (P : Ideal C) [P.IsPrime] : (P.under S).height = P.height := by
  have : P.LiesOver (P.under S) := ⟨rfl⟩
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (P.under S) P]
  suffices h : (P.map (Ideal.Quotient.mk ((P.under S).map (algebraMap S C)))).height = 0 by
    rw [h, add_zero]
  have hmin := Ideal.IsIntegral.mem_minimalPrimes_map_under (R := S) P
  generalize (P.under S).map (algebraMap S C) = I at hmin ⊢
  rw [Ideal.minimalPrimes_eq_comap] at hmin
  obtain ⟨Q, hQ, hQP⟩ := hmin
  have e : P.map (Ideal.Quotient.mk I) = Q := by
    rw [← hQP, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  rw [e]
  haveI := hQ.1.1
  exact Ideal.height_eq_zero_iff.mpr hQ

/-- The coheight of a point of `Spec C` equals that of its image in `Spec S`, for `C` integral
over the integrally closed domain `S`. -/
private theorem coheight_SpecMap_eq {S C : Type u} [CommRing S] [CommRing C] [IsDomain S]
    [IsDomain C]
    [IsIntegrallyClosed S] [IsNoetherianRing S] [IsNoetherianRing C] [Algebra S C]
    [Algebra.IsIntegral S C]
    [FaithfulSMul S C] (x : Spec (.of C)) :
    Order.coheight (Spec.map (CommRingCat.ofHom (algebraMap S C)) x) = Order.coheight x := by
  rw [← idealHeight_eq_coheight, ← idealHeight_eq_coheight]
  haveI : x.asIdeal.IsPrime := x.isPrime
  exact height_under_eq (S := S) (C := C) x.asIdeal

/-! ### Descent of local equations along finite morphisms -/

section Descent

variable {Z T : Scheme.{u}} (π : T ⟶ Z)
    [IsIntegral Z] [IsIntegral T] [IsLocallyNoetherian Z] [IsLocallyNoetherian T]
    [IsNormal Z] [IsNormal T] [IsFinite π] [Surjective π]

/-- Incomparability: a specialization inside a fibre of a locally quasi-finite morphism is
trivial, the fibres being discrete. -/
private lemma eq_of_specializes_of_map_eq {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
    {x x' : X} (h : x ⤳ x') (he : f x = f x') : x = x' := by
  have : DiscreteTopology (f.fiber (f x')) := IsLocallyArtinian.discreteTopology
  have : DiscreteTopology (f ⁻¹' {f x'}) := (f.fiberHomeo (f x')).discreteTopology
  let a : ↥(f ⁻¹' {f x'}) := ⟨x, he⟩
  let b : ↥(f ⁻¹' {f x'}) := ⟨x', rfl⟩
  have hab : a ⤳ b := Topology.IsInducing.subtypeVal.specializes_iff.mp h
  have hb : a ∈ ({b} : Set _) := hab.mem_open (isOpen_discrete _) rfl
  exact congrArg Subtype.val hb

/-- A finite morphism is strictly monotone for the specialization order. -/
private lemma strictMono_of_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] :
    StrictMono f := fun x y hxy =>
  have hyx : y ⤳ x := hxy.le
  lt_of_le_not_ge (hyx.map f.continuous) fun hle => hxy.not_ge <| by
    have hxy' : f x ⤳ f y := hle
    have he : f y = f x := ((hyx.map f.continuous).antisymm hxy').eq
    rw [eq_of_specializes_of_map_eq f hyx he]

omit [IsLocallyNoetherian Z] [IsLocallyNoetherian T] [IsNormal Z] [IsNormal T] in
/-- A point of `T` above a codimension-one point of `Z` has codimension one: by incomparability
its coheight is at most that of its image, and it is not the generic point, whose image is the
generic point of `Z`. -/
private lemma coheight_eq_one_of_coheight_map_eq_one (x : T) (hx : Order.coheight (π x) = 1) :
    Order.coheight x = 1 := by
  refine le_antisymm (hx ▸ Order.coheight_le_coheight_apply_of_strictMono _
    (strictMono_of_isFinite π) x) ?_
  have hne : x ≠ genericPoint T := by
    rintro rfl
    rw [map_genericPoint_of_isDominant π, coheight_genericPoint_eq_zero] at hx
    exact zero_ne_one hx
  have hlt : x < genericPoint T := lt_of_le_not_ge (genericPoint_specializes x) fun h =>
    hne ((show x ⤳ genericPoint T from h).antisymm (genericPoint_specializes x)).eq
  simpa [coheight_genericPoint_eq_zero] using Order.coheight_add_one_le hlt

omit [IsLocallyNoetherian Z] [IsLocallyNoetherian T] [IsNormal Z] [IsNormal T] in
/-- A finite dominant morphism of integral schemes induces a finite extension of function
fields. -/
private lemma finite_functionField :
    letI := (functionFieldMap π).toAlgebra
    Module.Finite Z.functionField T.functionField := by
  classical
  let := (functionFieldMap π).toAlgebra
  have hdom : functionFieldMap π = dominantFunctionFieldMap π :=
    (congrArg CommRingCat.Hom.hom (Stacks.Chow.stalkMap_cast_target π (genericPoint T)
      (map_genericPoint_of_isDominant π))).symm
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint Z)) isOpen_univ
  have : Nonempty U := ⟨⟨_, hηU⟩⟩
  have hηT : genericPoint T ∈ π ⁻¹ᵁ U := by
    change π (genericPoint T) ∈ U
    rw [map_genericPoint_of_isDominant π]; exact hηU
  have : Nonempty (π ⁻¹ᵁ U) := ⟨⟨_, hηT⟩⟩
  let A := Γ(Z, U)
  let B := Γ(T, π ⁻¹ᵁ U)
  have : IsDomain A := IsIntegral.component_integral U
  have : IsDomain B := IsIntegral.component_integral (π ⁻¹ᵁ U)
  let : Algebra A B := (π.app U).hom.toAlgebra
  have : Module.Finite A B := π.finite_app U hU
  have hcompat : ∀ a : A, functionFieldMap π (Z.germToFunctionField U a) =
      T.germToFunctionField (π ⁻¹ᵁ U) (π.app U a) := by
    intro a
    have hc := RingHom.congr_fun
      (Stacks.Chow.appLE_germToFunctionField_commutes π U (π ⁻¹ᵁ U) le_rfl) a
    rw [RingHom.comp_apply, RingHom.comp_apply] at hc
    rw [hdom, ← hc, Scheme.Hom.app_eq_appLE]
  have hmap : Function.Injective (π.app U).hom := fun a b hab =>
    Z.germToFunctionField_injective U <| (functionFieldMap π).injective <| by
      rw [hcompat a, hcompat b, hab]
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2 hmap
  let : Algebra A T.functionField :=
    ((functionFieldMap π).comp (Z.germToFunctionField U).hom).toAlgebra
  have : IsScalarTower A Z.functionField T.functionField := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A B T.functionField :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext hcompat)
  have : IsFractionRing A Z.functionField := functionField_isFractionRing_of_isAffineOpen Z U hU
  have : IsFractionRing B T.functionField :=
    functionField_isFractionRing_of_isAffineOpen T (π ⁻¹ᵁ U) (hU.preimage π)
  apply Module.rank_lt_aleph0_iff.mp
  rw [Algebra.IsAlgebraic.rank_of_isFractionRing A Z.functionField B T.functionField]
  exact Module.rank_lt_aleph0 A B

/-- In a Noetherian domain of dimension at most one, a nonzero nonunit has positive order. -/
private lemma ofAdd_one_le_ordFrac {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {x : R}
    (hx0 : x ≠ 0) (hx : ¬ IsUnit x) :
    ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤
      Ring.ordFrac R (algebraMap R K x) := by
  have hnz : x ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hx0
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ring.ord_ne_top hnz)
  have : Nontrivial (R ⧸ Ideal.span {x}) :=
    Ideal.Quotient.nontrivial_iff.mpr (by rwa [ne_eq, Ideal.span_singleton_eq_top])
  have hpos : 0 < Ring.ord R x := Module.length_pos
  rw [Ring.ordFrac_eq_ord R hx0, Ring.ordMonoidWithZeroHom_eq_coe R hnz hn.symm]
  have : 1 ≤ n := by
    rw [← hn] at hpos; exact_mod_cast hpos
  exact_mod_cast (Multiplicative.ofAdd_le.mpr (by exact_mod_cast this))

/-- A nonzero section vanishing at a point `η` of codimension one has positive order at `η`. -/
private lemma one_le_ord_of_notMem_basicOpen {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] {V : X.Opens} [Nonempty V] (s : Γ(X, V)) {η : X} (hηV : η ∈ V)
    (hη : Order.coheight η = 1) (hs : η ∉ X.basicOpen s) (hs0 : s ≠ 0) :
    1 ≤ X.ord (X.germToFunctionField V s) η := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk η) := krullDimLE_of_coheight_le hη.le
  have hg0 : X.presheaf.germ V η hηV s ≠ 0 := fun h =>
    hs0 (germ_injective_of_isIntegral X η hηV (by rw [h, map_zero]))
  have hf : X.germToFunctionField V s ≠ 0 := by
    rw [← Scheme.algebraMap_germ_eq_germToFunctionField _ hηV]
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hg0
  rw [Scheme.le_ord_iff hη hf, ← Scheme.algebraMap_germ_eq_germToFunctionField _ hηV]
  exact ofAdd_one_le_ordFrac hg0 (by rwa [Scheme.mem_basicOpen X s η hηV] at hs)

/-- A section has nonnegative order at every point of its domain. -/
private lemma ord_germToFunctionField_nonneg {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] {V : X.Opens} [Nonempty V] (s : Γ(X, V)) (hs0 : s ≠ 0) {η : X}
    (hηV : η ∈ V) : 0 ≤ X.ord (X.germToFunctionField V s) η := by
  have h := Scheme.ord_le_smul hηV hs0 (1 : X.functionField)
  rwa [Scheme.ord_one, Algebra.smul_def, mul_one] at h

/-- **Algebraic Hartogs at a point.** On a normal integral locally Noetherian scheme, a rational
function `g ≠ 0` with `v_Γ(g) ≥ 0` for every prime divisor `Γ` through `x` lies in `𝒪_{X,x}`. -/
private lemma exists_algebraMap_stalk_eq_of_forall_ord_nonneg {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (x : X) {g : X.functionField} (hg : g ≠ 0)
    (h : ∀ Γ : MMP.Mori.PrimeDivisor X, x ∈ Γ.support → 0 ≤ X.ord g Γ.genericPoint) :
    ∃ r : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField r = g := by
  have : IsIntegrallyClosed (X.presheaf.stalk x) := IsNormal.stalk_normal x
  refine Stacks.AlgebraicGeometry.UnitsNormalProper.exists_algebraMap_eq_of_forall_height_eq_one
    X.functionField fun q hq => ?_
  have hξ1 : Order.coheight (X.fromSpecStalk x q) = 1 :=
    (Stacks.Chow.coheight_fromSpecStalk_eq_height x q).trans hq
  set E : MMP.Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hξ1 with hEdef
  have hEξ : E.genericPoint = X.fromSpecStalk x q :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hξ1
  have hspec : E.genericPoint ⤳ x := hEξ ▸ Stacks.Chow.specializes_fromSpecStalk x q
  have hxE : x ∈ E.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact specializes_iff_mem_closure.mp hspec
  have hv : E.divisorialValuation g ≤ 1 := by
    rw [E.divisorialValuation_eq_exp_neg_ord hg, ← WithZero.exp_zero, WithZero.exp_le_exp]
    linarith [h E hxE]
  obtain ⟨b, hb⟩ := (E.divisorialValuation_le_one_iff g).mp hv
  let := (X.presheaf.stalkSpecializes hspec).hom.toAlgebra
  have hloc := Stacks.Chow.isLocalization_stalk_of_specializes hspec q hEξ.symm
  obtain ⟨⟨a, s⟩, hab⟩ := IsLocalization.mk'_surjective q.asIdeal.primeCompl b
  change IsLocalization.mk' E.localRing a s = b at hab
  refine ⟨a, s, s.2, ?_⟩
  have hspec' := IsLocalization.mk'_spec E.localRing a s
  rw [hab] at hspec'
  have h2 := congrArg (algebraMap E.localRing X.functionField) hspec'
  rw [map_mul, hb] at h2
  change g * algebraMap E.localRing X.functionField ((X.presheaf.stalkSpecializes hspec).hom s) =
    algebraMap E.localRing X.functionField ((X.presheaf.stalkSpecializes hspec).hom a) at h2
  rwa [MMP.Mori.algebraMap_stalkSpecializes, MMP.Mori.algebraMap_stalkSpecializes] at h2

/-- A unit of the stalk at `y` has order zero at every point of some open neighbourhood of `y`. -/
private lemma exists_open_ord_algebraMap_eq_zero {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] {y : X} {u : X.presheaf.stalk y} (hu : IsUnit u) :
    ∃ W : X.Opens, y ∈ W ∧ ∀ η ∈ W,
      X.ord (algebraMap (X.presheaf.stalk y) X.functionField u) η = 0 := by
  obtain ⟨V, hyV, s, rfl⟩ := X.presheaf.exists_germ_eq u
  have hyb : y ∈ X.basicOpen s := (Scheme.mem_basicOpen X s y hyV).mpr hu
  have : Nonempty (X.basicOpen s) := ⟨⟨y, hyb⟩⟩
  have : Nonempty V := ⟨⟨y, hyV⟩⟩
  refine ⟨X.basicOpen s, hyb, fun η hη => ?_⟩
  have : Nonempty (X.toRingedSpace.basicOpen s) := ⟨⟨y, hyb⟩⟩
  have h := Scheme.ord_of_isUnit (X.toRingedSpace.isUnit_res_basicOpen s) hη
  rw [Scheme.algebraMap_germ_eq_germToFunctionField]
  convert h using 2
  simp only [Scheme.germToFunctionField]
  rw [← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (X.basicOpen_le s))]
  rfl

private lemma scheme_ord_div {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (η : X)
    {f g : X.functionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    X.ord (f / g) η = X.ord f η - X.ord g η := by
  have h := Scheme.ord_mul (x := η) (div_ne_zero hf hg) hg
  rw [div_mul_cancel₀ f hg] at h
  omega

/-- **Semilocal generator.** Let `S` be a finite set of pairwise incomparable points in an affine
open `V₀` of a normal integral locally Noetherian scheme, at each of which the divisor `D` has a
local equation. Then `D` has a single local equation on an open neighbourhood of `S`: choose
local equations `φ_x`, clear their poles against each other by sections `s_x` invertible at `x`,
and combine them with sections `a_x` invertible at `x` and vanishing at the other points; the
combination `g = ∑ a_x s_x^N φ_x` has `g / φ_y` a unit of `𝒪_{X,y}` for every `y ∈ S`, by
algebraic Hartogs. -/
private lemma exists_isLocalEquation_finset {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (D : Divisor X) (S : Finset X) (hS : S.Nonempty)
    (V0 : X.Opens) (hV0 : IsAffineOpen V0) (hSV0 : ∀ x ∈ S, x ∈ V0)
    (hinc : ∀ x ∈ S, ∀ y ∈ S, x ⤳ y → x = y)
    (hD : ∀ x ∈ S, ∃ U : X.Opens, x ∈ U ∧ ∃ φ : (RationalFunctions X)ˣ, D.IsLocalEquation U φ) :
    ∃ W : X.Opens, (∀ x ∈ S, x ∈ W) ∧ ∃ g : (RationalFunctions X)ˣ, D.IsLocalEquation W g := by
  classical
  obtain ⟨x₀, hx₀⟩ := hS
  have : Nonempty V0 := ⟨⟨x₀, hSV0 x₀ hx₀⟩⟩
  choose! V hxV φ hφ using hD
  set eX := rationalFunctionsEquivFunctionField X
  have hspecmem : ∀ (E : MMP.Mori.PrimeDivisor X) (W : X.Opens) (y : X), y ∈ E.support → y ∈ W →
      E.genericPoint ∈ W := fun E W y hyE hyW => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hyE
    exact (specializes_iff_mem_closure.mpr hyE).mem_open W.isOpen hyW
  obtain ⟨F, hF0, hF⟩ : ∃ F : X → X.functionField, (∀ x, F x ≠ 0) ∧
      ∀ x ∈ S, ∀ E : MMP.Mori.PrimeDivisor X, E.genericPoint ∈ V x →
        D.coeff E = X.ord (F x) E.genericPoint :=
    ⟨fun x => eX (φ x : RationalFunctions X), fun x =>
      (Units.map (eX : RationalFunctions X →* X.functionField) (φ x)).ne_zero,
      fun x hx E hE => by
        rw [hφ x hx E ((E.genericPoint_mem_iff _).mp hE), ord_eq_ord_genericPoint]⟩
  -- the finitely many points of codimension one of `V₀` where some `F x / F y` has a zero or pole
  have hQfin : (⋃ p ∈ S ×ˢ S, {η : X | η ∈ V0 ∧ X.ord (F p.1 / F p.2) η ≠ 0}).Finite :=
    Set.Finite.biUnion (S ×ˢ S).finite_toSet fun p _ =>
      (Stacks.Chow.locallyFiniteSupport_ord X _).finite_inter_support_of_isCompact hV0.isCompact
  obtain ⟨Qf, hQf⟩ : ∃ Qf : Finset X, ∀ η, η ∈ V0 → ∀ x ∈ S, ∀ y ∈ S,
      X.ord (F x / F y) η ≠ 0 → η ∈ Qf :=
    ⟨hQfin.toFinset, fun η hη x hx y hy hne => hQfin.mem_toFinset.mpr
      (Set.mem_biUnion (x := (x, y)) (Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨hx, hy⟩))
        ⟨hη, hne⟩)⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ η ∈ Qf, ∀ x ∈ S, ∀ y ∈ S, (X.ord (F x / F y) η).natAbs ≤ N :=
    ⟨∑ η ∈ Qf, ∑ p ∈ S ×ˢ S, (X.ord (F p.1 / F p.2) η).natAbs, fun η hη x hx y hy =>
      (Finset.single_le_sum (f := fun p : X × X => (X.ord (F p.1 / F p.2) η).natAbs)
        (fun _ _ => Nat.zero_le _) (a := (x, y)) (Finset.mem_product.mpr ⟨hx, hy⟩)).trans
      (Finset.single_le_sum (f := fun η => ∑ p ∈ S ×ˢ S, (X.ord (F p.1 / F p.2) η).natAbs)
        (fun _ _ => Nat.zero_le _) hη)⟩
  -- sections separating the points of `S`
  have ha : ∀ x ∈ S, ∃ a : Γ(X, V0), (∀ y ∈ S.erase x, y ∉ X.basicOpen a) ∧
      x ∈ X.basicOpen a := by
    intro x hx
    let O : X.Opens := V0 ⊓ ⟨⋂ y ∈ S.erase x, (closure {y})ᶜ,
      isOpen_biInter_finset fun y _ => isClosed_closure.isOpen_compl⟩
    have hxO : x ∈ O := ⟨hSV0 x hx, Set.mem_iInter₂.mpr fun y hy hxy =>
      (Finset.mem_erase.mp hy).1
        (hinc y (Finset.mem_of_mem_erase hy) x hx (specializes_iff_mem_closure.mpr hxy))⟩
    obtain ⟨f, hfO, hxf⟩ := hV0.exists_basicOpen_le (V := O) ⟨x, hxO⟩ (hSV0 x hx)
    refine ⟨f, fun y hy hyf => ?_, hxf⟩
    have h : y ∈ ⋂ y' ∈ S.erase x, (closure {y'})ᶜ := (hfO hyf).2
    rw [Set.mem_iInter₂] at h
    exact h y hy (subset_closure rfl)
  -- sections clearing the poles of the `F x / F y` not passing through `x`
  have hs : ∀ x ∈ S, ∃ s : Γ(X, V0), (∀ η ∈ Qf, ¬ η ⤳ x → η ∉ X.basicOpen s) ∧
      x ∈ X.basicOpen s := by
    intro x hx
    let O : X.Opens := V0 ⊓ ⟨⋂ η ∈ Qf.filter (fun η => ¬ η ⤳ x), (closure {η})ᶜ,
      isOpen_biInter_finset fun y _ => isClosed_closure.isOpen_compl⟩
    have hxO : x ∈ O := ⟨hSV0 x hx, Set.mem_iInter₂.mpr fun η hη hxη =>
      (Finset.mem_filter.mp hη).2 (specializes_iff_mem_closure.mpr hxη)⟩
    obtain ⟨f, hfO, hxf⟩ := hV0.exists_basicOpen_le (V := O) ⟨x, hxO⟩ (hSV0 x hx)
    refine ⟨f, fun η hη hηx hηf => ?_, hxf⟩
    have h : η ∈ ⋂ η' ∈ Qf.filter (fun η => ¬ η ⤳ x), (closure {η'})ᶜ := (hfO hηf).2
    rw [Set.mem_iInter₂] at h
    exact h η (Finset.mem_filter.mpr ⟨hη, hηx⟩) (subset_closure rfl)
  choose! a haV hxa using ha
  choose! s hsV hxs using hs
  have hne0 : ∀ (t : Γ(X, V0)) (x : X), x ∈ X.basicOpen t → t ≠ 0 := by
    rintro t x hx rfl
    rw [Scheme.basicOpen_zero] at hx
    exact hx
  set A : X → X.functionField := fun x => X.germToFunctionField V0 (a x)
  set Sx : X → X.functionField := fun x => X.germToFunctionField V0 (s x)
  have hSx0 : ∀ x ∈ S, Sx x ≠ 0 := fun x hx => by
    simp only [Sx, ne_eq, map_eq_zero_iff _ (X.germToFunctionField_injective V0)]
    exact hne0 _ x (hxs x hx)
  -- the quotients `s_x^N F_x / F_y` are regular at `y`
  have hreg : ∀ x ∈ S, ∀ y ∈ S, ∃ r : X.presheaf.stalk y,
      algebraMap (X.presheaf.stalk y) X.functionField r = Sx x ^ N * F x / F y := by
    intro x hx y hy
    refine exists_algebraMap_stalk_eq_of_forall_ord_nonneg y
      (div_ne_zero (mul_ne_zero (pow_ne_zero _ (hSx0 x hx)) (hF0 x)) (hF0 y)) fun E hyE => ?_
    have hηV0 : E.genericPoint ∈ V0 := hspecmem E V0 y hyE (hSV0 y hy)
    have hη1 : Order.coheight E.genericPoint = 1 := E.coheight_genericPoint
    rw [mul_div_assoc, Scheme.ord_mul (pow_ne_zero _ (hSx0 x hx)) (div_ne_zero (hF0 x) (hF0 y)),
      Scheme.ord_pow (hSx0 x hx) _ _]
    have hnn : 0 ≤ X.ord (Sx x) E.genericPoint :=
      ord_germToFunctionField_nonneg _ (hne0 _ x (hxs x hx)) hηV0
    by_cases hQη : E.genericPoint ∈ Qf
    · by_cases hηx : E.genericPoint ⤳ x
      · have h0 : X.ord (F x / F y) E.genericPoint = 0 := by
          rw [scheme_ord_div _ (hF0 x) (hF0 y), ← hF x hx E (hηx.mem_open (V x).isOpen (hxV x hx)),
            ← hF y hy E (hspecmem E (V y) y hyE (hxV y hy)), sub_self]
        rw [h0]; positivity
      · have hnot : E.genericPoint ∉ X.basicOpen (s x) := hsV x hx _ hQη hηx
        have h1 := one_le_ord_of_notMem_basicOpen (s x) hηV0 hη1 hnot (hne0 _ x (hxs x hx))
        have hle := hN _ hQη x hx y hy
        have hle' : -(X.ord (F x / F y) E.genericPoint) ≤ N := by omega
        have hNo : (N : ℤ) ≤ N * X.ord (Sx x) E.genericPoint :=
          le_mul_of_one_le_right (Nat.cast_nonneg N) h1
        linarith
    · have h0 : X.ord (F x / F y) E.genericPoint = 0 := by
        by_contra hne
        exact hQη (hQf _ hηV0 x hx y hy hne)
      rw [h0]; positivity
  choose! r hr using hreg
  set G : X.functionField := ∑ x ∈ S, A x * (Sx x ^ N * F x) with hG
  -- `G / F y` is a unit of `𝒪_{X,y}`
  have hunit : ∀ y ∈ S, ∃ u : X.presheaf.stalk y, IsUnit u ∧
      G = F y * algebraMap (X.presheaf.stalk y) X.functionField u := by
    intro y hy
    have hyV0 := hSV0 y hy
    refine ⟨∑ x ∈ S, X.presheaf.germ V0 y hyV0 (a x) * r x y, ?_, ?_⟩
    · have hyy : r y y = X.presheaf.germ V0 y hyV0 (s y) ^ N := by
        apply IsFractionRing.injective (X.presheaf.stalk y) X.functionField
        rw [hr y hy y hy, map_pow, Scheme.algebraMap_germ_eq_germToFunctionField,
          mul_div_assoc, div_self (hF0 y), mul_one]
      rw [← Finset.add_sum_erase _ _ hy, hyy]
      have hu : IsUnit (X.presheaf.germ V0 y hyV0 (a y) * X.presheaf.germ V0 y hyV0 (s y) ^ N) :=
        ((Scheme.mem_basicOpen X _ y hyV0).mp (hxa y hy)).mul
          (((Scheme.mem_basicOpen X _ y hyV0).mp (hxs y hy)).pow N)
      have hm : ∑ x ∈ S.erase y, X.presheaf.germ V0 y hyV0 (a x) * r x y ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
        refine Ideal.sum_mem _ fun x hx => Ideal.mul_mem_right _ _ ?_
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← Scheme.mem_basicOpen X _ y hyV0]
        exact haV x (Finset.mem_of_mem_erase hx) y
          (Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hx).1 h.symm, hy⟩)
      by_contra hnu
      have hmem := Ideal.sub_mem _ ((IsLocalRing.mem_maximalIdeal _).mpr hnu) hm
      rw [add_sub_cancel_right] at hmem
      exact (IsLocalRing.mem_maximalIdeal _).mp hmem hu
    · rw [map_sum, Finset.mul_sum, hG]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [map_mul, hr x hx y hy, Scheme.algebraMap_germ_eq_germToFunctionField]
      field_simp [hF0 y]
      simp only [A]
      ring
  have hG0 : G ≠ 0 := by
    obtain ⟨u, hu, hGu⟩ := hunit x₀ hx₀
    rw [hGu]
    exact mul_ne_zero (hF0 x₀) ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hu.ne_zero)
  choose! u hu hGu using hunit
  choose! W hyW hW using fun y (hy : y ∈ S) => exists_open_ord_algebraMap_eq_zero (hu y hy)
  refine ⟨⨆ y ∈ S, W y ⊓ V y, fun y hy => ?_, (Units.mk0 G hG0).map
    (eX.symm : X.functionField →* RationalFunctions X), fun E hE => ?_⟩
  · simp only [TopologicalSpace.Opens.mem_iSup]
    exact ⟨y, hy, hyW y hy, hxV y hy⟩
  · have hη := (E.genericPoint_mem_iff _).mpr hE
    simp only [TopologicalSpace.Opens.mem_iSup] at hη
    obtain ⟨y, hy, hηW, hηV⟩ := hη
    rw [hF y hy E hηV, ord_eq_ord_genericPoint]
    have : rationalFunctionsEquivFunctionField X
        (((Units.mk0 G hG0).map (eX.symm : X.functionField →* RationalFunctions X) :
          (RationalFunctions X)ˣ) : RationalFunctions X) = G := by
      simp [eX]
    rw [this, hGu y hy, Scheme.ord_mul (hF0 y)
      ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (hu y hy).ne_zero),
      hW y hy _ hηW, add_zero]

/-- A divisor on `T` which has a local equation near every point of the fibre over `z` has a
single local equation on `π⁻¹ U` for a neighbourhood `U` of `z`. -/
private lemma exists_isLocalEquation_preimage_of_forall {D' : Divisor T} (z : Z)
    (hD' : ∀ x : T, π x = z → ∃ U : T.Opens, x ∈ U ∧ ∃ φ : (RationalFunctions T)ˣ,
      D'.IsLocalEquation U φ) :
    ∃ U : Z.Opens, z ∈ U ∧ ∃ g : (RationalFunctions T)ˣ, D'.IsLocalEquation (π ⁻¹ᵁ U) g := by
  obtain ⟨_, ⟨U0, hU0, rfl⟩, hzU0, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  have hfin : (π.base ⁻¹' {z}).Finite := π.finite_preimage_singleton z
  obtain ⟨x₀, hx₀⟩ := π.surjective z
  obtain ⟨W, hSW, g, hg⟩ := exists_isLocalEquation_finset D' hfin.toFinset
    ⟨x₀, hfin.mem_toFinset.mpr hx₀⟩ (π ⁻¹ᵁ U0) (hU0.preimage π)
    (fun x hx => by
      have : π x = z := by simpa using hx
      change π x ∈ U0
      rw [this]; exact hzU0)
    (fun x hx y hy hxy => eq_of_specializes_of_map_eq π hxy (by
      have h1 : π x = z := by simpa using hx
      have h2 : π y = z := by simpa using hy
      rw [h1, h2]))
    (fun x hx => hD' x (by simpa using hx))
  have hcl : IsClosed (π '' ((W : Set T)ᶜ)) := π.isClosedMap _ W.isOpen.isClosed_compl
  refine ⟨⟨(π '' ((W : Set T)ᶜ))ᶜ, hcl.isOpen_compl⟩, ?_, g, hg.mono ?_⟩
  · rintro ⟨w, hw, hwz⟩
    exact hw (hSW w (hfin.mem_toFinset.mpr hwz))
  · intro t ht
    by_contra htW
    exact ht ⟨t, htW, rfl⟩

/-- The norm of a local equation of `π^*B` on `π⁻¹ U` is a local equation of `n B` on `U`,
where `n = [K(T) : K(Z)]`. At a prime divisor `E` of `Z` meeting `U`, Stacks 02RT
(`Stacks.Chow.finsum_ord_mul_residueDegree_of_isFinite`) gives
`ord_E N(g) = ∑ fᵢ ord_{Eᵢ}(g)` over the prime divisors `Eᵢ` above `E`; applied to a uniformizer
`t` at `E` it gives `∑ eᵢ fᵢ = ord_E (t ^ n) = n`. -/
private lemma exists_isLocalEquation_norm (B : QDivisor Z) (B' : QDivisor T)
    (hB' : ∀ (E : MMP.Mori.PrimeDivisor Z) (E' : MMP.Mori.PrimeDivisor T),
      π E'.genericPoint = E.genericPoint → ∀ t : Z.functionField, Z.ord t E.genericPoint = 1 →
        B' E' = (T.ord (AlgebraicGeometry.functionFieldMap π t) E'.genericPoint : ℚ) * B E) :
    ∃ n : ℕ, 0 < n ∧ ∀ (U : Z.Opens) (g : (RationalFunctions T)ˣ),
      (∀ E' : MMP.Mori.PrimeDivisor T, (E'.support ∩ π ⁻¹ᵁ U).Nonempty →
        B' E' = (E'.ord g : ℚ)) →
        ∃ φ : (RationalFunctions Z)ˣ, ∀ E : MMP.Mori.PrimeDivisor Z,
          (E.support ∩ U).Nonempty → (n : ℚ) * B E = (E.ord φ : ℚ) := by
  let : Algebra Z.functionField T.functionField :=
    (AlgebraicGeometry.functionFieldMap π).toAlgebra
  have : Module.Finite Z.functionField T.functionField := finite_functionField π
  have halg : algebraMap Z.functionField T.functionField = dominantFunctionFieldMap π :=
    (congrArg CommRingCat.Hom.hom (Stacks.Chow.stalkMap_cast_target π (genericPoint T)
      (map_genericPoint_of_isDominant π))).symm
  refine ⟨Module.finrank Z.functionField T.functionField, Module.finrank_pos, ?_⟩
  intro U g hg
  set eT := rationalFunctionsEquivFunctionField T
  set eZ := rationalFunctionsEquivFunctionField Z
  have hg0 : eT g ≠ 0 := (Units.map (eT : RationalFunctions T →* T.functionField) g).ne_zero
  have hN0 : Algebra.norm Z.functionField (eT g) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hg0
  refine ⟨(Units.mk0 _ hN0).map (eZ.symm : Z.functionField →* RationalFunctions Z),
    fun E hE => ?_⟩
  set y := E.genericPoint
  have hyU : y ∈ U := by
    obtain ⟨w, hwE, hwU⟩ := hE
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hwE
    exact (specializes_iff_mem_closure.mpr hwE).mem_open U.isOpen hwU
  have hy1 : Order.coheight y = 1 := E.coheight_genericPoint
  have hfib : ∀ x : T, π x = y → Order.coheight x = 1 := fun x hx =>
    coheight_eq_one_of_coheight_map_eq_one π x (hx ▸ hy1)
  obtain ⟨t, ht⟩ := exists_ord_genericPoint_eq_one E
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht
  have hπt0 : algebraMap Z.functionField T.functionField t ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap Z.functionField T.functionField).injective).mpr ht0
  have key := Stacks.Chow.finsum_ord_mul_residueDegree_of_isFinite π halg (eT g) hg0 y hy1 hfib
  have key2 := Stacks.Chow.finsum_ord_mul_residueDegree_of_isFinite π halg _ hπt0 y hy1 hfib
  rw [Algebra.norm_algebraMap, Scheme.ord_pow ht0 _ y, ht, mul_one] at key2
  have hfin : (π.base ⁻¹' {y}).Finite := π.finite_preimage_singleton y
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at key key2
  have hφ : E.ord ((Units.mk0 _ hN0).map (eZ.symm : Z.functionField →* RationalFunctions Z)) =
      Z.ord (Algebra.norm Z.functionField (eT g)) y := by
    rw [ord_eq_ord_genericPoint]
    simp [eZ, y]
  have hterm : ∀ x ∈ hfin.toFinset,
      ((T.ord (eT g) x : ℤ) : ℚ) = B E * T.ord (algebraMap _ _ t) x := by
    intro x hx
    have hxy : π x = y := by simpa using hx
    have hx1 := hfib x hxy
    set E' : MMP.Mori.PrimeDivisor T := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hx1
    have hE' : E'.genericPoint = x :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hx1
    have hmeet : (E'.support ∩ π ⁻¹ᵁ U).Nonempty := by
      refine ⟨x, ?_, ?_⟩
      · have hx' : x ∈ closure {E'.genericPoint} := by rw [hE']; exact subset_closure rfl
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact hx'
      · change π x ∈ U
        rw [hxy]; exact hyU
    have h1 := hg E' hmeet
    rw [ord_eq_ord_genericPoint, hE'] at h1
    have h3 := hB' E E' (by rw [hE', hxy]) t ht
    rw [hE'] at h3
    rw [← h1, h3, mul_comm]
    rfl
  rw [hφ, ← key]
  push_cast
  rw [Finset.sum_congr rfl fun x hx => by rw [hterm x hx]]
  have key2' := congrArg (fun k : ℤ => (k : ℚ)) key2
  push_cast at key2'
  rw [← key2', Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-- **Local descent along a finite morphism.** If `π^*B` is principal near every point over `z`,
then some positive multiple of `B` is principal near `z`. -/
private theorem exists_localEquation_of_isFinite (B : QDivisor Z) (B' : QDivisor T)
    (hB' : ∀ (E : MMP.Mori.PrimeDivisor Z) (E' : MMP.Mori.PrimeDivisor T),
      π E'.genericPoint = E.genericPoint → ∀ t : Z.functionField, Z.ord t E.genericPoint = 1 →
        B' E' = (T.ord (AlgebraicGeometry.functionFieldMap π t) E'.genericPoint : ℚ) * B E)
    (z : Z)
    (hloc : ∀ x : T, π x = z → ∃ O : T.Opens, x ∈ O ∧ ∃ Ψ : (RationalFunctions T)ˣ,
      ∀ E' : MMP.Mori.PrimeDivisor T, (E'.support ∩ O).Nonempty → B' E' = (E'.ord Ψ : ℚ)) :
    ∃ N : ℕ, 0 < N ∧ ∃ U : Z.Opens, z ∈ U ∧ ∃ φ : (RationalFunctions Z)ˣ,
      ∀ E : MMP.Mori.PrimeDivisor Z, (E.support ∩ U).Nonempty → (N : ℚ) * B E = (E.ord φ : ℚ) := by
  classical
  obtain ⟨n, hn, hnorm⟩ := exists_isLocalEquation_norm π B B' hB'
  let D' : Divisor T := Finsupp.mapRange (fun q : ℚ => ⌊q⌋) (by simp) B'
  choose O hxO Ψ hΨ using hloc
  have hD'O : ∀ x (hx : π x = z) (E' : MMP.Mori.PrimeDivisor T), (E'.support ∩ O x hx).Nonempty →
      D'.coeff E' = E'.ord (Ψ x hx) ∧ B' E' = (D'.coeff E' : ℚ) := by
    intro x hx E' hE'
    have h := hΨ x hx E' hE'
    have hD : D'.coeff E' = E'.ord (Ψ x hx) := by
      change ⌊B' E'⌋ = _
      rw [h, Int.floor_intCast]
    exact ⟨hD, by rw [hD, h]⟩
  obtain ⟨U, hzU, g, hg⟩ := exists_isLocalEquation_preimage_of_forall π z
    (D' := D') fun x hx => ⟨O x hx, hxO x hx, Ψ x hx, fun E' hE' => (hD'O x hx E' hE').1⟩
  set Ω : Set T := ⋃ x, ⋃ (hx : π x = z), (O x hx : Set T)
  have hΩ : IsOpen Ω := isOpen_iUnion fun x => isOpen_iUnion fun hx => (O x hx).isOpen
  have hcl : IsClosed (π '' Ωᶜ) := π.isClosedMap _ hΩ.isClosed_compl
  set U' : Z.Opens := U ⊓ ⟨(π '' Ωᶜ)ᶜ, hcl.isOpen_compl⟩
  have hzU' : z ∈ U' := by
    refine ⟨hzU, ?_⟩
    rintro ⟨w, hw, hwz⟩
    exact hw (Set.mem_iUnion₂.mpr ⟨w, hwz, hxO w hwz⟩)
  refine ⟨n, hn, U', hzU', hnorm U' g fun E' hE' => ?_⟩
  obtain ⟨w, hwE, hwU⟩ := hE'
  have hwΩ : w ∈ Ω := by
    by_contra hw
    exact hwU.2 ⟨w, hw, rfl⟩
  obtain ⟨x, hx, hwO⟩ := Set.mem_iUnion₂.mp hwΩ
  rw [(hD'O x hx E' ⟨w, hwE, hwO⟩).2, hg E' ⟨w, hwE, hwU.1⟩]

end Descent

/-! ### Local principality of the pull-back of `B` -/

/-- At the generic point, the map from the local ring to the function field is the identity. -/
private theorem algebraMap_stalk_genericPoint {X : Scheme.{u}} [IsIntegral X]
    (f : X.presheaf.stalk (genericPoint X)) :
    @algebraMap _ _ _ _ (stalkFunctionFieldAlgebra X (genericPoint X)) f = f := by
  rw [RingHom.algebraMap_toAlgebra, TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- An open immersion into an integral scheme from a nonempty scheme induces a bijection of
function fields. -/
private theorem functionFieldMap_bijective_of_isOpenImmersion' {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X) [IsOpenImmersion f] [IsDominant f] :
    Function.Bijective (AlgebraicGeometry.functionFieldMap f) := by
  haveI : IsOpenImmersion ((⊤ : Y.Opens).ι ≫ f) := inferInstance
  exact MMP.Mori.functionFieldMap_bijective_of_isOpenImmersion f ⊤
    ⟨genericPoint Y, trivial⟩

/-- **The pull-back of `B` is principal near a slice.** Let `ι_W : Z ⟶ W` be an open immersion,
`π : T ⟶ Z` dominant and preserving codimension one, `ρ : T_r ⟶ T` an open immersion and
`τ : T_r ⟶ V` a morphism with `τ ≫ g = ρ ≫ π ≫ ι_W`, sending the generic point of `T_r` to a
point `ξ` of codimension one of `V` which lies on no component of `D`. If `ψ` is a local equation
of `D` near the image of `τ`, then `π^*B` agrees with `div(τ^*ψ)` along every prime divisor of `T`
meeting `ρ(T_r)`: near `y = τ(ξ')`, `ψⁿ (g^*t)^{-m}` (with `B = m/n` along the prime divisor under
`y`) has order zero along every prime divisor of `V` through `y`, so it is a unit, which pulls
back along `τ`. -/
private theorem exists_localEquation_pullback {d : ℕ} {K : Divisor V} {Δ : QDivisor V}
    {g : V ⟶ W} (h : IsLogEllipticFiberSpace k sV sW d K Δ g) [IsDominant g]
    (hfib : ∀ w : W, ∀ Y ∈ irreducibleComponents (g.base ⁻¹' {w}), topologicalKrullDim Y = 1)
    (D : Divisor V)
    (hDv : ∀ E : MMP.Mori.PrimeDivisor V, g E.genericPoint = genericPoint W → D.coeff E = 0)
    (B : QDivisor W)
    (hB : ∀ (E : MMP.Mori.PrimeDivisor V) (C : MMP.Mori.PrimeDivisor W),
      g E.genericPoint = C.genericPoint → ∀ t : W.functionField, W.ord t C.genericPoint = 1 →
        (D.coeff E : ℚ) = B C * V.ord (AlgebraicGeometry.functionFieldMap g t) E.genericPoint)
    {Z T Tr : Scheme.{u}} [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [IsIntegral Tr] [IsLocallyNoetherian Tr]
    [IsNormal Tr]
    (ιW : Z ⟶ W) [IsOpenImmersion ιW] [IsDominant ιW] (π : T ⟶ Z) [IsDominant π]
    (ρ : Tr ⟶ T) [IsOpenImmersion ρ] [IsDominant ρ] (τ : Tr ⟶ V) (hτ : τ ≫ g = ρ ≫ π ≫ ιW)
    (hcoh : ∀ x : T, Order.coheight x = 1 → Order.coheight (π x) = 1)
    (B' : QDivisor T)
    (hB' : ∀ (E : MMP.Mori.PrimeDivisor Z) (E' : MMP.Mori.PrimeDivisor T),
      π E'.genericPoint = E.genericPoint → ∀ t : Z.functionField, Z.ord t E.genericPoint = 1 →
        B' E' = (T.ord (AlgebraicGeometry.functionFieldMap π t) E'.genericPoint : ℚ) *
          B (OpenWeilRestriction.primeDivisorMap ιW E))
    (Uψ : V.Opens) (ψ : (RationalFunctions V)ˣ) (hψ : D.IsLocalEquation Uψ ψ)
    (hτU : ∀ p : Tr, τ p ∈ Uψ) (hξ1 : Order.coheight (τ (genericPoint Tr)) = 1)
    (hξD : D.coeff (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hξ1) = 0) :
    ∃ Ψ : (RationalFunctions T)ˣ, ∀ E' : MMP.Mori.PrimeDivisor T,
      (E'.support ∩ ρ.opensRange).Nonempty → B' E' = (E'.ord Ψ : ℚ) := by
  classical
  have gm : ∀ {X : Scheme.{u}} (E : MMP.Mori.PrimeDivisor X), E.genericPoint ∈ E.support :=
    fun E => by rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  set ξ := τ (genericPoint Tr) with hξdef
  set H : MMP.Mori.PrimeDivisor V := AlgebraicGeometry.PrimeDivisor.ofCoheightOne ξ hξ1
  have hHξ : H.genericPoint = ξ := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  -- `ψ` is a unit at `ξ`
  set ψV := rationalFunctionsEquivFunctionField V (ψ : RationalFunctions V)
  have hψ0 : ψV ≠ 0 := (ψ.isUnit.map (rationalFunctionsEquivFunctionField V)).ne_zero
  have hordψ : ∀ F : MMP.Mori.PrimeDivisor V, (F.support ∩ Uψ).Nonempty →
      V.ord ψV F.genericPoint = D.coeff F := fun F hF => by
    rw [← ord_eq_ord_genericPoint, hψ F hF]
  have hHU : (H.support ∩ Uψ).Nonempty := ⟨H.genericPoint, gm H, by rw [hHξ]; exact hτU _⟩
  have hψξ : V.ord ψV ξ = 0 := by rw [← hHξ, hordψ H hHU, hξD]
  haveI : IsDiscreteValuationRing (V.presheaf.stalk ξ) := by
    rw [← hHξ]; exact H.isDiscreteValuationRing_localRing
  obtain ⟨tH, htH⟩ := exists_ord_genericPoint_eq_one H
  obtain ⟨a, ha⟩ := exists_eq_algebraMap_mul_zpow hξ1 hψ0 (by rw [← hHξ]; exact htH)
  rw [hψξ, zpow_zero, mul_one] at ha
  -- `τ^*ψ`
  set τψ : Tr.functionField := (τ.stalkMap (genericPoint Tr)).hom (a : V.presheaf.stalk ξ)
  have hτψ : IsUnit τψ := a.isUnit.map _
  obtain ⟨ΨT, hΨT⟩ := (functionFieldMap_bijective_of_isOpenImmersion' ρ).2 τψ
  have hΨT0 : ΨT ≠ 0 := by
    rintro rfl
    rw [map_zero] at hΨT
    exact hτψ.ne_zero hΨT.symm
  let Ψ : (RationalFunctions T)ˣ :=
    Units.map (rationalFunctionsEquivFunctionField T).symm.toMonoidHom (Units.mk0 ΨT hΨT0)
  have hΨ : rationalFunctionsEquivFunctionField T (Ψ : RationalFunctions T) = ΨT := by simp [Ψ]
  refine ⟨Ψ, fun E' hE' => ?_⟩
  -- the point of `T_r` over `η_{E'}`
  obtain ⟨er, her⟩ : E'.genericPoint ∈ Set.range ρ :=
    (E'.genericPoint_mem_iff ρ.opensRange).mpr hE'
  have her1 : Order.coheight er = 1 := by
    rw [← coheight_eq_of_isOpenImmersion ρ, her]; exact E'.coheight_genericPoint
  set Er : MMP.Mori.PrimeDivisor Tr := AlgebraicGeometry.PrimeDivisor.ofCoheightOne er her1
  have hEr : Er.genericPoint = er := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  have hρE : ρ Er.genericPoint = E'.genericPoint := by rw [hEr, her]
  -- the left side
  have hL : (E'.ord Ψ : ℤ) = Tr.ord τψ er := by
    rw [ord_eq_ord_genericPoint E' Ψ, hΨ, ← hEr, ← hΨT,
      MMP.Positivity.ord_functionFieldMap_of_isIso ρ Er E' hρE ΨT]
  -- the prime divisors under `E'`
  have hcZ : Order.coheight (π E'.genericPoint) = 1 := hcoh _ E'.coheight_genericPoint
  set E : MMP.Mori.PrimeDivisor Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcZ
  have hE : E.genericPoint = π E'.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  set C : MMP.Mori.PrimeDivisor W := OpenWeilRestriction.primeDivisorMap ιW E
  have hC : C.genericPoint = ιW E.genericPoint :=
    OpenWeilRestriction.genericPoint_primeDivisorMap _ _
  set y := τ er
  have hgy : g y = C.genericPoint := by
    rw [hC, hE, ← her]
    change (τ ≫ g) er = (ρ ≫ π ≫ ιW) er
    rw [hτ]
  obtain ⟨t, ht⟩ := exists_ord_genericPoint_eq_one C
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht
  set tZ := AlgebraicGeometry.functionFieldMap ιW t
  have htZ : Z.ord tZ E.genericPoint = 1 := by
    rw [MMP.Positivity.ord_functionFieldMap_of_isIso ιW E C hC.symm t, ht]
  have hB'E' := hB' E E' hE.symm tZ htZ
  -- the unit `ψⁿ (g^*t)^{-m}` near `y`
  set gt := AlgebraicGeometry.functionFieldMap g t
  have hgt0 : gt ≠ 0 := (map_ne_zero _).mpr ht0
  set m : ℤ := (B C).num
  set n : ℕ := (B C).den
  have hBmn : B C = (m : ℚ) / n := (Rat.num_div_den (B C)).symm
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (B C).den_pos.ne'
  set G : V.functionField := ψV ^ (n : ℤ) * gt ^ (-m)
  have hG0 : G ≠ 0 := mul_ne_zero (zpow_ne_zero _ hψ0) (zpow_ne_zero _ hgt0)
  have hyU : y ∈ Uψ := hτU er
  have hordG : ∀ F : MMP.Mori.PrimeDivisor V, y ∈ F.support → V.ord G F.genericPoint = 0 := by
    intro F hyF
    have hFU : (F.support ∩ Uψ).Nonempty := ⟨y, hyF, hyU⟩
    have hsp : g F.genericPoint ⤳ C.genericPoint := by
      rw [← hgy]
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hyF
      exact (specializes_iff_mem_closure.mpr hyF).map g.continuous
    rw [Scheme.ord_mul (zpow_ne_zero _ hψ0) (zpow_ne_zero _ hgt0), ord_zpow hψ0, ord_zpow hgt0,
      hordψ F hFU]
    rcases map_genericPoint_eq h hfib F with hη | ⟨C', hC'⟩
    · rw [hDv F hη, ord_functionFieldMap_eq_zero_of_eq_genericPoint g _ hη ht0]
      simp
    · rw [hC'] at hsp
      rw [primeDivisor_eq_of_specializes hsp] at hC'
      have hDF := hB F C hC' t ht
      rw [hBmn] at hDF
      have : (n : ℚ) * D.coeff F = m * V.ord gt F.genericPoint := by
        rw [hDF, show gt = AlgebraicGeometry.functionFieldMap g t from rfl]; field_simp
      have : (n : ℤ) * D.coeff F = m * V.ord gt F.genericPoint := by exact_mod_cast this
      linarith
  obtain ⟨u, hu⟩ := exists_algebraMap_stalk_eq_of_forall_ord_nonneg y hG0 fun F hF =>
    (hordG F hF).ge
  obtain ⟨u', hu'⟩ := exists_algebraMap_stalk_eq_of_forall_ord_nonneg y (inv_ne_zero hG0)
    fun F hF => by
      rw [show V.ord G⁻¹ F.genericPoint = - V.ord G F.genericPoint by
        have := Scheme.ord_mul (x := F.genericPoint) (inv_ne_zero hG0) hG0
        rw [inv_mul_cancel₀ hG0, Scheme.ord_one] at this
        omega, hordG F hF, neg_zero]
  have huu : u * u' = 1 := IsFractionRing.injective (V.presheaf.stalk y) V.functionField (by
    rw [map_mul, hu, hu', mul_inv_cancel₀ hG0, map_one])
  have huU : IsUnit u := ⟨⟨u, u', huu, by rw [mul_comm]; exact huu⟩, rfl⟩
  -- transport to the local ring at `ξ` and pull back along `τ`
  have hηer : genericPoint Tr ⤳ er := (genericPoint_spec Tr).specializes trivial
  have hξy : ξ ⤳ y := hηer.map τ.continuous
  haveI : IsDominant (τ ≫ g) := by rw [hτ]; infer_instance
  have hgξ : g ξ = genericPoint W := by
    change (τ ≫ g) (genericPoint Tr) = _
    exact map_genericPoint_of_isDominant (τ ≫ g)
  obtain ⟨ub, hub⟩ := exists_eq_algebraMap_mul_zpow hξ1 hgt0 (by rw [← hHξ]; exact htH)
  rw [ord_functionFieldMap_eq_zero_of_eq_genericPoint g ξ hgξ ht0, zpow_zero, mul_one] at hub
  have hrel : (V.presheaf.stalkSpecializes hξy).hom u =
      ((a ^ (n : ℤ) * ub ^ (-m) : (V.presheaf.stalk ξ)ˣ) : V.presheaf.stalk ξ) := by
    apply IsFractionRing.injective (V.presheaf.stalk ξ) V.functionField
    rw [MMP.Mori.algebraMap_stalkSpecializes, hu]
    change G = ((Units.map (algebraMap (V.presheaf.stalk ξ) V.functionField).toMonoidHom
      (a ^ (n : ℤ) * ub ^ (-m)) : V.functionFieldˣ) : V.functionField)
    rw [map_mul, map_zpow, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val,
      Units.val_zpow_eq_zpow_val]
    change G = (algebraMap _ _ (a : V.presheaf.stalk ξ)) ^ (n : ℤ) *
      (algebraMap _ _ (ub : V.presheaf.stalk ξ)) ^ (-m)
    rw [← ha, ← hub]
  have hτrel : (τ.stalkMap (genericPoint Tr)).hom ((V.presheaf.stalkSpecializes hξy).hom u) =
      τψ ^ (n : ℤ) * ((τ.stalkMap (genericPoint Tr)).hom ub) ^ (-m) := by
    rw [hrel]
    change ((Units.map (τ.stalkMap (genericPoint Tr)).hom.toMonoidHom
      (a ^ (n : ℤ) * ub ^ (-m)) : Tr.functionFieldˣ) : Tr.functionField) = _
    rw [map_mul, map_zpow, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val,
      Units.val_zpow_eq_zpow_val]
    rfl
  have hLHS : Tr.ord ((τ.stalkMap (genericPoint Tr)).hom
      ((V.presheaf.stalkSpecializes hξy).hom u)) er = 0 := by
    have hsq := Scheme.Hom.stalkSpecializes_stalkMap τ (genericPoint Tr) er hηer
    have h2 := congrArg (fun φ => φ.hom u) hsq
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
    rw [h2, ← algebraMap_stalk_genericPoint
      ((Tr.presheaf.stalkSpecializes hηer).hom ((τ.stalkMap er).hom u)),
      MMP.Mori.algebraMap_stalkSpecializes]
    exact ord_algebraMap_eq_zero _ (huU.map _)
  have hτub : (τ.stalkMap (genericPoint Tr)).hom ub =
      AlgebraicGeometry.functionFieldMap ρ (AlgebraicGeometry.functionFieldMap π tZ) := by
    set a' := (W.presheaf.stalkSpecializes
      (show g ξ ⤳ genericPoint W from hgξ ▸ specializes_rfl)).hom t
    have hub' : (ub : V.presheaf.stalk ξ) = (g.stalkMap ξ).hom a' := by
      apply IsFractionRing.injective (V.presheaf.stalk ξ) V.functionField
      rw [← hub, ← MMP.Mori.functionFieldMap_algebraMap_stalk, MMP.Mori.algebraMap_stalkSpecializes,
        algebraMap_stalk_genericPoint]
    rw [hub']
    have h3 : (τ.stalkMap (genericPoint Tr)).hom ((g.stalkMap ξ).hom a') =
        ((τ ≫ g).stalkMap (genericPoint Tr)).hom a' := by
      rw [Scheme.Hom.stalkMap_comp]; rfl
    rw [h3]
    have h4 := MMP.Mori.functionFieldMap_algebraMap_stalk (τ ≫ g) (genericPoint Tr) a'
    rw [algebraMap_stalk_genericPoint] at h4
    have h5 : algebraMap (W.presheaf.stalk ((τ ≫ g) (genericPoint Tr))) W.functionField a' = t := by
      change algebraMap (W.presheaf.stalk (g ξ)) W.functionField a' = t
      rw [MMP.Mori.algebraMap_stalkSpecializes, algebraMap_stalk_genericPoint]
    rw [← h4, h5, MMP.Positivity.DivisorOver.functionFieldMap_congr hτ,
      ← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      ← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  have hτub0 : (τ.stalkMap (genericPoint Tr)).hom ub ≠ 0 := (ub.isUnit.map _).ne_zero
  have hord := congrArg (fun f => Tr.ord f er) hτrel
  simp only at hord
  rw [hLHS, Scheme.ord_mul (zpow_ne_zero _ hτψ.ne_zero) (zpow_ne_zero _ hτub0),
    ord_zpow hτψ.ne_zero, ord_zpow hτub0, hτub, ← hEr,
    MMP.Positivity.ord_functionFieldMap_of_isIso ρ Er E' hρE] at hord
  rw [hB'E', hL, ← hEr]
  change _ * B C = _
  rw [hBmn]
  have hq : ((n : ℤ) : ℚ) * (Tr.ord τψ Er.genericPoint : ℚ) =
      (m : ℚ) * (T.ord (AlgebraicGeometry.functionFieldMap π tZ) E'.genericPoint : ℚ) := by
    have : (n : ℤ) * Tr.ord τψ Er.genericPoint =
        m * T.ord (AlgebraicGeometry.functionFieldMap π tZ) E'.genericPoint := by linarith
    exact_mod_cast this
  push_cast at hq
  field_simp
  linarith

/-! ### Transporting local equations along automorphisms and open immersions -/

/-- **Transport along an automorphism over the base.** Let `α` be an automorphism of `T` over
`Z`. If `π^*B` agrees with `div Ψ` along the prime divisors meeting `O`, it agrees with
`div(α^*Ψ)` along those meeting `α⁻¹(O)`: `α` permutes the prime divisors over each prime divisor
of `Z` without changing the order of `π^*t`. -/
private theorem exists_localEquation_of_iso {Z T : Scheme.{u}} [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    (π : T ⟶ Z) [IsDominant π] (hcoh : ∀ x : T, Order.coheight x = 1 → Order.coheight (π x) = 1)
    (BZ : QDivisor Z) (B' : QDivisor T)
    (hB' : ∀ (E : MMP.Mori.PrimeDivisor Z) (E' : MMP.Mori.PrimeDivisor T),
      π E'.genericPoint = E.genericPoint → ∀ t : Z.functionField, Z.ord t E.genericPoint = 1 →
        B' E' = (T.ord (AlgebraicGeometry.functionFieldMap π t) E'.genericPoint : ℚ) * BZ E)
    (α : T ≅ T) (hα : α.hom ≫ π = π) (O : T.Opens) (Ψ : (RationalFunctions T)ˣ)
    (hΨ : ∀ E' : MMP.Mori.PrimeDivisor T, (E'.support ∩ O).Nonempty → B' E' = (E'.ord Ψ : ℚ)) :
    ∃ Ψ' : (RationalFunctions T)ˣ, ∀ E' : MMP.Mori.PrimeDivisor T,
      (E'.support ∩ α.hom ⁻¹ᵁ O).Nonempty → B' E' = (E'.ord Ψ' : ℚ) := by
  classical
  set eT := rationalFunctionsEquivFunctionField T
  set f := AlgebraicGeometry.functionFieldMap α.hom (eT (Ψ : RationalFunctions T))
  have hf0 : f ≠ 0 := (map_ne_zero _).mpr ((Ψ.isUnit.map eT).ne_zero)
  let Ψ' : (RationalFunctions T)ˣ := Units.map eT.symm.toMonoidHom (Units.mk0 f hf0)
  have hΨ' : eT (Ψ' : RationalFunctions T) = f := by simp [Ψ']
  refine ⟨Ψ', fun E' hE' => ?_⟩
  have hc : Order.coheight (α.hom E'.genericPoint) = 1 := by
    rw [coheight_eq_of_isOpenImmersion α.hom]; exact E'.coheight_genericPoint
  set E'' : MMP.Mori.PrimeDivisor T := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc
  have hE'' : E''.genericPoint = α.hom E'.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  have hE''O : (E''.support ∩ O).Nonempty := by
    rw [← E''.genericPoint_mem_iff, hE'']
    exact (E'.genericPoint_mem_iff _).mpr hE'
  -- orders along `E'` and `E''`
  have hord : ∀ g : T.functionField,
      T.ord (AlgebraicGeometry.functionFieldMap α.hom g) E'.genericPoint =
        T.ord g E''.genericPoint := fun g =>
    MMP.Positivity.ord_functionFieldMap_of_isIso α.hom E' E'' hE''.symm g
  have hπα : ∀ t : Z.functionField, AlgebraicGeometry.functionFieldMap α.hom
      (AlgebraicGeometry.functionFieldMap π t) = AlgebraicGeometry.functionFieldMap π t := by
    intro t
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_congr hα]
  -- the prime divisor of `Z` under both
  have hcZ : Order.coheight (π E'.genericPoint) = 1 := hcoh _ E'.coheight_genericPoint
  set E : MMP.Mori.PrimeDivisor Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcZ
  have hE : E.genericPoint = π E'.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  have hπE'' : π E''.genericPoint = E.genericPoint := by
    rw [hE'', hE, ← Scheme.Hom.comp_apply, hα]
  obtain ⟨t, ht⟩ := exists_ord_genericPoint_eq_one E
  rw [hB' E E' hE.symm t ht, ← hπα t, hord, ← hB' E E'' hπE'' t ht, hΨ E'' hE''O,
    ord_eq_ord_genericPoint E' Ψ', hΨ', hord, ← ord_eq_ord_genericPoint]

/-- **Transport along an open immersion.** A local equation of `N B|_Z` on an open `U` of an
open subscheme `Z ⊆ W` is a local equation of `N B` on the image of `U`. -/
private theorem exists_localEquation_of_isOpenImmersion {Z : Scheme.{u}} [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    (ιW : Z ⟶ W) [IsOpenImmersion ιW] [IsDominant ιW] (B : QDivisor W) (N : ℕ) (U : Z.Opens)
    (φ : (RationalFunctions Z)ˣ)
    (hφ : ∀ E : MMP.Mori.PrimeDivisor Z, (E.support ∩ U).Nonempty →
      (N : ℚ) * B (OpenWeilRestriction.primeDivisorMap ιW E) = (E.ord φ : ℚ)) :
    ∃ φ' : (RationalFunctions W)ˣ, ∀ E : MMP.Mori.PrimeDivisor W,
      (E.support ∩ ιW ''ᵁ U).Nonempty → (N : ℚ) * B E = (E.ord φ' : ℚ) := by
  classical
  set eZ := rationalFunctionsEquivFunctionField Z
  set eW := rationalFunctionsEquivFunctionField W
  obtain ⟨f, hf⟩ := (functionFieldMap_bijective_of_isOpenImmersion' ιW).2 (eZ (φ : _))
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [map_zero] at hf
    exact (φ.isUnit.map eZ).ne_zero hf.symm
  let φ' : (RationalFunctions W)ˣ := Units.map eW.symm.toMonoidHom (Units.mk0 f hf0)
  have hφ' : eW (φ' : RationalFunctions W) = f := by simp [φ']
  refine ⟨φ', fun E hE => ?_⟩
  obtain ⟨w, hwE, hwU⟩ := hE
  obtain ⟨v, hvU, rfl⟩ := hwU
  obtain ⟨E₀, rfl⟩ :=
    MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support ιW E v hwE
  have hE₀ : (E₀.support ∩ U).Nonempty :=
    ⟨v, (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff ιW E₀ v).mp hwE, hvU⟩
  rw [hφ E₀ hE₀, ord_eq_ord_genericPoint E₀ φ, ord_eq_ord_genericPoint _ φ', hφ', ← hf,
    MMP.Positivity.ord_functionFieldMap_of_isIso ιW E₀ _
      (OpenWeilRestriction.genericPoint_primeDivisorMap ιW E₀).symm]

/-- **The pull-back of a `ℚ`-divisor along a finite morphism.** For a finite dominant morphism
`π : T ⟶ Z` of integral normal Noetherian schemes and a `ℚ`-divisor `B` on `Z` there is a
`ℚ`-divisor `π^*B` on `T` whose coefficient along a prime divisor `E'` over a prime divisor `E` is
`ord_{E'}(π^*t) · B_E` for every uniformizer `t` at `E`. -/
private theorem exists_pullback_of_isFinite {Z T : Scheme.{u}} [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    (π : T ⟶ Z) [IsFinite π] [IsDominant π] (BZ : QDivisor Z) :
    ∃ B' : QDivisor T, ∀ (E : MMP.Mori.PrimeDivisor Z) (E' : MMP.Mori.PrimeDivisor T),
      π E'.genericPoint = E.genericPoint → ∀ t : Z.functionField, Z.ord t E.genericPoint = 1 →
        B' E' = (T.ord (AlgebraicGeometry.functionFieldMap π t) E'.genericPoint : ℚ) * BZ E := by
  classical
  choose tE htE using fun E : MMP.Mori.PrimeDivisor Z => exists_ord_genericPoint_eq_one E
  let c : MMP.Mori.PrimeDivisor T → ℚ := fun E' =>
    if hc : Order.coheight (π E'.genericPoint) = 1 then
      (T.ord (AlgebraicGeometry.functionFieldMap π
        (tE (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc))) E'.genericPoint : ℚ) *
        BZ (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc)
    else 0
  have hfin : {E' | c E' ≠ 0}.Finite := by
    refine (Set.Finite.biUnion BZ.support.finite_toSet fun E _ =>
      ((π.finite_preimage_singleton E.genericPoint).preimage
        (AlgebraicGeometry.PrimeDivisor.genericPoint_injective.injOn))).subset ?_
    intro E' hE'
    simp only [Set.mem_setOf_eq, c] at hE'
    split_ifs at hE' with hc
    · refine Set.mem_iUnion₂.mpr ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc, ?_, ?_⟩
      · rw [Finset.mem_coe, Finsupp.mem_support_iff]
        exact right_ne_zero_of_mul hE'
      · exact (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hc).symm
    · exact absurd rfl hE'
  refine ⟨Finsupp.ofSupportFinite c hfin, fun E E' hE t ht => ?_⟩
  have hc : Order.coheight (π E'.genericPoint) = 1 := by rw [hE]; exact E.coheight_genericPoint
  have hEE : AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc = E :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      ((AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _).trans hE)
  change c E' = _
  simp only [c, dif_pos hc, hEE]
  congr 2
  haveI : IsDiscreteValuationRing (Z.presheaf.stalk (π E'.genericPoint)) := by
    rw [hE]; exact E.isDiscreteValuationRing_localRing
  have htE0 : tE E ≠ 0 := by intro h0; have := htE E; rw [h0] at this; simp at this
  rw [ord_functionFieldMap_eq_mul π E'.genericPoint hc htE0 (hE ▸ ht), hE, htE E, one_mul]

/-! ### `ℚ`-Cartier divisors from local equations -/

/-- A `ℚ`-divisor `B` such that `N B` has, near every point, a local equation, is `ℚ`-Cartier. -/
private lemma isQCartier_of_forall_exists {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] (B : QDivisor X) (N : ℕ) (hN : 0 < N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ φ : (RationalFunctions X)ˣ,
      ∀ E : MMP.Mori.PrimeDivisor X, (E.support ∩ U).Nonempty → (N : ℚ) * B E = (E.ord φ : ℚ)) :
    B.IsQCartier := by
  have hint : ∀ E : MMP.Mori.PrimeDivisor X, ∃ k : ℤ, (N : ℚ) * B E = k := by
    intro E
    obtain ⟨U, hU, φ, hφ⟩ := h E.genericPoint
    refine ⟨E.ord φ, hφ E ⟨E.genericPoint, ?_, hU⟩⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  let D : Divisor X := Finsupp.mapRange (fun q : ℚ => ⌊(N : ℚ) * q⌋) (by simp) B
  have hD : ∀ E, ((D E : ℤ) : ℚ) = (N : ℚ) * B E := by
    intro E
    obtain ⟨k, hk⟩ := hint E
    simp only [D, Finsupp.mapRange_apply, hk, Int.floor_intCast]
  refine ⟨N, by exact_mod_cast hN.ne', D, ?_, ?_⟩
  · refine Finsupp.ext fun E => ?_
    have := Divisor.coeff_toQDivisor D E
    simp only [DivisorWithCoeffs.coeff] at this
    rw [this, hD, Finsupp.smul_apply, zsmul_eq_mul]
    simp
  · intro x
    obtain ⟨U, hU, φ, hφ⟩ := h x
    refine ⟨U, hU, φ, fun E hE => ?_⟩
    have := hφ E hE
    rw [← hD] at this
    exact_mod_cast this

/-- **`ℚ`-Cartierness is checked at closed points.** On a quasi-compact Noetherian normal scheme,
a `ℚ`-divisor `B` such that near every closed point some positive multiple `N B` has a local
equation is `ℚ`-Cartier: every point specializes to a closed point, and finitely many of the
neighbourhoods cover, so one multiple works everywhere. -/
private theorem isQCartier_of_forall_isClosed {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] (B : QDivisor X)
    (h : ∀ z : X, IsClosed ({z} : Set X) → ∃ N : ℕ, 0 < N ∧ ∃ U : X.Opens, z ∈ U ∧
      ∃ φ : (RationalFunctions X)ˣ, ∀ E : MMP.Mori.PrimeDivisor X, (E.support ∩ U).Nonempty →
        (N : ℚ) * B E = (E.ord φ : ℚ)) :
    B.IsQCartier := by
  classical
  have h' : ∀ x : X, ∃ N : ℕ, 0 < N ∧ ∃ U : X.Opens, x ∈ U ∧
      ∃ φ : (RationalFunctions X)ˣ, ∀ E : MMP.Mori.PrimeDivisor X, (E.support ∩ U).Nonempty →
        (N : ℚ) * B E = (E.ord φ : ℚ) := by
    intro x
    obtain ⟨z, hz, hzc⟩ :=
      (isClosed_closure : IsClosed (closure ({x} : Set X))).exists_closed_singleton
      ⟨x, subset_closure rfl⟩
    obtain ⟨N, hN, U, hzU, φ, hφ⟩ := h z hzc
    exact ⟨N, hN, U, (specializes_iff_mem_closure.mpr hz).mem_open U.isOpen hzU, φ, hφ⟩
  choose N hN U hxU φ hφ using h'
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (U x : Set X))
    (fun x => (U x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hxU x⟩)
  set M := ∏ x ∈ t, N x
  have hM : 0 < M := Finset.prod_pos fun x _ => hN x
  refine isQCartier_of_forall_exists B M hM fun y => ?_
  obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
  obtain ⟨c, hc⟩ : N x ∣ M := Finset.dvd_prod_of_mem _ hxt
  refine ⟨U x, hyx, φ x ^ (c : ℤ), fun E hE => ?_⟩
  rw [PrimeDivisor.ord_zpow, hc]
  push_cast
  rw [mul_comm (N x : ℚ), mul_assoc, hφ x E hE, smul_eq_mul]
  push_cast
  ring

/-- In a closed subset `F` of a quasi-sober `T₀` space all of whose irreducible components have
dimension one, a point `y ∈ F` with a proper specialization `x ∈ F` is the generic point of an
irreducible component of `F`. -/
private lemma exists_isGenericPoint_of_specializes {X : Type*} [TopologicalSpace X] [T0Space X]
    [QuasiSober X] {F : Set X} (hF : IsClosed F)
    (hdim : ∀ Y ∈ irreducibleComponents F, topologicalKrullDim Y = 1) {x y : X} (hx : x ∈ F)
    (hy : y ∈ F) (hyx : y ⤳ x) (hne : y ≠ x) :
    ∃ Y ∈ irreducibleComponents F, IsGenericPoint (⟨y, hy⟩ : F) Y := by
  haveI : QuasiSober F := hF.isClosedEmbedding_subtypeVal.quasiSober
  obtain ⟨Y, hY, hyY⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    {(⟨y, hy⟩ : F)} isIrreducible_singleton
  have hYc : IsClosed Y := isClosed_of_mem_irreducibleComponents Y hY
  have hYi : IsIrreducible Y := hY.1
  have hη : IsGenericPoint hYi.genericPoint Y := by
    simpa [hYc.closure_eq] using hYi.isGenericPoint_genericPoint_closure
  refine ⟨Y, hY, ?_⟩
  by_contra hng
  have hyY' : (⟨y, hy⟩ : F) ∈ Y := hyY rfl
  have h1 : hYi.genericPoint ⤳ ⟨y, hy⟩ := hη.specializes hyY'
  have h2 : (⟨y, hy⟩ : F) ⤳ ⟨x, hx⟩ := (subtype_specializes_iff _ _).mpr hyx
  have hxY : (⟨x, hx⟩ : F) ∈ Y := h2.mem_closed hYc hyY'
  have hne1 : hYi.genericPoint ≠ ⟨y, hy⟩ := fun he => hng (he ▸ hη)
  have hne2 : (⟨y, hy⟩ : F) ≠ ⟨x, hx⟩ := fun he => hne (congrArg Subtype.val he)
  have h2le := MMP.Flips.two_le_topologicalKrullDim_of_specializes hη.mem hyY' hxY h1 h2 hne1 hne2
  rw [hdim Y hY] at h2le
  exact absurd h2le (by decide)

/-- **The slice dominates `W`.** Let `q` be a prime of `Γ(U_a)`, `U_a ⊆ g⁻¹(W₀)` affine, whose
point `ξ` has codimension one, such that `Γ(U_a)/q` is quasi-finite over `Γ(W₀)` at some prime.
Then `g(ξ)` is the generic point of `W` and `Γ(W₀) → Γ(U_a)/q` is injective: by Zariski's main
theorem `κ(ξ)` is algebraic over `κ(g ξ)`, and the dimension formula
`dim 𝒪_ξ + trdeg κ(ξ)/κ(gξ) = dim 𝒪_{gξ} + trdeg K(V)/K(W)` with `trdeg K(V)/K(W) = 1` (the
generic fibre is a curve) forces `dim 𝒪_{gξ} = 0`. -/
private theorem map_eq_genericPoint_of_quasiFiniteAt {d : ℕ} {K : Divisor V} {Δ : QDivisor V}
    {g : V ⟶ W} (h : IsLogEllipticFiberSpace k sV sW d K Δ g) [IsDominant g]
    {W0 : W.Opens} (hW0 : IsAffineOpen W0) {Ua : V.Opens} (hUa : IsAffineOpen Ua)
    (hUaW : Ua ≤ g ⁻¹ᵁ W0) [IsDomain Γ(W, W0)] (q : Ideal Γ(V, Ua)) [q.IsPrime]
    (hq1 : Order.coheight (hUa.fromSpec ⟨q, inferInstance⟩) = 1) (p : Ideal (Γ(V, Ua) ⧸ q))
    [p.IsPrime]
    (hQF : letI := (g.appLE W0 Ua hUaW).hom.toAlgebra; Algebra.QuasiFiniteAt Γ(W, W0) p) :
    letI := (g.appLE W0 Ua hUaW).hom.toAlgebra
    g (hUa.fromSpec ⟨q, inferInstance⟩) = genericPoint W ∧
      Function.Injective (algebraMap Γ(W, W0) (Γ(V, Ua) ⧸ q)) := by
  letI := (g.appLE W0 Ua hUaW).hom.toAlgebra
  haveI := hQF
  haveI := h.isContraction.isVariety_source.toLocallyOfFiniteType
  haveI := h.isContraction.isVariety_target.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType g :=
    MMP.Flips.locallyOfFiniteType_of_comp_eq sV sW g h.isContraction.comp_eq
  haveI : Algebra.FiniteType Γ(W, W0) Γ(V, Ua) := g.finiteType_appLE hW0 hUa hUaW
  set ξ := hUa.fromSpec ⟨q, inferInstance⟩ with hξdef
  have hξ : ξ ∈ Ua := hUa.range_fromSpec.subset ⟨_, rfl⟩
  have hcat := Scheme.isUniversallyCatenary_of_locallyOfFiniteType_over_field k sW
  -- The transcendence degree of `K(V)/K(W)` is one.
  have hT := ringKrullDim_stalk_add_trdeg_residueField_eq g hcat (genericPoint V)
  have hfib := toENat_trdeg_eq_topologicalKrullDim_fiber g (genericPoint V)
    (MMP.Flips.isGenericPoint_asFiber_genericPoint g)
  have hdim1 : topologicalKrullDim (g.base ⁻¹' {g (genericPoint V)}) = 1 := by
    rw [map_genericPoint_of_isDominant]
    exact h.dim_genericFiber
  rw [(g.fiberHomeo _).isHomeomorph.topologicalKrullDim_eq, hdim1] at hfib
  dsimp only at hT hfib
  letI : Algebra (W.residueField (g (genericPoint V))) (V.residueField (genericPoint V)) :=
    (g.residueFieldMap (genericPoint V)).hom.toAlgebra
  have ht1 : Cardinal.toNat (Algebra.trdeg (W.residueField (g (genericPoint V)))
      (V.residueField (genericPoint V))) = 1 := by
    rw [← Cardinal.toNat_toENat]
    have : Cardinal.toENat (Algebra.trdeg (W.residueField (g (genericPoint V)))
        (V.residueField (genericPoint V))) = 1 := by exact_mod_cast hfib
    rw [this]
    rfl
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, ht1,
    map_genericPoint_of_isDominant, coheight_genericPoint_eq_zero,
    coheight_genericPoint_eq_zero] at hT
  -- At `ξ` the residue field extension is algebraic.
  have hxi := ringKrullDim_stalk_add_trdeg_residueField_eq g hcat ξ
  dsimp only at hxi
  have htr := trdeg_residueField_eq_trdeg_residueField_primeIdealOf g hW0 hUa hUaW ξ hξ
  dsimp only at htr
  have hQ : hUa.primeIdealOf ⟨ξ, hξ⟩ = ⟨q, inferInstance⟩ := hUa.primeIdealOf_fromSpec _ hξ
  have hzero : ∀ (Q' : PrimeSpectrum Γ(V, Ua)), Q' = ⟨q, inferInstance⟩ →
      ∀ (𝔮 : Ideal Γ(W, W0)) [𝔮.IsPrime] [Q'.asIdeal.LiesOver 𝔮],
        letI : Algebra 𝔮.ResidueField Q'.asIdeal.ResidueField :=
          (Ideal.ResidueField.map _ _ (algebraMap Γ(W, W0) Γ(V, Ua)) Ideal.LiesOver.over).toAlgebra
        Algebra.trdeg 𝔮.ResidueField Q'.asIdeal.ResidueField = 0 := by
    rintro Q' rfl 𝔮 _ _
    letI : Algebra 𝔮.ResidueField q.ResidueField :=
      (Ideal.ResidueField.map _ _ (algebraMap Γ(W, W0) Γ(V, Ua)) Ideal.LiesOver.over).toAlgebra
    haveI := isAlgebraic_residueField_of_quasiFiniteAt 𝔮 q p
    exact trdeg_eq_zero
  have : (hUa.primeIdealOf ⟨ξ, hξ⟩).asIdeal.LiesOver (hW0.primeIdealOf ⟨g ξ, hUaW hξ⟩).asIdeal :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE W0 hW0 Ua hUa hUaW hξ).1).symm⟩
  have h0 := hzero _ hQ (hW0.primeIdealOf ⟨g ξ, hUaW hξ⟩).asIdeal
  rw [← htr] at h0
  letI : Algebra W.functionField V.functionField := g.functionFieldMap.hom.toAlgebra
  have hT1 : ((Cardinal.toNat (Algebra.trdeg W.functionField V.functionField) : ℕ) :
      WithBot ℕ∞) = 1 := by
    simpa using hT.symm
  rw [h0, ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hq1, hT1] at hxi
  -- Hence `g ξ` has coheight zero.
  have hc0 : Order.coheight (g ξ) = 0 := by
    have e : ((1 : ℕ∞) : WithBot ℕ∞) + ((0 : ℕ) : WithBot ℕ∞) =
        ((Order.coheight (g ξ) : ℕ∞) : WithBot ℕ∞) + ((1 : ℕ) : WithBot ℕ∞) := by
      simpa using hxi
    have e' : (1 : ℕ∞) = Order.coheight (g ξ) + 1 := by exact_mod_cast e
    induction hcg : Order.coheight (g ξ) using ENat.recTopCoe with
    | top => rw [hcg] at e'; simp at e'
    | coe n =>
      rw [hcg] at e'
      have : n + 1 = 1 := by exact_mod_cast e'.symm
      have hn : n = 0 := by omega
      rw [hn]; rfl
  refine ⟨eq_genericPoint_of_coheight_eq_zero hc0, ?_⟩
  -- The prime of `Γ(W₀)` under `q` has height zero, hence is zero.
  have hht : (hW0.primeIdealOf ⟨g ξ, hUaW hξ⟩).asIdeal.height = 0 := by
    have e1 : (hW0.primeIdealOf ⟨g ξ, hUaW hξ⟩).asIdeal.height =
        Order.coheight (show Spec Γ(W, W0) from hW0.primeIdealOf ⟨g ξ, hUaW hξ⟩) :=
      idealHeight_eq_coheight _ _
    rw [e1, ← coheight_eq_of_isOpenImmersion hW0.fromSpec, hW0.fromSpec_primeIdealOf]
    exact hc0
  rw [Ideal.height_eq_zero_iff_eq_bot] at hht
  rw [RingHom.injective_iff_ker_eq_bot, ← hht, ← IsAffineOpen.comap_primeIdealOf_appLE W0 hW0 Ua
    hUa hUaW hξ, hQ]
  ext s
  change Ideal.Quotient.mk q (algebraMap Γ(W, W0) Γ(V, Ua) s) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem]
  rfl

/-- **Step 4 from a Galois cover of a slice.** Let `W₀ ∋ z` and `U_a ⊆ g⁻¹(W₀)` be affine, with
`U_a` inside the domain of a local equation `ψ` of `D`, and let `q` be a prime of `Γ(U_a)` whose
point `ξ` has codimension one and lies on no component of `D`. Suppose `C` is a finite normal
`Γ(W₀)`-algebra whose primes over a common prime are conjugate, `x` a prime of `C` over `z` and
`θ : Γ(U_a)/q ⟶ C[1/r]` an injection over `Γ(W₀)` with `r ∉ x`. Then some positive multiple of
`B` has a local equation near `z`: `π^*B` agrees with `div(τ^*ψ)` near `x`, hence near every
point over `z` after a Galois conjugation, and the norm descends it to `Spec Γ(W₀)`. -/
private theorem exists_localEquation_of_galoisCover {d : ℕ} {K : Divisor V} {Δ : QDivisor V}
    {g : V ⟶ W} (h : IsLogEllipticFiberSpace k sV sW d K Δ g) [IsDominant g]
    (hfib : ∀ w : W, ∀ Y ∈ irreducibleComponents (g.base ⁻¹' {w}), topologicalKrullDim Y = 1)
    (D : Divisor V)
    (hDv : ∀ E : MMP.Mori.PrimeDivisor V, g E.genericPoint = genericPoint W → D.coeff E = 0)
    (B : QDivisor W)
    (hB : ∀ (E : MMP.Mori.PrimeDivisor V) (C : MMP.Mori.PrimeDivisor W),
      g E.genericPoint = C.genericPoint → ∀ t : W.functionField, W.ord t C.genericPoint = 1 →
        (D.coeff E : ℚ) = B C * V.ord (AlgebraicGeometry.functionFieldMap g t) E.genericPoint)
    {z : W} {W0 : W.Opens} (hW0 : IsAffineOpen W0) (hzW0 : z ∈ W0)
    {Ua : V.Opens} (hUa : IsAffineOpen Ua) (hUaW : Ua ≤ g ⁻¹ᵁ W0)
    (Uψ : V.Opens) (ψ : (RationalFunctions V)ˣ) (hψ : D.IsLocalEquation Uψ ψ) (hUaψ : Ua ≤ Uψ)
    [IsIntegrallyClosed Γ(W, W0)] [IsNoetherianRing Γ(W, W0)] [IsDomain Γ(W, W0)]
    (q : Ideal Γ(V, Ua)) [q.IsPrime]
    (hq1 : Order.coheight (hUa.fromSpec ⟨q, inferInstance⟩) = 1)
    (hqD : D.coeff (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hq1) = 0)
    (C : Type u) [CommRing C] [IsDomain C] [IsNoetherianRing C] [IsIntegrallyClosed C]
    [Algebra Γ(W, W0) C] [Module.Finite Γ(W, W0) C] [FaithfulSMul Γ(W, W0) C]
    (hgal : ∀ P Q : Ideal C, P.IsPrime → Q.IsPrime →
      P.comap (algebraMap Γ(W, W0) C) = Q.comap (algebraMap Γ(W, W0) C) →
        ∃ σ : C ≃ₐ[Γ(W, W0)] C, Q.comap (σ : C →+* C) = P)
    (r : C) (x : Ideal C) [x.IsPrime] (hr0 : r ≠ 0) (hrx : r ∉ x)
    (hxz : x.comap (algebraMap Γ(W, W0) C) = (hW0.primeIdealOf ⟨z, hzW0⟩).asIdeal)
    (θ : Γ(V, Ua) ⧸ q →+* Localization.Away r) (hθ : Function.Injective θ)
    (hθS : θ.comp ((Ideal.Quotient.mk q).comp (g.appLE W0 Ua hUaW).hom) =
      (algebraMap C (Localization.Away r)).comp (algebraMap Γ(W, W0) C)) :
    ∃ N : ℕ, 0 < N ∧ ∃ U : W.Opens, z ∈ U ∧ ∃ φ : (RationalFunctions W)ˣ,
      ∀ E : MMP.Mori.PrimeDivisor W, (E.support ∩ U).Nonempty → (N : ℚ) * B E = (E.ord φ : ℚ) := by
  classical
  -- The base `Z = Spec Γ(W₀)` and its open immersion into `W`.
  let ιW : Spec Γ(W, W0) ⟶ W := hW0.fromSpec
  haveI : IsNormal (Spec Γ(W, W0)) := isNormal_spec_of_isIntegrallyClosed Γ(W, W0)
  haveI : Nonempty (Spec Γ(W, W0)) := ⟨hW0.primeIdealOf ⟨z, hzW0⟩⟩
  haveI : IsDominant ιW := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion ιW
  -- The finite cover `T = Spec C`.
  let π : Spec (.of C) ⟶ Spec Γ(W, W0) := Spec.map (CommRingCat.ofHom (algebraMap Γ(W, W0) C))
  haveI : IsNormal (Spec (.of C)) := isNormal_spec_of_isIntegrallyClosed C
  haveI : IsFinite π := (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  haveI : Surjective π := ⟨fun y => by
    haveI : y.asIdeal.IsPrime := y.isPrime
    obtain ⟨⟨Q, hQ, hQy⟩⟩ := Ideal.nonempty_primesOver (S := C) y.asIdeal
    exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext ((Ideal.liesOver_iff _ _).mp hQy).symm⟩⟩
  have hcoh : ∀ y : Spec (.of C), Order.coheight y = 1 → Order.coheight (π y) = 1 :=
    fun y hy => (coheight_SpecMap_eq (S := Γ(W, W0)) (C := C) y).trans hy
  -- The basic open `T_r = Spec C[1/r]`.
  haveI : IsDomain (Localization.Away r) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hr0)
  haveI : IsIntegrallyClosed (Localization.Away r) :=
    isIntegrallyClosed_of_isLocalization (R := C) (S := Localization.Away r) (Submonoid.powers r)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hr0)
  haveI : IsNormal (Spec (.of (Localization.Away r))) :=
    isNormal_spec_of_isIntegrallyClosed (Localization.Away r)
  let ρ : Spec (.of (Localization.Away r)) ⟶ Spec (.of C) :=
    Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away r)))
  haveI : IsDominant ρ := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion ρ
  -- The map `τ : T_r ⟶ V` through the slice.
  let τ : Spec (.of (Localization.Away r)) ⟶ V :=
    Spec.map (CommRingCat.ofHom θ) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk q)) ≫
      hUa.fromSpec
  have e : (g.appLE W0 Ua hUaW ≫ CommRingCat.ofHom (Ideal.Quotient.mk q)) ≫
      CommRingCat.ofHom θ = CommRingCat.ofHom (algebraMap Γ(W, W0) C) ≫
        CommRingCat.ofHom (algebraMap C (Localization.Away r)) := CommRingCat.hom_ext hθS
  have hτ : τ ≫ g = ρ ≫ π ≫ ιW := by
    calc τ ≫ g = Spec.map (CommRingCat.ofHom θ) ≫ Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk q)) ≫ Spec.map (g.appLE W0 Ua hUaW) ≫ hW0.fromSpec := by
          simp only [τ, Category.assoc]
          rw [IsAffineOpen.SpecMap_appLE_fromSpec g hW0 hUa hUaW]
      _ = Spec.map ((g.appLE W0 Ua hUaW ≫ CommRingCat.ofHom (Ideal.Quotient.mk q)) ≫
          CommRingCat.ofHom θ) ≫ hW0.fromSpec := by
          simp only [Spec.map_comp, Category.assoc]
      _ = ρ ≫ π ≫ ιW := by
          rw [e]
          simp only [Spec.map_comp, Category.assoc]
          rfl
  have hτU : ∀ p, τ p ∈ Uψ := fun p => hUaψ (by
    change hUa.fromSpec _ ∈ Ua
    exact hUa.range_fromSpec.subset ⟨_, rfl⟩)
  have hgen : τ (genericPoint (Spec (.of (Localization.Away r)))) =
      hUa.fromSpec ⟨q, inferInstance⟩ := by
    have h0 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk q))
        (Spec.map (CommRingCat.ofHom θ) (genericPoint (Spec (.of (Localization.Away r))))) =
          (⟨q, inferInstance⟩ : PrimeSpectrum Γ(V, Ua)) := by
      rw [genericPoint_eq_bot_of_affine]
      apply PrimeSpectrum.ext
      change Ideal.comap (Ideal.Quotient.mk q) (Ideal.comap θ ⊥) = q
      rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot θ).mp hθ,
        ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    change hUa.fromSpec (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk q))
      (Spec.map (CommRingCat.ofHom θ) (genericPoint (Spec (.of (Localization.Away r)))))) = _
    rw [h0]
  have key : ∀ (ξ : V) (hξ : Order.coheight ξ = 1), ξ = hUa.fromSpec ⟨q, inferInstance⟩ →
      D.coeff (AlgebraicGeometry.PrimeDivisor.ofCoheightOne ξ hξ) = 0 := by
    rintro ξ hξ rfl; exact hqD
  have hξ1 : Order.coheight (τ (genericPoint (Spec (.of (Localization.Away r))))) = 1 :=
    hgen ▸ hq1
  have hξD := key _ hξ1 hgen
  -- The pull-backs of `B` to `Z` and `T`.
  let BZ : QDivisor (Spec Γ(W, W0)) := Finsupp.comapDomain
    (OpenWeilRestriction.primeDivisorMap ιW) B
    ((OpenWeilRestriction.primeDivisorMap_injective ιW).injOn)
  obtain ⟨B', hB'⟩ := exists_pullback_of_isFinite π BZ
  have hB'' : ∀ (E : MMP.Mori.PrimeDivisor (Spec Γ(W, W0)))
      (E' : MMP.Mori.PrimeDivisor (Spec (.of C))),
      π E'.genericPoint = E.genericPoint → ∀ t, (Spec Γ(W, W0)).ord t E.genericPoint = 1 →
        B' E' = ((Spec (.of C)).ord (AlgebraicGeometry.functionFieldMap π t) E'.genericPoint : ℚ) *
          B (OpenWeilRestriction.primeDivisorMap ιW E) := fun E E' hE t ht => by
    rw [hB' E E' hE t ht]
    rfl
  -- A local equation of `π^*B` on `ρ(T_r)`.
  obtain ⟨Ψ, hΨ⟩ := exists_localEquation_pullback h hfib D hDv B hB ιW π ρ τ hτ hcoh B' hB''
    Uψ ψ hψ hτU hξ1 hξD
  -- Galois conjugation spreads it over every point above `z`.
  set z' : Spec Γ(W, W0) := hW0.primeIdealOf ⟨z, hzW0⟩
  have hloc : ∀ y : Spec (.of C), π y = z' → ∃ O : (Spec (.of C)).Opens, y ∈ O ∧
      ∃ Ψ' : (RationalFunctions (Spec (.of C)))ˣ, ∀ E' : MMP.Mori.PrimeDivisor (Spec (.of C)),
        (E'.support ∩ O).Nonempty → B' E' = (E'.ord Ψ' : ℚ) := by
    intro y hy
    have hyx : x.comap (algebraMap Γ(W, W0) C) = y.asIdeal.comap (algebraMap Γ(W, W0) C) := by
      rw [hxz]
      exact (congrArg PrimeSpectrum.asIdeal hy).symm
    obtain ⟨σ, hσ⟩ := hgal x y.asIdeal inferInstance y.isPrime hyx
    let α : Spec (.of C) ≅ Spec (.of C) :=
      { hom := Spec.map (CommRingCat.ofHom (σ : C →+* C))
        inv := Spec.map (CommRingCat.ofHom (σ.symm : C →+* C))
        hom_inv_id := by
          rw [← Spec.map_comp, ← Spec.map_id]
          congr 1
          ext c
          exact σ.apply_symm_apply c
        inv_hom_id := by
          rw [← Spec.map_comp, ← Spec.map_id]
          congr 1
          ext c
          exact σ.symm_apply_apply c }
    have hα : α.hom ≫ π = π := by
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp]
      congr 1
      ext c
      exact σ.commutes c
    have hαy : α.hom y ∈ ρ.opensRange := by
      erw [Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of C) r]
      have : α.hom y = ⟨x, inferInstance⟩ := PrimeSpectrum.ext hσ
      rw [this]
      exact hrx
    obtain ⟨Ψ', hΨ'⟩ := exists_localEquation_of_iso π hcoh BZ B' hB' α hα ρ.opensRange Ψ hΨ
    exact ⟨α.hom ⁻¹ᵁ ρ.opensRange, hαy, Ψ', hΨ'⟩
  -- Descent along `π` and transport to `W`.
  obtain ⟨N, hN, U, hzU, φ, hφ⟩ := exists_localEquation_of_isFinite π BZ B' hB' z' hloc
  obtain ⟨φ', hφ'⟩ := exists_localEquation_of_isOpenImmersion ιW B N U φ fun E hE => by
    rw [← hφ E hE]
    rfl
  refine ⟨N, hN, ιW ''ᵁ U, ?_, φ', hφ'⟩
  exact ⟨z', hzU, hW0.fromSpec_primeIdealOf ⟨z, hzW0⟩⟩

/-- **Step 4, at a closed point.** Near every closed point `z` of `W`, some positive multiple of
`B` has a local equation. -/
private theorem exists_localEquation_of_isClosed [CharZero k] {d : ℕ} {K : Divisor V}
    {Δ : QDivisor V} {g : V ⟶ W} (h : IsLogEllipticFiberSpace k sV sW d K Δ g) [IsDominant g]
    (hfib : ∀ w : W, ∀ Y ∈ irreducibleComponents (g.base ⁻¹' {w}), topologicalKrullDim Y = 1)
    (D : Divisor V) (hDc : D.IsCartier)
    (hDv : ∀ E : MMP.Mori.PrimeDivisor V, g E.genericPoint = genericPoint W → D.coeff E = 0)
    (B : QDivisor W)
    (hB : ∀ (E : MMP.Mori.PrimeDivisor V) (C : MMP.Mori.PrimeDivisor W),
      g E.genericPoint = C.genericPoint → ∀ t : W.functionField, W.ord t C.genericPoint = 1 →
        (D.coeff E : ℚ) = B C * V.ord (AlgebraicGeometry.functionFieldMap g t) E.genericPoint)
    {z : W} (hz : IsClosed ({z} : Set W)) :
    ∃ N : ℕ, 0 < N ∧ ∃ U : W.Opens, z ∈ U ∧ ∃ φ : (RationalFunctions W)ˣ,
      ∀ E : MMP.Mori.PrimeDivisor W, (E.support ∩ U).Nonempty → (N : ℚ) * B E = (E.ord φ : ℚ) := by
  classical
  haveI := h.isContraction.isProper
  haveI := h.isContraction.isVariety_source.toLocallyOfFiniteType
  haveI := h.isContraction.isVariety_target.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType g :=
    MMP.Flips.locallyOfFiniteType_of_comp_eq sV sW g h.isContraction.comp_eq
  -- If `z` is the generic point, `W` is a point and has no prime divisors.
  by_cases hzη : z = genericPoint W
  · refine ⟨1, one_pos, ⊤, trivial, 1, fun E _ => ?_⟩
    exfalso
    have huniv : ∀ w : W, w = z := fun w => by
      have : w ∈ closure ({z} : Set W) := by
        rw [hzη, (genericPoint_spec W).def]; trivial
      rwa [hz.closure_eq] at this
    have h1 := E.coheight_genericPoint
    rw [Order.coheight_eq_zero.mpr fun b _ => by rw [huniv b, huniv E.genericPoint]] at h1
    exact zero_ne_one h1
  -- An affine neighbourhood `W₀` of `z` and a closed point `x` over `z`.
  obtain ⟨W0, hW0, hzW0, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show z ∈ (⊤ : W.Opens) from trivial)
  haveI : JacobsonSpace V := LocallyOfFiniteType.jacobsonSpace sV
  have hsurj : Function.Surjective g := by
    have hcl : IsClosed (Set.range g) := g.isClosedMap.isClosed_range
    have hd : Dense (Set.range g) := g.denseRange
    rw [← Set.range_eq_univ, ← hcl.closure_eq, hd.closure_eq]
  have hF : IsClosed (g.base ⁻¹' {z}) := hz.preimage g.continuous
  obtain ⟨x, hxF, hxc⟩ := nonempty_inter_closedPoints
    (Z := g.base ⁻¹' {z}) (hsurj z) hF.isLocallyClosed
  have hxz : g x = z := hxF
  have hxc' : IsClosed ({x} : Set V) := hxc
  obtain ⟨Ux, hxUx, ψ, hψ⟩ := hDc x
  obtain ⟨Ua, hUa, hxUa, hUaU⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ g ⁻¹ᵁ W0 ⊓ Ux from ⟨by change g x ∈ W0; rw [hxz]; exact hzW0, hxUx⟩)
  have hUaW : Ua ≤ g ⁻¹ᵁ W0 := fun y hy => (hUaU hy).1
  have hUaψ : Ua ≤ Ux := fun y hy => (hUaU hy).2
  -- The rings.
  haveI : Nonempty Ua := ⟨⟨x, hxUa⟩⟩
  haveI : Nonempty W0 := ⟨⟨z, hzW0⟩⟩
  haveI : IsDomain Γ(V, Ua) := IsIntegral.component_integral Ua
  haveI : IsDomain Γ(W, W0) := IsIntegral.component_integral W0
  haveI : IsNoetherianRing Γ(V, Ua) := IsLocallyNoetherian.component_noetherian ⟨Ua, hUa⟩
  haveI : IsNoetherianRing Γ(W, W0) := IsLocallyNoetherian.component_noetherian ⟨W0, hW0⟩
  haveI : IsIntegrallyClosed Γ(W, W0) :=
    (isNormal_iff_forall_affineOpen_normal W).mp inferInstance ⟨W0, hW0⟩ inferInstance
  haveI : CharZero Γ(W, W0) :=
    charZero_of_injective_ringHom (f := ((Scheme.ΓSpecIso (.of k)).inv ≫
      sW.appLE ⊤ W0 (by simp)).hom) (RingHom.injective _)
  letI : Algebra Γ(W, W0) Γ(V, Ua) := (g.appLE W0 Ua hUaW).hom.toAlgebra
  haveI : Algebra.FiniteType Γ(W, W0) Γ(V, Ua) := g.finiteType_appLE hW0 hUa hUaW
  -- The maximal ideal of `x` and the primes to avoid.
  set m := hUa.primeIdealOf ⟨x, hxUa⟩ with hmdef
  haveI hmax : m.asIdeal.IsMaximal := hUa.primeIdealOf_isMaximal_of_isClosed _ hxc'
  have hfx : hUa.fromSpec m = x := hUa.fromSpec_primeIdealOf ⟨x, hxUa⟩
  have hinjS : Function.Injective hUa.fromSpec := hUa.fromSpec.isOpenEmbedding.injective
  set Fz : Set V := g.base ⁻¹' {z}
  set Ξfib : Set V := {y | ∃ hy : y ∈ Fz, ∃ Y ∈ irreducibleComponents Fz,
    IsGenericPoint (⟨y, hy⟩ : Fz) Y}
  have hΞfib : Ξfib.Finite := by
    haveI : IsNoetherian V := {}
    have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := Fz)
    refine (hfin.biUnion fun Y _ => (Set.Subsingleton.finite (s := Subtype.val ''
      {p : Fz | IsGenericPoint p Y}) ?_)).subset ?_
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact congrArg Subtype.val (ha.eq hb)
    · rintro y ⟨hy, Y, hY, hgen⟩
      exact Set.mem_iUnion₂.mpr ⟨Y, hY, ⟨y, hy⟩, hgen, rfl⟩
  set ΞD : Set V := (fun E : MMP.Mori.PrimeDivisor V => E.genericPoint) '' (D.support : Set _)
  have hΞD : ΞD.Finite := D.support.finite_toSet.image _
  set Ξpts : Set V := (Ξfib ∪ ΞD) \ {x}
  have hΞpts : Ξpts.Finite := (hΞfib.union hΞD).diff
  set Ξsp : Set (PrimeSpectrum Γ(V, Ua)) := hUa.fromSpec ⁻¹' Ξpts
  have hΞsp : Ξsp.Finite := hΞpts.preimage hinjS.injOn
  set Ξ : Finset (Ideal Γ(V, Ua)) := hΞsp.toFinset.image PrimeSpectrum.asIdeal
  have hmemΞ : ∀ 𝔭 : PrimeSpectrum Γ(V, Ua), hUa.fromSpec 𝔭 ∈ Ξpts → 𝔭.asIdeal ∈ Ξ :=
    fun 𝔭 h𝔭 => Finset.mem_image.mpr ⟨𝔭, hΞsp.mem_toFinset.mpr h𝔭, rfl⟩
  have hΞprime : ∀ 𝔭 ∈ Ξ, 𝔭.IsPrime := by
    intro 𝔭 h𝔭
    obtain ⟨P, -, rfl⟩ := Finset.mem_image.mp h𝔭
    exact P.isPrime
  have hmΞ : m.asIdeal ∉ Ξ := by
    intro hm
    obtain ⟨P, hP, hPm⟩ := Finset.mem_image.mp hm
    have hPm' : P = m := PrimeSpectrum.ext hPm
    have := (hΞsp.mem_toFinset.mp hP).2
    exact this (by rw [hPm', hfx]; rfl)
  have hm0 : m.asIdeal ≠ ⊥ := by
    intro hm0
    have hηU : genericPoint V ∈ Ua :=
      ((genericPoint_spec V).mem_open_set_iff Ua.isOpen).mpr ⟨x, trivial, hxUa⟩
    have he : hUa.primeIdealOf ⟨genericPoint V, hηU⟩ = m := PrimeSpectrum.ext
      (hmax.eq_of_le (hUa.primeIdealOf _).isPrime.ne_top (hm0 ▸ bot_le)).symm
    have hηx : genericPoint V = x := by
      have := hUa.fromSpec_primeIdealOf ⟨genericPoint V, hηU⟩
      rw [he, hfx] at this
      exact this.symm
    apply hzη
    rw [← hxz, ← hηx, map_genericPoint_of_isDominant]
  have hgen : ∀ 𝔭 : Ideal Γ(V, Ua), 𝔭.IsPrime → 𝔭 ≤ m.asIdeal →
      𝔭.comap (algebraMap Γ(W, W0) Γ(V, Ua)) = m.asIdeal.comap (algebraMap Γ(W, W0) Γ(V, Ua)) →
        𝔭 ≠ m.asIdeal → 𝔭 ∈ Ξ := by
    intro 𝔭 h𝔭 h𝔭m h𝔭c hne
    apply hmemΞ ⟨𝔭, h𝔭⟩
    set y := hUa.fromSpec ⟨𝔭, h𝔭⟩
    have hyU : y ∈ Ua := hUa.range_fromSpec.subset ⟨_, rfl⟩
    have hpy : hUa.primeIdealOf ⟨y, hyU⟩ = ⟨𝔭, h𝔭⟩ := hUa.primeIdealOf_fromSpec _ hyU
    have hgy : g y = z := by
      have e1 := IsAffineOpen.comap_primeIdealOf_appLE W0 hW0 Ua hUa hUaW hyU
      have e2 := IsAffineOpen.comap_primeIdealOf_appLE W0 hW0 Ua hUa hUaW hxUa
      have e3 : hW0.primeIdealOf ⟨g y, hUaW hyU⟩ = hW0.primeIdealOf ⟨g x, hUaW hxUa⟩ := by
        rw [← e1, ← e2, hpy]
        exact PrimeSpectrum.ext h𝔭c
      have e4 := congrArg hW0.fromSpec e3
      rw [hW0.fromSpec_primeIdealOf, hW0.fromSpec_primeIdealOf] at e4
      exact e4.trans hxz
    have hyx : y ⤳ x := by
      rw [← hfx]
      exact ((PrimeSpectrum.le_iff_specializes ⟨𝔭, h𝔭⟩ m).mp h𝔭m).map hUa.fromSpec.continuous
    have hyx' : y ≠ x := fun e => hne (congrArg PrimeSpectrum.asIdeal (hinjS (e.trans hfx.symm)))
    exact ⟨Or.inl ⟨hgy, exists_isGenericPoint_of_specializes hF (hfib z) hxF hgy hyx hyx'⟩, hyx'⟩
  obtain ⟨q, hqp, hpp, hqm, hq1, hqΞ, hQF⟩ := exists_slice m.asIdeal hm0 Ξ hΞprime hmΞ hgen
  -- The point `ξ` of the slice.
  have hξ1 : Order.coheight (hUa.fromSpec ⟨q, hqp⟩) = 1 := by
    have e1 := idealHeight_eq_coheight Γ(V, Ua) ⟨q, hqp⟩
    have e0 := coheight_eq_of_isOpenImmersion (x := (⟨q, hqp⟩ : PrimeSpectrum Γ(V, Ua)))
      hUa.fromSpec
    exact e0.trans (e1.symm.trans hq1)
  obtain ⟨hgξ, hinj⟩ := map_eq_genericPoint_of_quasiFiniteAt h hW0 hUa hUaW q hξ1 _ hQF
  have hqD : D.coeff (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hξ1) = 0 := by
    by_contra hne
    apply hqΞ q (hmemΞ ⟨q, hqp⟩ ⟨Or.inr ⟨_, Finsupp.mem_support_iff.mpr hne,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _⟩, ?_⟩) le_rfl
    intro hξx
    apply hzη
    rw [← hxz, ← (Set.mem_singleton_iff.mp hξx), hgξ]
  -- The Galois cover.
  haveI : FaithfulSMul Γ(W, W0) (Γ(V, Ua) ⧸ q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have hfd := finiteDimensional_fractionRing_of_isAlgebraic
    (isAlgebraic_of_quasiFiniteAt (S := Γ(W, W0)) (m.asIdeal.map (Ideal.Quotient.mk q)))
  obtain ⟨C, _, _, _, _, _, _, _, hgal, r, xC, hxC, hr0, hrx, hxCz, θ, hθ, hθS⟩ :=
    exists_galoisCover (S := Γ(W, W0)) (R := Γ(V, Ua) ⧸ q) (m.asIdeal.map (Ideal.Quotient.mk q))
      hfd
  have hxz' : xC.comap (algebraMap Γ(W, W0) C) = (hW0.primeIdealOf ⟨z, hzW0⟩).asIdeal := by
    rw [hxCz, IsScalarTower.algebraMap_eq Γ(W, W0) Γ(V, Ua) (Γ(V, Ua) ⧸ q), ← Ideal.comap_comap,
      Ideal.Quotient.algebraMap_eq, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hqm]
    have e := congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE W0 hW0 Ua hUa hUaW hxUa)
    have e2 : (⟨g x, hUaW hxUa⟩ : W0) = ⟨z, hzW0⟩ := Subtype.ext hxz
    rw [e2] at e
    exact e
  have hθS' : θ.comp ((Ideal.Quotient.mk q).comp (g.appLE W0 Ua hUaW).hom) =
      (algebraMap C (Localization.Away r)).comp (algebraMap Γ(W, W0) C) := by
    rw [← IsScalarTower.algebraMap_eq, ← hθS]
    rfl
  exact exists_localEquation_of_galoisCover h hfib D hDv B hB hW0 hzW0 hUa hUaW Ux ψ hψ hUaψ q
    hξ1 hqD C hgal r xC hr0 hrx hxz' θ hθ hθS'

/-- **Step 5.** A Cartier divisor `B` on `W` pulls back to `D` if the coefficients of `D` are
those of `g^*B`, the components of `D` dominating `W` having coefficient zero. -/
private theorem isPullback_of_coeff_eq {g : V ⟶ W} [IsDominant g]
    (hg : ∀ E : MMP.Mori.PrimeDivisor V, g E.genericPoint = genericPoint W ∨
      ∃ C : MMP.Mori.PrimeDivisor W, g E.genericPoint = C.genericPoint)
    (D : Divisor V) (B : Divisor W) (hBc : B.IsCartier)
    (hDv : ∀ E : MMP.Mori.PrimeDivisor V, g E.genericPoint = genericPoint W → D.coeff E = 0)
    (hB : ∀ (E : MMP.Mori.PrimeDivisor V) (C : MMP.Mori.PrimeDivisor W),
      g E.genericPoint = C.genericPoint → ∀ t : W.functionField, W.ord t C.genericPoint = 1 →
        D.coeff E = B C * V.ord (AlgebraicGeometry.functionFieldMap g t) E.genericPoint) :
    ∃ hB : ∀ Z : irreducibleComponents V, g (componentGenericPoint V Z) ∉ B.supp,
      B.IsPullback g hB D := by
  classical
  obtain ⟨C', hC'⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant g hBc
  suffices hD : D = C' by subst hD; exact ⟨_, hC'⟩
  ext E
  rcases hg E with hη | ⟨C, hC⟩
  · -- Away from `Supp B`, `1` is a local equation of `B`.
    let U : W.Opens := ⟨(B.supp : Set W)ᶜ, (DivisorWithCoeffs.isClosed_supp B).isOpen_compl⟩
    have hψ : B.IsLocalEquation U 1 := by
      rintro P ⟨x, hxP, hxU⟩
      rw [PrimeDivisor.ord_one]
      by_contra hne
      exact hxU (DivisorWithCoeffs.support_subset_supp hne hxP)
    have hU : g E.genericPoint ∈ U := by
      have := MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp g B
        (pointComponent E.genericPoint)
      rw [MMP.Threefold.Mori.CanonUniq.componentGenericPoint_eq,
        map_genericPoint_of_isDominant] at this
      rwa [hη]
    rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hC' hψ E hU
      (pointComponent (g E.genericPoint)), hDv E hη, Units.val_one, map_one, map_one]
    have h1 := ord_algebraMap_eq_zero (X := V) (x := E.genericPoint) 1 isUnit_one
    rw [map_one] at h1
    exact h1.symm
  · obtain ⟨U, hU, ψ, hψ⟩ := hBc (g E.genericPoint)
    rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hC' hψ E hU
      (pointComponent (g E.genericPoint))]
    obtain ⟨t, ht⟩ := exists_ord_genericPoint_eq_one C
    have hCU : (C.support ∩ U).Nonempty := (C.genericPoint_mem_iff U).mp (hC ▸ hU)
    have hBC := hψ C hCU
    rw [MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord] at hBC
    have hZ : pointComponent (g E.genericPoint) = C.component :=
      Subsingleton.elim (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents) _ _
    rw [hZ]
    have : IsDiscreteValuationRing (W.presheaf.stalk (g E.genericPoint)) := by
      rw [hC]; exact C.isDiscreteValuationRing_localRing
    have hf : MMP.Threefold.Mori.Helpers.evalFF C.component (ψ : RationalFunctions W) ≠ 0 :=
      (ψ.isUnit.map _).ne_zero
    rw [hB E C hC t ht, ord_functionFieldMap_eq_mul g E.genericPoint
      (hC ▸ C.coheight_genericPoint) hf (hC ▸ ht), hC, ← hBC]
    rfl

/-- The core of FA 15.12: for a Cartier multiple `M = n₀ (K_V + Δ_V)`, some multiple `m M` is
linearly equivalent to the pull-back of a Cartier divisor on `W`. -/
private theorem exists_isPullback [CharZero k] {d : ℕ} {K : Divisor V}
    {Δ : QDivisor V} {g : V ⟶ W} (h : IsLogEllipticFiberSpace k sV sW d K Δ g) [IsDominant g]
    (hfib : ∀ w : W, ∀ Y ∈ irreducibleComponents (g.base ⁻¹' {w}), topologicalKrullDim Y = 1)
    (hnef :
      haveI := h.isContraction.isVariety_source.toQuasiCompact
      (Divisor.toQDivisor K + Δ).IsNef k sV)
    {n₀ : ℕ} (hn₀ : 0 < n₀) {M : Divisor V}
    (hM : Divisor.toQDivisor M = (n₀ : ℤ) • (Divisor.toQDivisor K + Δ)) (hMc : M.IsCartier) :
    ∃ m : ℕ, 0 < m ∧ ∃ (φ : (RationalFunctions V)ˣ) (B : Divisor W) (_ : B.IsCartier)
      (hB : ∀ Z : irreducibleComponents V, g (componentGenericPoint V Z) ∉ B.supp),
      B.IsPullback g hB ((m : ℤ) • M + MMP.Mori.principalDivisor φ) := by
  classical
  haveI := h.isContraction.isVariety_source.toQuasiCompact
  obtain ⟨φ, hφ⟩ := exists_coeff_principalDivisor_add_eq_zero h hn₀ hM hMc
  set D := M + MMP.Mori.principalDivisor φ with hDdef
  have hDc : D.IsCartier := hMc.add (Divisor.isCartier_principalDivisor φ)
  -- `D` has nonnegative degree on contracted curves: it is linearly equivalent to `n₀ L`.
  have hDdeg : ∀ Γ : ProperCurve sV, Γ.IsContractedBy g →
      0 ≤ D.degreeOn k sV Γ.ι Γ.dim_le hDc := by
    intro Γ _
    obtain ⟨hLq, hL⟩ := hnef
    have h1 := hL Γ.scheme Γ.ι Γ.dim_eq
    rw [QDivisor.intersectionNumber_eq_of_smul k sV Γ.ι Γ.dim_le _ hLq hn₀ M hMc hM] at h1
    have h2 : (MMP.Mori.principalDivisor φ).degreeOn k sV Γ.ι Γ.dim_le
        (Divisor.isCartier_principalDivisor φ) = 0 :=
      Divisor.degreeOn_eq_zero_of_linearlyEquivalent sV Γ.ι Γ.dim_le _ ⟨φ, by simp⟩
    rw [Divisor.degreeOn_add k sV Γ.ι Γ.dim_le M _ hMc (Divisor.isCartier_principalDivisor φ), h2,
      add_zero]
    have hn : (0 : ℚ) < n₀ := by exact_mod_cast hn₀
    rcases div_nonneg_iff.mp h1 with ⟨h3, -⟩ | ⟨-, h3⟩
    · exact_mod_cast h3
    · exact absurd h3 (not_le.mpr hn)
  choose r hr using fun C => exists_coeff_eq_mul_ord h hfib D hDc hDdeg hφ C
  -- The `ℚ`-divisor `B = ∑ r_C C`, keeping only the prime divisors under components of `D`.
  let c : MMP.Mori.PrimeDivisor W → ℚ := fun C =>
    if ∃ E : MMP.Mori.PrimeDivisor V, D.coeff E ≠ 0 ∧ g E.genericPoint = C.genericPoint
    then r C else 0
  have hcfin : {C | c C ≠ 0}.Finite := by
    refine ((D.support.finite_toSet.image fun E => g E.genericPoint).preimage
      (AlgebraicGeometry.PrimeDivisor.genericPoint_injective.injOn)).subset ?_
    intro C hC
    by_contra hC'
    refine hC (if_neg ?_)
    rintro ⟨E, hE, hEC⟩
    exact hC' ⟨E, Finsupp.mem_support_iff.mpr hE, hEC⟩
  let B : QDivisor W := Finsupp.ofSupportFinite c hcfin
  have hB : ∀ (E : MMP.Mori.PrimeDivisor V) (C : MMP.Mori.PrimeDivisor W),
      g E.genericPoint = C.genericPoint → ∀ t : W.functionField, W.ord t C.genericPoint = 1 →
        (D.coeff E : ℚ) = B C * V.ord (AlgebraicGeometry.functionFieldMap g t)
          E.genericPoint := by
    intro E C hEC t ht
    change (D.coeff E : ℚ) = c C * _
    by_cases hex : ∃ E : MMP.Mori.PrimeDivisor V, D.coeff E ≠ 0 ∧
        g E.genericPoint = C.genericPoint
    · rw [show c C = r C from if_pos hex]
      exact hr C E hEC t ht
    · rw [show c C = 0 from if_neg hex, zero_mul]
      by_contra hne
      exact hex ⟨E, fun h0 => hne (by rw [h0]; simp), hEC⟩
  obtain ⟨m, hm, Bm, hBm, hBmc⟩ :=
    (isQCartier_of_forall_isClosed B fun _ hz =>
      exists_localEquation_of_isClosed h hfib D hDc hφ B hB hz).exists_pos
  refine ⟨m, hm, φ ^ m, Bm, hBmc, ?_⟩
  have hBm' : ∀ (E : MMP.Mori.PrimeDivisor V) (C : MMP.Mori.PrimeDivisor W),
      g E.genericPoint = C.genericPoint → ∀ t : W.functionField, W.ord t C.genericPoint = 1 →
        ((m : ℤ) • D).coeff E =
          Bm C * V.ord (AlgebraicGeometry.functionFieldMap g t) E.genericPoint := by
    intro E C hEC t ht
    have h1 := hB E C hEC t ht
    have h2 : (Bm C : ℚ) = m * B C := by
      have := congrArg (fun F : QDivisor W => F.coeff C) hBm
      simp only [DivisorWithCoeffs.coeff, Finsupp.smul_apply, zsmul_eq_mul,
        Int.cast_natCast] at this
      exact this
    have h3 : ((((m : ℤ) • D).coeff E : ℤ) : ℚ) =
        ((Bm C * V.ord (AlgebraicGeometry.functionFieldMap g t) E.genericPoint : ℤ) : ℚ) := by
      push_cast
      rw [DivisorWithCoeffs.coeff, Finsupp.smul_apply, smul_eq_mul, Int.cast_mul, h2,
        Int.cast_natCast]
      rw [← DivisorWithCoeffs.coeff, h1]
      ring
    exact_mod_cast h3
  have hDv' : ∀ E : MMP.Mori.PrimeDivisor V, g E.genericPoint = genericPoint W →
      ((m : ℤ) • D).coeff E = 0 := by
    intro E hE
    rw [DivisorWithCoeffs.coeff, Finsupp.smul_apply, ← DivisorWithCoeffs.coeff, hφ E hE,
      smul_zero]
  obtain ⟨hB', hpb⟩ := isPullback_of_coeff_eq (map_genericPoint_eq h hfib) ((m : ℤ) • D) Bm hBmc
    hDv' hBm'
  have heq : (m : ℤ) • D = (m : ℤ) • M + MMP.Mori.principalDivisor (φ ^ m) := by
    ext E
    simp [hDdef, smul_add, PrimeDivisor.ord_pow]
  rw [← heq]
  exact ⟨hB', hpb⟩

end

/-- Let `g : V ⟶ W` be a log elliptic fiber space over a field `k` of characteristic zero whose
fibers are equidimensional of dimension one. If `(V, Δ)` is log canonical and `K + Δ` is nef, then
for some positive integer `n` there is an integral divisor `N` with `N = n • (K + Δ)` and an
invertible sheaf `L` on `W` such that `𝒪_V(N) ≅ g^* L`. -/
theorem solution :
    ∀ {k : Type u} [inst : Field k] [inst_1 : CharZero k] {V W : Scheme.{u}}
      {sV : V ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)} [inst_2 : IsLocallyNoetherian V]
      [inst_3 : IsNormal V] {d : ℕ} {K : Divisor V} {Δ : QDivisor V} {g : V ⟶ W}
      (h : IsLogEllipticFiberSpace k sV sW d K Δ g),
      (∀ w : W, ∀ Y ∈ irreducibleComponents (g.base ⁻¹' {w}), topologicalKrullDim Y = 1) →
      (haveI := h.isContraction.isVariety_source.toIsIntegral
       haveI := h.isContraction.isVariety_source.toQuasiCompact
       haveI := QuasiCompact.compactSpace_of_compactSpace sV
       haveI := h.isContraction.isVariety_source.toLocallyOfFiniteType
       IsLogCanonical sV d K (QDivisor.toRDivisor Δ)) →
      (haveI := h.isContraction.isVariety_source.toQuasiCompact
       (Divisor.toQDivisor K + Δ).IsNef k sV) →
      ∃ n : ℕ, 0 < n ∧ ∃ N : Divisor V,
        Divisor.toQDivisor N = (n : ℤ) • (Divisor.toQDivisor K + Δ) ∧
        ∃ (L : W.Modules) (_ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L),
          Nonempty (N.divisorialSheaf ≅ (Scheme.Modules.pullback g).obj L) := by
  intro k _ _ V W sV sW _ _ d K Δ g h hfib _ hnef
  haveI := h.isContraction.isVariety_source.toIsIntegral
  haveI := h.isContraction.isVariety_target.toIsIntegral
  haveI := h.isContraction.isVariety_source.toQuasiCompact
  haveI := h.isContraction.isVariety_target.toQuasiCompact
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  haveI := h.isContraction.isVariety_target.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  haveI : IsDominant g := isDominant_of_forall_isIso_app g h.isContraction.isIso_app
  haveI : IsIso g.c := by
    haveI : ∀ U, IsIso (g.c.app U) := fun U => h.isContraction.isIso_app U.unop
    exact NatIso.isIso_of_isIso_app _
  haveI : IsNormal W := MMP.Mori.isNormal_of_isIso_c sW g h.isContraction.isVariety_target
    (by rw [h.isContraction.comp_eq]; exact h.isContraction.isVariety_source)
  obtain ⟨M, hM, hMc⟩ := QDivisor.isCartierDivisor_cartierIndex_smul h.isQCartier
  obtain ⟨m, hm, φ, B, hBc, hB, hpb⟩ :=
    exists_isPullback h hfib hnef (QDivisor.cartierIndex_pos h.isQCartier) hM hMc
  refine ⟨m * _, Nat.mul_pos hm (QDivisor.cartierIndex_pos h.isQCartier), (m : ℤ) • M, ?_,
    B.divisorialSheaf, hBc.isInvertibleModule_divisorialSheaf, ⟨?_⟩⟩
  · rw [map_zsmul, hM, smul_smul]
    push_cast
    rfl
  · exact Divisor.divisorialSheafMulIso φ⁻¹ (fun E => by simp) ≪≫
      hpb.divisorialSheafIso (hBc := hBc)

end MMP.FourfoldProofs.Fa15EquidimensionalLogEllipticPullbackProof

end

section

/-!
# Equidimensional log elliptic fiber spaces: the log canonical bundle is a pullback

Let `g : (V, Δ_V) ⟶ W` be a log elliptic fiber space all of whose fibers have pure dimension
one, with `(V, Δ_V)` log canonical and `K_V + Δ_V` nef. Then some positive multiple
`n (K_V + Δ_V)` is an integral divisor whose divisorial sheaf is the pullback of an invertible
sheaf on `W`.

## Main results

* `MMP.Flips.IsLogEllipticFiberSpace.exists_divisorialSheaf_iso_pullback`: FA Prop. 15.12.

## Implementation notes

Neither `V` nor `W` is assumed proper over `k`; only `g` is proper. Nefness is
`MMP.Mori.QDivisor.IsNef`, positivity on every closed curve of `V` that is proper over `k`.
"`g` has fibers of pure dimension one" says that every irreducible component of the subspace
`g⁻¹(w)` of `V`, for every point `w` of `W`, has dimension one. The ground field is any field of
characteristic zero.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 15.12
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Flips

open MMP.Mori

/-- **FA Prop. 15.12.** Let `g : (V, Δ_V) ⟶ W` be a log elliptic fiber space over a field `k` of
characteristic zero (`MMP.Flips.IsLogEllipticFiberSpace`), with `K_V` a canonical divisor of `V`
of dimension `d`. Assume that every fiber of `g` has pure dimension one, that `(V, Δ_V)` is log
canonical (`MMP.Flips.IsLogCanonical`) and that `K_V + Δ_V` is nef (`MMP.Mori.QDivisor.IsNef`).
Then there are an integer `n > 0` and an invertible sheaf `L` on `W` such that
`n (K_V + Δ_V)` is an integral divisor `N` with `𝒪_V(N) ≅ g^* L`. -/
@[mmp "prop_fa15_equidimensional_log_elliptic_pullback"]
public theorem IsLogEllipticFiberSpace.exists_divisorialSheaf_iso_pullback
    {k : Type u} [Field k] [CharZero k] {V W : Scheme.{u}} {sV : V ⟶ Spec (.of k)}
    {sW : W ⟶ Spec (.of k)} [IsLocallyNoetherian V] [IsNormal V] {d : ℕ} {K : Divisor V}
    {Δ : QDivisor V} {g : V ⟶ W} (h : IsLogEllipticFiberSpace k sV sW d K Δ g)
    (hfib : ∀ w : W, ∀ Y ∈ irreducibleComponents (g.base ⁻¹' {w}), topologicalKrullDim Y = 1)
    (hlc :
      haveI := h.isContraction.isVariety_source.toIsIntegral
      haveI := h.isContraction.isVariety_source.toQuasiCompact
      haveI := QuasiCompact.compactSpace_of_compactSpace sV
      haveI := h.isContraction.isVariety_source.toLocallyOfFiniteType
      IsLogCanonical sV d K (QDivisor.toRDivisor Δ))
    (hnef :
      haveI := h.isContraction.isVariety_source.toQuasiCompact
      (Divisor.toQDivisor K + Δ).IsNef k sV) :
    ∃ n : ℕ, 0 < n ∧ ∃ N : Divisor V, Divisor.toQDivisor N = (n : ℤ) • (Divisor.toQDivisor K + Δ) ∧
      ∃ (L : W.Modules) (_ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L),
        Nonempty (N.divisorialSheaf ≅ (Scheme.Modules.pullback g).obj L) :=
  MMP.FourfoldProofs.Fa15EquidimensionalLogEllipticPullbackProof.solution h hfib hlc hnef

end MMP.Flips

end
