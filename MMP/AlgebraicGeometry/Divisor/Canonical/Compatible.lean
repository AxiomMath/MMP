module

public import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
public import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
public import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison

/-!
# Compatible canonical divisors (KM 2.22, 2.26)

For a proper birational morphism `f : Y → X` of normal varieties of dimension `n` over a perfect
field and canonical divisors `K_X`, `K_Y` with `f_* K_Y = K_X`, there is a nonzero rational
`1`-canonical form `ω` with `K_X = div_X(ω)` and `K_Y = div_Y(f^*ω)`.

## Main results

* `MMP.Positivity.exists_divisorOfForm_eq_of_transformDivisor_eq`
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Positivity

open MMP.Mori

/-- The order of vanishing is invariant under a ring isomorphism `R ≃+* R'` of discrete valuation
rings, extended to a map `K → K'` of their fraction fields. -/
theorem ordFrac_map_of_ringEquiv {R R' K K' : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Field K] [Field K'] [Algebra R K] [IsFractionRing R K] [Algebra R' K'] [IsFractionRing R' K']
    (φ : R ≃+* R') (e : K →+* K') (he : ∀ r, e (algebraMap R K r) = algebraMap R' K' (φ r))
    (x : K) : Ring.ordFrac R' (e x) = Ring.ordFrac R x := by
  have h : ∀ r : R, Ring.ordFrac R' (algebraMap R' K' (φ r)) =
      Ring.ordFrac R (algebraMap R K r) := by
    intro r
    by_cases hr : r = 0
    · simp [hr]
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
    have hϖ' : Irreducible (φ ϖ) := (MulEquiv.irreducible_iff φ.toMulEquiv).mpr hϖ
    simp only [map_mul, map_pow]
    rw [Ring.ordFrac_of_isUnit (u.isUnit.map φ), Ring.ordFrac_of_isUnit u.isUnit,
      Ring.ordFrac_irreducible hϖ, Ring.ordFrac_irreducible hϖ']
  obtain ⟨a, s, -, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  rw [map_div₀, he, he, map_div₀, map_div₀, h, h]

section Order

variable {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-- The specialization map between the stalks at two equal points is an isomorphism. -/
theorem isIso_stalkSpecializes_of_eq {x x' : X} (h : x = x') (hsp : x ⤳ x') :
    IsIso (X.presheaf.stalkSpecializes hsp) := by
  rw [show X.presheaf.stalkSpecializes hsp = (X.presheaf.stalkCongr (Inseparable.of_eq h)).inv
    from rfl]
  infer_instance

/-- Pulling back along `f` the image of a stalk element at `x` in `k(X)` agrees with first
specializing it to `f y` and then applying `f^♯` at `y`. -/
theorem functionFieldMap_algebraMap_stalkSpecializes (f : Y ⟶ X) [IsDominant f] {x : X} {y : Y}
    (hsp : f y ⤳ x) (r : X.presheaf.stalk x) :
    functionFieldMap f (algebraMap _ X.functionField r) =
      algebraMap _ Y.functionField
        ((f.stalkMap y).hom ((X.presheaf.stalkSpecializes hsp).hom r)) := by
  rw [← functionFieldMap_algebraMap_stalk, algebraMap_stalkSpecializes]

/-- Let `E ⊆ Y`, `P ⊆ X` be prime divisors with `f(η_E) = η_P` and `f^♯ : 𝒪_{X,P} ⟶ 𝒪_{Y,E}` an
isomorphism. Then `v_E(f^*g) = v_P(g)` for every rational function `g` on `X`. -/
theorem ord_functionFieldMap_of_isIso (f : Y ⟶ X) [IsDominant f] (E : Mori.PrimeDivisor Y)
    (P : Mori.PrimeDivisor X) (heq : f E.genericPoint = P.genericPoint)
    [IsIso (f.stalkMap E.genericPoint)] (g : X.functionField) :
    Y.ord (functionFieldMap f g) E.genericPoint = X.ord g P.genericPoint := by
  have := P.isDiscreteValuationRing_localRing
  have := E.isDiscreteValuationRing_localRing
  have hsp : f E.genericPoint ⤳ P.genericPoint := heq ▸ specializes_rfl
  let φ : X.presheaf.stalk P.genericPoint ⟶ Y.presheaf.stalk E.genericPoint :=
    X.presheaf.stalkSpecializes hsp ≫ f.stalkMap E.genericPoint
  have := isIso_stalkSpecializes_of_eq heq hsp
  have : IsIso φ := by infer_instance
  rw [Scheme.ord_eq_ordHom_of_coheight_eq_one E.coheight_genericPoint,
    Scheme.ord_eq_ordHom_of_coheight_eq_one P.coheight_genericPoint]
  congr 2
  exact ordFrac_map_of_ringEquiv (asIso φ).commRingCatIsoToRingEquiv (functionFieldMap f)
    (functionFieldMap_algebraMap_stalkSpecializes f hsp) g

/-- **The order of a pulled-back form along a strict transform.** Let `f : Y → X` be a dominant
morphism of normal integral schemes over a perfect field `k`, with `f^* : k(X) → k(Y)` bijective,
and `E ⊆ Y`, `P ⊆ X` prime divisors with `f(η_E) = η_P` at which `f^♯ : 𝒪_{X,P} ⟶ 𝒪_{Y,E}` is an
isomorphism. Then `ord_E(f^*τ) = ord_P(τ)` for every rational `m`-canonical form `τ` on `X`. -/
theorem ordForm_pullbackRationalPluriForms_of_isIso {k : Type u} [Field k] [PerfectField k]
    {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX] (f : Y ⟶ X) [IsDominant f]
    (hbij : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    (E : Mori.PrimeDivisor Y) (P : Mori.PrimeDivisor X) (heq : f E.genericPoint = P.genericPoint)
    [IsIso (f.stalkMap E.genericPoint)] {m : ℤ} (τ : RationalPluriForms sX d m) :
    E.ordForm (pullbackRationalPluriForms sX f τ) = P.ordForm τ := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  let := stalkAlgebra sX P.genericPoint
  have := isScalarTower_stalk_functionField sX P.genericPoint
  let := stalkAlgebra (f ≫ sX) E.genericPoint
  have := isScalarTower_stalk_functionField (f ≫ sX) E.genericPoint
  have hsp : f E.genericPoint ⤳ P.genericPoint := heq ▸ specializes_rfl
  let φ : X.presheaf.stalk P.genericPoint ⟶ Y.presheaf.stalk E.genericPoint :=
    X.presheaf.stalkSpecializes hsp ≫ f.stalkMap E.genericPoint
  have := isIso_stalkSpecializes_of_eq heq hsp
  have hφ : IsIso φ := by infer_instance
  let : Algebra P.localRing E.localRing := φ.hom.toAlgebra
  let : Algebra P.localRing Y.functionField :=
    ((algebraMap X.functionField Y.functionField).comp
      (algebraMap P.localRing X.functionField)).toAlgebra
  have : IsScalarTower P.localRing X.functionField Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower P.localRing E.localRing Y.functionField :=
    IsScalarTower.of_algebraMap_eq (functionFieldMap_algebraMap_stalkSpecializes f hsp)
  have : IsScalarTower k P.localRing E.localRing := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    have h : (Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ sX).appTop ≫
          Y.presheaf.germ ⊤ E.genericPoint (Opens.mem_top _) =
        ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
          X.presheaf.germ ⊤ P.genericPoint (Opens.mem_top _)) ≫ φ := by
      simp only [φ, Scheme.Hom.comp_appTop, Category.assoc,
        TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]
      rfl
    exact congrArg CommRingCat.Hom.hom h
  have : IsScalarTower k P.localRing Y.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    rw [IsScalarTower.algebraMap_apply k X.functionField Y.functionField,
      IsScalarTower.algebraMap_apply k P.localRing X.functionField]
    rfl
  have := P.isDiscreteValuationRing_localRing
  obtain ⟨σ, hσ, h0⟩ := P.exists_topForms_generator hd
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
  have hgen := MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω
    (span_singleton_topFormsMap (nonZeroDivisors P.localRing) hσ) h0
  have hbijA : Function.Bijective (algebraMap P.localRing E.localRing) :=
    (ConcreteCategory.isIso_iff_bijective φ).mp hφ
  exact MMP.Threefold.Mori.Helpers.ordAt_pullbackForms_eq (k := k) hbijA
    P.ord_mul_of_ne_zero (fun _ ha => P.ord_algebraMap_of_isUnit ha)
    E.ord_mul_of_ne_zero (fun _ ha => E.ord_algebraMap_of_isUnit ha)
    (fun x => ord_functionFieldMap_of_isIso f E P heq x) hσ hgen τ

end Order

variable {k : Type u} [Field k] [PerfectField k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]

/-- **Compatible canonical divisors** (implicit in KM 2.22, 2.26). Let `f : Y → X` be a proper
birational morphism of normal varieties of dimension `n`, and `K_X`, `K_Y` canonical divisors with
`f_* K_Y = K_X`. Then there is a nonzero rational `1`-canonical form `ω` with `K_X = div_X(ω)` and
`K_Y = div_Y(f^*ω)`. -/
@[mmp "lem_km2b_compatible_canonical_divisors"]
theorem exists_divisorOfForm_eq_of_transformDivisor_eq (hX : IsNormalVariety k sX) {f : Y ⟶ X}
    [LocallyOfFiniteType (f ≫ sX)] (hY : IsNormalVariety k (f ≫ sX)) [IsProper f]
    (hf : IsBirationalMorphism f) [IsDominant f] {n : ℕ} {KX : Divisor X} {KY : Divisor Y}
    (hKX : KX.IsCanonicalDivisor sX n) (hKY : KY.IsCanonicalDivisor (f ≫ sX) n)
    (hpush : RationalMap.transformDivisor (X := Y) f.toRationalMap KY = KX) :
    ∃ ω : RationalPluriForms sX n 1, ω ≠ 0 ∧ divisorOfForm ω = KX ∧
      divisorOfForm (pullbackRationalPluriForms sX f ω) = KY := by
  have hbij := hf.functionFieldMap_bijective
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX)
    hKX.topologicalKrullDim_eq
  obtain ⟨ω₁, hω₁0, hω₁⟩ := IsCanonicalDivisor.exists_ordForm_eq hY hKY
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
  obtain ⟨g, hg⟩ := hbij.2
    ((ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) 1).repr ω₁ ())
  let τ : RationalPluriForms sX n 1 :=
    g • ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) 1 ()
  have hpull : pullbackRationalPluriForms sX f τ = ω₁ := by
    change pullbackForms (K := X.functionField) (K' := Y.functionField) 1 τ = ω₁
    rw [pullbackForms_eq hω, pullbackFormsAlong]
    simp only [τ, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_eq_same, smul_eq_mul, mul_one]
    change functionFieldMap f g • _ = ω₁
    rw [hg]
    exact basis_unit_repr_smul _ ω₁
  refine ⟨τ, fun h0 => hω₁0 ?_, Finsupp.ext fun P => ?_, Finsupp.ext fun Γ => ?_⟩
  · rw [← hpull, h0]
    change pullbackForms (K := X.functionField) (K' := Y.functionField) 1 0 = 0
    rw [pullbackForms_eq hω, pullbackFormsAlong]
    simp
  · obtain ⟨E, heq, hiso, htr⟩ := exists_isIso_stalkMap_forall_transformDivisor_apply hX hY hf P
    rw [← hpush, htr]
    change P.ordForm τ = KY.coeff E
    rw [← ordForm_pullbackRationalPluriForms_of_isIso f hbij hd E P heq τ, hpull, hω₁]
  · change Γ.ordForm _ = KY.coeff Γ
    rw [hpull, hω₁]

end MMP.Positivity
