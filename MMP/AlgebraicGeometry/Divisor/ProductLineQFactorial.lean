module
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.Analysis.Complex.CauchyOsgoodLaurent
public import MMP.AlgebraicGeometry.Morphisms.ProductWithLine

/-!
# Products with a line preserve `ℚ`-factoriality

Let `Y` be a normal variety over a field `k` and `L` the affine line `𝔸¹_k` or the projective
line `ℙ¹_k`, with first projection `pr : Y × L ⟶ Y`. For a Weil divisor `D₀ = ∑ nₖ Zₖ` on `Y`,
write `pr^* D₀ = ∑ nₖ (Zₖ × L)`, where `Zₖ × L = pr⁻¹(Zₖ)`. If `m D₀` is Cartier, then so is
`m pr^* D₀`, and it is the pull-back of the Cartier divisor `m D₀` along `pr`: its local equations
are the pull-backs of local equations of `m D₀`. Consequently, if `Y` is `ℚ`-factorial, so is
`Y × L`.

## Main results

* `MMP.Fourfold.isQFactorial_pullback_line`: the two statements above.

## Implementation notes

* As for `MMP.Fourfold.product_line_basic`, the line is any `k`-scheme `L` with a
  `k`-isomorphism to `AlgebraicGeometry.projectiveLine k` or to `𝔸(PUnit; Spec k)`, and
  `Y × L` is the pull-back of the two structure morphisms, a `k`-scheme through `pr ≫ s_Y`.
* The divisor `pr^* D₀` is characterised by its coefficients: the coefficient of a prime divisor
  `E` of `Y × L` is that of `Γ` in `D₀` when the support of `E` is `pr⁻¹(Γ)`, and `0` when `E` is
  of no such form (it dominates `Y`). "Local equations are the pull-backs" is
  `MMP.Mori.Divisor.IsPullback`.
* The normality and local Noetherianity of `Y` and of `Y × L`, needed to speak of their Weil and
  Cartier divisors, are derived in the statement from the hypothesis that `Y` is a normal variety
  (using `MMP.Fourfold.product_line_basic` for `Y × L`).
* The source works over `ℂ`; the statements hold over an arbitrary field `k`.
-/

open CategoryTheory AlgebraicGeometry Limits
open scoped TensorProduct

universe u

namespace MMP.Fourfold

open MMP MMP.Mori

/-! ### Charts of the line and of the product -/

/-- The affine line `𝔸(PUnit; Spec k)` is `Spec k[X]` over `k`. -/
private theorem exists_iso_affineLine (k : Type u) [Field k] :
    ∃ c : Spec (.of (Polynomial k)) ≅ 𝔸(PUnit.{u + 1}; Spec (.of k)),
      c.hom ≫ (𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k)) =
        Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) := by
  let φ : MvPolynomial PUnit.{u + 1} k ≃+* Polynomial k :=
    (MvPolynomial.pUnitAlgEquiv k).toRingEquiv
  let c : Spec (.of (Polynomial k)) ⟶ 𝔸(PUnit.{u + 1}; Spec (.of k)) :=
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (AffineSpace.SpecIso PUnit.{u + 1} (.of k)).inv
  have : IsIso (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
    inferInstanceAs (IsIso (Spec.map (φ.toCommRingCatIso.hom)))
  refine ⟨asIso c, ?_⟩
  change c ≫ _ = _
  simp only [c, Category.assoc, AffineSpace.SpecIso_inv_over]
  rw [← Spec.map_comp]
  congr 1
  ext x
  simp [φ]

/-- Every point of `L` lies in an open chart `Spec k[X] ⟶ L` over `k`. -/
private theorem exists_lineChart {k : Type u} [Field k] {L : Scheme.{u}}
    (sL : L ⟶ Spec (.of k))
    (hL : (∃ e : L ≅ projectiveLine k, e.hom ≫ (projectiveLine k ↘ Spec (.of k)) = sL) ∨
      ∃ e : L ≅ 𝔸(PUnit.{u + 1}; Spec (.of k)),
        e.hom ≫ (𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k)) = sL) (l : L) :
    ∃ j : Spec (.of (Polynomial k)) ⟶ L, IsOpenImmersion j ∧
      j ≫ sL = Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) ∧
      l ∈ Set.range j := by
  rcases hL with ⟨e, rfl⟩ | ⟨e, rfl⟩
  · obtain ⟨i, y, hy⟩ := (projectiveLineGluingData k).ι_jointly_surjective (e.hom l)
    have key : ∀ j : Spec (.of (Polynomial k)) ⟶ projectiveLine k, IsOpenImmersion j →
        j ≫ (projectiveLine k ↘ Spec (.of k)) =
          Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) →
        e.hom l ∈ Set.range j →
        ∃ j : Spec (.of (Polynomial k)) ⟶ L, IsOpenImmersion j ∧
          j ≫ e.hom ≫ (projectiveLine k ↘ Spec (.of k)) =
            Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) ∧
          l ∈ Set.range j := by
      rintro j hj hjs ⟨y, hy⟩
      refine ⟨j ≫ e.inv, inferInstance, by simpa using hjs, ⟨y, ?_⟩⟩
      rw [Scheme.Hom.comp_apply, hy, ← Scheme.Hom.comp_apply, e.hom_inv_id]
      rfl
    obtain ⟨⟨_ | _⟩⟩ := i
    · exact key (projectiveLineXChart k) inferInstance
        (projectiveLineXChart_comp_structureMorphism k) ⟨y, hy⟩
    · exact key (projectiveLineYChart k) inferInstance
        (projectiveLineYChart_comp_structureMorphism k) ⟨y, hy⟩
  · obtain ⟨c, hc⟩ := exists_iso_affineLine k
    refine ⟨c.hom ≫ e.inv, inferInstance, by simpa using hc, ?_⟩
    exact (inferInstance : Surjective (c.hom ≫ e.inv)).surj l

/-- An open immersion `Ψ : Spec R ⟶ X` lying over `Spec α : Spec R ⟶ U` identifies `R` with the
sections over its range, compatibly with `α`. -/
private theorem exists_ringEquiv_opensRange {X Y : Scheme.{u}} {R : CommRingCat.{u}}
    (Ψ : Spec R ⟶ X) [IsOpenImmersion Ψ] (f : X ⟶ Y) {U : Y.Opens} (hU : IsAffineOpen U)
    (α : Γ(Y, U) ⟶ R) (hΨ : Ψ ≫ f = Spec.map α ≫ hU.fromSpec) :
    ∃ (hVU : Ψ.opensRange ≤ f ⁻¹ᵁ U) (e : R ≃+* Γ(X, Ψ.opensRange)),
      ∀ a, e (α.hom a) = (f.appLE U Ψ.opensRange hVU).hom a := by
  have hVU : Ψ.opensRange ≤ f ⁻¹ᵁ U := by
    rintro _ ⟨z, rfl⟩
    change f (Ψ z) ∈ U
    rw [← Scheme.Hom.comp_apply, hΨ, Scheme.Hom.comp_apply]
    have := Set.mem_range_self (f := hU.fromSpec) (Spec.map α z)
    rwa [hU.range_fromSpec] at this
  have hV : IsAffineOpen Ψ.opensRange := isAffineOpen_opensRange Ψ
  let ι := IsOpenImmersion.isoOfRangeEq hV.fromSpec Ψ (by rw [hV.range_fromSpec]; rfl)
  have hι : ι.hom ≫ Ψ = hV.fromSpec := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let g : R ⟶ Γ(X, Ψ.opensRange) := Spec.preimage ι.hom
  let g' : Γ(X, Ψ.opensRange) ⟶ R := Spec.preimage ι.inv
  have hgg' : g ≫ g' = 𝟙 _ := Spec.map_injective (by simp [g, g'])
  have hg'g : g' ≫ g = 𝟙 _ := Spec.map_injective (by simp [g, g'])
  refine ⟨hVU, (⟨g, g', hgg', hg'g⟩ : R ≅ _).commRingCatIsoToRingEquiv, fun a => ?_⟩
  have key : Spec.map (f.appLE U Ψ.opensRange hVU) = Spec.map (α ≫ g) := by
    rw [← cancel_mono hU.fromSpec, IsAffineOpen.SpecMap_appLE_fromSpec _ hU hV, Spec.map_comp,
      Category.assoc, ← hΨ, ← hι, Category.assoc]
    simp [g]
  rw [Spec.map_injective key]
  rfl

/-- Every point of `Y ×_k L` lies in an affine open `V` over an affine open `U` of `Y` with
`Γ(V) ≅ Γ(U)[X]` compatibly with the projection. -/
private theorem exists_productChart {k : Type u} [Field k] {Y L : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) (sL : L ⟶ Spec (.of k))
    (hL : (∃ e : L ≅ projectiveLine k, e.hom ≫ (projectiveLine k ↘ Spec (.of k)) = sL) ∨
      ∃ e : L ≅ 𝔸(PUnit.{u + 1}; Spec (.of k)),
        e.hom ≫ (𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k)) = sL)
    (x : ↥(pullback sY sL)) :
    ∃ (U : Y.Opens) (hU : IsAffineOpen U) (V : (pullback sY sL).Opens) (hV : IsAffineOpen V)
      (hVU : V ≤ pullback.fst sY sL ⁻¹ᵁ U), x ∈ V ∧
      ∃ e : Polynomial Γ(Y, U) ≃+* Γ(pullback sY sL, V),
        ∀ a, e (Polynomial.C a) = ((pullback.fst sY sL).appLE U V hVU).hom a := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (show pullback.fst sY sL x ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨j, hj, hjs, hxj⟩ := exists_lineChart sL hL (pullback.snd sY sL x)
  set A := Γ(Y, U)
  set ψ : CommRingCat.of k ⟶ A := Spec.preimage (hU.fromSpec ≫ sY)
  have hψ : Spec.map ψ = hU.fromSpec ≫ sY := Spec.map_preimage _
  letI : Algebra k A := ψ.hom.toAlgebra
  have hψ' : CommRingCat.ofHom (algebraMap k A) = ψ := rfl
  have hC : CommRingCat.ofHom (algebraMap k (Polynomial k)) =
      CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k) := by
    rw [Polynomial.algebraMap_eq]
  let Ψ₀ : pullback (Spec.map (CommRingCat.ofHom (algebraMap k A)))
      (Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))) ⟶ pullback sY sL :=
    pullback.map _ _ _ _ hU.fromSpec j (𝟙 _) (by rw [hψ', hψ, Category.comp_id])
      (by rw [hC, ← hjs, Category.comp_id])
  have hΨ₀ : IsOpenImmersion Ψ₀ :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion) (inferInstanceAs
      (IsOpenImmersion hU.fromSpec)) hj (by rw [hψ', hψ]) (by rw [hC, ← hjs])
  let σ : A ⊗[k] Polynomial k →+* Polynomial A := (polyEquivTensor k A).symm.toRingEquiv.toRingHom
  have hσ : IsIso (Spec.map (CommRingCat.ofHom σ)) :=
    inferInstanceAs (IsIso (Spec.map ((polyEquivTensor k A).symm.toRingEquiv.toCommRingCatIso.hom)))
  let Ψ : Spec (.of (Polynomial A)) ⟶ pullback sY sL :=
    Spec.map (CommRingCat.ofHom σ) ≫ (pullbackSpecIso k A (Polynomial k)).inv ≫ Ψ₀
  have hΨ : IsOpenImmersion Ψ := inferInstance
  have hΨpr : Ψ ≫ pullback.fst sY sL =
      Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ hU.fromSpec := by
    simp only [Ψ, Ψ₀, Category.assoc, pullback.lift_fst]
    rw [pullbackSpecIso_inv_fst_assoc, ← Spec.map_comp_assoc]
    congr 2
    ext a : 2
    change (polyEquivTensor k A).symm (a ⊗ₜ 1) = Polynomial.C a
    rw [AlgEquiv.symm_apply_eq]
    simp [polyEquivTensor_apply]
  have hrange : Set.range Ψ = Set.range Ψ₀ := by
    have h1 : Function.Surjective (Spec.map (CommRingCat.ofHom σ) ≫
        (pullbackSpecIso k A (Polynomial k)).inv) :=
      (inferInstance : Surjective (Spec.map (CommRingCat.ofHom σ) ≫
        (pullbackSpecIso k A (Polynomial k)).inv)).surj
    simp only [Ψ, ← Category.assoc]
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, h1.range_eq, Set.image_univ]
  have hxV : x ∈ Set.range Ψ := by
    rw [hrange, Scheme.Pullback.range_map]
    exact ⟨by rwa [hU.range_fromSpec], hxj⟩
  obtain ⟨hVU, e, he⟩ := exists_ringEquiv_opensRange Ψ (pullback.fst sY sL) hU _ hΨpr
  exact ⟨U, hU, Ψ.opensRange, isAffineOpen_opensRange Ψ, hVU, hxV, e, he⟩

/-- The facts about the line used below: smooth, geometrically irreducible, a variety, of
dimension one. -/
private theorem line_facts {k : Type u} [Field k] {L : Scheme.{u}} (sL : L ⟶ Spec (.of k))
    (hL : (∃ e : L ≅ projectiveLine k, e.hom ≫ (projectiveLine k ↘ Spec (.of k)) = sL) ∨
      ∃ e : L ≅ 𝔸(PUnit.{u + 1}; Spec (.of k)),
        e.hom ≫ (𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k)) = sL) :
    Smooth sL ∧ GeometricallyIrreducible sL ∧ AlgebraicGeometry.IsVariety k sL ∧
      topologicalKrullDim L = 1 := by
  obtain ⟨M, s₀, e, rfl, h₁, h₂, h₃, h₄⟩ : ∃ (M : Scheme.{u}) (s₀ : M ⟶ Spec (.of k))
      (e : L ≅ M), sL = e.hom ≫ s₀ ∧ Smooth s₀ ∧ GeometricallyIrreducible s₀ ∧
        AlgebraicGeometry.IsVariety k s₀ ∧ topologicalKrullDim M = 1 := by
    rcases hL with ⟨e, rfl⟩ | ⟨e, rfl⟩
    · exact ⟨_, _, e, rfl, inferInstance, geometricallyIrreducible_projectiveLine k,
        inferInstance, topologicalKrullDim_projectiveLine k⟩
    · obtain ⟨c, hc⟩ := exists_iso_affineLine k
      have : Smooth (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))) :=
        projectiveLineAffineStructureMorphism_smooth k
      have : GeometricallyIrreducible
          (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))) :=
        Algebra.isGeometricallyIrreducible_polynomial k
      have : AlgebraicGeometry.IsVariety k
          (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))) := {}
      refine ⟨Spec (.of (Polynomial k)), Spec.map (CommRingCat.ofHom Polynomial.C), e ≪≫ c.symm,
        ?_, inferInstance, inferInstance, inferInstance, ?_⟩
      · rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← hc, Iso.inv_hom_id_assoc]
      change topologicalKrullDim (PrimeSpectrum (Polynomial k)) = 1
      rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
        Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
      rfl
  have : IsIntegral M := h₃.toIsIntegral
  have : Nonempty L := ⟨e.inv (Nonempty.some inferInstance)⟩
  refine ⟨inferInstance,
    (MorphismProperty.cancel_left_of_respectsIso @GeometricallyIrreducible e.hom s₀).2 h₂,
    @AlgebraicGeometry.IsVariety.mk _ _ _ _ (isIntegral_of_isOpenImmersion e.hom) inferInstance
      inferInstance inferInstance, ?_⟩
  rw [e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq, h₄]

/-! ### Local algebra of `A[X]` -/

/-- The extension of a prime of `A` to an `A`-algebra isomorphic to `A[X]` is prime. -/
private theorem isPrime_map_of_polyEquiv {A R : Type*} [CommRing A] [CommRing R] (α : A →+* R)
    (e : Polynomial A ≃+* R) (he : ∀ a, e (Polynomial.C a) = α a) (𝔭 : Ideal A) [𝔭.IsPrime] :
    (Ideal.map α 𝔭).IsPrime := by
  have : α = (e : Polynomial A →+* R).comp Polynomial.C := RingHom.ext fun a => (he a).symm
  rw [this, ← Ideal.map_map]
  exact Ideal.map_isPrime_of_equiv e

/-- The structure map `A → R` of an `A`-algebra isomorphic to `A[X]` is injective. -/
private theorem injective_of_polyEquiv {A R : Type*} [CommRing A] [CommRing R] (α : A →+* R)
    (e : Polynomial A ≃+* R) (he : ∀ a, e (Polynomial.C a) = α a) : Function.Injective α := by
  have : (α : A → R) = e ∘ Polynomial.C := by ext a; exact (he a).symm
  rw [this]
  exact e.injective.comp Polynomial.C_injective

attribute [local instance] Polynomial.algebra in
/-- A prime `Q` of `A[X]` over `0` is generated, up to nonzero constants, by one of its elements:
its extension to `K[X]`, `K = Frac A`, is principal. -/
private theorem exists_mem_forall_C_mul_mem_span {A : Type*} [CommRing A] [IsDomain A]
    (Q : Ideal (Polynomial A)) :
    ∃ φ ∈ Q, ∀ q ∈ Q, ∃ c : A, c ≠ 0 ∧ Polynomial.C c * q ∈ Ideal.span {φ} := by
  classical
  let K := FractionRing A
  let M := Submonoid.map (Polynomial.C : A →+* Polynomial A) (nonZeroDivisors A)
  haveI : IsLocalization M (Polynomial K) := Polynomial.isLocalization _ _
  let I : Ideal (Polynomial K) := Ideal.map (algebraMap (Polynomial A) (Polynomial K)) Q
  obtain ⟨g, hg⟩ := (inferInstance : Submodule.IsPrincipal I)
  have hgI : g ∈ I := hg ▸ Ideal.mem_span_singleton_self g
  obtain ⟨⟨φ, ⟨_, c, hc, rfl⟩⟩, hφ⟩ :=
    (IsLocalization.mem_map_algebraMap_iff M (Polynomial K)).mp hgI
  refine ⟨φ, φ.2, fun q hq => ?_⟩
  have hqI : algebraMap (Polynomial A) (Polynomial K) q ∈ I := Ideal.mem_map_of_mem _ hq
  rw [hg, Submodule.mem_span_singleton] at hqI
  obtain ⟨h, hh⟩ := hqI
  obtain ⟨⟨h', s⟩, hh'⟩ := IsLocalization.mk'_surjective M h
  change IsLocalization.mk' (Polynomial K) h' s = h at hh'
  obtain ⟨c', hc', hs⟩ := s.2
  have hh'' : h * algebraMap (Polynomial A) (Polynomial K) (Polynomial.C c') =
      algebraMap (Polynomial A) (Polynomial K) h' := by
    rw [← hh', hs]
    exact IsLocalization.mk'_spec _ _ _
  refine ⟨c * c', mul_ne_zero (nonZeroDivisors.ne_zero hc) (nonZeroDivisors.ne_zero hc'), ?_⟩
  rw [Ideal.mem_span_singleton']
  refine ⟨h', ?_⟩
  apply IsLocalization.injective (Polynomial K) (show M ≤ nonZeroDivisors (Polynomial A) from ?_)
  · rw [map_mul, map_mul, Polynomial.C_mul, map_mul]
    rw [smul_eq_mul] at hh
    change g * algebraMap (Polynomial A) (Polynomial K) (Polynomial.C c) =
      algebraMap (Polynomial A) (Polynomial K) φ at hφ
    linear_combination (-(algebraMap (Polynomial A) (Polynomial K) φ)) * hh'' +
      (-(h * algebraMap (Polynomial A) (Polynomial K) (Polynomial.C c'))) * hφ +
      (algebraMap (Polynomial A) (Polynomial K) (Polynomial.C c) *
        algebraMap (Polynomial A) (Polynomial K) (Polynomial.C c')) * hh
  · rintro _ ⟨a, ha, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (Polynomial.C_ne_zero.mpr (nonZeroDivisors.ne_zero ha))

/-- `exists_mem_forall_C_mul_mem_span` for an `A`-algebra isomorphic to `A[X]`. -/
private theorem exists_mem_forall_mul_mem_span_of_polyEquiv {A R : Type*} [CommRing A]
    [IsDomain A] [CommRing R] (α : A →+* R) (e : Polynomial A ≃+* R)
    (he : ∀ a, e (Polynomial.C a) = α a) (Q : Ideal R) :
    ∃ φ ∈ Q, ∀ q ∈ Q, ∃ c : A, c ≠ 0 ∧ α c * q ∈ Ideal.span {φ} := by
  obtain ⟨φ, hφ, h⟩ := exists_mem_forall_C_mul_mem_span (Q.comap (e : Polynomial A →+* R))
  refine ⟨e φ, hφ, fun q hq => ?_⟩
  obtain ⟨c, hc, hcq⟩ := h (e.symm q) (by rw [Ideal.mem_comap]; simpa using hq)
  refine ⟨c, hc, ?_⟩
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hcq
  refine Ideal.mem_span_singleton'.mpr ⟨e r, ?_⟩
  rw [← map_mul, hr, map_mul, he, RingEquiv.apply_symm_apply]

/-! ### Stalks on affine opens -/

-- The `overlappingInstances` linter fails to synthesize on these `[IsDomain Γ(X, V)]` binders.
set_option linter.overlappingInstances false in
/-- If `𝔭 Γ(V)` is prime for the prime `𝔭` of `f(x)`, the stalk map at `x` carries uniformizers
of the discrete valuation ring `𝒪_{Y,f(x)}` to uniformizers of `𝒪_{X,x}`. -/
private theorem irreducible_stalkMap {X Y : Scheme} (f : X ⟶ Y) {U : Y.Opens}
    (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) {x : X}
    (hx : x ∈ V) [IsDomain Γ(X, V)]
    (hprime : (Ideal.map (f.appLE U V hVU).hom
      (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal).IsPrime)
    (hinj : Function.Injective (f.appLE U V hVU).hom)
    [IsDomain (Y.presheaf.stalk (f x))] [IsDiscreteValuationRing (Y.presheaf.stalk (f x))]
    [IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)]
    {ϖ : Y.presheaf.stalk (f x)} (hϖ : Irreducible ϖ) : Irreducible ((f.stalkMap x).hom ϖ) := by
  have hfx : f x ∈ U := hVU hx
  let := Y.presheaf.algebra_section_stalk ⟨f x, hfx⟩
  have hlocY := hU.isLocalization_stalk ⟨f x, hfx⟩
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have hlocX := hV.isLocalization_stalk ⟨x, hx⟩
  set 𝔭 := (hU.primeIdealOf ⟨f x, hfx⟩).asIdeal
  set P := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  set α := (f.appLE U V hVU).hom
  have hcomp : (f.stalkMap x).hom.comp (algebraMap Γ(Y, U) (Y.presheaf.stalk (f x))) =
      (algebraMap Γ(X, V) (X.presheaf.stalk x)).comp α := by
    ext a
    have h : (Y.presheaf.germ U (f x) hfx ≫ f.stalkMap x).hom a =
        (f.appLE U V hVU ≫ X.presheaf.germ V x hx).hom a := by
      rw [Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
    exact h
  have hJP : Ideal.map α 𝔭 ≤ P := by
    have h := IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx
    have h' : Ideal.comap α P = 𝔭 := congrArg PrimeSpectrum.asIdeal h
    rw [← h']
    exact Ideal.map_comap_le
  have h𝔭 : 𝔭 ≠ ⊥ := by
    intro h
    have hm := IsLocalization.AtPrime.map_eq_maximalIdeal 𝔭 (Y.presheaf.stalk (f x))
    rw [h, Ideal.map_bot] at hm
    exact IsDiscreteValuationRing.not_a_field _ hm.symm
  have hJ0 : Ideal.map α 𝔭 ≠ ⊥ := by
    rwa [Ne, Ideal.map_eq_bot_iff_of_injective hinj]
  have hinjX : Function.Injective (algebraMap Γ(X, V) (X.presheaf.stalk x)) :=
    IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors P)
  have hprimeX : (Ideal.map (algebraMap Γ(X, V) (X.presheaf.stalk x)) (Ideal.map α 𝔭)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint P.primeCompl _ _ hprime
      (Set.disjoint_left.mpr fun _ ha ha' => ha (hJP ha'))
  have hne : Ideal.map (algebraMap Γ(X, V) (X.presheaf.stalk x)) (Ideal.map α 𝔭) ≠ ⊥ := by
    rwa [Ne, Ideal.map_eq_bot_iff_of_injective hinjX]
  have hmax : Ideal.map (f.stalkMap x).hom (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal 𝔭 (Y.presheaf.stalk (f x)), Ideal.map_map,
      hcomp, ← Ideal.map_map]
    exact IsLocalRing.eq_maximalIdeal (hprimeX.isMaximal hne)
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer] at hϖ ⊢
  rw [← hmax, hϖ, Ideal.map_span, Set.image_singleton]

-- The `overlappingInstances` linter fails to synthesize on these `[IsDomain Γ(X, V)]` binders.
set_option linter.overlappingInstances false in
/-- A section `φ` in the prime `P` of `x` which generates `P` up to factors outside `P` is a
uniformizer of the discrete valuation ring `𝒪_{X,x}`. -/
private theorem irreducible_germ_of_forall_mul_mem_span {X : Scheme} {V : X.Opens}
    (hV : IsAffineOpen V) {x : X} (hx : x ∈ V) [IsDomain (X.presheaf.stalk x)]
    [IsDiscreteValuationRing (X.presheaf.stalk x)] {φ : Γ(X, V)}
    (hφ : φ ∈ (hV.primeIdealOf ⟨x, hx⟩).asIdeal)
    (h : ∀ q ∈ (hV.primeIdealOf ⟨x, hx⟩).asIdeal,
      ∃ s ∉ (hV.primeIdealOf ⟨x, hx⟩).asIdeal, s * q ∈ Ideal.span {φ}) :
    Irreducible ((X.presheaf.germ V x hx).hom φ) := by
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have hloc := hV.isLocalization_stalk ⟨x, hx⟩
  set P := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer,
    ← IsLocalization.AtPrime.map_eq_maximalIdeal P (X.presheaf.stalk x)]
  change _ = Ideal.span {algebraMap Γ(X, V) (X.presheaf.stalk x) φ}
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro q hq
    obtain ⟨s, hs, hsq⟩ := h q hq
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hsq
    have hu : IsUnit (algebraMap Γ(X, V) (X.presheaf.stalk x) s) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff _ P s).mpr hs
    rw [Ideal.mem_comap, Ideal.mem_span_singleton']
    refine ⟨hu.unit⁻¹ * algebraMap _ _ r, ?_⟩
    rw [mul_assoc, ← map_mul, hr, map_mul, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ hφ

/-- A section outside the prime of `x` is a unit of `𝒪_{X,x}`. -/
private theorem isUnit_germ_of_notMem {X : Scheme} {V : X.Opens} (hV : IsAffineOpen V)
    {x : X} (hx : x ∈ V) {φ : Γ(X, V)} (hφ : φ ∉ (hV.primeIdealOf ⟨x, hx⟩).asIdeal) :
    IsUnit ((X.presheaf.germ V x hx).hom φ) := by
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have hloc := hV.isLocalization_stalk ⟨x, hx⟩
  exact (IsLocalization.AtPrime.isUnit_to_map_iff _ (hV.primeIdealOf ⟨x, hx⟩).asIdeal φ).mpr hφ

-- The `overlappingInstances` linter fails to synthesize on these `[IsDomain Γ(X, V)]` binders.
set_option linter.overlappingInstances false in
/-- Two points of an affine open with nonzero comparable primes, the larger one with a discrete
valuation ring as local ring, coincide. -/
private theorem eq_of_primeIdealOf_le {X : Scheme} {V : X.Opens} (hV : IsAffineOpen V)
    [IsDomain Γ(X, V)] {x y : X} (hx : x ∈ V) (hy : y ∈ V) [IsDomain (X.presheaf.stalk y)]
    [IsDiscreteValuationRing (X.presheaf.stalk y)]
    (hle : (hV.primeIdealOf ⟨x, hx⟩).asIdeal ≤ (hV.primeIdealOf ⟨y, hy⟩).asIdeal)
    (hne : (hV.primeIdealOf ⟨x, hx⟩).asIdeal ≠ ⊥) : x = y := by
  let := X.presheaf.algebra_section_stalk ⟨y, hy⟩
  have hloc := hV.isLocalization_stalk ⟨y, hy⟩
  set P := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  set Q := (hV.primeIdealOf ⟨y, hy⟩).asIdeal
  have hdisj : Disjoint (Q.primeCompl : Set Γ(X, V)) P :=
    Set.disjoint_left.mpr fun _ ha ha' => ha (hle ha')
  have hprime := IsLocalization.isPrime_of_isPrime_disjoint Q.primeCompl (X.presheaf.stalk y) P
    inferInstance hdisj
  have hinj : Function.Injective (algebraMap Γ(X, V) (X.presheaf.stalk y)) :=
    IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors Q)
  have hne' : Ideal.map (algebraMap Γ(X, V) (X.presheaf.stalk y)) P ≠ ⊥ := by
    rwa [Ne, Ideal.map_eq_bot_iff_of_injective hinj]
  have hmax := IsLocalRing.eq_maximalIdeal (hprime.isMaximal hne')
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal Q (X.presheaf.stalk y)] at hmax
  have hPQ : P = Q := by
    rw [← IsLocalization.comap_map_of_isPrime_disjoint Q.primeCompl (X.presheaf.stalk y)
      (I := P) inferInstance hdisj, hmax,
      IsLocalization.comap_map_of_isPrime_disjoint Q.primeCompl (X.presheaf.stalk y)
      (I := Q) inferInstance (Set.disjoint_left.mpr fun _ ha ha' => ha ha')]
  have h1 := hV.fromSpec_primeIdealOf ⟨x, hx⟩
  have h2 := hV.fromSpec_primeIdealOf ⟨y, hy⟩
  rw [show hV.primeIdealOf ⟨x, hx⟩ = hV.primeIdealOf ⟨y, hy⟩ from PrimeSpectrum.ext hPQ] at h1
  exact h1.symm.trans h2

/-- The prime of the generic point of an integral scheme in an affine open is zero. -/
private theorem primeIdealOf_genericPoint_eq_bot {Y : Scheme} [IsIntegral Y] {U : Y.Opens}
    (hU : IsAffineOpen U) (h : genericPoint Y ∈ U) :
    (hU.primeIdealOf ⟨genericPoint Y, h⟩).asIdeal = ⊥ := by
  let := Y.presheaf.algebra_section_stalk ⟨genericPoint Y, h⟩
  have hloc := hU.isLocalization_stalk ⟨genericPoint Y, h⟩
  have hm := IsLocalization.AtPrime.map_eq_maximalIdeal
    (hU.primeIdealOf ⟨genericPoint Y, h⟩).asIdeal (Y.presheaf.stalk (genericPoint Y))
  have hfield : IsField (Y.presheaf.stalk (genericPoint Y)) :=
    (inferInstance : Field Y.functionField).toIsField
  rw [(IsLocalRing.isField_iff_maximalIdeal_eq).mp hfield] at hm
  rw [eq_bot_iff]
  intro a ha
  have : algebraMap Γ(Y, U) (Y.presheaf.stalk (genericPoint Y)) a = 0 := by
    have := Ideal.mem_map_of_mem (algebraMap Γ(Y, U) (Y.presheaf.stalk (genericPoint Y))) ha
    rwa [hm, Ideal.mem_bot] at this
  exact (Ideal.mem_bot).mpr (germ_injective_of_isIntegral Y _ h (this.trans (map_zero _).symm))

/-! ### Orders of pulled-back local equations -/

section Order

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y]
  [IsNormal Y]

/-- The order of vanishing along a prime divisor `E` of the pull-back of a local equation is zero
when `f(η_E)` lies off the support. -/
private theorem ordUnit_pullbackComponent_eq_zero (f : X ⟶ Y) {B : Divisor Y}
    (hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp)
    {U : Y.Opens} {φ : (RationalFunctions Y)ˣ} (hφ : B.IsLocalEquation U φ)
    (E : MMP.Mori.PrimeDivisor X)
    (hE : (E.support ∩ f ⁻¹ᵁ U).Nonempty) (hEB : f E.genericPoint ∉ B.supp) :
    E.ordUnit (pullbackComponent f hB hφ E.component
      (E.map_componentGenericPoint_mem f hE)) = 0 := by
  have hU : f E.genericPoint ∈ U := (E.genericPoint_mem_iff (f ⁻¹ᵁ U)).mpr hE
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hU hEB (mem_pointComponent _)
  have h := pullbackComponent_val_eq_stalkMap f hB hφ (mem_pointComponent (f E.genericPoint))
    a.val ha.symm E.genericPoint_mem_component (E.map_componentGenericPoint_mem f hE)
  exact E.ordUnit_eq_zero_of_isUnit (a.isUnit.map (f.stalkMap _).hom) h.symm

/-- Transport of the valuation facts of `𝒪_{Y,Γ}` to the stalk at a point equal to `η_Γ`. -/
private theorem valuation_stalkToRationalFunctions (Γ : MMP.Mori.PrimeDivisor Y) {y : Y}
    (hy : Γ.genericPoint = y) (hW : y ∈ Γ.component.1) :
    IsDiscreteValuationRing (Y.presheaf.stalk y) ∧
    (∀ ϖ : Y.presheaf.stalk y, Irreducible ϖ →
      Γ.valuation ((stalkToRationalFunctions Y hW).hom ϖ) = WithZero.exp 1) ∧
    (∀ a : Y.presheaf.stalk y, IsUnit a →
      Γ.valuation ((stalkToRationalFunctions Y hW).hom a) = 1) := by
  subst hy
  exact ⟨Γ.isDiscreteValuationRing_localRing, fun ϖ h => Γ.valuation_toComponent_of_irreducible h,
    fun a h => Γ.valuation_toComponent_of_isUnit h⟩

/-- If `f(η_E) = η_Γ` and the stalk map at `η_E` carries uniformizers to uniformizers, the
valuations `v_E` and `v_Γ` agree along it. -/
private theorem valuation_stalkMap_eq (f : X ⟶ Y) (E : MMP.Mori.PrimeDivisor X)
    (Γ : MMP.Mori.PrimeDivisor Y) (hEΓ : Γ.genericPoint = f E.genericPoint)
    (hyΓ : f E.genericPoint ∈ Γ.component.1)
    (hirr : ∀ ϖ : Y.presheaf.stalk (f E.genericPoint), Irreducible ϖ →
      Irreducible ((f.stalkMap E.genericPoint).hom ϖ))
    (b : Y.presheaf.stalk (f E.genericPoint)) :
    E.valuation (E.toComponent.hom ((f.stalkMap E.genericPoint).hom b)) =
      Γ.valuation ((stalkToRationalFunctions Y hyΓ).hom b) := by
  obtain ⟨hdvr, hvϖ, hvu⟩ := valuation_stalkToRationalFunctions Γ hEΓ hyΓ
  have hE1 := E.isDiscreteValuationRing_localRing
  by_cases hb : b = 0
  · simp [hb]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Y.presheaf.stalk (f E.genericPoint))
  obtain ⟨n, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
  simp only [map_mul, map_pow]
  rw [E.valuation_toComponent_of_isUnit (w.isUnit.map (f.stalkMap E.genericPoint).hom),
    E.valuation_toComponent_of_irreducible (hirr ϖ hϖ), hvu _ w.isUnit, hvϖ ϖ hϖ]

/-- A nonzero divisor of the stalk at a point of `Γ` has nonzero `Γ`-valuation. -/
private theorem valuation_stalkToRationalFunctions_ne_zero (Γ : MMP.Mori.PrimeDivisor Y) {y : Y}
    (hy : y ∈ Γ.component.1) (c : nonZeroDivisors (Y.presheaf.stalk y)) :
    Γ.valuation ((stalkToRationalFunctions Y hy).hom c) ≠ 0 := by
  have hne : (stalkToRationalFunctions Y hy).hom c ≠ 0 := fun h0 =>
    nonZeroDivisors.ne_zero c.2 (stalkToRationalFunctions_injective hy (h0.trans (map_zero _).symm))
  obtain ⟨d, hd⟩ := (RationalFunctions.isField_stalk Y Γ.component).mul_inv_cancel hne
  have := congrArg Γ.valuation hd
  rw [map_mul, map_one] at this
  exact left_ne_zero_of_mul_eq_one this

/-- If `f(η_E) = η_Γ` and the stalk map at `η_E` carries uniformizers to uniformizers, the order
of vanishing along `E` of the pull-back of a local equation `φ` is `v_Γ(φ)`. -/
private theorem ordUnit_pullbackComponent_eq_ord (f : X ⟶ Y) {B : Divisor Y}
    (hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp)
    {U : Y.Opens} {φ : (RationalFunctions Y)ˣ} (hφ : B.IsLocalEquation U φ)
    (E : MMP.Mori.PrimeDivisor X) (Γ : MMP.Mori.PrimeDivisor Y)
    (hE : (E.support ∩ f ⁻¹ᵁ U).Nonempty) (hEΓ : Γ.genericPoint = f E.genericPoint)
    (hirr : ∀ ϖ : Y.presheaf.stalk (f E.genericPoint), Irreducible ϖ →
      Irreducible ((f.stalkMap E.genericPoint).hom ϖ)) :
    E.ordUnit (pullbackComponent f hB hφ E.component
      (E.map_componentGenericPoint_mem f hE)) = Γ.ord φ := by
  have hyΓ : f E.genericPoint ∈ Γ.component.1 := hEΓ ▸ Γ.genericPoint_mem_component
  have hval := valuation_stalkMap_eq f E Γ hEΓ hyΓ hirr
  set x := E.genericPoint
  set ρ := (f.stalkMap x).hom
  letI := (stalkToRationalFunctions Y hyΓ).hom.toAlgebra
  haveI := isFractionRing_stalkToRationalFunctions hyΓ
  obtain ⟨⟨b, c⟩, hbc⟩ := IsLocalization.surj (nonZeroDivisors (Y.presheaf.stalk (f x)))
    ((φ : RationalFunctions Y) Γ.component)
  change (φ : RationalFunctions Y) Γ.component * (stalkToRationalFunctions Y hyΓ).hom c =
    (stalkToRationalFunctions Y hyΓ).hom b at hbc
  set z := componentGenericPoint X E.component
  have hsz : z ⤳ x := E.specializes_genericPoint
  have hs : f z ⤳ f x := f.base.hom.map_specializes hsz
  have hy₀ : f z ∈ Γ.component.1 := by
    have h1 := mem_pointComponent (f z)
    have h2 : f x ∈ (pointComponent (f z)).1 :=
      hs.mem_closed (isClosed_of_mem_irreducibleComponents _ (pointComponent (f z)).2) h1
    rwa [eq_of_mem_irreducibleComponents h2 hyΓ] at h1
  have hZ := E.map_componentGenericPoint_mem f hE
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hZ (hB _) hy₀
  rw [pullbackComponent_eq hB hφ hZ hy₀ a ha]
  set sp := (Y.presheaf.stalkSpecializes hs).hom
  have hsp : ∀ b', (stalkToRationalFunctions Y hy₀).hom (sp b') =
      (stalkToRationalFunctions Y hyΓ).hom b' := by
    intro b'
    change (Y.presheaf.stalkSpecializes hs ≫ Y.presheaf.stalkSpecializes _).hom b' = _
    rw [TopCat.Presheaf.stalkSpecializes_comp]
    rfl
  have hrel : a.val * sp c = sp b := by
    apply stalkToRationalFunctions_injective hy₀
    rwa [map_mul, hsp, hsp, ha]
  have hι : ∀ b', (f.stalkMap z).hom (sp b') = E.toComponent.hom (ρ b') := fun b' =>
    Scheme.Hom.stalkSpecializes_stalkMap_apply f z x hsz b'
  have hrelX : (f.stalkMap z).hom a.val * E.toComponent.hom (ρ c) =
      E.toComponent.hom (ρ b) := by
    rw [← hι, ← hι, ← map_mul, hrel]
  have hvE := congrArg E.valuation hrelX
  rw [map_mul, hval, hval] at hvE
  have hvΓ := congrArg Γ.valuation hbc
  rw [map_mul] at hvΓ
  have key := mul_right_cancel₀ (valuation_stalkToRationalFunctions_ne_zero Γ hyΓ c)
    (hvE.trans hvΓ.symm)
  have h1 := E.valuation_eq_exp_ordUnit (Units.map (f.stalkMap z).hom.toMonoidHom a)
  rw [Units.coe_map] at h1
  have h2 := Γ.valuation_component φ
  exact WithZero.exp_injective (h1.symm.trans (key.trans h2))

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- A nonzero section `φ` on a nonempty open `V` of an integral scheme, as a unit of `K(X)`:
its image in the local ring at every point of `V` maps to it. -/
private theorem exists_unit_rationalFunctions_eq_germ [IsIntegral X] {V : X.Opens}
    (hV : (V : Set X).Nonempty) (φ : Γ(X, V)) (hφ : φ ≠ 0) :
    ∃ u : (RationalFunctions X)ˣ, ∀ (E : MMP.Mori.PrimeDivisor X) (hE : E.genericPoint ∈ V),
      E.toComponent.hom ((X.presheaf.germ V E.genericPoint hE).hom φ) =
        (u : RationalFunctions X) E.component := by
  have hmem : ∀ Z : irreducibleComponents X, componentGenericPoint X Z ∈ V := by
    intro Z
    have hZ : Z.1 = Set.univ :=
      Z.2.eq_of_subset (IrreducibleSpace.isIrreducible_univ X) (Set.subset_univ _)
    obtain ⟨y, hy⟩ := hV
    exact ((isGenericPoint_componentGenericPoint X Z).mem_open_set_iff V.isOpen).mpr
      ⟨y, by rw [hZ]; trivial, hy⟩
  let v : RationalFunctions X := fun Z => (X.presheaf.germ V _ (hmem Z)).hom φ
  have hv : IsUnit v := by
    refine Pi.isUnit_iff.mpr fun Z => ?_
    let := (RationalFunctions.isField_stalk X Z).toField
    refine isUnit_iff_ne_zero.mpr fun h => hφ ?_
    exact germ_injective_of_isIntegral _ _ (hmem Z) (h.trans (map_zero _).symm)
  refine ⟨hv.unit, fun E hE => ?_⟩
  change _ = (X.presheaf.germ V _ (hmem E.component)).hom φ
  exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _

end Order

/-! ### Generic points under the projection -/

/-- A point whose closure has dense image maps to the generic point. -/
private theorem eq_genericPoint_of_dense {X Y : Scheme.{u}} [IsIntegral Y] (f : X ⟶ Y) {z : X}
    (hz : Dense (f '' closure {z})) : f z = genericPoint Y := by
  refine IsGenericPoint.eq ?_ (genericPoint_spec Y)
  refine Set.eq_univ_of_univ_subset ?_
  rw [← hz.closure_eq]
  refine closure_minimal ?_ isClosed_closure
  refine (image_closure_subset_closure_image f.continuous).trans ?_
  rw [Set.image_singleton]

/-- The generic point of an irreducible component of an irreducible space is dense. -/
private theorem closure_componentGenericPoint {X : Scheme.{u}} [IrreducibleSpace X]
    (Z : irreducibleComponents X) : closure {componentGenericPoint X Z} = Set.univ := by
  rw [(isGenericPoint_componentGenericPoint X Z).def]
  exact Z.2.eq_of_subset (IrreducibleSpace.isIrreducible_univ X) (Set.subset_univ _)

/-- On a locally Noetherian normal scheme a prime divisor is determined by its support. -/
private theorem eq_of_support_eq {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {E E' : MMP.Mori.PrimeDivisor X} (h : E.support = E'.support) : E = E' := by
  refine (MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E' E ?_).symm
  rw [← h, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact subset_closure rfl

/-- If `E = f⁻¹(Γ)` for a surjective `f`, then `f` maps `η_E` to `η_Γ`. -/
private theorem genericPoint_eq_of_support_eq_preimage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : Function.Surjective f) {E : MMP.Mori.PrimeDivisor X} {Γ : MMP.Mori.PrimeDivisor Y}
    (h : E.support = f ⁻¹' Γ.support) : Γ.genericPoint = f E.genericPoint := by
  have hEη : E.genericPoint ∈ E.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  refine IsGenericPoint.eq (S := Γ.support) ?_ ?_
  · exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure Γ).symm
  · refine subset_antisymm (closure_minimal ?_ Γ.idealSheaf.support.isClosed) ?_
    · rw [Set.singleton_subset_iff]
      exact (h ▸ hEη : E.genericPoint ∈ f ⁻¹' Γ.support)
    · rw [← hf.image_preimage Γ.support, ← h, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      refine (image_closure_subset_closure_image f.continuous).trans ?_
      rw [Set.image_singleton]

/-! ### The two parts -/

/-- The prime divisors `Γ × L = pr⁻¹(Γ)` of `Y × L`, and where `pr` sends generic points. -/
private theorem exists_preimagePrimeDivisor {k : Type u} [Field k] {Y L : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) (sL : L ⟶ Spec (.of k)) (hY : IsNormalVariety k sY)
    [IsLocallyNoetherian Y] [IsNormal Y]
    [IsLocallyNoetherian (pullback sY sL)] [IsNormal (pullback sY sL)]
    (hL : (∃ e : L ≅ projectiveLine k, e.hom ≫ (projectiveLine k ↘ Spec (.of k)) = sL) ∨
      ∃ e : L ≅ 𝔸(PUnit.{u + 1}; Spec (.of k)),
        e.hom ≫ (𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k)) = sL)
    [IsIntegral Y] [IsIntegral (pullback sY sL)] :
    ∃ ι : MMP.Mori.PrimeDivisor Y → MMP.Mori.PrimeDivisor (pullback sY sL),
      (∀ Γ, (ι Γ).support = pullback.fst sY sL ⁻¹' Γ.support) ∧ Function.Injective ι ∧
      (∀ E Γ, E.support = pullback.fst sY sL ⁻¹' Γ.support → E = ι Γ) ∧
      (∀ E ∉ Set.range ι, pullback.fst sY sL E.genericPoint = genericPoint Y) ∧
      (∀ Z : irreducibleComponents ↥(pullback sY sL),
        pullback.fst sY sL (componentGenericPoint _ Z) = genericPoint Y) ∧
      ∀ Γ, Γ.genericPoint = pullback.fst sY sL (ι Γ).genericPoint := by
  obtain ⟨⟨-, hsurj, -, -, -, -⟩, -⟩ := product_line_basic sY sL hY hL
  haveI : AlgebraicGeometry.IsVariety k sY := hY.1
  obtain ⟨_, _, _, hLd⟩ := line_facts sL hL
  have hcl := MMP.primeDivisor_pullback_eq_preimage_or_dense_of_smooth sY sL hLd
  set pr := pullback.fst sY sL
  have hs : Function.Surjective pr := hsurj.surj
  choose ι hι using hcl.1
  have hιeq : ∀ (E : MMP.Mori.PrimeDivisor (pullback sY sL)) (Γ : MMP.Mori.PrimeDivisor Y),
      E.support = pr ⁻¹' Γ.support → E = ι Γ := fun E Γ h =>
    eq_of_support_eq (h.trans (hι Γ).symm)
  refine ⟨ι, hι, fun Γ Γ' h => ?_, hιeq, fun E hE => ?_,
    fun Z => ?_, fun Γ => genericPoint_eq_of_support_eq_preimage pr hs (hι Γ)⟩
  · exact eq_of_support_eq (hs.preimage_injective (by
      change pr ⁻¹' Γ.support = pr ⁻¹' Γ'.support
      rw [← hι, ← hι, h]))
  · rcases hcl.2 E with ⟨Γ, -, hEΓ⟩ | hd
    · exact absurd ⟨Γ, (hιeq E Γ hEΓ).symm⟩ hE
    · refine eq_genericPoint_of_dense pr ?_
      rwa [← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  · refine eq_genericPoint_of_dense pr ?_
    rw [closure_componentGenericPoint, Set.image_univ, hs.range_eq]
    exact dense_univ

/-- Obligation (1): the pull-back `pr^* D₀` exists and `m pr^* D₀` is `pr^*(m D₀)`. -/
private theorem pullback_line_divisor {k : Type u} [Field k] {Y L : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) (sL : L ⟶ Spec (.of k)) (hY : IsNormalVariety k sY)
    [IsLocallyNoetherian Y] [IsNormal Y]
    [IsLocallyNoetherian (pullback sY sL)] [IsNormal (pullback sY sL)]
    (hL : (∃ e : L ≅ projectiveLine k, e.hom ≫ (projectiveLine k ↘ Spec (.of k)) = sL) ∨
      ∃ e : L ≅ 𝔸(PUnit.{u + 1}; Spec (.of k)),
        e.hom ≫ (𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k)) = sL) :
    ∀ (D₀ : Divisor Y) (m : ℤ), (m • D₀).IsCartier →
      ∃ D : Divisor (pullback sY sL),
        (∀ (E : Mori.PrimeDivisor (pullback sY sL)) (Γ : Mori.PrimeDivisor Y),
          (E.support : Set ↥(pullback sY sL : Scheme.{u})) =
            (pullback.fst sY sL).base ⁻¹' (Γ.support : Set Y) →
          D.coeff E = D₀.coeff Γ) ∧
        (∀ E : Mori.PrimeDivisor (pullback sY sL),
          (∀ Γ : Mori.PrimeDivisor Y, (E.support : Set ↥(pullback sY sL : Scheme.{u})) ≠
            (pullback.fst sY sL).base ⁻¹' (Γ.support : Set Y)) →
          D.coeff E = 0) ∧
        (m • D).IsCartier ∧
        ∃ hB, (m • D₀).IsPullback (pullback.fst sY sL) hB (m • D) := by
  intro D₀ m hm
  obtain ⟨⟨-, -, hnvX, -, -, -⟩, -⟩ := product_line_basic sY sL hY hL
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : IsIntegral (pullback sY sL) := hnvX.1.toIsIntegral
  obtain ⟨ι, hι, hιinj, hιeq, hgen, hgenZ, hΓgen⟩ := exists_preimagePrimeDivisor sY sL hY hL
  set pr := pullback.fst sY sL
  have hB : ∀ (B : Divisor Y) (Z : irreducibleComponents ↥(pullback sY sL)),
      pr (componentGenericPoint _ Z) ∉ B.supp := fun B Z => by
    rw [hgenZ Z]
    exact genericPoint_notMem_supp B
  have hirr : ∀ Γ (ϖ : Y.presheaf.stalk (pr (ι Γ).genericPoint)), Irreducible ϖ →
      Irreducible ((pr.stalkMap (ι Γ).genericPoint).hom ϖ) := by
    intro Γ ϖ hϖ
    obtain ⟨U, hU, V, hV, hVU, hxV, e, he⟩ := exists_productChart sY sL hL (ι Γ).genericPoint
    haveI : Nonempty V := ⟨⟨_, hxV⟩⟩
    have hW : pr (ι Γ).genericPoint ∈ Γ.component.1 :=
      hΓgen Γ ▸ Γ.genericPoint_mem_component
    haveI := (valuation_stalkToRationalFunctions Γ (hΓgen Γ) hW).1
    haveI := (ι Γ).isDiscreteValuationRing_localRing
    exact irreducible_stalkMap pr hU hV hVU hxV (isPrime_map_of_polyEquiv _ e he _)
      (injective_of_polyEquiv _ e he) hϖ
  set D : Divisor (pullback sY sL) := Finsupp.mapDomain ι D₀
  have hD1 : ∀ Γ, D.coeff (ι Γ) = D₀.coeff Γ := fun Γ =>
    Finsupp.mapDomain_apply_of_injective hιinj D₀ Γ
  have hD0 : ∀ E ∉ Set.range ι, D.coeff E = 0 := fun E hE =>
    Finsupp.mapDomain_notin_range D₀ E hE
  have hPB : (m • D₀).IsPullback pr (hB _) (m • D) := by
    refine Divisor.IsPullback.of_forall_exists fun E => ?_
    obtain ⟨U, hU, φ, hφ⟩ := hm (pr E.genericPoint)
    have hE := (E.genericPoint_mem_iff (pr ⁻¹ᵁ U)).mp hU
    refine ⟨U, φ, hφ, hE, ?_⟩
    rw [DivisorWithCoeffs.coeff_smul]
    by_cases hr : E ∈ Set.range ι
    · obtain ⟨Γ, rfl⟩ := hr
      rw [hD1, ordUnit_pullbackComponent_eq_ord pr (hB _) hφ (ι Γ) Γ hE (hΓgen Γ) (hirr Γ)]
      have hΓU : (Γ.support ∩ U).Nonempty := by
        refine ⟨Γ.genericPoint, ?_, hΓgen Γ ▸ hU⟩
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact subset_closure rfl
      have := hφ Γ hΓU
      rwa [DivisorWithCoeffs.coeff_smul] at this
    · rw [hD0 E hr, smul_zero, ordUnit_pullbackComponent_eq_zero pr (hB _) hφ E hE
        (by rw [hgen E hr]; exact genericPoint_notMem_supp _)]
  refine ⟨D, fun E Γ h => ?_, fun E h => ?_, fun x => ?_, hB _, hPB⟩
  · rw [hιeq E Γ h, hD1]
  · refine hD0 E ?_
    rintro ⟨Γ, rfl⟩
    exact h Γ (hι Γ)
  · obtain ⟨U, hxU, φ, hφ⟩ := hm (pr x)
    obtain ⟨ψ, hψ, -⟩ := exists_isLocalEquation_of_isPullback pr (hB _) hPB hφ
    exact ⟨pr ⁻¹ᵁ U, hxU, ψ, hψ⟩

/-! ### Dominating prime divisors and local-to-global -/

/-- Over a chart `Γ(V) ≅ Γ(U)[X]` of `f : X ⟶ Y`, a prime divisor `E` of `X` dominating `Y` with
`η_E ∈ V` is cut out on `V` by a single section: some `u ∈ K(X)ˣ` has `v_E(u) = 1` and
`v_{E'}(u) = 0` for every other prime divisor `E'` dominating `Y` and meeting `V`. -/
private theorem exists_ord_eq_one_of_polyEquiv {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) {U : Y.Opens} (hU : IsAffineOpen U)
    {V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) (e : Polynomial Γ(Y, U) ≃+* Γ(X, V))
    (he : ∀ a, e (Polynomial.C a) = (f.appLE U V hVU).hom a) {E : MMP.Mori.PrimeDivisor X}
    (hEV : E.genericPoint ∈ V) (hE : f E.genericPoint = genericPoint Y) :
    ∃ u : (RationalFunctions X)ˣ, E.ord u = 1 ∧ ∀ E' : MMP.Mori.PrimeDivisor X, E' ≠ E →
      f E'.genericPoint = genericPoint Y → (E'.support ∩ V).Nonempty → E'.ord u = 0 := by
  haveI : Nonempty V := ⟨⟨_, hEV⟩⟩
  haveI : Nonempty U := ⟨⟨_, hVU hEV⟩⟩
  set α := (f.appLE U V hVU).hom
  have hbot : ∀ (E' : MMP.Mori.PrimeDivisor X) (h' : E'.genericPoint ∈ V),
      f E'.genericPoint = genericPoint Y →
        Ideal.comap α (hV.primeIdealOf ⟨_, h'⟩).asIdeal = ⊥ := by
    intro E' h' hg'
    have hg : genericPoint Y ∈ U := hg' ▸ hVU h'
    rw [← primeIdealOf_genericPoint_eq_bot hU hg]
    exact congrArg PrimeSpectrum.asIdeal ((IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU
      h').trans (congrArg hU.primeIdealOf (Subtype.ext hg')))
  set Q := (hV.primeIdealOf ⟨_, hEV⟩).asIdeal
  obtain ⟨φ, hφQ, hφgen⟩ := exists_mem_forall_mul_mem_span_of_polyEquiv α e he Q
  haveI := E.isDiscreteValuationRing_localRing
  have hirr : Irreducible ((X.presheaf.germ V _ hEV).hom φ) := by
    refine irreducible_germ_of_forall_mul_mem_span hV hEV hφQ fun q hq => ?_
    obtain ⟨c, hc, hcq⟩ := hφgen q hq
    refine ⟨α c, fun hcQ => hc ?_, hcq⟩
    have : c ∈ Ideal.comap α Q := hcQ
    rwa [hbot E hEV hE, Ideal.mem_bot] at this
  have hφ0 : φ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hirr
    exact not_irreducible_zero hirr
  obtain ⟨u, hu⟩ := exists_unit_rationalFunctions_eq_germ ⟨_, hEV⟩ φ hφ0
  refine ⟨u, E.ord_eq_one_of_irreducible hirr (hu E hEV), fun E' hne hg' hE' => ?_⟩
  have h' := (E'.genericPoint_mem_iff V).mpr hE'
  haveI := E'.isDiscreteValuationRing_localRing
  refine E'.ord_eq_zero_of_isUnit (isUnit_germ_of_notMem hV h' fun hφ' => hne ?_) (hu E' h')
  have hle : Q ≤ (hV.primeIdealOf ⟨_, h'⟩).asIdeal := fun q hq => by
    obtain ⟨c, hc, hcq⟩ := hφgen q hq
    have h1 : α c * q ∈ (hV.primeIdealOf ⟨_, h'⟩).asIdeal :=
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hφ')) hcq
    refine ((hV.primeIdealOf ⟨_, h'⟩).isPrime.mem_or_mem h1).resolve_left fun h => hc ?_
    have : c ∈ Ideal.comap α (hV.primeIdealOf ⟨_, h'⟩).asIdeal := h
    rwa [hbot E' h' hg', Ideal.mem_bot] at this
  have hQne : Q ≠ ⊥ := fun h0 => hφ0 (by simpa [h0] using hφQ)
  exact (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (eq_of_primeIdealOf_le hV hEV h' hle hQne)).symm

section Cartier

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]

/-- On a quasi-compact scheme, a divisor with a Cartier multiple near every point has a Cartier
multiple. -/
private theorem exists_isCartier_nsmul_of_locally [CompactSpace X] {D : Divisor X}
    (h : ∀ x : X, ∃ n : ℕ, 0 < n ∧ ∃ W : X.Opens, x ∈ W ∧
      ∃ ψ, Divisor.IsLocalEquation ((n : ℤ) • D) W ψ) :
    ∃ n : ℕ, 0 < n ∧ Divisor.IsCartier ((n : ℤ) • D) := by
  choose n hn W hxW ψ hψ using h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (W x : Set X))
    (fun x => (W x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hxW x⟩)
  refine ⟨∏ x ∈ t, n x, Finset.prod_pos fun x _ => hn x, fun y => ?_⟩
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n hx
  refine ⟨W x, hyx, ψ x ^ (c : ℤ), ?_⟩
  have h := (hψ x).zsmul (c : ℤ)
  rw [smul_smul] at h
  rw [hc]
  push_cast
  rwa [mul_comm]

/-- A divisor whose prime divisors all have Cartier multiples has a Cartier multiple. -/
private theorem exists_isCartier_nsmul_of_forall_single
    (h : ∀ E : MMP.Mori.PrimeDivisor X, ∃ n : ℕ, 0 < n ∧
      Divisor.IsCartier ((n : ℤ) • (Finsupp.single E 1 : Divisor X)))
    (D : Divisor X) : ∃ n : ℕ, 0 < n ∧ Divisor.IsCartier ((n : ℤ) • D) := by
  refine Finsupp.induction D ⟨1, one_pos, by simpa using Divisor.isCartier_zero⟩ ?_
  intro E c f _ _ ih
  obtain ⟨n₁, hn₁, h₁⟩ := h E
  obtain ⟨n₂, hn₂, h₂⟩ := ih
  refine ⟨n₁ * n₂, Nat.mul_pos hn₁ hn₂, ?_⟩
  have e1 : ((n₁ * n₂ : ℕ) : ℤ) • (Finsupp.single E c + f) =
      ((n₂ : ℤ) * c) • ((n₁ : ℤ) • (Finsupp.single E 1 : Divisor X)) +
        (n₁ : ℤ) • ((n₂ : ℤ) • f) := by
    rw [← Finsupp.smul_single_one]
    push_cast
    module
  rw [e1]
  exact (h₁.zsmul _).add (h₂.zsmul _)

end Cartier

/-- A divisor whose coefficient on `ι Γ' = f⁻¹(Γ')` is that of `single Γ 1` at `Γ'`, and which
vanishes on prime divisors of no such form, is `single (ι Γ) 1`. -/
private theorem eq_single_of_coeff_preimage {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y)
    {ι : MMP.Mori.PrimeDivisor Y → MMP.Mori.PrimeDivisor X}
    (hι : ∀ Γ, (ι Γ).support = f ⁻¹' Γ.support) (hιinj : Function.Injective ι)
    (hιeq : ∀ E Γ, E.support = f ⁻¹' Γ.support → E = ι Γ) (Γ : MMP.Mori.PrimeDivisor Y)
    {P : Divisor X}
    (hP1 : ∀ (E : Mori.PrimeDivisor X) (Γ' : Mori.PrimeDivisor Y),
      (E.support : Set X) = f.base ⁻¹' (Γ'.support : Set Y) →
      P.coeff E = DivisorWithCoeffs.coeff (Finsupp.single Γ 1 : Divisor Y) Γ')
    (hP2 : ∀ E : Mori.PrimeDivisor X,
      (∀ Γ' : Mori.PrimeDivisor Y, (E.support : Set X) ≠ f.base ⁻¹' (Γ'.support : Set Y)) →
      P.coeff E = 0) :
    P = Finsupp.single (ι Γ) 1 := by
  refine DivisorWithCoeffs.ext' fun E' => ?_
  by_cases h : E' ∈ Set.range ι
  · obtain ⟨Γ', rfl⟩ := h
    rw [hP1 (ι Γ') Γ' (hι Γ')]
    by_cases hΓ : Γ = Γ'
    · subst hΓ
      rw [DivisorWithCoeffs.coeff_single_self, DivisorWithCoeffs.coeff_single_self]
    · rw [DivisorWithCoeffs.coeff_single_of_ne hΓ,
        DivisorWithCoeffs.coeff_single_of_ne (hιinj.ne hΓ)]
  · rw [hP2 E' (fun Γ' h' => h ⟨Γ', (hιeq _ _ h').symm⟩),
      DivisorWithCoeffs.coeff_single_of_ne]
    rintro rfl
    exact h ⟨Γ, rfl⟩

/-- If `Y` is `ℚ`-factorial, a prime divisor `E` of `Y × L` dominating `Y` has a Cartier multiple
near every point `x`: on a chart, `E - div(u)` is a combination of divisors `Γ × L`. -/
private theorem exists_isLocalEquation_nsmul_single_of_dominating {k : Type u} [Field k]
    {Y L : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (sL : L ⟶ Spec (.of k)) (hY : IsNormalVariety k sY)
    [IsLocallyNoetherian Y] [IsNormal Y]
    [IsLocallyNoetherian (pullback sY sL)] [IsNormal (pullback sY sL)]
    (hL : (∃ e : L ≅ projectiveLine k, e.hom ≫ (projectiveLine k ↘ Spec (.of k)) = sL) ∨
      ∃ e : L ≅ 𝔸(PUnit.{u + 1}; Spec (.of k)),
        e.hom ≫ (𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k)) = sL)
    [IsIntegral Y] [IsIntegral (pullback sY sL)] [CompactSpace ↥(pullback sY sL)]
    (hQF : IsQFactorial sY)
    {ι : MMP.Mori.PrimeDivisor Y → MMP.Mori.PrimeDivisor (pullback sY sL)}
    (hι : ∀ Γ, (ι Γ).support = pullback.fst sY sL ⁻¹' Γ.support) (hιinj : Function.Injective ι)
    (hιeq : ∀ E Γ, E.support = pullback.fst sY sL ⁻¹' Γ.support → E = ι Γ)
    (hgen : ∀ E ∉ Set.range ι, pullback.fst sY sL E.genericPoint = genericPoint Y)
    {E : MMP.Mori.PrimeDivisor (pullback sY sL)} (hr : E ∉ Set.range ι)
    (x : ↥(pullback sY sL)) :
    ∃ n : ℕ, 0 < n ∧ ∃ W : (pullback sY sL).Opens, x ∈ W ∧
      ∃ ψ, Divisor.IsLocalEquation
        ((n : ℤ) • (Finsupp.single E 1 : Divisor (pullback sY sL))) W ψ := by
  obtain ⟨U, hU, V, hV, hVU, hxV, e, he⟩ := exists_productChart sY sL hL x
  by_cases hEV : E.genericPoint ∈ V
  swap
  · refine ⟨1, one_pos, V, hxV, 1, fun E' hE' => ?_⟩
    have hne : E' ≠ E := by rintro rfl; exact hEV ((E'.genericPoint_mem_iff V).mpr hE')
    rw [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hne),
      smul_zero, PrimeDivisor.ord_one]
  obtain ⟨u, hordE, hord0⟩ :=
    exists_ord_eq_one_of_polyEquiv (pullback.fst sY sL) hU hV hVU e he hEV (hgen E hr)
  set N : Divisor (pullback sY sL) := Finsupp.single E 1 - principalDivisor u
  obtain ⟨n₀, hn₀, hc₀⟩ := hQF.2 (Finsupp.comapDomain ι N hιinj.injOn)
  obtain ⟨P, hP1, hP2, hP3, -⟩ := pullback_line_divisor sY sL hY hL _ _ hc₀
  have hNP : ∀ E' : MMP.Mori.PrimeDivisor (pullback sY sL), (E'.support ∩ V).Nonempty →
      N.coeff E' = P.coeff E' := by
    intro E' hE'
    by_cases hr' : E' ∈ Set.range ι
    · obtain ⟨Γ, rfl⟩ := hr'
      rw [hP1 (ι Γ) Γ (hι Γ)]
      exact (Finsupp.comapDomain_apply _ _ _ Γ).symm
    · rw [hP2 E' (fun Γ h' => hr' ⟨Γ, (hιeq _ _ h').symm⟩), DivisorWithCoeffs.coeff_sub,
        coeff_principalDivisor]
      by_cases hEE : E' = E
      · subst hEE
        rw [DivisorWithCoeffs.coeff_single_self, hordE, sub_self]
      · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hEE), hord0 E' hEE (hgen E' hr') hE',
          sub_zero]
  obtain ⟨U', hxU', ψ, hψ⟩ := hP3 x
  refine ⟨n₀, hn₀, V ⊓ U', ⟨hxV, hxU'⟩, ψ * u ^ (n₀ : ℤ), fun E' hE' => ?_⟩
  have h1 := hψ E' (hE'.mono fun z hz => ⟨hz.1, hz.2.2⟩)
  have h2 := hNP E' (hE'.mono fun z hz => ⟨hz.1, hz.2.1⟩)
  rw [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor] at h2
  rw [PrimeDivisor.ord_mul, PrimeDivisor.ord_zpow, ← h1, DivisorWithCoeffs.coeff_smul,
    DivisorWithCoeffs.coeff_smul, ← h2, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  ring

/-- Obligation (2): `Y × L` is `ℚ`-factorial when `Y` is. -/
private theorem isQFactorial_line {k : Type u} [Field k] {Y L : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) (sL : L ⟶ Spec (.of k)) (hY : IsNormalVariety k sY)
    [IsLocallyNoetherian Y] [IsNormal Y]
    [IsLocallyNoetherian (pullback sY sL)] [IsNormal (pullback sY sL)]
    (hL : (∃ e : L ≅ projectiveLine k, e.hom ≫ (projectiveLine k ↘ Spec (.of k)) = sL) ∨
      ∃ e : L ≅ 𝔸(PUnit.{u + 1}; Spec (.of k)),
        e.hom ≫ (𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k)) = sL) :
    IsQFactorial sY → IsQFactorial (pullback.fst sY sL ≫ sY) := by
  intro hQF
  obtain ⟨⟨-, -, hnvX, -, -, -⟩, -⟩ := product_line_basic sY sL hY hL
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : IsIntegral (pullback sY sL) := hnvX.1.toIsIntegral
  obtain ⟨ι, hι, hιinj, hιeq, hgen, -, -⟩ := exists_preimagePrimeDivisor sY sL hY hL
  haveI : AlgebraicGeometry.IsVariety k (pullback.fst sY sL ≫ sY) := hnvX.1
  haveI : CompactSpace ↥(pullback sY sL) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst sY sL ≫ sY)
  refine ⟨hnvX, exists_isCartier_nsmul_of_forall_single fun E => ?_⟩
  by_cases hr : E ∈ Set.range ι
  · obtain ⟨Γ, rfl⟩ := hr
    obtain ⟨n, hn, hc⟩ := hQF.2 (Finsupp.single Γ 1)
    obtain ⟨P, hP1, hP2, hP3, -⟩ := pullback_line_divisor sY sL hY hL _ _ hc
    exact ⟨n, hn, eq_single_of_coeff_preimage _ hι hιinj hιeq Γ hP1 hP2 ▸ hP3⟩
  exact exists_isCartier_nsmul_of_locally (X := pullback sY sL)
    (exists_isLocalEquation_nsmul_single_of_dominating sY sL hY hL hQF hι hιinj hιeq hgen hr)

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- **Products with a line preserve `ℚ`-factoriality.** Let `Y` be a normal variety over `k`
and `L` a `k`-scheme isomorphic to `ℙ¹_k` or `𝔸¹_k`, with `pr : Y × L ⟶ Y` the first projection.
1. If `D₀` is a Weil divisor on `Y` with `m D₀` Cartier, the divisor `pr^* D₀` (coefficient of
   `D₀` at `Γ` on `pr⁻¹(Γ)`, zero on the prime divisors dominating `Y`) exists, `m pr^* D₀` is
   Cartier, and it is the pull-back of `m D₀` along `pr` (`MMP.Mori.Divisor.IsPullback`).
2. If `Y` is `ℚ`-factorial, so is `Y × L`. -/
@[mmp "lem_mmp_indexb_product_q_factorial"]
public theorem isQFactorial_pullback_line {k : Type u} [Field k] {Y L : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) (sL : L ⟶ Spec (.of k)) (hY : IsNormalVariety k sY)
    (hL : (∃ e : L ≅ projectiveLine k, e.hom ≫ (projectiveLine k ↘ Spec (.of k)) = sL) ∨
      ∃ e : L ≅ 𝔸(PUnit.{u + 1}; Spec (.of k)),
        e.hom ≫ (𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k)) = sL) :
    letI : IsLocallyNoetherian Y :=
      @LocallyOfFiniteType.isLocallyNoetherian _ _ sY hY.1.toLocallyOfFiniteType
        (isLocallyNoetherian_Spec.mpr inferInstance)
    letI : IsNormal Y := hY.2
    letI : IsLocallyNoetherian (pullback sY sL) :=
      @LocallyOfFiniteType.isLocallyNoetherian _ _ (pullback.fst sY sL ≫ sY)
        (product_line_basic sY sL hY hL).1.2.2.1.1.toLocallyOfFiniteType
        (isLocallyNoetherian_Spec.mpr inferInstance)
    letI : IsNormal (pullback sY sL) := (product_line_basic sY sL hY hL).1.2.2.1.2
    -- (1) the pull-back of a divisor with a Cartier multiple
    (∀ (D₀ : Divisor Y) (m : ℤ), (m • D₀).IsCartier →
      ∃ D : Divisor (pullback sY sL),
        (∀ (E : Mori.PrimeDivisor (pullback sY sL)) (Γ : Mori.PrimeDivisor Y),
          (E.support : Set ↥(pullback sY sL : Scheme.{u})) =
            (pullback.fst sY sL).base ⁻¹' (Γ.support : Set Y) →
          D.coeff E = D₀.coeff Γ) ∧
        (∀ E : Mori.PrimeDivisor (pullback sY sL),
          (∀ Γ : Mori.PrimeDivisor Y, (E.support : Set ↥(pullback sY sL : Scheme.{u})) ≠
            (pullback.fst sY sL).base ⁻¹' (Γ.support : Set Y)) →
          D.coeff E = 0) ∧
        (m • D).IsCartier ∧
        ∃ hB, (m • D₀).IsPullback (pullback.fst sY sL) hB (m • D)) ∧
    -- (2) `ℚ`-factoriality
    (IsQFactorial sY → IsQFactorial (pullback.fst sY sL ≫ sY)) := by
  letI : IsLocallyNoetherian Y :=
    @LocallyOfFiniteType.isLocallyNoetherian _ _ sY hY.1.toLocallyOfFiniteType
      (isLocallyNoetherian_Spec.mpr inferInstance)
  letI : IsNormal Y := hY.2
  letI : IsLocallyNoetherian (pullback sY sL) :=
    @LocallyOfFiniteType.isLocallyNoetherian _ _ (pullback.fst sY sL ≫ sY)
      (product_line_basic sY sL hY hL).1.2.2.1.1.toLocallyOfFiniteType
      (isLocallyNoetherian_Spec.mpr inferInstance)
  letI : IsNormal (pullback sY sL) := (product_line_basic sY sL hY hL).1.2.2.1.2
  exact ⟨pullback_line_divisor sY sL hY hL, isQFactorial_line sY sL hY hL⟩

end MMP.Fourfold
