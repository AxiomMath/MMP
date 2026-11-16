module

public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
public import MMP.AlgebraicGeometry.Divisor.Canonical.TopFormGenerator
public import StacksFrontier.AlgebraicGeometry.UnitsNormalProper.Hartogs
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.StalkPrimes
public import StacksFrontier.AlgebraicGeometry.Chow.PointClosureHeightOneCorrespondence

/-!
# Uniqueness of the discrepancy

Let `X` be a normal variety of dimension `n` over a perfect field `k` (for instance a field of
characteristic zero), `Δ` a `ℚ`-divisor on `X` and `(Y, f, E)` a divisor over `X`. A rational
number `a` is the discrepancy `a(E, X, Δ)` if `m · a = ord_E(f^*τ)` for a local generator `τ` of
`𝒪_X(m(K + Δ))` on an open set containing `f(η_E)` (`MMP.Mori.IsDiscrepancy`). This file shows
that this number is unique.

A birational morphism `f : Y ⟶ X` is an open immersion on a dense open subset, so it induces an
isomorphism of function fields `f^* : k(X) ≅ k(Y)`. This extension is formally étale, so a
generator `ω` of the line `Ω^n_{k(X)/k}` pulls back to a generator of `Ω^n_{k(Y)/k}` and the
pull-back of forms is `f^*(c · ω^{⊗m}) = f^*(c) · (f^*ω)^{⊗m}`. The same holds in characteristic
zero for a dominant morphism of varieties of the same dimension. Along a basis `b` of
`Ω^n_{k(X)/k}` every order of a form is affine in the coordinate: there are integers `N_Γ` and
`N_E` with `ord_Γ(c · b^{⊗m}) = v_Γ(c) + m N_Γ` and `ord_E(f^*(c · b^{⊗m})) = v_E(f^*c) + m N_E`.

Given two local generators `τ = c · b^{⊗m}` and `τ' = c' · b^{⊗m'}`, the rational function
`g = c^{m'} c'^{-m}` has order `m' ord_Γ(τ) - m ord_Γ(τ') = 0` along every prime divisor `Γ`
through `f(η_E)`. By algebraic Hartogs for the Noetherian normal domain `𝒪_{X,f(η_E)}` it is a
unit there, so `f^*g` is a unit of `𝒪_{Y,E}` and `v_E(f^*g) = 0`, which is
`m m' (a - a') = 0`.

## Main definitions

* `MMP.Mori.discrepancy`: the discrepancy `a(E, X, Δ)`, given that it exists.

## Main results

* `MMP.Mori.IsBirationalMorphism.functionFieldMap_bijective`: a birational morphism induces an
  isomorphism of function fields.
* `MMP.Mori.exists_isPullbackGenerator_of_bijective`,
  `MMP.Mori.exists_isPullbackGenerator_of_topologicalKrullDim_eq`: pull-back generators exist
  along a birational morphism over a perfect field, and along a dominant morphism of varieties of
  the same dimension in characteristic zero, so `MMP.Mori.pullbackRationalPluriForms` is the
  pull-back of forms.
* `MMP.Mori.PrimeDivisor.exists_ordForm_eq_ord_add_mul`,
  `MMP.Mori.DivisorOver.exists_ordPullback_eq`: orders of forms along a basis.
* `MMP.Mori.exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero`: algebraic Hartogs at a
  point of a normal integral scheme.
* `MMP.Mori.IsDiscrepancy.eq`, `MMP.Mori.IsDiscrepancyNoBoundary.eq`: uniqueness of the
  discrepancy, `MMP.Mori.existsUnique_isDiscrepancy`, and `MMP.Mori.isDiscrepancy_discrepancy`,
  `MMP.Mori.discrepancy_eq_iff`, `MMP.Mori.IsDiscrepancy.discrepancy_eq`.
* `MMP.Mori.pullbackRationalPluriForms_id`: the pull-back along the identity is the identity.
* `MMP.Mori.IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor`, `MMP.Mori.discrepancy_ofPrimeDivisor`:
  a prime divisor `P` of `X`, regarded as `(X, 𝟙_X, P)`, has discrepancy `-coeff_P(Δ)` when the
  discrepancy exists.

## Implementation notes

The ratio `τ^{⊗m'} / τ'^{⊗m}` of the source is the rational function `c^{m'} c'^{-m}` of the
coordinates along a fixed basis `b`; no tensor product of forms is needed. The field `k` is
assumed perfect, which is what the orders of forms along a prime divisor need
(`MMP.Mori.PrimeDivisor.ordForm_smul`). The value `MMP.Mori.discrepancy` takes the existence of
a discrepancy as an argument.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.25
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace MMP.Mori

/-! ### Birational morphisms induce isomorphisms of function fields -/

/-- If `f : Y ⟶ X` restricts to an open immersion on a nonempty open `W ⊆ Y`, the extension of
function fields `f^* : k(X) → k(Y)` is bijective. -/
theorem functionFieldMap_bijective_of_isOpenImmersion {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (f : Y ⟶ X) [IsDominant f] (W : Y.Opens) (hW : (W : Set Y).Nonempty)
    [IsOpenImmersion (W.ι ≫ f)] : Function.Bijective (functionFieldMap f) := by
  have hη : genericPoint Y ∈ W :=
    ((genericPoint_spec Y).mem_open_set_iff W.isOpen).mpr (by simpa using hW)
  let y : W.toScheme := ⟨genericPoint Y, hη⟩
  have h1 : IsIso ((W.ι ≫ f).stalkMap y) := inferInstance
  rw [Scheme.Hom.stalkMap_comp] at h1
  have : IsIso (f.stalkMap (W.ι y)) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ (f.stalkMap (W.ι y)) (W.ι.stalkMap y) _ h1
  have : IsIso (f.stalkMap (genericPoint Y)) := this
  exact ConcreteCategory.bijective_of_isIso
    ((X.presheaf.stalkCongr (Inseparable.of_eq (map_genericPoint_of_isDominant f).symm)).hom ≫
      f.stalkMap (genericPoint Y))

/-- **A birational morphism induces an isomorphism of function fields**: for a birational
morphism `f : Y ⟶ X` of integral schemes, `f^* : k(X) → k(Y)` is bijective. -/
theorem IsBirationalMorphism.functionFieldMap_bijective {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] {f : Y ⟶ X} [IsDominant f] (hf : IsBirationalMorphism f) :
    Function.Bijective (functionFieldMap f) := by
  obtain ⟨e, he⟩ := hf
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff] at he
  obtain ⟨W, hW, hWe, hWf, h⟩ := he
  simp only [Scheme.PartialMap.restrict_hom] at h
  have he' : IsOpenImmersion e.toPartialMap.hom := by
    change IsOpenImmersion (e.iso.hom ≫ e.target.ι)
    infer_instance
  have hι : IsOpenImmersion (W.ι ≫ f) := by
    have : W.ι ≫ f = Y.homOfLE hWf ≫ f.toPartialMap.hom := by
      change W.ι ≫ f = (Y.homOfLE (le_top : W ≤ ⊤) ≫ Y.topIso.hom) ≫ f
      simp only [Scheme.topIso_hom, Scheme.homOfLE_ι]
    rw [this, ← h]
    infer_instance
  exact functionFieldMap_bijective_of_isOpenImmersion f W hW.nonempty

/-! ### The pull-back of forms along a birational morphism -/

section Pullback

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X)
  [IsIntegral X] [IsIntegral Y] [IsDominant f]

/-- A bijective extension of function fields `f^* : k(X) → k(Y)`, as an isomorphism of
`k`-algebras for the `k`-structure `f ≫ s_X` of `Y`. -/
def functionFieldAlgEquiv (hf : Function.Bijective (functionFieldMap f)) :
    letI := functionFieldAlgebra sX
    letI := functionFieldAlgebra (f ≫ sX)
    X.functionField ≃ₐ[k] Y.functionField :=
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra (f ≫ sX)
  letI := functionFieldMapAlgebra f
  haveI := isScalarTower_functionFieldMap sX f
  { RingEquiv.ofBijective (functionFieldMap f) hf with
    commutes' := fun c =>
      (IsScalarTower.algebraMap_apply k X.functionField Y.functionField c).symm }

@[simp]
theorem functionFieldAlgEquiv_apply (hf : Function.Bijective (functionFieldMap f))
    (x : X.functionField) :
    letI := functionFieldAlgebra sX
    letI := functionFieldAlgebra (f ≫ sX)
    functionFieldAlgEquiv sX f hf x = functionFieldMap f x :=
  rfl

/-- If `f^* : k(X) → k(Y)` is bijective, `k(X)` and `k(Y)` have the same transcendence degree
over `k`. -/
theorem trdeg_functionField_eq_of_bijective (hf : Function.Bijective (functionFieldMap f)) :
    letI := functionFieldAlgebra sX
    letI := functionFieldAlgebra (f ≫ sX)
    Algebra.trdeg k X.functionField = Algebra.trdeg k Y.functionField := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  exact (functionFieldAlgEquiv sX f hf).trdeg_eq

omit [IsDominant f] in
/-- If `X` and `Y` are integral, locally of finite type over `k` and of the same dimension `d`,
then `k(X)` and `k(Y)` have the same transcendence degree over `k`. -/
theorem trdeg_functionField_eq_of_topologicalKrullDim_eq [LocallyOfFiniteType sX]
    [LocallyOfFiniteType (f ≫ sX)] {d : ℕ} (hX : topologicalKrullDim X = d)
    (hY : topologicalKrullDim Y = d) :
    letI := functionFieldAlgebra sX
    letI := functionFieldAlgebra (f ≫ sX)
    Algebra.trdeg k X.functionField = Algebra.trdeg k Y.functionField := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  have h1 : Cardinal.toENat (Algebra.trdeg k X.functionField) = d :=
    mod_cast (toENat_trdeg_functionField (sX := sX)).trans hX
  have h2 : Cardinal.toENat (Algebra.trdeg k Y.functionField) = d :=
    mod_cast (toENat_trdeg_functionField (sX := f ≫ sX)).trans hY
  rw [Cardinal.toENat_eq_natCast] at h1 h2
  rw [h1, h2]

/-- **Pull-back generators along a birational extension.** If `X` is integral and locally of
finite type over a perfect field `k`, `trdeg_k k(X) = d`, and `f^* : k(X) → k(Y)` is bijective
(for instance `f` birational, `MMP.Mori.IsBirationalMorphism.functionFieldMap_bijective`), then
`Ω^d_{k(X)/k}` has a generator whose pull-back generates `Ω^d_{k(Y)/k}`. -/
theorem exists_isPullbackGenerator_of_bijective [PerfectField k] [LocallyOfFiniteType sX]
    (hf : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d) :
    letI := functionFieldAlgebra sX
    letI := functionFieldAlgebra (f ≫ sX)
    letI := functionFieldMapAlgebra f
    haveI := isScalarTower_functionFieldMap sX f
    ∃ ω : ⋀[X.functionField]^d Ω[X.functionField⁄k], IsPullbackGenerator Y.functionField ω := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  have : Algebra.FormallyEtale X.functionField Y.functionField :=
    Algebra.FormallyEtale.of_equiv
      (AlgEquiv.ofBijective (Algebra.ofId X.functionField Y.functionField) hf)
  have := essFiniteType_functionField (sX := sX)
  have : FiniteDimensional X.functionField Ω[X.functionField⁄k] :=
    (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k X.functionField).1
  exact exists_isPullbackGenerator_of_formallyEtale
    ((finrank_kaehlerDifferential_eq_trdeg k X.functionField).trans hd)

/-- **Pull-back generators along a dominant morphism of varieties of the same dimension**, in
characteristic zero: if `X` and `Y` are integral, locally of finite type over `k` and of the same
dimension `d`, then `Ω^d_{k(X)/k}` has a generator whose pull-back generates `Ω^d_{k(Y)/k}`. -/
theorem exists_isPullbackGenerator_of_topologicalKrullDim_eq [CharZero k]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType (f ≫ sX)] {d : ℕ}
    (hX : topologicalKrullDim X = d) (hY : topologicalKrullDim Y = d) :
    letI := functionFieldAlgebra sX
    letI := functionFieldAlgebra (f ≫ sX)
    letI := functionFieldMapAlgebra f
    haveI := isScalarTower_functionFieldMap sX f
    ∃ ω : ⋀[X.functionField]^d Ω[X.functionField⁄k], IsPullbackGenerator Y.functionField ω := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  have := essFiniteType_functionField (sX := sX)
  exact exists_isPullbackGenerator (trdeg_functionField_eq_of_topologicalKrullDim_eq sX f hX hY)
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq hX)

end Pullback

/-! ### The order of a form along a fixed basis of the top forms -/

section OrderAlongBasis

variable {K : Type*} [Field K] {v : K → ℤ}

/-- A function `v : K → ℤ` turning products of nonzero elements into sums satisfies
`v(x^n) = n · v(x)`. -/
theorem map_zpow_of_map_mul (hmul : ∀ x y : K, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y)
    {x : K} (hx : x ≠ 0) (n : ℤ) : v (x ^ n) = n * v x := by
  have h1 : v 1 = 0 := by simpa using hmul 1 1 one_ne_zero one_ne_zero
  have hnat : ∀ n : ℕ, v (x ^ n) = n * v x := by
    intro n
    induction n with
    | zero => simp [h1]
    | succ n ih =>
      rw [pow_succ, hmul _ _ (pow_ne_zero _ hx) hx, ih]
      push_cast
      ring
  have hinv : ∀ y : K, y ≠ 0 → v y⁻¹ = -v y := by
    intro y hy
    have := hmul y y⁻¹ hy (inv_ne_zero hy)
    rw [mul_inv_cancel₀ hy, h1] at this
    omega
  cases n with
  | ofNat n => simpa using hnat n
  | negSucc n =>
    rw [zpow_negSucc, hinv _ (pow_ne_zero _ hx), hnat, Int.negSucc_eq]
    push_cast
    ring

variable {k : Type*} [CommRing k] [Algebra k K] {A : Type*} [CommRing A] [Algebra k A]
  [Algebra A K] [IsScalarTower k A K] [IsFractionRing A K] {d : ℕ}

omit [IsFractionRing A K] in
/-- The coordinate of a nonzero form along a basis is nonzero. -/
theorem repr_ne_zero_of_ne_zero (b : Module.Basis Unit K (⋀[K]^d Ω[K⁄k])) {m : ℤ}
    {τ : PluriForms k K d m} (hτ : τ ≠ 0) : (ZTensorPower.basis b m).repr τ () ≠ 0 := by
  intro h
  apply hτ
  rw [← basis_unit_repr_smul (ZTensorPower.basis b m) τ, h, zero_smul]

/-- **The order of a form along a basis.** Let `A ⊆ K` have a generator of `Ω^d_{A/k}` with
nonzero image in `Ω^d_{K/k}`, and let `v` turn products of nonzero elements into sums and be
trivial on the units of `A`. For a basis `b` of the line `Ω^d_{K/k}` there is an integer `N`
(the order of `b`) with `ordAt A v τ = v(τ / b^{⊗m}) + m · N` for every nonzero `m`-canonical
form `τ` and every `m`. -/
theorem exists_ordAt_eq_add_mul (hmul : ∀ x y : K, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y)
    (hunit : ∀ a : A, IsUnit a → v (algebraMap A K a) = 0)
    (h : ∃ σ : ⋀[A]^d Ω[A⁄k], Submodule.span A {σ} = ⊤ ∧ topFormsMap k A K d σ ≠ 0)
    (b : Module.Basis Unit K (⋀[K]^d Ω[K⁄k])) :
    ∃ N : ℤ, ∀ (m : ℤ) (τ : PluriForms k K d m), τ ≠ 0 →
      ordAt A v τ = v ((ZTensorPower.basis b m).repr τ ()) + m * N := by
  obtain ⟨σ, hσ, h0⟩ := h
  set a := (topFormsBasis A hσ h0).repr (b ()) ()
  have hb : b () = a • topFormsBasis A hσ h0 () := (basis_unit_repr_smul _ _).symm
  have ha : a ≠ 0 := by
    intro h
    rw [h, zero_smul] at hb
    exact b.ne_zero () hb
  refine ⟨v a, fun m τ hτ => ?_⟩
  have hr := ZTensorPower.basis_repr_of_eq_smul hb m τ
  have hfc : formCoeff A hσ h0 τ = a ^ m * (ZTensorPower.basis b m).repr τ () := by
    rw [hr, formCoeff, ← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ ha), one_mul]
  rw [ordAt_eq hmul hunit hσ h0, hfc, hmul _ _ (zpow_ne_zero _ ha) (repr_ne_zero_of_ne_zero b hτ),
    map_zpow_of_map_mul hmul ha]
  ring

end OrderAlongBasis

/-! ### The coordinate of a pull-back -/

section PullbackCoordinate

variable {k : Type*} [CommRing k] {K K' : Type*} [Field K] [Field K'] [Algebra k K]
  [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] {d : ℕ}

/-- Along a pull-back generator `ω`, the coordinate of `u^*τ` along `(u^*ω)^{⊗m}` is the image
`u(τ / ω^{⊗m})` of the coordinate of `τ` along `ω^{⊗m}`. -/
theorem repr_pullbackFormsAlong {ω : ⋀[K]^d Ω[K⁄k]} (hω : IsPullbackGenerator K' ω) (m : ℤ)
    (τ : PluriForms k K d m) :
    (ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) m).repr
        (pullbackFormsAlong hω m τ) () =
      algebraMap K K'
        ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) := by
  simp [pullbackFormsAlong, Algebra.smul_def]

end PullbackCoordinate

/-! ### Orders of forms and units at a point -/

section Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]

/-- **The order of a form along a basis**, on a normal integral scheme locally of finite type
over a perfect field `k`, with `d = trdeg_k k(X)`: for a basis `b` of `Ω^d_{k(X)/k}` and a prime
divisor `Γ` there is an integer `N` with `ord_Γ(τ) = v_Γ(τ / b^{⊗m}) + m · N` for every `m` and
every nonzero rational `m`-canonical form `τ`. -/
theorem PrimeDivisor.exists_ordForm_eq_ord_add_mul [PerfectField k] [IsLocallyNoetherian X]
    [IsNormal X] [LocallyOfFiniteType sX] (Γ : PrimeDivisor X) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    (b : letI := functionFieldAlgebra sX
      Module.Basis Unit X.functionField (⋀[X.functionField]^d Ω[X.functionField⁄k])) :
    letI := functionFieldAlgebra sX
    ∃ N : ℤ, ∀ (m : ℤ) (τ : RationalPluriForms sX d m), τ ≠ 0 →
      Γ.ordForm τ = X.ord ((ZTensorPower.basis b m).repr τ ()) Γ.genericPoint + m * N := by
  let := stalkAlgebra sX Γ.genericPoint
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX Γ.genericPoint
  exact exists_ordAt_eq_add_mul (k := k) Γ.ord_mul_of_ne_zero
    (fun _ ha => Γ.ord_algebraMap_of_isUnit ha) (Γ.exists_topForms_generator hd) b

/-- The generization `𝒪_{X,x} ⟶ 𝒪_{X,ξ}` to a point `ξ ⤳ x` commutes with the maps to the
function field. -/
theorem algebraMap_stalkSpecializes {ξ x : X} (h : ξ ⤳ x) (t : X.presheaf.stalk x) :
    algebraMap (X.presheaf.stalk ξ) X.functionField ((X.presheaf.stalkSpecializes h).hom t) =
      algebraMap (X.presheaf.stalk x) X.functionField t := by
  change (X.presheaf.stalkSpecializes h ≫ X.presheaf.stalkSpecializes _).hom t =
    (X.presheaf.stalkSpecializes _).hom t
  rw [TopCat.Presheaf.stalkSpecializes_comp]

variable [IsLocallyNoetherian X]

/-- For `g ≠ 0`, the order of vanishing of `g ^ n` at `z` is `n · v_z(g)`. -/
theorem ord_zpow (z : X) {g : X.functionField} (hg : g ≠ 0) (n : ℤ) :
    X.ord (g ^ n) z = n * X.ord g z :=
  map_zpow_of_map_mul (v := fun f => X.ord f z) (fun _ _ => Scheme.ord_mul) hg n

variable [IsNormal X]

/-- **Algebraic Hartogs at a point.** On a normal integral locally Noetherian scheme, a rational
function `g ≠ 0` with `v_Γ(g) = 0` for every prime divisor `Γ` through `x` lies in `𝒪_{X,x}`. -/
theorem exists_algebraMap_stalk_eq_of_forall_ord_eq_zero (x : X) {g : X.functionField}
    (hg : g ≠ 0) (h : ∀ Γ : PrimeDivisor X, x ∈ Γ.support → X.ord g Γ.genericPoint = 0) :
    ∃ r : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField r = g := by
  have : IsIntegrallyClosed (X.presheaf.stalk x) := IsNormal.stalk_normal x
  refine Stacks.AlgebraicGeometry.UnitsNormalProper.exists_algebraMap_eq_of_forall_height_eq_one
    X.functionField fun q hq => ?_
  have hξ1 : Order.coheight (X.fromSpecStalk x q) = 1 :=
    (Stacks.Chow.coheight_fromSpecStalk_eq_height x q).trans hq
  set E : PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hξ1
  have hEξ : E.genericPoint = X.fromSpecStalk x q :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hξ1
  have hspec : E.genericPoint ⤳ x := hEξ ▸ Stacks.Chow.specializes_fromSpecStalk x q
  have hxE : x ∈ E.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact specializes_iff_mem_closure.mp hspec
  have hv : E.divisorialValuation g ≤ 1 := by
    rw [E.divisorialValuation_eq_exp_neg_ord hg, h E hxE, neg_zero, WithZero.exp_zero]
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
  rwa [algebraMap_stalkSpecializes, algebraMap_stalkSpecializes] at h2

/-- **Algebraic Hartogs at a point, for units.** On a normal integral locally Noetherian scheme,
a rational function `g ≠ 0` with `v_Γ(g) = 0` for every prime divisor `Γ` through `x` is the
image of a unit of `𝒪_{X,x}`. -/
theorem exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero (x : X) {g : X.functionField}
    (hg : g ≠ 0) (h : ∀ Γ : PrimeDivisor X, x ∈ Γ.support → X.ord g Γ.genericPoint = 0) :
    ∃ a : X.presheaf.stalk x, IsUnit a ∧
      algebraMap (X.presheaf.stalk x) X.functionField a = g := by
  obtain ⟨r, hr⟩ := exists_algebraMap_stalk_eq_of_forall_ord_eq_zero x hg h
  obtain ⟨r', hr'⟩ := exists_algebraMap_stalk_eq_of_forall_ord_eq_zero x (inv_ne_zero hg)
    fun Γ hΓ => by
      have := ord_zpow Γ.genericPoint hg (-1)
      rw [zpow_neg, zpow_one] at this
      rw [this, h Γ hΓ, mul_zero]
  have h1 : r * r' = 1 := IsFractionRing.injective (X.presheaf.stalk x) X.functionField (by
    rw [map_mul, hr, hr', mul_inv_cancel₀ hg, map_one])
  exact ⟨r, isUnit_iff_exists_inv.mpr ⟨r', h1⟩, hr⟩

end Scheme

/-- The extension of function fields `f^* : k(X) → k(Y)` of a dominant morphism of integral
schemes extends the local homomorphism `f^♯_y : 𝒪_{X,f(y)} ⟶ 𝒪_{Y,y}`. -/
theorem functionFieldMap_algebraMap_stalk {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsDominant f] (y : Y) (a : X.presheaf.stalk (f y)) :
    functionFieldMap f (algebraMap (X.presheaf.stalk (f y)) X.functionField a) =
      algebraMap (Y.presheaf.stalk y) Y.functionField ((f.stalkMap y).hom a) := by
  have hy : genericPoint Y ⤳ y := (genericPoint_spec Y).specializes trivial
  have hX : genericPoint X ⤳ f y := (genericPoint_spec X).specializes trivial
  have hη : f (genericPoint Y) ⤳ genericPoint X := by rw [map_genericPoint_of_isDominant f]
  change (X.presheaf.stalkSpecializes hX ≫ X.presheaf.stalkSpecializes hη ≫
      f.stalkMap (genericPoint Y)).hom a = (f.stalkMap y ≫ Y.presheaf.stalkSpecializes hy).hom a
  rw [TopCat.Presheaf.stalkSpecializes_comp_assoc, ← Scheme.Hom.stalkSpecializes_stalkMap]

/-! ### The order of the pull-back along a divisor over `X` -/

section DivisorOver

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- **The order of a pull-back along a basis.** Let `X` be a normal variety of dimension `n` over
a perfect field `k` and `(Y, f, E)` a divisor over `X`. There are a basis `b` of `Ω^n_{k(X)/k}`
and an integer `N` (the order of `f^*b` along `E`) with
`ord_E(f^*τ) = v_E(f^*(τ / b^{⊗m})) + m · N` for every `m` and every nonzero rational
`m`-canonical form `τ` on `X`. -/
theorem DivisorOver.exists_ordPullback_eq [PerfectField k] (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) (D : DivisorOver k sX) :
    letI := functionFieldAlgebra sX
    haveI := D.isIntegral
    haveI := D.isLocallyNoetherian
    haveI := D.isDominant
    ∃ (b : Module.Basis Unit X.functionField (⋀[X.functionField]^n Ω[X.functionField⁄k]))
      (N : ℤ), ∀ (m : ℤ) (τ : RationalPluriForms sX n m), τ ≠ 0 →
        D.ordPullback τ =
          D.Y.ord (functionFieldMap D.f ((ZTensorPower.basis b m).repr τ ())) D.E.genericPoint +
            m * N := by
  let := functionFieldAlgebra sX
  have := D.isIntegral
  have := D.isDominant
  have := D.isLocallyNoetherian
  have := D.isNormal
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (D.f ≫ sX) := D.isNormalVariety.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have hbij := D.isBirationalMorphism.functionFieldMap_bijective
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX D.f hbij hd
  let := functionFieldAlgebra (D.f ≫ sX)
  let := functionFieldMapAlgebra D.f
  have := isScalarTower_functionFieldMap sX D.f
  have hdY : (Algebra.trdeg k D.Y.functionField).toNat = n := by
    rw [← trdeg_functionField_eq_of_bijective sX D.f hbij]
    exact hd
  obtain ⟨N, hN⟩ := D.E.exists_ordForm_eq_ord_add_mul (sX := D.f ≫ sX) hdY
    (basisOfSpanSingleton hω.2.1 hω.2.2)
  refine ⟨basisOfSpanSingleton hω.1 hω.ne_zero, N, fun m τ hτ => ?_⟩
  have hpull : pullbackRationalPluriForms sX D.f τ = pullbackFormsAlong hω m τ :=
    pullbackForms_eq hω m τ
  have hrepr := repr_pullbackFormsAlong hω m τ
  have hne : pullbackRationalPluriForms sX D.f τ ≠ 0 := by
    intro h0
    have h0' : pullbackFormsAlong hω m τ = 0 := hpull ▸ h0
    have h1 : algebraMap X.functionField D.Y.functionField
        ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
      rw [← hrepr, h0']
      simp
    exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)
  change D.E.ordForm (pullbackRationalPluriForms sX D.f τ) = _
  rw [hN m _ hne, hpull, hrepr]
  rfl

/-- **Uniqueness of the discrepancy.** On a normal variety `X` over a perfect field `k`, a divisor
`(Y, f, E)` over `X` has at most one discrepancy `a(E, X, Δ)`. -/
theorem IsDiscrepancy.eq [PerfectField k] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    {D : DivisorOver k sX} {a a' : ℚ} (ha : IsDiscrepancy sX n K Δ D a)
    (ha' : IsDiscrepancy sX n K Δ D a') : a = a' := by
  obtain ⟨hX, hK, m, hm, -, U, hU, τ, hτ, hτa⟩ := ha
  obtain ⟨-, -, m', hm', -, U', hU', τ', hτ', hτa'⟩ := ha'
  let := functionFieldAlgebra sX
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isDominant
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hn := hK.topologicalKrullDim_eq
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨b, N, hN⟩ := D.exists_ordPullback_eq hX hn
  set c := (ZTensorPower.basis b m).repr τ ()
  set c' := (ZTensorPower.basis b m').repr τ' ()
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hτ.1
  have hc' : c' ≠ 0 := repr_ne_zero_of_ne_zero b hτ'.1
  set g : X.functionField := c ^ (m' : ℤ) * c' ^ (-(m : ℤ)) with hg_def
  have hg : g ≠ 0 := mul_ne_zero (zpow_ne_zero _ hc) (zpow_ne_zero _ hc')
  have hord : ∀ Γ : PrimeDivisor X, D.f D.E.genericPoint ∈ Γ.support →
      X.ord g Γ.genericPoint = 0 := by
    intro Γ hΓ
    obtain ⟨NΓ, hNΓ⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
    have f1 : (Γ.ordForm τ : ℚ) = (X.ord c Γ.genericPoint : ℚ) + m * NΓ := mod_cast hNΓ m τ hτ.1
    have f2 : (Γ.ordForm τ' : ℚ) = (X.ord c' Γ.genericPoint : ℚ) + m' * NΓ :=
      mod_cast hNΓ m' τ' hτ'.1
    rw [hg_def, Scheme.ord_mul (zpow_ne_zero _ hc) (zpow_ne_zero _ hc'), ord_zpow _ hc,
      ord_zpow _ hc']
    have : ((m' : ℚ) * X.ord c Γ.genericPoint + -(m : ℚ) * X.ord c' Γ.genericPoint) = 0 := by
      linear_combination (m' : ℚ) * hτ.2 Γ ⟨_, hΓ, hU⟩ - (m : ℚ) * hτ'.2 Γ ⟨_, hΓ, hU'⟩ -
        (m' : ℚ) * f1 + (m : ℚ) * f2
    exact_mod_cast this
  obtain ⟨u, hu, hug⟩ := exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero _ hg hord
  have hY0 : D.Y.ord (functionFieldMap D.f g) D.E.genericPoint = 0 := by
    rw [← hug, functionFieldMap_algebraMap_stalk]
    exact D.E.ord_algebraMap_of_isUnit (hu.map _)
  have hfc : functionFieldMap D.f c ≠ 0 := (map_ne_zero _).mpr hc
  have hfc' : functionFieldMap D.f c' ≠ 0 := (map_ne_zero _).mpr hc'
  rw [hg_def, map_mul, map_zpow₀, map_zpow₀,
    Scheme.ord_mul (zpow_ne_zero _ hfc) (zpow_ne_zero _ hfc'), ord_zpow _ hfc, ord_zpow _ hfc']
    at hY0
  have hY0' : ((m' : ℚ) * D.Y.ord (functionFieldMap D.f c) D.E.genericPoint +
      -(m : ℚ) * D.Y.ord (functionFieldMap D.f c') D.E.genericPoint) = 0 := mod_cast hY0
  have h1 : (D.ordPullback τ : ℚ) =
      (D.Y.ord (functionFieldMap D.f c) D.E.genericPoint : ℚ) + m * N := mod_cast hN m τ hτ.1
  have h2 : (D.ordPullback τ' : ℚ) =
      (D.Y.ord (functionFieldMap D.f c') D.E.genericPoint : ℚ) + m' * N := mod_cast hN m' τ' hτ'.1
  have key : (m : ℚ) * m' * (a - a') = 0 := by
    linear_combination (m' : ℚ) * hτa - (m : ℚ) * hτa' + (m' : ℚ) * h1 - (m : ℚ) * h2 + hY0'
  have hm0 : (m : ℚ) * m' ≠ 0 := by positivity
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hm0)

/-- **Uniqueness of the discrepancy without boundary**: an exceptional divisor over a normal
variety over a perfect field has at most one discrepancy `a(E, X)`. -/
theorem IsDiscrepancyNoBoundary.eq [PerfectField k] {n : ℕ} {K : Divisor X}
    {D : DivisorOver k sX} {a a' : ℚ} (ha : IsDiscrepancyNoBoundary sX n K D a)
    (ha' : IsDiscrepancyNoBoundary sX n K D a') : a = a' :=
  (isDiscrepancyNoBoundary_iff.mp ha).2.eq (isDiscrepancyNoBoundary_iff.mp ha').2

/-- On a normal variety over a perfect field, the discrepancy `a(E, X, Δ)` is unique when it
exists. -/
theorem existsUnique_isDiscrepancy [PerfectField k] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    {D : DivisorOver k sX} (h : ∃ a, IsDiscrepancy sX n K Δ D a) :
    ∃! a, IsDiscrepancy sX n K Δ D a :=
  let ⟨a, ha⟩ := h
  ⟨a, ha, fun _ ha' => ha'.eq ha⟩

variable (sX) in
/-- **The discrepancy** `a(E, X, Δ)` of a divisor `(Y, f, E)` over `X`, given that some rational
number is the discrepancy (`MMP.Mori.IsDiscrepancy`); over a perfect field it is the unique such
number (`MMP.Mori.discrepancy_eq_iff`). -/
def discrepancy (n : ℕ) (K : Divisor X) (Δ : QDivisor X) (D : DivisorOver k sX)
    (h : ∃ a, IsDiscrepancy sX n K Δ D a) : ℚ :=
  h.choose

/-- The value `MMP.Mori.discrepancy` is a discrepancy `a(E, X, Δ)`. -/
theorem isDiscrepancy_discrepancy {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    {D : DivisorOver k sX} (h : ∃ a, IsDiscrepancy sX n K Δ D a) :
    IsDiscrepancy sX n K Δ D (discrepancy sX n K Δ D h) :=
  h.choose_spec

/-- Over a perfect field, `a` is the discrepancy `a(E, X, Δ)` exactly when it is the value
`MMP.Mori.discrepancy`. -/
theorem discrepancy_eq_iff [PerfectField k] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    {D : DivisorOver k sX} (h : ∃ a, IsDiscrepancy sX n K Δ D a) {a : ℚ} :
    discrepancy sX n K Δ D h = a ↔ IsDiscrepancy sX n K Δ D a :=
  ⟨fun e => e ▸ isDiscrepancy_discrepancy h, fun ha => (isDiscrepancy_discrepancy h).eq ha⟩

/-- Over a perfect field, if `a` is the discrepancy `a(E, X, Δ)` then `MMP.Mori.discrepancy` equals
`a`. -/
theorem IsDiscrepancy.discrepancy_eq [PerfectField k] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    {D : DivisorOver k sX} {a : ℚ} (ha : IsDiscrepancy sX n K Δ D a) :
    discrepancy sX n K Δ D ⟨a, ha⟩ = a :=
  (discrepancy_eq_iff _).mpr ha

end DivisorOver

/-! ### The pull-back along the identity -/

section IdentityAlgebra

variable {k : Type*} [CommRing k] {K : Type*} [Field K] [Algebra k K] (e : K →+* K)

/-- If a ring endomorphism `e` of `K` is the identity, the map `Ω_{K/k} → Ω_{K/k}` it induces
(for `K` a `K`-algebra through `e`) is the identity. -/
theorem kaehlerDifferential_map_eq_self (he : ∀ a, e a = a) (w : Ω[K⁄k]) :
    letI := e.toAlgebra
    haveI : @IsScalarTower k K K _ e.toAlgebra.toSMul _ :=
      IsScalarTower.of_algebraMap_eq fun _ => (he _).symm
    KaehlerDifferential.map k k K K w = w := by
  obtain rfl : e = RingHom.id K := RingHom.ext he
  have hw : w ∈ Submodule.span K (Set.range (KaehlerDifferential.D k K)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, rfl⟩ := hw
    rw [KaehlerDifferential.map_D]
    rfl
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul a x _ hx => rw [map_smul, hx]

/-- If a ring endomorphism `e` of `K` is the identity, the pull-back `Ω^d_{K/k} → Ω^d_{K/k}` it
induces is the identity. -/
theorem topFormsMap_eq_self (he : ∀ a, e a = a) {d : ℕ} (ω : ⋀[K]^d Ω[K⁄k]) :
    letI := e.toAlgebra
    haveI : @IsScalarTower k K K _ e.toAlgebra.toSMul _ :=
      IsScalarTower.of_algebraMap_eq fun _ => (he _).symm
    topFormsMap k K K d ω = ω := by
  have hΩ := kaehlerDifferential_map_eq_self (k := k) e he
  obtain rfl : e = RingHom.id K := RingHom.ext he
  have hω : ω ∈ Submodule.span K (Set.range (exteriorPower.ιMulti K d (M := Ω[K⁄k]))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hω using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨v, rfl⟩ := hw
    rw [topFormsMap_ιMulti]
    exact congrArg _ (funext fun i => hΩ (v i))
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul a x _ hx => rw [map_smul, hx]

/-- If a ring endomorphism `e` of `K` is the identity, the pull-back of `m`-canonical forms along
`e` is the identity, as soon as `Ω^d_{K/k}` is a line. -/
theorem pullbackForms_eq_self (he : ∀ a, e a = a) {d : ℕ} {ω : ⋀[K]^d Ω[K⁄k]}
    (hω : Submodule.span K {ω} = ⊤) (h0 : ω ≠ 0) (m : ℤ) (τ : PluriForms k K d m) :
    letI := e.toAlgebra
    haveI : @IsScalarTower k K K _ e.toAlgebra.toSMul _ :=
      IsScalarTower.of_algebraMap_eq fun _ => (he _).symm
    pullbackForms (K' := K) m τ = τ := by
  have hT := topFormsMap_eq_self (k := k) e he ω
  obtain rfl : e = RingHom.id K := RingHom.ext he
  let := (RingHom.id K).toAlgebra
  have : @IsScalarTower k K K _ (RingHom.id K).toAlgebra.toSMul _ :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hgen : IsPullbackGenerator K ω := ⟨hω, by rwa [hT], by rwa [hT]⟩
  have hb : basisOfSpanSingleton hgen.2.1 hgen.2.2 () =
      (1 : K) • basisOfSpanSingleton hgen.1 hgen.ne_zero () := by
    rw [basisOfSpanSingleton_apply, basisOfSpanSingleton_apply, one_smul, hT]
  rw [pullbackForms_eq hgen, pullbackFormsAlong, ZTensorPower.basis_apply_of_eq_smul hb, one_zpow,
    one_smul]
  exact basis_unit_repr_smul _ τ

end IdentityAlgebra

/-! ### The discrepancy of a prime divisor of `X` -/

section OfPrimeDivisor

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]

/-- The extension of function fields of the identity is the identity. -/
@[simp]
theorem functionFieldMap_id_apply (a : X.functionField) : functionFieldMap (𝟙 X) a = a := by
  change ((X.presheaf.stalkCongr (Inseparable.refl (genericPoint X))).hom ≫
    Scheme.Hom.stalkMap (𝟙 X) (genericPoint X)).hom a = a
  simp [TopCat.Presheaf.stalkCongr_hom, Scheme.Hom.stalkMap_id]

/-- **The pull-back along the identity is the identity**: on an integral scheme of finite type
over a perfect field `k` with `trdeg_k k(X) = d`, `𝟙^*τ = τ` for every rational `m`-canonical
form `τ`. -/
theorem pullbackRationalPluriForms_id [PerfectField k] [LocallyOfFiniteType sX] {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d) {m : ℤ}
    (τ : RationalPluriForms sX d m) :
    (pullbackRationalPluriForms sX (𝟙 X) τ : RationalPluriForms sX d m) = τ := by
  let := functionFieldAlgebra sX
  have hbij : Function.Bijective (functionFieldMap (𝟙 X)) := by
    rw [show ⇑(functionFieldMap (𝟙 X)) = id from funext functionFieldMap_id_apply]
    exact Function.bijective_id
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX (𝟙 X) hbij hd
  have h0 : ω ≠ 0 := fun h0 => hω.2.2 (by rw [h0, map_zero])
  exact pullbackForms_eq_self (k := k) (functionFieldMap (𝟙 X)) functionFieldMap_id_apply hω.1
    h0 m τ

variable [IsLocallyNoetherian X] [IsNormal X]

omit [IsNormal X] in
/-- For a prime divisor `P` of a normal variety `X` of dimension `n` over a perfect field,
regarded as the divisor `(X, 𝟙_X, P)` over `X`, `ord_P(𝟙^*τ) = ord_P(τ)`. -/
theorem DivisorOver.ordPullback_ofPrimeDivisor [PerfectField k] (hX : IsNormalVariety k sX)
    {n : ℕ} (hn : topologicalKrullDim X = n) (P : PrimeDivisor X) {m : ℤ}
    (τ : RationalPluriForms sX n m) :
    (DivisorOver.ofPrimeDivisor k hX P).ordPullback τ = P.ordForm τ := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  change P.ordForm (sX := sX) (pullbackRationalPluriForms sX (𝟙 X) τ : RationalPluriForms sX n m) =
    _
  rw [pullbackRationalPluriForms_id
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn)]

/-- **The discrepancy of a prime divisor of `X`.** For a prime divisor `P` of a normal variety
`X` over a perfect field, regarded as the divisor `(X, 𝟙_X, P)` over `X`, the discrepancy
`a(P, X, Δ)`, when it exists, is `-coeff_P(Δ)`. -/
theorem IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor [PerfectField k] (hX : IsNormalVariety k sX)
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {P : PrimeDivisor X} {a : ℚ}
    (h : IsDiscrepancy sX n K Δ (DivisorOver.ofPrimeDivisor k hX P) a) : a = -Δ.coeff P := by
  obtain ⟨-, hK, m, hm, -, U, hU, τ, hτ, hτa⟩ := h
  rw [DivisorOver.ordPullback_ofPrimeDivisor hX hK.topologicalKrullDim_eq] at hτa
  have hPU : (P.support ∩ U).Nonempty := by
    refine ⟨P.genericPoint, ?_, hU⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hm0 : (m : ℚ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hm0
  linear_combination hτa + hτ.2 P hPU

/-- The value `a(P, X, Δ) = -coeff_P(Δ)` of the discrepancy of a prime divisor `P` of `X`,
regarded as the divisor `(X, 𝟙_X, P)` over `X`, when it exists. -/
theorem discrepancy_ofPrimeDivisor [PerfectField k] (hX : IsNormalVariety k sX) {n : ℕ}
    {K : Divisor X} {Δ : QDivisor X} {P : PrimeDivisor X}
    (h : ∃ a, IsDiscrepancy sX n K Δ (DivisorOver.ofPrimeDivisor k hX P) a) :
    discrepancy sX n K Δ _ h = -Δ.coeff P :=
  (isDiscrepancy_discrepancy h).eq_neg_coeff_of_ofPrimeDivisor hX

end OfPrimeDivisor

end MMP.Mori
