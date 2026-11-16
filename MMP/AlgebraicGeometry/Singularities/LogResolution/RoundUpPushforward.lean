module

public import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible

/-!
# The pushforward of `𝒪_Y(⌈B_f⌉)` along a proper birational morphism

Let `(X, Δ)` be a pair with `Δ` effective and `f : Y ⟶ X` a proper birational morphism from a
normal variety, and let `B = B_f = ∑_E max {a(E, X, Δ), 0} E` be the positive part of the
discrepancy. Then `⌈B⌉` is effective and the natural map
`𝒪_X ⟶ f_* 𝒪_Y ⟶ f_* 𝒪_Y(⌈B⌉)` is an isomorphism: a rational function on `f⁻¹ U` with poles
bounded by `⌈B⌉` is regular on `U`.

## Main results

* `MMP.Mori.isIso_pushforward_structureSheafToDivisorialSheaf_roundUp`: `⌈B_f⌉ ≥ 0` and
  `𝒪_X ⟶ f_* 𝒪_Y(⌈B_f⌉)` is an isomorphism.

## Implementation notes

The map is the composite of `SheafOfModules.unitToPushforwardObjUnit`, the map `𝒪_X ⟶ f_* 𝒪_Y`
given by `f^♯`, with the pushforward of `MMP.Mori.Divisor.structureSheafToDivisorialSheaf`, the
inclusion `𝒪_Y ⟶ 𝒪_Y(⌈B⌉)`. The latter needs the effectivity of `⌈B⌉`, which is asserted in the
conclusion alongside the isomorphism.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998], proof of
  Theorem 5.22.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Mori

universe u

/-- An integral scheme has the single irreducible component `univ`. -/
private theorem component_eq_univ {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : Z.1 = Set.univ := by
  obtain ⟨Z, h⟩ := Z
  exact (irreducibleComponents_eq_singleton (X := Y) ▸ h : Z ∈ ({Set.univ} : Set (Set Y)))

/-- In an irreducible scheme the generic point lies in every nonempty open. -/
private theorem genericPoint_mem {X : Scheme.{u}} [IrreducibleSpace X] {U : X.Opens}
    (hU : (U : Set X).Nonempty) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU)

/-- A specialization between equal points induces an isomorphism of stalks. -/
private theorem isIso_stalkSpecializes {X : Scheme.{u}} {x y : X} (hsp : x ⤳ y)
    (h : x = y) : IsIso (X.presheaf.stalkSpecializes hsp) := by
  subst h
  simp only [TopCat.Presheaf.stalkSpecializes_refl]
  infer_instance

/-- A bijective algebra map is a localization at the trivial submonoid. -/
private theorem isLocalization_bot_of_bijective {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (h : Function.Bijective (algebraMap R S)) :
    IsLocalization (⊥ : Submonoid R) S :=
  (IsLocalization.isLocalization_iff_of_algEquiv (⊥ : Submonoid R)
    (AlgEquiv.ofBijective (Algebra.ofId R S) h)).mp
    (IsLocalization.self fun x hx => by rw [Submonoid.mem_bot.mp hx]; exact isUnit_one)

/-- On an integral scheme the generic point of every irreducible component is the generic
point. -/
private theorem componentGenericPoint_eq {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : componentGenericPoint Y Z = genericPoint Y := by
  refine (isGenericPoint_componentGenericPoint Y Z).eq ?_
  rw [component_eq_univ Z]
  exact genericPoint_spec Y

/-- For a dominant morphism of integral schemes, `f^♯ : Γ(X, U) → Γ(Y, f⁻¹U)` is injective. -/
private theorem app_injective {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X)
    [IsDominant f] (U : X.Opens) : Function.Injective (f.app U) := by
  intro r r' h
  by_cases hU : (U : Set X).Nonempty
  · have hfη : f (genericPoint Y) = genericPoint X := map_genericPoint_of_isDominant f
    have hη : f (genericPoint Y) ∈ U := hfη ▸ genericPoint_mem hU
    apply germ_injective_of_isIntegral X _ hη
    have e := congrArg (Y.presheaf.germ (f ⁻¹ᵁ U) (genericPoint Y) hη) h
    rw [← Scheme.Hom.germ_stalkMap_apply, ← Scheme.Hom.germ_stalkMap_apply] at e
    have : Function.Injective (f.stalkMap (genericPoint Y)) := by
      let e := X.presheaf.stalkCongr (Inseparable.of_eq hfη.symm)
      have hg : Function.Injective (e.hom ≫ f.stalkMap (genericPoint Y)) :=
        RingHom.injective (R := X.functionField) (e.hom ≫ f.stalkMap (genericPoint Y)).hom
      intro a b hab
      have h2 := @hg (e.inv a) (e.inv b) (by simp [hab])
      simpa using congrArg e.hom h2
    exact this e
  · obtain rfl : U = ⊥ := eq_bot_iff.mpr fun x hx => (hU ⟨x, hx⟩).elim
    exact Subsingleton.elim _ _

section

variable {k : Type*} [CommRing k] {K L : Type*} [Field K] [Field L] [Algebra k K] [Algebra k L]
  [Algebra K L] [IsScalarTower k K L]

/-- Along a bijective map of fields over `k`, `Ω^d_{K/k} ⟶ Ω^d_{L/k}` is injective: the inverse
map is a left inverse. -/
private theorem topFormsMap_injective_of_bijective (h : Function.Bijective (algebraMap K L))
    (d : ℕ) :
    Function.Injective (topFormsMap k K L d) := by
  let e := RingEquiv.ofBijective (algebraMap K L) h
  let : Algebra L K := e.symm.toRingHom.toAlgebra
  have : IsScalarTower k L K := IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap k K c = e.symm (algebraMap k L c)
    rw [IsScalarTower.algebraMap_apply k K L]
    exact (e.symm_apply_apply _).symm
  have : IsScalarTower K L K := IsScalarTower.of_algebraMap_eq fun c =>
    (e.symm_apply_apply c).symm
  intro x y hxy
  have h1 := congrArg (topFormsMap k L K d) hxy
  rw [MMP.Threefold.Mori.Helpers.topFormsMap_comp,
    MMP.Threefold.Mori.Helpers.topFormsMap_comp] at h1
  have hid := topFormsMap_eq_self (k := k) (RingHom.id K) (fun _ => rfl) (d := d)
  rwa [hid, hid] at h1

end

section

variable {k : Type*} [CommRing k] {d : ℕ}
variable {A B K L : Type*} [CommRing A] [CommRing B] [Field K] [Field L] [Algebra k A]
  [Algebra k B] [Algebra k K] [Algebra k L] [Algebra A K] [Algebra B L] [Algebra A B]
  [Algebra K L] [Algebra A L] [IsScalarTower k A K] [IsScalarTower k B L] [IsScalarTower k A B]
  [IsScalarTower k K L] [IsScalarTower k A L] [IsScalarTower A B L] [IsScalarTower A K L]

/-- A generator of `Ω^d_{A/k}` with nonzero image in `Ω^d_{K/k}` is carried, along bijective
maps `A ⟶ B` and `K ⟶ L`, to a generator of `Ω^d_{B/k}` with nonzero image in `Ω^d_{L/k}`. -/
private theorem exists_generator_of_bijective (hAB : Function.Bijective (algebraMap A B))
    (hKL : Function.Bijective (algebraMap K L))
    (h : ∃ σ : ⋀[A]^d Ω[A⁄k], Submodule.span A {σ} = ⊤ ∧ topFormsMap k A K d σ ≠ 0) :
    ∃ σ : ⋀[B]^d Ω[B⁄k], Submodule.span B {σ} = ⊤ ∧ topFormsMap k B L d σ ≠ 0 := by
  obtain ⟨σ, hσ, h0⟩ := h
  have := isLocalization_bot_of_bijective hAB
  refine ⟨topFormsMap k A B d σ, span_singleton_topFormsMap ⊥ hσ, ?_⟩
  rw [MMP.Threefold.Mori.Helpers.topFormsMap_comp,
    ← MMP.Threefold.Mori.Helpers.topFormsMap_comp (B := K) (C := L)]
  exact fun h1 => h0 (topFormsMap_injective_of_bijective hKL d (h1.trans (map_zero _).symm))

end

section

variable {k : Type*} [CommRing k] {d : ℕ} {m : ℤ}
variable {K K' : Type*} [Field K] [Field K'] [Algebra k K] [Algebra k K'] [Algebra K K']
  [IsScalarTower k K K']
variable {A A' : Type*} [CommRing A] [CommRing A'] [Algebra k A] [Algebra k A'] [Algebra A K]
  [IsScalarTower k A K] [IsFractionRing A K] [Algebra A' K'] [IsScalarTower k A' K']
  [IsFractionRing A' K'] [Algebra A A'] [IsScalarTower k A A'] [Algebra A K']
  [IsScalarTower A A' K'] [IsScalarTower A K K'] [IsScalarTower k A K']

/-- The order of a form is invariant under bijective maps `A ⟶ A'`, `K ⟶ K'` compatible with the
valuations, with no hypothesis on `k`: if `Ω^d_{A/k}` has a generator the orders are computed
from it and its image; otherwise neither side has one and both orders are `0`. -/
private theorem ordAt_pullbackForms_eq_of_bijective (hbij : Function.Bijective (algebraMap A A'))
    (hbijK : Function.Bijective (algebraMap K K'))
    {v : K → ℤ} {v' : K' → ℤ}
    (hmul : ∀ x y : K, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y)
    (hunit : ∀ a : A, IsUnit a → v (algebraMap A K a) = 0)
    (hmul' : ∀ x y : K', x ≠ 0 → y ≠ 0 → v' (x * y) = v' x + v' y)
    (hunit' : ∀ a : A', IsUnit a → v' (algebraMap A' K' a) = 0)
    (hvv : ∀ x, v' (algebraMap K K' x) = v x) (τ : PluriForms k K d m) :
    ordAt A' v' (pullbackForms (K' := K') m τ) = ordAt A v τ := by
  classical
  by_cases h : ∃ σ : ⋀[A]^d Ω[A⁄k], Submodule.span A {σ} = ⊤ ∧ topFormsMap k A K d σ ≠ 0
  · obtain ⟨σ, hσ, h0⟩ := h
    have := isLocalization_bot_of_bijective hbijK
    have hK := span_singleton_topFormsMap (K := K) (nonZeroDivisors A) hσ
    have hω : IsPullbackGenerator K' (topFormsMap k A K d σ) :=
      ⟨hK, span_singleton_topFormsMap ⊥ hK, fun h1 =>
        h0 (topFormsMap_injective_of_bijective hbijK d (h1.trans (map_zero _).symm))⟩
    exact MMP.Threefold.Mori.Helpers.ordAt_pullbackForms_eq hbij hmul hunit hmul' hunit' hvv
      hσ hω τ
  · have h' : ¬ ∃ σ : ⋀[A']^d Ω[A'⁄k], Submodule.span A' {σ} = ⊤ ∧
        topFormsMap k A' K' d σ ≠ 0 := by
      intro h'
      apply h
      let eA := RingEquiv.ofBijective (algebraMap A A') hbij
      let eK := RingEquiv.ofBijective (algebraMap K K') hbijK
      let : Algebra A' A := eA.symm.toRingHom.toAlgebra
      let : Algebra K' K := eK.symm.toRingHom.toAlgebra
      let : Algebra A' K := ((algebraMap A K).comp (algebraMap A' A)).toAlgebra
      have hA : ∀ c : k, algebraMap k A c = eA.symm (algebraMap k A' c) := fun c => by
        rw [IsScalarTower.algebraMap_apply k A A']
        exact (eA.symm_apply_apply _).symm
      have hKc : ∀ c : k, algebraMap k K c = eK.symm (algebraMap k K' c) := fun c => by
        rw [IsScalarTower.algebraMap_apply k K K']
        exact (eK.symm_apply_apply _).symm
      have : IsScalarTower k A' A := IsScalarTower.of_algebraMap_eq hA
      have : IsScalarTower k K' K := IsScalarTower.of_algebraMap_eq hKc
      have : IsScalarTower A' A K := IsScalarTower.of_algebraMap_eq fun _ => rfl
      have : IsScalarTower k A' K := IsScalarTower.of_algebraMap_eq fun c => by
        change _ = algebraMap A K (eA.symm (algebraMap k A' c))
        rw [← hA, ← IsScalarTower.algebraMap_apply]
      have : IsScalarTower A' K' K := IsScalarTower.of_algebraMap_eq fun a => by
        change algebraMap A K (eA.symm a) = eK.symm (algebraMap A' K' a)
        apply eK.injective
        rw [RingEquiv.apply_symm_apply]
        change algebraMap K K' (algebraMap A K (eA.symm a)) = _
        rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A A' K']
        congr 1
        exact eA.apply_symm_apply a
      exact exists_generator_of_bijective (A := A') (B := A) (K := K') (L := K)
        eA.symm.bijective eK.symm.bijective h'
    simp only [ordAt, h, h', dite_false]

end

/-- The order of a rational pluricanonical form is unchanged by pulling back along a prime
divisor `F` of `Y` dominating a prime divisor `P` of `X`: `ord_F(f^*τ) = ord_P(τ)` when
`f(η_F) = η_P` and `f^♯ : 𝒪_{X,P} ⟶ 𝒪_{Y,F}` is an isomorphism, `f^* : k(X) → k(Y)` being an
isomorphism. The isomorphisms carry a generator of `Ω^d_{𝒪_{X,P}/k}` to one of `Ω^d_{𝒪_{Y,F}/k}`
and back, so both sides are computed from the same generator, or both vanish. -/
private theorem ordForm_pullbackRationalPluriForms_of_isIso {k : Type u} [Field k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal X] [IsNormal Y] {sX : X ⟶ Spec (.of k)} (f : Y ⟶ X)
    [IsDominant f]
    (hbij : Function.Bijective (functionFieldMap f)) {d : ℕ} (F : MMP.Mori.PrimeDivisor Y)
    (P : MMP.Mori.PrimeDivisor X) (heq : f F.genericPoint = P.genericPoint)
    [IsIso (f.stalkMap F.genericPoint)] {m : ℤ} (τ : RationalPluriForms sX d m) :
    F.ordForm (pullbackRationalPluriForms sX f τ) = P.ordForm τ := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  let := stalkAlgebra sX P.genericPoint
  have := isScalarTower_stalk_functionField sX P.genericPoint
  let := stalkAlgebra (f ≫ sX) F.genericPoint
  have := isScalarTower_stalk_functionField (f ≫ sX) F.genericPoint
  have hsp : f F.genericPoint ⤳ P.genericPoint := heq ▸ specializes_rfl
  let φ : X.presheaf.stalk P.genericPoint ⟶ Y.presheaf.stalk F.genericPoint :=
    X.presheaf.stalkSpecializes hsp ≫ f.stalkMap F.genericPoint
  have := isIso_stalkSpecializes hsp heq
  have hφ : IsIso φ := by infer_instance
  let : Algebra P.localRing F.localRing := φ.hom.toAlgebra
  let : Algebra P.localRing Y.functionField :=
    ((algebraMap X.functionField Y.functionField).comp
      (algebraMap P.localRing X.functionField)).toAlgebra
  have : IsScalarTower P.localRing X.functionField Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hφK : ∀ r : P.localRing, algebraMap P.localRing Y.functionField r =
      algebraMap F.localRing Y.functionField (φ.hom r) := fun r => by
    change functionFieldMap f _ = algebraMap _ Y.functionField ((f.stalkMap F.genericPoint).hom
        ((X.presheaf.stalkSpecializes hsp).hom r))
    rw [← functionFieldMap_algebraMap_stalk, algebraMap_stalkSpecializes]
  have : IsScalarTower P.localRing F.localRing Y.functionField :=
    IsScalarTower.of_algebraMap_eq hφK
  have : IsScalarTower k P.localRing F.localRing := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    have h : (Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ sX).appTop ≫
          Y.presheaf.germ ⊤ F.genericPoint (Opens.mem_top _) =
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
  have hbijA : Function.Bijective (algebraMap P.localRing F.localRing) :=
    (ConcreteCategory.isIso_iff_bijective φ).mp hφ
  exact ordAt_pullbackForms_eq_of_bijective (k := k) hbijA hbij
    P.ord_mul_of_ne_zero (fun _ ha => P.ord_algebraMap_of_isUnit ha)
    F.ord_mul_of_ne_zero (fun _ ha => F.ord_algebraMap_of_isUnit ha)
    (fun x => MMP.Positivity.ord_functionFieldMap_of_isIso f F P heq x) τ

/-- For an effective boundary, a prime divisor `F` of `Y` dominating a prime divisor `P` of `X`
(so not `f`-exceptional) has discrepancy `a(F, X, Δ) = -coeff_P Δ ≤ 0`, so `⌈B_f⌉` does not
contain it. -/
private theorem coeff_roundUp_eq_zero_of_isIso_stalkMap {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of k)) {n : ℕ}
    {K : Divisor X} {Δ : QDivisor X} (hΔ : 0 ≤ Δ) {Y : Scheme.{u}} (f : Y ⟶ X)
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) {B : QDivisor Y}
    (hB : IsDiscrepancyPositivePart sX n K Δ f hY hf B) (F : MMP.Mori.PrimeDivisor Y)
    (P : MMP.Mori.PrimeDivisor X) (hFP : f F.genericPoint = P.genericPoint)
    (hiso : IsIso (f.stalkMap F.genericPoint)) : B.roundUp.coeff F = 0 := by
  haveI := hY.1.toIsIntegral
  haveI : IsLocallyNoetherian Y := hY.1.isLocallyNoetherian
  haveI : IsNormal Y := hY.2
  haveI := hf.isDominant
  obtain ⟨a, ha, hBa⟩ := hB.2 F
  obtain ⟨-, -, m, hm, -, U, hU, τ, hτ, hτa⟩ := ha
  have hPU : (P.support ∩ (U : Set X)).Nonempty := by
    refine ⟨P.genericPoint, ?_, ?_⟩
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    · rw [← hFP]
      exact hU
  have e := hτ.2 P hPU
  have hord : (DivisorOver.ordPullback ⟨Y, f, hY, hf, F⟩ τ : ℤ) = P.ordForm τ :=
    ordForm_pullbackRationalPluriForms_of_isIso f hf.functionFieldMap_bijective F P hFP τ
  rw [hord] at hτa
  have hΔP : 0 ≤ Δ.coeff P := hΔ P
  have hm0 : (0 : ℚ) < m := by exact_mod_cast hm
  have ha0 : a ≤ 0 := by
    by_contra! h
    nlinarith
  rw [DivisorWithCoeffs.coeff_roundUp, hBa, max_eq_right ha0, Int.ceil_zero]

/-- The valuation `v_P` is carried to `v_F` by a map of the factors of `𝒦` compatible with an
isomorphism `𝒪_{X,P} ≅ 𝒪_{Y,F}`. -/
private theorem valuation_map {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] (P : MMP.Mori.PrimeDivisor X) (F : MMP.Mori.PrimeDivisor Y)
    (φ : P.localRing ≃+* F.localRing)
    (T : X.presheaf.stalk (componentGenericPoint X P.component) →+*
      Y.presheaf.stalk (componentGenericPoint Y F.component))
    (hT : ∀ a, T (P.toComponent.hom a) = F.toComponent.hom (φ a))
    (x : X.presheaf.stalk (componentGenericPoint X P.component)) :
    F.valuation (T x) = P.valuation x := by
  let := P.toComponent.hom.toAlgebra
  have := isFractionRing_stalkToRationalFunctions P.genericPoint_mem_component
  have : Ring.KrullDimLE 1 P.localRing := krullDimLE_of_coheight_le P.coheight_genericPoint.le
  have := P.isDiscreteValuationRing_localRing
  let := F.toComponent.hom.toAlgebra
  have := isFractionRing_stalkToRationalFunctions F.genericPoint_mem_component
  have : Ring.KrullDimLE 1 F.localRing := krullDimLE_of_coheight_le F.coheight_genericPoint.le
  have := F.isDiscreteValuationRing_localRing
  let eP := IsLocalization.algEquiv (nonZeroDivisors P.localRing)
    (X.presheaf.stalk (componentGenericPoint X P.component)) (FractionRing P.localRing)
  let eF := IsLocalization.algEquiv (nonZeroDivisors F.localRing)
    (Y.presheaf.stalk (componentGenericPoint Y F.component)) (FractionRing F.localRing)
  change Ring.ordFrac F.localRing (eF (T x)) = Ring.ordFrac P.localRing (eP x)
  have key := MMP.Positivity.ordFrac_map_of_ringEquiv (K := FractionRing P.localRing)
    (K' := FractionRing F.localRing) φ
    ((eF.toRingEquiv.toRingHom.comp T).comp eP.symm.toRingEquiv.toRingHom) (fun r => by
      have h1 : eP.symm (algebraMap _ (FractionRing P.localRing) r) = P.toComponent.hom r :=
        eP.symm.commutes r
      have h2 : eF (F.toComponent.hom (φ r)) = algebraMap _ (FractionRing F.localRing) (φ r) :=
        eF.commutes (φ r)
      simp only [RingHom.coe_comp, Function.comp_apply]
      change eF (T (eP.symm (algebraMap _ (FractionRing P.localRing) r))) = _
      rw [h1, hT, h2]) (eP x)
  simpa using key

/-- Let `f : Y ⟶ X` be a dominant morphism of normal integral schemes with `f^* : k(X) ≅ k(Y)`
and `D` a divisor on `Y` such that every prime divisor `P` of `X` is dominated by a prime divisor
`F` of `Y` with `coeff_F D = 0`. Then every section of `𝒪_Y(D)` over `f⁻¹ U` is `f^♯ r` for a
regular function `r` on `U`: `v_P(φ) = v_F(φ) ≥ 0` for every `P` meeting `U`, and algebraic
Hartogs applies on `X`. -/
private theorem exists_app_eq_of_mem_divisorialSubmodule {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (f : Y ⟶ X) [IsDominant f] (hf : Function.Bijective (functionFieldMap f)) (D : Divisor Y)
    (hD : ∀ P : MMP.Mori.PrimeDivisor X, ∃ F : MMP.Mori.PrimeDivisor Y,
      f F.genericPoint = P.genericPoint ∧ IsIso (f.stalkMap F.genericPoint) ∧ D.coeff F = 0)
    (U : X.Opens) (ψ : D.divisorialSubmodule (f ⁻¹ᵁ U)) :
    ∃ r : Γ(X, U), (toRationalFunctionsPresheaf Y).app (Opposite.op (f ⁻¹ᵁ U)) (f.app U r) =
      ψ.1 := by
  by_cases hU : (U : Set X).Nonempty
  swap
  · exact ⟨0, funext fun Z => (hU ⟨_, Z.2⟩).elim⟩
  have hfη : f (genericPoint Y) = genericPoint X := map_genericPoint_of_isDominant f
  have hηX : genericPoint X ∈ U := genericPoint_mem hU
  have hηY : genericPoint Y ∈ f ⁻¹ᵁ U := show f _ ∈ U from hfη ▸ hηX
  obtain ⟨ZY, -⟩ := exists_mem_irreducibleComponents (genericPoint Y)
  obtain ⟨ZX, -⟩ := exists_mem_irreducibleComponents (genericPoint X)
  have hZYU : componentGenericPoint Y ZY ∈ f ⁻¹ᵁ U := by
    rwa [componentGenericPoint_eq]
  have hZXU : componentGenericPoint X ZX ∈ U := by
    rwa [componentGenericPoint_eq]
  have hsub : ∀ Z Z' : irreducibleComponents Y, Z = Z' := fun Z Z' =>
    Subtype.ext (by rw [component_eq_univ Z, component_eq_univ Z'])
  let Φ := RingEquiv.ofBijective (functionFieldMap f) hf
  let eX : ∀ Z : irreducibleComponents X,
      X.presheaf.stalk (componentGenericPoint X Z) ≃+* X.functionField := fun Z =>
    (X.presheaf.stalkCongr
      (Inseparable.of_eq (componentGenericPoint_eq Z).symm)).commRingCatIsoToRingEquiv.symm
  let eY : ∀ Z : irreducibleComponents Y,
      Y.presheaf.stalk (componentGenericPoint Y Z) ≃+* Y.functionField := fun Z =>
    (Y.presheaf.stalkCongr
      (Inseparable.of_eq (componentGenericPoint_eq Z).symm)).commRingCatIsoToRingEquiv.symm
  have heX : ∀ Z a, eX Z a = algebraMap _ X.functionField a := fun _ _ => rfl
  have heY : ∀ Z a, eY Z a = algebraMap _ Y.functionField a := fun _ _ => rfl
  let φX : ToType ((rationalFunctionsPresheaf X).obj (Opposite.op U)) := fun Z =>
    (eX Z.1).symm (Φ.symm (eY ZY (ψ.1 ⟨ZY, hZYU⟩)))
  have hφX : (0 : Divisor X).IsDivisorialSection U φX := by
    intro P hP
    obtain ⟨F, hFP, hiso, hF0⟩ := hD P
    have hFU : (F.support ∩ (f ⁻¹ᵁ U : Set Y)).Nonempty := by
      refine ⟨F.genericPoint, ?_, ?_⟩
      · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact subset_closure rfl
      · show f _ ∈ U
        rw [hFP]
        exact P.genericPoint_mem_of_nonempty hP
    have hψF := ψ.2 F hFU
    rw [hF0, neg_zero] at hψF
    obtain rfl := hsub ZY F.component
    have hsp : f F.genericPoint ⤳ P.genericPoint := hFP ▸ specializes_rfl
    have := isIso_stalkSpecializes hsp hFP
    let φ : P.localRing ≃+* F.localRing :=
      (asIso (X.presheaf.stalkSpecializes hsp ≫
        f.stalkMap F.genericPoint)).commRingCatIsoToRingEquiv
    let T : X.presheaf.stalk (componentGenericPoint X P.component) →+*
        Y.presheaf.stalk (componentGenericPoint Y F.component) :=
      (eY F.component).symm.toRingHom.comp (Φ.toRingHom.comp (eX P.component).toRingHom)
    have hTinj : Function.Injective T :=
      (eY F.component).symm.injective.comp (Φ.injective.comp (eX P.component).injective)
    have hT : ∀ b, T (P.toComponent.hom b) = F.toComponent.hom (φ b) := by
      intro b
      apply (eY F.component).injective
      simp only [T, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        RingEquiv.apply_symm_apply]
      rw [heX, heY]
      change Φ (algebraMap _ X.functionField ((X.presheaf.stalkSpecializes _).hom b)) =
        algebraMap _ Y.functionField ((Y.presheaf.stalkSpecializes _).hom
          ((f.stalkMap F.genericPoint).hom ((X.presheaf.stalkSpecializes hsp).hom b)))
      rw [algebraMap_stalkSpecializes, algebraMap_stalkSpecializes,
        ← functionFieldMap_algebraMap_stalk, algebraMap_stalkSpecializes]
      rfl
    have hTa : T (φX ⟨P.component, P.componentGenericPoint_mem_of_nonempty hP⟩) =
        ψ.1 ⟨F.component, F.componentGenericPoint_mem_of_nonempty hFU⟩ := by
      simp [T, φX]
    rcases hψF with h0 | hv
    · exact Or.inl (hTinj (hTa.trans (h0.trans (map_zero T).symm)))
    · right
      rwa [← valuation_map P F φ T hT, hTa]
  obtain ⟨s, hs⟩ := hφX.exists_eq
  refine ⟨s, funext fun Z' => ?_⟩
  obtain rfl : Z' = ⟨ZY, hZYU⟩ := Subtype.ext (hsub _ _)
  rw [toRationalFunctionsPresheaf_app_apply]
  apply (eY ZY).injective
  have h1 := congrFun hs ⟨ZX, hZXU⟩
  rw [toRationalFunctionsPresheaf_app_apply] at h1
  have hsp : componentGenericPoint X ZX ⤳ f (componentGenericPoint Y ZY) :=
    (isGenericPoint_componentGenericPoint X ZX).specializes (by rw [component_eq_univ ZX]; trivial)
  have hR : (eY ZY) (ψ.1 ⟨ZY, hZYU⟩) = Φ (eX ZX (X.presheaf.germ U _ hZXU s)) := by
    rw [h1]
    simp [φX]
  have h2 : Y.presheaf.germ (f ⁻¹ᵁ U) (componentGenericPoint Y ZY) hZYU (f.app U s) =
      f.stalkMap _ (X.presheaf.germ U _ hZYU s) :=
    (Scheme.Hom.germ_stalkMap_apply f U _ hZYU s).symm
  rw [hR, heY, heX]
  erw [h2]
  rw [← functionFieldMap_algebraMap_stalk,
    ← TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hZYU hsp, algebraMap_stalkSpecializes]
  rfl

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X]

/-- Let `(X, Δ)` be a pair with `Δ` effective, `f : Y ⟶ X` a proper birational morphism from a
normal variety and `B = B_f` the positive part of the discrepancy
(`MMP.Mori.IsDiscrepancyPositivePart`). Then `⌈B⌉` is effective and the natural map
`𝒪_X ⟶ f_* 𝒪_Y ⟶ f_* 𝒪_Y(⌈B⌉)` is an isomorphism. -/
@[mmp "lem_km5d_klt_log_resolution_pushforward"]
public theorem isIso_pushforward_structureSheafToDivisorialSheaf_roundUp
    (sX : X ⟶ Spec (.of k)) {n : ℕ} {K : Divisor X} {Δ : QDivisor X} (hΔ : 0 ≤ Δ)
    {Y : Scheme.{u}} (f : Y ⟶ X) [IsProper f] (hY : IsNormalVariety k (f ≫ sX))
    (hf : IsBirationalMorphism f) {B : QDivisor Y}
    (hB : IsDiscrepancyPositivePart sX n K Δ f hY hf B) :
    haveI : IsLocallyNoetherian Y := hY.1.isLocallyNoetherian
    haveI : IsNormal Y := hY.2
    ∃ h : 0 ≤ B.roundUp,
      IsIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward f).map (Divisor.structureSheafToDivisorialSheaf h)) := by
  haveI : IsLocallyNoetherian Y := hY.1.isLocallyNoetherian
  haveI : IsNormal Y := hY.2
  have h0 : 0 ≤ B.roundUp := by
    intro F
    obtain ⟨a, -, ha⟩ := hB.2 F
    show 0 ≤ B.roundUp.coeff F
    rw [DivisorWithCoeffs.coeff_roundUp, ha]
    exact Int.ceil_nonneg (le_max_right _ _)
  refine ⟨h0, ?_⟩
  refine (Scheme.Modules.Hom.isIso_iff_isIso_app (X := X)).mpr fun U => ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  set φ := (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward f).map (Divisor.structureSheafToDivisorialSheaf h0))
  have key : ∀ r : Γ(X, U), (Scheme.Modules.Hom.app φ U r).1
      = (toRationalFunctionsPresheaf Y).app (Opposite.op (f ⁻¹ᵁ U)) (f.app U r) := fun r =>
    Divisor.coe_structureSheafToDivisorialSheaf_app h0 (f ⁻¹ᵁ U) (f.app U r)
  haveI := hY.1.toIsIntegral
  haveI := hf.isDominant
  refine ⟨fun r r' hrr => ?_, fun ψ => ?_⟩
  · exact app_injective f U (toRationalFunctionsPresheaf_app_injective (f ⁻¹ᵁ U)
      ((key r).symm.trans ((congrArg Subtype.val hrr).trans (key r'))))
  · obtain ⟨r, hr⟩ := exists_app_eq_of_mem_divisorialSubmodule f hf.functionFieldMap_bijective
      B.roundUp
      (fun P => by
        obtain ⟨F, hFP, hiso, -⟩ :=
          MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hB.1.1 hY hf P
        exact ⟨F, hFP, hiso,
          coeff_roundUp_eq_zero_of_isIso_stalkMap sX hΔ f hY hf hB F P hFP hiso⟩)
      U ψ
    exact ⟨r, Subtype.ext ((key r).trans hr)⟩

end MMP.Mori

end
