module

public import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion
public import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
public import MMP.AlgebraicGeometry.Singularities.Adjunction.PoincareResidueSmoothDivisor

/-!
# Residue along a smooth divisor is Cartier restriction

Let `Y` be a smooth variety of dimension `n + 1` over a field `k`, `S' ⊂ Y` a smooth prime
divisor and `σ` a rational top form on `Y` with a simple pole along `S'`, with Poincaré residue
`η'`, a rational top form on `S'`. Put `K_Y = div(σ)` and `K_{S'} = div(η')`. Then `η' ≠ 0`, the
divisor `K_Y + S'` does not contain `S'`, and its Cartier restriction to `S'` is `K_{S'}`.
Consequently, for every `ℚ`-Cartier `ℚ`-divisor `D` on `Y` not containing `S'` and
`Γ = D - K_Y`, the restriction of `Γ - S'` to `S'` is defined and
`K_{S'} + (Γ - S')|_{S'} = D|_{S'}`.

## Main results

* `MMP.Mori.QDivisor.IsPullback.add`: pull-back of `ℚ`-Cartier `ℚ`-divisors is additive.
* `MMP.Fourfold.isPullback_divisorOfForm_add_of_isPoincareResidue`

## Implementation notes

Restriction to `S'` is pull-back along the closed immersion `S' ⟶ Y`: for integral divisors
`MMP.Mori.Divisor.IsPullback`, for `ℚ`-divisors `MMP.Mori.QDivisor.IsPullback`, both defined once
the generic point of `S'` lies off the support of the divisor being restricted. The second
assertion is stated for `ℚ`-divisors, which contains the case of an integral Cartier divisor `D`
(take `m = 1` in `MMP.Mori.QDivisor.IsPullback`).

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], Chapter 16
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Mori.QDivisor

/-- **Pull-back of `ℚ`-Cartier `ℚ`-divisors is additive.** If `R₁ = f^*G₁` and `R₂ = f^*G₂` with `G₁`,
`G₂` `ℚ`-Cartier, then `R₁ + R₂ = f^*(G₁ + G₂)`. -/
theorem IsPullback.add {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} {G₁ G₂ : QDivisor Y}
    (hG₁ : G₁.IsQCartier) (hG₂ : G₂.IsQCartier)
    {h₁ : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ G₁.supp}
    {h₂ : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ G₂.supp}
    {R₁ R₂ : QDivisor X} (p₁ : G₁.IsPullback f h₁ R₁) (p₂ : G₂.IsPullback f h₂ R₂)
    (h : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ (G₁ + G₂).supp) :
    (G₁ + G₂).IsPullback f h (R₁ + R₂) := by
  intro m hm D hD hDc
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  obtain ⟨m₁, hm₁, A₁, hA₁, hA₁c⟩ := hG₁.exists_pos
  obtain ⟨m₂, hm₂, A₂, hA₂, hA₂c⟩ := hG₂.exists_pos
  have hm₁' : (m₁ : ℤ) ≠ 0 := by exact_mod_cast hm₁.ne'
  have hm₂' : (m₂ : ℤ) ≠ 0 := by exact_mod_cast hm₂.ne'
  obtain ⟨A₁', hA₁', p₁'⟩ := p₁ m₁ hm₁ A₁ hA₁ hA₁c
  obtain ⟨A₂', hA₂', p₂'⟩ := p₂ m₂ hm₂ A₂ hA₂ hA₂c
  have hsuppD : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ D.supp :=
    fun W hW => h W (by rwa [QDivisor.supp_eq_of_toQDivisor_eq hm' hD] at hW)
  have hsupp : ∀ {G : QDivisor Y} (A : Divisor Y) (c : ℤ), c ≠ 0 →
      Divisor.toQDivisor A = c • G →
      (∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ G.supp) →
      ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ A.supp :=
    fun A c hc hA hG W hW => hG W (by rwa [QDivisor.supp_eq_of_toQDivisor_eq hc hA] at hW)
  set N : ℤ := (m₁ : ℤ) * m₂
  have hN : N ≠ 0 := mul_ne_zero hm₁' hm₂'
  set A : Divisor Y := (m : ℤ) • ((m₂ : ℤ) • A₁ + (m₁ : ℤ) • A₂)
  have hAD : A = N • D := by
    apply Divisor.toQDivisor_injective
    simp only [A, N, map_zsmul, map_add, hA₁, hA₂, hD, smul_add, smul_smul]
    congr 1 <;> congr 1 <;> ring
  have hAc : A.IsCartier := ((hA₁c.zsmul _).add (hA₂c.zsmul _)).zsmul _
  have hA₁N : Divisor.toQDivisor ((m₂ : ℤ) • A₁) = N • G₁ := by
    simp only [map_zsmul, hA₁, smul_smul, N]
    congr 1
    ring
  have hA₂N : Divisor.toQDivisor ((m₁ : ℤ) • A₂) = N • G₂ := by
    simp only [map_zsmul, hA₂, smul_smul, N]
  have hsum : Divisor.toQDivisor ((m₂ : ℤ) • A₁ + (m₁ : ℤ) • A₂) = N • (G₁ + G₂) := by
    rw [map_add, hA₁N, hA₂N, smul_add]
  have hAq : Divisor.toQDivisor A = ((m : ℤ) * N) • (G₁ + G₂) := by
    simp only [A, map_zsmul, hsum, smul_smul]
  have pA := ((p₁'.zsmul hA₁c (m₂ : ℤ) (hsupp _ _ hN hA₁N h₁)).add (hA₁c.zsmul _)
    (hA₂c.zsmul _) (hsupp _ _ hN hsum h) (p₂'.zsmul hA₂c (m₁ : ℤ) (hsupp _ _ hN hA₂N h₂))).zsmul
    ((hA₁c.zsmul _).add (hA₂c.zsmul _)) (m : ℤ)
    (hsupp _ _ (mul_ne_zero hm' hN) hAq h)
  obtain ⟨D', hD'⟩ := hDc.exists_isPullback hsuppD
  refine ⟨D', ?_, hD'⟩
  have pND := hD'.zsmul hDc N (hsupp _ _ (mul_ne_zero hN hm') (by
    rw [map_zsmul, hD, smul_smul]) h)
  have heq := pA.eq hAc (pND.of_eq hAD.symm)
  have heqQ := congrArg Divisor.toQDivisor heq
  simp only [map_zsmul, map_add, hA₁', hA₂', smul_smul] at heqQ
  ext E
  have := congrArg (fun G : QDivisor X => G.coeff E) heqQ
  simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add, zsmul_eq_mul,
    Divisor.coeff_toQDivisor, N] at this ⊢
  apply mul_left_cancel₀ (show ((m₁ : ℚ) * m₂) ≠ 0 by positivity)
  push_cast at this ⊢
  linear_combination -this

end MMP.Mori.QDivisor

namespace MMP.Fourfold

open MMP.Mori

/-- On an integral scheme, the order `v_Q` of a unit of the factor `K(X)` is the order of
vanishing of its image in the function field. -/
private theorem ordUnit_eq_ord {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X]
    (Q : Mori.PrimeDivisor X) (v : (X.presheaf.stalk (componentGenericPoint X Q.component))ˣ) :
    Q.ordUnit v = X.ord ((MMP.Positivity.componentToFunctionField Q.component).hom v.val)
      Q.genericPoint := by
  classical
  let φ : (RationalFunctions X)ˣ :=
    (RationalFunctions.unitsEquiv X).symm (Pi.mulSingle Q.component v)
  have hφ : Units.map (RationalFunctions.component X Q.component).toMonoidHom φ = v := by
    ext
    change ((RationalFunctions.unitsEquiv X φ) Q.component).val = v.val
    simp [φ]
  have := MMP.Positivity.ord_eq_ord_componentToFunctionField Q φ
  rw [PrimeDivisor.ord_eq_ordUnit, hφ] at this
  rw [this]
  congr 2
  exact congrArg Units.val hφ

/-- Generization from a stalk to a component, then to the function field, is generization to the
function field. -/
private theorem componentToFunctionField_stalkSpecializes (X : Scheme.{u}) [IsIntegral X]
    (Z : irreducibleComponents X) {x : X} (h : componentGenericPoint X Z ⤳ x)
    (z : X.presheaf.stalk x) :
    (MMP.Positivity.componentToFunctionField Z).hom (X.presheaf.stalkSpecializes h z) =
      algebraMap (X.presheaf.stalk x) X.functionField z :=
  MMP.Mori.algebraMap_stalkSpecializes h z

/-- `componentToFunctionField_stalkSpecializes` for `stalkToRationalFunctions`. -/
private theorem componentToFunctionField_stalkToRationalFunctions (X : Scheme.{u}) [IsIntegral X]
    {Z : irreducibleComponents X} {x : X} (hx : x ∈ Z.1) (z : X.presheaf.stalk x) :
    (MMP.Positivity.componentToFunctionField Z).hom ((stalkToRationalFunctions X hx).hom z) =
      algebraMap (X.presheaf.stalk x) X.functionField z :=
  componentToFunctionField_stalkSpecializes X Z _ z

/-- If `f b = a` with `f, b ≠ 0`, then `ord f = ord a - ord b`. -/
private theorem ord_eq_sub_of_mul_eq {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {f a b : X.functionField}
    (hf : f ≠ 0) (hb : b ≠ 0) (h : f * b = a) (z : X) : X.ord f z = X.ord a z - X.ord b z := by
  rw [← h, Scheme.ord_mul hf hb]
  ring

/-- For `y ⤳ y'`, a unit `a` of `𝒪_{X,y}` is a fraction `r / s` of elements of `𝒪_{X,y'}`
whose images in `𝒪_{X,y}` are units. -/
private theorem exists_mul_stalkSpecializes_eq {X : Scheme.{u}} {y y' : X} (hsp : y ⤳ y')
    (a : (X.presheaf.stalk y)ˣ) :
    ∃ r s : X.presheaf.stalk y', a.val * X.presheaf.stalkSpecializes hsp s =
      X.presheaf.stalkSpecializes hsp r ∧ IsUnit (X.presheaf.stalkSpecializes hsp s) ∧
      IsUnit (X.presheaf.stalkSpecializes hsp r) := by
  let := (X.presheaf.stalkSpecializes hsp).hom.toAlgebra
  have := MMP.Intersection.isLocalization_stalkSpecializes hsp
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.mk'_surjective
    ((IsLocalRing.maximalIdeal (X.presheaf.stalk y)).comap
      (X.presheaf.stalkSpecializes hsp).hom).primeCompl a.val
  have hrs' : a.val * X.presheaf.stalkSpecializes hsp s.val =
      X.presheaf.stalkSpecializes hsp r := by
    rw [← hrs]
    exact IsLocalization.mk'_spec _ r s
  have hsU : IsUnit (X.presheaf.stalkSpecializes hsp s.val) := by
    simpa [Ideal.primeCompl, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using s.2
  exact ⟨r, s, hrs', hsU, hrs' ▸ a.isUnit.mul hsU⟩

/-- For `t ⤳ t'` on an integral `T` and `j : T ⟶ Y`, an element of `𝒪_{Y,j t'}` that becomes a
unit in `𝒪_{Y,j t}` has nonzero image in `𝒪_{T,t'}` and in `K(T)`. -/
private theorem stalkMap_ne_zero_of_isUnit_stalkSpecializes {T Y : Scheme.{u}} [IsIntegral T]
    (j : T ⟶ Y) {t t' : T} (h : t ⤳ t') (hsp : j t ⤳ j t') {x : Y.presheaf.stalk (j t')}
    (hx : IsUnit (Y.presheaf.stalkSpecializes hsp x)) :
    algebraMap (T.presheaf.stalk t') T.functionField ((j.stalkMap t').hom x) ≠ 0 ∧
      (j.stalkMap t').hom x ≠ 0 := by
  have h₁ : IsUnit (algebraMap (T.presheaf.stalk t') T.functionField ((j.stalkMap t').hom x)) := by
    rw [← MMP.Mori.algebraMap_stalkSpecializes h,
      ← Scheme.Hom.stalkSpecializes_stalkMap_apply j _ _ h x]
    exact (hx.map _).map _
  exact ⟨h₁.ne_zero, fun h₀ => h₁.ne_zero (by rw [h₀, map_zero])⟩

/-- If `a = r / s` in `𝒪_{Y,j η}` with `r, s ∈ 𝒪_{Y,j t}` and `η ⤳ t` the generic point of a
component `Z` of `T`, then `j^*a · s = r` in `K(T)`. -/
private theorem componentToFunctionField_stalkMap_mul_eq {T Y : Scheme.{u}} [IsIntegral T]
    (j : T ⟶ Y) {Z : irreducibleComponents T} {t : T} (h : componentGenericPoint T Z ⤳ t)
    (hsp : j (componentGenericPoint T Z) ⤳ j t)
    {a : (Y.presheaf.stalk (j (componentGenericPoint T Z)))ˣ} {r s : Y.presheaf.stalk (j t)}
    (hrs : a.val * Y.presheaf.stalkSpecializes hsp s = Y.presheaf.stalkSpecializes hsp r) :
    (MMP.Positivity.componentToFunctionField Z).hom
      (Units.map (j.stalkMap (componentGenericPoint T Z)).hom.toMonoidHom a).val *
        algebraMap (T.presheaf.stalk t) T.functionField ((j.stalkMap t).hom s) =
      algebraMap (T.presheaf.stalk t) T.functionField ((j.stalkMap t).hom r) := by
  have hcomp : ∀ x, (j.stalkMap _).hom (Y.presheaf.stalkSpecializes hsp x) =
      T.presheaf.stalkSpecializes h ((j.stalkMap t).hom x) := fun x =>
    Scheme.Hom.stalkSpecializes_stalkMap_apply j _ _ h x
  rw [← componentToFunctionField_stalkSpecializes T Z h,
    ← componentToFunctionField_stalkSpecializes T Z h, ← hcomp, ← hcomp, ← hrs, map_mul, map_mul]
  rfl

/-- If `φ` is a local equation of `G` on `U ∋ y'`, `a` the unit of `𝒪_{Y,y}` representing `φ`,
and `a = r / s` with `r, s ∈ 𝒪_{Y,y'}`, then the coefficient of `G` at a prime divisor through `y'`
is `ord r - ord s`. -/
private theorem coeff_eq_ord_sub_ord_of_mul_stalkSpecializes_eq {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {G : Divisor Y} {U : Y.Opens}
    {φ : (RationalFunctions Y)ˣ} (hφ : G.IsLocalEquation U φ) {y y' : Y} (hsp : y ⤳ y')
    (hy'U : y' ∈ U) {a : (Y.presheaf.stalk y)ˣ}
    (ha : (stalkToRationalFunctions Y (mem_pointComponent y)).hom a =
      (φ : RationalFunctions Y) (pointComponent y))
    {r s : Y.presheaf.stalk y'}
    (hrs : a.val * Y.presheaf.stalkSpecializes hsp s = Y.presheaf.stalkSpecializes hsp r)
    (hsU : IsUnit (Y.presheaf.stalkSpecializes hsp s)) {E : Mori.PrimeDivisor Y}
    (hE : y' ∈ E.support) :
    G E = Y.ord (algebraMap (Y.presheaf.stalk y') Y.functionField r) E.genericPoint -
      Y.ord (algebraMap (Y.presheaf.stalk y') Y.functionField s) E.genericPoint := by
  have h₁ := hφ E ⟨y', hE, hy'U⟩
  rw [MMP.Positivity.ord_eq_ord_componentToFunctionField,
    (subsingleton_irreducibleComponents (X := Y)).elim E.component (pointComponent y)] at h₁
  change G.coeff E = _
  rw [h₁, ← ha, componentToFunctionField_stalkToRationalFunctions]
  have hmul : algebraMap (Y.presheaf.stalk y) Y.functionField a.val *
      algebraMap (Y.presheaf.stalk y') Y.functionField s =
      algebraMap (Y.presheaf.stalk y') Y.functionField r := by
    rw [← MMP.Mori.algebraMap_stalkSpecializes hsp, ← MMP.Mori.algebraMap_stalkSpecializes hsp r,
      ← hrs, map_mul]
  refine ord_eq_sub_of_mul_eq ((a.isUnit.map _).ne_zero) ?_ hmul _
  rw [← MMP.Mori.algebraMap_stalkSpecializes hsp]
  exact (hsU.map _).ne_zero

/-- **Restriction to a smooth divisor is the Cartier pull-back.** For a smooth variety `Y` and a
smooth integral `j : T ⟶ Y` of codimension one, the restriction `G|_T` by intersection lengths is
the pull-back `j^*G` of every divisor `G` not containing `T`. -/
private theorem divisor_isPullback_restrict {k : Type u} [Field k] {Y T : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [Smooth sY]
    (j : T ⟶ Y) [IsClosedImmersion j] [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    [CompactSpace T] [Smooth (j ≫ sY)] (hcodim : Order.coheight (j (genericPoint T)) = 1)
    (G : Divisor Y) (hG : ∀ W : irreducibleComponents T, j (componentGenericPoint T W) ∉ G.supp) :
    G.IsPullback j hG (G.restrict j) := by
  classical
  have : AlgebraicGeometry.IsNoetherian T := ⟨⟩
  intro U φ hφ Q hQ
  set η := componentGenericPoint T Q.component
  have hηT : η = genericPoint T := componentGenericPoint_eq_genericPoint _
  have hgen : ∀ s : T, Order.coheight s = 0 → s = η := fun s hs => by
    have hle : s ≤ genericPoint T := genericPoint_specializes s
    rw [hηT]
    exact (Specializes.antisymm (Order.coheight_eq_zero.mp hs hle) hle).eq
  have hηQ : η ⤳ Q.genericPoint := Q.specializes_genericPoint
  set y' := j Q.genericPoint
  set y := j η with hydef
  have hsp : y ⤳ y' := j.base.hom.map_specializes hηQ
  have hy'U : y' ∈ U := (Q.genericPoint_mem_iff (j ⁻¹ᵁ U)).mpr hQ
  have hyG : y ∉ G.supp := hG Q.component
  have hpure : ∀ s : T, Order.coheight s = 0 → Order.coheight (j s) = 1 := fun s hs => by
    rw [hgen s hs, hηT]
    exact hcodim
  have hD : ∀ E ∈ G.support, ∀ s : T, Order.coheight s = 0 → j s ≠ E.genericPoint := by
    intro E hE s hs hjs
    rw [hgen s hs] at hjs
    refine hyG (DivisorWithCoeffs.support_subset_supp (Finsupp.mem_support_iff.mp hE) ?_)
    rw [hydef, hjs, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  rw [DivisorWithCoeffs.coeff_restrict_of_pure j G hpure hD Q]
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk (hsp.mem_open U.isOpen hy'U) hyG (mem_pointComponent y)
  rw [pullbackComponent_eq hG hφ _ (mem_pointComponent y) a ha]
  obtain ⟨r, s, hrs, hsU, hrU⟩ := exists_mul_stalkSpecializes_eq hsp a
  rw [ordUnit_eq_ord,
    ord_eq_sub_of_mul_eq (((Units.map (j.stalkMap η).hom.toMonoidHom a).isUnit.map _).ne_zero)
    (stalkMap_ne_zero_of_isUnit_stalkSpecializes j hηQ hsp hsU).1
    (componentToFunctionField_stalkMap_mul_eq j hηQ hsp hrs)]
  obtain ⟨Sr, -, hfr⟩ := Q.ord_stalkMap_eq_sum_intersectionLength_mul_ord sY j r
    (stalkMap_ne_zero_of_isUnit_stalkSpecializes j hηQ hsp hrU).2
  obtain ⟨Ss, -, hfs⟩ := Q.ord_stalkMap_eq_sum_intersectionLength_mul_ord sY j s
    (stalkMap_ne_zero_of_isUnit_stalkSpecializes j hηQ hsp hsU).2
  set S := G.support ∪ Sr ∪ Ss
  rw [hfr S (fun E hE => by simp [S, hE]), hfs S (fun E hE => by simp [S, hE]),
    ← Finset.sum_sub_distrib, Finsupp.sum, Finset.sum_subset (s₁ := G.support) (s₂ := S)
      (fun E hE => by simp [S, hE]) (fun E _ hE => by simp [Finsupp.notMem_support_iff.mp hE])]
  refine Finset.sum_congr rfl fun E _ => ?_
  by_cases hE : j Q.genericPoint ∈ E.support
  · simp only [hE, ↓reduceIte]
    rw [← mul_sub, nsmul_eq_mul,
      coeff_eq_ord_sub_ord_of_mul_stalkSpecializes_eq hφ hsp hy'U ha hrs hsU hE]
  · simp only [hE, ↓reduceIte, PrimeDivisor.intersectionLength_eq_zero_of_notMem j E hE, zero_smul,
      sub_zero]

/-- A closed immersion of an irreducible scheme onto the support of a prime divisor maps the
generic point to the generic point of the divisor. -/
private theorem map_genericPoint_eq {X T : Scheme.{u}} (j : T ⟶ X) [IsClosedImmersion j]
    [IrreducibleSpace T] (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X)) :
    j (genericPoint T) = P.genericPoint := by
  have h1 : IsGenericPoint (j (genericPoint T)) (P.support : Set X) := by
    have := (genericPoint_spec T).image j.base.hom.continuous
    rwa [Set.image_univ, j.isClosedEmbedding.isClosed_range.closure_eq, hP] at this
  have h2 : IsGenericPoint P.genericPoint (P.support : Set X) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isGenericPoint_closure
  exact h1.eq h2

/-- The generic point of a prime divisor `P` lies off the support of a divisor in which `P` has
coefficient zero. -/
private theorem genericPoint_notMem_supp_of_coeff_eq_zero {R : Type*} [Zero R] {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X]
    {G : DivisorWithCoeffs R X} {P : Mori.PrimeDivisor X} (hG : G.coeff P = 0) :
    P.genericPoint ∉ G.supp := by
  intro h
  obtain ⟨E, hE, hmem⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
  obtain rfl := MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support hmem
  exact hE hG

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- **Residue along a smooth divisor is Cartier restriction.** Let `Y` be a smooth variety over
a field `k` of dimension `n + 1`, `j : T ⟶ Y` the inclusion of a prime divisor `P` smooth over
`k`, `σ` a rational top form with `ord_P σ = -1` and `η'` its Poincaré residue along `T`
(`MMP.Fourfold.IsPoincareResidue`). Then `η' ≠ 0`, the generic point of `T` lies off the support
of `div(σ) + P`, and `div(η')` is the pull-back of `div(σ) + P` along `j`
(`MMP.Mori.Divisor.IsPullback`). Moreover, for every `ℚ`-Cartier `ℚ`-divisor `D` whose support
misses the generic point of `T`, and `Γ` with `div(σ) + Γ = D`, the restriction `R` of `Γ - P` to
`T` is defined and `div(η') + R = D|_T` (`MMP.Mori.QDivisor.IsPullback`). -/
@[mmp "lem_fourfold_smooth_divisor_cartier_residue"]
public theorem isPullback_divisorOfForm_add_of_isPoincareResidue
    {k : Type} [Field k] {Y T : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [IsNormal Y]
    [IsLocallyNoetherian Y] [CompactSpace Y] [LocallyOfFiniteType sY]
    (hY : AlgebraicGeometry.IsVariety k sY) [Smooth sY] {n : ℕ}
    (hdim : topologicalKrullDim Y = n + 1) (j : T ⟶ Y) [IsClosedImmersion j] [IsIntegral T]
    [IsNormal T] [IsLocallyNoetherian T] [CompactSpace T] [Smooth (j ≫ sY)]
    (P : Mori.PrimeDivisor Y) (hP : Set.range j.base = (P.support : Set Y))
    (σ : RationalPluriForms sY (n + 1) 1) (hσ0 : σ ≠ 0) (hσ : P.ordForm σ = -1)
    (η : RationalPluriForms (j ≫ sY) n 1) (hη : IsPoincareResidue sY j n 1 σ η) :
    η ≠ 0 ∧
    (∃ hgen : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉
        (divisorOfForm σ + Finsupp.single P 1).supp,
      (divisorOfForm σ + Finsupp.single P 1).IsPullback j hgen (divisorOfForm η)) ∧
    ∀ (D Γ : QDivisor Y), D.IsQCartier →
      (hD : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ D.supp) →
      Divisor.toQDivisor (divisorOfForm σ) + Γ = D →
      ∃ R : QDivisor T,
        (∃ hgen' : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉
            (Γ - Finsupp.single P 1).supp,
          (Γ - Finsupp.single P 1).IsPullback j hgen' R) ∧
        D.IsPullback j hD (Divisor.toQDivisor (divisorOfForm η) + R) := by
  classical
  have hjT : j (genericPoint T) = P.genericPoint := map_genericPoint_eq j P hP
  have hcgp : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) = P.genericPoint :=
    fun Z => by rw [componentGenericPoint_eq_genericPoint, hjT]
  have hsmY : IsSmoothScheme sY := (isSmoothScheme_iff sY).mpr inferInstance
  obtain ⟨η₀, hη₀, hη₀0, hdiv, -⟩ :=
    existsUnique_isPoincareResidue_of_ordForm_eq_neg_one sY hdim j P hjT σ hσ0 hσ
  obtain rfl : η = η₀ := (hη₀ η).mp hη
  set K : Divisor Y := divisorOfForm σ + Finsupp.single P 1
  have hKP : K.coeff P = 0 := by
    rw [DivisorWithCoeffs.coeff_add, coeff_divisorOfForm, DivisorWithCoeffs.coeff_single_self, hσ]
    rfl
  have hKgen : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ K.supp :=
    fun Z => by rw [hcgp]; exact genericPoint_notMem_supp_of_coeff_eq_zero hKP
  have hKpull := divisor_isPullback_restrict sY j (by rw [hjT]; exact P.coheight_genericPoint)
    K hKgen
  rw [← hdiv] at hKpull
  refine ⟨hη₀0, ⟨hKgen, hKpull⟩, ?_⟩
  intro D Γ hDq hD hΓ
  have hKc : K.IsCartier := isCartier_of_isSmoothScheme hsmY K
  have hKQ := QDivisor.isPullback_toQDivisor hKc
    (by simpa only [Divisor.supp_toQDivisor] using hKgen) hKpull
  have hDP : D.coeff P = 0 := by
    by_contra hne
    refine hD (pointComponent (genericPoint T)) ?_
    rw [hcgp, DivisorWithCoeffs.mem_supp_iff]
    refine ⟨P, hne, ?_⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  set Γ₁ := Γ - Finsupp.single P (1 : ℚ)
  have hΓ₁P : Γ₁.coeff P = 0 := by
    rw [← hΓ, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm, hσ]
      at hDP
    rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_single_self]
    push_cast at hDP
    linarith
  have hΓ₁gen : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ Γ₁.supp :=
    fun Z => by rw [hcgp]; exact genericPoint_notMem_supp_of_coeff_eq_zero hΓ₁P
  have hΓ₁q : Γ₁.IsQCartier := isQCartier_of_isSmoothScheme hsmY Γ₁
  obtain ⟨R, hR, -⟩ := hΓ₁q.existsUnique_isPullback hΓ₁gen
  refine ⟨R, ⟨hΓ₁gen, hR⟩, ?_⟩
  have hDeq : Divisor.toQDivisor K + Γ₁ = D := by
    rw [← hΓ]
    ext E
    obtain rfl | hE := eq_or_ne P E
    · simp [K, Γ₁, Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_single_self]
    · simp [K, Γ₁, Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_single_of_ne hE]
  subst hDeq
  exact hKQ.add (QDivisor.isQCartier_toQDivisor hKc) hΓ₁q hR hD

end MMP.Fourfold
