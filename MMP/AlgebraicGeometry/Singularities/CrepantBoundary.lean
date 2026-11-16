module

public import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
public import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
public import MMP.AlgebraicGeometry.MMP.Abundance.Basic

/-!
# Crepant boundaries and discrepancies under birational morphisms

Let `(X, Δ)` be a pair over a perfect field `k`, with canonical divisor `K` of dimension `n`.

A divisor `(Y, f, E)` over `X` which is not exceptional has as center a prime divisor `D` of
`X`, and its discrepancy is `a(E, X, Δ) = -coeff_D(Δ)`.

For a (not necessarily proper) birational morphism `f : Y ⟶ X` from a normal variety, only
finitely many prime divisors `F` of `Y` have nonzero discrepancy: `f` is an injective local
isomorphism on a dense open `W ⊆ Y`, the prime divisors with generic point outside `W` are among
the finitely many codimension-one points of `Y ∖ W`, and a prime divisor with generic point in `W`
is not exceptional, so has discrepancy `-coeff_D(Δ)` for the prime divisor `D` through its image.
Hence the crepant boundary `Δ_Y = -∑_F a(F, X, Δ) F` exists, and it is unique since discrepancies
are. If `m(K + Δ)` is Cartier then `m Δ_Y` is a divisor, since `m · a(F, X, Δ) = ord_F(f^*τ)` for
a local generator `τ` of `𝒪_X(m(K + Δ))`; and `f^*τ` generates `𝒪_Y(m(K_Y + Δ_Y))` on `f⁻¹(U)`.

For compatible canonical divisors `K_X = div_X(ω)`, `K_Y = div_Y(f^*ω)` (or `f` proper with
`f_*K_Y = K_X`), the divisor `m(K_Y + Δ_Y)` is then the Cartier pull-back `f^*(m(K_X + Δ))`: if
`φ` is a local equation of `m(K_X + Δ)` on `U`, then `τ = ω^{⊗m}/φ` generates
`𝒪_X(m(K_X + Δ))` there, and comparing orders of `f^*τ` along prime divisors of `Y` gives the
pull-back relation. Consequently `(Y, Δ_Y)` is a pair, and discrepancies are invariant under
crepant pull-back: by the functoriality `g^* f^* τ = (f ∘ g)^* τ` of the pull-back of forms, a
divisor `(W, g, F)` over `Y` has `a(F, Y, Δ_Y) = a(F, X, Δ)`.

Finally, on a smooth projective variety `Y` of dimension `n`, the degree-`n` homogeneous part of
a polynomial `P` with `P(u) = χ(Y, 𝒪_Y(∑ᵢ uᵢ Dᵢ + ⌈A⌉))` on `ℤᵏ` is `u ↦ ((∑ᵢ uᵢ Dᵢ)ⁿ) / n!`.

## Main results

* `MMP.Mori.DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff`: the center of a
  non-exceptional divisor over a pair is a prime divisor `D`, and `-coeff_D(Δ)` is its
  discrepancy.
* `MMP.Mori.IsPair.existsUnique_isCrepantBoundary`: the crepant boundary exists and is unique,
  and `m Δ_Y` is a divisor whenever `m(K + Δ)` is a Cartier divisor.
* `MMP.Mori.IsPair.generatesOn_pullbackRationalPluriForms`: `f^*τ` generates
  `𝒪_Y(m(K_Y + Δ_Y))` on `f⁻¹(U)`.
* `MMP.Mori.IsPair.isPullback_of_isCrepantBoundary`: `m(K_Y + Δ_Y) = f^*(m(K_X + Δ))` as Cartier
  divisors whenever `m(K_X + Δ)` is Cartier, `(Y, Δ_Y)` is a pair, and
  `K_Y + Δ_Y = f^*(K_X + Δ)` as `ℚ`-divisors.
* `MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant`: `(Y, Δ_Y)` is a pair, and for a divisor `E`
  over `Y` and a divisor `E'` over `X` inducing the same valuation of `k(X)`, a rational number
  is the discrepancy of `E` over `(Y, Δ_Y)` exactly when it is that of `E'` over `(X, Δ)`.
* `MMP.Mori.Divisor.eval_homogeneousComponent_of_eulerPolynomial`: the value at `u ∈ ℤᵏ` of the
  degree-`n` homogeneous component of `P` is `((∑ᵢ uᵢ Dᵢ)ⁿ) / n!`.

## Implementation notes

As in `MMP.Mori.IsDiscrepancy`, "`a` is the discrepancy `a(E, X, Δ)`" is a predicate on `a`,
which over a perfect field determines `a` (`MMP.Mori.IsDiscrepancy.eq`). The base field is
assumed perfect, as in Kollár–Mori 2.25. Over an imperfect field the description of the
discrepancy of a non-exceptional divisor fails: for `k = 𝔽_p(t)` and `X` the affine line over
`k(t^{1/p})`, viewed over `k`, the module of differentials `Ω_{X/k}` is free of rank `2`, so
`K = 0` is a canonical divisor and `(X, 0)` is a pair, yet no discrepancy exists for the prime
divisor `[0]`.

A `ℚ`-divisor is a finitely supported function on prime divisors, so the existence of `Δ_Y` with
`coeff_F(Δ_Y) = -a(F, X, Δ)` for all `F` contains the finiteness of the set of prime divisors of
`Y` with nonzero discrepancy. "`σ` generates `𝒪_Y(m(K_Y + Δ_Y))` on `V`" is
`MMP.Mori.GeneratesOn Δ_Y m V σ`, phrased through orders along prime divisors.

The pull-back of a divisor `B` along `f` is defined under the condition that `f` maps no generic
point of a component of `Y` into `Supp B`; for a birational morphism this holds, and the
conclusion asserts it together with the pull-back relation. The push-forward `f_*K_Y` is the
birational transform `MMP.Mori.RationalMap.transformDivisor`.

A divisor `(W, g, F)` over `Y` is regarded as a divisor over `X` through any divisor `E'` over
`X` whose valuation of `k(X)` is the restriction of that of `F` along `f^* : k(X) → k(Y)`; the
divisor `(W, f ∘ g, F)` is one such, and by the independence of discrepancies of the model the
statement for it is equivalent to the statement for all of them.

For the Euler characteristic, the polynomial `P` is given together with the hypothesis that it
interpolates `MMP.Mori.Divisor.eulerPolynomial` on `ℤᵏ`. Kollár–Mori expand
`((k₀ L₀ + ∑ᵢ kᵢ Lᵢ)ⁿ)`, with `L₀ = ⌈A⌉`, by multilinearity of the intersection number. Here the
comparison is made on the Snapper polynomial `Q` of `(L₀, D₁, …, D_k)`: `P(u) = Q(1, u)`, and for
fixed `u` the coefficient of `tⁿ` in `t ↦ Q(c, t u)` is the degree-`n` component of `Q` at
`(0, u)` whatever `c` is; at `c = 1` it is the degree-`n` component of `P` at `u`, and at `c = 0`
it is `1/n!` times the `n`-th finite difference defining `((∑ᵢ uᵢ Dᵢ)ⁿ)`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.25, 2.26,
  2.30, 3.4
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

/-! ### The discrepancy of a non-exceptional divisor -/

namespace MMP.Mori.DivisorOver

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X} {Δ : QDivisor X}

/-- **The discrepancy of a non-exceptional divisor** (Kollár–Mori 2.25: `a(D_i, X, Δ) = -a_i`).
Let `(X, Δ)` be a pair with canonical divisor `K` of dimension `n`, and `(Y, f, E)` a divisor
over `X` which is not exceptional over `X`, over a perfect field `k`. Then `center_X E` is a prime
divisor `D` of `X`, and `-coeff_D(Δ)` is the discrepancy `a(E, X, Δ)`: `E` has the valuation of
`D`, so `ord_E(f^*τ) = ord_D(τ)` for a local generator `τ` of `𝒪_X(m(K + Δ))` near the generic
point of `D`, and `ord_D(τ) = -m · coeff_D(Δ)`. -/
@[mmp "lem_km2b_discrepancy_nonexceptional"]
theorem exists_center_eq_isDiscrepancy_neg_coeff [PerfectField k] (hΔ : IsPairWith sX n K Δ)
    (E : DivisorOver k sX) (hE : ¬ E.IsExceptional) :
    ∃ D : PrimeDivisor X, (E.center : Set X) = D.support ∧
      IsDiscrepancy sX n K Δ E (-Δ.coeff D) := by
  obtain ⟨hX, hK, hC⟩ := id hΔ
  obtain ⟨P, hv⟩ :=
    MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX E hE
  have hx : E.f E.E.genericPoint = P.genericPoint :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hv
  have hsupp : (P.support : Set X) = closure {P.genericPoint} := P.support_eq_closure
  refine ⟨P, ?_, ?_⟩
  · rw [MMP.Positivity.DivisorOver.center_eq_closureSingleton, hsupp, ← hx]
    rfl
  · obtain ⟨m, hm, hmC⟩ := hC.exists_pos
    obtain ⟨-, U, hU, τ, hτ⟩ :=
      MMP.Positivity.IsPair.exists_generatesOn hΔ.isPair hK hmC P.genericPoint
    refine ⟨hX, hK, m, hm, hmC, U, hx ▸ hU, τ, hτ, ?_⟩
    rw [MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hX
        hK.topologicalKrullDim_eq hv τ,
      DivisorOver.ordPullback_ofPrimeDivisor hX hK.topologicalKrullDim_eq P τ]
    linear_combination -hτ.2 P ⟨P.genericPoint, hsupp ▸ subset_closure rfl, hU⟩

end MMP.Mori.DivisorOver

namespace MMP.Mori.IsPair

open TopologicalSpace

/-! ### Existence and uniqueness of the crepant boundary -/

/-- An exceptional prime divisor of a morphism maps its generic point to a point of coheight at
least two. -/
private theorem two_le_coheight_of_isExceptional {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {f : Y ⟶ X} (E : MMP.Mori.PrimeDivisor Y)
    (hE : RationalMap.IsExceptional (X := Y) f.toRationalMap E) :
    2 ≤ Order.coheight (f E.genericPoint) := by
  set η := E.genericPoint
  have hdef : RationalMap.DefinedAt (X := Y) f.toRationalMap η := by
    rw [RationalMap.DefinedAt, RationalMap.dom_toRationalMap_hom]
    trivial
  have h2 := (RationalMap.isExceptional_iff.mp hE) hdef
  have hsub : (IrreducibleCloseds.closureSingleton (f η) : Set X) ⊆
      (RationalMap.transform (X := Y) f.toRationalMap E.idealSheaf.support : Set X) := by
    rw [IrreducibleCloseds.coe_closureSingleton]
    refine (Closeds.isClosed _).closure_subset_iff.mpr ?_
    rintro _ rfl
    refine RationalMap.image_subset_transform f.toPartialMap rfl _ ?_
    rw [MMP.Positivity.image_toPartialMap_hom]
    refine ⟨η, ?_, rfl⟩
    change η ∈ E.support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hle := le_closedsCodimension_iff.mp h2 _ hsub
  have hcodim : codimension (IrreducibleCloseds.closureSingleton (f η)) =
      Order.coheight (f η) := by
    have h : IrreducibleCloseds.closureSingleton (f η) = irreducibleSetEquivPoints.symm (f η) :=
      IrreducibleCloseds.ext (by
        rw [IrreducibleCloseds.coe_closureSingleton, coe_irreducibleEquivPoints_symm_apply])
    rw [codimension_eq_coheight, h]
    exact Order.coheight_orderIso irreducibleSetEquivPoints.symm (f η)
  rwa [hcodim] at hle

/-- **A birational morphism is an injective local isomorphism near the generic point.** For a
birational morphism `f : Y ⟶ X` of integral schemes with `X` separated, there is an open `W ∋ η_Y`
on which `f` is injective and preserves coheights. -/
private theorem exists_injOn_coheight_eq {X Y : Scheme.{u}} [IsIntegral Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] {f : Y ⟶ X} (hf : IsBirationalMorphism f) :
    ∃ W : Y.Opens, genericPoint Y ∈ W ∧ Set.InjOn f W ∧
      ∀ y ∈ W, Order.coheight (f y) = Order.coheight y := by
  obtain ⟨e, he⟩ := hf
  have hcomp : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
    ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
      (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm
  have hfe (u : e.source.toScheme) : f u.1 = (e.iso.hom ≫ e.target.ι) u := by
    rw [← hcomp, Scheme.Hom.comp_apply]
    rfl
  obtain ⟨y₀⟩ : Nonempty e.source := e.dense_source.nonempty.to_subtype
  refine ⟨e.source,
    ((genericPoint_spec Y).mem_open_set_iff e.source.isOpen).mpr ⟨y₀.1, trivial, y₀.2⟩,
    fun y₁ h₁ y₂ h₂ h => congrArg Subtype.val ((e.iso.hom ≫ e.target.ι).isOpenEmbedding.injective
      (((hfe ⟨y₁, h₁⟩).symm.trans h).trans (hfe ⟨y₂, h₂⟩))), fun y hy => ?_⟩
  let u : e.source.toScheme := ⟨y, hy⟩
  rw [hfe u, coheight_eq_of_isOpenImmersion, ← coheight_eq_of_isOpenImmersion e.source.ι]
  rfl

/-- **The discrepancy of a non-exceptional prime divisor is minus a coefficient of the boundary,
at the prime divisor through its image.** If `f` maps the generic point of a prime divisor `F` of
`Y` to a point of coheight one, then `a(F, X, Δ) = -coeff_D(Δ)` for the prime divisor `D` of `X`
with generic point `f(η_F)`. -/
private theorem exists_discrepancy_eq_neg_coeff {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {Y : Scheme.{u}}
    {f : Y ⟶ X} {hY : IsNormalVariety k (f ≫ sX)} {hf : IsBirationalMorphism f}
    {F : MMP.Mori.PrimeDivisor Y} {a : ℚ} (ha : IsDiscrepancy sX n K Δ ⟨Y, f, hY, hf, F⟩ a)
    (h1 : Order.coheight (f F.genericPoint) = 1) :
    ∃ D : MMP.Mori.PrimeDivisor X, a = -Δ.coeff D ∧ D.genericPoint = f F.genericPoint := by
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsNormal Y := hY.2
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have hE : ¬ (⟨Y, f, hY, hf, F⟩ : DivisorOver k sX).IsExceptional := fun hE => by
    have h2 := two_le_coheight_of_isExceptional (f := f) F hE
    rw [h1] at h2
    exact absurd h2 (by decide)
  obtain ⟨hX, hK, m, hm, hC, -⟩ := id ha
  obtain ⟨D, hc, hD⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff
    ⟨hX, hK, m, by exact_mod_cast hm.ne', hC⟩ _ hE
  refine ⟨D, ha.eq hD, ?_⟩
  have h := (⟨Y, f, hY, hf, F⟩ : DivisorOver k sX).isGenericPoint_center
  rw [hc] at h
  exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure D ▸ isGenericPoint_closure).eq h

/-- **Only finitely many prime divisors of `Y` have nonzero discrepancy.** Off the open set where
`f` is an isomorphism there are finitely many prime divisors of `Y`; on it, `F ↦ f(η_F)` is
injective and a prime divisor with nonzero discrepancy is sent into the support of `Δ`. -/
private theorem finite_setOf_discrepancy_ne_zero {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X} {Δ : QDivisor X} (hX : IsNormalVariety k sX)
    {Y : Scheme.{u}} {f : Y ⟶ X} {hY : IsNormalVariety k (f ≫ sX)} {hf : IsBirationalMorphism f}
    {a : MMP.Mori.PrimeDivisor Y → ℚ}
    (ha : ∀ F, IsDiscrepancy sX n K Δ ⟨Y, f, hY, hf, F⟩ (a F)) :
    {F | a F ≠ 0}.Finite := by
  have := hY.1
  have : IsIntegral Y := hY.1.toIsIntegral
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  have : AlgebraicGeometry.IsNoetherian Y := ⟨⟩
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  obtain ⟨W, hη, hinj, hcoh⟩ := exists_injOn_coheight_eq hf
  have hA : {F : MMP.Mori.PrimeDivisor Y | F.genericPoint ∉ W}.Finite := by
    refine Set.Finite.of_finite_image
      ((MMP.Mori.finite_coheight_eq_one_mem_closure_notMem (genericPoint Y) W hη).subset ?_)
      AlgebraicGeometry.PrimeDivisor.genericPoint_injective.injOn
    rintro - ⟨F, hF, rfl⟩
    exact ⟨by rw [(genericPoint_spec Y).def]; trivial, hF, F.coheight_genericPoint⟩
  have hB : {F : MMP.Mori.PrimeDivisor Y | F.genericPoint ∈ W ∧
      f F.genericPoint ∈ (·.genericPoint) '' (Δ.support : Set (MMP.Mori.PrimeDivisor X))}.Finite :=
    ((Δ.support.finite_toSet.image _).subset (by rintro - ⟨F, hF, rfl⟩; exact hF.2)).of_finite_image
      fun _ h₁ _ h₂ h => AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hinj h₁.1 h₂.1 h)
  refine (hA.union hB).subset fun F hF => (em (F.genericPoint ∈ W)).symm.imp id fun hW => ?_
  obtain ⟨D, haD, hD⟩ := exists_discrepancy_eq_neg_coeff (ha F)
    ((hcoh _ hW).trans F.coheight_genericPoint)
  refine ⟨hW, D, ?_, hD⟩
  rw [Finset.mem_coe, Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply]
  exact fun h0 => hF (by rw [haD, h0, neg_zero])

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X}
  {Δ : QDivisor X}

/-- **`m` times a discrepancy is an integer when `m(K + Δ)` is Cartier**, `m > 0`: for a local
generator `τ` of `𝒪_X(m(K + Δ))` at the center, `m · a(E, X, Δ) = ord_E(f^*τ)`. -/
private theorem exists_natCast_mul_eq_intCast (hP : IsPair sX Δ)
    (hK : K.IsCanonicalDivisor sX n) {E : DivisorOver k sX} {a : ℚ}
    (ha : IsDiscrepancy sX n K Δ E a) {m : ℕ} (hm : 0 < m)
    (hC : ((m : ℤ) • (Divisor.toQDivisor K + Δ)).IsCartierDivisor) :
    ∃ z : ℤ, (m : ℚ) * a = z := by
  obtain ⟨-, U, hU, τ, hτ⟩ :=
    MMP.Positivity.IsPair.exists_generatesOn hP hK hC (E.f E.E.genericPoint)
  have hm' : (m : ℚ) ≠ 0 := by positivity
  refine ⟨E.ordPullback τ, ?_⟩
  rw [ha.eq (show IsDiscrepancy sX n K Δ E (E.ordPullback τ / m) from
    ⟨ha.1, hK, m, hm, hC, U, hU, τ, hτ, by field_simp⟩)]
  field_simp

/-- **`m` times a discrepancy is an integer when `m(K + Δ)` is Cartier**, for every integer `m`. -/
private theorem exists_intCast_mul_eq_intCast (hP : IsPair sX Δ)
    (hK : K.IsCanonicalDivisor sX n) {E : DivisorOver k sX} {a : ℚ}
    (ha : IsDiscrepancy sX n K Δ E a) {m : ℤ}
    (hC : (m • (Divisor.toQDivisor K + Δ)).IsCartierDivisor) :
    ∃ z : ℤ, (m : ℚ) * a = z := by
  obtain ⟨j, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rcases j.eq_zero_or_pos with rfl | hj
    · exact ⟨0, by simp⟩
    exact exists_natCast_mul_eq_intCast hP hK ha hj hC
  · rcases j.eq_zero_or_pos with rfl | hj
    · exact ⟨0, by simp⟩
    obtain ⟨z, hz⟩ := exists_natCast_mul_eq_intCast hP hK ha hj
      (by
        rw [neg_smul] at hC
        simpa using hC.neg)
    exact ⟨-z, by push_cast; rw [neg_mul, hz]⟩

/-- **The crepant boundary exists** (Kollár–Mori 2.26). Let `(X, Δ)` be a pair over a perfect
field, `K` a canonical divisor of `X` of dimension `n`, and `f : Y ⟶ X` a birational morphism from
a normal variety `Y`. Then there is a unique `ℚ`-divisor `Δ_Y` on `Y` with
`coeff_F(Δ_Y) = -a(F, X, Δ)` for every prime divisor `F` of `Y`; and if `m(K + Δ)` is a Cartier
divisor, then `m Δ_Y` is a divisor. -/
@[mmp "lem_km2b_crepant_boundary_exists"]
theorem existsUnique_isCrepantBoundary (hP : IsPair sX Δ)
    (hK : K.IsCanonicalDivisor sX n) {Y : Scheme.{u}} (f : Y ⟶ X)
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) :
    (∃! ΔY : QDivisor Y, IsCrepantBoundary sX n K Δ f hY hf ΔY) ∧
      ∀ ΔY : QDivisor Y, IsCrepantBoundary sX n K Δ f hY hf ΔY → ∀ m : ℤ,
        (m • (Divisor.toQDivisor K + Δ)).IsCartierDivisor →
          m • ΔY ∈ Set.range (Divisor.toQDivisor (X := Y)) := by
  have ha F :=
    MMP.Positivity.IsPair.exists_isDiscrepancy hP hK (⟨Y, f, hY, hf, F⟩ : DivisorOver k sX)
  have haF F := isDiscrepancy_discrepancy (ha F)
  let ΔY : QDivisor Y := Finsupp.ofSupportFinite (fun F => -discrepancy sX n K Δ _ (ha F))
    ((finite_setOf_discrepancy_ne_zero hP.isNormalVariety haF).subset fun F hF => by simpa using hF)
  have hΔY : IsCrepantBoundary sX n K Δ f hY hf ΔY := fun F => by
    simpa [ΔY, DivisorWithCoeffs.coeff_apply, Finsupp.ofSupportFinite_coe] using haF F
  refine ⟨⟨ΔY, hΔY, fun ΔY' hΔY' => ?_⟩, fun ΔY' hΔY' m hm => ?_⟩
  · ext F
    exact neg_injective ((hΔY' F).eq (hΔY F))
  · refine (QDivisor.mem_range_toQDivisor_iff _).2 fun F => ?_
    obtain ⟨z, hz⟩ := exists_intCast_mul_eq_intCast hP hK (hΔY' F) hm
    refine ⟨-z, ?_⟩
    rw [DivisorWithCoeffs.coeff_apply, Finsupp.smul_apply, zsmul_eq_mul,
      ← DivisorWithCoeffs.coeff_apply]
    push_cast
    linarith

/-! ### Pull-backs of local generators -/

/-- The pull-back of a nonzero rational pluricanonical form along a birational morphism of
varieties over a perfect field is nonzero, since `f^* : k(X) → k(Y)` is an isomorphism. -/
private theorem pullbackRationalPluriForms_ne_zero [LocallyOfFiniteType sX] {Y : Scheme.{u}}
    [IsIntegral Y] (f : Y ⟶ X) [IsDominant f] (hf : IsBirationalMorphism f) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d) {m : ℤ}
    {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) :
    pullbackRationalPluriForms sX f τ ≠ 0 := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f
    hf.functionFieldMap_bijective hd
  intro h0
  refine repr_ne_zero_of_ne_zero (basisOfSpanSingleton hω.1 hω.ne_zero) hτ
    ((map_eq_zero_iff _ (algebraMap X.functionField Y.functionField).injective).mp ?_)
  rw [show (pullbackRationalPluriForms sX f τ : RationalPluriForms (f ≫ sX) d m) =
    pullbackFormsAlong hω m τ from pullbackForms_eq hω m τ] at h0
  rw [← repr_pullbackFormsAlong hω m τ]
  simp only [h0]
  erw [LinearEquiv.map_zero]
  rfl

/-- **Pull-backs of local generators** (Kollár–Mori 2.26, 2.30). Let `(X, Δ)` be a pair over a
perfect field with canonical divisor `K` of dimension `n`, `f : Y ⟶ X` a birational morphism from
a normal variety, and `Δ_Y` the crepant boundary of `(X, Δ)` on `Y`. If `m > 0`, `m(K + Δ)` is a
Cartier divisor and `τ` generates `𝒪_X(m(K + Δ))` on an open `U`, then `f^*τ` generates
`𝒪_Y(m(K_Y + Δ_Y))` on `f⁻¹(U)`: for a prime divisor `F` meeting `f⁻¹(U)`, the triple
`(m, U, τ)` computes `a(F, X, Δ) = -coeff_F(Δ_Y)`, so `ord_F(f^*τ) = -m · coeff_F(Δ_Y)`. -/
@[mmp "lem_km2b_pullback_generator_divisor"]
theorem generatesOn_pullbackRationalPluriForms (hP : IsPair sX Δ)
    (hK : K.IsCanonicalDivisor sX n) {Y : Scheme.{u}} (f : Y ⟶ X)
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) {ΔY : QDivisor Y}
    (hΔY : IsCrepantBoundary sX n K Δ f hY hf ΔY) {m : ℕ} (hm : 0 < m)
    (hC : ((m : ℤ) • (Divisor.toQDivisor K + Δ)).IsCartierDivisor) {U : X.Opens}
    {τ : RationalPluriForms sX n m} (hτ : GeneratesOn Δ m U τ) :
    haveI : IsIntegral Y := hY.1.toIsIntegral
    haveI : IsLocallyNoetherian Y :=
      haveI := hY.1.toLocallyOfFiniteType
      LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
    haveI : IsDominant f := hf.isDominant
    GeneratesOn ΔY m (f ⁻¹ᵁ U) (pullbackRationalPluriForms sX f τ) := by
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsLocallyNoetherian Y :=
    haveI := hY.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have : IsDominant f := hf.isDominant
  have : LocallyOfFiniteType sX := hP.1.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX)
    hK.topologicalKrullDim_eq
  refine ⟨pullbackRationalPluriForms_ne_zero f hf hd hτ.1, fun F hF => ?_⟩
  obtain ⟨x, hxF, hxU⟩ := hF
  have hgen : f F.genericPoint ∈ U := by
    rw [F.support_eq_closure, ← specializes_iff_mem_closure] at hxF
    exact (hxF.map f.continuous).mem_open U.2 hxU
  have := (hΔY F).eq (a' := (F.ordForm (pullbackRationalPluriForms sX f τ) : ℚ) / m)
    ⟨hP.1, hK, m, hm, hC, U, hgen, τ, hτ, by field_simp; rfl⟩
  rw [eq_div_iff (by exact_mod_cast hm.ne')] at this
  change (F.ordForm (pullbackRationalPluriForms sX f τ) : ℚ) + _ = 0
  linarith

/-! ### The crepant boundary computes the pull-back of `K_X + Δ` -/

/-- The order along a prime divisor `E` of `Y` of the pull-back `f^*_i φ` of a local equation
`φ` is the order of `f^*φ ∈ k(Y)` at the generic point of `E`. -/
private theorem ordUnit_pullbackComponent_eq_ord {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {f : Y ⟶ X} [IsDominant f] {C : Divisor X}
    (hC : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ C.supp) {U : X.Opens}
    {φ : (RationalFunctions X)ˣ} (hφ : C.IsLocalEquation U φ) (E : MMP.Mori.PrimeDivisor Y)
    (hE : (E.support ∩ f ⁻¹ᵁ U).Nonempty) (Z : irreducibleComponents X) :
    E.ordUnit (pullbackComponent f hC hφ E.component (E.map_componentGenericPoint_mem f hE)) =
      Y.ord (functionFieldMap f
        (MMP.Threefold.Mori.Helpers.evalFF Z (φ : RationalFunctions X))) E.genericPoint := by
  classical
  have hZp := E.map_componentGenericPoint_mem f hE
  have hW := mem_pointComponent (f (componentGenericPoint Y E.component))
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hZp (hC _) hW
  rw [pullbackComponent_eq hC hφ hZp hW a ha]
  set u := Units.map (f.stalkMap (componentGenericPoint Y E.component)).hom.toMonoidHom a
  let ψ : (RationalFunctions Y)ˣ :=
    (RationalFunctions.unitsEquiv Y).symm (Function.update 1 E.component u)
  have hψZ : (ψ : RationalFunctions Y) E.component = u := by
    simp [ψ, RationalFunctions.unitsEquiv]
  have h1 : E.ordUnit u = E.ord ψ := by
    rw [PrimeDivisor.ord_eq_ordUnit]
    congr 1
    exact (Units.ext hψZ).symm
  rw [h1, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord]
  congr 1
  obtain rfl : Z = pointComponent (f (componentGenericPoint Y E.component)) :=
    Subsingleton.elim (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents) _ _
  change (Y.presheaf.stalkSpecializes _).hom ((ψ : RationalFunctions Y) E.component) =
    functionFieldMap f ((X.presheaf.stalkSpecializes _).hom
      ((φ : RationalFunctions X) _))
  rw [hψZ, ← ha]
  change _ = functionFieldMap f ((stalkToRationalFunctions X hW ≫
    X.presheaf.stalkSpecializes _).hom a)
  rw [stalkToRationalFunctions, TopCat.Presheaf.stalkSpecializes_comp]
  exact (functionFieldMap_algebraMap_stalk f (componentGenericPoint Y E.component) a.val).symm

/-- `v(c^m g⁻¹) = m v(c) - v(g)`. -/
private theorem ord_zpow_mul_inv {Z : Scheme.{u}} [IsIntegral Z] [IsLocallyNoetherian Z] (z : Z)
    {c g : Z.functionField} (hc : c ≠ 0) (hg : g ≠ 0) (m : ℤ) :
    Z.ord (c ^ m * g⁻¹) z = m * Z.ord c z - Z.ord g z := by
  rw [Scheme.ord_mul (zpow_ne_zero _ hc) (inv_ne_zero hg), MMP.Mori.ord_zpow _ hc,
    ← zpow_neg_one, MMP.Mori.ord_zpow _ hg]
  ring

/-- **A local generator of `𝒪_X(m(K_X + Δ))`.** With `K_X = div_X(ω)`, `b` a basis of the top
forms, `c` the coefficient of `ω` in `b`, and `φ` a local equation on `U` of `D = m(K_X + Δ)`
evaluated to `g`, the form `c^m g⁻¹ · b^{⊗m}` generates `𝒪_X(m(K_X + Δ))` on `U`. -/
private theorem generatesOn_smul_basis [CompactSpace X] [LocallyOfFiniteType sX] {KX : Divisor X}
    (hKX : KX.IsCanonicalDivisor sX n) {ω : RationalPluriForms sX n 1} (hω0 : ω ≠ 0)
    (hωK : divisorOfForm ω = KX) {m : ℕ} {D : Divisor X}
    (hD : Divisor.toQDivisor D = (m : ℤ) • (Divisor.toQDivisor KX + Δ)) {U : X.Opens}
    {φ : (RationalFunctions X)ˣ} (hφ : D.IsLocalEquation U φ)
    (b : letI := functionFieldAlgebra sX
      Module.Basis Unit X.functionField (⋀[X.functionField]^n Ω[X.functionField⁄k]))
    (Z0 : irreducibleComponents X) :
    letI := functionFieldAlgebra sX
    GeneratesOn Δ m U ((((ZTensorPower.basis b 1).repr ω ()) ^ (m : ℤ) *
      (MMP.Threefold.Mori.Helpers.evalFF Z0 (φ : RationalFunctions X))⁻¹) •
        ZTensorPower.basis b (m : ℤ) ()) := by
  let := functionFieldAlgebra sX
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX)
    hKX.topologicalKrullDim_eq
  set c := (ZTensorPower.basis b 1).repr ω () with hc_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hω0
  set g := MMP.Threefold.Mori.Helpers.evalFF Z0 (φ : RationalFunctions X)
  have hg : g ≠ 0 := (φ.isUnit.map _).ne_zero
  set c'' : X.functionField := c ^ (m : ℤ) * g⁻¹ with hc''_def
  have hc'' : c'' ≠ 0 := mul_ne_zero (zpow_ne_zero _ hc) (inv_ne_zero hg)
  set τ : RationalPluriForms sX n m := c'' • ZTensorPower.basis b (m : ℤ) ()
  have hτr : (ZTensorPower.basis b (m : ℤ)).repr τ () = c'' := by simp [τ]
  have hτ0 : τ ≠ 0 := smul_ne_zero hc'' ((ZTensorPower.basis b (m : ℤ)).ne_zero ())
  refine ⟨hτ0, fun Γ hΓ => ?_⟩
  obtain ⟨NΓ, hNΓ⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
  have h1 : (KX.coeff Γ : ℤ) = X.ord c Γ.genericPoint + NΓ := by
    rw [← hωK, coeff_divisorOfForm, hNΓ 1 ω hω0]
    simp [hc_def]
  have h2 : (Γ.ordForm τ : ℤ) = m * X.ord c Γ.genericPoint - X.ord g Γ.genericPoint
      + m * NΓ := by
    rw [hNΓ _ τ hτ0, hτr, hc''_def, ord_zpow_mul_inv _ hc hg]
  have h3 : X.ord g Γ.genericPoint = D.coeff Γ := by
    rw [hφ Γ hΓ, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord]
    have : Γ.component = Z0 := Subsingleton.elim
      (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents) _ _
    rw [this]
  have hCq : (D.coeff Γ : ℚ) = m * (KX.coeff Γ + Δ.coeff Γ) := by
    have := congrArg (fun D : QDivisor X => D.coeff Γ) hD
    rw [mul_add]
    simpa [zsmul_eq_mul] using this
  qify at h1 h2 h3
  linear_combination h2 - hCq - h3 - (m : ℚ) * h1

/-- **The crepant pull-back of a local equation of `m(K_X + Δ)`.** With `K_X = div_X(ω)` and
`K_Y = div_Y(f^*ω)`, let `φ` be a local equation on `U` of a divisor `D = m(K_X + Δ)`. Then
`τ = ω^{⊗m}/φ` generates `𝒪_X(m(K_X + Δ))` on `U`, so `f^*τ` generates `𝒪_Y(m(K_Y + Δ_Y))` on
`f⁻¹(U)`, and along a prime divisor `F` meeting `f⁻¹(U)`,
`v_F(f^*φ) = m ord_F(f^*ω) - ord_F(f^*τ) = m (coeff_F(K_Y) + coeff_F(Δ_Y))`. -/
private theorem ordUnit_pullbackComponent_eq_coeff [CompactSpace X] [LocallyOfFiniteType sX]
    (hP : IsPair sX Δ) {KX : Divisor X}
    (hKX : KX.IsCanonicalDivisor sX n) {Y : Scheme.{u}} (f : Y ⟶ X)
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) [IsIntegral Y]
    [LocallyOfFiniteType (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] [IsDominant f]
    [CompactSpace Y] {KY : Divisor Y} {ΔY : QDivisor Y}
    (hΔY : IsCrepantBoundary sX n KX Δ f hY hf ΔY) {ω : RationalPluriForms sX n 1}
    (hω0 : ω ≠ 0) (hωK : divisorOfForm ω = KX)
    (hωKY : divisorOfForm (pullbackRationalPluriForms sX f ω) = KY) {m : ℕ} (hm : 0 < m)
    {D : Divisor X} (hD : Divisor.toQDivisor D = (m : ℤ) • (Divisor.toQDivisor KX + Δ))
    (hDC : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp) {U : X.Opens}
    {φ : (RationalFunctions X)ˣ} (hφ : D.IsLocalEquation U φ) (F : MMP.Mori.PrimeDivisor Y)
    (hF : (F.support ∩ f ⁻¹ᵁ U).Nonempty) :
    (F.ordUnit (pullbackComponent f hB hφ F.component (F.map_componentGenericPoint_mem f hF)) :
      ℚ) = m * (KY.coeff F + ΔY.coeff F) := by
  have hn := hKX.topologicalKrullDim_eq
  set Dob : DivisorOver k sX := ⟨Y, f, hY, hf, F⟩
  obtain ⟨b, N', hb0⟩ := Dob.exists_ordPullback_eq hP.1 hn
  have hb : ∀ (m : ℤ) (τ : RationalPluriForms sX n m), τ ≠ 0 → Dob.ordPullback τ =
      Y.ord (functionFieldMap f ((ZTensorPower.basis b m).repr τ ())) F.genericPoint + m * N' :=
    hb0
  let := functionFieldAlgebra sX
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  let Z0 : irreducibleComponents X := ⟨Set.univ, by
    rw [irreducibleComponents_eq_singleton]; simp⟩
  set c := (ZTensorPower.basis b 1).repr ω () with hc_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hω0
  set g := MMP.Threefold.Mori.Helpers.evalFF Z0 (φ : RationalFunctions X)
  have hg : g ≠ 0 := (φ.isUnit.map _).ne_zero
  set c'' : X.functionField := c ^ (m : ℤ) * g⁻¹ with hc''_def
  have hc'' : c'' ≠ 0 := mul_ne_zero (zpow_ne_zero _ hc) (inv_ne_zero hg)
  let τ : RationalPluriForms sX n m := c'' • ZTensorPower.basis b (m : ℤ) ()
  have hτr : (ZTensorPower.basis b (m : ℤ)).repr τ () = c'' := by simp [τ]
  have hτ0 : τ ≠ 0 := smul_ne_zero hc'' ((ZTensorPower.basis b (m : ℤ)).ne_zero ())
  have hgen : GeneratesOn Δ m U τ := generatesOn_smul_basis hKX hω0 hωK hD hφ b Z0
  have hY0 := (generatesOn_pullbackRationalPluriForms hP hKX f hY hf hΔY hm
    ⟨D, hD, hDC⟩ hgen).2 F hF
  have hordτ : F.ordForm (pullbackRationalPluriForms sX f τ) =
      m * Y.ord (functionFieldMap f c) F.genericPoint
        - Y.ord (functionFieldMap f g) F.genericPoint + m * N' := by
    have hgY : functionFieldMap f g ≠ 0 := (map_ne_zero _).mpr hg
    have hcY : functionFieldMap f c ≠ 0 := (map_ne_zero _).mpr hc
    rw [← show Dob.ordPullback τ = F.ordForm (pullbackRationalPluriForms sX f τ) from rfl,
      hb _ τ hτ0, hτr, hc''_def, map_mul, map_zpow₀, map_inv₀, ord_zpow_mul_inv _ hcY hgY]
  have hKYc : KY.coeff F = Y.ord (functionFieldMap f c) F.genericPoint + N' := by
    have e : Dob.ordPullback ω = KY.coeff F := by
      rw [← hωKY, coeff_divisorOfForm]
      rfl
    rw [← e, hb 1 ω hω0]
    simp [hc_def]
  qify at hordτ hKYc
  rw [ordUnit_pullbackComponent_eq_ord hB hφ F hF Z0]
  push_cast
  linear_combination -hY0 + hordτ - (m : ℚ) * hKYc

/-- A dominant morphism of integral schemes maps the generic point off the support of every
divisor with coefficients in `R`. -/
private theorem map_componentGenericPoint_notMem_supp {R : Type*} [Zero R] {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X) [IsDominant f] (B : DivisorWithCoeffs R X)
    (Z : irreducibleComponents Y) : f (componentGenericPoint Y Z) ∉ B.supp := by
  intro h
  obtain ⟨E, -, hmem⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
  rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant,
    ← MMP.Fourfold.componentGenericPoint_eq_genericPoint (pointComponent (genericPoint X))] at hmem
  exact MMP.Flips.componentGenericPoint_notMem_support _ E hmem

/-- **The crepant pull-back of a Cartier divisor `m(K_X + Δ)`.** With `K_X = div_X(ω)` and
`K_Y = div_Y(f^*ω)`, the pull-back of a Cartier divisor `D = m(K_X + Δ)` is a Cartier divisor
equal to `m(K_Y + Δ_Y)`. -/
private theorem exists_isPullback_of_isCartier [CompactSpace X] [LocallyOfFiniteType sX]
    (hP : IsPair sX Δ) {KX : Divisor X}
    (hKX : KX.IsCanonicalDivisor sX n) {Y : Scheme.{u}} (f : Y ⟶ X)
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) [IsIntegral Y]
    [LocallyOfFiniteType (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] [IsDominant f]
    [CompactSpace Y] {KY : Divisor Y} {ΔY : QDivisor Y}
    (hΔY : IsCrepantBoundary sX n KX Δ f hY hf ΔY) {ω : RationalPluriForms sX n 1}
    (hω0 : ω ≠ 0) (hωK : divisorOfForm ω = KX)
    (hωKY : divisorOfForm (pullbackRationalPluriForms sX f ω) = KY) {m : ℕ} (hm : 0 < m)
    {D : Divisor X} (hD : Divisor.toQDivisor D = (m : ℤ) • (Divisor.toQDivisor KX + Δ))
    (hDC : D.IsCartier) :
    ∃ DY : Divisor Y, Divisor.toQDivisor DY = (m : ℤ) • (Divisor.toQDivisor KY + ΔY) ∧
      DY.IsCartier ∧ ∃ hB, D.IsPullback f hB DY := by
  have hB := map_componentGenericPoint_notMem_supp f D
  have hpb := Divisor.isPullback_pullback hDC hB
  refine ⟨D.pullback hDC hB, ?_, hpb.isCartier hDC, hB, hpb⟩
  ext F
  obtain ⟨U, hU, φ, hφ⟩ := hDC (f F.genericPoint)
  have hF : (F.support ∩ f ⁻¹ᵁ U).Nonempty := (F.genericPoint_mem_iff (f ⁻¹ᵁ U)).mp hU
  rw [Divisor.coeff_toQDivisor, hpb U φ hφ F hF,
    ordUnit_pullbackComponent_eq_coeff hP hKX f hY hf hΔY hω0 hωK hωKY hm hD hDC hB hφ F hF]
  simp [zsmul_eq_mul]
  ring

/-- **The crepant boundary computes the pull-back** (Kollár–Mori 2.26). Let `(X, Δ)` be a pair
over a perfect field, `f : Y ⟶ X` a birational morphism from a normal variety, `K_X`, `K_Y`
canonical divisors of dimension `n` with either `K_X = div_X(ω)`, `K_Y = div_Y(f^*ω)` for a
nonzero rational `1`-canonical form `ω`, or `f` proper and `f_*K_Y = K_X`, and `Δ_Y` the crepant
boundary of `(X, Δ)` on `Y`. Then for every `m > 0` and every Cartier divisor `D = m(K_X + Δ)`,
`m(K_Y + Δ_Y)` is a Cartier divisor `D_Y` with `D_Y = f^*D`; moreover `(Y, Δ_Y)` is a pair and
`K_Y + Δ_Y = f^*(K_X + Δ)` as `ℚ`-divisors. The proper case reduces to the first by
`MMP.Positivity.exists_divisorOfForm_eq_of_transformDivisor_eq`. -/
@[mmp "lem_km2b_crepant_boundary_pullback"]
theorem isPullback_of_isCrepantBoundary (hP : IsPair sX Δ) {Y : Scheme.{u}} (f : Y ⟶ X)
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) {KX : Divisor X}
    {KY : Divisor Y} (hKX : KX.IsCanonicalDivisor sX n)
    (hKY :
      haveI : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
      haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
      haveI : IsNormal Y := hY.2
      KY.IsCanonicalDivisor (f ≫ sX) n)
    (hcompat :
      haveI : CompactSpace X :=
        haveI := hP.1.1.toQuasiCompact
        QuasiCompact.compactSpace_of_compactSpace sX
      haveI : LocallyOfFiniteType sX := hP.1.1.toLocallyOfFiniteType
      haveI : IsIntegral Y := hY.1.toIsIntegral
      haveI : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
      haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
      haveI : IsNormal Y := hY.2
      haveI : IsDominant f := hf.isDominant
      haveI : CompactSpace Y :=
        haveI := hY.1.toQuasiCompact
        QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
      (∃ ω : RationalPluriForms sX n 1, ω ≠ 0 ∧ divisorOfForm ω = KX ∧
          divisorOfForm (pullbackRationalPluriForms sX f ω) = KY) ∨
        (IsProper f ∧ RationalMap.transformDivisor (X := Y) f.toRationalMap KY = KX))
    {ΔY : QDivisor Y} (hΔY : IsCrepantBoundary sX n KX Δ f hY hf ΔY) :
    haveI : IsIntegral Y := hY.1.toIsIntegral
    haveI : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
    haveI : IsNormal Y := hY.2
    (∀ m : ℕ, 0 < m → ∀ D : Divisor X,
        Divisor.toQDivisor D = (m : ℤ) • (Divisor.toQDivisor KX + Δ) → D.IsCartier →
          ∃ DY : Divisor Y, Divisor.toQDivisor DY = (m : ℤ) • (Divisor.toQDivisor KY + ΔY) ∧
            DY.IsCartier ∧ ∃ hB, D.IsPullback f hB DY) ∧
      IsPair (f ≫ sX) ΔY ∧
      ∃ hB, (Divisor.toQDivisor KX + Δ).IsPullback f hB (Divisor.toQDivisor KY + ΔY) := by
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI : IsNormal Y := hY.2
  haveI : IsDominant f := hf.isDominant
  haveI : LocallyOfFiniteType sX := hP.1.1.toLocallyOfFiniteType
  haveI : CompactSpace X := haveI := hP.1.1.toQuasiCompact
    QuasiCompact.compactSpace_of_compactSpace sX
  haveI : CompactSpace Y := haveI := hY.1.toQuasiCompact
    QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  obtain ⟨ω, hω0, hωK, hωKY⟩ : ∃ ω : RationalPluriForms sX n 1, ω ≠ 0 ∧ divisorOfForm ω = KX ∧
      divisorOfForm (pullbackRationalPluriForms sX f ω) = KY := by
    rcases hcompat with h | ⟨hprop, hpush⟩
    · exact h
    · exact MMP.Positivity.exists_divisorOfForm_eq_of_transformDivisor_eq hP.1 hY hf hKX hKY hpush
  have hmain (m : ℕ) (hm : 0 < m) (D : Divisor X) hD hDC :=
    exists_isPullback_of_isCartier hP hKX f hY hf hΔY hω0 hωK hωKY (m := m) (D := D) hm hD hDC
  obtain ⟨_, K₀, hK₀, hq⟩ := hP.isQCartier_of_linearlyEquivalent
  obtain ⟨m, hm, D, hD, hDC⟩ := (hq KX
    (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hP.1 hKX hK₀)).exists_pos
  obtain ⟨DY, hDY, hDYC, -⟩ := hmain m hm D hD hDC
  refine ⟨hmain, isPair_of_isCanonicalDivisor hY hKY ⟨m, by exact_mod_cast hm.ne', DY, hDY, hDYC⟩,
    map_componentGenericPoint_notMem_supp f _, fun m' hm' D' hD' hD'C => ?_⟩
  obtain ⟨DY', hDY', -, _, hpb⟩ := hmain m' hm' D' hD' hD'C
  exact ⟨DY', hDY', hpb⟩

/-! ### Discrepancies are invariant under crepant pull-back -/

/-- A composite of birational morphisms of irreducible schemes is birational. -/
theorem isBirationalMorphism_comp {V X' X : Scheme.{u}} [IrreducibleSpace V]
    [IrreducibleSpace X'] [IrreducibleSpace X] {g : V ⟶ X'} {μ : X' ⟶ X}
    (hg : MMP.Mori.IsBirationalMorphism g) (hμ : MMP.Mori.IsBirationalMorphism μ) :
    MMP.Mori.IsBirationalMorphism (g ≫ μ) := by
  have : Nonempty V := (IrreducibleSpace.isIrreducible_univ V).nonempty.to_subtype.map Subtype.val
  have : Nonempty X' :=
    (IrreducibleSpace.isIrreducible_univ X').nonempty.to_subtype.map Subtype.val
  obtain ⟨Wg, hWgne, hWg⟩ := MMP.Mori.IsBirationalMorphism.exists_isOpenImmersion hg
  obtain ⟨Wμ, hWμne, hWμ⟩ := MMP.Mori.IsBirationalMorphism.exists_isOpenImmersion hμ
  obtain ⟨x₀, hx₀⟩ := hWgne
  obtain ⟨y, ⟨w, rfl⟩, hy⟩ := nonempty_preirreducible_inter
    (Wg.ι ≫ g).isOpenEmbedding.isOpen_range Wμ.isOpen ⟨_, (⟨x₀, hx₀⟩ : Wg.toScheme), rfl⟩ hWμne
  let U : V.Opens := Wg ⊓ g ⁻¹ᵁ Wμ
  have hwU : w.1 ∈ U := ⟨w.2, hy⟩
  have h1 : IsOpenImmersion (U.ι ≫ g) := by
    rw [← Scheme.homOfLE_ι V (inf_le_left : U ≤ Wg), Category.assoc]
    infer_instance
  have hrange : Set.range (U.ι ≫ g) ⊆ Set.range Wμ.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact z.2.2
  have hfac := IsOpenImmersion.lift_fac Wμ.ι (U.ι ≫ g) hrange
  have : IsOpenImmersion (IsOpenImmersion.lift Wμ.ι (U.ι ≫ g) hrange ≫ Wμ.ι) := by
    rwa [hfac]
  have : IsOpenImmersion (IsOpenImmersion.lift Wμ.ι (U.ι ≫ g) hrange) :=
    IsOpenImmersion.of_comp _ Wμ.ι
  have hU : IsOpenImmersion (U.ι ≫ g ≫ μ) := by
    rw [← Category.assoc, ← hfac, Category.assoc]
    infer_instance
  let V' : X.Opens := (U.ι ≫ g ≫ μ).opensRange
  have hle : U ≤ (g ≫ μ) ⁻¹ᵁ V' := fun x hx => ⟨⟨x, hx⟩, rfl⟩
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE (g ≫ μ) U V' ⟨_, hwU⟩
    ⟨_, ⟨⟨w.1, hwU⟩, rfl⟩⟩ hle ?_
  have e : (g ≫ μ).resLE V' U hle = (U.ι ≫ g ≫ μ).isoOpensRange.hom := by
    rw [← cancel_mono V'.ι, Scheme.Hom.resLE_comp_ι, Scheme.Hom.isoOpensRange_hom_ι]
  rw [e]
  infer_instance

/-- A divisor `(W, g, F)` over `Y`, for a birational morphism `f : Y ⟶ X` of varieties, regarded
as the divisor `(W, f ∘ g, F)` over `X`. -/
noncomputable def compDivisorOver {Y : Scheme.{u}} (f : Y ⟶ X)
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f)
    (E : DivisorOver k (f ≫ sX)) : DivisorOver k sX :=
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI := E.isIntegral
  { Y := E.Y
    f := E.f ≫ f
    isNormalVariety := by
      rw [Category.assoc]
      exact E.isNormalVariety
    isBirationalMorphism := isBirationalMorphism_comp E.isBirationalMorphism hf
    E := E.E }

/-- The valuation of `(W, f ∘ g, F)` is that of `(W, g, F)`, read on `k(X)` through `f^*`. -/
theorem valuation_compDivisorOver {Y : Scheme.{u}} (f : Y ⟶ X)
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f)
    (E : DivisorOver k (f ≫ sX)) :
    haveI : IsIntegral Y := hY.1.toIsIntegral
    haveI : IsDominant f := hf.isDominant
    (compDivisorOver f hY hf E).valuation = E.valuation.comap (functionFieldMap f) := by
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : IsDominant f := hf.isDominant
  haveI := E.isIntegral
  haveI := E.isDominant
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  ext t
  change E.E.divisorialValuation (functionFieldMap (E.f ≫ f) t) =
    E.E.divisorialValuation (functionFieldMap E.f (functionFieldMap f t))
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

open MMP.Threefold.Mori.Helpers in
/-- `ord_F((f ∘ g)^*τ) = ord_F(g^* f^* τ)`: the functoriality of the pull-back of forms, read
through the orders along a divisor `(W, g, F)` over `Y`. -/
theorem ordPullback_compDivisorOver [LocallyOfFiniteType sX]
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = n)
    {Y : Scheme.{u}} (f : Y ⟶ X) (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f)
    (E : DivisorOver k (f ≫ sX)) {m : ℤ} (τ : RationalPluriForms sX n m) :
    haveI : IsIntegral Y := hY.1.toIsIntegral
    haveI : IsDominant f := hf.isDominant
    (compDivisorOver f hY hf E).ordPullback τ =
      E.ordPullback (pullbackRationalPluriForms sX f τ) := by
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : IsDominant f := hf.isDominant
  haveI := E.isIntegral
  haveI := E.isDominant
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldAlgebra (E.f ≫ f ≫ sX)
  let := functionFieldMapAlgebra f
  let := functionFieldMapAlgebra E.f
  let := functionFieldMapAlgebra (E.f ≫ f)
  have := isScalarTower_functionFieldMap sX f
  have := isScalarTower_functionFieldMap (f ≫ sX) E.f
  have : IsScalarTower k X.functionField E.Y.functionField :=
    isScalarTower_functionFieldMap sX (E.f ≫ f)
  have : IsScalarTower X.functionField Y.functionField E.Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun t =>
      (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply E.f f t).symm
  obtain ⟨ω0, hω0⟩ := exists_isPullbackGenerator_of_bijective sX f
    hf.functionFieldMap_bijective hd
  obtain ⟨ω0', hω0'⟩ := exists_isPullbackGenerator_of_bijective sX (E.f ≫ f)
    (isBirationalMorphism_comp E.isBirationalMorphism hf).functionFieldMap_bijective hd
  have hω0_2 : IsPullbackGenerator E.Y.functionField ω0 :=
    IsPullbackGenerator.of_span hω0' hω0.1 hω0.ne_zero
  have hωb : IsPullbackGenerator E.Y.functionField
      (topFormsMap k X.functionField Y.functionField n ω0) := by
    refine ⟨hω0.2.1, ?_, ?_⟩
    · rw [topFormsMap_comp]
      exact hω0_2.2.1
    · rw [topFormsMap_comp]
      exact hω0_2.2.2
  show E.E.ordForm (pullbackForms (K := X.functionField) (K' := E.Y.functionField) m τ) =
    E.E.ordForm (pullbackForms (K := Y.functionField) (K' := E.Y.functionField) m
      (pullbackForms (K := X.functionField) (K' := Y.functionField) m τ))
  rw [pullbackForms_comp hω0 hωb τ]

/-- If `K ∼ K'` and `m(K' + Δ)` is a Cartier divisor, so is `m(K + Δ)`. -/
private theorem isCartierDivisor_zsmul_add_of_linearlyEquivalent {Z : Scheme.{u}} [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z] {K K' : Divisor Z} {Δ : QDivisor Z}
    (m : ℤ) (hK : K.LinearlyEquivalent K')
    (h : (m • (Divisor.toQDivisor K' + Δ)).IsCartierDivisor) :
    (m • (Divisor.toQDivisor K + Δ)).IsCartierDivisor := by
  obtain ⟨D, hD, hC⟩ := h
  obtain ⟨φ, hφ⟩ := hK
  refine ⟨D + m • principalDivisor φ, ?_, hC.add ((Divisor.isCartier_principalDivisor φ).zsmul m)⟩
  rw [map_add, map_zsmul, hD, ← hφ, map_sub, smul_add, smul_add, smul_sub]
  abel

/-- A discrepancy of a divisor over a pair is one of every divisor with the same valuation. -/
private theorem isDiscrepancy_of_valuation_eq (hP : IsPair sX Δ)
    (hK : K.IsCanonicalDivisor sX n) {D D' : DivisorOver k sX} (hv : D.valuation = D'.valuation)
    {a : ℚ} (ha : IsDiscrepancy sX n K Δ D a) : IsDiscrepancy sX n K Δ D' a := by
  obtain ⟨a', ha'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK D'
  obtain rfl := MMP.Threefold.Mori.ModelIndependence.isDiscrepancy_eq_of_center_eq hv
    (MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hP.1 hv) ha ha'
  exact ha'

/-- **The crepant direction.** If `Δ_Y` is the crepant boundary of `(X, Δ)` on `Y` and
`m(K_Y + Δ_Y)` is Cartier whenever `m(K_X + Δ)` is, a discrepancy of `(W, f ∘ g, F)` over
`(X, Δ)` is one of `(W, g, F)` over `(Y, Δ_Y)`: for `τ` generating `𝒪_X(m(K_X + Δ))` near
`f(g(η_F))`, `f^*τ` generates `𝒪_Y(m(K_Y + Δ_Y))` near `g(η_F)`, and
`ord_F((f ∘ g)^*τ) = ord_F(g^* f^* τ)`. -/
theorem isDiscrepancy_of_compDivisorOver (hP : IsPair sX Δ) {KX : Divisor X}
    (hKX : KX.IsCanonicalDivisor sX n) {Y : Scheme.{u}} (f : Y ⟶ X)
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) {ΔY : QDivisor Y}
    (hcb : IsCrepantBoundary sX n KX Δ f hY hf ΔY) [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor (f ≫ sX) n)
    (hCY : ∀ m : ℕ, 0 < m → ((m : ℤ) • (Divisor.toQDivisor KX + Δ)).IsCartierDivisor →
      ((m : ℤ) • (Divisor.toQDivisor KY + ΔY)).IsCartierDivisor)
    (E : DivisorOver k (f ≫ sX)) {a : ℚ}
    (ha : IsDiscrepancy sX n KX Δ (compDivisorOver f hY hf E) a) :
    IsDiscrepancy (f ≫ sX) n KY ΔY E a := by
  haveI : IsDominant f := hf.isDominant
  haveI : LocallyOfFiniteType sX := hP.1.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX)
    hKX.topologicalKrullDim_eq
  obtain ⟨-, -, m, hm, hC, U, hU, τ, hτ, hτa⟩ := ha
  refine ⟨hY, hKY, m, hm, hCY m hm hC, f ⁻¹ᵁ U, hU, pullbackRationalPluriForms sX f τ,
    generatesOn_pullbackRationalPluriForms hP hKX f hY hf hcb hm hC hτ, ?_⟩
  rw [hτa, ordPullback_compDivisorOver hd f hY hf E τ]

/-- **Case (b) is case (a).** If `f` is proper, `f_* K_Y = K_X` and `K_Y + Δ_Y` is the
`ℚ`-pull-back of `K_X + Δ`, then `Δ_Y` is the crepant boundary of `(X, Δ)` on `Y`: the crepant
boundary `Δ_Y⁰` satisfies the same pull-back identity, and the `ℚ`-pull-back is unique. -/
private theorem isCrepantBoundary_of_isPullback [LocallyOfFiniteType sX] [CompactSpace X]
    (hP : IsPair sX Δ) {Y : Scheme.{u}} (f : Y ⟶ X)
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) [IsIntegral Y]
    [LocallyOfFiniteType (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] [IsDominant f]
    [CompactSpace Y] {KX : Divisor X} {KY : Divisor Y}
    (hKX : KX.IsCanonicalDivisor sX n) (hKY : KY.IsCanonicalDivisor (f ≫ sX) n) {ΔY : QDivisor Y}
    (h : IsProper f ∧ RationalMap.transformDivisor (X := Y) f.toRationalMap KY = KX ∧
      ∃ hB, (Divisor.toQDivisor KX + Δ).IsPullback f hB (Divisor.toQDivisor KY + ΔY)) :
    IsCrepantBoundary sX n KX Δ f hY hf ΔY := by
  obtain ⟨hprop, hpush, hB, hpull⟩ := h
  obtain ⟨ΔY0, hΔY0⟩ := (existsUnique_isCrepantBoundary hP hKX f hY hf).1.exists
  obtain ⟨-, -, _, hpull0⟩ := isPullback_of_isCrepantBoundary hP f hY hf hKX
    hKY (Or.inr ⟨hprop, hpush⟩) hΔY0
  obtain ⟨_, K0, hK0, hq⟩ := hP.isQCartier_of_linearlyEquivalent
  have hQ := hq KX (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hP.1 hKX hK0)
  have heq := (hQ.existsUnique_isPullback hB).unique hpull hpull0
  rwa [add_left_cancel heq]

/-- **The crepant boundary is a boundary of the right shape.** For the crepant boundary `Δ_Y` of
`(X, Δ)` on `Y`, `(Y, Δ_Y)` is a pair and `m(K_Y + Δ_Y)` is Cartier whenever `m(K_X + Δ)` is:
writing `K_X = div(ω)`, `div(f^*ω) ∼ K_Y` is a canonical divisor compatible with `K_X`, to which
the crepant pull-back applies. -/
private theorem isPair_and_isCartier_of_isCrepantBoundary [LocallyOfFiniteType sX]
    [CompactSpace X] (hP : IsPair sX Δ) {KX : Divisor X} (hKX : KX.IsCanonicalDivisor sX n)
    {Y : Scheme.{u}} (f : Y ⟶ X) (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f)
    [IsIntegral Y] [LocallyOfFiniteType (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsDominant f] [CompactSpace Y] {KY : Divisor Y}
    (hKY : KY.IsCanonicalDivisor (f ≫ sX) n) {ΔY : QDivisor Y}
    (hcb : IsCrepantBoundary sX n KX Δ f hY hf ΔY) :
    IsPair (f ≫ sX) ΔY ∧
      ∀ m : ℕ, 0 < m → ((m : ℤ) • (Divisor.toQDivisor KX + Δ)).IsCartierDivisor →
        ((m : ℤ) • (Divisor.toQDivisor KY + ΔY)).IsCartierDivisor := by
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hP.1 hKX
  have hdivω : divisorOfForm ω = KX := by
    ext Γ
    rw [coeff_divisorOfForm, hω]
  have hpω := pullbackRationalPluriForms_ne_zero f hf
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq hKX.topologicalKrullDim_eq) hω0
  have hlin : (divisorOfForm (pullbackRationalPluriForms sX f ω)).LinearlyEquivalent KY := by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hY hKY hpω
  have hcomp := isPullback_of_isCrepantBoundary hP f hY hf hKX
    (hKY.of_linearlyEquivalent hlin) (Or.inl ⟨ω, hω0, hdivω, rfl⟩) hcb
  refine ⟨hcomp.2.1, ?_⟩
  rintro m hm ⟨D, hD, hDC⟩
  obtain ⟨DY, hDY, hDYC, -⟩ := hcomp.1 m hm D hD hDC
  exact isCartierDivisor_zsmul_add_of_linearlyEquivalent _ hlin.symm ⟨DY, hDY, hDYC⟩

/-- **Discrepancies are invariant under crepant pull-back** (Kollár–Mori 2.30). Let `(X, Δ)` be a
pair over a perfect field with canonical divisor `K_X` of dimension `n`, `f : Y ⟶ X` a birational
morphism from a normal variety with canonical divisor `K_Y`, and `Δ_Y` a `ℚ`-divisor on `Y` which
is either the crepant boundary of `(X, Δ)` on `Y`, or, for `f` proper with `f_*K_Y = K_X`,
satisfies `K_Y + Δ_Y = f^*(K_X + Δ)`. Then `(Y, Δ_Y)` is a pair, and for every divisor `E` over
`Y` and every divisor `E'` over `X` with the same valuation of `k(X)` (such as `E` regarded as a
divisor over `X` through `f`), `a` is the discrepancy `a(E, Y, Δ_Y)` if and only if it is the
discrepancy `a(E', X, Δ)`. -/
@[mmp "lem_km2b_discrepancy_crepant_invariance"]
theorem isDiscrepancy_iff_of_crepant (hP : IsPair sX Δ) {Y : Scheme.{u}} (f : Y ⟶ X)
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) {KX : Divisor X}
    {KY : Divisor Y} (hKX : KX.IsCanonicalDivisor sX n)
    (hKY :
      haveI : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
      haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
      haveI : IsNormal Y := hY.2
      KY.IsCanonicalDivisor (f ≫ sX) n)
    {ΔY : QDivisor Y}
    (hΔY :
      haveI : IsIntegral Y := hY.1.toIsIntegral
      haveI : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
      haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
      haveI : IsNormal Y := hY.2
      haveI : IsDominant f := hf.isDominant
      IsCrepantBoundary sX n KX Δ f hY hf ΔY ∨
        (IsProper f ∧ RationalMap.transformDivisor (X := Y) f.toRationalMap KY = KX ∧
          ∃ hB, (Divisor.toQDivisor KX + Δ).IsPullback f hB (Divisor.toQDivisor KY + ΔY))) :
    haveI : IsIntegral Y := hY.1.toIsIntegral
    haveI : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
    haveI : IsNormal Y := hY.2
    haveI : IsDominant f := hf.isDominant
    IsPair (f ≫ sX) ΔY ∧
      ∀ (E : DivisorOver k (f ≫ sX)) (E' : DivisorOver k sX),
        E'.valuation = E.valuation.comap (functionFieldMap f) → ∀ a : ℚ,
          (IsDiscrepancy (f ≫ sX) n KY ΔY E a ↔ IsDiscrepancy sX n KX Δ E' a) := by
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI : IsNormal Y := hY.2
  haveI : IsDominant f := hf.isDominant
  haveI : LocallyOfFiniteType sX := hP.1.1.toLocallyOfFiniteType
  haveI : CompactSpace X := haveI := hP.1.1; QuasiCompact.compactSpace_of_compactSpace sX
  haveI : CompactSpace Y := haveI := hY.1; QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  have hcb : IsCrepantBoundary sX n KX Δ f hY hf ΔY :=
    hΔY.elim id (isCrepantBoundary_of_isPullback hP f hY hf hKX hKY)
  obtain ⟨hPY, hCY⟩ := isPair_and_isCartier_of_isCrepantBoundary hP hKX f hY hf hKY hcb
  refine ⟨hPY, fun E E' hv a => ?_⟩
  have hv' : (compDivisorOver f hY hf E).valuation = E'.valuation :=
    (valuation_compDivisorOver f hY hf E).trans hv.symm
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨a', h'⟩ :=
      MMP.Positivity.IsPair.exists_isDiscrepancy hP hKX (compDivisorOver f hY hf E)
    obtain rfl := h.eq (isDiscrepancy_of_compDivisorOver hP hKX f hY hf hcb hKY hCY E h')
    exact isDiscrepancy_of_valuation_eq hP hKX hv' h'
  · exact isDiscrepancy_of_compDivisorOver hP hKX f hY hf hcb hKY hCY E
      (isDiscrepancy_of_valuation_eq hP hKX hv'.symm h)

end MMP.Mori.IsPair

/-! ### The leading term of the Euler characteristic function of several divisors -/

namespace MMP.Mori

section Polynomial

open MvPolynomial

private theorem aeval_cons_eq_sum {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ℚ) (c : ℚ)
    (v : Fin r → ℚ) :
    aeval (Fin.cons (Polynomial.C c) fun j => Polynomial.C (v j) * Polynomial.X :
        Fin (r + 1) → Polynomial ℚ) Q =
      ∑ s ∈ Q.support, Polynomial.C (Q.coeff s * c ^ s 0 * ∏ j : Fin r, v j ^ s j.succ) *
        Polynomial.X ^ (∑ j : Fin r, s j.succ) := by
  conv_lhs => rw [Q.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Polynomial.algebraMap_apply, map_mul, map_pow, map_prod,
    Algebra.algebraMap_self, RingHom.id_apply]
  ring

private theorem sum_eq_succ {r : ℕ} (s : Fin (r + 1) →₀ ℕ) :
    (s.sum fun _ e => e) = s 0 + ∑ j : Fin r, s j.succ := by
  rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_succ]

private theorem natDegree_aeval_cons_le {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ℚ) (c : ℚ)
    (v : Fin r → ℚ) :
    (aeval (Fin.cons (Polynomial.C c) fun j => Polynomial.C (v j) * Polynomial.X :
        Fin (r + 1) → Polynomial ℚ) Q).natDegree ≤ Q.totalDegree := by
  rw [aeval_cons_eq_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s hs => ?_
  refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
  have := le_totalDegree hs
  rw [sum_eq_succ] at this
  omega

/-- The coefficient of `tⁿ` in `t ↦ Q(c, t v)` is the degree-`n` component of `Q` at `(0, v)`,
whatever `c` is, when `Q` has total degree at most `n`. -/
private theorem coeff_aeval_cons {r n : ℕ} (Q : MvPolynomial (Fin (r + 1)) ℚ)
    (hQ : Q.totalDegree ≤ n) (c : ℚ) (v : Fin r → ℚ) :
    (aeval (Fin.cons (Polynomial.C c) fun j => Polynomial.C (v j) * Polynomial.X :
        Fin (r + 1) → Polynomial ℚ) Q).coeff n =
      eval (Fin.cons 0 v) (homogeneousComponent n Q) := by
  classical
  rw [aeval_cons_eq_sum, Polynomial.finset_sum_coeff, homogeneousComponent_apply, map_sum,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hd := (le_totalDegree hs).trans hQ
  rw [sum_eq_succ] at hd
  rw [Polynomial.coeff_C_mul_X_pow, eval_monomial, Finsupp.prod_fintype _ _ (by simp),
    Fin.prod_univ_succ, Finsupp.degree_eq_sum, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  by_cases h0 : s 0 = 0
  · simp only [h0, pow_zero, one_mul, mul_one, zero_add]
    split_ifs <;> first | rfl | omega
  · have h1 : ¬ n = ∑ j : Fin r, s j.succ := by omega
    simp [h1, h0]

private theorem coeff_aeval_smul_X {ι : Type*} [Fintype ι] (n : ℕ) (P : MvPolynomial ι ℚ)
    (u : ι → ℚ) :
    (aeval (fun i => Polynomial.C (u i) * Polynomial.X) P).coeff n =
      eval u (homogeneousComponent n P) := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum, Polynomial.finset_sum_coeff, homogeneousComponent_apply, map_sum,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [aeval_monomial, eval_monomial, Finsupp.prod_fintype _ _ (by simp),
    Finsupp.prod_fintype _ _ (by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, ← map_pow,
    ← map_prod]
  rw [← Finsupp.degree_eq_sum, ← mul_assoc, ← map_mul, Polynomial.coeff_C_mul_X_pow]
  by_cases h : s.degree = n
  · simp [h]
  · simp [h, Ne.symm h]

/-- The `n`-th finite difference of a polynomial of degree at most `n`, written as an
alternating sum over subsets, is `n!` times its coefficient of degree `n`. -/
private theorem sum_neg_one_pow_eval_neg_card {n : ℕ} (g : Polynomial ℚ) (hg : g.natDegree ≤ n) :
    ∑ I : Finset (Fin n), (-1 : ℚ) ^ I.card * g.eval (-(I.card : ℚ)) =
      n.factorial * g.coeff n := by
  have hfd : (fwdDiff (1 : ℚ))^[n] g.eval (-(n : ℚ)) = n.factorial * g.coeff n := by
    have h1 : g.eval = (fun r => ∑ j ∈ Finset.range n, g.coeff j * r ^ j) +
        g.coeff n • (fun r => r ^ n) := by
      funext r
      simp [g.eval_eq_sum_range' (show g.natDegree < n + 1 by omega), Finset.sum_range_succ]
    rw [h1, fwdDiff_iter_add, fwdDiff_iter_const_smul, fwdDiff_iter_sum_mul_pow_eq_zero,
      fwdDiff_iter_eq_factorial]
    simp [mul_comm]
  rw [← hfd, fwdDiff_iter_eq_sum_shift, ← Finset.powerset_univ,
    Finset.sum_powerset_apply_card (f := fun m => (-1 : ℚ) ^ m * g.eval (-(m : ℚ))),
    Finset.card_univ, Fintype.card_fin, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [show n + 1 - 1 - j = n - j by omega, Nat.choose_symm (by omega)]
  simp only [nsmul_eq_mul, zsmul_eq_mul, smul_eq_mul, mul_one]
  rw [show (-(n : ℚ) + j) = -((n - j : ℕ) : ℚ) by
      push_cast [show j ≤ n by omega]; ring]
  push_cast
  ring

private theorem eval_aeval_polynomial {σ : Type*} (g : σ → Polynomial ℚ) (t : ℚ)
    (Q : MvPolynomial σ ℚ) : (aeval g Q).eval t = eval (fun i => (g i).eval t) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

private theorem eval_aeval_cons {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ℚ) (c t : ℚ)
    (v : Fin r → ℚ) :
    (aeval (Fin.cons (Polynomial.C c) fun j => Polynomial.C (v j) * Polynomial.X :
        Fin (r + 1) → Polynomial ℚ) Q).eval t = eval (Fin.cons c fun j => v j * t) Q := by
  rw [eval_aeval_polynomial]
  refine congrArg (fun x => MvPolynomial.eval x Q) (funext fun i => ?_)
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- **Comparison of leading terms.** If `P(t u) = Q(1, t v)` for every integer `t` and `Q` has
total degree at most `n`, then the degree-`n` component of `P` at `u` equals that of `Q` at
`(0, v)`: both are the coefficient of `tⁿ` in `t ↦ Q(1, t v)`. -/
private theorem eval_homogeneousComponent_eq_of_forall_int {ι : Type*} [Fintype ι] {r n : ℕ}
    (P : MvPolynomial ι ℚ) (Q : MvPolynomial (Fin (r + 1)) ℚ) (hQ : Q.totalDegree ≤ n)
    (u : ι → ℚ) (v : Fin r → ℚ)
    (h : ∀ t : ℤ, eval (fun i => u i * t) P = eval (Fin.cons 1 fun j => v j * t) Q) :
    eval u (homogeneousComponent n P) = eval (Fin.cons 0 v) (homogeneousComponent n Q) := by
  rw [← coeff_aeval_smul_X, ← coeff_aeval_cons Q hQ 1 v]
  refine congrArg (fun p : Polynomial ℚ => p.coeff n) ?_
  refine Polynomial.eq_of_infinite_eval_eq _ _
    ((Set.infinite_range_of_injective (Int.cast_injective (α := ℚ))).mono ?_)
  rintro _ ⟨t, rfl⟩
  show _ = _
  rw [eval_aeval_cons, ← h t, eval_aeval_polynomial]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

end Polynomial

section Sheaves

open Stacks.SheafOfModules.Invertible

private noncomputable abbrev tens (X : Scheme.{u}) : X.Modules ⥤ X.Modules ⥤ X.Modules :=
  Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
    (X.presheaf) (forget₂ CommRingCat RingCat) (X.ringCatSheaf.2)⟩

private theorem nonempty_iso_of_tensor_iso {X : Scheme.{u}} (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] {A B : X.Modules}
    (h : ((tens X).obj A).obj L ≅ ((tens X).obj B).obj L) : Nonempty (A ≅ B) := by
  haveI : ((tens X).flip.obj L).IsEquivalence :=
    (isInvertible_iff_tensorRightFunctor_isEquivalence X.presheaf X.ringCatSheaf.2 L).1
      inferInstance
  exact ⟨((tens X).flip.obj L).preimageIso h⟩

/-- `𝒪_X(n D) ≅ 𝒪_X(D)^{⊗ n}` for a Cartier divisor `D` and an integer `n`. -/
private theorem nonempty_divisorialSheaf_zsmul_iso {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {D : Divisor X} (hD : D.IsCartier) (n : ℤ) :
    haveI := hD.isInvertibleModule_divisorialSheaf
    Nonempty ((n • D).divisorialSheaf ≅
      tensorPower X.presheaf X.ringCatSheaf.2 D.divisorialSheaf n) := by
  haveI := hD.isInvertibleModule_divisorialSheaf
  set L := D.divisorialSheaf
  induction n using Int.induction_on with
  | zero => exact ⟨eqToIso (by rw [zero_smul]) ≪≫ Divisor.divisorialSheafZeroIso⟩
  | succ i ih =>
    obtain ⟨e⟩ := ih
    have h : (((i : ℤ) + 1) • D).divisorialSheaf ≅
        ((tens X).obj ((i : ℤ) • D).divisorialSheaf).obj L :=
      eqToIso (by rw [add_smul, one_smul]) ≪≫ (((hD.zsmul i).divisorialSheafTensorIso hD)).symm
    exact ⟨h ≪≫ ((tens X).mapIso e).app L ≪≫ tensorPowerSuccIso X.presheaf X.ringCatSheaf.2 L i⟩
  | pred i ih =>
    obtain ⟨e⟩ := ih
    have h : ((tens X).obj ((-(i : ℤ) - 1) • D).divisorialSheaf).obj L ≅
        ((-(i : ℤ)) • D).divisorialSheaf :=
      (hD.zsmul _).divisorialSheafTensorIso hD ≪≫
        eqToIso (by rw [sub_smul, one_smul, sub_add_cancel])
    have h2 : ((tens X).obj (tensorPower X.presheaf X.ringCatSheaf.2 L (-(i : ℤ) - 1))).obj L ≅
        ((-(i : ℤ)) • D).divisorialSheaf :=
      tensorPowerSuccIso X.presheaf X.ringCatSheaf.2 L _ ≪≫
        tensorPowerReindex X.presheaf X.ringCatSheaf.2 L (n := -(i : ℤ) - 1 + 1) (m := -(i : ℤ))
          (by ring) ≪≫ e.symm
    exact nonempty_iso_of_tensor_iso L (h.trans h2.symm)

private theorem nonempty_fold_iso {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {r : ℕ} (L : Fin r → Divisor X) (hL : ∀ i, (L i).IsCartier)
    (n : Fin r → ℤ) (l : List (Fin r)) :
    haveI := fun i => (hL i).isInvertibleModule_divisorialSheaf
    ∀ (M : X.Modules) (D : Divisor X), D.IsCartier → Nonempty (D.divisorialSheaf ≅ M) →
      Nonempty (l.foldl (fun M i => ((tens X).obj M).obj
        (tensorPower X.presheaf X.ringCatSheaf.2 (L i).divisorialSheaf (n i))) M ≅
        (D + (l.map fun i => n i • L i).sum).divisorialSheaf) := by
  haveI := fun i => (hL i).isInvertibleModule_divisorialSheaf
  induction l with
  | nil => exact fun M D _ ⟨e⟩ => ⟨e.symm ≪≫ eqToIso (by simp)⟩
  | cons a l ih =>
    intro M D hDc ⟨e⟩
    obtain ⟨e'⟩ := nonempty_divisorialSheaf_zsmul_iso (hL a) (n a)
    have h : (D + n a • L a).divisorialSheaf ≅ ((tens X).obj M).obj
        (tensorPower X.presheaf X.ringCatSheaf.2 (L a).divisorialSheaf (n a)) :=
      (hDc.divisorialSheafTensorIso ((hL a).zsmul (n a))).symm ≪≫
        tensorProductIso X.presheaf X.ringCatSheaf.2 e e'
    obtain ⟨g⟩ := ih _ _ (hDc.add ((hL a).zsmul (n a))) ⟨h⟩
    exact ⟨g ≪≫ eqToIso (by simp [add_assoc])⟩

/-- `𝒪_X(∑ᵢ nᵢ Lᵢ)` is the twist of `𝒪_X` by the `𝒪_X(Lᵢ)^{⊗ nᵢ}`, for Cartier divisors `Lᵢ`. -/
private theorem nonempty_divisorialSheaf_sum_iso_twistedSheaf {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {r : ℕ} (L : Fin r → Divisor X)
    (hL : ∀ i, (L i).IsCartier) (n : Fin r → ℤ) :
    haveI := fun i => (hL i).isInvertibleModule_divisorialSheaf
    Nonempty ((∑ i, n i • L i).divisorialSheaf ≅
      twistedSheaf (SheafOfModules.unit X.ringCatSheaf) (fun i => (L i).divisorialSheaf) n) := by
  haveI := fun i => (hL i).isInvertibleModule_divisorialSheaf
  obtain ⟨g⟩ := nonempty_fold_iso L hL n (List.finRange r) _ 0 Divisor.isCartier_zero
    ⟨Divisor.divisorialSheafZeroIso⟩
  refine ⟨eqToIso ?_ ≪≫ g.symm⟩
  rw [zero_add, Fin.sum_univ_def]

/-- Integer tensor powers of isomorphic invertible modules are isomorphic. -/
private noncomputable def tensorPowerIsoOfIso {X : Scheme.{u}} (M N : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] (e : M ≅ N) (m : ℤ) :
    tensorPower X.presheaf X.ringCatSheaf.2 M m ≅ tensorPower X.presheaf X.ringCatSheaf.2 N m :=
  Stacks.Equivalence.powIntertwineObj
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).flip.obj M).asEquivalence
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).flip.obj N).asEquivalence (𝟭 _)
    (fun A => ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).obj A).mapIso e) m
    (SheafOfModules.unit _)

/-- The fold over a list of indices of a constant family of invertible modules, started at a
tensor power, is the tensor power with the exponents added on. -/
private noncomputable def twistListTensorPowerIso {X : Scheme.{u}} {r : ℕ}
    (M : Fin r → X.Modules)
    [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M i)]
    (N : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    (e : ∀ i, M i ≅ N) (n : Fin r → ℤ) :
    ∀ (l : List (Fin r)) (m : ℤ),
      twistList M n l (tensorPower X.presheaf X.ringCatSheaf.2 N m) ≅
        tensorPower X.presheaf X.ringCatSheaf.2 N (l.foldl (fun z i => z + n i) m) := by
  intro l
  induction l with
  | nil => exact fun m => Iso.refl _
  | cons i t ih =>
      exact fun m =>
        twistListIso M n t
            (tensorProductIso X.presheaf X.ringCatSheaf.2 (Iso.refl _)
                (tensorPowerIsoOfIso (M i) N (e i) (n i)) ≪≫
              (tensorPowerCoherence X.presheaf X.ringCatSheaf.2 N).mulIso m (n i)) ≪≫
          ih (m + n i)

private theorem finRange_foldl_add {r : ℕ} (n : Fin r → ℤ) (z : ℤ) :
    (List.finRange r).foldl (fun a i => a + n i) z = z + ∑ i, n i := by
  induction r generalizing z with
  | zero => simp
  | succ r ih =>
      rw [List.finRange_succ, List.foldl_cons, List.foldl_map, ih (fun i => n i.succ) (z + n 0)]
      simp [Fin.sum_univ_succ, add_assoc]

/-- **A twist of the structure sheaf by a constant family is a single tensor power.**
`𝒪_X ⊗ M_1^{⊗ n_1} ⊗ ⋯ ⊗ M_r^{⊗ n_r} ≅ N^{⊗ (n_1 + ⋯ + n_r)}` whenever every `M_i` is
isomorphic to `N`. -/
private noncomputable def twistedSheafUnitIsoTensorPower {X : Scheme.{u}} {r : ℕ}
    (M : Fin r → X.Modules)
    [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M i)]
    (N : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    (e : ∀ i, M i ≅ N) (n : Fin r → ℤ) :
    twistedSheaf (SheafOfModules.unit X.ringCatSheaf) M n ≅
      tensorPower X.presheaf X.ringCatSheaf.2 N (∑ i, n i) :=
  have hunit : (SheafOfModules.unit X.ringCatSheaf : X.Modules) =
      tensorPower X.presheaf X.ringCatSheaf.2 N 0 := rfl
  have hfold : (List.finRange r).foldl (fun z i => z + n i) 0 = ∑ i, n i := by
    rw [finRange_foldl_add, zero_add]
  twistListIso M n (List.finRange r) (eqToIso hunit) ≪≫
    twistListTensorPowerIso M N e n (List.finRange r) 0 ≪≫
    eqToIso (congrArg (tensorPower X.presheaf X.ringCatSheaf.2 N) hfold)

/-- The Euler characteristic `χ(X, 𝒪_X(G))` of a divisor, written as the alternating sum of the
dimensions of the cohomology groups. -/
private noncomputable abbrev chiDiv (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsLocallyNoetherian X] [IsNormal X] (G : Divisor X) : ℤ :=
  ∑ᶠ j : ℕ, (-1 : ℤ) ^ j * (Module.finrank k (cohomologyOverField k f G.divisorialSheaf j) : ℤ)

private theorem chiDiv_eq_of_iso (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsLocallyNoetherian X] [IsNormal X] {G : Divisor X} {F : X.Modules}
    (e : G.divisorialSheaf ≅ F) :
    chiDiv k f G = ∑ᶠ j : ℕ, (-1 : ℤ) ^ j * (Module.finrank k (cohomologyOverField k f F j) : ℤ) :=
  finsum_congr fun j => by rw [finrank_cohomologyOverField_eq_of_iso k f e j]

/-- The twist of `𝒪_X` by `n` copies of `𝒪_X(E)` pulled back along `𝟙 X`, with exponents `a`,
has the Euler characteristic of `𝒪_X((∑ⱼ aⱼ) E)`. -/
private theorem eulerCharacteristic_twistedSheaf_pullbackId (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {E : Divisor X} (hE : E.IsCartier) {n : ℕ} (a : Fin n → ℤ) :
    haveI := hE.isInvertibleModule_divisorialSheaf
    ∑ᶠ j : ℕ, (-1 : ℤ) ^ j * (Module.finrank k (cohomologyOverField k (𝟙 X ≫ f)
      (twistedSheaf (SheafOfModules.unit X.ringCatSheaf)
        (fun _ : Fin n => (Scheme.Modules.pullback (𝟙 X)).obj E.divisorialSheaf) a) j) : ℤ) =
      chiDiv k f ((∑ j, a j) • E) := by
  haveI := hE.isInvertibleModule_divisorialSheaf
  have g1 := twistedSheafUnitIsoTensorPower
    (fun _ : Fin n => (Scheme.Modules.pullback (𝟙 X)).obj E.divisorialSheaf) E.divisorialSheaf
    (fun _ => (Scheme.Modules.pullbackId X).app _) a
  obtain ⟨g2⟩ := nonempty_divisorialSheaf_zsmul_iso hE (∑ j, a j)
  rw [chiDiv_eq_of_iso k f (g2 ≪≫ g1.symm), Category.id_comp]

end Sheaves

namespace Divisor

/-- The intersection number `(∑ᵢ uᵢ Dᵢ)ⁿ` is `n!` times the value of the degree-`n` part of the
Euler polynomial `Q` of the twists by `L = (⌈A⌉, D)`, at `(0, u)`. -/
private theorem intersectionNumberOn_eq_factorial_mul_eval (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsLocallyNoetherian X] [IsNormal X] [IsProper f]
    [CompactSpace X] {n : ℕ} (hn : topologicalKrullDim X = n) {ι : Type*} [Fintype ι]
    (D : ι → Divisor X) (hD : ∀ i, (D i).IsCartier) (A : QDivisor X)
    (hC : ∀ G : Divisor X, G.IsCartier) (e : ι ≃ Fin (Fintype.card ι))
    (L : Fin (Fintype.card ι + 1) → Divisor X) (Q : MvPolynomial (Fin (Fintype.card ι + 1)) ℚ)
    (hQd : Q.totalDegree ≤ n)
    (hQv : ∀ m : Fin (Fintype.card ι + 1) → ℤ, MvPolynomial.eval (fun j => (m j : ℚ)) Q =
      (chiDiv k f (∑ j, m j • L j) : ℚ))
    (hsum : ∀ (c : ℤ) (w : ι → ℤ),
      ∑ j, (Fin.cons c (fun j => w (e.symm j)) : Fin (Fintype.card ι + 1) → ℤ) j • L j =
        c • DivisorWithCoeffs.roundUp A + ∑ i, w i • D i)
    (u : ι → ℤ) (v : Fin (Fintype.card ι) → ℚ) (hv : ∀ j, v j = u (e.symm j)) :
    (intersectionNumberOn k f (𝟙 X) n hn.le (fun _ => ∑ i, u i • D i)
        (fun _ => Finset.sum_induction _ IsCartier (fun _ _ h h' => h.add h')
          isCartier_zero (fun i _ => (hD i).zsmul (u i))) : ℚ) =
      n.factorial * MvPolynomial.eval (Fin.cons 0 v) (MvPolynomial.homogeneousComponent n Q) := by
  classical
  rw [← coeff_aeval_cons Q hQd 0 v,
    ← sum_neg_one_pow_eval_neg_card _ ((natDegree_aeval_cons_le Q 0 v).trans hQd)]
  unfold intersectionNumberOn sheafIntersectionNumber
  push_cast
  refine Finset.sum_congr rfl fun I _ => ?_
  congr 1
  rw [eval_aeval_cons, eulerCharacteristic_eq_finsum,
    eulerCharacteristic_twistedSheaf_pullbackId k f (hC (∑ i, u i • D i))]
  have hI : (∑ j : Fin n, if j ∈ I then (-1 : ℤ) else 0) = -(I.card : ℤ) := by
    simp [Finset.sum_ite_mem]
  rw [hI, Finset.smul_sum]
  simp only [smul_smul]
  rw [← zero_add (∑ i, _), ← zero_smul ℤ (DivisorWithCoeffs.roundUp A),
    ← hsum 0 (fun i => -(I.card : ℤ) * u i), ← hQv]
  refine congrArg (fun x => MvPolynomial.eval x Q) (funext fun j => ?_)
  refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp only [Fin.cons_succ, hv]
    push_cast
    ring

/-- **The leading term of the Euler characteristic function** (Kollár–Mori 3.4 Step 5). Let `Y`
be a smooth projective variety of dimension `n` over `k`, `Dᵢ` (`i ∈ ι`) Cartier divisors and `A`
a `ℚ`-divisor on `Y`, and let `P ∈ ℚ[uᵢ : i ∈ ι]` take the values
`χ(Y, 𝒪_Y(∑ᵢ uᵢ Dᵢ + ⌈A⌉))` on `ℤ^ι`. Then the homogeneous component of degree `n` of `P` is
`u ↦ ((∑ᵢ uᵢ Dᵢ)ⁿ) / n!`. -/
@[mmp "lem_km3b_multidivisor_euler_polynomial_leading_term"]
theorem eval_homogeneousComponent_of_eulerPolynomial (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsLocallyNoetherian X] [IsNormal X] [IsProper f]
    (hX : IsProjectiveVariety k f) (hsm : IsSmoothScheme f)
    {n : ℕ} (hn : topologicalKrullDim X = n) {ι : Type*} [Fintype ι] (D : ι → Divisor X)
    (hD : ∀ i, (D i).IsCartier) (A : QDivisor X) (P : MvPolynomial ι ℚ)
    (hP : ∀ u : ι → ℤ, MvPolynomial.eval (fun i => (u i : ℚ)) P = eulerPolynomial k f D A u)
    (u : ι → ℤ) :
    MvPolynomial.eval (fun i => (u i : ℚ)) (MvPolynomial.homogeneousComponent n P) =
      (intersectionNumberOn k f (𝟙 X) n hn.le (fun _ => ∑ i, u i • D i)
        (fun _ => Finset.sum_induction _ IsCartier (fun _ _ h h' => h.add h') isCartier_zero
          (fun i _ => (hD i).zsmul (u i))) : ℚ) / n.factorial := by
  classical
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hC : ∀ G : Divisor X, G.IsCartier :=
    MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm
  let e := Fintype.equivFin ι
  have hEP : ∀ w : ι → ℤ, eulerPolynomial k f D A w =
      chiDiv k f (∑ i, w i • D i + DivisorWithCoeffs.roundUp A) := fun _ => rfl
  let L : Fin (Fintype.card ι + 1) → Divisor X :=
    Fin.cons (DivisorWithCoeffs.roundUp A) fun j => D (e.symm j)
  haveI : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j).divisorialSheaf :=
    fun j => (hC (L j)).isInvertibleModule_divisorialSheaf
  obtain ⟨Q, hQ0, hQ⟩ := exists_eulerPolynomial_twistedSheaf_of_isProper k f
    (fun j => (L j).divisorialSheaf) (SheafOfModules.unit X.ringCatSheaf)
    (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f)
  have hQd : Q.totalDegree ≤ n := by
    rcases hQ0 with rfl | h
    · simp
    · rw [topologicalKrullDim_supp_unit, hn] at h
      exact_mod_cast h
  have hQv : ∀ m : Fin (Fintype.card ι + 1) → ℤ, MvPolynomial.eval (fun j => (m j : ℚ)) Q =
      (chiDiv k f (∑ j, m j • L j) : ℚ) := by
    intro m
    obtain ⟨g⟩ := nonempty_divisorialSheaf_sum_iso_twistedSheaf L (fun j => hC _) m
    rw [hQ m, chiDiv_eq_of_iso k f g, eulerCharacteristic_eq_finsum]
  have hsum : ∀ (c : ℤ) (w : ι → ℤ),
      ∑ j, (Fin.cons c (fun j => w (e.symm j)) : Fin (Fintype.card ι + 1) → ℤ) j • L j =
        c • DivisorWithCoeffs.roundUp A + ∑ i, w i • D i := by
    intro c w
    rw [Fin.sum_univ_succ]
    simp only [L, Fin.cons_zero, Fin.cons_succ]
    congr 1
    exact Equiv.sum_comp e.symm (fun i => w i • D i)
  let v : Fin (Fintype.card ι) → ℚ := fun j => (u (e.symm j) : ℚ)
  have hA : MvPolynomial.eval (fun i => (u i : ℚ)) (MvPolynomial.homogeneousComponent n P) =
      MvPolynomial.eval (Fin.cons 0 v) (MvPolynomial.homogeneousComponent n Q) := by
    refine eval_homogeneousComponent_eq_of_forall_int P Q hQd _ v fun t => ?_
    let m : Fin (Fintype.card ι + 1) → ℤ := Fin.cons 1 fun j => t * u (e.symm j)
    have e1 : (fun i => (u i : ℚ) * t) = fun i => ((t * u i : ℤ) : ℚ) := by
      funext i
      push_cast
      ring
    have e2 : (Fin.cons 1 fun j => v j * t : Fin (Fintype.card ι + 1) → ℚ) =
        fun j => ((m j : ℤ) : ℚ) := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [m]
      · simp only [m, v, Fin.cons_succ]
        push_cast
        ring
    rw [e1, hP, hEP, e2, hQv, hsum 1 (fun i => t * u i), one_smul, add_comm]
  rw [hA, intersectionNumberOn_eq_factorial_mul_eval k f hn D hD A hC e L Q hQd hQv hsum u v
    fun _ => rfl]
  field_simp

end Divisor

end MMP.Mori
