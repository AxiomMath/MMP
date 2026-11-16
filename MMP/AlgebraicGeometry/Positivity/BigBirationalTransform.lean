module
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.Divisor.AlgebraicHartogsUnits
public import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso

/-!
# An ample divisor stays big on a retained prime divisor

Let `X⁰` be a normal projective variety over a field `k`, `S⁰ ⊆ X⁰` a normal prime divisor and
`A⁰` an effective ample `ℚ`-divisor of which `S⁰` is not a component. Let `φ : X⁰ ⤏ X` be a
birational map onto a normal projective `ℚ`-factorial variety `X` which maps `S⁰` onto a normal
prime divisor `S` of `X`, and whose inverse extracts only finitely many prime divisors `F` of `X`,
each with valuation of order zero on `A⁰`; this includes the case of a birational contraction,
which extracts none. Then the birational transform `A = φ_* A⁰` restricts to `S`: `S` is not
contained in `Supp A`, and the pull-back `A|_S` of the `ℚ`-Cartier `ℚ`-divisor `A` to `S` is
effective and big.

Let `φ : X ⤏ Y` be a birational contraction over a projective variety `S` (no prime divisor of
`Y` is `φ⁻¹`-exceptional), with `X`, `Y` normal projective varieties and `Y` `ℚ`-factorial. If
`A ≥ 0` is a `ℚ`-Cartier `ℚ`-divisor on `X` which is big over `S`, then its birational transform
`φ_* A` is an effective `ℚ`-Cartier `ℚ`-divisor on `Y` which is big over `S`
(`MMP.Fourfold.isRelativelyBig_transformDivisor_of_isBirationalContraction`). Bigness comes from
an injection of `𝒪_S`-modules `πX_* 𝒪_X(D) ⟶ πY_* 𝒪_Y(φ_* D)` which reads a section as a
rational function and transports it along `K(X) ≅ K(Y)`; it stays injective on the fibres at the
generic point of the image, and the target fibre is finite-dimensional because the direct image
of an invertible sheaf along a proper morphism is coherent ([Stacks, Tag 02O5]).

## Main results

* `MMP.Fourfold.isRelativelyBig_pullback_transformDivisor_of_isAmple`: the restriction to the
  retained divisor of the transform of an effective ample `ℚ`-divisor is effective and big.
* `MMP.Fourfold.isRelativelyBig_transformDivisor_of_isBirationalContraction`: the
  pushforward of an effective relatively big `ℚ`-Cartier `ℚ`-divisor along a birational
  contraction onto a `ℚ`-factorial variety is effective, `ℚ`-Cartier and relatively big.
* `MMP.Fourfold.isRelativelyBig_transformDivisor_of_isBirational`: the same bigness statement
  without effectivity.
* `MMP.Fourfold.relativeGenericRank_le_of_functionFieldTransfer`: a ring map of function fields
  over `S` carrying sections of `𝒪_X(D)` to sections of `𝒪_Y(D')`, with `D'` Cartier, bounds the
  relative generic rank of `𝒪_X(D)` by that of `𝒪_Y(D')`.

## Implementation notes

The birational map is given with an inverse `ψ : X ⤏ X⁰` (`MMP.Mori.RationalMap.IsInverse`). The
primes of `X` extracted by `φ` are those which are `MMP.Flips.RationalMap.IsInverseExceptional`.
Since `A⁰` is effective, the valuation `ord_F` of such a prime has order zero on `A⁰` exactly when
its center on `X⁰` is not contained in `Supp A⁰`; the center is the closure of `ψ(η_F)`, so the
condition is stated as: every representative of `ψ` defined at `η_F` maps `η_F` outside
`Supp A⁰`. (Some representative is defined there, `X` being normal and `X⁰` proper.)

The restriction `A|_S` is the pull-back `MMP.Mori.QDivisor.IsPullback` of the `ℚ`-Cartier
`ℚ`-divisor `A` along the closed immersion of `S`; the statement asserts that `S` is not in
`Supp A` (so that the pull-back is defined) and that the pull-back is effective and big over the
point `Spec k` (`MMP.Mori.QDivisor.IsRelativelyBig`).

## References

* [J. Kollár and S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998]
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP MMP.Mori

section Helpers

variable {X Y : Scheme.{u}}

/-- The transform of a prime divisor `P` under a partial map `g'` defined at `η_P` is the closure
of `g'(η_P)`. -/
private theorem coe_transform_eq_closure_singleton [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = φ) (P : Mori.PrimeDivisor X) (hP : P.genericPoint ∈ g'.domain) :
    (Mori.RationalMap.transform φ P.idealSheaf.support : Set Y) =
      closure {g'.hom ⟨P.genericPoint, hP⟩} := by
  have hZ : closure ((P.idealSheaf.support : Set X) ∩ g'.domain) = P.idealSheaf.support := by
    refine le_antisymm ?_ ?_
    · exact closure_minimal Set.inter_subset_left P.idealSheaf.support.isClosed
    · change P.support ⊆ _
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      refine closure_mono (Set.singleton_subset_iff.mpr ⟨?_, hP⟩)
      change P.genericPoint ∈ P.support
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
  rw [← MMP.Positivity.closure_image_eq_transform g' hg' _ hZ, Closeds.coe_closure]
  refine le_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono ?_)
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : P.genericPoint ⤳ g'.domain.ι q := by
      have : g'.domain.ι q ∈ P.support := hq
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
      exact specializes_iff_mem_closure.mpr this
    have h1 := (g'.domain.ι.isOpenEmbedding.isInducing.specializes_iff (y := q)
      (x := ⟨P.genericPoint, hP⟩)).mp (by rwa [Scheme.Opens.ι_apply])
    exact specializes_iff_mem_closure.mp (h1.map g'.hom.continuous)
  · rw [Set.singleton_subset_iff]
    refine ⟨⟨P.genericPoint, hP⟩, ?_, rfl⟩
    change g'.domain.ι ⟨P.genericPoint, hP⟩ ∈ P.support
    rw [Scheme.Opens.ι_apply, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl

/-- If `φ_* P = E`, every representative of `φ` defined at `η_P` maps `η_P` to `η_E`. -/
private theorem genericPoint_eq_of_transformPrimeDivisor_eq_some [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : Mori.PrimeDivisor X}
    {E : Mori.PrimeDivisor Y} (h : Mori.RationalMap.transformPrimeDivisor φ P = some E)
    (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ) (hP : P.genericPoint ∈ g'.domain) :
    E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩ := by
  have h1 := Mori.RationalMap.support_transformPrimeDivisor h
  rw [coe_transform_eq_closure_singleton g' hg' P hP,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h1
  exact (inseparable_iff_closure_eq.2 h1).eq

/-- **A birational map is injective on the prime divisors it retains.** If `φ : X ⤏ Y` is
birational between integral separated schemes with `Y` normal, two prime divisors of `X` with the
same transform `E` are equal: a representative `g` of `φ` is a separated dominant morphism
inducing an isomorphism of function fields, and `𝒪_{Y,E}` is a valuation ring, so `g` is a local
isomorphism at both generic points, which therefore coincide. -/
private theorem eq_of_transformPrimeDivisor_eq_some [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [Scheme.IsSeparated X] [Scheme.IsSeparated Y]
    {φ : X.RationalMap Y} {ψ : Y.RationalMap X} (hψ : Mori.RationalMap.IsInverse φ ψ)
    {D₁ D₂ : Mori.PrimeDivisor X} {E : Mori.PrimeDivisor Y}
    (h₁ : Mori.RationalMap.transformPrimeDivisor φ D₁ = some E)
    (h₂ : Mori.RationalMap.transformPrimeDivisor φ D₂ = some E) : D₁ = D₂ := by
  obtain ⟨e, he, -⟩ := hψ
  set g := φ.toPartialMap with hg
  have hgφ : g.toRationalMap = φ := Scheme.RationalMap.toRationalMap_toPartialMap φ
  have hd₁ : D₁.genericPoint ∈ g.domain :=
    (Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp h₁).1
  have hd₂ : D₂.genericPoint ∈ g.domain :=
    (Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp h₂).1
  have hx₁ := genericPoint_eq_of_transformPrimeDivisor_eq_some h₁ g hgφ hd₁
  have hx₂ := genericPoint_eq_of_transformPrimeDivisor_eq_some h₂ g hgφ hd₂
  haveI : Nonempty g.domain := ⟨⟨_, hd₁⟩⟩
  obtain ⟨W, hW, hWe, hWg, hres⟩ :=
    Scheme.PartialMap.toRationalMap_eq_iff.mp (he.trans hgφ.symm)
  simp only [Scheme.PartialMap.restrict_hom] at hres
  have hWne : (W : Set X).Nonempty := hW.nonempty
  haveI : Nonempty W := hWne.to_subtype
  let W' : g.domain.toScheme.Opens := (X.homOfLE hWg).opensRange
  have hW'ι : W'.ι = (X.homOfLE hWg).isoOpensRange.inv ≫ X.homOfLE hWg := by
    rw [Iso.eq_inv_comp, Scheme.Hom.isoOpensRange_hom_ι]
  have hcomp : W'.ι ≫ g.hom =
      (X.homOfLE hWg).isoOpensRange.inv ≫ X.homOfLE hWe ≫ e.toPartialMap.hom := by
    rw [hW'ι, Category.assoc, ← hres]
  haveI he' : IsOpenImmersion e.toPartialMap.hom := by
    change IsOpenImmersion (e.iso.hom ≫ e.target.ι)
    infer_instance
  haveI : IsOpenImmersion (W'.ι ≫ g.hom) := by
    rw [hcomp]
    infer_instance
  haveI : Nonempty W' := ⟨(X.homOfLE hWg).isoOpensRange.hom (Classical.arbitrary W)⟩
  haveI : IsDominant (W'.ι ≫ g.hom) :=
    ⟨(W'.ι ≫ g.hom).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  haveI : IsDominant g.hom := IsDominant.of_comp W'.ι g.hom
  haveI : IsSeparated g.hom := by
    have : g.hom ≫ Limits.terminal.from Y = g.domain.ι ≫ Limits.terminal.from X :=
      Limits.terminal.hom_ext _ _
    haveI : IsSeparated (g.hom ≫ Limits.terminal.from Y) := by rw [this]; infer_instance
    exact IsSeparated.of_comp g.hom (Limits.terminal.from Y)
  have hμ : Function.Bijective (AlgebraicGeometry.functionFieldMap g.hom) :=
    MMP.Mori.functionFieldMap_bijective_of_isOpenImmersion g.hom W'
      ⟨_, (Classical.arbitrary W').2⟩
  have := E.isDiscreteValuationRing_localRing
  haveI : ValuationRing (Y.presheaf.stalk (g.hom ⟨_, hd₁⟩)) := by
    rw [← hx₁]; infer_instance
  haveI : ValuationRing (Y.presheaf.stalk (g.hom ⟨_, hd₂⟩)) := by
    rw [← hx₂]; infer_instance
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing g.hom hμ ⟨_, hd₁⟩
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing g.hom hμ ⟨_, hd₂⟩
  have h := MMP.Positivity.eq_of_isIso_stalkMap g.hom hμ (x₁ := ⟨_, hd₁⟩) (x₂ := ⟨_, hd₂⟩)
    (hx₂.symm.trans hx₁)
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (congrArg Subtype.val h)

/-- The linear extension of a partial map on prime divisors preserves effectivity. -/
private theorem mapPrimeDivisors_nonneg
    (φ : Mori.PrimeDivisor X → Option (Mori.PrimeDivisor Y)) {D : QDivisor X} (hD : 0 ≤ D) :
    0 ≤ (DivisorWithCoeffs.mapPrimeDivisors φ D : QDivisor Y) := by
  rw [← Finsupp.sum_single D, Finsupp.sum, map_sum]
  refine Finset.sum_nonneg fun p _ => ?_
  rw [DivisorWithCoeffs.mapPrimeDivisors_single]
  cases φ p with
  | none => exact le_rfl
  | some E => exact Finsupp.single_nonneg.mpr (hD p)

/-- **The pull-back of an effective `ℚ`-Cartier `ℚ`-divisor is effective.** With `m` the Cartier
index of `A`, `m f^*A` is the pull-back of the effective Cartier divisor `mA`, whose coefficients
are orders of regular functions. -/
private theorem nonneg_of_isPullback [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} {A : QDivisor Y} (hA : 0 ≤ A)
    (hAq : A.IsQCartier)
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ A.supp}
    {B : QDivisor X} (h : A.IsPullback f hB B) : 0 ≤ B := by
  have hm := QDivisor.cartierIndex_pos hAq
  obtain ⟨D₀, hD₀, hD₀c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hAq
  obtain ⟨D', hD', hp⟩ := h _ hm D₀ hD₀ hD₀c
  have hmq : (0 : ℚ) < (A.cartierIndex hAq : ℚ) := by exact_mod_cast hm
  have hD₀n : ∀ P : Mori.PrimeDivisor Y, (P.support ∩ (⊤ : Y.Opens)).Nonempty →
      0 ≤ D₀.coeff P := by
    intro P _
    have h2 := congrArg (fun G : QDivisor Y => G P) hD₀
    simp only [Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast] at h2
    have : (0 : ℚ) ≤ (D₀ P : ℚ) := by
      change (Divisor.toQDivisor D₀) P = _ at h2
      rw [show (Divisor.toQDivisor D₀) P = (D₀ P : ℚ) from rfl] at h2
      rw [h2]; exact mul_nonneg hmq.le (hA P)
    exact_mod_cast this
  intro E
  have hE : (E.support ∩ f ⁻¹ᵁ (⊤ : Y.Opens)).Nonempty := by
    refine ⟨E.genericPoint, ?_, trivial⟩
    change E.genericPoint ∈ E.support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have h0 := MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn hD₀c hD₀n hp E hE
  have h1 := congrArg (fun G : QDivisor X => G E) hD'
  simp only [Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast] at h1
  rw [show (Divisor.toQDivisor D') E = (D' E : ℚ) from rfl] at h1
  have h0' : (0 : ℚ) ≤ (D' E : ℚ) := by exact_mod_cast h0
  rw [h1] at h0'
  exact nonneg_of_mul_nonneg_right (by simpa [mul_comm] using h0') hmq

/-- **The retained divisor is not a component of the transform.** If `φ_* S⁰ = S` and `S⁰` is not
a component of `A⁰`, the generic point of `S` lies outside `Supp (φ_* A⁰)`: the only component of
`φ_* A⁰` through `η_S` is `S`, whose coefficient is that of `S⁰` in `A⁰`, `φ` being injective on
retained prime divisors. -/
private theorem genericPoint_notMem_supp_transformDivisor [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [Scheme.IsSeparated X] [Scheme.IsSeparated Y]
    {φ : X.RationalMap Y} {ψ : Y.RationalMap X} (hψ : Mori.RationalMap.IsInverse φ ψ)
    {S₀ : Mori.PrimeDivisor X} {S : Mori.PrimeDivisor Y}
    (hS : Mori.RationalMap.transformPrimeDivisor φ S₀ = some S) {R : Type*} [AddCommMonoid R]
    (A₀ : DivisorWithCoeffs R X) (hAS : A₀.coeff S₀ = 0) :
    S.genericPoint ∉ (Mori.RationalMap.transformDivisor φ A₀).supp := by
  intro h
  obtain ⟨E, hE, hmem⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
  obtain rfl := MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support hmem
  apply hE
  change DivisorWithCoeffs.mapPrimeDivisors _ A₀ S = 0
  rwa [MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hS
    (fun E' hE' => eq_of_transformPrimeDivisor_eq_some hψ hE' hS)]

/-- The birational transform of divisors commutes with regarding a divisor as a
`ℚ`-divisor. -/
private theorem transformDivisor_toQDivisor {X Y : Scheme.{u}} (φ : X.RationalMap Y)
    (D : Divisor X) :
    Mori.RationalMap.transformDivisor φ (Divisor.toQDivisor D) =
      Divisor.toQDivisor (Mori.RationalMap.transformDivisor φ D) := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' h h' => rw [map_add, map_add, h, h', map_add, map_add]
  | single P n =>
    have hP : Divisor.toQDivisor (Finsupp.single P n) = Finsupp.single P (n : ℚ) := by
      ext E
      show ((Finsupp.single P n E : ℤ) : ℚ) = Finsupp.single P (n : ℚ) E
      rw [Finsupp.single_apply, Finsupp.single_apply]
      split_ifs <;> simp
    rw [hP, Mori.RationalMap.transformDivisor_single, Mori.RationalMap.transformDivisor_single]
    cases Mori.RationalMap.transformPrimeDivisor φ P with
    | none => simp
    | some E =>
      ext F
      show Finsupp.single E (n : ℚ) F = ((Finsupp.single E n F : ℤ) : ℚ)
      rw [Finsupp.single_apply, Finsupp.single_apply]
      split_ifs <;> simp

/-- The generic point of a prime divisor `S` lies outside the support of a divisor in which `S`
has coefficient zero. -/
private theorem genericPoint_notMem_supp_self {X : Scheme.{u}} (S : Mori.PrimeDivisor X)
    {R : Type*} [AddCommMonoid R] (D : DivisorWithCoeffs R X) (hD : D.coeff S = 0) :
    S.genericPoint ∉ D.supp := by
  intro h
  obtain ⟨E, hE, hmem⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
  obtain rfl := MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support hmem
  exact hE hD

/-- If the generic point of `S` lies outside the closed set `T`, so does the image of the generic
point of every irreducible component of the subscheme `S`. -/
private theorem subschemeι_componentGenericPoint_notMem {X : Scheme.{u}}
    (S : Mori.PrimeDivisor X) {T : TopologicalSpace.Closeds X} (h : S.genericPoint ∉ T) :
    haveI := S.integral
    ∀ Z : irreducibleComponents S.idealSheaf.subscheme,
      S.idealSheaf.subschemeι (componentGenericPoint _ Z) ∉ T := by
  haveI := S.integral
  intro Z
  have hZ : Z.1 = Set.univ :=
    Set.eq_univ_of_univ_subset (Z.2.2 (IrreducibleSpace.isIrreducible_univ _) (Set.subset_univ _))
  have hgen : componentGenericPoint _ Z = genericPoint S.idealSheaf.subscheme :=
    (isGenericPoint_componentGenericPoint _ Z).eq (by rw [hZ]; exact genericPoint_spec _)
  rwa [hgen]

/-- A nonempty space of finite dimension has dimension a natural number. -/
private theorem exists_topologicalKrullDim_eq_natCast_of_ne_top {T : Type*} [TopologicalSpace T]
    [Nonempty T] (htop : topologicalKrullDim T ≠ ⊤) : ∃ n : ℕ, topologicalKrullDim T = n := by
  obtain ⟨x⟩ := (inferInstance : Nonempty T)
  have : Nonempty (TopologicalSpace.IrreducibleCloseds T) :=
    ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp
    (Order.krullDim_ne_bot_iff.mpr inferInstance : topologicalKrullDim T ≠ ⊥)
  obtain ⟨d, rfl⟩ := ENat.ne_top_iff_exists.mp (show e ≠ ⊤ by
    rintro rfl
    exact htop he.symm)
  exact ⟨d, he.symm⟩

/-- **A prime divisor has codimension one**: `dim S + 1 = dim X` for a prime divisor `S` of an
integral scheme locally of finite type over a field. -/
private theorem topologicalKrullDim_subscheme_add_one {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sX]
    (S : Mori.PrimeDivisor X) :
    topologicalKrullDim S.idealSheaf.subscheme + 1 = topologicalKrullDim X := by
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX S.genericPoint
  rw [S.coheight_genericPoint, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h
  rw [S.idealSheaf.subschemeι.isClosedEmbedding.toIsEmbedding.toHomeomorph.isHomeomorph
    |>.topologicalKrullDim_eq, S.idealSheaf.range_subschemeι]
  exact_mod_cast h

/-- Birational schemes locally of finite type over a field have the same dimension: both have
the dimension of the dense opens identified by a partial isomorphism. -/
private theorem topologicalKrullDim_eq_of_partialIso {k : Type u} [Field k] {X Y : Scheme.{u}}
    [IrreducibleSpace X] [IrreducibleSpace Y] (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] (e : X.PartialIso Y) :
    topologicalKrullDim X = topologicalKrullDim Y := by
  rw [AlgebraicGeometry.topologicalKrullDim_eq_of_isOpen k X sX _ e.source.isOpen
      e.dense_source.nonempty,
    AlgebraicGeometry.topologicalKrullDim_eq_of_isOpen k Y sY _ e.target.isOpen
      e.dense_target.nonempty]
  exact (Scheme.homeoOfIso e.iso).isHomeomorph.topologicalKrullDim_eq

/-- A prime divisor of a projective variety has finite dimension. -/
private theorem exists_topologicalKrullDim_subscheme_eq_natCast {k : Type u} [Field k]
    {X₀ : Scheme.{u}} [IsIntegral X₀] (sX₀ : X₀ ⟶ Spec (.of k))
    (hX₀p : Mori.IsProjectiveVariety k sX₀) (S₀ : Mori.PrimeDivisor X₀) :
    ∃ d : ℕ, topologicalKrullDim S₀.idealSheaf.subscheme = d := by
  have : AlgebraicGeometry.IsVariety k sX₀ := hX₀p.toIsVariety
  have : CompactSpace X₀ := QuasiCompact.compactSpace_of_compactSpace sX₀
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq_natCast_of_ne_top
    (topologicalKrullDim_ne_top_of_locallyOfFiniteType k sX₀)
  have h := topologicalKrullDim_subscheme_add_one sX₀ S₀
  rw [hn] at h
  have hne : topologicalKrullDim S₀.idealSheaf.subscheme ≠ ⊤ := by
    intro htop
    rw [htop, show (⊤ : WithBot ℕ∞) + 1 = ⊤ from rfl] at h
    exact absurd h (by
      change ((⊤ : ℕ∞) : WithBot ℕ∞) ≠ ((n : ℕ∞) : WithBot ℕ∞)
      exact_mod_cast (ENat.top_ne_natCast n))
  haveI := S₀.integral
  exact exists_topologicalKrullDim_eq_natCast_of_ne_top hne

/-! ### Bigness of the restriction -/

/-- The `k`-dimension of `H⁰(Y, 𝒪_Y(E))`, a `k`-vector space through `s : Y ⟶ Spec k`. -/
private noncomputable def sectionsFinrank {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] (s : Y ⟶ Spec (.of k)) (E : Divisor Y) : ℕ :=
  letI : Module k (E.divisorialSubmodule ⊤) :=
    Module.compHom _ (scalarsToGlobalSections k s)
  Module.finrank k (E.divisorialSubmodule ⊤)

/-- **Sections over a point.** For `π : Y ⟶ Spec k`, the stalk of `π_* 𝒪_Y(E)` at the point of
`Spec k` is `H⁰(Y, 𝒪_Y(E))`, and the stalk of `𝒪_{Spec k}` is `k`: the only open containing the
point is `Spec k`. So the two ranks agree. -/
private theorem rank_sections_eq_rank_stalk {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] (s : Y ⟶ Spec (.of k)) (E : Divisor Y) :
    letI G := (Scheme.Modules.pushforward s).obj E.divisorialSheaf
    letI : Module ((Spec (.of k)).presheaf.stalk (genericPoint (Spec (.of k))))
        (G.presheaf.stalk (genericPoint (Spec (.of k)))) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := (Spec (.of k)).presheaf) G.val (genericPoint (Spec (.of k)))
    letI : Module k (E.divisorialSubmodule ⊤) := Module.compHom _ (scalarsToGlobalSections k s)
    Module.rank k (E.divisorialSubmodule ⊤) =
      Module.rank ((Spec (.of k)).presheaf.stalk (genericPoint (Spec (.of k))))
        (G.presheaf.stalk (genericPoint (Spec (.of k)))) := by
  haveI : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  set G := (Scheme.Modules.pushforward s).obj E.divisorialSheaf with hG
  set η := genericPoint (Spec (.of k))
  have hU : ∀ U : (Spec (.of k)).Opens, η ∈ U → U = ⊤ := fun U hU => by
    ext x
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    rwa [Subsingleton.elim x η]
  have hR : Function.Bijective ((Spec (.of k)).presheaf.germ ⊤ η trivial) := by
    refine ⟨fun a b h => ?_, fun t => ?_⟩
    · obtain ⟨W, hW, iU, iV, he⟩ :=
        TopCat.Presheaf.germ_eq (Spec (.of k)).presheaf (U := ⊤) (V := ⊤) η trivial trivial a b h
      obtain rfl := hU W hW
      have h1 : iU = 𝟙 _ := Subsingleton.elim _ _
      have h2 : iV = 𝟙 _ := Subsingleton.elim _ _
      subst h1 h2
      simpa using he
    · obtain ⟨W, hW, a, rfl⟩ := (Spec (.of k)).presheaf.exists_germ_eq t
      obtain rfl := hU W hW
      exact ⟨a, rfl⟩
  have hM : Function.Bijective (G.presheaf.germ ⊤ η trivial) := by
    refine ⟨fun a b h => ?_, fun t => ?_⟩
    · obtain ⟨W, hW, iU, iV, he⟩ :=
        TopCat.Presheaf.germ_eq G.presheaf (U := ⊤) (V := ⊤) η trivial trivial a b h
      obtain rfl := hU W hW
      have h1 : iU = 𝟙 _ := Subsingleton.elim _ _
      have h2 : iV = 𝟙 _ := Subsingleton.elim _ _
      subst h1 h2
      simpa using he
    · obtain ⟨W, hW, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ t
      obtain rfl := hU W hW
      exact ⟨a, rfl⟩
  letI : Module k (E.divisorialSubmodule ⊤) := Module.compHom _ (scalarsToGlobalSections k s)
  let j : E.divisorialSubmodule ⊤ ≃+ G.presheaf.stalk η :=
    AddEquiv.ofBijective (G.presheaf.germ ⊤ η trivial).hom hM
  exact rank_eq_of_equiv_equiv (R := k) (R' := (Spec (.of k)).presheaf.stalk η)
    (fun c => (Spec (.of k)).presheaf.germ ⊤ η trivial ((Scheme.ΓSpecIso (.of k)).inv c)) j
    (hR.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv)) (fun c m =>
      (PresheafOfModules.germ_smul (R := (Spec (.of k)).presheaf) G.val η ⊤ trivial _ m))

/-- **The generic rank over a point.** Over `Spec k`, the rank of `π_* 𝒪_Y(E)` at the point is the
`k`-dimension of `H⁰(Y, 𝒪_Y(E))`. -/
private theorem relativeGenericRank_eq_sectionsFinrank {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (s : Y ⟶ Spec (.of k)) [IsProper s]
    (E : Divisor Y) (hE : E.IsCartier) :
    relativeGenericRank s E.divisorialSheaf = sectionsFinrank s E := by
  haveI : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have hinv := hE.isInvertibleModule_divisorialSheaf
  have : (E.divisorialSheaf).IsCoherent :=
    @Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible Y _ _ hinv
  have : ((Scheme.Modules.pushforward s).obj E.divisorialSheaf).IsCoherent :=
    ProperCoherenceWitness.isCoherent_pushforward s E.divisorialSheaf
  haveI : ((Scheme.Modules.pushforward s).obj E.divisorialSheaf).IsFiniteType :=
    SheafOfModules.IsCoherent.isFiniteType
  have hη : s (genericPoint Y) = genericPoint (Spec (.of k)) := Subsingleton.elim _ _
  unfold relativeGenericRank
  rw [hη, Scheme.Modules.fiberRank_genericPoint_eq_finrank_stalk]
  unfold sectionsFinrank
  simp only [Module.finrank, rank_sections_eq_rank_stalk s E]

/-- `H⁰(Y, 𝒪_Y(E))` is finite-dimensional over `k` for a Cartier divisor `E` on `Y` proper over
`k`: the direct image of the coherent `𝒪_Y(E)` is coherent ([Stacks, Tag 02O5]). -/
private theorem finiteDimensional_sections {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] (s : Y ⟶ Spec (.of k)) [IsProper s]
    (E : Divisor Y) (hE : E.IsCartier) :
    letI : Module k (E.divisorialSubmodule ⊤) := Module.compHom _ (scalarsToGlobalSections k s)
    FiniteDimensional k (E.divisorialSubmodule ⊤) := by
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have hinv := hE.isInvertibleModule_divisorialSheaf
  have : (E.divisorialSheaf).IsCoherent :=
    @Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible Y _ _ hinv
  have : ((Scheme.Modules.pushforward s).obj E.divisorialSheaf).IsCoherent :=
    ProperCoherenceWitness.isCoherent_pushforward s E.divisorialSheaf
  have hfin := Scheme.Modules.finite_stalk_of_isCoherent
    ((Scheme.Modules.pushforward s).obj E.divisorialSheaf) (genericPoint (Spec (.of k)))
  letI : Module k (E.divisorialSubmodule ⊤) := Module.compHom _ (scalarsToGlobalSections k s)
  have hlt : Module.rank k (E.divisorialSubmodule ⊤) < Cardinal.aleph0 := by
    rw [rank_sections_eq_rank_stalk s E]
    exact Module.rank_lt_aleph0 _ _
  exact Module.rank_lt_aleph0_iff.mp hlt

/-- **Linear algebra of the comparison.** If `ρ : V ↠ W₀` and `Φ : V → W` are linear, `W` is
finite-dimensional and `ker Φ ⊆ ker ρ`, then `dim W₀ ≤ dim W`. -/
private theorem finrank_le_of_surjective_of_ker_le {K V W₀ W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W₀] [Module K W₀] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (ρ : V →ₗ[K] W₀) (hρ : Function.Surjective ρ) (Φ : V →ₗ[K] W)
    (h : ∀ v, Φ v = 0 → ρ v = 0) : Module.finrank K W₀ ≤ Module.finrank K W := by
  have hker : LinearMap.ker Φ ≤ LinearMap.ker ρ := fun v hv => h v hv
  let eρ := ρ.quotKerEquivOfSurjective hρ
  let eΦ := Φ.quotKerEquivRange
  haveI : FiniteDimensional K (V ⧸ LinearMap.ker Φ) := Module.Finite.equiv eΦ.symm
  let π : (V ⧸ LinearMap.ker Φ) →ₗ[K] (V ⧸ LinearMap.ker ρ) :=
    Submodule.mapQ _ _ LinearMap.id hker
  have hπ : Function.Surjective π := by
    intro x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨Submodule.Quotient.mk v, rfl⟩
  calc Module.finrank K W₀ = Module.finrank K (V ⧸ LinearMap.ker ρ) := eρ.finrank_eq.symm
    _ ≤ Module.finrank K (V ⧸ LinearMap.ker Φ) := LinearMap.finrank_le_finrank_of_surjective hπ
    _ = Module.finrank K (LinearMap.range Φ) := eΦ.finrank_eq
    _ ≤ Module.finrank K W := Submodule.finrank_le _

/-- The image of a scheme over `Spec k` in `Spec k` has dimension zero. -/
private theorem topologicalKrullDim_closure_range_eq_zero {k : Type u} [Field k] {Y : Scheme.{u}}
    [Nonempty Y] (s : Y ⟶ Spec (.of k)) :
    topologicalKrullDim (closure (Set.range s.base)) = ((0 : ℕ) : WithBot ℕ∞) := by
  haveI : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  set T := closure (Set.range s.base)
  obtain ⟨y⟩ := ‹Nonempty Y›
  let t : T := ⟨s y, subset_closure ⟨y, rfl⟩⟩
  haveI : Nonempty (TopologicalSpace.IrreducibleCloseds T) :=
    ⟨⟨closure {t}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  haveI : Subsingleton (TopologicalSpace.IrreducibleCloseds T) := ⟨fun a b => by
    ext x
    obtain ⟨a', ha'⟩ := a.isIrreducible.nonempty
    obtain ⟨b', hb'⟩ := b.isIrreducible.nonempty
    constructor
    · intro _; rwa [Subsingleton.elim x b']
    · intro _; rwa [Subsingleton.elim x a']⟩
  exact Order.krullDim_eq_zero

/-- The retained divisor `S` and its source `S⁰` have the same dimension. -/
private theorem topologicalKrullDim_subscheme_eq {k : Type u} [Field k] {X₀ X : Scheme.{u}}
    [IsIntegral X₀] [IsLocallyNoetherian X₀] [IsNormal X₀]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX₀ : X₀ ⟶ Spec (.of k)) (sX : X ⟶ Spec (.of k))
    (hX₀p : Mori.IsProjectiveVariety k sX₀) (hXp : Mori.IsProjectiveVariety k sX)
    (S₀ : Mori.PrimeDivisor X₀) (φ : X₀.RationalMap X) (ψ : X.RationalMap X₀)
    (hψ : Mori.RationalMap.IsInverse φ ψ) (S : Mori.PrimeDivisor X)
    (hS : Mori.RationalMap.transformPrimeDivisor φ S₀ = some S) :
    topologicalKrullDim S.idealSheaf.subscheme = topologicalKrullDim S₀.idealSheaf.subscheme := by
  have : AlgebraicGeometry.IsVariety k sX₀ := hX₀p.toIsVariety
  have : AlgebraicGeometry.IsVariety k sX := hXp.toIsVariety
  have : LocallyOfFiniteType sX₀ := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  have : LocallyOfFiniteType sX := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  obtain ⟨d₀, hd₀⟩ := exists_topologicalKrullDim_subscheme_eq_natCast sX₀ hX₀p S₀
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_subscheme_eq_natCast sX hXp S
  obtain ⟨e, -, -⟩ := hψ
  have h₀ := topologicalKrullDim_subscheme_add_one sX₀ S₀
  have h := topologicalKrullDim_subscheme_add_one sX S
  rw [← topologicalKrullDim_eq_of_partialIso sX₀ sX e, ← h₀, hd, hd₀] at h
  rw [hd, hd₀]
  have : ((d + 1 : ℕ) : WithBot ℕ∞) = ((d₀ + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast h
  have := Nat.cast_injective this
  exact_mod_cast (by omega : d = d₀)

/-- `𝒪_X(D)^{⊗ q} ≅ 𝒪_X(qD)` for a Cartier divisor `D`, by multiplication of sections. -/
private theorem nonempty_tensorPower_iso_divisorialSheaf {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] (D : Divisor X) (hD : D.IsCartier) (q : ℕ) :
    haveI := hD.isInvertibleModule_divisorialSheaf
    Nonempty (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2
      D.divisorialSheaf (q : ℤ) ≅ ((q : ℤ) • D).divisorialSheaf) := by
  haveI := hD.isInvertibleModule_divisorialSheaf
  induction q with
  | zero =>
    refine ⟨eqToIso (Stacks.SheafOfModules.Invertible.tensorPower_zero _ _ _) ≪≫
      (Divisor.divisorialSheafZeroIso).symm ≪≫ eqToIso (by rw [Nat.cast_zero, zero_smul])⟩
  | succ q ih =>
    obtain ⟨e⟩ := ih
    refine ⟨(eqToIso (by push_cast; rfl)) ≪≫
      (Stacks.SheafOfModules.Invertible.tensorPowerSuccIso _ _ _ (q : ℤ)).symm ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso e).app _ ≪≫
      (hD.zsmul (q : ℤ)).divisorialSheafTensorIso hD ≪≫
      eqToIso (by congr 1; push_cast; rw [add_smul, one_smul])⟩

/-- The `k`-dimension of the global sections of `𝒪_Y(E)`, read through
`AlgebraicGeometry.globalSectionsOverField`, is `sectionsFinrank`. -/
private theorem finrank_globalSectionsOverField_eq_sectionsFinrank {k : Type u} [Field k]
    {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y] (s : Y ⟶ Spec (.of k))
    (E : Divisor Y) :
    Module.finrank k (globalSectionsOverField k s E.divisorialSheaf) = sectionsFinrank s E := by
  have key : ∀ φ : k →+* Γ(Y, ⊤), φ = scalarsToGlobalSections k s →
      (letI : Module k (E.divisorialSubmodule ⊤) := Module.compHom _ φ
       Module.finrank k (E.divisorialSubmodule ⊤)) = sectionsFinrank s E := by
    rintro φ rfl
    rfl
  refine key _ ?_
  have : s.appLE ⊤ ⊤ (by simp) = s.appTop := by
    simp [Scheme.Hom.appLE]
    exact Category.comp_id _
  rw [this]
  rfl

/-- **Growth of the sections on `S⁰`.** The pull-back `A⁰|_{S⁰}` of the ample Cartier divisor
`D₁` is ample, so by asymptotic Riemann–Roch `h⁰(S⁰, q D₁|_{S⁰})` grows like `q^{dim S⁰}`. -/
private theorem exists_growth_sectionsFinrank {k : Type u} [Field k] {X₀ : Scheme.{u}}
    [IsIntegral X₀] [IsLocallyNoetherian X₀] [IsNormal X₀] [CompactSpace X₀]
    (sX₀ : X₀ ⟶ Spec (.of k)) (hX₀p : Mori.IsProjectiveVariety k sX₀)
    (S₀ : Mori.PrimeDivisor X₀) [IsNormal S₀.idealSheaf.subscheme]
    (D₁ : Divisor X₀) (hD₁ : D₁.IsCartier) (hamp : D₁.IsAmple hD₁) (hD₁S : D₁.coeff S₀ = 0)
    (d : ℕ) (hd : topologicalKrullDim S₀.idealSheaf.subscheme = d) :
    haveI := S₀.integral
    haveI := S₀.idealSheaf.isLocallyNoetherian_subscheme
    ∃ c : ℝ, 0 < c ∧ ∃ q₁ : ℕ, ∀ q : ℕ, q₁ ≤ q →
      ∀ (hB : ∀ Z : irreducibleComponents S₀.idealSheaf.subscheme,
          S₀.idealSheaf.subschemeι (componentGenericPoint _ Z) ∉ ((q : ℤ) • D₁).supp)
        (E : Divisor S₀.idealSheaf.subscheme),
        ((q : ℤ) • D₁).IsPullback S₀.idealSheaf.subschemeι hB E →
          c * (q : ℝ) ^ d ≤
            (sectionsFinrank (S₀.idealSheaf.subschemeι ≫ sX₀) E : ℝ) := by
  haveI := S₀.integral
  haveI := S₀.idealSheaf.isLocallyNoetherian_subscheme
  haveI : IsProper sX₀ := isProper_of_isProjectiveMorphism sX₀ hX₀p.isProjective
  haveI : CompactSpace S₀.idealSheaf.subscheme :=
    S₀.idealSheaf.subschemeι.isClosedEmbedding.compactSpace
  set i := S₀.idealSheaf.subschemeι with hi
  have hB₁ : ∀ Z : irreducibleComponents S₀.idealSheaf.subscheme,
      i (componentGenericPoint _ Z) ∉ D₁.supp :=
    subschemeι_componentGenericPoint_notMem S₀ (genericPoint_notMem_supp_self S₀ D₁ hD₁S)
  obtain ⟨D₁', hD₁'⟩ := hD₁.exists_isPullback hB₁
  have hD₁'c : D₁'.IsCartier := Divisor.IsPullback.isCartier hD₁' hD₁
  haveI := hD₁'c.isInvertibleModule_divisorialSheaf
  haveI := hD₁.isInvertibleModule_divisorialSheaf
  -- `𝒪_{S⁰}(D₁|_{S⁰}) ≅ i^* 𝒪_{X⁰}(D₁)` is ample
  have hLamp : Scheme.Modules.IsAmple S₀.idealSheaf.subscheme D₁'.divisorialSheaf := by
    have h1 : Scheme.Modules.IsAmple X₀ D₁.divisorialSheaf :=
      Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple X₀ _ hamp
    have h2 := Scheme.Modules.isAmple_pullback_of_isClosedImmersion i D₁.divisorialSheaf h1
    exact Scheme.Modules.isAmple_of_iso
      (Divisor.IsPullback.divisorialSheafIso (hBc := hD₁) hD₁').symm h2
  obtain ⟨hpos, P, hPdeg, hev⟩ := asymptotic_riemann_roch k (i ≫ sX₀) d hd _ hLamp
  set a : ℚ := (degreeWithRespectTo k (i ≫ sX₀) (𝟙 _) d hd D₁'.divisorialSheaf hLamp : ℚ) /
    (d.factorial : ℚ) with ha
  have hlow : ∀ᶠ n : ℕ in Filter.atTop, -(a / 2) * (n : ℚ) ^ d ≤ P.eval (n : ℚ) := by
    have hdeg : P.degree < (Polynomial.X ^ d : Polynomial ℚ).degree := by
      rwa [Polynomial.degree_X_pow]
    have h := (Polynomial.div_tendsto_atTop_zero_of_degree_lt P (Polynomial.X ^ d) hdeg).comp
      tendsto_natCast_atTop_atTop
    have h2 := h.eventually (lt_mem_nhds (show -(a / 2) < 0 by linarith))
    filter_upwards [h2, Filter.eventually_ge_atTop 1] with n hn hn1
    simp only [Function.comp, Polynomial.eval_pow, Polynomial.eval_X] at hn
    have hpos' : (0 : ℚ) < (n : ℚ) ^ d := by
      have : (1 : ℚ) ≤ n := by exact_mod_cast hn1
      positivity
    rw [lt_div_iff₀ hpos'] at hn
    linarith
  obtain ⟨q₁, hq₁⟩ := Filter.eventually_atTop.mp (hev.and hlow)
  refine ⟨(a / 2 : ℚ), by exact_mod_cast (by linarith : (0 : ℚ) < a / 2), q₁,
    fun q hq hB E hE => ?_⟩
  obtain ⟨h1, h2⟩ := hq₁ q hq
  -- `E = q D₁|_{S⁰}`, and `𝒪_{S⁰}(q D₁|_{S⁰}) ≅ 𝒪_{S⁰}(D₁|_{S⁰})^{⊗ q}`
  have hE' := Divisor.IsPullback.zsmul hD₁ hD₁' (q : ℤ) hB
  obtain rfl := Divisor.IsPullback.eq (hD₁.zsmul (q : ℤ)) hE hE'
  obtain ⟨e⟩ := nonempty_tensorPower_iso_divisorialSheaf D₁' hD₁'c q
  have hfin : Module.finrank k (globalSectionsOverField k (i ≫ sX₀)
      (Stacks.SheafOfModules.Invertible.tensorPower S₀.idealSheaf.subscheme.presheaf
        S₀.idealSheaf.subscheme.ringCatSheaf.2 D₁'.divisorialSheaf (q : ℤ))) =
      sectionsFinrank (i ≫ sX₀) ((q : ℤ) • D₁') := by
    rw [← finrank_globalSectionsOverField_eq_sectionsFinrank]
    exact ((ModuleCat.restrictScalars _).mapIso
      ((SheafOfModules.evaluation _ (Opposite.op ⊤)).mapIso e)).toLinearEquiv.finrank_eq
  rw [← hfin]
  have h3 : ((a / 2 : ℚ) : ℝ) * (q : ℝ) ^ d ≤
      ((Module.finrank k (globalSectionsOverField k (i ≫ sX₀)
        (Stacks.SheafOfModules.Invertible.tensorPower S₀.idealSheaf.subscheme.presheaf
        S₀.idealSheaf.subscheme.ringCatSheaf.2 D₁'.divisorialSheaf (q : ℤ))) : ℚ) :
          ℝ) := by
    rw [h1]
    have : (a / 2) * (q : ℚ) ^ d ≤ a * (q : ℚ) ^ d + P.eval (q : ℚ) := by nlinarith
    exact_mod_cast this
  exact_mod_cast h3

/-- The support of a multiple of a divisor lies in the support of the divisor. -/
private theorem supp_zsmul_le {X : Scheme.{u}} (n : ℤ) (D : Divisor X) :
    (n • D).supp ≤ D.supp := by
  intro x hx
  obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
  refine DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, fun h => hE ?_, hxE⟩
  rw [DivisorWithCoeffs.coeff_smul, h, smul_zero]

/-- The closed immersion of a prime divisor sends the generic point of the subscheme to the generic
point of the divisor. -/
private theorem subschemeι_genericPoint_eq {X : Scheme.{u}} (S : Mori.PrimeDivisor X) :
    haveI := S.integral
    S.idealSheaf.subschemeι (genericPoint S.idealSheaf.subscheme) = S.genericPoint := by
  haveI := S.integral
  have h1 := (genericPoint_spec S.idealSheaf.subscheme).image
    S.idealSheaf.subschemeι.continuous
  rw [Set.image_univ, S.idealSheaf.range_subschemeι,
    S.idealSheaf.support.isClosed.closure_eq] at h1
  refine h1.eq ?_
  change closure _ = _
  exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure S).symm

/-- **Lifting sections from `S⁰` (Serre vanishing).** For `q ≫ 0`, `H¹(X⁰, 𝓘_{S⁰}(qD₁)) = 0`, so
the restriction `H⁰(X⁰, 𝒪(qD₁)) → H⁰(S⁰, 𝒪(qD₁)|_{S⁰})`, read through
`𝒪_{S⁰}(qD₁|_{S⁰}) ≅ i^* 𝒪_{X⁰}(qD₁)`, is surjective; it kills every section vanishing along
`S⁰`, since such a section is `a ψ⁻¹` near `η_{S⁰}` with `a` vanishing on `S⁰`. -/
private theorem exists_surjective_restriction {k : Type u} [Field k] {X₀ : Scheme.{u}}
    [IsIntegral X₀] [IsLocallyNoetherian X₀] [IsNormal X₀] [CompactSpace X₀]
    (sX₀ : X₀ ⟶ Spec (.of k)) (hX₀p : Mori.IsProjectiveVariety k sX₀)
    (S₀ : Mori.PrimeDivisor X₀) [IsNormal S₀.idealSheaf.subscheme]
    (D₁ : Divisor X₀) (hD₁ : D₁.IsCartier) (hamp : D₁.IsAmple hD₁) (hD₁S : D₁.coeff S₀ = 0) :
    haveI := S₀.integral
    haveI := S₀.idealSheaf.isLocallyNoetherian_subscheme
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      ∀ (hB₀ : ∀ Z : irreducibleComponents S₀.idealSheaf.subscheme,
          S₀.idealSheaf.subschemeι (componentGenericPoint _ Z) ∉ ((q : ℤ) • D₁).supp)
        (E₀ : Divisor S₀.idealSheaf.subscheme),
        ((q : ℤ) • D₁).IsPullback S₀.idealSheaf.subschemeι hB₀ E₀ →
        letI : Module k (((q : ℤ) • D₁).divisorialSubmodule ⊤) :=
          Module.compHom _ (scalarsToGlobalSections k sX₀)
        letI : Module k (E₀.divisorialSubmodule ⊤) :=
          Module.compHom _ (scalarsToGlobalSections k (S₀.idealSheaf.subschemeι ≫ sX₀))
        ∃ ρ : ((q : ℤ) • D₁).divisorialSubmodule ⊤ →ₗ[k] E₀.divisorialSubmodule ⊤,
          Function.Surjective ρ ∧
            ∀ f : ((q : ℤ) • D₁).divisorialSubmodule ⊤,
              S₀.OrdGE 1 ((f : ToType ((rationalFunctionsPresheaf X₀).obj (Opposite.op ⊤)))
                ⟨S₀.component, trivial⟩) → ρ f = 0 := by
  haveI := S₀.integral
  haveI := S₀.idealSheaf.isLocallyNoetherian_subscheme
  haveI : IsProper sX₀ := isProper_of_isProjectiveMorphism sX₀ hX₀p.isProjective
  haveI := hD₁.isInvertibleModule_divisorialSheaf
  haveI : CompactSpace S₀.idealSheaf.subscheme :=
    S₀.idealSheaf.subschemeι.isClosedEmbedding.compactSpace
  set i := S₀.idealSheaf.subschemeι with hi
  -- the ideal sheaf of `S⁰` is coherent
  have hIc : (Stacks.Divisors.negativeTwist S₀.idealSheaf).IsCoherent := by
    have : (SheafOfModules.unit (structureSheafRing X₀.toRingedSpace)).IsCoherent :=
      Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k sX₀
    have : ((RingedSpaceModuleAdjunction.modulePushforward i.toLRSHom.toShHom).obj
        (SheafOfModules.unit
          (structureSheafRing S₀.idealSheaf.subscheme.toRingedSpace))).IsCoherent :=
      Stacks.Chow.isCoherent_pushforwardStructureSheaf i
    exact AlgebraicGeometry.CoherentAbelian.isCoherent_kernel
      (Stacks.IdealSheafSequence.divisorQuotientMap S₀.idealSheaf)
  -- Serre vanishing for `𝓘_{S⁰} ⊗ 𝒪(D₁)^{⊗ q}`
  haveI hIc' : SheafOfModules.IsCoherent
      (show X₀.Modules from Stacks.Divisors.negativeTwist S₀.idealSheaf) := hIc
  obtain ⟨d₀, hd₀⟩ :=
    Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist
    sX₀ (show X₀.Modules from Stacks.Divisors.negativeTwist S₀.idealSheaf) D₁.divisorialSheaf hamp
  refine ⟨d₀, fun q hq hB₀ E₀ hE₀ => ?_⟩
  have hqc : ((q : ℤ) • D₁).IsCartier := hD₁.zsmul q
  haveI := hqc.isInvertibleModule_divisorialSheaf
  obtain ⟨e⟩ := nonempty_tensorPower_iso_divisorialSheaf D₁ hD₁ q
  let e' : Stacks.Ample.tensorPowModule X₀ D₁.divisorialSheaf (q : ℤ) ≅
      ((q : ℤ) • D₁).divisorialSheaf :=
    (Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso X₀ _ (q : ℤ)).symm ≪≫ e
  have hH1 : Limits.IsZero (Hgroup X₀.ringCatSheaf ⊤ 1
      (Stacks.RelativeVeryAmple.tensorModules X₀ (Stacks.Divisors.negativeTwist S₀.idealSheaf)
        ((q : ℤ) • D₁).divisorialSheaf)) :=
    (hd₀ q 1 hq one_pos).of_iso ((Hfunctor X₀.ringCatSheaf ⊤ 1).mapIso
      (Stacks.RelativeVeryAmple.tensorModulesMapIso X₀ (Iso.refl _) e'.symm))
  obtain ⟨w, hSE⟩ := Stacks.Divisors.exists_shortExact_invertibleTwist S₀.idealSheaf
    ((q : ℤ) • D₁).divisorialSheaf inferInstance
  have hsurj := Stacks.SerreAffinenessCriterion.surjective_app_of_isZero_hgroup_one X₀ ⊤ hSE hH1
  -- the restriction, read in `𝒪_{S⁰}(E₀)`
  let γ := (Adjunction.leftAdjointUniq
      (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction i.toLRSHom.toShHom)
      (Scheme.Modules.pullbackPushforwardAdjunction i)).app ((q : ℤ) • D₁).divisorialSheaf ≪≫
    (Divisor.IsPullback.divisorialSheafIso (hBc := hqc) hE₀).symm
  let u := ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
    i.toLRSHom.toShHom).unit.app ((q : ℤ) • D₁).divisorialSheaf).val
  let ρ₀ : ((q : ℤ) • D₁).divisorialSubmodule ⊤ → E₀.divisorialSubmodule ⊤ :=
    fun f => (γ.hom.val.app (Opposite.op ⊤)).hom ((u.app (Opposite.op ⊤)).hom f)
  have hρ₀ : ∀ (r : Γ(X₀, ⊤)) (f : ((q : ℤ) • D₁).divisorialSubmodule ⊤),
      ρ₀ (r • f) = (i.appTop r) • ρ₀ f := by
    intro r f
    have h1 := (u.app (Opposite.op ⊤)).hom.map_smul (show X₀.ringCatSheaf.obj.obj (Opposite.op ⊤)
      from r) (show ((q : ℤ) • D₁).divisorialSheaf.val.obj (Opposite.op ⊤) from f)
    have h2 := (γ.hom.val.app (Opposite.op ⊤)).hom.map_smul (i.appTop r)
      ((u.app (Opposite.op ⊤)).hom f)
    exact (congrArg (γ.hom.val.app (Opposite.op ⊤)).hom h1).trans h2
  letI : Module k (((q : ℤ) • D₁).divisorialSubmodule ⊤) :=
    Module.compHom _ (scalarsToGlobalSections k sX₀)
  letI : Module k (E₀.divisorialSubmodule ⊤) :=
    Module.compHom _ (scalarsToGlobalSections k (i ≫ sX₀))
  let ρ : ((q : ℤ) • D₁).divisorialSubmodule ⊤ →ₗ[k] E₀.divisorialSubmodule ⊤ :=
    { toFun := ρ₀
      map_add' := fun f g =>
        (congrArg (γ.hom.val.app (Opposite.op ⊤)).hom
          ((u.app (Opposite.op ⊤)).hom.map_add f g)).trans
          ((γ.hom.val.app (Opposite.op ⊤)).hom.map_add _ _)
      map_smul' := fun c f => by
        change ρ₀ (scalarsToGlobalSections k sX₀ c • f) =
          scalarsToGlobalSections k (i ≫ sX₀) c • ρ₀ f
        rw [hρ₀]
        congr 1 }
  refine ⟨ρ, ?_, ?_⟩
  · intro y
    have hγ : (γ.hom.val.app (Opposite.op ⊤)).hom ((γ.inv.val.app (Opposite.op ⊤)).hom y) = y :=
      congrArg (fun φ => (φ.val.app (Opposite.op ⊤)).hom y) γ.inv_hom_id
    obtain ⟨f, hf⟩ := hsurj ((γ.inv.val.app (Opposite.op ⊤)).hom y)
    refine ⟨f, ?_⟩
    change (γ.hom.val.app (Opposite.op ⊤)).hom ((u.app (Opposite.op ⊤)).hom f) = y
    rw [← hγ]
    exact congrArg _ hf
  · intro f hf
    obtain ⟨U, hU, ψ, hψ⟩ := hqc S₀.genericPoint
    have hS₀U : (S₀.support ∩ U).Nonempty := ⟨S₀.genericPoint, by
      change S₀.genericPoint ∈ S₀.support
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl, hU⟩
    have hψS : S₀.ord ψ = 0 := by
      rw [← hψ S₀ hS₀U, DivisorWithCoeffs.coeff_smul, hD₁S, smul_zero]
    have hmem : componentGenericPoint X₀ S₀.component ∈ U :=
      S₀.componentGenericPoint_mem_of_nonempty hS₀U
    -- `f = a ψ⁻¹` on `U`
    obtain ⟨a, ha⟩ := (hψ.isLocalGenerator_invSection U le_rfl).2
      (((q : ℤ) • D₁).divisorialSheaf.presheaf.map (homOfLE le_top).op f)
    have hfa : (f : ToType ((rationalFunctionsPresheaf X₀).obj (Opposite.op ⊤)))
        ⟨S₀.component, trivial⟩ = X₀.presheaf.germ U _ hmem a *
          ((ψ⁻¹ : (RationalFunctions X₀)ˣ) : RationalFunctions X₀) S₀.component := by
      have := congrArg (fun φ : ((q : ℤ) • D₁).divisorialSubmodule U =>
        (φ : ToType ((rationalFunctionsPresheaf X₀).obj (Opposite.op U))) ⟨S₀.component, hmem⟩) ha
      exact this.symm
    -- `a` vanishes at `η_{S⁰}`
    set b := X₀.presheaf.germ U S₀.genericPoint hU a with hb
    have hbc : S₀.toComponent.hom b = X₀.presheaf.germ U _ hmem a :=
      TopCat.Presheaf.germ_stalkSpecializes_apply X₀.presheaf hU _ a
    have hbnu : ¬ IsUnit b := by
      intro hbu
      have hv := S₀.valuation_toComponent_of_isUnit hbu
      rw [hbc] at hv
      have hψv : S₀.valuation (((ψ⁻¹ : (RationalFunctions X₀)ˣ) : RationalFunctions X₀)
          S₀.component) = 1 := by
        rw [PrimeDivisor.valuation_component, PrimeDivisor.ord_inv, hψS, neg_zero,
          WithZero.exp_zero]
      rcases hf with h0 | h1
      · rw [hfa] at h0
        have hu := (Pi.isUnit_iff.mp (ψ⁻¹).isUnit) S₀.component
        have h00 : X₀.presheaf.germ U _ hmem a = 0 := hu.mul_left_eq_zero.mp h0
        rw [h00, map_zero] at hv
        exact zero_ne_one hv
      · rw [hfa, map_mul, hv, hψv, one_mul] at h1
        exact absurd h1 (by
          rw [not_le, ← WithZero.exp_zero, WithZero.exp_lt_exp]; exact one_pos)
    -- so `a` restricts to zero on `S⁰`
    set η' := genericPoint S₀.idealSheaf.subscheme
    have hiη : i η' = S₀.genericPoint := subschemeι_genericPoint_eq S₀
    have hη'U : η' ∈ i ⁻¹ᵁ U := by
      change i η' ∈ U; rwa [hiη]
    have hia : i.app U a = 0 := by
      apply germ_injective_of_isIntegral _ η' hη'U
      rw [map_zero, ← Scheme.Hom.germ_stalkMap_apply i U η' (by rwa [hiη]) a]
      have hnu' : ∀ (y : X₀) (hy : y = S₀.genericPoint) (hyU : y ∈ U),
          ¬ IsUnit (X₀.presheaf.germ U y hyU a) := by
        rintro _ rfl hyU; exact hbnu
      have hnu := hnu' (i η') hiη (by rwa [hiη])
      by_contra hne
      exact hnu (isUnit_of_map_unit (i.stalkMap η').hom _ (Ne.isUnit hne))
    -- hence `ρ f` vanishes on `i⁻¹ U`, and so everywhere
    have hres : E₀.divisorialSheaf.val.map (homOfLE le_top : i ⁻¹ᵁ U ⟶ ⊤).op (ρ₀ f) = 0 := by
      have h1 := PresheafOfModules.naturality_apply γ.hom.val
        (homOfLE le_top : i ⁻¹ᵁ U ⟶ ⊤).op ((u.app (Opposite.op ⊤)).hom f)
      have h2 := PresheafOfModules.naturality_apply u (homOfLE le_top : U ⟶ ⊤).op f
      have ha' : (show ((q : ℤ) • D₁).divisorialSubmodule U from
          ((q : ℤ) • D₁).divisorialSheaf.val.map (homOfLE le_top : U ⟶ ⊤).op f) =
          a • (show ((q : ℤ) • D₁).divisorialSubmodule U from
            ((q : ℤ) • D₁).divisorialSheaf.val.map (homOfLE le_rfl : U ⟶ U).op
              hψ.invSection) := ha.symm
      set x := (show ((q : ℤ) • D₁).divisorialSheaf.val.obj (Opposite.op U) from
        ((q : ℤ) • D₁).divisorialSheaf.val.map (homOfLE le_rfl : U ⟶ U).op hψ.invSection)
      have h5 := (congrArg (u.app (Opposite.op U)).hom ha').trans
        ((u.app (Opposite.op U)).hom.map_smul (show X₀.ringCatSheaf.obj.obj (Opposite.op U)
          from a) x)
      have h7 := (γ.hom.val.app (Opposite.op (i ⁻¹ᵁ U))).hom.map_smul (i.app U a)
        ((u.app (Opposite.op U)).hom x)
      refine h1.symm.trans ((congrArg (γ.hom.val.app (Opposite.op (i ⁻¹ᵁ U))).hom
        (h2.symm.trans h5)).trans (h7.trans ?_))
      rw [hia, zero_smul]
      rfl
    apply Subtype.ext
    funext Z
    have hZ : componentGenericPoint _ Z.1 ∈ i ⁻¹ᵁ U := by
      rwa [MMP.Fourfold.componentGenericPoint_eq_genericPoint]
    exact congrArg (fun x : E₀.divisorialSubmodule (i ⁻¹ᵁ U) =>
      (x : ToType ((rationalFunctionsPresheaf _).obj (Opposite.op (i ⁻¹ᵁ U)))) ⟨Z.1, hZ⟩) hres

/-! ### Transfer of rational functions along `φ` -/

/-- On an integral scheme there is a single irreducible component. -/
private theorem irreducibleComponents_subsingleton (X : Scheme.{u}) [IsIntegral X] :
    Subsingleton (irreducibleComponents X) :=
  ⟨fun Z₁ Z₂ => Subtype.ext <| by
    have h₁ := Z₁.2
    have h₂ := Z₂.2
    simp only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at h₁ h₂
    rw [h₁, h₂]⟩

/-- The irreducible component `X` of an integral scheme `X`. -/
private def univComponent (X : Scheme.{u}) [IsIntegral X] : irreducibleComponents X :=
  ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩

/-- The specialization map of stalks along `x ⤳ y` is bijective when `y = x`. -/
public theorem bijective_stalkSpecializes_of_eq {X : Scheme.{u}} {x y : X} (h : x ⤳ y)
    (hxy : y = x) : Function.Bijective (X.presheaf.stalkSpecializes h).hom := by
  subst hxy
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  exact Function.bijective_id

/-- The identification of the factor `𝒪_{X,η_Z}` of the rational functions of an integral
scheme `X` with its function field `K(X)`: `η_Z` is the generic point of `X`, and the map is the
specialization map of stalks. -/
public noncomputable def toFunctionField (X : Scheme.{u}) [IsIntegral X]
    (Z : irreducibleComponents X) :
    X.presheaf.stalk (componentGenericPoint X Z) ≃+* X.functionField :=
  RingEquiv.ofBijective
    (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial :
      genericPoint X ⤳ componentGenericPoint X Z)).hom
    (bijective_stalkSpecializes_of_eq _ (MMP.Fourfold.componentGenericPoint_eq_genericPoint Z))

/-- `toFunctionField` sends the germ of a section at `η_Z` to its germ at the generic point. -/
public theorem toFunctionField_germ (X : Scheme.{u}) [IsIntegral X]
    (Z : irreducibleComponents X) (U : X.Opens) (h : componentGenericPoint X Z ∈ U)
    (h' : genericPoint X ∈ U) (a : Γ(X, U)) :
    toFunctionField X Z (X.presheaf.germ U _ h a) = X.presheaf.germ U (genericPoint X) h' a :=
  TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf h _ a

/-- The value in `K(X)` of a rational function of an integral scheme does not depend on the
component it is read on. -/
public theorem toFunctionField_apply_eq {X : Scheme.{u}} [IsIntegral X] {U : X.Opens}
    (φ : ToType ((rationalFunctionsPresheaf X).obj (Opposite.op U)))
    (Z₁ Z₂ : irreducibleComponents X) (h₁ : componentGenericPoint X Z₁ ∈ U)
    (h₂ : componentGenericPoint X Z₂ ∈ U) :
    toFunctionField X Z₁ (φ ⟨Z₁, h₁⟩) = toFunctionField X Z₂ (φ ⟨Z₂, h₂⟩) := by
  have := irreducibleComponents_subsingleton X
  obtain rfl : Z₁ = Z₂ := Subsingleton.elim _ _
  rfl

/-- The order of vanishing on a fraction field does not depend on the presentation of the
fraction field: it is preserved by `R`-algebra maps between fraction fields of `R`. -/
private theorem ordFrac_algHom {R K K' : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] [Field K] [Field K'] [Algebra R K] [Algebra R K'] [IsFractionRing R K]
    [IsFractionRing R K'] (ψ : K →ₐ[R] K') (x : K) : Ring.ordFrac R (ψ x) = Ring.ordFrac R x := by
  obtain ⟨⟨a, b⟩, hx⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) x
  dsimp only at hx
  subst hx
  have h : ψ (IsLocalization.mk' K a b) = IsLocalization.mk' K' a b := by
    rw [IsLocalization.eq_mk'_iff_mul_eq, ← AlgHom.commutes ψ, ← map_mul,
      IsLocalization.mk'_spec, AlgHom.commutes]
  by_cases ha : a = 0
  · subst ha
    rw [IsLocalization.mk'_zero, map_zero, map_zero, map_zero]
  have ha' : a ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero ha
  rw [h, show (a : R) = (⟨a, ha'⟩ : nonZeroDivisors R).1 from rfl, Ring.ordFrac_eq_div,
    Ring.ordFrac_eq_div]

/-- The valuation of a prime divisor `E` read on the factor `𝒪_{X,η_Z}` of the rational
functions is the inverse of the divisorial valuation `v_E` read on the function field. -/
public theorem valuation_symm_toFunctionField {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (E : Mori.PrimeDivisor X) (f : X.functionField) :
    E.valuation ((toFunctionField X E.component).symm f) = (E.divisorialValuation f)⁻¹ := by
  let := E.toComponent.hom.toAlgebra
  have := isFractionRing_stalkToRationalFunctions E.genericPoint_mem_component
  have : Ring.KrullDimLE 1 E.localRing := krullDimLE_of_coheight_le E.coheight_genericPoint.le
  have := E.isDiscreteValuationRing_localRing
  rw [Mori.PrimeDivisor.divisorialValuation_eq_inv_ordHom, inv_inv]
  change Ring.ordFrac E.localRing (IsLocalization.algEquiv (nonZeroDivisors E.localRing)
      (X.presheaf.stalk (componentGenericPoint X E.component)) (FractionRing E.localRing)
      ((toFunctionField X E.component).symm f)) = Ring.ordFrac E.localRing f
  let ψ : X.presheaf.stalk (componentGenericPoint X E.component) →ₐ[E.localRing]
      X.functionField :=
    { (toFunctionField X E.component).toRingHom with
      commutes' := fun r => by
        change (X.presheaf.stalkSpecializes _).hom ((X.presheaf.stalkSpecializes _).hom r) =
          (X.presheaf.stalkSpecializes _).hom r
        rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp] }
  let e := IsLocalization.algEquiv (nonZeroDivisors E.localRing)
    (X.presheaf.stalk (componentGenericPoint X E.component)) (FractionRing E.localRing)
  have h1 := ordFrac_algHom (R := E.localRing) (ψ.comp e.symm.toAlgHom)
    (e ((toFunctionField X E.component).symm f))
  have h2 : (ψ.comp e.symm.toAlgHom) (e ((toFunctionField X E.component).symm f)) = f := by
    change ψ (e.symm (e _)) = f
    rw [AlgEquiv.symm_apply_apply]
    exact (toFunctionField X E.component).apply_symm_apply f
  rw [h2] at h1
  exact h1.symm

/-- The extension of function fields of a dominant morphism on the germ of a section. -/
private theorem functionFieldMap_germ {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (f : A ⟶ B) [IsDominant f] (U : B.Opens) (hB : genericPoint B ∈ U)
    (hA : genericPoint A ∈ f ⁻¹ᵁ U) (b : Γ(B, U)) :
    functionFieldMap f (B.presheaf.germ U _ hB b) = A.presheaf.germ (f ⁻¹ᵁ U) _ hA (f.app U b) := by
  change (f.stalkMap (genericPoint A)).hom
    ((B.presheaf.stalkCongr _).hom.hom (B.presheaf.germ U _ hB b)) = _
  rw [TopCat.Presheaf.stalkCongr_hom]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  exact Scheme.Hom.germ_stalkMap_apply f U _ hA b

/-- At a point where a dominant morphism induces an isomorphism of local rings, a rational
function of the target is regular exactly when its pull-back is. -/
private theorem functionFieldMap_mem_range_iff {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (f : A ⟶ B) [IsDominant f] (z : A) [IsIso (f.stalkMap z)] (b : B.functionField) :
    functionFieldMap f b ∈ (algebraMap (A.presheaf.stalk z) A.functionField).range ↔
      b ∈ (algebraMap (B.presheaf.stalk (f z)) B.functionField).range := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨d, hd⟩ := (ConcreteCategory.bijective_of_isIso (f.stalkMap z)).2 c
    refine ⟨d, (functionFieldMap f).injective ?_⟩
    rw [MMP.Mori.functionFieldMap_algebraMap_stalk, hd, hc]
  · rintro ⟨d, rfl⟩
    exact ⟨_, (MMP.Mori.functionFieldMap_algebraMap_stalk f z d).symm⟩

private theorem germ_app_congr {A S : Scheme.{u}} {f g : A ⟶ S} (h : f = g) (W : S.Opens)
    (x : A) (hf : x ∈ f ⁻¹ᵁ W) (hg : x ∈ g ⁻¹ᵁ W) (r : Γ(S, W)) :
    A.presheaf.germ _ x hf (f.app W r) = A.presheaf.germ _ x hg (g.app W r) := by
  subst h
  rfl

/-- Two prime divisors whose local rings correspond under an isomorphism of function fields have
corresponding divisorial valuations: both are normalized valuations of discrete valuation
rings, determined by their valuation rings. -/
private theorem divisorialValuation_comap_eq {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (P : Mori.PrimeDivisor X) (Q : Mori.PrimeDivisor Y) (t : X.functionField ≃+* Y.functionField)
    (H : ∀ a, t a ∈ (algebraMap Q.localRing Y.functionField).range ↔
      a ∈ (algebraMap P.localRing X.functionField).range) :
    Q.divisorialValuation.comap t.toRingHom = P.divisorialValuation := by
  have := P.isDiscreteValuationRing_localRing
  have := Q.isDiscreteValuationRing_localRing
  have hle : ∀ a, Q.divisorialValuation (t a) ≤ 1 ↔ P.divisorialValuation a ≤ 1 := fun a => by
    rw [Mori.PrimeDivisor.divisorialValuation_le_one_iff,
      Mori.PrimeDivisor.divisorialValuation_le_one_iff, H]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible P.localRing
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible Q.localRing
  have h1 : ∀ r : P.localRing,
      Q.divisorialValuation (t (algebraMap P.localRing X.functionField r)) ≤ 1 := fun r => by
    rw [hle, Mori.PrimeDivisor.divisorialValuation_le_one_iff]
    exact ⟨r, rfl⟩
  refine MMP.Positivity.DivisorOver.valuation_eq_of_isDiscreteValuationRing (R := P.localRing)
    h1 (fun r hr => ?_) ⟨t.symm (algebraMap Q.localRing Y.functionField ϖ'), ?_⟩
    (fun r => ?_) (fun r hr => ?_) ⟨_, P.divisorialValuation_algebraMap_of_irreducible hϖ⟩
  · change Q.divisorialValuation (t (algebraMap P.localRing X.functionField r)) < 1
    set x := algebraMap P.localRing X.functionField r
    by_contra hlt
    have heq : Q.divisorialValuation (t x) = 1 := le_antisymm (h1 r) (not_lt.1 hlt)
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0, map_zero, map_zero] at heq
      exact zero_ne_one heq
    have hinv : P.divisorialValuation x⁻¹ ≤ 1 := by
      rw [← hle, map_inv₀, map_inv₀, heq, inv_one]
    have hlt' : P.divisorialValuation x < 1 :=
      (Mori.PrimeDivisor.divisorialValuation_algebraMap_lt_one_iff _ r).2 hr
    have hne : P.divisorialValuation x ≠ 0 := (map_ne_zero _).2 hx0
    rw [map_inv₀] at hinv
    have := mul_lt_one_of_lt_of_le hlt' hinv
    rw [mul_inv_cancel₀ hne] at this
    exact lt_irrefl _ this
  · change Q.divisorialValuation (t (t.symm _)) = _
    rw [RingEquiv.apply_symm_apply, Q.divisorialValuation_algebraMap_of_irreducible hϖ']
  · rw [Mori.PrimeDivisor.divisorialValuation_le_one_iff]
    exact ⟨r, rfl⟩
  · exact (Mori.PrimeDivisor.divisorialValuation_algebraMap_lt_one_iff _ r).2 hr

/-- A separated scheme over a field is separated over the terminal scheme. -/
private theorem isSeparated_terminal_of_isSeparated {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsSeparated sX] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
    Limits.terminal.hom_ext _ _]
  infer_instance

/-- A representative of a rational map over `S` commutes with the structure morphisms to `S`
on its whole domain. -/
private theorem hom_comp_eq_of_isOver {X Y S : Scheme.{u}} [IsReduced X]
    [IsSeparated (S ↘ ⊤_ Scheme)] (πX : X ⟶ S) (πY : Y ⟶ S) (g : X.PartialMap Y)
    (hover : MMP.Flips.RationalMap.IsOver πX πY g.toRationalMap) :
    g.hom ≫ πY = g.domain.ι ≫ πX := by
  have h : (g.compHom πY).toRationalMap = πX.toPartialMap.toRationalMap := by
    rwa [Scheme.RationalMap.compHom_toRationalMap]
  exact (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp h)

/-- **The birational contraction at a non-exceptional divisor.** If the transform of a prime
divisor `P` of `X` under the partial isomorphism `e` over `S` is `Q`, then `πX(η_P) = πY(η_Q)`,
and the isomorphism `t : K(X) ≅ K(Y)` induced by `e` identifies `𝒪_{X,P}` with `𝒪_{Y,Q}`: a
representative of `e` defined at `η_P` sends `η_P` to `η_Q` and induces an isomorphism of local
rings there, the local ring at `η_Q` being a valuation ring. -/
private theorem transfer_at_primeDivisor {X Y S : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsSeparated (Y ↘ ⊤_ Scheme)] [IsSeparated (S ↘ ⊤_ Scheme)]
    (πX : X ⟶ S) (πY : Y ⟶ S) (e : X.PartialIso Y)
    (hover : MMP.Flips.RationalMap.IsOver πX πY e.toRationalMap)
    [IsIntegral e.source.toScheme] [IsDominant e.source.ι] [IsDominant (e.iso.hom ≫ e.target.ι)]
    (t : X.functionField ≃+* Y.functionField)
    (ht : ∀ a, functionFieldMap (e.iso.hom ≫ e.target.ι) (t a) = functionFieldMap e.source.ι a)
    (P : Mori.PrimeDivisor X) (Q : Mori.PrimeDivisor Y)
    (h : Mori.RationalMap.transformPrimeDivisor e.toRationalMap P = some Q) :
    πX P.genericPoint = πY Q.genericPoint ∧
      ∀ a, t a ∈ (algebraMap Q.localRing Y.functionField).range ↔
        a ∈ (algebraMap P.localRing X.functionField).range := by
  obtain ⟨g, hgP, hg⟩ := Mori.RationalMap.definedAt_iff.mp
    (Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp h).1
  let x : g.domain.toScheme := ⟨P.genericPoint, hgP⟩
  have hgx : g.hom x = Q.genericPoint :=
    (genericPoint_eq_of_transformPrimeDivisor_eq_some h g hg hgP).symm
  have hgS := hom_comp_eq_of_isOver πX πY g (hg ▸ hover)
  refine ⟨?_, ?_⟩
  · have h1 := congrArg (fun f => f x) hgS
    simp only [Scheme.Hom.comp_apply] at h1
    rw [hgx] at h1
    exact h1.symm
  -- `g` and `e` agree on `W = dom g ∩ source e`
  have hξg : genericPoint X ∈ g.domain :=
    ((genericPoint_spec X).mem_open_set_iff g.domain.isOpen).mpr
      (by simpa using g.dense_domain.nonempty)
  have hξe : genericPoint X ∈ e.source :=
    ((genericPoint_spec X).mem_open_set_iff e.source.isOpen).mpr
      (by simpa using e.dense_source.nonempty)
  let W : X.Opens := g.domain ⊓ e.source
  have hξW : genericPoint X ∈ W := ⟨hξg, hξe⟩
  have : Nonempty g.domain := ⟨x⟩
  have : Nonempty W := ⟨⟨_, hξW⟩⟩
  let a : W.toScheme ⟶ g.domain.toScheme := X.homOfLE inf_le_left
  let b : W.toScheme ⟶ e.source.toScheme := X.homOfLE inf_le_right
  have : IsDominant a := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
  have : IsDominant b := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
  have : IsDominant g.domain.ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
  have : IsDominant (a ≫ g.domain.ι) :=
    MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
  have : IsDominant (b ≫ e.source.ι) :=
    MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
  have : IsDominant (b ≫ e.iso.hom ≫ e.target.ι) :=
    MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
  have hcomp : a ≫ g.hom = b ≫ e.iso.hom ≫ e.target.ι := by
    have h2 := (Scheme.PartialMap.equiv_iff_of_isSeparated (S := ⊤_ Scheme)
      (f := g) (g := e.toPartialMap)).mp
      (Scheme.PartialMap.toRationalMap_eq_iff.mp hg)
    simp only [Scheme.PartialMap.restrict_hom, Scheme.PartialIso.toPartialMap_hom] at h2
    exact h2
  have hcompι : a ≫ g.domain.ι = b ≫ e.source.ι := by
    simp only [a, b, Scheme.homOfLE_ι]
  have : IsDominant (a ≫ g.hom) := by rw [hcomp]; infer_instance
  have : IsDominant g.hom := IsDominant.of_comp a g.hom
  have hgt : ∀ c, functionFieldMap g.hom (t c) = functionFieldMap g.domain.ι c := by
    intro c
    apply (functionFieldMap a).injective
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_congr hcomp,
      ← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply, ht,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_congr hcompι.symm,
      ← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  have hbijι : Function.Bijective (functionFieldMap g.domain.ι) :=
    MMP.Mori.functionFieldMap_bijective_of_isOpenImmersion _ ⊤ ⟨x, trivial⟩
  have hbij : Function.Bijective (functionFieldMap g.hom) := by
    refine ⟨(functionFieldMap g.hom).injective, fun c => ?_⟩
    obtain ⟨c', rfl⟩ := hbijι.2 c
    exact ⟨t c', hgt c'⟩
  have := Q.isDiscreteValuationRing_localRing
  have : ValuationRing (Y.presheaf.stalk (g.hom x)) := by rw [hgx]; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing g.hom hbij x
  intro c
  have h1 := functionFieldMap_mem_range_iff g.hom x (t c)
  have h2 := functionFieldMap_mem_range_iff g.domain.ι x c
  rw [hgt, h2, hgx] at h1
  exact h1.symm

/-- **The transfer of rational functions along `φ`.** The isomorphism `t : K(X⁰) ≅ K(X)` of the
partial isomorphism representing `φ` is `k`-linear, identifies the valuation of a retained prime
`P` with that of `φ_* P`, and sends a function regular at the centre `g(η_Q)` on `X⁰` of a prime
`Q` of `X` (`g` a representative of `ψ` defined at `η_Q`) to a function regular along `Q`. -/
private theorem exists_transfer {k : Type u} [Field k] {X₀ X : Scheme.{u}}
    [IsIntegral X₀] [IsLocallyNoetherian X₀] [IsNormal X₀]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX₀ : X₀ ⟶ Spec (.of k)) (sX : X ⟶ Spec (.of k))
    (hX₀p : Mori.IsProjectiveVariety k sX₀) (hXp : Mori.IsProjectiveVariety k sX)
    (φ : X₀.RationalMap X) (ψ : X.RationalMap X₀) (hψ : Mori.RationalMap.IsInverse φ ψ)
    (hφk : MMP.Flips.RationalMap.IsOver sX₀ sX φ) :
    ∃ t : X₀.functionField ≃+* X.functionField,
      (∀ c : k, t (X₀.presheaf.germ ⊤ (genericPoint X₀) trivial
          (scalarsToGlobalSections k sX₀ c)) =
        X.presheaf.germ ⊤ (genericPoint X) trivial (scalarsToGlobalSections k sX c)) ∧
      (∀ (P : Mori.PrimeDivisor X₀) (Q : Mori.PrimeDivisor X),
        Mori.RationalMap.transformPrimeDivisor φ P = some Q →
          ∀ a, Q.divisorialValuation (t a) = P.divisorialValuation a) ∧
      (∀ (Q : Mori.PrimeDivisor X) (g : X.PartialMap X₀), g.toRationalMap = ψ →
        ∀ (hQ : Q.genericPoint ∈ g.domain) (a : X₀.functionField),
          a ∈ (algebraMap (X₀.presheaf.stalk (g.hom ⟨Q.genericPoint, hQ⟩))
            X₀.functionField).range →
          Q.divisorialValuation (t a) ≤ 1) := by
  have : IsSeparated sX := hXp.toIsSeparated
  have : IsSeparated sX₀ := hX₀p.toIsSeparated
  have := isSeparated_terminal_of_isSeparated sX
  have := isSeparated_terminal_of_isSeparated sX₀
  have : IsSeparated (Spec (.of k) ↘ ⊤_ Scheme) := inferInstance
  obtain ⟨e, rfl, he'⟩ := hψ
  have hξe : genericPoint X₀ ∈ e.source :=
    ((genericPoint_spec X₀).mem_open_set_iff e.source.isOpen).mpr
      (by simpa using e.dense_source.nonempty)
  have : Nonempty e.source := ⟨⟨_, hξe⟩⟩
  have : Nonempty e.target := ⟨e.iso.hom ⟨_, hξe⟩⟩
  have : IsDominant e.source.ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
  have : IsDominant e.target.ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
  have : IsDominant (e.iso.hom ≫ e.target.ι) :=
    MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
  have : IsDominant (e.iso.inv ≫ e.source.ι) :=
    MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
  have : IsIntegral e.source.toScheme := inferInstance
  have : IsIntegral e.target.toScheme := inferInstance
  have bX : Function.Bijective (functionFieldMap e.source.ι) :=
    MMP.Mori.functionFieldMap_bijective_of_isOpenImmersion _ ⊤ ⟨⟨_, hξe⟩, trivial⟩
  have bY : Function.Bijective (functionFieldMap (e.iso.hom ≫ e.target.ι)) :=
    MMP.Mori.functionFieldMap_bijective_of_isOpenImmersion _ ⊤ ⟨⟨_, hξe⟩, trivial⟩
  let t : X₀.functionField ≃+* X.functionField :=
    (RingEquiv.ofBijective _ bX).trans (RingEquiv.ofBijective _ bY).symm
  have ht : ∀ a, functionFieldMap (e.iso.hom ≫ e.target.ι) (t a) =
      functionFieldMap e.source.ι a := fun a =>
    (RingEquiv.ofBijective _ bY).apply_symm_apply _
  have hE : (e.iso.hom ≫ e.target.ι) ≫ sX = e.source.ι ≫ sX₀ :=
    hom_comp_eq_of_isOver sX₀ sX e.toPartialMap hφk
  -- the inverse partial isomorphism
  have ht' : ∀ a, functionFieldMap (e.iso.inv ≫ e.source.ι) a =
      functionFieldMap e.target.ι (t a) := by
    intro a
    have h1 : e.iso.inv ≫ e.iso.hom ≫ e.target.ι = e.target.ι := by simp
    rw [← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply, ← ht,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_congr h1]
  refine ⟨t, fun c => ?_, fun P Q h a => ?_, fun Q g hg hQ a ha => ?_⟩
  · -- `k`-linearity
    have hs : genericPoint e.source ∈ e.source.ι ⁻¹ᵁ (sX₀ ⁻¹ᵁ ⊤) := trivial
    have hs' : genericPoint e.source ∈ (e.iso.hom ≫ e.target.ι) ⁻¹ᵁ (sX ⁻¹ᵁ ⊤) := trivial
    apply (functionFieldMap (e.iso.hom ≫ e.target.ι)).injective
    rw [ht]
    have h1 := functionFieldMap_germ e.source.ι (sX₀ ⁻¹ᵁ ⊤) trivial hs
      (sX₀.app ⊤ ((Scheme.ΓSpecIso (.of k)).inv c))
    have h2 := functionFieldMap_germ (e.iso.hom ≫ e.target.ι) (sX ⁻¹ᵁ ⊤) trivial hs'
      (sX.app ⊤ ((Scheme.ΓSpecIso (.of k)).inv c))
    refine h1.trans (Eq.trans ?_ h2.symm)
    have e1 : e.source.ι.app (sX₀ ⁻¹ᵁ ⊤) (sX₀.app ⊤ ((Scheme.ΓSpecIso (.of k)).inv c)) =
        (e.source.ι ≫ sX₀).app ⊤ ((Scheme.ΓSpecIso (.of k)).inv c) := by
      rw [Scheme.Hom.comp_app]; rfl
    have e2 : (e.iso.hom ≫ e.target.ι).app (sX ⁻¹ᵁ ⊤)
        (sX.app ⊤ ((Scheme.ΓSpecIso (.of k)).inv c)) =
        ((e.iso.hom ≫ e.target.ι) ≫ sX).app ⊤ ((Scheme.ΓSpecIso (.of k)).inv c) := by
      rw [Scheme.Hom.comp_app (e.iso.hom ≫ e.target.ι) sX]; rfl
    rw [e1, e2]
    exact germ_app_congr hE.symm ⊤ _ _ _ _
  · -- retained primes
    have hR := (transfer_at_primeDivisor sX₀ sX e hφk t ht P Q h).2
    have hcomap := divisorialValuation_comap_eq P Q t hR
    rw [← hcomap]; rfl
  · -- extracted primes: `g` agrees with `e⁻¹` on a dense open
    let x : g.domain.toScheme := ⟨Q.genericPoint, hQ⟩
    have hξg : genericPoint X ∈ g.domain :=
      ((genericPoint_spec X).mem_open_set_iff g.domain.isOpen).mpr
        (by simpa using g.dense_domain.nonempty)
    have hξe' : genericPoint X ∈ e.target :=
      ((genericPoint_spec X).mem_open_set_iff e.target.isOpen).mpr
        (by simpa using e.dense_target.nonempty)
    let W : X.Opens := g.domain ⊓ e.target
    have hξW : genericPoint X ∈ W := ⟨hξg, hξe'⟩
    have : Nonempty g.domain := ⟨x⟩
    have : Nonempty W := ⟨⟨_, hξW⟩⟩
    let a' : W.toScheme ⟶ g.domain.toScheme := X.homOfLE inf_le_left
    let b' : W.toScheme ⟶ e.target.toScheme := X.homOfLE inf_le_right
    have : IsDominant a' := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
    have : IsDominant b' := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
    have : IsDominant g.domain.ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
    have : IsDominant (a' ≫ g.domain.ι) :=
      MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
    have : IsDominant (b' ≫ e.target.ι) :=
      MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
    have : IsDominant (b' ≫ e.iso.inv ≫ e.source.ι) :=
      MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
    have hcomp : a' ≫ g.hom = b' ≫ e.iso.inv ≫ e.source.ι := by
      have h2 := (Scheme.PartialMap.equiv_iff_of_isSeparated (S := ⊤_ Scheme)
        (f := g) (g := e.symm.toPartialMap)).mp
        (Scheme.PartialMap.toRationalMap_eq_iff.mp (hg.trans he'.symm))
      simp only [Scheme.PartialMap.restrict_hom, Scheme.PartialIso.toPartialMap_hom,
        Scheme.PartialIso.symm_iso, Iso.symm_hom] at h2
      exact h2
    have hcompι : a' ≫ g.domain.ι = b' ≫ e.target.ι := by
      simp only [a', b', Scheme.homOfLE_ι]
    have : IsDominant (a' ≫ g.hom) := by rw [hcomp]; infer_instance
    have : IsDominant g.hom := IsDominant.of_comp a' g.hom
    have hgt : ∀ c, functionFieldMap g.hom c = functionFieldMap g.domain.ι (t c) := by
      intro c
      apply (functionFieldMap a').injective
      rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
        MMP.Positivity.DivisorOver.functionFieldMap_congr hcomp,
        ← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply, ht',
        MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
        MMP.Positivity.DivisorOver.functionFieldMap_congr hcompι.symm,
        ← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
    obtain ⟨r, rfl⟩ := ha
    have h1 := MMP.Mori.functionFieldMap_algebraMap_stalk g.hom x r
    rw [hgt] at h1
    have h2 : functionFieldMap g.domain.ι (t (algebraMap _ X₀.functionField r)) ∈
        (algebraMap (g.domain.toScheme.presheaf.stalk x) g.domain.toScheme.functionField).range :=
      ⟨_, h1.symm⟩
    rw [functionFieldMap_mem_range_iff g.domain.ι x] at h2
    rwa [Mori.PrimeDivisor.divisorialValuation_le_one_iff]

/-- The linear extension of a partial map on prime divisors has coefficient zero at a prime
divisor outside its image. -/
private theorem mapPrimeDivisors_apply_eq_zero_of_forall_ne {X Y : Scheme.{u}} {R : Type*}
    [AddCommMonoid R] {φ : Mori.PrimeDivisor X → Option (Mori.PrimeDivisor Y)}
    {P : Mori.PrimeDivisor Y} (h : ∀ E, φ E ≠ some P) (D : DivisorWithCoeffs R X) :
    DivisorWithCoeffs.mapPrimeDivisors φ D P = 0 := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' hD hD' => rw [map_add, Finsupp.add_apply, hD, hD', add_zero]
  | single E r =>
    rw [DivisorWithCoeffs.mapPrimeDivisors_single]
    rcases hE : φ E with _ | E'
    · rfl
    · have hne : E' ≠ P := fun he => h E (by rw [hE, he])
      exact Finsupp.single_eq_of_ne' hne

/-- **The transform of sections.** A section `f` of `𝒪_{X⁰}(D)`, read as a rational function `F`,
transforms to the section `t F` of `𝒪_X(φ_* D)`: along `Q = φ_* P` the valuations agree and so do
the coefficients; along a prime `Q` extracted by `φ`, the coefficient is zero and `F` is regular at
the centre of `Q` on `X⁰` (which lies outside `Supp A⁰ ⊇ Supp D`, Hartogs), so `t F` is regular
along `Q`. -/
private theorem exists_transform_sections {k : Type u} [Field k] {X₀ X : Scheme.{u}}
    [IsIntegral X₀] [IsLocallyNoetherian X₀] [IsNormal X₀] [Scheme.IsSeparated X₀]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [Scheme.IsSeparated X]
    (sX₀ : X₀ ⟶ Spec (.of k)) (sX : X ⟶ Spec (.of k)) [IsProper sX₀]
    (A₀ : QDivisor X₀) (D : Divisor X₀) (hDA : D.supp ≤ A₀.supp)
    (φ : X₀.RationalMap X) (ψ : X.RationalMap X₀) (hψ : Mori.RationalMap.IsInverse φ ψ)
    (hψk : MMP.Flips.RationalMap.IsOver sX sX₀ ψ)
    (hord : ∀ F : Mori.PrimeDivisor X, MMP.Flips.RationalMap.IsInverseExceptional φ F →
      ∀ g : X.PartialMap X₀, g.toRationalMap = ψ → ∀ hF : F.genericPoint ∈ g.domain,
        g.hom ⟨F.genericPoint, hF⟩ ∉ (A₀.supp : Set X₀))
    (t : X₀.functionField ≃+* X.functionField)
    (ht1 : ∀ c : k, t (X₀.presheaf.germ ⊤ (genericPoint X₀) trivial
          (scalarsToGlobalSections k sX₀ c)) =
        X.presheaf.germ ⊤ (genericPoint X) trivial (scalarsToGlobalSections k sX c))
    (ht2 : ∀ (P : Mori.PrimeDivisor X₀) (Q : Mori.PrimeDivisor X),
        Mori.RationalMap.transformPrimeDivisor φ P = some Q →
          ∀ a, Q.divisorialValuation (t a) = P.divisorialValuation a)
    (ht3 : ∀ (Q : Mori.PrimeDivisor X) (g : X.PartialMap X₀), g.toRationalMap = ψ →
        ∀ (hQ : Q.genericPoint ∈ g.domain) (a : X₀.functionField),
          a ∈ (algebraMap (X₀.presheaf.stalk (g.hom ⟨Q.genericPoint, hQ⟩))
            X₀.functionField).range →
          Q.divisorialValuation (t a) ≤ 1) :
    letI : Module k (D.divisorialSubmodule ⊤) := Module.compHom _ (scalarsToGlobalSections k sX₀)
    letI : Module k (Divisor.divisorialSubmodule (Mori.RationalMap.transformDivisor φ D) ⊤) :=
      Module.compHom _ (scalarsToGlobalSections k sX)
    ∃ T : D.divisorialSubmodule ⊤ →ₗ[k]
        Divisor.divisorialSubmodule (Mori.RationalMap.transformDivisor φ D) ⊤,
      ∀ f : D.divisorialSubmodule ⊤,
        toFunctionField X (univComponent X)
          ((T f : ToType ((rationalFunctionsPresheaf X).obj (Opposite.op ⊤)))
            ⟨univComponent X, trivial⟩) =
        t (toFunctionField X₀ (univComponent X₀)
          ((f : ToType ((rationalFunctionsPresheaf X₀).obj (Opposite.op ⊤)))
            ⟨univComponent X₀, trivial⟩)) := by
  set Z₀ := univComponent X₀
  let F : D.divisorialSubmodule ⊤ → X₀.functionField := fun f =>
    toFunctionField X₀ Z₀ ((f : ToType ((rationalFunctionsPresheaf X₀).obj (Opposite.op ⊤)))
      ⟨Z₀, trivial⟩)
  have hfP : ∀ (f : D.divisorialSubmodule ⊤) (P : Mori.PrimeDivisor X₀),
      P.OrdGE (-D.coeff P) ((toFunctionField X₀ P.component).symm (F f)) := by
    intro f P
    have hP : (P.support ∩ (⊤ : X₀.Opens)).Nonempty := ⟨P.genericPoint, by
      change P.genericPoint ∈ P.support
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl, trivial⟩
    have := f.2 P hP
    simp only [F]
    rw [toFunctionField_apply_eq (f : ToType ((rationalFunctionsPresheaf X₀).obj (Opposite.op ⊤)))
      Z₀ P.component trivial trivial, RingEquiv.symm_apply_apply]
    exact this
  have hmem : ∀ f : D.divisorialSubmodule ⊤,
      Divisor.IsDivisorialSection (Mori.RationalMap.transformDivisor φ D) ⊤
        (fun Z => (toFunctionField X Z.1).symm (t (F f))) := by
    intro f Q _
    by_cases hex : ∃ P, Mori.RationalMap.transformPrimeDivisor φ P = some Q
    · obtain ⟨P, hPQ⟩ := hex
      have hcoeff : DivisorWithCoeffs.coeff (Mori.RationalMap.transformDivisor φ D) Q = D.coeff P :=
        MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hPQ
          (fun P' hP' => eq_of_transformPrimeDivisor_eq_some hψ hP' hPQ) D
      change Q.OrdGE _ ((toFunctionField X Q.component).symm (t (F f)))
      rw [hcoeff]
      rcases hfP f P with h0 | hle
      · left
        have hf : F f = 0 :=
          (toFunctionField X₀ P.component).symm.injective (h0.trans (map_zero _).symm)
        rw [hf, map_zero, map_zero]
      · right
        rw [valuation_symm_toFunctionField] at hle ⊢
        rwa [ht2 P Q hPQ]
    · push Not at hex
      have hcoeff : DivisorWithCoeffs.coeff (Mori.RationalMap.transformDivisor φ D) Q = 0 :=
        mapPrimeDivisors_apply_eq_zero_of_forall_ne hex D
      change Q.OrdGE _ ((toFunctionField X Q.component).symm (t (F f)))
      rw [hcoeff, neg_zero]
      by_cases hF0 : F f = 0
      · left; rw [hF0, map_zero, map_zero]
      right
      have htF0 : t (F f) ≠ 0 := fun h => hF0 (t.injective (h.trans (map_zero t).symm))
      have hvpos : 0 < Q.divisorialValuation (t (F f)) := by
        rw [zero_lt_iff]; exact (map_ne_zero _).mpr htF0
      rw [valuation_symm_toFunctionField, WithZero.exp_zero, one_le_inv₀ hvpos]
      have hdom : Q.genericPoint ∈ ψ.domain :=
        MMP.Flips.RationalMap.mem_domain_of_coheight_le_one sX sX₀ ψ hψk Q.coheight_genericPoint.le
      obtain ⟨g, hQg, hg⟩ := Scheme.RationalMap.mem_domain.mp hdom
      have hc := hord Q (fun P hP => hex P hP) g hg hQg
      refine ht3 Q g hg hQg (F f) ?_
      suffices hreg : ∀ Γ : Mori.PrimeDivisor X₀, g.hom ⟨Q.genericPoint, hQg⟩ ∈ Γ.support →
          0 ≤ X₀.ord (F f) Γ.genericPoint by
        obtain ⟨r, hr⟩ := MMP.Threefold.Bridges.exists_algebraMap_stalk_eq_of_forall_zero_le_ord
          _ hF0 hreg
        exact ⟨r, hr⟩
      intro Γ hΓ
      have hΓ0 : D.coeff Γ = 0 := by
        by_contra hne
        exact hc (hDA (DivisorWithCoeffs.mem_supp_iff.mpr ⟨Γ, hne, hΓ⟩))
      rcases hfP f Γ with h0 | hle
      · exact absurd ((toFunctionField X₀ Γ.component).symm.injective
          (h0.trans (map_zero _).symm)) hF0
      · have hvpos' : 0 < Γ.divisorialValuation (F f) := by
          rw [zero_lt_iff]; exact (map_ne_zero _).mpr hF0
        rw [hΓ0, neg_zero, valuation_symm_toFunctionField, WithZero.exp_zero,
          one_le_inv₀ hvpos', Γ.divisorialValuation_eq_exp_neg_ord hF0, ← WithZero.exp_zero,
          WithZero.exp_le_exp] at hle
        linarith
  letI : Module k (D.divisorialSubmodule ⊤) := Module.compHom _ (scalarsToGlobalSections k sX₀)
  letI : Module k (Divisor.divisorialSubmodule (Mori.RationalMap.transformDivisor φ D) ⊤) :=
    Module.compHom _ (scalarsToGlobalSections k sX)
  refine ⟨{ toFun := fun f => ⟨fun Z => (toFunctionField X Z.1).symm (t (F f)), hmem f⟩
            map_add' := fun f f' => Subtype.ext (funext fun Z => by
              change (toFunctionField X Z.1).symm (t (toFunctionField X₀ Z₀
                ((f : ToType ((rationalFunctionsPresheaf X₀).obj (Opposite.op ⊤))) ⟨Z₀, trivial⟩ +
                  (f' : ToType ((rationalFunctionsPresheaf X₀).obj (Opposite.op ⊤)))
                    ⟨Z₀, trivial⟩))) =
                (toFunctionField X Z.1).symm (t (F f)) + (toFunctionField X Z.1).symm (t (F f'))
              rw [map_add, map_add, map_add])
            map_smul' := fun c f => Subtype.ext (funext fun Z => by
              change (toFunctionField X Z.1).symm (t (toFunctionField X₀ Z₀
                (X₀.presheaf.germ ⊤ _ trivial (scalarsToGlobalSections k sX₀ c) *
                  (f : ToType ((rationalFunctionsPresheaf X₀).obj (Opposite.op ⊤)))
                    ⟨Z₀, trivial⟩))) =
                X.presheaf.germ ⊤ _ trivial (scalarsToGlobalSections k sX c) *
                  (toFunctionField X Z.1).symm (t (F f))
              rw [map_mul, map_mul, toFunctionField_germ X₀ Z₀ ⊤ trivial trivial, ht1, map_mul]
              congr 1
              rw [RingEquiv.symm_apply_eq, toFunctionField_germ X Z.1 ⊤ trivial trivial]) },
    fun f => ?_⟩
  change toFunctionField X (univComponent X) ((toFunctionField X (univComponent X)).symm
    (t (F f))) = _
  rw [RingEquiv.apply_symm_apply]

/-- A non-unit of the local ring `𝒪_{X,S}` vanishes along `S`. -/
private theorem ordGE_one_toComponent_of_not_isUnit {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] (S : Mori.PrimeDivisor X) {b : S.localRing} (hb : ¬ IsUnit b) :
    S.OrdGE 1 (S.toComponent.hom b) := by
  by_cases hb0 : b = 0
  · left; rw [hb0, map_zero]
  right
  have := S.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S.localRing
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hn : n ≠ 0 := by
    rintro rfl
    exact hb (by simp)
  rw [map_mul, map_mul, map_pow, map_pow, S.valuation_toComponent_of_isUnit v.isUnit,
    S.valuation_toComponent_of_irreducible hϖ, one_mul, ← WithZero.exp_nsmul, WithZero.exp_le_exp,
    nsmul_eq_mul, mul_one]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn

/-- **Restriction to `S` detects vanishing along `S`.** For a Cartier divisor `G` on `X` with
`S ⊄ Supp G` and `E = G|_S`, the restriction `H⁰(X, 𝒪(G)) → H⁰(S, 𝒪(E))`, read through
`𝒪_S(E) ≅ i^* 𝒪_X(G)`, is `k`-linear and kills only sections vanishing along `S`: near `η_S` a
section is `a ψ⁻¹` with `ψ⁻¹` a generator, whose pull-back is a generator of `i^* 𝒪_X(G)`, so the
restriction vanishes only if `a` vanishes on `S`. -/
private theorem exists_restriction_sections {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (sX : X ⟶ Spec (.of k)) (S : Mori.PrimeDivisor X) [IsNormal S.idealSheaf.subscheme]
    (G : Divisor X) (hG : G.IsCartier) (hGS : G.coeff S = 0) :
    haveI := S.integral
    haveI := S.idealSheaf.isLocallyNoetherian_subscheme
    ∀ (hB : ∀ Z : irreducibleComponents S.idealSheaf.subscheme,
          S.idealSheaf.subschemeι (componentGenericPoint _ Z) ∉ G.supp)
      (E : Divisor S.idealSheaf.subscheme), G.IsPullback S.idealSheaf.subschemeι hB E →
      letI : Module k (G.divisorialSubmodule ⊤) := Module.compHom _ (scalarsToGlobalSections k sX)
      letI : Module k (E.divisorialSubmodule ⊤) :=
        Module.compHom _ (scalarsToGlobalSections k (S.idealSheaf.subschemeι ≫ sX))
      ∃ R : G.divisorialSubmodule ⊤ →ₗ[k] E.divisorialSubmodule ⊤,
        ∀ g : G.divisorialSubmodule ⊤, R g = 0 →
          S.OrdGE 1 ((g : ToType ((rationalFunctionsPresheaf X).obj (Opposite.op ⊤)))
            ⟨S.component, trivial⟩) := by
  haveI := S.integral
  haveI := S.idealSheaf.isLocallyNoetherian_subscheme
  haveI : CompactSpace S.idealSheaf.subscheme :=
    S.idealSheaf.subschemeι.isClosedEmbedding.compactSpace
  haveI := hG.isInvertibleModule_divisorialSheaf
  intro hB E hE
  set i := S.idealSheaf.subschemeι with hi
  let γ := (Adjunction.leftAdjointUniq
      (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction i.toLRSHom.toShHom)
      (Scheme.Modules.pullbackPushforwardAdjunction i)).app G.divisorialSheaf ≪≫
    (Divisor.IsPullback.divisorialSheafIso (hBc := hG) hE).symm
  let u := ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
    i.toLRSHom.toShHom).unit.app G.divisorialSheaf).val
  let ρ₀ : G.divisorialSubmodule ⊤ → E.divisorialSubmodule ⊤ :=
    fun f => (γ.hom.val.app (Opposite.op ⊤)).hom ((u.app (Opposite.op ⊤)).hom f)
  have hρ₀ : ∀ (r : Γ(X, ⊤)) (f : G.divisorialSubmodule ⊤),
      ρ₀ (r • f) = (i.appTop r) • ρ₀ f := by
    intro r f
    have h1 := (u.app (Opposite.op ⊤)).hom.map_smul (show X.ringCatSheaf.obj.obj (Opposite.op ⊤)
      from r) (show G.divisorialSheaf.val.obj (Opposite.op ⊤) from f)
    have h2 := (γ.hom.val.app (Opposite.op ⊤)).hom.map_smul (i.appTop r)
      ((u.app (Opposite.op ⊤)).hom f)
    exact (congrArg (γ.hom.val.app (Opposite.op ⊤)).hom h1).trans h2
  letI : Module k (G.divisorialSubmodule ⊤) := Module.compHom _ (scalarsToGlobalSections k sX)
  letI : Module k (E.divisorialSubmodule ⊤) :=
    Module.compHom _ (scalarsToGlobalSections k (i ≫ sX))
  refine ⟨{ toFun := ρ₀
            map_add' := fun f g =>
              (congrArg (γ.hom.val.app (Opposite.op ⊤)).hom
                ((u.app (Opposite.op ⊤)).hom.map_add f g)).trans
                ((γ.hom.val.app (Opposite.op ⊤)).hom.map_add _ _)
            map_smul' := fun c f => by
              change ρ₀ (scalarsToGlobalSections k sX c • f) =
                scalarsToGlobalSections k (i ≫ sX) c • ρ₀ f
              rw [hρ₀]
              congr 1 }, fun g hg => ?_⟩
  change ρ₀ g = 0 at hg
  obtain ⟨U, hU, ψ, hψ⟩ := hG S.genericPoint
  have hSU : (S.support ∩ U).Nonempty := ⟨S.genericPoint, by
    change S.genericPoint ∈ S.support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl, hU⟩
  have hψS : S.ord ψ = 0 := by rw [← hψ S hSU, hGS]
  have hmem : componentGenericPoint X S.component ∈ U := S.componentGenericPoint_mem_of_nonempty hSU
  obtain ⟨a, ha⟩ := (hψ.isLocalGenerator_invSection U le_rfl).2
    (G.divisorialSheaf.presheaf.map (homOfLE le_top).op g)
  have hga : (g : ToType ((rationalFunctionsPresheaf X).obj (Opposite.op ⊤)))
      ⟨S.component, trivial⟩ = X.presheaf.germ U _ hmem a *
        ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) S.component := by
    have := congrArg (fun φ : G.divisorialSubmodule U =>
      (φ : ToType ((rationalFunctionsPresheaf X).obj (Opposite.op U))) ⟨S.component, hmem⟩) ha
    exact this.symm
  set b := X.presheaf.germ U S.genericPoint hU a with hb
  have hbc : S.toComponent.hom b = X.presheaf.germ U _ hmem a :=
    TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hU _ a
  rw [hga, ← hbc]
  have hψv : S.OrdGE 0 (((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) S.component) :=
    Or.inr (by rw [PrimeDivisor.valuation_component, PrimeDivisor.ord_inv, hψS, neg_zero])
  have := (ordGE_one_toComponent_of_not_isUnit S (b := b) ?_).mul hψv
  · simpa using this
  -- `b` is not a unit: otherwise the restriction of `g` is a unit times a generator
  intro hbu
  set η' := genericPoint S.idealSheaf.subscheme
  have hiη : i η' = S.genericPoint := subschemeι_genericPoint_eq S
  have hη'U : η' ∈ i ⁻¹ᵁ U := by change i η' ∈ U; rwa [hiη]
  have hu' : ∀ (y : X) (hy : y = S.genericPoint) (hyU : y ∈ U),
      IsUnit (X.presheaf.germ U y hyU a) := by
    rintro _ rfl hyU; exact hbu
  have hia : i.app U a ≠ 0 := by
    intro h0
    have h1 := Scheme.Hom.germ_stalkMap_apply i U η' (by rwa [hiη]) a
    rw [h0, map_zero] at h1
    have h2 := (hu' (i η') hiη (by rwa [hiη])).map (i.stalkMap η').hom
    rw [h1] at h2
    exact not_isUnit_zero h2
  apply hia
  -- the pulled-back generator
  have hgen := (Stacks.SheafOfModules.pullbackGenerator i G.divisorialSheaf inferInstance U
    ⟨hψ.invSection, fun V hV => hψ.isLocalGenerator_invSection V hV⟩).2 (i ⁻¹ᵁ U) le_rfl
  -- the restriction of `ρ₀ g` to `i⁻¹ U` is `i^♯ a` times the pulled-back generator
  have h1 := PresheafOfModules.naturality_apply γ.hom.val
    (homOfLE le_top : i ⁻¹ᵁ U ⟶ ⊤).op ((u.app (Opposite.op ⊤)).hom g)
  have h2 := PresheafOfModules.naturality_apply u (homOfLE le_top : U ⟶ ⊤).op g
  have ha' : (show G.divisorialSubmodule U from
      G.divisorialSheaf.val.map (homOfLE le_top : U ⟶ ⊤).op g) =
      a • (show G.divisorialSubmodule U from
        G.divisorialSheaf.val.map (homOfLE le_rfl : U ⟶ U).op hψ.invSection) := ha.symm
  set x := (show G.divisorialSheaf.val.obj (Opposite.op U) from
    G.divisorialSheaf.val.map (homOfLE le_rfl : U ⟶ U).op hψ.invSection)
  have h5 := (congrArg (u.app (Opposite.op U)).hom ha').trans
    ((u.app (Opposite.op U)).hom.map_smul (show X.ringCatSheaf.obj.obj (Opposite.op U)
      from a) x)
  have h7 := (γ.hom.val.app (Opposite.op (i ⁻¹ᵁ U))).hom.map_smul (i.app U a)
    ((u.app (Opposite.op U)).hom x)
  have hres := h1.symm.trans ((congrArg (γ.hom.val.app (Opposite.op (i ⁻¹ᵁ U))).hom
    (h2.symm.trans h5)).trans h7)
  change E.divisorialSheaf.val.map (homOfLE le_top : i ⁻¹ᵁ U ⟶ ⊤).op (ρ₀ g) = _ at hres
  rw [hg] at hres
  have hres' := hres.symm.trans (map_zero _)
  have hinj : Function.Injective (γ.hom.val.app (Opposite.op (i ⁻¹ᵁ U))).hom := by
    intro y y' hyy
    have e1 := congrArg (fun φ => (φ.val.app (Opposite.op (i ⁻¹ᵁ U))).hom y) γ.hom_inv_id
    have e2 := congrArg (fun φ => (φ.val.app (Opposite.op (i ⁻¹ᵁ U))).hom y') γ.hom_inv_id
    exact e1.symm.trans ((congrArg (γ.inv.val.app (Opposite.op (i ⁻¹ᵁ U))).hom hyy).trans e2)
  have h8 := hinj (h7.trans (hres'.trans (map_zero _).symm))
  apply hgen.1
  refine Eq.trans ?_ (zero_smul _ _).symm
  refine Eq.trans ?_ h8
  beta_reduce
  congr 1
  exact (PresheafOfModules.naturality_apply u (homOfLE le_rfl : U ⟶ U).op hψ.invSection).symm

/-- **Transform and restriction of sections.** A section `f` of `𝒪_{X⁰}(D)`, `D = qD₁`, read as a
rational function, transforms along `φ` to a section of `𝒪_X(φ_* D)` (each prime of `X` comes
from a prime of `X⁰`, with the same valuation, or is extracted with centre outside `Supp A⁰`, where
`f` is regular), and its residue at `η_S` is a section of `𝒪_S((φ_* D)|_S)`; the residue vanishes
only if `f` vanishes along `S⁰`, `φ` identifying `𝒪_{X⁰,S⁰}` with `𝒪_{X,S}`. -/
private theorem exists_transform_restriction {k : Type u} [Field k]
    {X₀ X : Scheme.{u}}
    [IsIntegral X₀] [IsLocallyNoetherian X₀] [IsNormal X₀] [CompactSpace X₀]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX₀ : X₀ ⟶ Spec (.of k)) (sX : X ⟶ Spec (.of k))
    (hX₀ : IsNormalVariety k sX₀) (hX₀p : Mori.IsProjectiveVariety k sX₀)
    (hXp : Mori.IsProjectiveVariety k sX)
    (S₀ : Mori.PrimeDivisor X₀) (A₀ : QDivisor X₀) (D : Divisor X₀) (hDA : D.supp ≤ A₀.supp)
    (hDS : D.coeff S₀ = 0)
    (φ : X₀.RationalMap X) (ψ : X.RationalMap X₀) (hψ : Mori.RationalMap.IsInverse φ ψ)
    (hφk : MMP.Flips.RationalMap.IsOver sX₀ sX φ) (hψk : MMP.Flips.RationalMap.IsOver sX sX₀ ψ)
    (S : Mori.PrimeDivisor X) [IsNormal S.idealSheaf.subscheme]
    (hS : Mori.RationalMap.transformPrimeDivisor φ S₀ = some S)
    (hord : ∀ F : Mori.PrimeDivisor X, MMP.Flips.RationalMap.IsInverseExceptional φ F →
      ∀ g : X.PartialMap X₀, g.toRationalMap = ψ → ∀ hF : F.genericPoint ∈ g.domain,
        g.hom ⟨F.genericPoint, hF⟩ ∉ (A₀.supp : Set X₀))
    (hC : Divisor.IsCartier (Mori.RationalMap.transformDivisor φ D)) :
    haveI := S.integral
    haveI := S.idealSheaf.isLocallyNoetherian_subscheme
    ∀ (hB : ∀ Z : irreducibleComponents S.idealSheaf.subscheme,
          S.idealSheaf.subschemeι (componentGenericPoint _ Z) ∉
            (Mori.RationalMap.transformDivisor φ D).supp)
        (E : Divisor S.idealSheaf.subscheme),
        Divisor.IsPullback S.idealSheaf.subschemeι (Mori.RationalMap.transformDivisor φ D) hB E →
        letI : Module k (D.divisorialSubmodule ⊤) :=
          Module.compHom _ (scalarsToGlobalSections k sX₀)
        letI : Module k (E.divisorialSubmodule ⊤) :=
          Module.compHom _ (scalarsToGlobalSections k (S.idealSheaf.subschemeι ≫ sX))
        ∃ Φ : D.divisorialSubmodule ⊤ →ₗ[k] E.divisorialSubmodule ⊤,
          ∀ f : D.divisorialSubmodule ⊤, Φ f = 0 →
            S₀.OrdGE 1 ((f : ToType ((rationalFunctionsPresheaf X₀).obj (Opposite.op ⊤)))
              ⟨S₀.component, trivial⟩) := by
  haveI := S.integral
  haveI := S.idealSheaf.isLocallyNoetherian_subscheme
  intro hB E hE
  haveI : IsProper sX₀ := isProper_of_isProjectiveMorphism sX₀ hX₀p.isProjective
  haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hXp.isProjective
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : Scheme.IsSeparated X₀ := ⟨isSeparated_terminal_of_isSeparated sX₀⟩
  haveI : Scheme.IsSeparated X := ⟨isSeparated_terminal_of_isSeparated sX⟩
  obtain ⟨t, ht1, ht2, ht3⟩ := exists_transfer sX₀ sX hX₀p hXp φ ψ hψ hφk
  obtain ⟨T, hT⟩ := exists_transform_sections sX₀ sX A₀ D hDA φ ψ hψ hψk hord t ht1 ht2 ht3
  have hGS : DivisorWithCoeffs.coeff (Mori.RationalMap.transformDivisor φ D) S = 0 := by
    change DivisorWithCoeffs.mapPrimeDivisors _ D S = 0
    rwa [MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hS
      (fun P hP => eq_of_transformPrimeDivisor_eq_some hψ hP hS) D]
  obtain ⟨R, hR⟩ := exists_restriction_sections sX S _ hC hGS hB E hE
  refine ⟨R.comp T, fun f hf => ?_⟩
  have h1 := hR (T f) hf
  set F := toFunctionField X₀ (univComponent X₀)
    ((f : ToType ((rationalFunctionsPresheaf X₀).obj (Opposite.op ⊤)))
      ⟨univComponent X₀, trivial⟩) with hF
  have e1 : ((T f : ToType ((rationalFunctionsPresheaf X).obj (Opposite.op ⊤)))
      ⟨S.component, trivial⟩) = (toFunctionField X S.component).symm (t F) := by
    rw [RingEquiv.eq_symm_apply, toFunctionField_apply_eq
      (T f : ToType ((rationalFunctionsPresheaf X).obj (Opposite.op ⊤))) S.component
      (univComponent X) trivial trivial, hT f]
  have e0 : ((f : ToType ((rationalFunctionsPresheaf X₀).obj (Opposite.op ⊤)))
      ⟨S₀.component, trivial⟩) = (toFunctionField X₀ S₀.component).symm F := by
    rw [RingEquiv.eq_symm_apply, toFunctionField_apply_eq
      (f : ToType ((rationalFunctionsPresheaf X₀).obj (Opposite.op ⊤))) S₀.component
      (univComponent X₀) trivial trivial]
  rw [e1] at h1
  rw [e0]
  rcases h1 with h0 | h1
  · left
    have htF : t F = 0 := (toFunctionField X S.component).symm.injective
      (h0.trans (map_zero _).symm)
    have hF0 : F = 0 := t.injective (htF.trans (map_zero t).symm)
    rw [hF0, map_zero]
  · right
    rw [valuation_symm_toFunctionField] at h1 ⊢
    rwa [ht2 S₀ S hS] at h1

/-- **The comparison of sections.** For `q ≫ 0`, `h⁰(S⁰, qD₁|_{S⁰}) ≤ h⁰(S, (φ_* qD₁)|_S)`: Serre
vanishing lifts every section on `S⁰` to `X⁰`, its transform is a section on `X` (each prime of
`X` comes from a prime of `X⁰`, or is extracted with centre outside `Supp A⁰`), and restriction at
the generic point of `S`, where `φ` identifies the residue fields of `S⁰` and `S`, is injective on
the restrictions to `S⁰`. -/
private theorem sectionsFinrank_le_of_isPullback {k : Type u} [Field k]
    {X₀ X : Scheme.{u}}
    [IsIntegral X₀] [IsLocallyNoetherian X₀] [IsNormal X₀] [CompactSpace X₀]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX₀ : X₀ ⟶ Spec (.of k)) (sX : X ⟶ Spec (.of k))
    (hX₀ : IsNormalVariety k sX₀) (hX₀p : Mori.IsProjectiveVariety k sX₀)
    (hXQ : IsQFactorial sX) (hXp : Mori.IsProjectiveVariety k sX)
    (S₀ : Mori.PrimeDivisor X₀) [IsNormal S₀.idealSheaf.subscheme]
    (A₀ : QDivisor X₀) (D₁ : Divisor X₀) (hD₁ : D₁.IsCartier) (hamp : D₁.IsAmple hD₁)
    (hD₁A : D₁.supp ≤ A₀.supp) (hD₁S : D₁.coeff S₀ = 0)
    (φ : X₀.RationalMap X) (ψ : X.RationalMap X₀) (hψ : Mori.RationalMap.IsInverse φ ψ)
    (hφk : MMP.Flips.RationalMap.IsOver sX₀ sX φ) (hψk : MMP.Flips.RationalMap.IsOver sX sX₀ ψ)
    (S : Mori.PrimeDivisor X) [IsNormal S.idealSheaf.subscheme]
    (hS : Mori.RationalMap.transformPrimeDivisor φ S₀ = some S)
    (hord : ∀ F : Mori.PrimeDivisor X, MMP.Flips.RationalMap.IsInverseExceptional φ F →
      ∀ g : X.PartialMap X₀, g.toRationalMap = ψ → ∀ hF : F.genericPoint ∈ g.domain,
        g.hom ⟨F.genericPoint, hF⟩ ∉ (A₀.supp : Set X₀)) :
    haveI := S₀.integral
    haveI := S₀.idealSheaf.isLocallyNoetherian_subscheme
    haveI := S.integral
    haveI := S.idealSheaf.isLocallyNoetherian_subscheme
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      ∀ (hB₀ : ∀ Z : irreducibleComponents S₀.idealSheaf.subscheme,
          S₀.idealSheaf.subschemeι (componentGenericPoint _ Z) ∉ ((q : ℤ) • D₁).supp)
        (E₀ : Divisor S₀.idealSheaf.subscheme),
        ((q : ℤ) • D₁).IsPullback S₀.idealSheaf.subschemeι hB₀ E₀ →
      ∀ (hC : Divisor.IsCartier (Mori.RationalMap.transformDivisor φ ((q : ℤ) • D₁)))
        (hB : ∀ Z : irreducibleComponents S.idealSheaf.subscheme,
          S.idealSheaf.subschemeι (componentGenericPoint _ Z) ∉
            (Mori.RationalMap.transformDivisor φ ((q : ℤ) • D₁)).supp)
        (E : Divisor S.idealSheaf.subscheme),
        Divisor.IsPullback S.idealSheaf.subschemeι
          (Mori.RationalMap.transformDivisor φ ((q : ℤ) • D₁)) hB E →
          sectionsFinrank (S₀.idealSheaf.subschemeι ≫ sX₀) E₀ ≤
            sectionsFinrank (S.idealSheaf.subschemeι ≫ sX) E := by
  haveI := S.integral
  haveI := S.idealSheaf.isLocallyNoetherian_subscheme
  haveI := S₀.integral
  haveI := S₀.idealSheaf.isLocallyNoetherian_subscheme
  haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hXp.isProjective
  obtain ⟨q₀, hq₀⟩ := exists_surjective_restriction sX₀ hX₀p S₀ D₁ hD₁ hamp hD₁S
  refine ⟨q₀, fun q hq hB₀ E₀ hE₀ hC hB E hE => ?_⟩
  obtain ⟨ρ, hρ, hρ0⟩ := hq₀ q hq hB₀ E₀ hE₀
  obtain ⟨Φ, hΦ⟩ := exists_transform_restriction sX₀ sX hX₀ hX₀p hXp S₀ A₀ ((q : ℤ) • D₁)
    ((supp_zsmul_le _ _).trans hD₁A)
    (by rw [DivisorWithCoeffs.coeff_smul, hD₁S, smul_zero]) φ ψ hψ hφk hψk S hS hord hC hB E hE
  have hEc : E.IsCartier := Divisor.IsPullback.isCartier hE hC
  letI : Module k (E.divisorialSubmodule ⊤) :=
    Module.compHom _ (scalarsToGlobalSections k (S.idealSheaf.subschemeι ≫ sX))
  haveI := finiteDimensional_sections (S.idealSheaf.subschemeι ≫ sX) E hEc
  letI : Module k (((q : ℤ) • D₁).divisorialSubmodule ⊤) :=
    Module.compHom _ (scalarsToGlobalSections k sX₀)
  letI : Module k (E₀.divisorialSubmodule ⊤) :=
    Module.compHom _ (scalarsToGlobalSections k (S₀.idealSheaf.subschemeι ≫ sX₀))
  unfold sectionsFinrank
  exact finrank_le_of_surjective_of_ker_le ρ hρ Φ fun f hf => hρ0 f (hΦ f hf)

/-- **Bigness of the restriction.** In the setting of
`MMP.Fourfold.isRelativelyBig_pullback_transformDivisor_of_isAmple`, the pull-back `A|_S` of
`A = φ_* A⁰` to the retained divisor `S` is big over `k`. The source's argument: for `m` divisible
by the Cartier indices and large, Serre vanishing for `𝓘_{S⁰}(mA⁰)` makes
`H⁰(X⁰, mA⁰) → H⁰(S⁰, mA⁰|_{S⁰})` surjective; a section of `mA⁰`, read as a rational function,
transforms to a section of `mA` (each prime of `X` comes from a prime of `X⁰`, or is extracted with
centre outside `Supp A⁰`, and `X` is normal); restriction at the generic point of `S`, where `φ`
identifies the residue fields of `S⁰` and `S`, gives an injection
`H⁰(S⁰, mA⁰|_{S⁰}) ↪ H⁰(S, mA|_S)`, and the source grows like `m^{dim S}` since `A⁰|_{S⁰}` is
ample. -/
private theorem isRelativelyBig_of_isPullback_transformDivisor {k : Type u} [Field k]
    {X₀ X : Scheme.{u}}
    [IsIntegral X₀] [IsLocallyNoetherian X₀] [IsNormal X₀] [CompactSpace X₀]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX₀ : X₀ ⟶ Spec (.of k)) (sX : X ⟶ Spec (.of k))
    (hX₀ : IsNormalVariety k sX₀) (hX₀p : Mori.IsProjectiveVariety k sX₀)
    (hXQ : IsQFactorial sX) (hXp : Mori.IsProjectiveVariety k sX)
    (S₀ : Mori.PrimeDivisor X₀) [IsNormal S₀.idealSheaf.subscheme]
    (A₀ : QDivisor X₀) (hA₀ : 0 ≤ A₀) (hAamp : A₀.IsAmple) (hAS : A₀.coeff S₀ = 0)
    (φ : X₀.RationalMap X) (ψ : X.RationalMap X₀) (hψ : Mori.RationalMap.IsInverse φ ψ)
    (hφk : MMP.Flips.RationalMap.IsOver sX₀ sX φ) (hψk : MMP.Flips.RationalMap.IsOver sX sX₀ ψ)
    (S : Mori.PrimeDivisor X) [IsNormal S.idealSheaf.subscheme]
    (hS : Mori.RationalMap.transformPrimeDivisor φ S₀ = some S)
    (hfin : {F : Mori.PrimeDivisor X | MMP.Flips.RationalMap.IsInverseExceptional φ F}.Finite)
    (hord : ∀ F : Mori.PrimeDivisor X, MMP.Flips.RationalMap.IsInverseExceptional φ F →
      ∀ g : X.PartialMap X₀, g.toRationalMap = ψ → ∀ hF : F.genericPoint ∈ g.domain,
        g.hom ⟨F.genericPoint, hF⟩ ∉ (A₀.supp : Set X₀)) :
    haveI := S.integral
    haveI := S.idealSheaf.isLocallyNoetherian_subscheme
    ∀ (hB : ∀ Z : irreducibleComponents S.idealSheaf.subscheme,
        S.idealSheaf.subschemeι (componentGenericPoint _ Z) ∉
          (Mori.RationalMap.transformDivisor φ A₀).supp)
      (B : QDivisor S.idealSheaf.subscheme),
      QDivisor.IsPullback S.idealSheaf.subschemeι (Mori.RationalMap.transformDivisor φ A₀) hB B →
        B.IsRelativelyBig (S.idealSheaf.subschemeι ≫ sX) := by
  intro hB B hBp
  haveI := S.integral
  haveI := S.idealSheaf.isLocallyNoetherian_subscheme
  haveI := S₀.integral
  haveI := S₀.idealSheaf.isLocallyNoetherian_subscheme
  haveI : IsProper sX₀ := isProper_of_isProjectiveMorphism sX₀ hX₀p.isProjective
  haveI : CompactSpace S₀.idealSheaf.subscheme :=
    S₀.idealSheaf.subschemeι.isClosedEmbedding.compactSpace
  haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hXp.isProjective
  haveI : Scheme.IsSeparated X₀ := ⟨isSeparated_terminal_of_isSeparated sX₀⟩
  haveI : Scheme.IsSeparated X := ⟨isSeparated_terminal_of_isSeparated sX⟩
  -- an ample Cartier multiple `D₁ = m₁ A⁰`
  obtain ⟨m₁, hm₁, D₁, hD₁, hD₁c, hD₁a⟩ := hAamp
  have hD₁q : Divisor.toQDivisor D₁ = ((m₁ : ℤ)) • A₀ := by
    rw [hD₁, ← Int.cast_smul_eq_zsmul ℚ]; rfl
  have hD₁S : D₁.coeff S₀ = 0 := by
    have h := congrArg (fun G : QDivisor X₀ => G S₀) hD₁q
    simp only [Finsupp.smul_apply, zsmul_eq_mul] at h
    change ((D₁ S₀ : ℤ) : ℚ) = _ at h
    have h0 : A₀ S₀ = 0 := hAS
    rw [h0, mul_zero] at h
    exact_mod_cast h
  have hD₁A : D₁.supp ≤ A₀.supp := by
    rw [← Divisor.supp_toQDivisor, hD₁q,
      QDivisor.supp_zsmul (by exact_mod_cast hm₁.ne')]
  -- a Cartier multiple `G = n φ_* D₁` of `φ_* A⁰`
  obtain ⟨n, hn, hnC⟩ := hXQ.2 (Mori.RationalMap.transformDivisor φ D₁)
  have hGq : Divisor.toQDivisor ((n : ℤ) • Mori.RationalMap.transformDivisor φ D₁) =
      ((n * m₁ : ℕ) : ℤ) • Mori.RationalMap.transformDivisor φ A₀ := by
    rw [map_zsmul, ← transformDivisor_toQDivisor, hD₁q, map_zsmul, smul_smul]
    push_cast; ring_nf
  obtain ⟨G', hG'q, hG'p⟩ := hBp (n * m₁) (by positivity) _ hGq hnC
  have hG'c : G'.IsCartier := Divisor.IsPullback.isCartier hG'p hnC
  -- dimensions
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_subscheme_eq_natCast sX₀ hX₀p S₀
  have hdS := topologicalKrullDim_subscheme_eq sX₀ sX hX₀p hXp S₀ φ ψ hψ S hS
  obtain ⟨c, hc, q₁, hq₁⟩ := exists_growth_sectionsFinrank sX₀ hX₀p S₀ D₁ hD₁c hD₁a hD₁S d hd
  obtain ⟨q₀, hq₀⟩ := sectionsFinrank_le_of_isPullback sX₀ sX hX₀ hX₀p hXQ hXp S₀ A₀ D₁ hD₁c
    hD₁a hD₁A hD₁S φ ψ hψ hφk hψk S hS hord
  refine ⟨n * m₁, by positivity, G', ?_, hG'c, d, 0, by rw [hdS, hd],
    topologicalKrullDim_closure_range_eq_zero _, c / 2, by positivity,
    ((q₀ + q₁ + 1 : ℕ) : ℤ), fun m hm => ?_⟩
  · rw [hG'q, ← Int.cast_smul_eq_zsmul ℚ]; rfl
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = j := ⟨m.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hj : q₀ + q₁ + 1 ≤ j := by exact_mod_cast hm
  set q : ℕ := j * n with hqdef
  have hjq : j ≤ q := Nat.le_mul_of_pos_right j hn
  -- the pull-backs at level `q`
  have hqG : (j : ℤ) • ((n : ℤ) • Mori.RationalMap.transformDivisor φ D₁) =
      Mori.RationalMap.transformDivisor φ ((q : ℤ) • D₁) := by
    rw [smul_smul, map_zsmul, hqdef]; push_cast; rfl
  have hB₀ : ∀ Z : irreducibleComponents S₀.idealSheaf.subscheme,
      S₀.idealSheaf.subschemeι (componentGenericPoint _ Z) ∉ ((q : ℤ) • D₁).supp :=
    subschemeι_componentGenericPoint_notMem S₀ (genericPoint_notMem_supp_self S₀ _
      (by rw [DivisorWithCoeffs.coeff_smul, hD₁S, smul_zero]))
  obtain ⟨E₀, hE₀⟩ := Divisor.IsCartier.exists_isPullback (hD₁c.zsmul (q : ℤ)) hB₀
  have hBq : ∀ Z : irreducibleComponents S.idealSheaf.subscheme,
      S.idealSheaf.subschemeι (componentGenericPoint _ Z) ∉
        (Mori.RationalMap.transformDivisor φ ((q : ℤ) • D₁)).supp :=
    subschemeι_componentGenericPoint_notMem S (genericPoint_notMem_supp_transformDivisor hψ hS _
      (by rw [DivisorWithCoeffs.coeff_smul, hD₁S, smul_zero]))
  have hjG := hG'p.zsmul hnC (j : ℤ) (by rwa [hqG])
  have hp : Divisor.IsPullback S.idealSheaf.subschemeι
      (Mori.RationalMap.transformDivisor φ ((q : ℤ) • D₁)) hBq ((j : ℤ) • G') :=
    Divisor.IsPullback.of_eq hqG hjG
  have hqC : Divisor.IsCartier (Mori.RationalMap.transformDivisor φ ((q : ℤ) • D₁)) :=
    hqG ▸ hnC.zsmul (j : ℤ)
  have h1 := hq₁ q (by omega) hB₀ E₀ hE₀
  have h2 := hq₀ q (by omega) hB₀ E₀ hE₀ hqC hBq _ hp
  haveI : IsProper (S.idealSheaf.subschemeι ≫ sX) := inferInstance
  rw [relativeGenericRank_eq_sectionsFinrank _ _ (hG'c.zsmul (j : ℤ)), Nat.sub_zero]
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
  have hjpos : (0 : ℝ) < (j : ℝ) ^ d := by positivity
  calc c / 2 * ((j : ℤ) : ℝ) ^ d < c * (j : ℝ) ^ d := by push_cast; nlinarith
    _ ≤ c * (q : ℝ) ^ d := by gcongr
    _ ≤ (sectionsFinrank (S₀.idealSheaf.subschemeι ≫ sX₀) E₀ : ℝ) := h1
    _ ≤ _ := by exact_mod_cast h2

/-- The image of the generic point of an irreducible space is dense in the closure of the
range: `closure (f X) = closure {f ξ_X}`. -/
private theorem closure_range_eq_closure_genericPoint {X S : Scheme.{u}} [IrreducibleSpace X]
    (f : X ⟶ S) :
    closure (Set.range f.base) = closure {f (genericPoint X)} := by
  refine le_antisymm (closure_minimal ?_ isClosed_closure)
    (closure_mono (Set.singleton_subset_iff.mpr ⟨_, rfl⟩))
  rintro _ ⟨x, rfl⟩
  exact specializes_iff_mem_closure.mp ((genericPoint_specializes x).map f.continuous)

/-- A partial isomorphism `e : X ⤏ Y` of irreducible schemes sends the generic point of `X` to
the generic point of `Y`. -/
private theorem iso_hom_genericPoint {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (e : X.PartialIso Y) (p : e.source) (hp : p.1 = genericPoint X) :
    (e.target.ι (e.iso.hom p)) = genericPoint Y := by
  have hspec : ∀ q : e.source, e.target.ι (e.iso.hom p) ⤳ e.target.ι (e.iso.hom q) := by
    intro q
    have hpq : p ⤳ q :=
      Topology.IsInducing.subtypeVal.specializes_iff.mp (hp ▸ genericPoint_specializes _)
    exact (hpq.map (e.iso.hom ≫ e.target.ι).continuous)
  have htarget : (e.target : Set Y) ⊆ closure {e.target.ι (e.iso.hom p)} := by
    intro z hz
    obtain ⟨w, rfl⟩ : z ∈ Set.range e.target.ι := by rwa [Scheme.Opens.range_ι]
    have hw : e.iso.hom (e.iso.inv w) = w := by
      simpa using (Scheme.homeoOfIso e.iso).apply_symm_apply w
    rw [← hw]
    exact specializes_iff_mem_closure.mp (hspec _)
  have hcl : closure {e.target.ι (e.iso.hom p)} = (Set.univ : Set Y) := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← e.dense_target.closure_eq]
    exact closure_minimal htarget isClosed_closure
  exact ((genericPoint_spec Y).eq (by rw [IsGenericPoint, hcl])).symm

/-- For a partial isomorphism `e : X ⤏ Y` of irreducible schemes over `S` (via `πX`, `πY`),
`πX (ξ_X) = πY (ξ_Y)`. -/
private theorem base_genericPoint_eq_of_isOver {X Y S : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (πX : X ⟶ S) (πY : Y ⟶ S) (e : X.PartialIso Y)
    (hover : MMP.Flips.RationalMap.IsOver πX πY e.toRationalMap) :
    πX (genericPoint X) = πY (genericPoint Y) := by
  have h1 : (e.toPartialMap.compHom πY).fromFunctionField = πX.toPartialMap.fromFunctionField :=
    congrArg Scheme.RationalMap.fromFunctionField hover
  simp only [Scheme.PartialMap.fromFunctionField, Scheme.PartialMap.fromSpecStalkOfMem_compHom,
    Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap] at h1
  obtain ⟨hx, h1⟩ : ∃ hx, e.toPartialMap.fromSpecStalkOfMem hx ≫ πY =
      X.fromSpecStalk (genericPoint X) ≫ πX := ⟨_, h1⟩
  obtain ⟨pt, hpt⟩ : ∃ pt : Spec (X.presheaf.stalk (genericPoint X)),
      X.fromSpecStalk _ pt = genericPoint X := ⟨_, Scheme.fromSpecStalk_closedPoint⟩
  have hx' : genericPoint X ∈ e.source := by simpa using hx
  have h2 : πY (e.toPartialMap.fromSpecStalkOfMem hx pt) = πX (genericPoint X) := by
    rw [← Scheme.Hom.comp_apply, h1, Scheme.Hom.comp_apply, hpt]
  rw [← h2]
  congr 1
  have h3 : e.source.ι (e.source.fromSpecStalkOfMem (genericPoint X) hx' pt) = genericPoint X := by
    rw [← Scheme.Hom.comp_apply, Scheme.Opens.fromSpecStalkOfMem_ι, hpt]
  change e.target.ι (e.iso.hom (e.source.fromSpecStalkOfMem (genericPoint X) hx' pt)) =
    genericPoint Y
  exact iso_hom_genericPoint e _ h3

/-- `LinearMap.finrank_le_finrank_of_injective` with the module structures taken from the map,
for modules whose instances are local definitions. -/
private theorem finrank_le_finrank_of_injective' {K M N : Type u} [Field K]
    {_ : AddCommMonoid M} {_ : Module K M} {_ : AddCommMonoid N} {_ : Module K N}
    (hN : Module.Finite K N) (f : M →ₗ[K] N) (hf : Function.Injective f) :
    Module.finrank K M ≤ Module.finrank K N :=
  f.finrank_le_finrank_of_injective hf

/-- `fiberRank` is monotone along an injective `κ(s)`-linear map of fibres into a
finite-dimensional fibre. -/
private theorem fiberRank_le_of_injective {S : Scheme.{u}} (F G : S.Modules) (s : S)
    (hfin :
      letI : Module (S.presheaf.stalk s) (G.presheaf.stalk s) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := S.presheaf) G.val s
      letI : Algebra (S.presheaf.stalk s) (S.residueField s) := (S.residue s).hom.toAlgebra
      Module.Finite (S.residueField s)
        (S.residueField s ⊗[S.presheaf.stalk s] G.presheaf.stalk s))
    (hinj :
      letI : Module (S.presheaf.stalk s) (F.presheaf.stalk s) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := S.presheaf) F.val s
      letI : Module (S.presheaf.stalk s) (G.presheaf.stalk s) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := S.presheaf) G.val s
      letI : Algebra (S.presheaf.stalk s) (S.residueField s) := (S.residue s).hom.toAlgebra
      ∃ f : (S.residueField s ⊗[S.presheaf.stalk s] F.presheaf.stalk s) →ₗ[S.residueField s]
          (S.residueField s ⊗[S.presheaf.stalk s] G.presheaf.stalk s),
        Function.Injective f) :
    Scheme.Modules.fiberRank F s ≤ Scheme.Modules.fiberRank G s := by
  obtain ⟨f, hf⟩ := hinj
  exact finrank_le_finrank_of_injective' hfin f hf

/-- **Finiteness of the fibres of `πY_* 𝒪_Y(E)`.** For a morphism `πY : Y ⟶ S` of projective
varieties over `k` with `Y` normal, and a Cartier divisor `E` on `Y`, the fibre
`κ(s) ⊗ (πY_* 𝒪_Y(E))_s` is finite-dimensional over `κ(s)` at every point `s` of `S`: `𝒪_Y(E)`
is invertible, hence coherent, its direct image along the proper `πY` is coherent
([Stacks, Tag 02O5]), so its stalks are finite `𝒪_{S,s}`-modules. -/
private theorem finite_fiber_pushforward_divisorialSheaf
    {k : Type u} [Field k] {Y S : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (sY : Y ⟶ Spec (.of k)) (sS : S ⟶ Spec (.of k))
    (hYp : Mori.IsProjectiveVariety k sY) (hS : Mori.IsProjectiveVariety k sS)
    (πY : Y ⟶ S) (hπY : πY ≫ sS = sY) (E : Divisor Y) (hE : E.IsCartier) (s : S) :
    letI G := (Scheme.Modules.pushforward πY).obj (Mori.Divisor.divisorialSheaf E)
    letI : Module (S.presheaf.stalk s) (G.presheaf.stalk s) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := S.presheaf) G.val s
    letI : Algebra (S.presheaf.stalk s) (S.residueField s) := (S.residue s).hom.toAlgebra
    Module.Finite (S.residueField s)
      (S.residueField s ⊗[S.presheaf.stalk s] G.presheaf.stalk s) := by
  have : IsProper sY := by
    have := hYp.isProjective
    exact isProper_of_isProjectiveMorphism sY this
  have : IsSeparated sS := hS.toIsSeparated
  have : LocallyOfFiniteType sS := hS.toLocallyOfFiniteType
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian sS
  have : IsProper (πY ≫ sS) := hπY ▸ inferInstance
  have : IsProper πY := IsProper.of_comp πY sS
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have hinv := hE.isInvertibleModule_divisorialSheaf
  have : (Mori.Divisor.divisorialSheaf E).IsCoherent :=
    @Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible Y _ _ hinv
  have := ProperCoherenceWitness.isCoherent_pushforward πY (Mori.Divisor.divisorialSheaf E)
  have := Scheme.Modules.finite_stalk_of_isCoherent
    ((Scheme.Modules.pushforward πY).obj (Mori.Divisor.divisorialSheaf E)) s
  exact Module.Finite.base_change _ _ _

/-- Base change to a quotient field `K` of `R` preserves the injectivity of `u : M → N` when the
kernel of `R → K` acts by zero on `N`: then `K ⊗ M` is spanned by the `1 ⊗ x`, and `1 ⊗ y = 0`
forces `y = 0`. -/
private theorem injective_baseChange_of_smul_eq_zero {R K M N : Type*} [CommRing R]
    [CommRing K] [Algebra R K] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (hsurj : Function.Surjective (algebraMap R K))
    (hN : ∀ r : R, algebraMap R K r = 0 → ∀ y : N, r • y = 0)
    (u : M →ₗ[R] N) (hu : Function.Injective u) :
    Function.Injective (u.baseChange K) := by
  classical
  choose pre hpre using hsurj
  have hkill : ∀ r r' : R, algebraMap R K r = algebraMap R K r' → ∀ y : N, r • y = r' • y := by
    intro r r' h y
    have := hN (r - r') (by rw [map_sub, h, sub_self]) y
    rwa [sub_smul, sub_eq_zero] at this
  let B : K →ₗ[R] N →ₗ[R] N := LinearMap.mk₂ R (fun c y => pre c • y)
    (fun c c' y => by
      rw [← add_smul]; exact hkill _ _ (by rw [map_add, hpre, hpre, hpre]) y)
    (fun r c y => by
      rw [smul_smul]
      exact hkill _ _ (by rw [map_mul, hpre, hpre, Algebra.smul_def]) y)
    (fun c y y' => smul_add _ _ _)
    (fun r c y => smul_comm _ _ _)
  let θ : K ⊗[R] N →ₗ[R] N := TensorProduct.lift B
  have hθ : ∀ y : N, θ (1 ⊗ₜ y) = y := fun y => by
    change pre 1 • y = y
    rw [hkill (pre 1) 1 (by rw [hpre, map_one]) y, one_smul]
  have hsurjM : ∀ z : K ⊗[R] M, ∃ x, z = 1 ⊗ₜ x := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by rw [TensorProduct.tmul_zero]⟩
    | tmul c x =>
      refine ⟨pre c • x, ?_⟩
      rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, hpre]
    | add z z' hz hz' =>
      obtain ⟨x, rfl⟩ := hz
      obtain ⟨x', rfl⟩ := hz'
      exact ⟨x + x', by rw [TensorProduct.tmul_add]⟩
  intro z z' h
  obtain ⟨x, rfl⟩ := hsurjM z
  obtain ⟨x', rfl⟩ := hsurjM z'
  rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul] at h
  have : u x = u x' := by rw [← hθ (u x), h, hθ]
  rw [hu this]

/-- The maximal ideal of `𝒪_{S,η}`, for `η = πY(ξ_Y)`, acts by zero on the stalk at `η` of
`πY_* 𝒪_Y(E)`: the image of an element of the maximal ideal in the function field `K(Y)` is a
non-unit of a field, hence zero, and sections of `𝒪_Y(E)` are rational functions. -/
private theorem smul_stalk_pushforward_divisorialSheaf_eq_zero {Y S : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (πY : Y ⟶ S) (E : Divisor Y) (s : S)
    (hs : πY (genericPoint Y) = s) :
    letI G := (Scheme.Modules.pushforward πY).obj (Mori.Divisor.divisorialSheaf E)
    letI : Module (S.presheaf.stalk s) (G.presheaf.stalk s) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := S.presheaf) G.val s
    ∀ r ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk s), ∀ m : G.presheaf.stalk s, r • m = 0 := by
  intro r hr m
  obtain ⟨W₁, h₁, r₀, rfl⟩ := S.presheaf.exists_germ_eq r
  obtain ⟨W₂, h₂, m₀, hm⟩ := TopCat.Presheaf.exists_germ_eq _ m
  subst hm
  have hW : s ∈ W₁ ⊓ W₂ := ⟨h₁, h₂⟩
  rw [← S.presheaf.germ_res_apply (homOfLE inf_le_left) s hW,
    ← TopCat.Presheaf.germ_res_apply _ (homOfLE inf_le_right) s hW]
  refine (PresheafOfModules.germ_smul (R := S.presheaf)
    ((Scheme.Modules.pushforward πY).obj E.divisorialSheaf).val s (W₁ ⊓ W₂) hW _ _).symm.trans ?_
  set r₁ := S.presheaf.map (homOfLE (inf_le_left : W₁ ⊓ W₂ ≤ W₁)).op r₀
  have hr₁ : S.presheaf.germ (W₁ ⊓ W₂) s hW r₁ ∈ IsLocalRing.maximalIdeal _ := by
    rwa [S.presheaf.germ_res_apply]
  -- the image of `r₁` at any point of `Y` over `s` with a field as local ring vanishes
  have hzero : ∀ (y : Y) (hy : y ∈ πY ⁻¹ᵁ (W₁ ⊓ W₂)), πY y = s →
      IsField (Y.presheaf.stalk y) → Y.presheaf.germ _ y hy (πY.app _ r₁) = 0 := by
    intro y hy hys hfield
    erw [← Scheme.Hom.germ_stalkMap_apply πY _ y hy]
    have hmem : ∀ (t : S) (ht : t ∈ W₁ ⊓ W₂), t = s →
        S.presheaf.germ (W₁ ⊓ W₂) t ht r₁ ∈ IsLocalRing.maximalIdeal _ := by
      rintro t ht rfl; exact hr₁
    have hnu := hmem _ hy hys
    by_contra hne
    let := hfield.toField
    exact (IsLocalRing.mem_maximalIdeal _).mp hnu
      (IsLocalHom.map_nonunit (f := (πY.stalkMap y).hom) _ (Ne.isUnit hne))
  let r₂ : S.ringCatSheaf.obj.obj (Opposite.op (W₁ ⊓ W₂)) := r₁
  have key : ∀ m : ((Scheme.Modules.pushforward πY).obj E.divisorialSheaf).val.obj
      (Opposite.op (W₁ ⊓ W₂)), r₂ • m = 0 := by
    intro m
    let m' : E.divisorialSubmodule (πY ⁻¹ᵁ (W₁ ⊓ W₂)) := m
    change (πY.app _ r₁) • m' = 0
    refine Subtype.ext (funext fun Z => ?_)
    change Y.presheaf.germ _ _ Z.2 (πY.app _ r₁) * (m'.1 Z) = 0
    rw [hzero _ Z.2 (by rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, hs])
      (Mori.RationalFunctions.isField_stalk Y Z.1), zero_mul]
  erw [key]
  exact map_zero _

/-- **Transfer of rational functions along the birational contraction.** The isomorphism
`t : K(X) ≅ K(Y)` read off a partial isomorphism representing `φ` is compatible with the maps
from `𝒪_S`, and sends a rational function `f` with `div f + D ≥ 0` over `πX⁻¹ W` to one with
`div (t f) + φ_* D ≥ 0` over `πY⁻¹ W`: every prime divisor `Q` of `Y` is `φ_* P` for a unique `P`
(`φ` extracts no divisor), with `v_Q ∘ t = v_P`, the same coefficient, and `πX(η_P) = πY(η_Q)`. -/
private theorem exists_functionField_transfer
    {k : Type u} [Field k] {X Y S : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) (sS : S ⟶ Spec (.of k))
    (hX : Mori.IsNormalVariety k sX)
    (hYp : Mori.IsProjectiveVariety k sY) (hS : Mori.IsProjectiveVariety k sS)
    (πX : X ⟶ S) (πY : Y ⟶ S)
    (φ : X.RationalMap Y) (hφ : Mori.RationalMap.IsBirational φ)
    (hover : MMP.Flips.RationalMap.IsOver πX πY φ)
    (hcontr : ∀ F : Mori.PrimeDivisor Y, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F)
    (D : Divisor X) :
    ∃ t : X.functionField →+* Y.functionField,
      (∀ (W : S.Opens) (r : Γ(S, W)) (hXW : genericPoint X ∈ πX ⁻¹ᵁ W)
          (hYW : genericPoint Y ∈ πY ⁻¹ᵁ W),
        t (X.presheaf.germ _ _ hXW (πX.app W r)) = Y.presheaf.germ _ _ hYW (πY.app W r)) ∧
      (∀ (W : S.Opens) (f : X.functionField),
        (∀ P : Mori.PrimeDivisor X, (P.support ∩ πX ⁻¹ᵁ W).Nonempty →
          P.OrdGE (-D.coeff P) ((toFunctionField X P.component).symm f)) →
        ∀ Q : Mori.PrimeDivisor Y, (Q.support ∩ πY ⁻¹ᵁ W).Nonempty →
          Q.OrdGE (-(Mori.RationalMap.transformDivisor φ D).coeff Q)
            ((toFunctionField Y Q.component).symm (t f))) := by
  have : IsSeparated sY := hYp.toIsSeparated
  have : IsSeparated sS := hS.toIsSeparated
  have := isSeparated_terminal_of_isSeparated sY
  have := isSeparated_terminal_of_isSeparated sS
  obtain ⟨e, rfl⟩ := id hφ
  have hξe : genericPoint X ∈ e.source :=
    ((genericPoint_spec X).mem_open_set_iff e.source.isOpen).mpr
      (by simpa using e.dense_source.nonempty)
  have : Nonempty e.source := ⟨⟨_, hξe⟩⟩
  have : IsDominant e.source.ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
  have : IsDominant (e.iso.hom ≫ e.target.ι) :=
    MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
  have bX : Function.Bijective (functionFieldMap e.source.ι) :=
    MMP.Mori.functionFieldMap_bijective_of_isOpenImmersion _ ⊤ ⟨⟨_, hξe⟩, trivial⟩
  have bY : Function.Bijective (functionFieldMap (e.iso.hom ≫ e.target.ι)) :=
    MMP.Mori.functionFieldMap_bijective_of_isOpenImmersion _ ⊤ ⟨⟨_, hξe⟩, trivial⟩
  let t : X.functionField ≃+* Y.functionField :=
    (RingEquiv.ofBijective _ bX).trans (RingEquiv.ofBijective _ bY).symm
  have ht : ∀ a, functionFieldMap (e.iso.hom ≫ e.target.ι) (t a) =
      functionFieldMap e.source.ι a := fun a =>
    (RingEquiv.ofBijective _ bY).apply_symm_apply _
  have hE : (e.iso.hom ≫ e.target.ι) ≫ πY = e.source.ι ≫ πX :=
    hom_comp_eq_of_isOver πX πY e.toPartialMap hover
  refine ⟨t.toRingHom, ?_, ?_⟩
  · intro W r hXW hYW
    have hs : genericPoint e.source ∈ e.source.ι ⁻¹ᵁ (πX ⁻¹ᵁ W) := by
      change e.source.ι (genericPoint e.source) ∈ πX ⁻¹ᵁ W
      rwa [map_genericPoint_of_isDominant]
    have hs' : genericPoint e.source ∈ (e.iso.hom ≫ e.target.ι) ⁻¹ᵁ (πY ⁻¹ᵁ W) := by
      change (e.iso.hom ≫ e.target.ι) (genericPoint e.source) ∈ πY ⁻¹ᵁ W
      rwa [map_genericPoint_of_isDominant]
    apply (functionFieldMap (e.iso.hom ≫ e.target.ι)).injective
    change functionFieldMap _ (t _) = _
    rw [ht, functionFieldMap_germ e.source.ι (πX ⁻¹ᵁ W) hXW hs,
      functionFieldMap_germ _ (πY ⁻¹ᵁ W) hYW hs']
    have e1 : e.source.ι.app (πX ⁻¹ᵁ W) (πX.app W r) = (e.source.ι ≫ πX).app W r := by
      rw [Scheme.Hom.comp_app]; rfl
    have e2 : (e.iso.hom ≫ e.target.ι).app (πY ⁻¹ᵁ W) (πY.app W r) =
        ((e.iso.hom ≫ e.target.ι) ≫ πY).app W r := by
      rw [Scheme.Hom.comp_app (e.iso.hom ≫ e.target.ι) πY]; rfl
    rw [e1, e2]
    exact germ_app_congr hE.symm W _ _ _ r
  · intro W f hP Q hQ
    obtain ⟨P, hPQ⟩ : ∃ P, Mori.RationalMap.transformPrimeDivisor e.toRationalMap P = some Q := by
      by_contra hne
      exact hcontr Q fun P hP => hne ⟨P, hP⟩
    obtain ⟨hπ, hR⟩ := transfer_at_primeDivisor πX πY e hover t ht P Q hPQ
    have hcomap := divisorialValuation_comap_eq P Q t hR
    have hv : ∀ a, Q.divisorialValuation (t a) = P.divisorialValuation a := fun a => by
      rw [← hcomap]; rfl
    have huniq : ∀ P', Mori.RationalMap.transformPrimeDivisor e.toRationalMap P' = some Q →
        P' = P := by
      intro P' hP'
      obtain ⟨-, hR'⟩ := transfer_at_primeDivisor πX πY e hover t ht P' Q hP'
      have hvv : P'.divisorialValuation = P.divisorialValuation :=
        (divisorialValuation_comap_eq P' Q t hR').symm.trans hcomap
      have hgen := MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1
        (D := Mori.DivisorOver.ofPrimeDivisor k hX P')
        (D' := Mori.DivisorOver.ofPrimeDivisor k hX P) (by
          ext g
          change P'.divisorialValuation (functionFieldMap (𝟙 X) g) =
            P.divisorialValuation (functionFieldMap (𝟙 X) g)
          rw [hvv])
      exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective hgen
    have hcoeff : (Mori.RationalMap.transformDivisor e.toRationalMap D).coeff Q = D.coeff P :=
      MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hPQ huniq D
    have hPW : (P.support ∩ πX ⁻¹ᵁ W).Nonempty := by
      refine ⟨P.genericPoint, ?_, ?_⟩
      · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact subset_closure rfl
      · change πX P.genericPoint ∈ W
        rw [hπ]
        exact Q.genericPoint_mem_of_nonempty hQ
    rw [hcoeff]
    rcases hP P hPW with h0 | hle
    · left
      have hf : f = 0 := (toFunctionField X P.component).symm.injective (h0.trans (map_zero _).symm)
      change (toFunctionField Y Q.component).symm (t f) = 0
      rw [hf, map_zero, map_zero]
    · right
      rw [valuation_symm_toFunctionField] at hle ⊢
      change _ ≤ (Q.divisorialValuation (t f))⁻¹
      rwa [hv]

/-- **The section comparison.** A ring map `t : K(X) → K(Y)` compatible with the maps from `𝒪_S`
and sending rational functions with `div f + D ≥ 0` over `πX⁻¹ W` to ones with
`div (t f) + D' ≥ 0` over `πY⁻¹ W` induces a morphism of `𝒪_S`-modules
`πX_* 𝒪_X(D) ⟶ πY_* 𝒪_Y(D')`, injective on sections. -/
private theorem exists_hom_pushforward_divisorialSheaf_injective
    {X Y S : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (πX : X ⟶ S) (πY : Y ⟶ S)
    (hη : πX (genericPoint X) = πY (genericPoint Y)) (D : Divisor X) (D' : Divisor Y)
    (t : X.functionField →+* Y.functionField)
    (hC : ∀ (W : S.Opens) (r : Γ(S, W)) (hXW : genericPoint X ∈ πX ⁻¹ᵁ W)
        (hYW : genericPoint Y ∈ πY ⁻¹ᵁ W),
      t (X.presheaf.germ _ _ hXW (πX.app W r)) = Y.presheaf.germ _ _ hYW (πY.app W r))
    (hV : ∀ (W : S.Opens) (f : X.functionField),
      (∀ P : Mori.PrimeDivisor X, (P.support ∩ πX ⁻¹ᵁ W).Nonempty →
        P.OrdGE (-D.coeff P) ((toFunctionField X P.component).symm f)) →
      ∀ Q : Mori.PrimeDivisor Y, (Q.support ∩ πY ⁻¹ᵁ W).Nonempty →
        Q.OrdGE (-D'.coeff Q) ((toFunctionField Y Q.component).symm (t f))) :
    ∃ Φ : (Scheme.Modules.pushforward πX).obj (Mori.Divisor.divisorialSheaf D) ⟶
        (Scheme.Modules.pushforward πY).obj (Mori.Divisor.divisorialSheaf D'),
      ∀ W : S.Opens, Function.Injective (Φ.val.app (Opposite.op W)) := by
  have memX : ∀ {W : S.Opens} {Z' : irreducibleComponents Y},
      componentGenericPoint Y Z' ∈ πY ⁻¹ᵁ W → genericPoint X ∈ πX ⁻¹ᵁ W := by
    intro W Z' h
    change πX (genericPoint X) ∈ W
    rwa [hη, ← MMP.Fourfold.componentGenericPoint_eq_genericPoint Z']
  have memX' : ∀ {W : S.Opens} {Z' : irreducibleComponents Y},
      componentGenericPoint Y Z' ∈ πY ⁻¹ᵁ W → ∀ Z : irreducibleComponents X,
        componentGenericPoint X Z ∈ πX ⁻¹ᵁ W := by
    intro W Z' h Z
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint Z]
    exact memX h
  let Z₀ := univComponent X
  let ψ : ∀ W : S.Opens, D.divisorialSubmodule (πX ⁻¹ᵁ W) →
      ToType ((rationalFunctionsPresheaf Y).obj (Opposite.op (πY ⁻¹ᵁ W))) :=
    fun W φ Z' => (toFunctionField Y Z'.1).symm
      (t (toFunctionField X Z₀ (φ.1 ⟨Z₀, memX' Z'.2 Z₀⟩)))
  have hψ : ∀ W φ, Divisor.IsDivisorialSection D' (πY ⁻¹ᵁ W) (ψ W φ) := by
    intro W φ Q hQ
    refine hV W _ (fun P hP => ?_) Q hQ
    rw [toFunctionField_apply_eq φ.1 Z₀ P.component _
      (P.componentGenericPoint_mem_of_nonempty hP), RingEquiv.symm_apply_apply]
    exact φ.2 P hP
  have hψ0 : ∀ W, ψ W 0 = 0 := fun W => funext fun Z' => by
    change (toFunctionField Y Z'.1).symm (t (toFunctionField X Z₀
      (0 : X.presheaf.stalk (componentGenericPoint X Z₀)))) =
        (0 : Y.presheaf.stalk (componentGenericPoint Y Z'.1))
    rw [map_zero, map_zero, map_zero]
  have hψadd : ∀ W φ φ', ψ W (φ + φ') = ψ W φ + ψ W φ' := fun W φ φ' => funext fun Z' => by
    change (toFunctionField Y Z'.1).symm (t (toFunctionField X Z₀
      ((φ.1 ⟨Z₀, memX' Z'.2 Z₀⟩ : X.presheaf.stalk (componentGenericPoint X Z₀)) +
        φ'.1 ⟨Z₀, memX' Z'.2 Z₀⟩))) =
        ((toFunctionField Y Z'.1).symm (t (toFunctionField X Z₀ (φ.1 ⟨Z₀, memX' Z'.2 Z₀⟩))) :
          Y.presheaf.stalk (componentGenericPoint Y Z'.1)) +
        (toFunctionField Y Z'.1).symm (t (toFunctionField X Z₀ (φ'.1 ⟨Z₀, memX' Z'.2 Z₀⟩)))
    rw [map_add, map_add, map_add]
  have hYW : ∀ {W : S.Opens} {Z' : irreducibleComponents Y},
      componentGenericPoint Y Z' ∈ πY ⁻¹ᵁ W → genericPoint Y ∈ πY ⁻¹ᵁ W := by
    intro W Z' h
    rwa [← MMP.Fourfold.componentGenericPoint_eq_genericPoint Z']
  have hψsmul : ∀ (W : S.Opens) (r : Γ(S, W)) (φ : D.divisorialSubmodule (πX ⁻¹ᵁ W)),
      ψ W ((πX.app W r) • φ) = (πY.app W r) • ψ W φ := fun W r φ => funext fun Z' => by
    change (toFunctionField Y Z'.1).symm (t (toFunctionField X Z₀
      (X.presheaf.germ _ _ (memX' Z'.2 Z₀) (πX.app W r) * φ.1 ⟨Z₀, memX' Z'.2 Z₀⟩))) =
      Y.presheaf.germ _ _ Z'.2 (πY.app W r) *
        (toFunctionField Y Z'.1).symm (t (toFunctionField X Z₀ (φ.1 ⟨Z₀, memX' Z'.2 Z₀⟩)))
    rw [map_mul, map_mul, toFunctionField_germ X Z₀ _ _ (memX Z'.2), hC W r (memX Z'.2)
      (hYW Z'.2), map_mul]
    congr 1
    rw [RingEquiv.symm_apply_eq, toFunctionField_germ Y Z'.1 _ _ (hYW Z'.2)]
  let A : ∀ W : S.Opens, D.divisorialSubmodule (πX ⁻¹ᵁ W) →+
      Divisor.divisorialSubmodule D' (πY ⁻¹ᵁ W) := fun W =>
    { toFun := fun φ => ⟨ψ W φ, hψ W φ⟩
      map_zero' := Subtype.ext (hψ0 W)
      map_add' := fun φ φ' => Subtype.ext (hψadd W φ φ') }
  refine ⟨⟨PresheafOfModules.homMk
    { app W := AddCommGrpCat.ofHom (A W.unop)
      naturality W W' i := by
        ext φ
        rfl } fun W r φ => Subtype.ext (hψsmul W.unop r φ)⟩, fun W φ φ' h => ?_⟩
  have h' : ψ W φ = ψ W φ' := congrArg Subtype.val h
  refine Subtype.ext (funext fun Z => ?_)
  have hXW : genericPoint X ∈ πX ⁻¹ᵁ W := by
    rw [← MMP.Fourfold.componentGenericPoint_eq_genericPoint Z.1]
    exact Z.2
  let Z₀' := univComponent Y
  have hZ₀' : componentGenericPoint Y Z₀' ∈ πY ⁻¹ᵁ W := by
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint]
    change πY (genericPoint Y) ∈ W
    rwa [← hη]
  apply (toFunctionField X Z.1).injective
  rw [toFunctionField_apply_eq φ.1 Z.1 Z₀ Z.2 (memX' hZ₀' Z₀),
    toFunctionField_apply_eq φ'.1 Z.1 Z₀ Z.2 (memX' hZ₀' Z₀)]
  exact congrArg _ <| (toFunctionField X Z₀).injective <|
    t.injective <| (toFunctionField Y Z₀').symm.injective <| congrFun h' ⟨Z₀', hZ₀'⟩

/-- **The fibre comparison at the generic point.** Under the hypotheses of
`exists_hom_pushforward_divisorialSheaf_injective`, the induced map of fibres at
`s = πX(ξ_X) = πY(ξ_Y)` from `πX_* 𝒪_X(D)` to `πY_* 𝒪_Y(D')` is injective: the maximal ideal of
`𝒪_{S,s}` acts by zero on the target stalk, so base change to `κ(s)` keeps injectivity. -/
private theorem exists_injective_fiber_of_functionFieldTransfer
    {X Y S : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (πX : X ⟶ S) (πY : Y ⟶ S)
    (hη : πX (genericPoint X) = πY (genericPoint Y)) (D : Divisor X) (D' : Divisor Y)
    (t : X.functionField →+* Y.functionField)
    (hC : ∀ (W : S.Opens) (r : Γ(S, W)) (hXW : genericPoint X ∈ πX ⁻¹ᵁ W)
        (hYW : genericPoint Y ∈ πY ⁻¹ᵁ W),
      t (X.presheaf.germ _ _ hXW (πX.app W r)) = Y.presheaf.germ _ _ hYW (πY.app W r))
    (hV : ∀ (W : S.Opens) (f : X.functionField),
      (∀ P : Mori.PrimeDivisor X, (P.support ∩ πX ⁻¹ᵁ W).Nonempty →
        P.OrdGE (-D.coeff P) ((toFunctionField X P.component).symm f)) →
      ∀ Q : Mori.PrimeDivisor Y, (Q.support ∩ πY ⁻¹ᵁ W).Nonempty →
        Q.OrdGE (-D'.coeff Q) ((toFunctionField Y Q.component).symm (t f)))
    (s : S) (hs : s = πX (genericPoint X)) :
    letI F := (Scheme.Modules.pushforward πX).obj (Mori.Divisor.divisorialSheaf D)
    letI G := (Scheme.Modules.pushforward πY).obj (Mori.Divisor.divisorialSheaf D')
    letI : Module (S.presheaf.stalk s) (F.presheaf.stalk s) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := S.presheaf) F.val s
    letI : Module (S.presheaf.stalk s) (G.presheaf.stalk s) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := S.presheaf) G.val s
    letI : Algebra (S.presheaf.stalk s) (S.residueField s) := (S.residue s).hom.toAlgebra
    ∃ f : (S.residueField s ⊗[S.presheaf.stalk s] F.presheaf.stalk s) →ₗ[S.residueField s]
        (S.residueField s ⊗[S.presheaf.stalk s] G.presheaf.stalk s),
      Function.Injective f := by
  obtain ⟨Φ, hΦ⟩ := exists_hom_pushforward_divisorialSheaf_injective πX πY hη D D' t hC hV
  have hη' : πY (genericPoint Y) = s := hs ▸ hη.symm
  refine ⟨(AlgebraicGeometry.stalkLinearMap _ _ Φ s).baseChange _,
    injective_baseChange_of_smul_eq_zero (IsLocalRing.residue_surjective) ?_ _ ?_⟩
  · intro r hr y
    exact smul_stalk_pushforward_divisorialSheaf_eq_zero πY _ s hη' r
      ((IsLocalRing.residue_eq_zero_iff r).mp hr) y
  · exact TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective
      (f := Scheme.Modules.Hom.mapPresheaf Φ) hΦ s

/-- **Comparison of relative generic ranks along a transfer of rational functions.** Let
`πX : X ⟶ S`, `πY : Y ⟶ S` be morphisms from normal integral schemes to a projective variety `S`
with `πX(ξ_X) = πY(ξ_Y) = η`, `Y` projective over `k` through `πY`, `D` a divisor on `X` and `D'` a
Cartier divisor on `Y`. A ring map `t : K(X) → K(Y)` compatible with the maps from `𝒪_S` and
sending rational functions with `div f + D ≥ 0` over `πX⁻¹ W` to ones with `div (t f) + D' ≥ 0`
over `πY⁻¹ W` gives an injection of the fibres at `η` of `πX_* 𝒪_X(D)` into that of
`πY_* 𝒪_Y(D')`, which is finite-dimensional ([Stacks, Tag 02O5]); so the relative generic rank of
`𝒪_X(D)` is at most that of `𝒪_Y(D')`. -/
public theorem relativeGenericRank_le_of_functionFieldTransfer
    {k : Type u} [Field k] {X Y S : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sY : Y ⟶ Spec (.of k)) (sS : S ⟶ Spec (.of k))
    (hYp : Mori.IsProjectiveVariety k sY) (hS : Mori.IsProjectiveVariety k sS)
    (πX : X ⟶ S) (πY : Y ⟶ S) (hπY : πY ≫ sS = sY)
    (hη : πX (genericPoint X) = πY (genericPoint Y)) (D : Divisor X) (D' : Divisor Y)
    (hD' : D'.IsCartier)
    (t : X.functionField →+* Y.functionField)
    (hC : ∀ (W : S.Opens) (r : Γ(S, W)) (hXW : genericPoint X ∈ πX ⁻¹ᵁ W)
        (hYW : genericPoint Y ∈ πY ⁻¹ᵁ W),
      t (X.presheaf.germ _ _ hXW (πX.app W r)) = Y.presheaf.germ _ _ hYW (πY.app W r))
    (hV : ∀ (W : S.Opens) (f : X.functionField),
      (∀ P : Mori.PrimeDivisor X, (P.support ∩ πX ⁻¹ᵁ W).Nonempty →
        P.OrdGE (-D.coeff P) ((toFunctionField X P.component).symm f)) →
      ∀ Q : Mori.PrimeDivisor Y, (Q.support ∩ πY ⁻¹ᵁ W).Nonempty →
        Q.OrdGE (-D'.coeff Q) ((toFunctionField Y Q.component).symm (t f))) :
    relativeGenericRank πX D.divisorialSheaf ≤ relativeGenericRank πY D'.divisorialSheaf := by
  unfold relativeGenericRank
  rw [← hη]
  exact fiberRank_le_of_injective _ _ _
    (finite_fiber_pushforward_divisorialSheaf sY sS hYp hS πY hπY _ hD' _)
    (exists_injective_fiber_of_functionFieldTransfer πX πY hη D D' t hC hV _ rfl)

/-- **Comparison of relative generic ranks under a birational contraction.** For a birational
map `φ : X ⤏ Y` over `S` of normal projective varieties that extracts no divisor, and any
divisor `D` on `X`, the rank at the common generic point `η` of the image in `S` of
`πX_* 𝒪_X(D)` is at most that of `πY_* 𝒪_Y(φ_* D)`: the transfer of rational functions is the
isomorphism `K(X) ≅ K(Y)` of `exists_functionField_transfer`. -/
private theorem relativeGenericRank_le_transformDivisor
    {k : Type u} [Field k] {X Y S : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) (sS : S ⟶ Spec (.of k))
    (hX : Mori.IsNormalVariety k sX)
    (hYp : Mori.IsProjectiveVariety k sY) (hS : Mori.IsProjectiveVariety k sS)
    (πX : X ⟶ S) (πY : Y ⟶ S) (hπY : πY ≫ sS = sY)
    (φ : X.RationalMap Y) (hφ : Mori.RationalMap.IsBirational φ)
    (hover : MMP.Flips.RationalMap.IsOver πX πY φ)
    (hcontr : ∀ F : Mori.PrimeDivisor Y, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F)
    (D : Divisor X) (hDc : Divisor.IsCartier (Mori.RationalMap.transformDivisor φ D)) :
    relativeGenericRank πX D.divisorialSheaf ≤
      relativeGenericRank πY
        (Mori.Divisor.divisorialSheaf (Mori.RationalMap.transformDivisor φ D)) := by
  obtain ⟨e, he⟩ := id hφ
  obtain ⟨t, hC, hV⟩ := exists_functionField_transfer sX sY sS hX hYp hS πX πY φ hφ
    hover hcontr D
  exact relativeGenericRank_le_of_functionFieldTransfer sY sS hYp hS πX πY hπY
    (base_genericPoint_eq_of_isOver πX πY e (he ▸ hover)) D _ hDc t hC hV

/-- **Birational pushforward preserves relative bigness.** Let `φ : X ⤏ Y` be a birational map
over a projective variety `S` (via `πX`, `πY`) of normal projective varieties which extracts no
divisor, with `Y` `ℚ`-factorial. If a `ℚ`-divisor `A` on `X` is big over `S`, so is `φ_* A`; no
effectivity is needed. With `mA = D` Cartier and `n φ_* D` Cartier, the rank of
`πX_* 𝒪_X(jD)` is at most that of `πY_* 𝒪_Y(φ_*(jD))`
(`relativeGenericRank_le_transformDivisor`), and `X`, `Y` have the same dimension and the same
image in `S`. -/
public theorem isRelativelyBig_transformDivisor_of_isBirational
    {k : Type u} [Field k] {X Y S : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) (sS : S ⟶ Spec (.of k))
    (hX : Mori.IsNormalVariety k sX) (hXp : Mori.IsProjectiveVariety k sX)
    (hYQ : MMP.Fourfold.IsQFactorial sY) (hYp : Mori.IsProjectiveVariety k sY)
    (hS : Mori.IsProjectiveVariety k sS)
    (πX : X ⟶ S) (πY : Y ⟶ S) (hπY : πY ≫ sS = sY)
    (φ : X.RationalMap Y) (hφ : Mori.RationalMap.IsBirational φ)
    (hover : MMP.Flips.RationalMap.IsOver πX πY φ)
    (hcontr : ∀ F : Mori.PrimeDivisor Y, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F)
    (A : QDivisor X) (hAbig : A.IsRelativelyBig πX) :
    QDivisor.IsRelativelyBig πY (Mori.RationalMap.transformDivisor φ A) := by
  obtain ⟨m₀, hm₀, D, hD, -, a, b, ha, hb, c, hc, k₀, hk⟩ := hAbig
  obtain ⟨e, he⟩ := id hφ
  subst he
  have : LocallyOfFiniteType sX := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  have : LocallyOfFiniteType sY := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  set G := Mori.RationalMap.transformDivisor e.toRationalMap D with hG
  obtain ⟨n, hn, hnC⟩ := hYQ.2 G
  refine ⟨n * m₀, by positivity, (n : ℤ) • G, ?_, hnC, a, b, ?_, ?_, c, hc, max k₀ 1,
    fun m hm => ?_⟩
  · rw [map_zsmul, hG, ← transformDivisor_toQDivisor, hD,
      ← Mori.RationalMap.transformDivisorₗ_apply ℚ, map_smul,
      Mori.RationalMap.transformDivisorₗ_apply, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    congr 1
    push_cast
    ring
  · rwa [← topologicalKrullDim_eq_of_partialIso sX sY e]
  · rwa [closure_range_eq_closure_genericPoint, ← base_genericPoint_eq_of_isOver πX πY e hover,
      ← closure_range_eq_closure_genericPoint]
  · have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
    have hmk : k₀ ≤ m := le_trans (le_max_left _ _) hm
    have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast hn
    have hmn : k₀ ≤ m * n := by nlinarith
    have heq : m • (n : ℤ) • G = Mori.RationalMap.transformDivisor e.toRationalMap
        ((m * n) • D) := by
      rw [map_zsmul, smul_smul]
    rw [heq]
    have hrank := relativeGenericRank_le_transformDivisor sX sY sS hX hYp hS πX πY hπY
      e.toRationalMap hφ hover hcontr ((m * n) • D) (heq ▸ hnC.zsmul m)
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    calc c * (m : ℝ) ^ (a - b) ≤ c * ((m * n : ℤ) : ℝ) ^ (a - b) := by
          push_cast
          have h1 : (m : ℝ) ≤ m * n := by
            nlinarith [mul_le_mul_of_nonneg_left hnR (by linarith : (0 : ℝ) ≤ m)]
          gcongr
      _ < (relativeGenericRank πX ((m * n) • D).divisorialSheaf : ℝ) := hk (m * n) hmn
      _ ≤ _ := by exact_mod_cast hrank

end Helpers

section RetainedFloor

variable {k : Type u} [Field k] {X₀ X : Scheme.{u}}
  [IsIntegral X₀] [IsLocallyNoetherian X₀] [IsNormal X₀] [CompactSpace X₀]
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- **An ample divisor stays big on a retained divisor.** Let `φ : X⁰ ⤏ X` be a birational map
(with inverse `ψ`) of normal projective varieties over `k`, with `X` `ℚ`-factorial, mapping the
normal prime divisor `S⁰` of `X⁰` to the normal prime divisor `S` of `X`, and extracting only
finitely many prime divisors of `X`, whose valuations have order zero on `A⁰`. If `A⁰` is an
effective ample `ℚ`-divisor of which `S⁰` is not a component, then `S ⊄ Supp (φ_* A⁰)` and the
restriction `(φ_* A⁰)|_S` is effective and big. -/
@[mmp "lem_fourfold_ample_sections_on_retained_floor"]
public theorem isRelativelyBig_pullback_transformDivisor_of_isAmple
    (sX₀ : X₀ ⟶ Spec (.of k)) (sX : X ⟶ Spec (.of k))
    (hX₀ : IsNormalVariety k sX₀) (hX₀p : Mori.IsProjectiveVariety k sX₀)
    (hXQ : IsQFactorial sX) (hXp : Mori.IsProjectiveVariety k sX)
    (S₀ : Mori.PrimeDivisor X₀) [IsNormal S₀.idealSheaf.subscheme]
    (A₀ : QDivisor X₀) (hA₀ : 0 ≤ A₀) (hAamp : A₀.IsAmple) (hAS : A₀.coeff S₀ = 0)
    (φ : X₀.RationalMap X) (ψ : X.RationalMap X₀) (hψ : Mori.RationalMap.IsInverse φ ψ)
    (hφk : MMP.Flips.RationalMap.IsOver sX₀ sX φ) (hψk : MMP.Flips.RationalMap.IsOver sX sX₀ ψ)
    (S : Mori.PrimeDivisor X) [IsNormal S.idealSheaf.subscheme]
    (hS : Mori.RationalMap.transformPrimeDivisor φ S₀ = some S)
    (hfin : {F : Mori.PrimeDivisor X | MMP.Flips.RationalMap.IsInverseExceptional φ F}.Finite)
    (hord : ∀ F : Mori.PrimeDivisor X, MMP.Flips.RationalMap.IsInverseExceptional φ F →
      ∀ g : X.PartialMap X₀, g.toRationalMap = ψ → ∀ hF : F.genericPoint ∈ g.domain,
        g.hom ⟨F.genericPoint, hF⟩ ∉ (A₀.supp : Set X₀)) :
    haveI := S.integral
    haveI := S.idealSheaf.isLocallyNoetherian_subscheme
    ∃ hB : ∀ Z : irreducibleComponents S.idealSheaf.subscheme,
        S.idealSheaf.subschemeι (componentGenericPoint _ Z) ∉
          (Mori.RationalMap.transformDivisor φ A₀).supp,
      ∃ B : QDivisor S.idealSheaf.subscheme,
        QDivisor.IsPullback S.idealSheaf.subschemeι (Mori.RationalMap.transformDivisor φ A₀) hB B ∧
          0 ≤ B ∧ B.IsRelativelyBig (S.idealSheaf.subschemeι ≫ sX) := by
  haveI := S.integral
  haveI := S.idealSheaf.isLocallyNoetherian_subscheme
  haveI : IsProper sX₀ := isProper_of_isProjectiveMorphism sX₀ hX₀p.isProjective
  haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hXp.isProjective
  haveI : Scheme.IsSeparated X₀ := ⟨isSeparated_terminal_of_isSeparated sX₀⟩
  haveI : Scheme.IsSeparated X := ⟨isSeparated_terminal_of_isSeparated sX⟩
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : CompactSpace S.idealSheaf.subscheme :=
    S.idealSheaf.subschemeι.isClosedEmbedding.compactSpace
  -- `S` is not a component of `φ_* A⁰`, since `S⁰` is not a component of `A⁰`
  have hB := subschemeι_componentGenericPoint_notMem S
    (genericPoint_notMem_supp_transformDivisor hψ hS A₀ hAS)
  -- `φ_* A⁰` is `ℚ`-Cartier, `X` being `ℚ`-factorial
  have hAq := isQCartier_of_isQFactorial sX hXQ (Mori.RationalMap.transformDivisor φ A₀)
  obtain ⟨B, hBp, -⟩ := QDivisor.IsQCartier.existsUnique_isPullback hAq hB
  exact ⟨hB, B, hBp, nonneg_of_isPullback (mapPrimeDivisors_nonneg _ hA₀) hAq hBp,
    isRelativelyBig_of_isPullback_transformDivisor sX₀ sX hX₀ hX₀p hXQ hXp S₀ A₀ hA₀ hAamp hAS
      φ ψ hψ hφk hψk S hS hfin hord hB B hBp⟩

end RetainedFloor

section BirationalContraction

variable {k : Type u} [Field k] {X Y S : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-- **Birational pushforward preserves relative bigness.** Let `φ : X ⤏ Y` be a birational map
over a projective variety `S` (via `πX`, `πY`) of normal projective varieties, which is a
contraction (no prime divisor of `Y` is `φ⁻¹`-exceptional), with `Y` `ℚ`-factorial. If `A ≥ 0`
is a `ℚ`-Cartier `ℚ`-divisor on `X` which is big over `S`, then `G = φ_* A` is effective,
`ℚ`-Cartier and big over `S`. -/
@[mmp "lem_fourfold_pushforward_relative_ample_core_big"]
public theorem isRelativelyBig_transformDivisor_of_isBirationalContraction
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) (sS : S ⟶ Spec (.of k))
    (hX : IsNormalVariety k sX) (hXp : Mori.IsProjectiveVariety k sX)
    (hYQ : IsQFactorial sY) (hYp : Mori.IsProjectiveVariety k sY)
    (hS : Mori.IsProjectiveVariety k sS)
    (πX : X ⟶ S) (πY : Y ⟶ S) (hπX : πX ≫ sS = sX) (hπY : πY ≫ sS = sY)
    (φ : X.RationalMap Y) (hφ : Mori.RationalMap.IsBirational φ)
    (hover : MMP.Flips.RationalMap.IsOver πX πY φ)
    (hcontr : ∀ F : Mori.PrimeDivisor Y, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F)
    (A : QDivisor X) (hA0 : 0 ≤ A) (hAQ : A.IsQCartier) (hAbig : A.IsRelativelyBig πX) :
    0 ≤ Mori.RationalMap.transformDivisor φ A ∧
      QDivisor.IsQCartier (Mori.RationalMap.transformDivisor φ A) ∧
      QDivisor.IsRelativelyBig πY (Mori.RationalMap.transformDivisor φ A) :=
  ⟨mapPrimeDivisors_nonneg _ hA0, MMP.Fourfold.isQCartier_of_isQFactorial sY hYQ _,
    isRelativelyBig_transformDivisor_of_isBirational sX sY sS hX hXp hYQ hYp hS πX πY hπY φ hφ hover
      hcontr A hAbig⟩

end BirationalContraction

end MMP.Fourfold

end
