module

public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Dimension
public import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeSections
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Divisor.SmoothRDivisors
import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion

/-!
# Multiplier ideals of effective divisors are ideal sheaves (Lazarsfeld §9.1.B, §9.2)

Let `μ : X' ⟶ X` be a proper birational morphism of varieties over a field `k`, with `X'`
non-singular and `X` normal. The relative canonical divisor `K_{X'/X}` is effective and its
prime components lie in the exceptional locus of `μ`, so `μ_*𝒪_{X'}(K_{X'/X}) = 𝒪_X` inside
`K(X) = K(X')`. For an effective divisor `N` on `X'` it follows that
`μ_*𝒪_{X'}(K_{X'/X} - N) ⊆ 𝒪_X`, and this subsheaf is a quasi-coherent (indeed coherent) ideal
sheaf of `𝒪_X`.

If moreover `X` is non-singular, `D` is an effective `ℝ`-divisor on `X` and `μ` is a log
resolution of `D`, then `⌊μ^*D⌋ ≥ 0`, so the multiplier ideal
`𝒥_μ(X, D) = μ_*𝒪_{X'}(K_{X'/X} - ⌊μ^*D⌋)`, a priori an `𝒪_X`-submodule of `K(X)`, is an
ideal sheaf of `𝒪_X`.

## Main results

* `MMP.Intersection.IsRelativeCanonicalDivisor.multiplierIdealSections_eq_range`:
  `μ_*𝒪_{X'}(K_{X'/X}) = 𝒪_X` inside `K(X)`.
* `MMP.Intersection.IsRelativeCanonicalDivisor.exists_idealSheafData_multiplierIdealSections_sub`:
  `μ_*𝒪_{X'}(K_{X'/X} - N) ⊆ 𝒪_X`, and it is the ideal sheaf of some
  `AlgebraicGeometry.Scheme.IdealSheafData` of `X`.
* `MMP.Intersection.IsMultiplierIdealOn.exists_idealSheafData`: for effective `D`, the sections
  of `𝒥_μ(X, D)` are regular functions, and they are the sections of an
  `AlgebraicGeometry.Scheme.IdealSheafData` of `X` on every non-empty affine open.

## Implementation notes

* `μ_*𝒪_{X'}(G)` is given by its sections over the opens `U ⊆ X`, as subsets of `K(X)`
  (`MMP.Intersection.multiplierIdealSections`), and `𝒪_X` by the images
  `AlgebraicGeometry.Scheme.germToFunctionField` of the regular functions on `U`.
* An ideal sheaf of `𝒪_X` is an `AlgebraicGeometry.Scheme.IdealSheafData`, quasi-coherent by
  construction and determined by its ideals on affine opens. On the locally Noetherian `X` every
  such ideal sheaf is coherent (`MMP.Flips.isCoherent_idealModule`), so coherence is not
  restated. The ideal sheaf is built directly: on an affine open `U` it consists of the
  `a ∈ Γ(X, U)` with `v_P(μ^* a) ≤ exp (coeff_P G)` for every prime divisor `P` of `X'` whose
  centre lies in `U`. It is compatible with a basic open `D(f) ⊆ U`: a section on `D(f)` is
  `y / f ^ n` with `y` regular on `U`, `v_P(μ^* f) < 1` whenever the centre of `P` lies outside
  `D(f)`, and so `f ^ m y` satisfies the conditions on `U` once `-m` bounds the coefficients of
  `G` from below.
* Non-singularity of `X` is not needed for the first two results: they hold for `X` normal.
* Effectivity of `D` is effectivity of its Weil `ℝ`-divisor
  (`MMP.Intersection.WeilRDivisor.IsEffective`); on the non-singular `X` it gives an effective
  representation `D = ∑ dⱼ Bⱼ`. The pull-back `μ^*D` is given relative to an arbitrary
  representation `D = ∑ cᵢ Aᵢ`; its order along a prime divisor `P` of `X'` is
  `∑ cᵢ ord_P(μ^* Aᵢ)`, where `A ↦ ord_P(μ^* A)` is the order at `η_P` of `μ^*` of a local
  equation of `A` at `μ(η_P)`. This is independent of the local equation and additive in `A`,
  hence extends to a `ℤ`-linear map `Div(X) ⊗ ℝ → ℝ`, and evaluating it on the effective
  representation shows that it is non-negative.

## References

* [Laz04] R. Lazarsfeld, *Positivity in Algebraic Geometry II*, §9.1.B, (9.2), Def. 9.2.1.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Intersection

open MMP.Mori (Divisor RDivisor)

/-! ### The push-forward of `𝒪_{X'}(K_{X'/X})` -/

/-- The Weil divisor of an effective Cartier divisor on a locally Noetherian integral scheme is
effective. -/
private theorem coeff_nonneg_of_isEffective {X : Scheme} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {K : X.CartierDivisor} (hK : IsEffective K)
    {wK : Divisor X}
    (hw : IsWeilDivisorOfCartier K wK) (P : MMP.Mori.PrimeDivisor X) : 0 ≤ wK.coeff P := by
  obtain ⟨U, hη, s, hs, hloc⟩ := hK (MMP.Mori.PrimeDivisor.genericPoint P)
  have hf : IsLocalEquationAt K _ (X.totalQuotientSheaf.presheaf.germ U _ hη (hs.unit : _)) :=
    ⟨U, hη, hs.unit, hloc, rfl⟩
  have hne := totalQuotientStalkToFunctionField_ne_zero_of_isLocalEquationAt hf
  rw [← ord_eq_coeff_of_isLocalEquationAt hw P rfl hf]
  refine (Scheme.mem_range_algebraMap_stalk_iff_zero_le_ord
    (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P) hne).mp ⟨X.presheaf.germ U _ hη s, ?_⟩
  rw [IsUnit.unit_spec, germ_toTotalQuotient,
    totalQuotientStalkToFunctionField_stalkToTotalQuotient]

section RelativeCanonical

variable {k : Type u} [Field k] {X X' : Scheme.{u}}
variable [X.Over (Spec (.of k))] [X'.Over (Spec (.of k))]

/-- **`μ_*𝒪_{X'}(K_{X'/X}) = 𝒪_X`** (Lazarsfeld §9.1.B). Let `μ : X' ⟶ X` be a proper birational
morphism of varieties over `k`, with `X'` non-singular and `X` normal, let `K` be the relative
canonical divisor `K_{X'/X}` and `wK` its Weil divisor. Then over every non-empty open `U ⊆ X`
the sections of `μ_*𝒪_{X'}(K_{X'/X})`, as rational functions on `X`, are exactly the regular
functions on `U`. -/
@[mmp "lem_p09a_relative_canonical_pushforward"]
public theorem IsRelativeCanonicalDivisor.multiplierIdealSections_eq_range
    [MMP.Mori.IsVariety k (X ↘ Spec (.of k))] [MMP.Mori.IsVariety k (X' ↘ Spec (.of k))]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    (hsm : MMP.Mori.IsSmoothScheme (X' ↘ Spec (.of k)))
    {μ : X' ⟶ X} [μ.IsOver (Spec (.of k))] [IsProper μ] (hμ : MMP.Mori.IsBirationalMorphism μ)
    [IsDominant μ] {K : X'.CartierDivisor} (hK : IsRelativeCanonicalDivisor (X ↘ Spec (.of k)) μ K)
    {wK : Divisor X'} (hw : IsWeilDivisorOfCartier K wK) (U : X.Opens) [Nonempty U] :
    multiplierIdealSections μ wK U = Set.range (X.germToFunctionField U) := by
  have hcomp : μ ≫ (X ↘ Spec (.of k)) = X' ↘ Spec (.of k) := comp_over μ _
  have : MMP.Mori.IsVariety k (μ ≫ (X ↘ Spec (.of k))) := hcomp ▸ inferInstance
  exact multiplierIdealSections_eq_range_of_exceptional (k := k) hμ
    (coeff_nonneg_of_isEffective (hK.isEffective _ hμ) hw)
    (fun _ hP => hK.support_subset_exceptionalLocus _ (hcomp ▸ hsm) hμ hw hP) U

end RelativeCanonical

/-! ### `μ_*𝒪_{X'}(K_{X'/X} - N)` is an ideal sheaf -/

section Ideal

variable {X X' : Scheme.{u}} [IsIntegral X] [IsIntegral X'] [IsLocallyNoetherian X']
  [IsNormal X'] (μ : X' ⟶ X) [IsDominant μ]

/-- The valuation `v_P(μ^* ·)` on the stalk of `X` at the centre `μ(η_P)` is at most `1`. -/
private theorem val_stalk_le_one (P : MMP.Mori.PrimeDivisor X')
    (a : X.presheaf.stalk (μ P.genericPoint)) :
    P.valuationOver μ (algebraMap _ X.functionField a) ≤ 1 := by
  rw [MMP.Mori.PrimeDivisor.valuationOver_apply,
    MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff,
    MMP.Mori.functionFieldMap_algebraMap_stalk]
  exact ⟨_, rfl⟩

/-- A non-unit of the stalk of `X` at the centre `μ(η_P)` has `v_P(μ^* ·) < 1`. -/
private theorem val_stalk_lt_one (P : MMP.Mori.PrimeDivisor X')
    (a : X.presheaf.stalk (μ P.genericPoint)) (ha : ¬ IsUnit a) :
    P.valuationOver μ (algebraMap _ X.functionField a) < 1 := by
  rw [MMP.Mori.PrimeDivisor.valuationOver_apply, MMP.Mori.functionFieldMap_algebraMap_stalk,
    MMP.Mori.PrimeDivisor.divisorialValuation_algebraMap_lt_one_iff]
  exact (IsLocalRing.mem_maximalIdeal _).mpr fun h => ha (isUnit_of_map_unit _ _ h)

/-- In `ℤᵐ⁰`, an element below `1` is at most `exp (-1)`. -/
private theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (hx : x < 1) :
    x ≤ WithZero.exp (-1) := by
  rcases eq_or_ne x 0 with rfl | h0
  · exact zero_le'
  rw [← WithZero.exp_log h0] at hx ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
  rw [WithZero.exp_le_exp]
  omega

/-- The regular functions `a` on `U` with `v_P(μ^* a) ≤ exp (coeff_P G)` at every prime divisor
`P` whose generic point maps into `U`. -/
private def valIdeal (G : Divisor X') (U : X.Opens) : Ideal Γ(X, U) where
  carrier := {a | ∀ (P : MMP.Mori.PrimeDivisor X') (hP : μ P.genericPoint ∈ U),
    P.valuationOver μ (algebraMap _ X.functionField (X.presheaf.germ U _ hP a)) ≤
      WithZero.exp (G.coeff P)}
  add_mem' {a b} ha hb P hP := by
    rw [map_add, map_add]
    exact (Valuation.map_add _ _ _).trans (max_le (ha P hP) (hb P hP))
  zero_mem' P hP := by simp
  smul_mem' c a ha P hP := by
    rw [smul_eq_mul, map_mul, map_mul, Valuation.map_mul]
    exact (mul_le_of_le_one_left' (val_stalk_le_one μ P _)).trans (ha P hP)

/-- Some `m : ℕ` bounds every coefficient of `G` from below by `-m`. -/
private theorem exists_neg_le_coeff (G : Divisor X') : ∃ m : ℕ, ∀ P, -(m : ℤ) ≤ G.coeff P := by
  refine ⟨∑ P ∈ G.support, (G.coeff P).natAbs, fun P => ?_⟩
  by_cases hP : P ∈ G.support
  · have := Finset.single_le_sum (f := fun P => (G.coeff P).natAbs) (fun _ _ => Nat.zero_le _) hP
    omega
  · rw [MMP.Mori.DivisorWithCoeffs.coeff_apply, Finsupp.notMem_support_iff.mp hP]
    omega

/-- If `y|_{D(f)} = f ^ n b` with `b` in the ideal on `D(f)`, then `f ^ m y` lies in the ideal on
`U` as soon as `-m` bounds the coefficients of `G` from below: at a prime divisor whose centre lies
outside `D(f)`, `v_P(μ^* f) ≤ exp (-1)`, so `v_P(μ^* f) ^ m ≤ exp (-m) ≤ exp (coeff_P G)`. -/
private theorem pow_mul_mem_valIdeal {G : Divisor X'} {U : X.Opens} {f y : Γ(X, U)}
    {b : Γ(X, X.basicOpen f)} {n m : ℕ} (hb : b ∈ valIdeal μ G (X.basicOpen f))
    (hy : y |_ X.basicOpen f = (f |_ X.basicOpen f) ^ n * b) (hm : ∀ P, -(m : ℤ) ≤ G.coeff P) :
    f ^ m * y ∈ valIdeal μ G U := by
  intro P hP
  rw [map_mul, map_mul, Valuation.map_mul, map_pow, map_pow, Valuation.map_pow]
  by_cases hf : μ P.genericPoint ∈ X.basicOpen f
  · refine (mul_le_of_le_one_left' (pow_le_one' (val_stalk_le_one μ P _) m)).trans ?_
    have h2 : X.presheaf.germ _ _ hP y = X.presheaf.germ _ _ hP f ^ n *
        X.presheaf.germ _ _ hf b := by
      rw [← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (X.basicOpen_le f)) _ hf,
        ← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (X.basicOpen_le f)) _ hf,
        ← map_pow, ← map_mul]
      exact congrArg _ hy
    rw [h2, map_mul, Valuation.map_mul, map_pow, Valuation.map_pow]
    exact (mul_le_of_le_one_left' (pow_le_one' (val_stalk_le_one μ P _) n)).trans (hb P hf)
  · have hle := le_exp_neg_one_of_lt_one (val_stalk_lt_one μ P (X.presheaf.germ _ _ hP f)
      (by rwa [← X.mem_basicOpen f _ hP]))
    refine (mul_le_of_le_one_right' (val_stalk_le_one μ P _)).trans
      ((pow_le_pow_left₀ zero_le' hle m).trans ?_)
    rw [← WithZero.exp_nsmul, WithZero.exp_le_exp]
    simpa using hm P

/-- The ideal sheaf of `X` whose ideal on an affine open `U` is `valIdeal μ G U`. -/
private def valIdealSheaf (G : Divisor X') : X.IdealSheafData where
  ideal U := valIdeal μ G U
  map_ideal_basicOpen U f := by
    change _ = valIdeal μ G (X.basicOpen f)
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha P hP
      change P.valuationOver μ (algebraMap _ X.functionField
        (X.presheaf.germ _ _ hP ((X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom a))) ≤ _
      rw [TopCat.Presheaf.germ_res_apply]
      exact ha P (X.basicOpen_le f hP)
    · intro b hb
      obtain ⟨n, y, hy⟩ := exists_eq_pow_mul_of_isAffineOpen X U U.2 f b
      obtain ⟨m, hm⟩ := exists_neg_le_coeff G
      have hin := Ideal.mem_map_of_mem (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
        (pow_mul_mem_valIdeal μ hb hy hm)
      rw [map_mul, map_pow] at hin
      change _ * (y |_ X.basicOpen f) ∈ _ at hin
      rw [hy, ← mul_assoc] at hin
      have hu := X.toRingedSpace.isUnit_res_basicOpen f
      exact (Ideal.unit_mul_mem_iff_mem _ ((hu.pow m).mul (hu.pow n))).mp hin

end Ideal

section MinusEffective

variable {k : Type u} [Field k] {X X' : Scheme.{u}}
variable [X.Over (Spec (.of k))] [X'.Over (Spec (.of k))]

/-- **`μ_*𝒪_{X'}(K_{X'/X} - N)` is an ideal sheaf of `𝒪_X`** (Lazarsfeld (9.2)). Let
`μ : X' ⟶ X` be a proper birational morphism of varieties over `k`, with `X'` non-singular and
`X` normal, let `K` be the relative canonical divisor `K_{X'/X}`, `wK` its Weil divisor, and `N`
an effective divisor on `X'`. Then over every non-empty open `U ⊆ X` the sections of
`μ_*𝒪_{X'}(K_{X'/X} - N)` are regular functions on `U`, and there is an ideal sheaf `I` of `X`
whose ideal on each non-empty affine open `U` is exactly these sections. -/
@[mmp "lem_p09a_pushforward_relative_canonical_minus_effective"]
public theorem IsRelativeCanonicalDivisor.exists_idealSheafData_multiplierIdealSections_sub
    [MMP.Mori.IsVariety k (X ↘ Spec (.of k))] [MMP.Mori.IsVariety k (X' ↘ Spec (.of k))]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    (hsm : MMP.Mori.IsSmoothScheme (X' ↘ Spec (.of k)))
    {μ : X' ⟶ X} [μ.IsOver (Spec (.of k))] [IsProper μ] (hμ : MMP.Mori.IsBirationalMorphism μ)
    [IsDominant μ] {K : X'.CartierDivisor} (hK : IsRelativeCanonicalDivisor (X ↘ Spec (.of k)) μ K)
    {wK : Divisor X'} (hw : IsWeilDivisorOfCartier K wK) {N : Divisor X'} (hN : 0 ≤ N) :
    (∀ (U : X.Opens) [Nonempty U],
      multiplierIdealSections μ (wK - N) U ⊆ Set.range (X.germToFunctionField U)) ∧
    ∃ I : X.IdealSheafData, ∀ (U : X.affineOpens) [Nonempty (U : X.Opens)],
      multiplierIdealSections μ (wK - N) U =
        X.germToFunctionField (U : X.Opens) '' (I.ideal U : Set Γ(X, U)) := by
  have hsub : ∀ (U : X.Opens) [Nonempty U],
      multiplierIdealSections μ (wK - N) U ⊆ Set.range (X.germToFunctionField U) := by
    intro U _ g ⟨h0, hg⟩
    rw [← IsRelativeCanonicalDivisor.multiplierIdealSections_eq_range hsm hμ hK hw U]
    exact ⟨h0, fun P hP => (hg P hP).trans (WithZero.exp_le_exp.mpr (sub_le_self _ (hN P)))⟩
  refine ⟨hsub, valIdealSheaf μ (wK - N), fun U _ => ?_⟩
  have hne : μ ⁻¹ᵁ (U : X.Opens) ≠ ⊥ := by
    obtain ⟨u⟩ := ‹Nonempty (U : X.Opens)›
    obtain ⟨_, hx', x', rfl⟩ :=
      μ.denseRange.inter_open_nonempty _ (U : X.Opens).isOpen ⟨u.1, u.2⟩
    exact (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mpr ⟨x', hx'⟩
  ext g
  constructor
  · intro hg
    obtain ⟨a, rfl⟩ := hsub U hg
    refine ⟨a, fun P hP => ?_, rfl⟩
    have := hg.2 P (support_inter_nonempty_of_genericPoint_mem P (V := μ ⁻¹ᵁ (U : X.Opens)) hP)
    rwa [← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hP] at this
  · rintro ⟨a, ha, rfl⟩
    refine ⟨fun h => absurd h hne, fun P hP => ?_⟩
    have hη : μ P.genericPoint ∈ (U : X.Opens) := genericPoint_mem_of_support_inter_nonempty P hP
    rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hη]
    exact ha P hη

end MinusEffective

/-! ### Multiplier ideals of effective divisors -/

section Multiplier

variable {k : Type u} [Field k] {X X' : Scheme.{u}}

section PullOrd

variable [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral X'] [IsLocallyNoetherian X']
  [IsNormal X'] (μ : X' ⟶ X) [IsDominant μ] (P : MMP.Mori.PrimeDivisor X')

omit [IsLocallyNoetherian X'] [IsNormal X'] in
private theorem functionFieldMap_algebraMap_ne_zero {x : X} {a : X.presheaf.stalk x}
    (ha : a ≠ 0) : functionFieldMap μ (algebraMap _ X.functionField a) ≠ 0 :=
  (map_ne_zero _).2 (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero ha))

/-- `ord_P(μ^* a) ≥ 0` for `a` regular at the centre `μ(η_P)`. -/
private theorem ord_functionFieldMap_algebraMap_nonneg {a : X.presheaf.stalk (μ P.genericPoint)}
    (ha : a ≠ 0) :
    0 ≤ X'.ord (functionFieldMap μ (algebraMap _ X.functionField a)) P.genericPoint := by
  have hne := functionFieldMap_algebraMap_ne_zero μ ha
  have h1 : P.divisorialValuation (functionFieldMap μ (algebraMap _ X.functionField a)) ≤ 1 := by
    rw [MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff,
      MMP.Mori.functionFieldMap_algebraMap_stalk]
    exact ⟨_, rfl⟩
  rw [P.divisorialValuation_eq_exp_neg_ord hne, ← WithZero.exp_zero,
    WithZero.exp_le_exp] at h1
  omega

/-- `ord_P(μ^* w) = 0` for `w` a unit at the centre `μ(η_P)`. -/
private theorem ord_functionFieldMap_algebraMap_unit
    (w : (X.presheaf.stalk (μ P.genericPoint))ˣ) :
    X'.ord (functionFieldMap μ (algebraMap _ X.functionField
      (w : X.presheaf.stalk (μ P.genericPoint)))) P.genericPoint = 0 := by
  have h1 := ord_functionFieldMap_algebraMap_nonneg μ P w.ne_zero
  have h2 := ord_functionFieldMap_algebraMap_nonneg μ P (w⁻¹).ne_zero
  have h3 := Scheme.ord_mul (x := P.genericPoint) (functionFieldMap_algebraMap_ne_zero μ w.ne_zero)
    (functionFieldMap_algebraMap_ne_zero μ (w⁻¹).ne_zero)
  rw [← map_mul, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one,
    map_one] at h3
  have h4 := Scheme.ord_mul (X := X') (x := P.genericPoint) (one_ne_zero (α := X'.functionField))
    one_ne_zero
  rw [mul_one] at h4
  omega

/-- The order along `P` of a pull-back of a local equation at the centre `μ(η_P)`. -/
private noncomputable def pullOrdFun (A : X.CartierDivisor) : ℤ :=
  X'.ord (functionFieldMap μ (totalQuotientStalkToFunctionField (μ P.genericPoint)
    (exists_isLocalEquationAt A (μ P.genericPoint)).choose)) P.genericPoint

private theorem functionFieldMap_ne_zero_of_isLocalEquationAt {A : X.CartierDivisor}
    {g : X.totalQuotientSheaf.presheaf.stalk (μ P.genericPoint)}
    (hg : IsLocalEquationAt A (μ P.genericPoint) g) :
    functionFieldMap μ (totalQuotientStalkToFunctionField _ g) ≠ 0 :=
  (map_ne_zero _).2 (totalQuotientStalkToFunctionField_ne_zero_of_isLocalEquationAt hg)

private theorem pullOrdFun_eq {A : X.CartierDivisor}
    {g : X.totalQuotientSheaf.presheaf.stalk (μ P.genericPoint)}
    (hg : IsLocalEquationAt A (μ P.genericPoint) g) :
    pullOrdFun μ P A =
      X'.ord (functionFieldMap μ (totalQuotientStalkToFunctionField _ g)) P.genericPoint := by
  have h₀ := (exists_isLocalEquationAt A (μ P.genericPoint)).choose_spec
  obtain ⟨w, hw⟩ := h₀.exists_eq_mul_units hg
  rw [hw, map_mul, totalQuotientStalkToFunctionField_stalkToTotalQuotient, map_mul,
    Scheme.ord_mul (functionFieldMap_ne_zero_of_isLocalEquationAt μ P h₀)
      (functionFieldMap_algebraMap_ne_zero μ w.ne_zero),
    ord_functionFieldMap_algebraMap_unit, add_zero]
  rfl

/-- `A ↦ ord_P(μ^* A)`, an additive map on Cartier divisors of `X`. -/
private noncomputable def pullOrd : X.CartierDivisor →+ ℤ :=
  AddMonoidHom.mk' (pullOrdFun μ P) fun A B => by
    have hA := (exists_isLocalEquationAt A (μ P.genericPoint)).choose_spec
    have hB := (exists_isLocalEquationAt B (μ P.genericPoint)).choose_spec
    rw [pullOrdFun_eq μ P (hA.add hB), map_mul, map_mul,
      Scheme.ord_mul (functionFieldMap_ne_zero_of_isLocalEquationAt μ P hA)
        (functionFieldMap_ne_zero_of_isLocalEquationAt μ P hB)]
    rfl

private theorem pullOrd_nonneg {A : X.CartierDivisor} (hA : IsEffective A) :
    0 ≤ pullOrd μ P A := by
  obtain ⟨U, hxU, s, hs, hsA⟩ := hA (μ P.genericPoint)
  have hf : IsLocalEquationAt A (μ P.genericPoint)
      (stalkToTotalQuotient _ (X.presheaf.germ U (μ P.genericPoint) hxU s)) :=
    ⟨U, hxU, hs.unit, hsA, germ_toTotalQuotient hxU s⟩
  have hne := totalQuotientStalkToFunctionField_ne_zero_of_isLocalEquationAt hf
  rw [totalQuotientStalkToFunctionField_stalkToTotalQuotient] at hne
  change 0 ≤ pullOrdFun μ P A
  rw [pullOrdFun_eq μ P hf, totalQuotientStalkToFunctionField_stalkToTotalQuotient]
  exact ord_functionFieldMap_algebraMap_nonneg μ P fun h => hne (by rw [h, map_zero])

/-- The order along a prime divisor `P` is the order at `η_P` of a local equation there. -/
private theorem ord_eq_of_isOrderAlong {G : X'.CartierDivisor} {N : ℤ}
    (hGP : IsOrderAlong G (primeDivisorSubvariety P) N)
    {f : X'.totalQuotientSheaf.presheaf.stalk P.genericPoint}
    (hf : IsLocalEquationAt G P.genericPoint f) :
    X'.ord (totalQuotientStalkToFunctionField P.genericPoint f) P.genericPoint = N := by
  rw [← cartierMultiplicity_eq_ord_of_isLocalEquationAt hf]
  unfold IsOrderAlong at hGP
  dsimp only [primeDivisorSubvariety_genericPoint] at hGP
  obtain ⟨a, b, ha, hb, ⟨g, hg, hgab⟩, la, lb, hla, hlb, hN⟩ := hGP
  rw [cartierMultiplicity_eq_ord_of_isLocalEquationAt hg, hN]
  have hcoh : Order.coheight (MMP.Mori.PrimeDivisor.genericPoint P) = 1 :=
    AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap (X'.presheaf.stalk _) X'.functionField b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have key : totalQuotientStalkToFunctionField _ g *
      algebraMap (X'.presheaf.stalk _) X'.functionField b =
      algebraMap (X'.presheaf.stalk _) X'.functionField a := by
    have := congrArg (totalQuotientStalkToFunctionField _) hgab.2
    rw [map_mul, totalQuotientStalkToFunctionField_stalkToTotalQuotient,
      totalQuotientStalkToFunctionField_stalkToTotalQuotient] at this
    exact (mul_comm _ _).trans this
  have hTg := totalQuotientStalkToFunctionField_ne_zero_of_isLocalEquationAt hg
  have hord := X'.ord_mul (x := MMP.Mori.PrimeDivisor.genericPoint P) hTg hbK
  rw [key, ord_algebraMap_stalk _ hcoh a ha0, ord_algebraMap_stalk _ hcoh b hb0] at hord
  erw [hla, hlb, ENat.toNat_coe, ENat.toNat_coe] at hord
  omega

/-- `ord_P(A') = ord_P(μ^* A)` for a pull-back `A'` of `A`. -/
private theorem primeDivisorOrder_eq_pullOrd {A : X.CartierDivisor} {A' : X'.CartierDivisor}
    (h : MMP.Intersection.IsPullback μ A A') : primeDivisorOrder P A' = pullOrd μ P A := by
  obtain ⟨a, b, ⟨g, hg, hab⟩, -, hb', g', hg', hab'⟩ := h.2 P.genericPoint
  have hbK : algebraMap (X'.presheaf.stalk _) X'.functionField (μ.stalkMap _ b) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb'
  have e1 := congrArg (fun t => functionFieldMap μ (totalQuotientStalkToFunctionField _ t)) hab.2
  have e2 := congrArg (totalQuotientStalkToFunctionField P.genericPoint) hab'.2
  simp only [map_mul, totalQuotientStalkToFunctionField_stalkToTotalQuotient,
    MMP.Mori.functionFieldMap_algebraMap_stalk] at e1 e2
  have key : totalQuotientStalkToFunctionField P.genericPoint g' =
      functionFieldMap μ (totalQuotientStalkToFunctionField _ g) :=
    mul_left_cancel₀ hbK (e2.trans e1.symm)
  rw [← ord_eq_of_isOrderAlong P (isOrderAlong_primeDivisorOrder A' P) hg', key]
  exact (pullOrdFun_eq μ P hg).symm

/-- The extension `Div_ℝ(X) → ℝ` of `pullOrd μ P`, `A ⊗ c ↦ c · ord_P(μ^* A)`. -/
private noncomputable def pullOrdR : RCartierDivisor X →ₗ[ℤ] ℝ :=
  TensorProduct.lift (LinearMap.mk₂ ℤ (fun (A : X.CartierDivisor) (r : ℝ) =>
      (pullOrd μ P A : ℝ) * r)
    (fun D₁ D₂ r => by rw [map_add, Int.cast_add, add_mul])
    (fun n D r => by rw [map_zsmul, zsmul_eq_mul, zsmul_eq_mul]; push_cast; ring)
    (fun D r₁ r₂ => mul_add _ _ _)
    (fun n D r => by rw [zsmul_eq_mul, zsmul_eq_mul]; ring))

private theorem pullOrdR_sum {m : ℕ} (c : Fin m → ℝ) (A : Fin m → X.CartierDivisor) :
    pullOrdR μ P (∑ i, A i ⊗ₜ c i) = ∑ i, (pullOrd μ P (A i) : ℝ) * c i := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => TensorProduct.lift.tmul _ _

/-- **Pull-backs of effective `ℝ`-divisors are effective.** For an effective `ℝ`-divisor `D` and a
Weil divisor `F` of a pull-back `μ^*D`, `ord_P(F) ≥ 0`: `ord_P(F) = ∑ cᵢ ord_P(μ^* Aᵢ)` for any
representation `D = ∑ cᵢ Aᵢ`, and computed on an effective representation every term is `≥ 0`. -/
private theorem coeff_nonneg_of_isWeilPullback {D : RCartierDivisor X}
    (hDeff : CartierDivisorWithCoeffs.IsEffective D) {F : RDivisor X'}
    (hF : IsWeilPullback μ D F) : 0 ≤ F.coeff P := by
  obtain ⟨m, c, A, D', ⟨hrep, -, A', hrep', hA'⟩, hD'⟩ := hF
  rw [hD'.coeff_eq_primeDivisorOrderR P, hrep', primeDivisorOrderR_sum]
  have e : ∑ i, (primeDivisorOrder P (A' i) : ℝ) * c i = pullOrdR μ P D := by
    rw [hrep, pullOrdR_sum]
    simp only [primeDivisorOrder_eq_pullOrd μ P (hA' _)]
  rw [e]
  obtain ⟨m', d, B, hrepB, hB⟩ := hDeff
  rw [hrepB, pullOrdR_sum]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (Int.cast_nonneg (pullOrd_nonneg μ P (hB i).2)) (hB i).1

end PullOrd

/-- On a non-singular variety an `ℝ`-divisor whose Weil divisor is effective is effective. -/
private theorem isEffective_of_isWeilRDivisorOf [IsIntegral X] {sX : X ⟶ Spec (.of k)}
    (hX : MMP.Mori.IsVariety k sX) (hsm : MMP.Mori.IsSmoothScheme sX)
    {D : RCartierDivisor X} {wD : RDivisor X} (hw : IsWeilRDivisorOf D wD)
    (hD : WeilRDivisor.IsEffective wD) : CartierDivisorWithCoeffs.IsEffective D := by
  letI : X.Over (Spec (.of k)) := ⟨sX⟩
  haveI : MMP.Mori.IsVariety k (X ↘ Spec (.of k)) := hX
  haveI : AlgebraicGeometry.IsVariety k sX := hX
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : IsNoetherian X := {}
  obtain ⟨n, hn⟩ : ∃ n : ℕ, topologicalKrullDim X = (n : WithBot ℕ∞) := by
    have hne := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sX
    have hbot : topologicalKrullDim X ≠ ⊥ := by
      rw [topologicalKrullDim, ne_eq, Order.krullDim_eq_bot_iff, not_isEmpty_iff]
      exact ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩⟩
    obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hbot
    rw [← hm] at hne
    have hm' : m ≠ ⊤ := fun h => hne (by rw [h]; rfl)
    obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hm'
    exact ⟨n, hm.symm⟩
  have hpd : IsPureDimensional X n := by
    intro Z hZ
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ
    subst hZ
    rw [(Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq, hn]
  have hsm' : MMP.Mori.IsSmoothScheme (X ↘ Spec (.of k)) := hsm
  refine (CartierDivisorWithCoeffs.isEffective_iff_of_isSmoothScheme (k := k) hpd hsm' D).2 ?_
  intro V
  have hcoh : Order.coheight V.1.genericPoint = 1 :=
    (subvarietyDim_add_one_eq_iff k hpd V.1).1 V.2
  let P := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh
  have hPV : primeDivisorSubvariety P = V.1 := Scheme.Subvariety.ext_genericPoint
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcoh)
  have h := hD P
  rw [hw.coeff_eq_primeDivisorOrderR P] at h
  obtain ⟨m, c, A, -, hrep, -, -⟩ := hw
  rw [hrep, primeDivisorOrderR_sum] at h
  rw [hrep, CartierDivisorWithCoeffs.weilDivisorTensorEquiv_cycleMap_sum]
  have e : ∀ i, cycleMap hpd (A i) V = primeDivisorOrder P (A i) := fun i => by
    rw [cycleMap_apply, orderAlong_eq_iff]
    have := isOrderAlong_primeDivisorOrder (A i) P
    rwa [hPV] at this
  simpa only [e] using h

/-- **The multiplier ideal of an effective divisor is an ideal sheaf** (Lazarsfeld Def. 9.2.1).
Let `X` be a non-singular variety over `k` (structure morphism `sX`), `D` an `ℝ`-divisor on `X`
with effective Weil `ℝ`-divisor `wD`, and `J = 𝒥_μ(X, D)` the multiplier ideal computed on a log
resolution `μ` of `D`. Then over every non-empty open `U` the sections of `J` are regular functions
on `U`, and there is an ideal sheaf `I` of `X` whose ideal on each non-empty affine open `U` is
exactly `J U`. -/
@[mmp "lem_p09a_multiplier_ideal_effective_is_ideal"]
public theorem IsMultiplierIdealOn.exists_idealSheafData [IsIntegral X]
    {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsVariety k sX) (hsm : MMP.Mori.IsSmoothScheme sX)
    {D : RCartierDivisor X} {wD : RDivisor X} (hw : IsWeilRDivisorOf D wD)
    (hD : WeilRDivisor.IsEffective wD) {μ : X' ⟶ X} {J : X.Opens → Set X.functionField}
    (hJ : IsMultiplierIdealOn sX D μ J) :
    (∀ (U : X.Opens) [Nonempty U], J U ⊆ Set.range (X.germToFunctionField U)) ∧
    ∃ I : X.IdealSheafData, ∀ (U : X.affineOpens) [Nonempty (U : X.Opens)],
      J U = X.germToFunctionField (U : X.Opens) '' (I.ideal U : Set Γ(X, U)) := by
  obtain ⟨⟨hproj, hbir, hX'var, hX'sm, -⟩, _, _, _, _, K, wK, F, hK, hwK, hF, rfl⟩ := hJ
  letI : X.Over (Spec (.of k)) := ⟨sX⟩
  letI : X'.Over (Spec (.of k)) := ⟨μ ≫ sX⟩
  haveI : MMP.Mori.IsVariety k (X ↘ Spec (.of k)) := hX
  haveI : MMP.Mori.IsVariety k (X' ↘ Spec (.of k)) := hX'var
  haveI : μ.IsOver (Spec (.of k)) := ⟨rfl⟩
  haveI : IsProper μ := isProper_of_isProjectiveMorphism μ hproj
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : IsNormal X := ⟨fun x => inferInstance, fun x => by
    haveI := uniqueFactorizationMonoid_stalk_of_isSmoothScheme
      (show MMP.Mori.IsSmoothScheme (X ↘ Spec (.of k)) from hsm) x
    infer_instance⟩
  have hN : 0 ≤ WeilRDivisor.roundDown F := by
    intro P
    change (0 : ℤ) ≤ (WeilRDivisor.roundDown F).coeff P
    rw [WeilRDivisor.coeff_roundDown, Int.floor_nonneg]
    exact coeff_nonneg_of_isWeilPullback μ P (isEffective_of_isWeilRDivisorOf hX hsm hw hD) hF
  exact IsRelativeCanonicalDivisor.exists_idealSheafData_multiplierIdealSections_sub
    (k := k) hX'sm hbir hK hwK hN

end Multiplier

end MMP.Intersection
