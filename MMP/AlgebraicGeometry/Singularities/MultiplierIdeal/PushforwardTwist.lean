module
public import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeSections

/-!
# Twisting a push-forward by an integral divisor (Lazarsfeld §9.2)

Let `μ : X' ⟶ X` be a dominant morphism of normal integral locally Noetherian schemes, `G` a Weil
divisor on `X'` and `A` a Cartier divisor on `X` with pull-back `μ^*A`. Then
`μ_*𝒪_{X'}(G + μ^*A) = 𝒪_X(A) · μ_*𝒪_{X'}(G)` as `𝒪_X`-submodules of `K(X)`.

## Main results

* `MMP.Intersection.multiplierIdealSections_add_pullback`

## Implementation notes

* `μ_*𝒪_{X'}(G)` is `MMP.Intersection.multiplierIdealSections μ G`, and `𝒪_X(A) ⊆ K(X)` is
  `MMP.Intersection.multiplierIdealSections (𝟙 X) [A]` for the Weil divisor `[A]` of `A`, which on
  the normal scheme `X` is the line bundle of `A`
  (`MMP.Intersection.mem_lineBundleSections_iff_forall_zero_le_ord_add`).
* The product `𝒪_X(A) · M` of `𝒪_X`-submodules of the constant sheaf `K(X)` is the sheaf image of
  `𝒪_X(A) ⊗ M`: its sections over `U` are the `g` which near every point `x ∈ U`, on some open
  `x ∈ V ⊆ U`, are finite sums of products `a m` with `a ∈ 𝒪_X(A)(V)`, `m ∈ M(V)` (and `g = 0`
  over `U = ∅`).
* Lazarsfeld's hypotheses that `X, X'` are non-singular varieties and `μ` is proper birational are
  used only through normality and dominance.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry Pointwise
open scoped WithZero

namespace MMP.Intersection

open MMP.Mori (Divisor)

variable {X X' : Scheme.{u}}

/-- The images in `K(X)` of the germs of a section of `𝓜_X` over `U` agree at all points of `U`. -/
private theorem totalQuotientStalkToFunctionField_germ_eq [IsIntegral X] [IsLocallyNoetherian X]
    {U : X.Opens} (s : X.totalQuotientSheaf.obj.obj (Opposite.op U)) {z z' : X} (hz : z ∈ U)
    (hz' : z' ∈ U) :
    totalQuotientStalkToFunctionField z (X.totalQuotientSheaf.presheaf.germ U z hz s) =
      totalQuotientStalkToFunctionField z' (X.totalQuotientSheaf.presheaf.germ U z' hz' s) := by
  have key : ∀ (y : X) (hy : y ∈ U),
      totalQuotientStalkToFunctionField y (X.totalQuotientSheaf.presheaf.germ U y hy s) =
        totalQuotientStalkToFunctionField (genericPoint X)
          (X.totalQuotientSheaf.presheaf.germ U (genericPoint X)
            (((genericPoint_spec X).specializes trivial : genericPoint X ⤳ y).mem_open
              U.isOpen hy) s) := by
    intro y hy
    have h : genericPoint X ⤳ y := (genericPoint_spec X).specializes trivial
    rw [← totalQuotientStalkToFunctionField_stalkSpecializes h]
    congr 1
    exact ConcreteCategory.congr_hom
      (TopCat.Presheaf.germ_stalkSpecializes X.totalQuotientSheaf.presheaf hy h) s
  rw [key z hz, key z' hz']

/-- A fraction `f = a / b` of `𝓜_{X,x}` maps to `a / b` in `K(X)`. -/
private theorem totalQuotientStalkToFunctionField_mul_of_isFraction [IsIntegral X]
    [IsLocallyNoetherian X] {x : X} {f : X.totalQuotientSheaf.presheaf.stalk x}
    {a b : X.presheaf.stalk x} (h : IsFraction f a b) :
    totalQuotientStalkToFunctionField x f * algebraMap _ X.functionField b =
      algebraMap _ X.functionField a := by
  have := congrArg (totalQuotientStalkToFunctionField x) h.2
  rw [map_mul, totalQuotientStalkToFunctionField_stalkToTotalQuotient,
    totalQuotientStalkToFunctionField_stalkToTotalQuotient] at this
  rwa [mul_comm]

/-- A unit of the local ring along a prime divisor has valuation one. -/
private theorem divisorialValuation_algebraMap_unit [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (P : MMP.Mori.PrimeDivisor X) (w : (X.presheaf.stalk P.genericPoint)ˣ) :
    P.divisorialValuation
      (algebraMap (X.presheaf.stalk P.genericPoint) X.functionField w) = 1 := by
  have h1 : ∀ r : X.presheaf.stalk P.genericPoint,
      P.divisorialValuation (algebraMap _ X.functionField r) ≤ 1 :=
    fun r => (P.divisorialValuation_le_one_iff _).mpr ⟨r, rfl⟩
  have hprod : P.divisorialValuation
      (algebraMap _ X.functionField (w : X.presheaf.stalk P.genericPoint)) *
      P.divisorialValuation
        (algebraMap _ X.functionField (↑w⁻¹ : X.presheaf.stalk P.genericPoint)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine le_antisymm (h1 _) ?_
  calc (1 : ℤᵐ⁰) = _ := hprod.symm
    _ ≤ _ * 1 := by
      gcongr
      exact h1 _
    _ = _ := mul_one _

/-- Near every point, `A` has a local equation `φ ∈ K(X)^*` on an open `V` whose valuation along
every prime divisor of `X` meeting `V` is `exp (-[A]_Q)`, and whose pull-back has valuation
`exp (-[A']_P)` along every prime divisor `P` of `X'` meeting `μ⁻¹ V`. -/
private theorem exists_localEquation_valuation [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] {μ : X' ⟶ X} [IsDominant μ]
    {A : X.CartierDivisor} {wA : Divisor X} (hA : IsWeilDivisorOfCartier A wA)
    {A' : X'.CartierDivisor} (hA' : IsPullback μ A A')
    {wA' : Divisor X'} (hwA' : IsWeilDivisorOfCartier A' wA') (x : X) :
    ∃ V : X.Opens, x ∈ V ∧ ∃ φ : X.functionField, φ ≠ 0 ∧
      (∀ Q : MMP.Mori.PrimeDivisor X, (Q.support ∩ V).Nonempty →
        Q.divisorialValuation φ = WithZero.exp (-wA.coeff Q)) ∧
      (∀ P : MMP.Mori.PrimeDivisor X', (P.support ∩ μ ⁻¹ᵁ V).Nonempty →
        P.valuationOver μ φ = WithZero.exp (-wA'.coeff P)) := by
  obtain ⟨-, U, hxU, g, hg, rfl⟩ := exists_isLocalEquationAt A x
  set φ := totalQuotientStalkToFunctionField x
    (X.totalQuotientSheaf.presheaf.germ U x hxU (g : _))
  have hφ0 : φ ≠ 0 :=
    totalQuotientStalkToFunctionField_ne_zero_of_isLocalEquationAt ⟨U, hxU, g, hg, rfl⟩
  have hloc : ∀ (z : X) (hz : z ∈ U), totalQuotientStalkToFunctionField z
      (X.totalQuotientSheaf.presheaf.germ U z hz (g : _)) = φ :=
    fun z hz => totalQuotientStalkToFunctionField_germ_eq _ hz hxU
  refine ⟨U, hxU, φ, hφ0, fun Q hQ => ?_, fun P hP => ?_⟩
  · have hη := genericPoint_mem_of_support_inter_nonempty Q hQ
    rw [MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hφ0, ← hloc _ hη,
      ord_eq_coeff_of_isLocalEquationAt hA Q rfl ⟨U, hη, g, hg, rfl⟩]
  · have hη : μ P.genericPoint ∈ U := genericPoint_mem_of_support_inter_nonempty P hP
    obtain ⟨a, b, ⟨g₀, hg₀, hfr₀⟩, -, hb, g₀', hg₀', hfr₀'⟩ := hA'.2 P.genericPoint
    have hfz : IsLocalEquationAt A (μ P.genericPoint)
        (X.totalQuotientSheaf.presheaf.germ U _ hη (g : _)) := ⟨U, hη, g, hg, rfl⟩
    obtain ⟨w, hw⟩ := hfz.exists_eq_mul_units hg₀
    have h1 := totalQuotientStalkToFunctionField_mul_of_isFraction hfr₀
    have h2 := totalQuotientStalkToFunctionField_mul_of_isFraction hfr₀'
    rw [hw, map_mul, hloc _ hη, totalQuotientStalkToFunctionField_stalkToTotalQuotient] at h1
    have h3 := congrArg (functionFieldMap μ) h1
    simp only [map_mul, MMP.Mori.functionFieldMap_algebraMap_stalk] at h3
    have hbne : algebraMap (X'.presheaf.stalk P.genericPoint) X'.functionField
        ((μ.stalkMap P.genericPoint).hom b) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have key : functionFieldMap μ φ * algebraMap (X'.presheaf.stalk P.genericPoint)
        X'.functionField ((μ.stalkMap P.genericPoint).hom w) =
        totalQuotientStalkToFunctionField _ g₀' :=
      mul_right_cancel₀ hbne (h3.trans h2.symm)
    have hv := congrArg P.divisorialValuation key
    rw [map_mul, MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _
      (totalQuotientStalkToFunctionField_ne_zero_of_isLocalEquationAt hg₀'),
      ord_eq_coeff_of_isLocalEquationAt hwA' P rfl hg₀'] at hv
    have hu := divisorialValuation_algebraMap_unit P
      (Units.map (μ.stalkMap P.genericPoint).hom.toMonoidHom w)
    rw [Units.coe_map] at hu
    rw [MMP.Mori.PrimeDivisor.valuationOver_apply, ← hv]
    erw [hu, mul_one]

/-- The preimage of an open containing a point under a dominant morphism is non-empty. -/
private theorem preimage_ne_bot (μ : X' ⟶ X) [IsDominant μ] {V : X.Opens} {x : X} (hx : x ∈ V) :
    μ ⁻¹ᵁ V ≠ ⊥ := by
  obtain ⟨_, hx', ⟨x', rfl⟩⟩ := μ.denseRange.inter_open_nonempty V V.isOpen ⟨x, hx⟩
  exact (TopologicalSpace.Opens.ne_bot_iff_nonempty _).2 ⟨x', hx'⟩

/-- A valuation bounded by `γ` on a set is bounded by `γ` on its `ℤ`-span. -/
private theorem valuation_le_of_mem_span {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {S : Set K} {γ : Γ}
    (hS : ∀ s ∈ S, v s ≤ γ) {g : K} (hg : g ∈ Submodule.span ℤ S) : v g ≤ γ := by
  induction hg using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => simp
  | add x y _ _ hx hy => exact v.map_add_le hx hy
  | smul n x _ hx =>
    induction n using Int.induction_on with
    | zero => simp
    | succ k hk =>
      rw [add_smul, one_smul]
      exact v.map_add_le hk hx
    | pred k hk =>
      rw [sub_smul, one_smul]
      exact v.map_sub_le hk hx

/-- **The converse bound.** If `h ∈ 𝒪_X([A])(V)` and `x = μ(η_P) ∈ V`, then the valuation of `h`
along `P` is at most `exp [A']_P`: with `φ` a local equation of `A` near `x`, the product `h φ` has
non-negative order along every prime divisor through `x`, hence is regular at `x` by normality,
so its pull-back is regular at `η_P`. -/
private theorem valuationOver_le_of_mem_twist [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] {μ : X' ⟶ X} [IsDominant μ]
    {A : X.CartierDivisor} {wA : Divisor X} (hA : IsWeilDivisorOfCartier A wA)
    {A' : X'.CartierDivisor} (hA' : IsPullback μ A A')
    {wA' : Divisor X'} (hwA' : IsWeilDivisorOfCartier A' wA') {P : MMP.Mori.PrimeDivisor X'}
    {V : X.Opens} (hxV : μ P.genericPoint ∈ V) {h : X.functionField}
    (hh : h ∈ multiplierIdealSections (𝟙 X) wA V) :
    P.valuationOver μ h ≤ WithZero.exp (wA'.coeff P) := by
  obtain ⟨V₀, hxV₀, φ, hφ0, hφX, hφX'⟩ :=
    exists_localEquation_valuation hA hA' hwA' (μ P.genericPoint)
  obtain ⟨r, hr⟩ : h * φ ∈
      (algebraMap (X.presheaf.stalk (μ P.genericPoint)) X.functionField).range := by
    refine Scheme.mem_range_algebraMap_stalk_of_forall_coheight_eq_one _ fun y hy hyx => ?_
    let Q : MMP.Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hy
    have hQη : Q.genericPoint = y := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y hy
    have hQ := hh.2 Q (support_inter_nonempty_of_genericPoint_mem Q
      (hQη ▸ hyx.mem_open V.isOpen hxV))
    rw [MMP.Mori.PrimeDivisor.valuationOver_apply, MMP.Mori.functionFieldMap_id_apply] at hQ
    rw [← hQη, ← MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff, map_mul,
      hφX Q (support_inter_nonempty_of_genericPoint_mem Q (hQη ▸ hyx.mem_open V₀.isOpen hxV₀))]
    calc _ ≤ WithZero.exp (wA.coeff Q) * WithZero.exp (-wA.coeff Q) := by gcongr
      _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
  have hle : P.valuationOver μ (h * φ) ≤ 1 := by
    rw [MMP.Mori.PrimeDivisor.valuationOver_apply, ← hr,
      MMP.Mori.functionFieldMap_algebraMap_stalk]
    exact (P.divisorialValuation_le_one_iff _).mpr ⟨_, rfl⟩
  rw [show h = h * φ * φ⁻¹ by field_simp, map_mul, map_inv₀,
    hφX' P (support_inter_nonempty_of_genericPoint_mem P hxV₀), WithZero.exp_neg, inv_inv]
  simpa using mul_le_mul_left hle (WithZero.exp (wA'.coeff P))

/-- **Twisting a push-forward by an integral divisor** (Lazarsfeld §9.2). Let `μ : X' ⟶ X` be a
dominant morphism of normal integral locally Noetherian schemes, `G` a Weil divisor on `X'`, `A` a
Cartier divisor on `X` with Weil divisor `[A]`, `A'` a pull-back of `A` along `μ` with Weil divisor
`[A']`. Then over every open `U ⊆ X`, the sections of `μ_*𝒪_{X'}(G + [A'])` are those of
`𝒪_X(A) · μ_*𝒪_{X'}(G)`: the `g ∈ K(X)` which near every point of `U` are finite sums of products
of a section of `𝒪_X([A])` and a section of `μ_*𝒪_{X'}(G)` (and `g = 0` if `U = ∅`). -/
@[mmp "lem_p09a_pushforward_twist_integral"]
public theorem multiplierIdealSections_add_pullback {X X' : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    {μ : X' ⟶ X} [IsDominant μ] (G : Divisor X')
    {A : X.CartierDivisor} {wA : Divisor X} (hA : IsWeilDivisorOfCartier A wA)
    {A' : X'.CartierDivisor} (hA' : IsPullback μ A A')
    {wA' : Divisor X'} (hwA' : IsWeilDivisorOfCartier A' wA') (U : X.Opens) :
    multiplierIdealSections μ (G + wA') U =
      {g | (U = ⊥ → g = 0) ∧ ∀ x ∈ U, ∃ V : X.Opens, x ∈ V ∧ V ≤ U ∧
        g ∈ Submodule.span ℤ
          (multiplierIdealSections (𝟙 X) wA V * multiplierIdealSections μ G V)} := by
  ext g
  constructor
  · rintro ⟨h0, hg⟩
    refine ⟨fun hU => h0 (by simp [hU]), fun x hx => ?_⟩
    obtain ⟨V₀, hxV₀, φ, hφ0, hφX, hφX'⟩ := exists_localEquation_valuation hA hA' hwA' x
    have hxV : x ∈ V₀ ⊓ U := ⟨hxV₀, hx⟩
    refine ⟨V₀ ⊓ U, hxV, inf_le_right, Submodule.subset_span ⟨φ⁻¹, ?_, φ * g, ?_, ?_⟩⟩
    · refine ⟨fun h => absurd h (preimage_ne_bot (𝟙 X) hxV), fun Q hQ => ?_⟩
      rw [MMP.Mori.PrimeDivisor.valuationOver_apply, MMP.Mori.functionFieldMap_id_apply,
        map_inv₀, hφX Q (hQ.mono (Set.inter_subset_inter_right _ fun z hz => hz.1)),
        WithZero.exp_neg, inv_inv]
    · refine ⟨fun h => absurd h (preimage_ne_bot μ hxV), fun P hP => ?_⟩
      have hP₀ := hP.mono (Set.inter_subset_inter_right _ fun z hz => hz.1)
      have hPU := hP.mono (Set.inter_subset_inter_right _ fun z hz => hz.2)
      rw [MMP.Mori.PrimeDivisor.valuationOver_apply, map_mul, map_mul,
        ← MMP.Mori.PrimeDivisor.valuationOver_apply, hφX' P hP₀]
      have := hg P hPU
      rw [MMP.Mori.DivisorWithCoeffs.coeff_add] at this
      calc WithZero.exp (-wA'.coeff P) * _ ≤
            WithZero.exp (-wA'.coeff P) * WithZero.exp (G.coeff P + wA'.coeff P) := by
            gcongr
            exact this
        _ = _ := by
          rw [← WithZero.exp_add]
          congr 1
          ring
    · exact inv_mul_cancel_left₀ hφ0 g
  · rintro ⟨h0, hg⟩
    refine ⟨fun hU => ?_, fun P hP => ?_⟩
    · refine h0 (by_contra fun h => ?_)
      obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty U).1 h
      exact preimage_ne_bot μ hx hU
    · have hη : μ P.genericPoint ∈ U := genericPoint_mem_of_support_inter_nonempty P hP
      obtain ⟨V, hxV, -, hgV⟩ := hg _ hη
      refine valuation_le_of_mem_span (P.valuationOver μ) ?_ hgV
      rintro _ ⟨h, hh, m, hm, rfl⟩
      rw [map_mul, MMP.Mori.DivisorWithCoeffs.coeff_add, add_comm, WithZero.exp_add]
      exact mul_le_mul' (valuationOver_le_of_mem_twist hA hA' hwA' hxV hh)
        (hm.2 P (support_inter_nonempty_of_genericPoint_mem P hxV))

end MMP.Intersection
