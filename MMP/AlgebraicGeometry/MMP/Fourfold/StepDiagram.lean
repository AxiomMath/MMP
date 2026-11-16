module
public import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldGraphDivisor

/-!
# Step diagrams and default weights for projective lc fourfolds

A step diagram `(X⁻, B⁻) → Z ← (X⁺, B⁺)` (`MMP.Fourfold.IsFourfoldStepDiagram`) has a small
positive side `f⁺`, so it extracts no divisor: every prime divisor `P` of `X⁺` has a divisorial
centre `P⁻` on `X⁻`, with `f⁻(P⁻) = f⁺(P)` a prime divisor of `Z`. Indeed `f⁺` is an isomorphism
at the generic point of `P`, the local ring of `Z` at the generic point of `Q = f⁺(P)` is a
discrete valuation ring, and a proper birational morphism onto the spectrum of a discrete
valuation ring is an isomorphism.

Consequently the graph divisor `H = u^* D⁻ - v^* D⁺` on the normalized graph `(G, u, v)` of a
step is `v`-exceptional, and `u`-exceptional too when `f⁻` is small: at a prime divisor of `G`
which is not contracted, all four maps are local isomorphisms and the coefficients of `u^* D⁻`
and `v^* D⁺` agree, `D⁺` being the strict transform of `D⁻`. Running the same coefficient
comparison along a finite chain of steps shows that the comparison divisor
`F = q_0^*(K_0 + Θ_0) - q_m^*(K_m + Θ_m)` on a common normal model `W` is `q_m`-exceptional.

Finally, for `b < 1` the weight `w(1 - j(1 - b)) = ⌈N max{1 - j(1 - b), 0}⌉` vanishes unless
`j < 1 / (1 - b)`, so the default `d(b) = ∑_{j ≥ 1} w(1 - j(1 - b))` is a finite sum, and it is
monotone in `b < 1`.

## Main results

* `MMP.Fourfold.exists_primeDivisor_valuationOver_eq_of_isSmallMorphism`: every prime divisor
  of `X⁺` has a prime divisor of `X⁻` with the same valuation and the same image in `Z`.
* `MMP.Fourfold.IsGraphDivisor.transformDivisor_eq_zero`: `v_* H = 0`.
* `MMP.Fourfold.IsGraphDivisor.transformDivisor_fst_eq_zero`: if `f⁻` is small, `u_* H = 0`.
* `MMP.Fourfold.transformDivisor_pullback_sub_pullback_eq_zero_of_isSmallMorphism`:
  `q_{m*} F = 0` for any finite chain of proper birational morphisms `g_k` and small `g_k⁺`.
* `MMP.Fourfold.transformDivisor_pullback_sub_pullback_eq_zero`: `q_{m*} F = 0` for a chain of
  step diagrams.
* `MMP.Fourfold.lt_inv_of_difficultyWeight_ne_zero`: `w(1 - j(1 - b)) ≠ 0` implies
  `j < (1 - b)⁻¹`.
* `MMP.Fourfold.defaultWeight_le_defaultWeight`: `d(b') ≤ d(b)` for `b' ≤ b < 1`.

## Implementation notes

The valuation `ord_P` of `k(X⁺)` is compared with `ord_{P⁻}` of `k(X⁻)` as the valuations
`MMP.Mori.PrimeDivisor.valuationOver` of `k(Z)`. Only the parts of a step diagram the argument
uses are assumed there: normality of `Z`, properness and birationality of `f⁻`, smallness of `f⁺`.

The push-forward along a birational morphism `v` is the birational transform
`MMP.Mori.RationalMap.transformDivisor` along `v` regarded as a rational map: it keeps the
components whose image is a prime divisor and drops the exceptional ones.

In the chain, the models, bases and morphisms are families indexed by `ℕ`; only the data with
`k ≤ m` (models, the morphisms `q_k`) and `k < m` (steps) are constrained. Compatibility of `q_k`
and `q_{k+1}` with `(g_k⁺)⁻¹ ∘ g_k : V_k ⇢ V_{k+1}` is `q_k ≫ g_k = q_{k+1} ≫ g_k⁺`, equivalent
since `g_k⁺` is birational. The source factors `F` as a sum of pull-backs of graph divisors; the
proof here runs the coefficient comparison directly on `W`, which needs no normalized graph, so
`W` is only assumed to be a Noetherian normal integral scheme rather than smooth and projective.

The weight results hold at every scale `N`; the source takes `N` the admissible scale.

## References

* [OpenAI, *Projective lc fourfolds*][OAI4], step diagrams and the difficulty
-/

open CategoryTheory AlgebraicGeometry MMP.Mori TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

/-! ### Prime divisors, generic points and the biregular locus -/

section Helpers

variable {X Y : Scheme.{u}}

/-- Over the biregular locus, a morphism reflects specialization. -/
private theorem specializes_of_map_specializes {f : X ⟶ Y} {x y : X}
    (hx : f x ∈ biregularLocus f) (hy : f y ∈ biregularLocus f) (h : f x ⤳ f y) : x ⤳ y := by
  set V := biregularLocus f
  have : IsIso (f ∣_ V) := isBiregular_biregularLocus f
  let p : (f ⁻¹ᵁ V).toScheme := ⟨x, hx⟩
  let q : (f ⁻¹ᵁ V).toScheme := ⟨y, hy⟩
  have hp : ((f ∣_ V) ≫ V.ι) p = f x := by rw [morphismRestrict_ι]; rfl
  have hq : ((f ∣_ V) ≫ V.ι) q = f y := by rw [morphismRestrict_ι]; rfl
  have hpq : p ⤳ q := by
    rwa [← ((f ∣_ V) ≫ V.ι).isOpenEmbedding.isInducing.specializes_iff, hp, hq]
  exact hpq.map (f ⁻¹ᵁ V).ι.continuous

/-- If the exceptional set of `f` has codimension at least two, it misses the generic point of
every prime divisor. -/
private theorem genericPoint_notMem_exceptionalSet {f : X ⟶ Y}
    (h2 : 2 ≤ closedsCodimension (exceptionalSet f)) (P : MMP.Mori.PrimeDivisor X) :
    P.genericPoint ∉ (exceptionalSet f : Set X) := fun h => by
  simpa [P.coheight_genericPoint] using MMP.Positivity.two_le_coheight_of_mem_exceptionalSet h2 h

/-- A morphism whose exceptional set has codimension at least two is biregular over the image
of the generic point of every prime divisor. -/
private theorem map_genericPoint_mem_biregularLocus {f : X ⟶ Y}
    (h2 : 2 ≤ closedsCodimension (exceptionalSet f)) (P : MMP.Mori.PrimeDivisor X) :
    f P.genericPoint ∈ biregularLocus f :=
  not_not.mp (genericPoint_notMem_exceptionalSet h2 P)

private theorem mem_support_iff (D : MMP.Mori.PrimeDivisor X) (x : X) :
    x ∈ D.support ↔ D.genericPoint ⤳ x := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, specializes_iff_mem_closure]

/-- If `f(P) = Q` as sets then `f(η_P) = η_Q`. -/
public theorem map_genericPoint_eq_of_image_eq {f : X ⟶ Y} (P : MMP.Mori.PrimeDivisor X)
    (Q : MMP.Mori.PrimeDivisor Y) (h : f '' P.support = Q.support) :
    f P.genericPoint = Q.genericPoint := by
  have h1 : f P.genericPoint ∈ Q.support :=
    h ▸ ⟨_, (mem_support_iff P _).mpr specializes_rfl, rfl⟩
  obtain ⟨y, hy, hfy⟩ : Q.genericPoint ∈ f '' P.support :=
    h ▸ (mem_support_iff Q _).mpr specializes_rfl
  have h3 : f P.genericPoint ⤳ Q.genericPoint :=
    hfy ▸ ((mem_support_iff P y).mp hy).map f.continuous
  exact (h3.antisymm ((mem_support_iff Q _).mp h1)).eq

/-- A proper morphism sending `η_E` to `η_Q` sends the support of `E` onto that of `Q`. -/
private theorem image_support_eq_of_map_genericPoint (f : X ⟶ Y) [IsProper f]
    (E : MMP.Mori.PrimeDivisor X) (Q : MMP.Mori.PrimeDivisor Y)
    (heq : f E.genericPoint = Q.genericPoint) : f '' E.support = Q.support := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    ← f.isClosedMap.closure_image_eq_of_continuous f.continuous, Set.image_singleton, heq]

/-- Over the biregular locus, the inverse transform of `Q` is the prime divisor through the
point over `η_Q`. -/
private theorem inverseTransformPrimeDivisor_eq_some_of_mem_biregularLocus {f : X ⟶ Y}
    (P : MMP.Mori.PrimeDivisor X) (Q : MMP.Mori.PrimeDivisor Y)
    (hPQ : f P.genericPoint = Q.genericPoint) (hV : Q.genericPoint ∈ biregularLocus f) :
    inverseTransformPrimeDivisor f Q = some P := by
  have hset : (inverseTransform f Q.idealSheaf.support : Set X) = P.support := by
    rw [inverseTransform, Closeds.coe_closure]
    refine le_antisymm (closure_minimal ?_ ?_) ?_
    · rintro y ⟨hyQ, hyV⟩
      have h1 : f P.genericPoint ⤳ f y := hPQ ▸ (mem_support_iff Q _).mp hyQ
      exact (mem_support_iff P y).mpr (specializes_of_map_specializes (hPQ ▸ hV) hyV h1)
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact isClosed_closure
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      refine closure_minimal (Set.singleton_subset_iff.mpr (subset_closure ?_)) isClosed_closure
      refine ⟨?_, ?_⟩
      · change f P.genericPoint ∈ Q.support
        exact hPQ ▸ (mem_support_iff Q _).mpr specializes_rfl
      · change f P.genericPoint ∈ biregularLocus f
        rwa [hPQ]
  refine inverseTransformPrimeDivisor_eq_some_iff.mpr ⟨⟨Q.genericPoint,
    (mem_support_iff Q _).mpr specializes_rfl, hV⟩, ?_⟩
  have := P.integral
  rw [inverseTransformIdeal,
    Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme P.idealSheaf _ rfl]
  congr 1
  ext1
  exact hset.symm

/-- For a surjective `f`, `P` is the inverse transform of at most one prime divisor `Q`. -/
private theorem eq_of_inverseTransformPrimeDivisor_eq_some {f : X ⟶ Y}
    (hs : Function.Surjective f) {P : MMP.Mori.PrimeDivisor X} {Q Q' : MMP.Mori.PrimeDivisor Y}
    (hPQ : f P.genericPoint = Q.genericPoint) (h : inverseTransformPrimeDivisor f Q' = some P) :
    Q' = Q := by
  obtain ⟨⟨z, hzQ, hzV⟩, hI⟩ := inverseTransformPrimeDivisor_eq_some_iff.mp h
  have hset : P.support = closure (f ⁻¹' ((Q'.support : Set Y) ∩ biregularLocus f)) := by
    have := congrArg (fun I ↦ (I.support : Set X)) hI
    simp only [inverseTransformIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
    rw [AlgebraicGeometry.PrimeDivisor.support, this, inverseTransform, Closeds.coe_closure]
  have hQ'cl : IsClosed (Q'.support : Set Y) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isClosed_closure
  -- `η_Q ∈ Q'`
  have h1 : Q.genericPoint ∈ Q'.support := by
    have hP : P.genericPoint ∈ closure (f ⁻¹' ((Q'.support : Set Y) ∩ biregularLocus f)) :=
      hset ▸ (mem_support_iff P _).mpr specializes_rfl
    have := image_closure_subset_closure_image f.continuous ⟨_, hP, rfl⟩
    rw [hPQ] at this
    refine closure_minimal ?_ hQ'cl this
    rintro _ ⟨y, ⟨hy, -⟩, rfl⟩
    exact hy
  -- `η_{Q'} ∈ Q`
  have h2 : Q'.genericPoint ∈ Q.support := by
    have hgV : Q'.genericPoint ∈ biregularLocus f :=
      ((mem_support_iff Q' z).mp hzQ).mem_open (biregularLocus f).isOpen hzV
    obtain ⟨y, hy⟩ := hs Q'.genericPoint
    have hyP : y ∈ P.support := by
      rw [hset]
      refine subset_closure ⟨?_, ?_⟩
      · change f y ∈ Q'.support
        exact hy ▸ (mem_support_iff Q' _).mpr specializes_rfl
      · change f y ∈ biregularLocus f
        rwa [hy]
    rw [← hy, mem_support_iff, ← hPQ]
    exact ((mem_support_iff P y).mp hyP).map f.continuous
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (((mem_support_iff Q' _).mp h1).antisymm ((mem_support_iff Q _).mp h2)).eq

/-- The transform `φ_* D` vanishes when every component of `D` with a transform has
coefficient zero. -/
public theorem mapPrimeDivisors_eq_zero_of_forall {R : Type*} [AddCommMonoid R]
    {φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)}
    (D : DivisorWithCoeffs R X) (h : ∀ E P, φ E = some P → D E = 0) :
    DivisorWithCoeffs.mapPrimeDivisors φ D = 0 := by
  rw [DivisorWithCoeffs.mapPrimeDivisors, Finsupp.liftAddHom_apply]
  refine Finset.sum_eq_zero fun E _ => ?_
  rcases hE : φ E with _ | P
  · simp [hE]
  · simp [h E P hE]

end Helpers

/-- A normal variety is separated. -/
public theorem isSeparated_toTerminal_of_isNormalVariety {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} (h : IsNormalVariety k s) :
    IsSeparated (X ↘ Limits.terminal Scheme) := by
  have := h.1
  rw [show (X ↘ Limits.terminal Scheme) = s ≫ (Spec (.of k) ↘ Limits.terminal Scheme) from
    Limits.terminal.hom_ext _ _]
  infer_instance

/-! ### Birational morphisms over the generic point of a prime divisor -/

section Birational

variable {X Y : Scheme.{u}}

/-- A separated birational morphism is injective over a point whose local ring is a valuation
ring. -/
public theorem eq_of_map_eq_of_valuationRing [IsIntegral X] [IsIntegral Y] {f : X ⟶ Y}
    [IsSeparated f] [IsDominant f] (hμ : Function.Bijective (functionFieldMap f)) {y : Y}
    [ValuationRing (Y.presheaf.stalk y)] {x₁ x₂ : X} (h₁ : f x₁ = y) (h₂ : f x₂ = y) :
    x₁ = x₂ := by
  subst h₁
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing f hμ x₁
  haveI : ValuationRing (Y.presheaf.stalk (f x₂)) := by rw [h₂]; infer_instance
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing f hμ x₂
  exact MMP.Positivity.eq_of_isIso_stalkMap f hμ h₂

/-- A birational morphism onto a normal scheme is a local isomorphism at every point over the
generic point of a prime divisor. -/
public theorem isIso_stalkMap_of_map_eq_genericPoint [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} (hf : IsBirationalMorphism f)
    {x : X} {P : MMP.Mori.PrimeDivisor Y} (hx : f x = P.genericPoint) :
    IsIso (f.stalkMap x) := by
  have := P.isDiscreteValuationRing_localRing
  have := hf.isDominant
  have : ValuationRing (Y.presheaf.stalk (f x)) := by rw [hx]; infer_instance
  exact MMP.Positivity.isIso_stalkMap_of_valuationRing f hf.functionFieldMap_bijective x

/-- If `f(η_E) = η_Q` and `f^♯ : 𝒪_{Y,Q} ⟶ 𝒪_{X,E}` is an isomorphism, then `v_E`, seen on
`k(Y)` through `f`, is `v_Q`. -/
private theorem valuationOver_eq_of_isIso [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsDominant f]
    (E : MMP.Mori.PrimeDivisor X) (Q : MMP.Mori.PrimeDivisor Y)
    (heq : f E.genericPoint = Q.genericPoint) [IsIso (f.stalkMap E.genericPoint)] :
    E.valuationOver f = Q.divisorialValuation := by
  refine Valuation.ext fun t => ?_
  rw [PrimeDivisor.valuationOver_apply]
  by_cases ht : t = 0
  · rw [ht, map_zero, map_zero, map_zero]
  rw [PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ((map_ne_zero _).mpr ht),
    PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ht,
    MMP.Positivity.ord_functionFieldMap_of_isIso f E Q heq t]

/-- **Valuative criterion at a divisor.** A proper birational morphism `f : X ⟶ Y` onto a normal
scheme is an isomorphism of local rings over the generic point of each prime divisor `Q` of `Y`:
there is a prime divisor `E` of `X` with `f(η_E) = η_Q` and `f^♯ : 𝒪_{Y,η_Q} ≅ 𝒪_{X,η_E}`. -/
private theorem exists_primeDivisor_isIso_stalkMap [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsProper f]
    (hf : IsBirationalMorphism f) (Q : MMP.Mori.PrimeDivisor Y) :
    ∃ E : MMP.Mori.PrimeDivisor X,
      f E.genericPoint = Q.genericPoint ∧ IsIso (f.stalkMap E.genericPoint) := by
  have := Q.isDiscreteValuationRing_localRing
  haveI := hf.isDominant
  obtain ⟨x, hx, hiso⟩ :=
    MMP.Intersection.exists_isIso_stalkMap_of_valuationRing f hf.functionFieldMap_bijective
      Q.genericPoint
  have hco : Order.coheight x = 1 := by
    have h := ringKrullDim_eq_of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hx,
      Q.coheight_genericPoint] at h
    exact_mod_cast h.symm
  let E : MMP.Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hco
  have hE : E.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hco
  exact ⟨E, hE ▸ hx, hE ▸ hiso⟩

/-- Let `E ⊆ X`, `P ⊆ Y` be prime divisors with `f(η_E) = η_P` and `𝒪_{Y,P} ≅ 𝒪_{X,E}`. The
coefficient of `E` in the pull-back of a `ℚ`-Cartier `ℚ`-divisor `B` is the coefficient of `P`
in `B`. -/
public theorem coeff_eq_of_isPullback_qDivisor [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} (E : MMP.Mori.PrimeDivisor X)
    (P : MMP.Mori.PrimeDivisor Y) (heq : f E.genericPoint = P.genericPoint)
    [IsIso (f.stalkMap E.genericPoint)] {B : QDivisor Y} (hBq : B.IsQCartier)
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp}
    {B' : QDivisor X} (hB' : B.IsPullback f hB B') : B' E = B P := by
  have hm := QDivisor.cartierIndex_pos hBq
  obtain ⟨D₀, hD₀, hD₀c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hBq
  obtain ⟨D', hD', hp⟩ := hB' _ hm D₀ hD₀ hD₀c
  have hc := MMP.Positivity.coeff_eq_of_isPullback E P heq hD₀c hp
  have h1 := congrArg (fun G : QDivisor X => G E) hD'
  have h2 := congrArg (fun G : QDivisor Y => G P) hD₀
  simp only [Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast] at h1 h2
  exact mul_left_cancel₀ (by exact_mod_cast hm.ne')
    (h1.symm.trans ((congrArg (fun z : ℤ => (z : ℚ)) hc).trans h2))

end Birational

/-! ### Strict transforms across a step -/

section FlipTransform

variable {Xm Xp Z : Scheme.{u}} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}

/-- The coefficient of `P` in the strict transform `(f⁺)⁻¹_* f⁻_* D` is that of `P⁻` in `D`,
when `P⁻` is the only prime divisor with transform `Q` under `f⁻` and `Q` the only prime divisor
with inverse transform `P` under `f⁺`. -/
private theorem flipTransform_apply
    {Pm : MMP.Mori.PrimeDivisor Xm} {Q : MMP.Mori.PrimeDivisor Z} {P : MMP.Mori.PrimeDivisor Xp}
    (h1 : RationalMap.transformPrimeDivisor (X := Xm) fm.toRationalMap Pm = some Q)
    (h1' : ∀ E', RationalMap.transformPrimeDivisor (X := Xm) fm.toRationalMap E' = some Q →
      E' = Pm)
    (h2 : inverseTransformPrimeDivisor fp Q = some P)
    (h2' : ∀ Q', inverseTransformPrimeDivisor fp Q' = some P → Q' = Q)
    {R : Type*} [AddCommMonoid R] (D : DivisorWithCoeffs R Xm) :
    flipTransform fm fp D P = D Pm := by
  simp only [flipTransform, AddMonoidHom.coe_comp, Function.comp_apply]
  rw [inverseTransformDivisor, MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq h2 h2',
    RationalMap.transformDivisor, MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq h1 h1']

/-- Let `f⁻ : X⁻ → Z ← X⁺ : f⁺` be birational, `f⁻` separated, `f⁺` surjective, and let `Q` be a
prime divisor of `Z` whose local ring is a valuation ring, with `f⁻(η_P) = η_Q = f⁺(η_{P⁺})` and
`f⁺` biregular over `η_Q`. Then the coefficient of the strict transform `(f⁺)⁻¹_* f⁻_* D` at
`P⁺` equals the coefficient of `D` at `P`. -/
public theorem flipTransform_apply_of_map_genericPoint [IsIntegral Xm] [IsIntegral Z]
    [IsSeparated (Z ↘ Limits.terminal Scheme)] [IsSeparated fm] [IsDominant fm]
    (hbm : Function.Bijective (functionFieldMap fm))
    (hs : Function.Surjective fp) {P : MMP.Mori.PrimeDivisor Xm} {Pp : MMP.Mori.PrimeDivisor Xp}
    {Q : MMP.Mori.PrimeDivisor Z} [ValuationRing (Z.presheaf.stalk Q.genericPoint)]
    (hPQ : fm P.genericPoint = Q.genericPoint) (hPpQ : fp Pp.genericPoint = Q.genericPoint)
    (hV : Q.genericPoint ∈ biregularLocus fp) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R Xm) : flipTransform fm fp D Pp = D P :=
  flipTransform_apply
    ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff fm P Q).mpr hPQ)
    (fun E' hE' => AlgebraicGeometry.PrimeDivisor.genericPoint_injective <|
      eq_of_map_eq_of_valuationRing hbm
        ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff fm E' Q).mp hE') hPQ)
    (inverseTransformPrimeDivisor_eq_some_of_mem_biregularLocus Pp Q hPpQ hV)
    (fun _ hQ' => eq_of_inverseTransformPrimeDivisor_eq_some hs hPpQ hQ') D

end FlipTransform

/-! ### A step extracts no divisor -/

/-- In a diagram `X⁻ ⟶ Z ⟵ X⁺` with `f⁻` proper birational, `Z` normal and `f⁺` small, every
prime divisor `P` of `X⁺` is not exceptional over `X⁻`: there is a prime divisor `P⁻` of `X⁻`
with `ord_{P⁻} = ord_P` as valuations of `k(Z)`, and `f⁻(P⁻) = f⁺(P)` is a prime divisor `Q`
of `Z`. -/
@[mmp "lem_oai4_c1_step_extracts_no_divisor"]
public theorem exists_primeDivisor_valuationOver_eq_of_isSmallMorphism
    {k : Type u} [Field k] {Xm Xp Z : Scheme.{u}}
    [IsIntegral Xm] [IsLocallyNoetherian Xm] [IsNormal Xm]
    [IsIntegral Xp] [IsLocallyNoetherian Xp] [IsNormal Xp] [IsIntegral Z]
    {sXp : Xp ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (hZ : IsNormalVariety k sZ) [IsProper fm] (hfm : IsBirationalMorphism fm)
    (hfp : IsSmallMorphism sXp sZ fp) (P : MMP.Mori.PrimeDivisor Xp) :
    haveI := hfm.isDominant
    haveI := hfp.isBirationalMorphism.isDominant
    ∃ (Pm : MMP.Mori.PrimeDivisor Xm) (Q : MMP.Mori.PrimeDivisor Z),
      Pm.valuationOver fm = P.valuationOver fp ∧
        fm '' Pm.support = Q.support ∧ fp '' P.support = Q.support := by
  haveI := hfm.isDominant
  haveI := hfp.isBirationalMorphism.isDominant
  haveI : IsProper fp := hfp.isProper
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  -- `η_P` lies outside `Ex(f⁺)`, so `ζ = f⁺(η_P)` has codimension one
  have hζ : Order.coheight (fp P.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus fp
      (map_genericPoint_mem_biregularLocus hfp.two_le_codimension P), P.coheight_genericPoint]
  set Q : MMP.Mori.PrimeDivisor Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hζ
  have hQ : fp P.genericPoint = Q.genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hζ).symm
  haveI := isIso_stalkMap_of_map_eq_genericPoint hfp.isBirationalMorphism hQ
  obtain ⟨Pm, hPm, _⟩ := exists_primeDivisor_isIso_stalkMap fm hfm Q
  refine ⟨Pm, Q, ?_, image_support_eq_of_map_genericPoint fm Pm Q hPm,
    image_support_eq_of_map_genericPoint fp P Q hQ⟩
  rw [valuationOver_eq_of_isIso fm Pm Q hPm, valuationOver_eq_of_isIso fp P Q hQ]

/-- **One step of the chain.** Let `f⁻ : X⁻ ⟶ Z ⟵ X⁺ : f⁺` with `f⁻` proper birational and `f⁺`
small, let `P` be a prime divisor of `X⁺` and `x ∈ X⁻` a point with `f⁻(x) = f⁺(η_P)`. Then `x`
is the generic point of a prime divisor `P⁻` of `X⁻`, and the coefficient of `P` in a strict
transform `(f⁺)⁻¹_* f⁻_* D` is the coefficient of `P⁻` in `D`. -/
public theorem exists_eq_genericPoint_flipTransform_apply {k : Type u} [Field k]
    {Xm Xp Z : Scheme.{u}} [IsIntegral Xm] [IsLocallyNoetherian Xm] [IsNormal Xm]
    [IsIntegral Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
    {sXp : Xp ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    [IsProper fm] (hfm : IsBirationalMorphism fm) (hfp : IsSmallMorphism sXp sZ fp)
    (P : MMP.Mori.PrimeDivisor Xp) (x : Xm) (hx : fm x = fp P.genericPoint) :
    ∃ Pm : MMP.Mori.PrimeDivisor Xm, x = Pm.genericPoint ∧
      ∀ {R : Type*} [AddCommMonoid R] (D : DivisorWithCoeffs R Xm),
        flipTransform fm fp D P = D Pm := by
  haveI : IsProper fp := hfp.isProper
  have hZ := hfp.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI := isSeparated_toTerminal_of_isNormalVariety hZ
  haveI := hfm.isDominant
  haveI := hfp.isBirationalMorphism.isDominant
  obtain ⟨Pm, Q, -, hPmQ, hPQ⟩ :=
    exists_primeDivisor_valuationOver_eq_of_isSmallMorphism hZ hfm hfp P
  have hPmQ' := map_genericPoint_eq_of_image_eq Pm Q hPmQ
  have hPQ' := map_genericPoint_eq_of_image_eq P Q hPQ
  have := Q.isDiscreteValuationRing_localRing
  exact ⟨Pm, eq_of_map_eq_of_valuationRing hfm.functionFieldMap_bijective (hx.trans hPQ') hPmQ',
    fun D => flipTransform_apply_of_map_genericPoint hfm.functionFieldMap_bijective fp.surjective
      hPmQ' hPQ' (hPQ' ▸ map_genericPoint_mem_biregularLocus hfp.two_le_codimension P) D⟩

/-! ### The graph divisor is exceptional -/

section GraphDivisor

variable {Xm Xp Z G : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
  [IsLocallyNoetherian G] [IsNormal G]

/-- For a step diagram with normalized graph `(G, u, v)` and graph divisor `H`, the push-forward
`v_* H` vanishes. -/
@[mmp "lem_oai4_c1_graph_pushforward_zero"]
public theorem IsGraphDivisor.transformDivisor_eq_zero {sXm : Xm ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)} {K : Divisor Xm} {B : QDivisor Xm}
    {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} {u : G ⟶ Xm} {v : G ⟶ Xp} {H : QDivisor G}
    (h : IsGraphDivisor sXm sZ sXp K B fm fp u v H) :
    RationalMap.transformDivisor v.toRationalMap H = 0 := by
  obtain ⟨Hm, Hp, hm, hp, hHm, hHp, rfl⟩ := h.exists_pullback
  have hD := h.isFourfoldStepDiagram
  have hG := h.isNormalizedGraph
  haveI := hG.isIntegral
  haveI : IsProper fm := isProper_of_isProjectiveMorphism _ hD.isProjectiveMorphism_minus
  haveI : IsProper v := by
    haveI := hG.isFinite
    rw [← Limits.pullback.lift_snd u v hG.comp_eq]
    infer_instance
  have hXp := hD.isNormalVariety_plus
  have hGv : IsNormalVariety ℂ (v ≫ sXp) := by
    refine ⟨?_, inferInstance⟩
    have := hXp.1
    exact (isVariety_iff ℂ (v ≫ sXp)).mpr
      ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  refine Finsupp.ext fun P => ?_
  obtain ⟨E, hvE, _, htr⟩ := MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply
    hXp hGv hG.isBirationalMorphism_plus P
  -- `u(η_E)` lies over `f⁺(η_P)`, so it is the generic point of the prime divisor `P⁻` over `P`
  obtain ⟨Pm, huE, hfl⟩ := exists_eq_genericPoint_flipTransform_apply hD.isBirationalMorphism_minus
    hD.isSmallMorphism_plus P (u E.genericPoint)
    (by rw [← Scheme.Hom.comp_apply, hG.comp_eq, Scheme.Hom.comp_apply, hvE])
  haveI := isIso_stalkMap_of_map_eq_genericPoint hG.isBirationalMorphism_minus huE
  rw [map_sub, Finsupp.sub_apply, htr, htr, Finsupp.coe_zero, Pi.zero_apply, sub_eq_zero,
    coeff_eq_of_isPullback_qDivisor E Pm huE hD.isQCartier_minus hHm,
    coeff_eq_of_isPullback_qDivisor E P hvE hD.isQCartier_plus hHp]
  change ((K Pm : ℤ) : ℚ) + B Pm = ((flipTransform fm fp K P : ℤ) : ℚ) + flipTransform fm fp B P
  rw [hfl K, hfl B]

/-- For a step diagram with `f⁻` small, normalized graph `(G, u, v)` and graph divisor `H`, the
push-forward `u_* H` vanishes. -/
@[mmp "lem_oai4_c1_graph_pushforward_zero_minus"]
public theorem IsGraphDivisor.transformDivisor_fst_eq_zero {sXm : Xm ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)} {K : Divisor Xm} {B : QDivisor Xm}
    {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} {u : G ⟶ Xm} {v : G ⟶ Xp} {H : QDivisor G}
    (h : IsGraphDivisor sXm sZ sXp K B fm fp u v H) (hfm : IsSmallMorphism sXm sZ fm) :
    RationalMap.transformDivisor u.toRationalMap H = 0 := by
  obtain ⟨Hm, Hp, hm, hp, hHm, hHp, rfl⟩ := h.exists_pullback
  have hD := h.isFourfoldStepDiagram
  have hG := h.isNormalizedGraph
  haveI := hG.isIntegral
  haveI : IsProper fm := isProper_of_isProjectiveMorphism _ hD.isProjectiveMorphism_minus
  haveI : IsProper fp := hD.isProper_plus
  haveI : IsProper u := by
    haveI := hG.isFinite
    rw [← Limits.pullback.lift_fst u v hG.comp_eq]
    infer_instance
  have hZ := hD.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI := isSeparated_toTerminal_of_isNormalVariety hZ
  have hXm := hD.isNormalVariety_minus
  have hGu : IsNormalVariety ℂ (u ≫ sXm) := by
    refine ⟨?_, inferInstance⟩
    have := hXm.1
    exact (isVariety_iff ℂ (u ≫ sXm)).mpr
      ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  have hbm := hD.isBirationalMorphism_minus
  have hbp := hD.isBirationalMorphism_plus
  haveI := hbm.isDominant
  haveI := hbp.isDominant
  refine Finsupp.ext fun P => ?_
  obtain ⟨E, huE, _, htr⟩ := MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply
    hXm hGu hG.isBirationalMorphism_minus P
  obtain ⟨Pp, Q, -, hPpQ, hPQ⟩ :=
    exists_primeDivisor_valuationOver_eq_of_isSmallMorphism hZ hbp hfm P
  have hPpQ' := map_genericPoint_eq_of_image_eq Pp Q hPpQ
  have hPQ' := map_genericPoint_eq_of_image_eq P Q hPQ
  have := Q.isDiscreteValuationRing_localRing
  -- `P⁺` is the only point of `X⁺` over `η_Q`, so `v(η_E) = η_{P⁺}`
  have hvE : v E.genericPoint = Pp.genericPoint :=
    eq_of_map_eq_of_valuationRing hbp.functionFieldMap_bijective (by
      rw [← Scheme.Hom.comp_apply, ← hG.comp_eq, Scheme.Hom.comp_apply, huE, hPQ']) hPpQ'
  haveI := isIso_stalkMap_of_map_eq_genericPoint hG.isBirationalMorphism_plus hvE
  have hfl {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R Xm) :=
    flipTransform_apply_of_map_genericPoint hbm.functionFieldMap_bijective fp.surjective hPQ'
      hPpQ' (hPpQ' ▸ map_genericPoint_mem_biregularLocus
        hD.isSmallMorphism_plus.two_le_codimension Pp) D
  rw [map_sub, Finsupp.sub_apply, htr, htr, Finsupp.coe_zero, Pi.zero_apply, sub_eq_zero,
    coeff_eq_of_isPullback_qDivisor E P huE hD.isQCartier_minus hHm,
    coeff_eq_of_isPullback_qDivisor E Pp hvE hD.isQCartier_plus hHp]
  change ((K P : ℤ) : ℚ) + B P = ((flipTransform fm fp K Pp : ℤ) : ℚ) + flipTransform fm fp B Pp
  rw [hfl K, hfl B]

end GraphDivisor

/-! ### The comparison divisor of a finite chain of steps is exceptional -/

section Chain

variable {k : Type u} [Field k] {m : ℕ} {V : ℕ → Scheme.{u}} {sV : ∀ i, V i ⟶ Spec (.of k)}
  [∀ i, IsIntegral (V i)] [∀ i, IsLocallyNoetherian (V i)] [∀ i, IsNormal (V i)]
  {T : ℕ → Scheme.{u}} {sT : ∀ i, T i ⟶ Spec (.of k)} {g : ∀ i, V i ⟶ T i}
  {gp : ∀ i, V (i + 1) ⟶ T i} {W : Scheme.{u}} {q : ∀ i, W ⟶ V i}

/-- **Descending the chain.** Let `g_i : V_i ⟶ T_i ⟵ V_{i+1} : g_i⁺`, `i < m`, with `g_i` proper
birational and `g_i⁺` small, and `q_i : W ⟶ V_i` with `q_i ≫ g_i = q_{i+1} ≫ g_i⁺`. For a point
`w` of `W` lying over the generic point of a prime divisor `P` of `V_i`, `i ≤ m`, the point
`q_0(w)` is the generic point of a prime divisor `P₀` of `V_0`, and every family of strict
transforms along the chain has the same coefficient at `P` as at `P₀`. -/
public theorem exists_primeDivisor_zero_forall_coeff_eq (hg : ∀ i < m, IsProper (g i))
    (hgb : ∀ i < m, IsBirationalMorphism (g i))
    (hgp : ∀ i < m, IsSmallMorphism (sV (i + 1)) (sT i) (gp i))
    (hcomp : ∀ i < m, q i ≫ g i = q (i + 1) ≫ gp i) (w : W) :
    ∀ i ≤ m, ∀ P : MMP.Mori.PrimeDivisor (V i), q i w = P.genericPoint →
      ∃ P₀ : MMP.Mori.PrimeDivisor (V 0), q 0 w = P₀.genericPoint ∧
        ∀ {R : Type*} [AddCommMonoid R] (B : ∀ i, DivisorWithCoeffs R (V i)),
          (∀ i < m, B (i + 1) = flipTransform (g i) (gp i) (B i)) → B i P = B 0 P₀ := by
  intro i
  induction i with
  | zero => exact fun _ P hP => ⟨P, hP, fun _ _ => rfl⟩
  | succ i ih =>
    intro hi P hP
    haveI := hg i hi
    obtain ⟨Pi, hPi, hfl⟩ := exists_eq_genericPoint_flipTransform_apply (hgb i hi) (hgp i hi) P
      (q i w) (by rw [← hP, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hcomp i hi])
    obtain ⟨P₀, hP₀, hB⟩ := ih (by omega) Pi hPi
    exact ⟨P₀, hP₀, fun B hBfl => by rw [hBfl i hi, hfl, hB B hBfl]⟩

end Chain

/-- **The comparison divisor of a finite chain of steps is exceptional.** For diagrams
`V_k ⟶ T_k ⟵ V_{k+1}`, `k < m`, of a proper birational morphism `g_k` and a small morphism `g_k⁺`
of normal varieties, with transported divisors `K_{k+1} = (g_k⁺)⁻¹_* (g_k)_* K_k` and
`Θ_{k+1} = (g_k⁺)⁻¹_* (g_k)_* Θ_k`, and birational morphisms `q_k : W ⟶ V_k`, `k ≤ m`, from a
normal integral scheme with `q_k ≫ g_k = q_{k+1} ≫ g_k⁺`, the push-forward along `q_m` of
`q_0^*(K_0 + Θ_0) - q_m^*(K_m + Θ_m)` vanishes. -/
public theorem transformDivisor_pullback_sub_pullback_eq_zero_of_isSmallMorphism
    {𝕜 : Type u} [Field 𝕜] (m : ℕ) {V : ℕ → Scheme.{u}} (sV : ∀ k, V k ⟶ Spec (.of 𝕜))
    [∀ k, IsIntegral (V k)] [∀ k, IsLocallyNoetherian (V k)] [∀ k, IsNormal (V k)]
    (K : ∀ k, Divisor (V k)) (Θ : ∀ k, QDivisor (V k))
    {T : ℕ → Scheme.{u}} (sT : ∀ k, T k ⟶ Spec (.of 𝕜))
    (g : ∀ k, V k ⟶ T k) (gp : ∀ k, V (k + 1) ⟶ T k) (hg : ∀ k < m, IsProper (g k))
    (hgb : ∀ k < m, IsBirationalMorphism (g k))
    (hgp : ∀ k < m, IsSmallMorphism (sV (k + 1)) (sT k) (gp k))
    (hK : ∀ k < m, K (k + 1) = flipTransform (g k) (gp k) (K k))
    (hΘ : ∀ k < m, Θ (k + 1) = flipTransform (g k) (gp k) (Θ k))
    {W : Scheme.{u}} [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]
    (q : ∀ k, W ⟶ V k) (hq : ∀ k ≤ m, IsBirationalMorphism (q k))
    (hcomp : ∀ k < m, q k ≫ g k = q (k + 1) ≫ gp k)
    (hD₀ : (Divisor.toQDivisor (K 0) + Θ 0).IsQCartier)
    (hDₘ : (Divisor.toQDivisor (K m) + Θ m).IsQCartier)
    (h₀ : ∀ Z : irreducibleComponents W,
      q 0 (componentGenericPoint W Z) ∉ (Divisor.toQDivisor (K 0) + Θ 0).supp)
    (hₘ : ∀ Z : irreducibleComponents W,
      q m (componentGenericPoint W Z) ∉ (Divisor.toQDivisor (K m) + Θ m).supp) :
    RationalMap.transformDivisor (X := W) (q m).toRationalMap
      ((Divisor.toQDivisor (K 0) + Θ 0).pullback hD₀ h₀ -
        (Divisor.toQDivisor (K m) + Θ m).pullback hDₘ hₘ) = 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [sub_self, map_zero]
  have hVm := (hgp (m - 1) (by omega)).isNormalVariety_source
  rw [Nat.sub_add_cancel hm] at hVm
  have := isSeparated_toTerminal_of_isNormalVariety hVm
  rw [RationalMap.transformDivisor]
  refine mapPrimeDivisors_eq_zero_of_forall _ fun E P hEP => ?_
  have hEm := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff (q m) E P).mp hEP
  obtain ⟨P₀, hP₀, hB⟩ :=
    exists_primeDivisor_zero_forall_coeff_eq hg hgb hgp hcomp E.genericPoint m le_rfl P hEm
  haveI := isIso_stalkMap_of_map_eq_genericPoint (hq 0 m.zero_le) hP₀
  haveI := isIso_stalkMap_of_map_eq_genericPoint (hq m le_rfl) hEm
  rw [Finsupp.sub_apply,
    coeff_eq_of_isPullback_qDivisor E P₀ hP₀ hD₀ (QDivisor.isPullback_pullback hD₀ h₀),
    coeff_eq_of_isPullback_qDivisor E P hEm hDₘ (QDivisor.isPullback_pullback hDₘ hₘ)]
  change ((K 0 P₀ : ℤ) : ℚ) + Θ 0 P₀ - (((K m P : ℤ) : ℚ) + Θ m P) = 0
  rw [hB K hK, hB Θ hΘ, sub_self]

/-- **The comparison divisor of a finite chain of step diagrams is exceptional.** For step
diagrams `(V_k, Θ_k) → T_k ← (V_{k+1}, Θ_{k+1})`, `k < m`, with transported canonical divisors
`K_{k+1} = (g_k⁺)⁻¹_* (g_k)_* K_k` and boundaries `Θ_{k+1} = (g_k⁺)⁻¹_* (g_k)_* Θ_k`, and
birational morphisms `q_k : W ⟶ V_k`, `k ≤ m`, from a normal integral scheme with
`q_k ≫ g_k = q_{k+1} ≫ g_k⁺`, the push-forward along `q_m` of `q_0^*(K_0 + Θ_0) - q_m^*(K_m + Θ_m)`
vanishes. -/
@[mmp "lem_oai4_c1_finite_program_exceptional"]
public theorem transformDivisor_pullback_sub_pullback_eq_zero (m : ℕ)
    {V : ℕ → Scheme.{0}} (sV : ∀ k, V k ⟶ Spec (.of ℂ)) [∀ k, IsIntegral (V k)]
    [∀ k, CompactSpace (V k)] [∀ k, IsLocallyNoetherian (V k)] [∀ k, IsNormal (V k)]
    (K : ∀ k, Divisor (V k)) (Θ : ∀ k, QDivisor (V k))
    {T : ℕ → Scheme.{0}} (sT : ∀ k, T k ⟶ Spec (.of ℂ))
    (g : ∀ k, V k ⟶ T k) (gp : ∀ k, V (k + 1) ⟶ T k)
    (hstep : ∀ k < m, IsFourfoldStepDiagram (sV k) (sT k) (sV (k + 1)) (K k) (Θ k) (g k) (gp k))
    (hK : ∀ k < m, K (k + 1) = flipTransform (g k) (gp k) (K k))
    (hΘ : ∀ k < m, Θ (k + 1) = flipTransform (g k) (gp k) (Θ k))
    {W : Scheme.{0}} [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]
    (q : ∀ k, W ⟶ V k) (hq : ∀ k ≤ m, IsBirationalMorphism (q k))
    (hcomp : ∀ k < m, q k ≫ g k = q (k + 1) ≫ gp k)
    (hD₀ : (Divisor.toQDivisor (K 0) + Θ 0).IsQCartier)
    (hDₘ : (Divisor.toQDivisor (K m) + Θ m).IsQCartier)
    (h₀ : ∀ Z : irreducibleComponents W,
      q 0 (componentGenericPoint W Z) ∉ (Divisor.toQDivisor (K 0) + Θ 0).supp)
    (hₘ : ∀ Z : irreducibleComponents W,
      q m (componentGenericPoint W Z) ∉ (Divisor.toQDivisor (K m) + Θ m).supp) :
    RationalMap.transformDivisor (X := W) (q m).toRationalMap
      ((Divisor.toQDivisor (K 0) + Θ 0).pullback hD₀ h₀ -
        (Divisor.toQDivisor (K m) + Θ m).pullback hDₘ hₘ) = 0 :=
  transformDivisor_pullback_sub_pullback_eq_zero_of_isSmallMorphism m sV K Θ sT g gp
    (fun k hk => isProper_of_isProjectiveMorphism _ (hstep k hk).isProjectiveMorphism_minus)
    (fun k hk => (hstep k hk).isBirationalMorphism_minus)
    (fun k hk => (hstep k hk).isSmallMorphism_plus) hK hΘ q hq hcomp hD₀ hDₘ h₀ hₘ

/-! ### The default echo weight -/

/-- If `b < 1` and the weight `w(1 - j(1 - b))` at any scale `N` is nonzero, then
`j < 1 / (1 - b)`. -/
@[mmp "lem_oai4_difficulty_preparation_b"]
public theorem lt_inv_of_difficultyWeight_ne_zero {N : ℕ} {b : ℝ} (hb : b < 1) {j : ℕ}
    (hj : difficultyWeight N (1 - j * (1 - b)) ≠ 0) : (j : ℝ) < (1 - b)⁻¹ := by
  by_contra h
  refine hj (difficultyWeight_of_nonpos ?_)
  have := (inv_le_iff_one_le_mul₀ (sub_pos.mpr hb)).mp (not_lt.mp h)
  linarith

/-- Each term `w(1 - j(1 - c))` of the default is monotone in `c`. -/
private lemma difficultyWeight_le_of_le (N j : ℕ) {c b : ℝ} (hcb : c ≤ b) :
    difficultyWeight N (1 - j * (1 - c)) ≤ difficultyWeight N (1 - j * (1 - b)) :=
  difficultyWeight_mono N (by nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])

/-- For `c ≤ b < 1`, the default `d(c)` is the finite sum of its terms over
`1 ≤ j < ⌈(1 - b)⁻¹⌉`. -/
private lemma defaultWeight_eq_sum_Ico (N : ℕ) {c b : ℝ} (hcb : c ≤ b) (hb : b < 1) :
    defaultWeight N c =
      ∑ j ∈ Finset.Ico 1 ⌈(1 - b)⁻¹⌉₊, difficultyWeight N (1 - j * (1 - c)) :=
  finsum_mem_eq_sum_of_subset (s := Set.Ici 1) _
    (fun j hj => Finset.mem_Ico.mpr ⟨hj.1, Nat.lt_ceil.mpr <|
      lt_inv_of_difficultyWeight_ne_zero hb <| Nat.pos_iff_ne_zero.mp <|
        (Nat.pos_of_ne_zero hj.2).trans_le (difficultyWeight_le_of_le N j hcb)⟩)
    (fun _ hj => (Finset.mem_Ico.mp hj).1)

/-- For `b' ≤ b < 1`, the default weight at `b'` is at most the default weight at `b`,
at any scale `N`. -/
@[mmp "lem_oai4_difficulty_preparation_c"]
public theorem defaultWeight_le_defaultWeight {N : ℕ} {b b' : ℝ} (hbb : b' ≤ b) (hb : b < 1) :
    defaultWeight N b' ≤ defaultWeight N b := by
  rw [defaultWeight_eq_sum_Ico N hbb hb, defaultWeight_eq_sum_Ico N le_rfl hb]
  exact Finset.sum_le_sum fun j _ => difficultyWeight_le_of_le N j hbb

end MMP.Fourfold
