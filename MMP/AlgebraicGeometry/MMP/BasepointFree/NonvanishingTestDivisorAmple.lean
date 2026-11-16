module

public import MMP.AlgebraicGeometry.MMP.BasepointFree.ProofData
public import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
public import MMP.AlgebraicGeometry.Positivity.AmplePlusNefSum

/-!
# The test divisors of the non-vanishing theorem are ample

Let `(x, q, e, M; f; F_•; b_•; p_•; r_•)` be an adapted resolution of a smooth non-vanishing
datum `(X, D, G, a)` and `β, c ∈ ℚ` with `0 ≤ c ≤ ½` and `β ≥ a + c(q - a)`. Then the test
divisor `N(β, c) = β f^*D - K_Y + ∑_j (-c r_j + b_j - p_j) F_j` is ample.

Since the crepant boundary of `(X, -G)` on `Y` is `-∑_j b_j F_j`, the divisor
`K_Y - ∑_j b_j F_j` is numerically `f^*(K_X - G)` (KM 2.26), and `∑_j r_j F_j = f^*M` is
numerically `f^*(qD + G - K_X)` because `eM ∼ e(qD + G - K_X)`. Hence, modulo numerical
equivalence,
`N(β, c) ≡ (β - a - c(q - a)) f^*D + (½ - c) f^*(aD + G - K_X)`
`+ (½ f^*(aD + G - K_X) - ∑_j p_j F_j)`.
The first two summands are nef, as pull-backs of nef divisors with nonnegative coefficients,
and the last is ample; so `N(β, c)` is ample.

## Main results

* `MMP.Mori.IsNonvanishingAdaptedResolution.isAmple_of_isTieBreakerTestDivisor`: `N(β, c)` is
  ample for `0 ≤ c ≤ ½` and `a + c(q - a) ≤ β`.

## Implementation notes

The test divisor is the relation `MMP.Mori.IsTieBreakerTestDivisor`: `N` is a test divisor for
some canonical divisor `K_Y` of `Y` and the pull-back of `D`. The statement holds for every
such `N`, whatever canonical divisor `K_Y` is chosen. The rational `b` of the source is called
`β` here, to keep `b` for the discrepancies `b_j`.

All numerical identities are checked curve by curve. For a curve `C ⊆ Y` the map
`L ↦ (f^*L · C)` is a `ℚ`-linear form on the `ℚ`-divisors of the smooth variety `X`: it is `0`
if `f(C)` is a point and `L ↦ deg(C → f(C)) · (L · f(C))` otherwise (the projection formula);
it is nonnegative on nef divisors and vanishes on principal divisors.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Theorem 3.4, 3.5 Step 4
-/

@[expose] public section

namespace MMP.FourfoldProofs.Km3aNonvanishingTestDivisorAmpleProof

open CategoryTheory AlgebraicGeometry MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section Projection

variable {k : Type} [Field k]

/-- On a scheme all of whose `ℚ`-divisors are `ℚ`-Cartier, the intersection number with a fixed
proper curve is a `ℚ`-linear form on `ℚ`-divisors. -/
private noncomputable def intersectionLinearMap {W C : Scheme.{0}} [IsLocallyNoetherian W]
    [IsNormal W] (sW : W ⟶ Spec (.of k)) [QuasiCompact sW] (j : C ⟶ W) [IsProper (j ≫ sW)]
    (hdim : topologicalKrullDim C ≤ 1) (hQ : ∀ L : QDivisor W, L.IsQCartier) :
    QDivisor W →ₗ[ℚ] ℚ where
  toFun L := L.intersectionNumber k sW j hdim (hQ L)
  map_add' L L' := QDivisor.intersectionNumber_add' k sW j hdim L L' (hQ L) (hQ L') (hQ _)
  map_smul' q L := MMP.Fourfold.intersectionNumber_smul sW j hdim L (hQ L) q (hQ _)

private theorem intersectionLinearMap_apply {W C : Scheme.{0}} [IsLocallyNoetherian W]
    [IsNormal W] (sW : W ⟶ Spec (.of k)) [QuasiCompact sW] (j : C ⟶ W) [IsProper (j ≫ sW)]
    (hdim : topologicalKrullDim C ≤ 1) (hQ : ∀ L : QDivisor W, L.IsQCartier) (L : QDivisor W)
    (hL : L.IsQCartier) :
    intersectionLinearMap sW j hdim hQ L = L.intersectionNumber k sW j hdim hL := rfl

/-- Linearly equivalent Cartier divisors have the same intersection number with a proper
curve. -/
private theorem intersectionLinearMap_toQDivisor_eq {W C : Scheme.{0}} [IsLocallyNoetherian W]
    [IsNormal W] [CompactSpace W] (sW : W ⟶ Spec (.of k)) [QuasiCompact sW] (j : C ⟶ W)
    [IsProper (j ≫ sW)] (hdim : topologicalKrullDim C ≤ 1) (hQ : ∀ L : QDivisor W, L.IsQCartier)
    (hcart : ∀ L : Divisor W, L.IsCartier) {A A' : Divisor W} (h : A.LinearlyEquivalent A') :
    intersectionLinearMap sW j hdim hQ (Divisor.toQDivisor A) =
      intersectionLinearMap sW j hdim hQ (Divisor.toQDivisor A') := by
  rw [intersectionLinearMap_apply sW j hdim hQ _ (QDivisor.isQCartier_toQDivisor (hcart A)),
    intersectionLinearMap_apply sW j hdim hQ _ (QDivisor.isQCartier_toQDivisor (hcart A')),
    QDivisor.intersectionNumber_toQDivisor k sW j hdim _ (hcart A),
    QDivisor.intersectionNumber_toQDivisor k sW j hdim _ (hcart A')]
  have := (hcart A).isInvertibleModule_divisorialSheaf
  have := (hcart A').isInvertibleModule_divisorialSheaf
  rw [Divisor.degreeOn, Divisor.degreeOn, degreeOn_eq_of_iso k sW j hdim h.divisorialSheafIso]

/-- **The projection formula as a linear form.** Let `u : V ⟶ W` be a morphism of normal
varieties over `k`, every `ℚ`-divisor of `W` being `ℚ`-Cartier, and `C ⊆ V` a proper curve.
There is a `ℚ`-linear form `φ` on the `ℚ`-divisors of `W` with `(L' · C) = φ(L)` for every
pull-back `L' = u^*L`, nonnegative on nef divisors and equal on linearly equivalent divisors. -/
private theorem exists_linearMap_intersectionNumber_isPullback {V W C : Scheme.{0}}
    {sV : V ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)} [AlgebraicGeometry.IsVariety k sV]
    [AlgebraicGeometry.IsVariety k sW] [IsLocallyNoetherian V] [IsNormal V]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {u : V ⟶ W} (hu : u ≫ sW = sV)
    (i : C ⟶ V) [IsIntegral C] [AlgebraicGeometry.IsCurve k (i ≫ sV)] [IsProper (i ≫ sV)]
    (hQ : ∀ L : QDivisor W, L.IsQCartier) (hcart : ∀ L : Divisor W, L.IsCartier) :
    ∃ φ : QDivisor W →ₗ[ℚ] ℚ,
      (∀ (L : QDivisor W)
        (hLB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp)
        (L' : QDivisor V) (h : L.IsPullback u hLB L'),
          L'.intersectionNumber k sV i (IsCurve.topologicalKrullDim_eq_one (f := i ≫ sV)).le
            (h.isQCartier (hQ L)) = φ L) ∧
      (∀ L : QDivisor W, L.IsNef k sW → 0 ≤ φ L) ∧
      (∀ A A' : Divisor W, A.LinearlyEquivalent A' →
        φ (Divisor.toQDivisor A) = φ (Divisor.toQDivisor A')) := by
  by_cases hpt : ∃ w : W, Set.range (i ≫ u) = {w}
  · refine ⟨0, fun L hLB L' h => ?_, fun _ _ => le_rfl, fun _ _ _ => rfl⟩
    rw [intersectionNumber_pullback_eq_zero k sV sW u hu i (hQ L) h hpt]
    rfl
  · have e : (i ≫ u) ≫ sW = i ≫ sV := by rw [Category.assoc, hu]
    have : IsProper ((i ≫ u) ≫ sW) := e ▸ inferInstance
    have : AlgebraicGeometry.IsCurve k ((i ≫ u) ≫ sW) := e ▸ inferInstance
    have : IsProper (i ≫ u) := IsProper.of_comp (i ≫ u) sW
    have : IsProper ((i ≫ u).imageι ≫ sW) := isProper_imageι_comp (i ≫ u) sW
    have hcurve := isCurve_imageι_comp sW (i ≫ u) hpt
    set ι := intersectionLinearMap sW (i ≫ u).imageι hcurve.topologicalKrullDim_eq_one.le hQ
    refine ⟨(degreeOver (i ≫ u).toImage : ℚ) • ι, fun L hLB L' h => ?_, fun L hL => ?_,
      fun A A' hA => ?_⟩
    · rw [intersectionNumber_pullback_eq_degreeOver_mul k sV sW u hu i (hQ L) h hcurve]
      rfl
    · exact mul_nonneg (by positivity)
        (hL.2 _ (i ≫ u).imageι hcurve.topologicalKrullDim_eq_one)
    · simp only [LinearMap.smul_apply]
      rw [intersectionLinearMap_toQDivisor_eq sW _ _ hQ hcart hA]

/-- A non-negative multiple of a nef divisor is nef, on a scheme all of whose `ℚ`-divisors are
`ℚ`-Cartier. -/
private theorem isNef_smul {W : Scheme.{0}} [IsLocallyNoetherian W] [IsNormal W]
    {sW : W ⟶ Spec (.of k)} [QuasiCompact sW] (hQ : ∀ L : QDivisor W, L.IsQCartier)
    {L : QDivisor W} (hL : L.IsNef k sW) {t : ℚ} (ht : 0 ≤ t) : (t • L).IsNef k sW :=
  ⟨hQ _, fun C i _ _ _ hC => by
    rw [← intersectionLinearMap_apply sW i hC.le hQ, map_smul, smul_eq_mul]
    exact mul_nonneg ht (hL.2 C i hC)⟩

/-- The pull-back of a nef divisor along a morphism of normal varieties is nef, every
`ℚ`-divisor of the source and of the target being `ℚ`-Cartier. -/
private theorem isNef_of_isPullback {V W : Scheme.{0}} {sV : V ⟶ Spec (.of k)}
    {sW : W ⟶ Spec (.of k)} [AlgebraicGeometry.IsVariety k sV] [AlgebraicGeometry.IsVariety k sW]
    [IsLocallyNoetherian V] [IsNormal V] [QuasiCompact sV] [IsLocallyNoetherian W] [IsNormal W]
    [CompactSpace W] [QuasiCompact sW] {u : V ⟶ W} (hu : u ≫ sW = sV)
    (hQV : ∀ L : QDivisor V, L.IsQCartier) (hQ : ∀ L : QDivisor W, L.IsQCartier)
    (hcart : ∀ L : Divisor W, L.IsCartier) {L : QDivisor W} (hL : L.IsNef k sW) {hLB}
    {L' : QDivisor V} (h : L.IsPullback u hLB L') : L'.IsNef k sV :=
  ⟨hQV _, fun C i _ _ _ hC => by
    have : AlgebraicGeometry.IsCurve k (i ≫ sV) := { topologicalKrullDim_eq_one := hC }
    obtain ⟨φ, hφ, hφnef, -⟩ := exists_linearMap_intersectionNumber_isPullback hu i hQ hcart
    exact (hφnef L hL).trans_eq (hφ L hLB L' h).symm⟩

end Projection

/-- A dominant morphism of integral schemes maps the generic point outside every divisor. -/
private theorem map_componentGenericPoint_notMem_supp {X : Scheme.{0}} [IsIntegral X]
    {Y : Scheme.{0}} [IsIntegral Y] (f : Y ⟶ X) [IsDominant f] {R : Type*} [Zero R]
    (D : DivisorWithCoeffs R X) (Z : irreducibleComponents Y) :
    f (componentGenericPoint Y Z) ∉ D.supp := by
  rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant]
  exact MMP.Fourfold.genericPoint_notMem_supp _

/-- The pull-back of a nonzero rational form along a birational morphism is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {k : Type} [Field k] [PerfectField k]
    {X Y : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX]
    {d : ℕ} (hd : topologicalKrullDim X = d) (g : Y ⟶ X) [IsIntegral Y] [IsDominant g]
    (hg : IsBirationalMorphism g) {m : ℤ} {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) :
    pullbackRationalPluriForms sX g τ ≠ 0 := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (g ≫ sX)
  let := functionFieldMapAlgebra g
  have := isScalarTower_functionFieldMap sX g
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX g hg.functionFieldMap_bijective
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hd)
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := (pullbackForms_eq hω m τ).symm.trans h0
  have h1 : algebraMap X.functionField Y.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← repr_pullbackFormsAlong hω m τ, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

/-- **`K_Y - ∑_j b_j F_j` is a pull-back of `K_X - G`** up to linear equivalence (KM 2.26). For
an adapted resolution of a smooth non-vanishing datum and a canonical divisor `K_Y` of `Y`, there
is a divisor `K_Y' ∼ K_Y` with `f^*(K_X - G) = K_Y' - ∑_j b_j F_j`: with `K_X = div(ω)`, take
`K_Y' = div(f^*ω)`. -/
private theorem exists_isPullback_canonical_sub {k : Type} [Field k] [IsAlgClosed k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ} {K D : Divisor X} {G : QDivisor X}
    {a : ℚ} {x : X} {q e : ℤ} {M : QDivisor X} {Y : Scheme.{0}} [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X} {s : ℕ}
    {F : Fin (s + 1) → MMP.Mori.PrimeDivisor Y} {b p r : Fin (s + 1) → ℚ}
    (h : IsNonvanishingAdaptedResolution sX n K D G a x q e M f F b p r) {KY : Divisor Y}
    (hKY : KY.IsCanonicalDivisor (f ≫ sX) n) :
    ∃ KY' : Divisor Y, KY'.LinearlyEquivalent KY ∧
      ∃ hB, (Divisor.toQDivisor K + -G).IsPullback f hB
        (Divisor.toQDivisor KY' + -∑ j, Finsupp.single (F j) (b j)) := by
  obtain ⟨hYn, hcrep⟩ := h.isCrepantBoundary
  have hfb : IsBirationalMorphism f := h.isLogResolution.isBirationalMorphism
  have : IsIntegral Y := hYn.1.toIsIntegral
  have : IsDominant f := hfb.isDominant
  have : LocallyOfFiniteType (f ≫ sX) := hYn.1.toLocallyOfFiniteType
  have hX : IsNormalVariety k sX := h.isKltPair.1.1
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hK : K.IsCanonicalDivisor sX n := h.isKltPair.1.2.1
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  have hωK' : divisorOfForm ω = K := by
    ext Γ
    rw [coeff_divisorOfForm, hωK]
  have hlin : (divisorOfForm (pullbackRationalPluriForms sX f ω)).LinearlyEquivalent KY := by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hYn hKY
      (pullbackRationalPluriForms_ne_zero sX hK.topologicalKrullDim_eq f hfb hω0)
  exact ⟨_, hlin, (h.isKltPair.isPair.isPullback_of_isCrepantBoundary f hYn hfb hK
    (hKY.of_linearlyEquivalent hlin) (Or.inl ⟨ω, hω0, hωK', rfl⟩) hcrep).2.2⟩

/-- **`M` is numerically `qD + G - K_X`.** A `ℚ`-linear form on the `ℚ`-divisors of `X`
that is constant on linear equivalence classes takes the same value on `M` as on
`qD + G - K_X`, since `eM ∼ e(qD + G - K_X)` with `e ≥ 1`. -/
private theorem map_M_eq {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] {n : ℕ} {K D : Divisor X} {G : QDivisor X} {a : ℚ} {x : X} {q e : ℤ}
    {M : QDivisor X} {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    {f : Y ⟶ X} {s : ℕ} {F : Fin (s + 1) → MMP.Mori.PrimeDivisor Y} {b p r : Fin (s + 1) → ℚ}
    (h : IsNonvanishingAdaptedResolution sX n K D G a x q e M f F b p r)
    (φ : QDivisor X →ₗ[ℚ] ℚ)
    (hφ : ∀ A A' : Divisor X, A.LinearlyEquivalent A' →
      φ (Divisor.toQDivisor A) = φ (Divisor.toQDivisor A')) :
    φ M = q * φ (Divisor.toQDivisor D) + φ G - φ (Divisor.toQDivisor K) := by
  obtain ⟨M', G', hM', hG', hMlin⟩ := h.linearlyEquivalent
  have h1 := hφ _ _ hMlin
  simp only [map_sub, map_add, map_zsmul, hM', hG', ← Int.cast_smul_eq_zsmul ℚ, map_smul,
    smul_eq_mul] at h1
  have he : (e : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (by have := h.one_le_e; omega)
  apply mul_left_cancel₀ he
  push_cast at h1
  linear_combination h1

/-- **The test divisor is numerically a sum of nef and ample pieces.** Modulo numerical
equivalence, `N(β, c) = β f^*D - K_Y + ∑_j (-c r_j + b_j - p_j) F_j` is
`(½ f^*P - ∑_j p_j F_j) + (β - a - c(q - a)) f^*D + (½ - c) f^*P` with `P = aD + G - K_X`. -/
private theorem numericallyEquivalent_testDivisor {k : Type} [Field k] [IsAlgClosed k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ} {K D : Divisor X} {G : QDivisor X}
    {a : ℚ} {x : X} {q e : ℤ} {M : QDivisor X} {Y : Scheme.{0}} [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X} {s : ℕ}
    {F : Fin (s + 1) → MMP.Mori.PrimeDivisor Y} {b p r : Fin (s + 1) → ℚ}
    (h : IsNonvanishingAdaptedResolution sX n K D G a x q e M f F b p r) {KY : Divisor Y}
    (hKY : KY.IsCanonicalDivisor (f ≫ sX) n) {hBD} {D' : Divisor Y} (hD' : D.IsPullback f hBD D')
    {hBB} {B' : QDivisor Y}
    (hB' : (a • Divisor.toQDivisor D + G - Divisor.toQDivisor K).IsPullback f hBB B')
    (β c : ℚ) :
    (β • Divisor.toQDivisor D' - Divisor.toQDivisor KY +
        ∑ j, Finsupp.single (F j) (-c * r j + b j - p j)).NumericallyEquivalent k (f ≫ sX)
      (((1 / 2 : ℚ) • B' - ∑ j, Finsupp.single (F j) (p j)) +
        ((β - a - c * (q - a)) • Divisor.toQDivisor D' + (1 / 2 - c) • B')) := by
  obtain ⟨hYn, -⟩ := h.isCrepantBoundary
  have hsm : IsSmoothScheme (f ≫ sX) := h.isLogResolution.isSmoothScheme
  have : AlgebraicGeometry.IsProjectiveVariety k (f ≫ sX) := h.isProjectiveVariety_source
  have : AlgebraicGeometry.IsProperVariety k sX := h.isProperVariety
  have : IsIntegral Y := hYn.1.toIsIntegral
  have : IsDominant f := h.isLogResolution.isBirationalMorphism.isDominant
  have hQ := MMP.Fourfold.isQCartier_of_isSmoothScheme hsm
  have hcart := MMP.Fourfold.isCartier_of_isSmoothScheme hsm
  have hDp := QDivisor.isPullback_toQDivisor h.isCartier
    (map_componentGenericPoint_notMem_supp f _) hD'
  obtain ⟨KY', hKY', _, hWp⟩ := exists_isPullback_canonical_sub h hKY
  obtain ⟨_, hRp⟩ := h.isPullback_M
  have hsum : (∑ j, Finsupp.single (F j) (-c * r j + b j - p j) : QDivisor Y) =
      ∑ j, Finsupp.single (F j) (b j) - ∑ j, Finsupp.single (F j) (p j) -
        c • ∑ j, Finsupp.single (F j) (r j) := by
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finsupp.smul_single, ← Finsupp.single_sub, ← Finsupp.single_sub, smul_eq_mul]
    congr 1
    ring
  refine ⟨hQ _, hQ _, fun C i _ _ _ hC => ?_⟩
  have : AlgebraicGeometry.IsCurve k (i ≫ f ≫ sX) := { topologicalKrullDim_eq_one := hC }
  obtain ⟨φ, hφ, -, hφlin⟩ := exists_linearMap_intersectionNumber_isPullback (sV := f ≫ sX)
    rfl i (MMP.Fourfold.isQCartier_of_isSmoothScheme h.isSmoothScheme)
    (MMP.Fourfold.isCartier_of_isSmoothScheme h.isSmoothScheme)
  rw [← intersectionLinearMap_apply (f ≫ sX) i hC.le hQ,
    ← intersectionLinearMap_apply (f ≫ sX) i hC.le hQ]
  set ι := intersectionLinearMap (f ≫ sX) i hC.le hQ
  have eD : ι (Divisor.toQDivisor D') = φ (Divisor.toQDivisor D) := hφ _ _ _ hDp
  have eB : ι B' = φ (a • Divisor.toQDivisor D + G - Divisor.toQDivisor K) := hφ _ _ _ hB'
  have eW : ι (Divisor.toQDivisor KY' + -∑ j, Finsupp.single (F j) (b j)) =
      φ (Divisor.toQDivisor K + -G) := hφ _ _ _ hWp
  have eR : ι (∑ j, Finsupp.single (F j) (r j)) = φ M := hφ _ _ _ hRp
  have eKY : ι (Divisor.toQDivisor KY') = ι (Divisor.toQDivisor KY) :=
    intersectionLinearMap_toQDivisor_eq (f ≫ sX) i hC.le hQ hcart hKY'
  have eM := map_M_eq h φ hφlin
  rw [hsum]
  simp only [map_add, map_sub, map_neg, map_smul, smul_eq_mul] at eB eW ⊢
  linear_combination (a + c * q - c * a) * eD - c * eR - c * eM - (1 - c) * eB - eW + eKY

end MMP.FourfoldProofs.Km3aNonvanishingTestDivisorAmpleProof

open CategoryTheory AlgebraicGeometry MMP.FourfoldProofs.Km3aNonvanishingTestDivisorAmpleProof

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori

/-- **The test divisors are ample** (Kollár–Mori 3.5, Step 4). Let
`(x, q, e, M; f; F_•; b_•; p_•; r_•)` be an adapted resolution of a smooth non-vanishing datum
`(X, D, G, a)`, and `β, c` rationals with `0 ≤ c ≤ ½` and `a + c(q - a) ≤ β`. Then the test
divisor `N(β, c) = β f^*D - K_Y + ∑_j (-c r_j + b_j - p_j) F_j` is ample. -/
@[mmp "lem_km3a_nonvanishing_test_divisor_ample"]
public theorem IsNonvanishingAdaptedResolution.isAmple_of_isTieBreakerTestDivisor
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] {n : ℕ} {K D : Divisor X} {G : QDivisor X} {a : ℚ} {x : X} {q e : ℤ}
    {M : QDivisor X} {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    {f : Y ⟶ X} {s : ℕ} {F : Fin (s + 1) → PrimeDivisor Y} {b p r : Fin (s + 1) → ℚ}
    (h : IsNonvanishingAdaptedResolution sX n K D G a x q e M f F b p r)
    {KY : Divisor Y} {β c : ℚ} {N : QDivisor Y} (_hc₀ : 0 ≤ c) (hc : c ≤ 1 / 2)
    (hβ : a + c * (q - a) ≤ β) (hN : IsTieBreakerTestDivisor sX n D f KY F r b p β c N) :
    N.IsAmple := by
  obtain ⟨hKY, _, D', hD', rfl⟩ := hN
  obtain ⟨hYn, -⟩ := h.isCrepantBoundary
  have hsm : IsSmoothScheme (f ≫ sX) := h.isLogResolution.isSmoothScheme
  have : AlgebraicGeometry.IsProjectiveVariety k (f ≫ sX) := h.isProjectiveVariety_source
  have : AlgebraicGeometry.IsProperVariety k sX := h.isProperVariety
  have : IsIntegral Y := hYn.1.toIsIntegral
  have : IsDominant f := h.isLogResolution.isBirationalMorphism.isDominant
  have hQ := MMP.Fourfold.isQCartier_of_isSmoothScheme hsm
  have hQX := MMP.Fourfold.isQCartier_of_isSmoothScheme h.isSmoothScheme
  have hcartX := MMP.Fourfold.isCartier_of_isSmoothScheme h.isSmoothScheme
  obtain ⟨_, B', hB', hA⟩ := h.isAmple_half
  refine QDivisor.isAmple_of_numericallyEquivalent_add_sum_of_isNef (f ≫ sX)
    (Finset.univ : Finset (Fin 2))
    ![(β - a - c * (q - a)) • Divisor.toQDivisor D', (1 / 2 - c) • B'] hA (fun j _ => ?_)
    (by rw [Fin.sum_univ_two]; exact numericallyEquivalent_testDivisor h hKY hD' hB' β c)
  fin_cases j
  · refine isNef_smul hQ (isNef_of_isPullback (sV := f ≫ sX) rfl hQ hQX hcartX
      ((QDivisor.isNef_toQDivisor_iff D h.isCartier).mpr h.isNef)
      (QDivisor.isPullback_toQDivisor h.isCartier
        (map_componentGenericPoint_notMem_supp f _) hD')) (by linarith)
  · exact isNef_smul hQ (isNef_of_isPullback (sV := f ≫ sX) rfl hQ hQX hcartX h.isNef_add hB')
      (by linarith)

end MMP.Mori

end
