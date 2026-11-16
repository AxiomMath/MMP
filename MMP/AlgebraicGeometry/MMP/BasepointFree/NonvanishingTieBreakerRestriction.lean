module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.BasepointFree.ProofData
public import MMP.AlgebraicGeometry.Divisor.Arithmetic
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
import MMP.AlgebraicGeometry.Positivity.AmpleNefBig
import MMP.AlgebraicGeometry.MMP.BasepointFree.NonvanishingTestDivisorAmple
import MMP.AlgebraicGeometry.Positivity.AmpleAdjunctionRestriction
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
public import MMP.AlgebraicGeometry.Morphisms.HProjective

/-!
# The tie-breaking divisor carries a smooth non-vanishing datum

Let `(x, q, e, M; f; F_0, …, F_s; b_•; p_•; r_•)` be an adapted resolution of a smooth
non-vanishing datum `(X, D, G, a)` of dimension `d`, with a tie-breaker `(j', c)` and test
boundary `A = ∑_{j ≠ j'} (-c r_j + b_j - p_j) F_j`, and put `F = F_{j'}`. If `D_F` is a Cartier
divisor on `F` with `𝒪_F(D_F) ≅ 𝒪_Y(f^*D)|_F` and `b₁ ≥ a + c(q - a)` is an integer, then
`(F, D_F, A|_F, b₁)` is a smooth non-vanishing datum of dimension `d - 1`. This is the step of
the proof of the non-vanishing theorem where the induction hypothesis is applied to `F`.

Indeed `F` is a smooth prime divisor of the smooth projective variety `Y`; `D_F` is nef since
`f^*D` is; the coefficients of `A|_F` are among the `-c r_j + b_j - p_j > -1` (`j ≠ j'`) and its
support is snc, so `(F, -A|_F)` is klt; and `N(b₁, c) = b₁ f^*D + A - F - K_Y` is ample, so by
adjunction `b₁ D_F + A|_F - K_F` is ample.

## Main results

* `MMP.Mori.IsNonvanishingTieBreaker.isSmoothNonvanishingDatum_restrictPrimeDivisor`: the
  restriction statement.

## Implementation notes

The prime divisor `F_{j'}` is regarded as the integral closed subscheme
`(F j').idealSheaf.subscheme`, over `k` through `(F j').idealSheaf.subschemeι ≫ f ≫ sX`, and
`A|_F` is `MMP.Mori.DivisorWithCoeffs.restrictPrimeDivisor`. The pull-back `f^*D` is any `D'`
with `D.IsPullback f hB D'`, and `𝒪_Y(f^*D)|_F` is the pull-back of `𝒪_Y(D')` along the closed
immersion. A non-vanishing datum carries its canonical divisor explicitly; the conclusion holds
for every canonical divisor `K_F` of `F` of dimension `d - 1`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Theorem 3.4, 3.5 Step 6
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

section Relation

variable {k : Type} [Field k] {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)}
  [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
  {F : PrimeDivisor Y} [IsLocallyNoetherian F.idealSheaf.subscheme]
  [IsNormal F.idealSheaf.subscheme] [CompactSpace F.idealSheaf.subscheme]

/-- `𝒪_F(E') ≅ ι^* 𝒪_Y(E)` is additive in `(E, E')`, for the inclusion `ι` of a smooth prime
divisor `F` of a smooth scheme. -/
private theorem nonempty_divisorialSheaf_add_iso (hY : IsSmoothScheme sY)
    (hF : IsSmoothScheme (F.idealSheaf.subschemeι ≫ sY)) {a b : Divisor Y}
    {a' b' : Divisor F.idealSheaf.subscheme}
    (ha : Nonempty (a'.divisorialSheaf ≅
      (Scheme.Modules.pullback F.idealSheaf.subschemeι).obj a.divisorialSheaf))
    (hb : Nonempty (b'.divisorialSheaf ≅
      (Scheme.Modules.pullback F.idealSheaf.subschemeι).obj b.divisorialSheaf)) :
    Nonempty ((a' + b').divisorialSheaf ≅
      (Scheme.Modules.pullback F.idealSheaf.subschemeι).obj (a + b).divisorialSheaf) := by
  obtain ⟨ea⟩ := ha
  obtain ⟨eb⟩ := hb
  have hc : ∀ D : Divisor Y, D.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hY
  have hc' : ∀ D : Divisor F.idealSheaf.subscheme, D.IsCartier :=
    MMP.Fourfold.isCartier_of_isSmoothScheme hF
  exact ⟨((hc' a').divisorialSheafTensorIso (hc' b')).symm ≪≫ MonoidalCategory.tensorIso ea eb ≪≫
    (Stacks.RelativeVeryAmple.pullbackTensorModulesIso F.idealSheaf.subschemeι _ _).symm ≪≫
    (Scheme.Modules.pullback F.idealSheaf.subschemeι).mapIso
      ((hc a).divisorialSheafTensorIso (hc b))⟩

/-- `𝒪_F(E') ≅ ι^* 𝒪_Y(E)` passes to positive multiples. -/
private theorem nonempty_divisorialSheaf_nsmul_iso (hY : IsSmoothScheme sY)
    (hF : IsSmoothScheme (F.idealSheaf.subschemeι ≫ sY)) {a : Divisor Y}
    {a' : Divisor F.idealSheaf.subscheme}
    (ha : Nonempty (a'.divisorialSheaf ≅
      (Scheme.Modules.pullback F.idealSheaf.subschemeι).obj a.divisorialSheaf))
    {j : ℕ} (hj : 0 < j) :
    Nonempty (((j : ℤ) • a').divisorialSheaf ≅
      (Scheme.Modules.pullback F.idealSheaf.subschemeι).obj ((j : ℤ) • a).divisorialSheaf) := by
  induction j, Nat.one_le_iff_ne_zero.mpr hj.ne' using Nat.le_induction with
  | base => simpa using ha
  | succ j hj ih =>
    simpa [add_smul] using nonempty_divisorialSheaf_add_iso hY hF (ih (by omega)) ha

end Relation

section Restriction

variable {Y : Scheme.{0}} {ι : Type*}

/-- The coefficients of the restriction of `∑_{j ∈ s} γ_j F_j` to a prime divisor `F_{j'}`
(`j' ∉ s`, the `F_j` distinct) are `∑_{j ∈ s} (F_j · Q) γ_j`. -/
private theorem coeff_restrictPrimeDivisor_sum_single [IsLocallyNoetherian Y] [CompactSpace Y]
    {R : Type*} [AddCommMonoid R] (F : ι → PrimeDivisor Y) (hF : Function.Injective F)
    (s : Finset ι) {j' : ι} (hj' : j' ∉ s) (γ : ι → R)
    (Q : PrimeDivisor (F j').idealSheaf.subscheme) :
    (DivisorWithCoeffs.restrictPrimeDivisor (∑ j ∈ s, Finsupp.single (F j) (γ j)) (F j')).coeff
        Q = ∑ j ∈ s, (F j).intersectionLength (F j').idealSheaf.subschemeι Q • γ j := by
  classical
  have : IsNoetherian Y := ⟨⟩
  have h0 : DivisorWithCoeffs.coeff (∑ j ∈ s, Finsupp.single (F j) (γ j)) (F j') = 0 := by
    rw [DivisorWithCoeffs.coeff, Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun j hj => ?_
    exact Finsupp.single_eq_of_ne fun h => hj' ((hF h).symm ▸ hj)
  rw [DivisorWithCoeffs.coeff_restrictPrimeDivisor _ _ h0,
    ← Finsupp.sum_finsetSum_index (fun _ => smul_zero _) (fun _ _ _ => smul_add _ _ _)]
  exact Finset.sum_congr rfl fun j _ => Finsupp.sum_single_index (smul_zero _)

/-- A sum `∑_{j ∈ s} ℓ_j β_j` of natural multiples with `∑_{j ∈ s} ℓ_j = 1` is one of the
`β_j`. -/
private theorem exists_sum_nsmul_eq_of_sum_eq_one {M : Type*} [AddCommMonoid M] (s : Finset ι)
    (ℓ : ι → ℕ) (β : ι → M) (h : ∑ j ∈ s, ℓ j = 1) : ∃ j ∈ s, ∑ i ∈ s, ℓ i • β i = β j := by
  classical
  obtain ⟨j, hj, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h.trans_ne one_ne_zero)
  have hsplit := Finset.add_sum_erase s ℓ hj
  rw [h] at hsplit
  have hrest : ∑ i ∈ s.erase j, ℓ i = 0 := by omega
  have hj1 : ℓ j = 1 := by omega
  rw [Finset.sum_eq_zero_iff] at hrest
  refine ⟨j, hj, ?_⟩
  rw [Finset.sum_eq_single_of_mem j hj fun i hi hij => by
    rw [hrest i (Finset.mem_erase.mpr ⟨hij, hi⟩), zero_smul], hj1, one_smul]

/-- **The restriction of a combination of snc components.** Let `Y` be a smooth variety over an
algebraically closed field of characteristic zero, `F_j` distinct prime divisors of `Y` and
`j' ∉ s` such that `F_{j'} + ∑_{j ∈ s} F_j` is snc. For `A = ∑_{j ∈ s} β_j F_j`, the support of
`A|_{F_{j'}}` is an snc divisor on `F_{j'}`, and every coefficient of `A|_{F_{j'}}` is `0` or one
of the `β_j`. -/
private theorem isSNC_and_coeff_restrictPrimeDivisor {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] (sY : Y ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sY] [Smooth sY]
    (F : ι → PrimeDivisor Y) (hF : Function.Injective F) (s : Finset ι) {j' : ι}
    (hj' : j' ∉ s)
    (hsnc : DivisorWithCoeffs.IsSNC sY
      (Finsupp.single (F j') (1 : ℤ) + ∑ j ∈ s, Finsupp.single (F j) (1 : ℤ)))
    (β : ι → ℚ) :
    DivisorWithCoeffs.IsSNC ((F j').idealSheaf.subschemeι ≫ sY)
        (DivisorWithCoeffs.restrictPrimeDivisor (∑ j ∈ s, Finsupp.single (F j) (β j)) (F j')) ∧
      ∀ Q, (DivisorWithCoeffs.restrictPrimeDivisor (∑ j ∈ s, Finsupp.single (F j) (β j))
          (F j')).coeff Q = 0 ∨
        ∃ j ∈ s, (DivisorWithCoeffs.restrictPrimeDivisor
          (∑ j ∈ s, Finsupp.single (F j) (β j)) (F j')).coeff Q = β j := by
  classical
  obtain ⟨_, _, _, _⟩ := (isVariety_iff k sY).mp ‹_›
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  set D := s.image F
  have hFD : F j' ∉ D := fun h => by
    obtain ⟨j, hj, hjF⟩ := Finset.mem_image.mp h
    exact hj' (hF hjF ▸ hj)
  have hsum : ∑ E ∈ D, Finsupp.single E (1 : ℤ) = ∑ j ∈ s, Finsupp.single (F j) (1 : ℤ) :=
    Finset.sum_image fun _ _ _ _ h => hF h
  obtain ⟨hsncT, hone⟩ :=
    DivisorWithCoeffs.isSNC_restrictPrimeDivisor_sum_single sY (F j') D hFD (by rwa [hsum])
  rw [hsum] at hsncT hone
  set A : QDivisor Y := ∑ j ∈ s, Finsupp.single (F j) (β j)
  set T : Divisor Y := ∑ j ∈ s, Finsupp.single (F j) (1 : ℤ)
  have hAc : ∀ Q, (A.restrictPrimeDivisor (F j')).coeff Q =
      ∑ j ∈ s, (F j).intersectionLength (F j').idealSheaf.subschemeι Q • β j :=
    coeff_restrictPrimeDivisor_sum_single F hF s hj' β
  have hTc : ∀ Q, (T.restrictPrimeDivisor (F j')).coeff Q =
      ∑ j ∈ s, (F j).intersectionLength (F j').idealSheaf.subschemeι Q • (1 : ℤ) :=
    coeff_restrictPrimeDivisor_sum_single F hF s hj' (fun _ => (1 : ℤ))
  have hTcQ : ∀ Q, (T.restrictPrimeDivisor (F j')).coeff Q =
      ((∑ j ∈ s, (F j).intersectionLength (F j').idealSheaf.subschemeι Q : ℕ) : ℤ) := by
    intro Q
    rw [hTc]
    push_cast
    simp
  have hsupp :
      (A.restrictPrimeDivisor (F j')).support ⊆ (T.restrictPrimeDivisor (F j')).support := by
    intro Q hQ
    rw [Finsupp.mem_support_iff] at hQ ⊢
    change (A.restrictPrimeDivisor (F j')).coeff Q ≠ 0 at hQ
    change (T.restrictPrimeDivisor (F j')).coeff Q ≠ 0
    rw [hAc] at hQ
    obtain ⟨j, hj, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hQ
    have hl : (F j).intersectionLength (F j').idealSheaf.subschemeι Q ≠ 0 := by
      rintro h0
      exact hne (by rw [h0, zero_smul])
    rw [hTcQ]
    exact_mod_cast (Finset.sum_pos' (fun _ _ => Nat.zero_le _)
      ⟨j, hj, Nat.pos_of_ne_zero hl⟩).ne'
  refine ⟨hsncT.of_support_subset hsupp, fun Q => or_iff_not_imp_left.mpr fun hQ => ?_⟩
  have hQT := hone Q (hsupp (Finsupp.mem_support_iff.mpr hQ))
  rw [hTcQ] at hQT
  rw [hAc]
  exact exists_sum_nsmul_eq_of_sum_eq_one s _ β (by exact_mod_cast hQT)

end Restriction

section Nef

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

/-- **The projection formula as a linear form.** For a morphism `u : V ⟶ W` of normal varieties
over `k`, every `ℚ`-divisor of `W` being `ℚ`-Cartier, and a proper curve `C ⊆ V`, there is a
`ℚ`-linear form `φ` on the `ℚ`-divisors of `W`, nonnegative on nef divisors, with
`(L' · C) = φ(L)` for every pull-back `L' = u^*L`. -/
private theorem exists_linearMap_intersectionNumber_isPullback {V W C : Scheme.{0}}
    {sV : V ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)} [AlgebraicGeometry.IsVariety k sV]
    [AlgebraicGeometry.IsVariety k sW] [IsLocallyNoetherian V] [IsNormal V]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {u : V ⟶ W} (hu : u ≫ sW = sV)
    (i : C ⟶ V) [AlgebraicGeometry.IsCurve k (i ≫ sV)] [IsProper (i ≫ sV)]
    (hQ : ∀ L : QDivisor W, L.IsQCartier) :
    ∃ φ : QDivisor W →ₗ[ℚ] ℚ,
      (∀ (L : QDivisor W)
        (hLB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp)
        (L' : QDivisor V) (h : L.IsPullback u hLB L'),
          L'.intersectionNumber k sV i (IsCurve.topologicalKrullDim_eq_one (f := i ≫ sV)).le
            (h.isQCartier (hQ L)) = φ L) ∧
      (∀ L : QDivisor W, L.IsNef k sW → 0 ≤ φ L) := by
  by_cases hpt : ∃ w : W, Set.range (i ≫ u) = {w}
  · refine ⟨0, fun L hLB L' h => ?_, fun _ _ => le_rfl⟩
    rw [intersectionNumber_pullback_eq_zero k sV sW u hu i (hQ L) h hpt]
    rfl
  · have e : (i ≫ u) ≫ sW = i ≫ sV := by rw [Category.assoc, hu]
    have : IsProper ((i ≫ u) ≫ sW) := e ▸ inferInstance
    have : AlgebraicGeometry.IsCurve k ((i ≫ u) ≫ sW) := e ▸ inferInstance
    have : IsProper (i ≫ u) := IsProper.of_comp (i ≫ u) sW
    have : IsProper ((i ≫ u).imageι ≫ sW) := isProper_imageι_comp (i ≫ u) sW
    have hcurve := isCurve_imageι_comp sW (i ≫ u) hpt
    refine ⟨(degreeOver (i ≫ u).toImage : ℚ) •
      intersectionLinearMap sW (i ≫ u).imageι hcurve.topologicalKrullDim_eq_one.le hQ,
      fun L hLB L' h => ?_, fun L hL => ?_⟩
    · rw [intersectionNumber_pullback_eq_degreeOver_mul k sV sW u hu i (hQ L) h hcurve]
      rfl
    · exact mul_nonneg (by positivity)
        (hL.2 _ (i ≫ u).imageι hcurve.topologicalKrullDim_eq_one)

/-- The pull-back of a nef divisor along a morphism of normal varieties is nef, every
`ℚ`-divisor of the source and of the target being `ℚ`-Cartier. -/
private theorem isNef_of_isPullback {V W : Scheme.{0}} {sV : V ⟶ Spec (.of k)}
    {sW : W ⟶ Spec (.of k)} [AlgebraicGeometry.IsVariety k sV] [AlgebraicGeometry.IsVariety k sW]
    [IsLocallyNoetherian V] [IsNormal V] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    {u : V ⟶ W} (hu : u ≫ sW = sV)
    (hQV : ∀ L : QDivisor V, L.IsQCartier) (hQ : ∀ L : QDivisor W, L.IsQCartier)
    {L : QDivisor W} (hL : L.IsNef k sW) {hLB}
    {L' : QDivisor V} (h : L.IsPullback u hLB L') : L'.IsNef k sV :=
  ⟨hQV _, fun C i _ _ _ hC => by
    have : AlgebraicGeometry.IsCurve k (i ≫ sV) := { topologicalKrullDim_eq_one := hC }
    obtain ⟨φ, hφ, hφnef⟩ := exists_linearMap_intersectionNumber_isPullback hu i hQ
    exact (hφnef L hL).trans_eq (hφ L hLB L' h).symm⟩

/-- **Restriction of a nef divisor to a closed subscheme.** If `E` is a nef Cartier divisor on
`Y` and `E'` a Cartier divisor on a closed subscheme `ι : Z ⟶ Y` with `𝒪_Z(E') ≅ ι^* 𝒪_Y(E)`,
then `E'` is nef. -/
private theorem isNef_of_nonempty_divisorialSheaf_iso {Y Z : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} [IsLocallyNoetherian Y] [IsNormal Y] [QuasiCompact sY]
    [IsLocallyNoetherian Z] [IsNormal Z] (ι : Z ⟶ Y) [IsClosedImmersion ι] [QuasiCompact (ι ≫ sY)]
    {E : Divisor Y} (hE : E.IsNef k sY) {E' : Divisor Z} (hE' : E'.IsCartier)
    (he : Nonempty (E'.divisorialSheaf ≅ (Scheme.Modules.pullback ι).obj E.divisorialSheaf)) :
    E'.IsNef k (ι ≫ sY) := by
  obtain ⟨hEc, hEn⟩ := hE
  obtain ⟨e⟩ := he
  refine ⟨hE', fun C i _ _ _ hC => ?_⟩
  have : IsProper ((i ≫ ι) ≫ sY) := by rw [Category.assoc]; infer_instance
  have h0 := hEn C (i ≫ ι) hC
  have := QuasiCompact.compactSpace_of_compactSpace sY
  have := QuasiCompact.compactSpace_of_compactSpace (ι ≫ sY)
  have := hEc.isInvertibleModule_divisorialSheaf
  have := hE'.isInvertibleModule_divisorialSheaf
  unfold Divisor.degreeOn at h0 ⊢
  rw [degreeOn_eq_of_iso k (ι ≫ sY) i hC.le e,
    degreeOn_pullback_eq_degreeOn_comp (ι ≫ sY) sY ι i rfl hC.le]
  exact h0

end Nef

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral in
/-- **The tie-breaking divisor carries a smooth non-vanishing datum** (Kollár–Mori 3.5,
Step 6). Let `(x, q, e, M; f; F_•; b_•; p_•; r_•)` be an adapted resolution of a smooth
non-vanishing datum `(X, D, G, a)` of dimension `n` with a tie-breaker `(j', c)`, let
`A = ∑_{j ≠ j'} (-c r_j + b_j - p_j) F_j` be the test boundary and `ι` the inclusion of
`F = F_{j'}`. Let `D'` be a pull-back of `D` along `f`, `D_F` a Cartier divisor on `F` with
`𝒪_F(D_F) ≅ ι^* 𝒪_Y(D')`, and `b₁ ≥ a + c(q - a)` an integer. Then for every canonical divisor
`K_F` of `F`, `(F, D_F, A|_F, b₁)` is a smooth non-vanishing datum of dimension `n - 1`. -/
@[mmp "lem_km3a_nonvanishing_restriction_hypotheses"]
public theorem IsNonvanishingTieBreaker.isSmoothNonvanishingDatum_restrictPrimeDivisor
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] {n : ℕ} {K D : Divisor X} {G : QDivisor X} {a : ℚ} {x : X} {q e : ℤ}
    {M : QDivisor X} {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    {f : Y ⟶ X} {s : ℕ} {F : Fin (s + 1) → PrimeDivisor Y} {b p r : Fin (s + 1) → ℚ}
    {j' : Fin (s + 1)} {c : ℚ}
    (h : IsNonvanishingTieBreaker sX n K D G a x q e M f F b p r j' c)
    [IsIntegral (F j').idealSheaf.subscheme] [IsLocallyNoetherian (F j').idealSheaf.subscheme]
    [IsNormal (F j').idealSheaf.subscheme] [CompactSpace (F j').idealSheaf.subscheme]
    [QuasiCompact ((F j').idealSheaf.subschemeι ≫ f ≫ sX)]
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp}
    {D' : Divisor Y} (hD' : D.IsPullback f hB D')
    {DF : Divisor (F j').idealSheaf.subscheme} (hDF : DF.IsCartier)
    (eDF : Nonempty (DF.divisorialSheaf ≅
      (Scheme.Modules.pullback (F j').idealSheaf.subschemeι).obj D'.divisorialSheaf))
    {b₁ : ℤ} (hb₁ : a + c * (q - a) ≤ b₁)
    {KF : Divisor (F j').idealSheaf.subscheme}
    (hKF : KF.IsCanonicalDivisor ((F j').idealSheaf.subschemeι ≫ f ≫ sX) (n - 1)) :
    IsSmoothNonvanishingDatum ((F j').idealSheaf.subschemeι ≫ f ≫ sX) (n - 1) KF DF
      ((tieBreakerBoundary F r b p j' c).restrictPrimeDivisor (F j')) b₁ := by
  classical
  have hPY : AlgebraicGeometry.IsProjectiveVariety k (f ≫ sX) := h.isProjectiveVariety_source
  have : AlgebraicGeometry.IsProperVariety k sX := h.isProperVariety
  have : IsIntegral Y := AlgebraicGeometry.IsVariety.toIsIntegral (k := k) (f := f ≫ sX)
  have hsm : IsSmoothScheme (f ≫ sX) := h.isLogResolution.isSmoothScheme
  have hKX : K.IsCanonicalDivisor sX n := h.isKltPair.1.2.1
  have hdim : topologicalKrullDim Y = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (f ≫ sX)
      h.isLogResolution.isBirationalMorphism).symm.trans hKX.1
  obtain ⟨KY, hKY⟩ := exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sX) hsm hdim
  set ι := (F j').idealSheaf.subschemeι
  set A := tieBreakerBoundary F r b p j' c with hA
  -- `F` is a smooth projective variety
  have hFmem : F j' ∈ (∑ j, Finsupp.single (F j) (1 : ℤ)).support := by
    rw [Finsupp.mem_support_iff, Finsupp.finsetSum_apply]
    simp [Finsupp.single_apply, h.injective.eq_iff]
  have hsmF : IsSmoothScheme (ι ≫ f ≫ sX) := h.isSNC.1 (F j') hFmem
  have hPF : AlgebraicGeometry.IsProjectiveVariety k (ι ≫ f ≫ sX) := by
    have : AlgebraicGeometry.IsVariety k (ι ≫ f ≫ sX) := ⟨⟩
    exact (AlgebraicGeometry.isProjectiveVariety_iff_isProjectiveMorphism k _).mpr
      ((MMP.isProjectiveMorphism_of_isClosedImmersion ι).comp hPY.isProjective)
  have hb₁pos : (0 : ℚ) < b₁ := by
    have := h.pos
    have := h.le_q
    have := h.pos_c
    nlinarith
  have hAF : A.coeff (F j') = 0 := by
    rw [hA, tieBreakerBoundary, DivisorWithCoeffs.coeff, Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun j hj => ?_
    exact Finsupp.single_eq_of_ne fun hFj => Finset.ne_of_mem_erase hj (h.injective hFj).symm
  have : AlgebraicGeometry.IsVariety k (f ≫ sX) := hPY.toIsVariety
  have : Smooth (f ≫ sX) := (isSmoothScheme_iff _).mp hsm
  -- the support of `A|_F` is snc and its coefficients are `0` or `-c r_j + b_j - p_j`, `j ≠ j'`
  have hsplit1 : Finsupp.single (F j') (1 : ℤ) + ∑ j ∈ Finset.univ.erase j',
      Finsupp.single (F j) (1 : ℤ) = ∑ j, Finsupp.single (F j) (1 : ℤ) :=
    Finset.add_sum_erase _ _ (Finset.mem_univ j')
  obtain ⟨hsncA, hcoeffA⟩ := isSNC_and_coeff_restrictPrimeDivisor (f ≫ sX) F h.injective
    (Finset.univ.erase j') (Finset.notMem_erase j' _) (by rw [hsplit1]; exact h.isSNC)
    (fun j => -c * r j + b j - p j)
  -- the test divisor `N(b₁, c) = b₁ f^*D + A - F - K_Y` is ample
  have hamp : (Divisor.toQDivisor (b₁ • D') + A - Divisor.toQDivisor (Finsupp.single (F j') 1) -
      Divisor.toQDivisor KY).IsAmple := by
    set N : QDivisor Y := (b₁ : ℚ) • Divisor.toQDivisor D' - Divisor.toQDivisor KY +
      ∑ j, Finsupp.single (F j) (-c * r j + b j - p j) with hNdef
    have hNt : IsTieBreakerTestDivisor sX n D f KY F r b p b₁ c N := ⟨hKY, hB, D', hD', rfl⟩
    have hampN : N.IsAmple :=
      h.toIsNonvanishingAdaptedResolution.isAmple_of_isTieBreakerTestDivisor h.pos_c.le
        h.lt_half.le hb₁ hNt
    have hsplit : ∑ j, Finsupp.single (F j) (-c * r j + b j - p j) =
        Finsupp.single (F j') (-1) + A := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j'), h.eq_neg_one]
      rfl
    convert hampN using 1
    rw [hNdef, hsplit, map_zsmul, ← Int.cast_smul_eq_zsmul ℚ]
    ext E
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_sub,
      DivisorWithCoeffs.coeff_smul]
    simp only [DivisorWithCoeffs.coeff, Finsupp.single_apply]
    split_ifs <;> push_cast <;> ring
  -- by adjunction, `b₁ D_F + A|_F - K_F` is ample
  have hn : n - 1 + 1 = n := Nat.sub_add_cancel h.one_le_dim
  have hampF : ((b₁ : ℚ) • Divisor.toQDivisor DF + A.restrictPrimeDivisor (F j') -
      Divisor.toQDivisor KF).IsAmple := by
    have hKY' : KY.IsCanonicalDivisor (f ≫ sX) (n - 1 + 1) := by rw [hn]; exact hKY
    have hb₁nat : ((b₁.toNat : ℕ) : ℤ) = b₁ := Int.toNat_of_nonneg (by exact_mod_cast hb₁pos.le)
    have hb₁nat' : 0 < b₁.toNat := by
      have : (0 : ℤ) < b₁ := by exact_mod_cast hb₁pos
      omega
    have ePF := nonempty_divisorialSheaf_nsmul_iso hsm hsmF eDF hb₁nat'
    rw [hb₁nat] at ePF
    have := QDivisor.isAmple_add_restrictPrimeDivisor_sub_of_isAmple (f ≫ sX) hsm (F j') hsmF
      hKY' hKF (MMP.Fourfold.isCartier_of_isSmoothScheme hsm _) hAF hamp
      (MMP.Fourfold.isCartier_of_isSmoothScheme hsmF _) ePF
    rwa [map_zsmul, ← Int.cast_smul_eq_zsmul ℚ] at this
  obtain ⟨hnefF, hbigF⟩ := QDivisor.isNef_and_isBig_of_isAmple (ι ≫ f ≫ sX) hampF
  refine
    { isProperVariety := inferInstance
      isCartier := hDF
      isNef := ?_
      isKltPair := ?_
      pos := hb₁pos
      isQCartier_add := hnefF.1
      isNef_add := hnefF
      isBig_add := hbigF
      isSmoothScheme := hsmF
      isProjectiveVariety := hPF
      isSNCSubset := ?_
      isAmple := hampF }
  · -- `D_F` is nef, since `f^*D` is
    have hQY := MMP.Fourfold.isQCartier_of_isSmoothScheme hsm
    have hQX := MMP.Fourfold.isQCartier_of_isSmoothScheme h.isSmoothScheme
    have hD'Q : (Divisor.toQDivisor D').IsNef k (f ≫ sX) :=
      isNef_of_isPullback (sV := f ≫ sX) rfl hQY hQX
        ((QDivisor.isNef_toQDivisor_iff D h.isCartier).mpr h.isNef)
        (QDivisor.isPullback_toQDivisor h.isCartier
          (fun Z => by rw [Divisor.supp_toQDivisor]; exact hB Z) hD')
    exact isNef_of_nonempty_divisorialSheaf_iso ι
      ((QDivisor.isNef_toQDivisor_iff D' (MMP.Fourfold.isCartier_of_isSmoothScheme hsm _)).mp hD'Q)
      hDF eDF
  · -- `(F, -A|_F)` is klt
    refine MMP.Mori.isKltPair_of_isSNC _ ⟨inferInstance, inferInstance⟩ hsmF hKF
      (hsncA.of_support_subset (Finsupp.support_neg _).le) fun Q => ?_
    rw [DivisorWithCoeffs.coeff_neg]
    rcases hcoeffA Q with h0 | ⟨j, hj, hjQ⟩
    · rw [show (A.restrictPrimeDivisor (F j')).coeff Q = 0 from h0, neg_zero]
      exact zero_lt_one
    · rw [show (A.restrictPrimeDivisor (F j')).coeff Q = -c * r j + b j - p j from hjQ]
      linarith [h.neg_one_lt j (Finset.ne_of_mem_erase hj)]
  · exact Or.inr ⟨_, (DivisorWithCoeffs.coe_supp _).symm, hsncA.of_support_subset <|
      Finsupp.support_finsetSum.trans <| Finset.biUnion_subset.mpr fun E hE =>
        Finsupp.support_single_subset.trans (Finset.singleton_subset_iff.mpr hE)⟩

end MMP.Mori
