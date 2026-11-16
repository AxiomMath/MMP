module

public import MMP.AlgebraicGeometry.MMP.BasepointFree.Nonvanishing
public import MMP.AlgebraicGeometry.MMP.BasepointFree.TestDivisorAmple
public import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy

@[expose] public section

section

/-!
# A basepoint-free datum has sections in every high multiple

Let `(X, Δ, D, a)` be a basepoint-free datum over an algebraically closed field of
characteristic zero. Then `H⁰(X, 𝒪_X(mD)) ≠ 0` for every sufficiently large integer `m`.
Indeed `H⁰(X, 𝒪_X) ∋ 1`, so `X` has a `0`-adapted resolution `f : Y ⟶ X` with exceptional
coefficients `a_j` and perturbations `p_j`; the non-vanishing theorem applied to `f^*D` and
`G = ∑_j (a_j - p_j) F_j` on `Y` gives `H⁰(Y, m f^*D + ⌈G⌉) ≠ 0` for `m ≫ 0`, and `⌈G⌉` is
effective and `f`-exceptional, so these sections descend to `H⁰(X, mD)`.

## Main results

* `MMP.Mori.IsBasepointFreeDatum.exists_section_ne_zero_nsmul`: there is `m₀` such that
  `H⁰(X, mD)` has a nonzero section for every `m ≥ m₀`.

## Implementation notes

`H⁰(X, mD) ≠ 0` is spelled, as in `MMP.Mori.IsBasepointFreeAdaptedResolution`, as the existence
of a nonzero element of `(m • D).divisorialSubmodule ⊤`. The multiple `m` ranges over `ℕ`: the
integers `m ≥ m₀` for an integer `m₀` are, after replacing `m₀` by `max m₀ 0`, natural numbers.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Theorem 3.3, 3.2 Step 1
-/

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.FourfoldProofs.Km3aBpfSomeSectionsProof

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- A dominant morphism of integral schemes maps the generic point outside every divisor. -/
private theorem map_componentGenericPoint_notMem_supp {X : Scheme.{0}} [IsIntegral X]
    {Y : Scheme.{0}} [IsIntegral Y] (f : Y ⟶ X) [IsDominant f] {R : Type*} [Zero R]
    (D : DivisorWithCoeffs R X) (Z : irreducibleComponents Y) :
    f (componentGenericPoint Y Z) ∉ D.supp := by
  rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant]
  exact MMP.Fourfold.genericPoint_notMem_supp _

/-- The coefficient of `F i` in `∑ j, c j • F j`, for an injective family `F`, is `c i`. -/
private theorem coeff_sum_single_self {Y : Scheme.{0}} {ι : Type*} [Fintype ι] {R : Type*}
    [AddCommMonoid R] {F : ι → MMP.Mori.PrimeDivisor Y} (hF : Function.Injective F) (c : ι → R)
    (i : ι) : DivisorWithCoeffs.coeff (∑ j, Finsupp.single (F j) (c j)) (F i) = c i := by
  classical
  change (∑ j, Finsupp.single (F j) (c j)) (F i) = _
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single i]
  · exact Finsupp.single_eq_same
  · exact fun j _ hj => Finsupp.single_eq_of_ne (hF.ne hj).symm
  · simp

/-- The coefficient of a prime divisor off the family `F` in `∑ j, c j • F j` is `0`. -/
private theorem coeff_sum_single_of_forall_ne {Y : Scheme.{0}} {ι : Type*} [Fintype ι]
    {R : Type*} [AddCommMonoid R] {F : ι → MMP.Mori.PrimeDivisor Y} (c : ι → R)
    {E : MMP.Mori.PrimeDivisor Y} (hE : ∀ j, F j ≠ E) :
    DivisorWithCoeffs.coeff (∑ j, Finsupp.single (F j) (c j)) E = 0 := by
  change (∑ j, Finsupp.single (F j) (c j)) E = 0
  rw [Finsupp.finset_sum_apply]
  exact Finset.sum_eq_zero fun j _ => Finsupp.single_eq_of_ne (hE j).symm

/-- A prime divisor with nonzero coefficient in `∑ j, c j • F j` is one of the `F i`. -/
private theorem exists_eq_of_coeff_sum_single_ne_zero {Y : Scheme.{0}} {ι : Type*} [Fintype ι]
    {R : Type*} [AddCommMonoid R] {F : ι → MMP.Mori.PrimeDivisor Y} {c : ι → R}
    {E : MMP.Mori.PrimeDivisor Y}
    (hE : DivisorWithCoeffs.coeff (∑ j, Finsupp.single (F j) (c j)) E ≠ 0) :
    ∃ i, F i = E := by
  by_contra! h
  exact hE (coeff_sum_single_of_forall_ne c h)

/-- Every coefficient of `∑ j, c j • F j`, for an injective family `F`, is `0` or some `c i`; so
a property of `0` and of every `c i` holds for all coefficients. -/
private theorem coeff_sum_single_induction {Y : Scheme.{0}} {ι : Type*} [Fintype ι] {R : Type*}
    [AddCommMonoid R] {F : ι → MMP.Mori.PrimeDivisor Y} (hF : Function.Injective F) (c : ι → R)
    {P : R → Prop} (h0 : P 0) (hc : ∀ i, P (c i)) (E : MMP.Mori.PrimeDivisor Y) :
    P (DivisorWithCoeffs.coeff (∑ j, Finsupp.single (F j) (c j)) E) := by
  by_cases hE : ∃ i, F i = E
  · obtain ⟨i, rfl⟩ := hE
    rw [coeff_sum_single_self hF]
    exact hc i
  · rw [coeff_sum_single_of_forall_ne c fun j hj => hE ⟨j, hj⟩]
    exact h0

/-- On an integral scheme the section `1` of `H⁰(X, 𝒪_X)` is nonzero. -/
private theorem exists_ne_zero_divisorialSubmodule_zero {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] :
    ∃ σ : (0 : Divisor X).divisorialSubmodule ⊤, σ ≠ 0 := by
  refine ⟨⟨1, Divisor.IsDivisorialSection.one le_rfl ⊤⟩, fun h1 => ?_⟩
  obtain ⟨x⟩ : Nonempty X := inferInstance
  let Z : irreducibleComponents X :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  have : Nontrivial (X.presheaf.stalk (componentGenericPoint X Z)) :=
    (RationalFunctions.isField_stalk X Z).nontrivial
  exact one_ne_zero (congrFun (congrArg Subtype.val h1) ⟨Z, trivial⟩)

section Nef

attribute [local instance] AlgebraicGeometry.IsVariety.toIsIntegral

variable {k : Type} [Field k]

/-- **The image of a curve that is not contracted is a curve.** If `u : V ⟶ W` is a
`k`-morphism and `C ⊆ V` a proper curve whose image is not a point, then the scheme-theoretic
image of `C` is a proper curve over `k`. -/
private theorem isProper_and_isCurve_imageι {V W C : Scheme.{0}} {sV : V ⟶ Spec (.of k)}
    {sW : W ⟶ Spec (.of k)} [IsSeparated sW] [LocallyOfFiniteType sW] {u : V ⟶ W}
    (hu : u ≫ sW = sV) (i : C ⟶ V)
    [AlgebraicGeometry.IsCurve k (i ≫ sV)] [IsProper (i ≫ sV)]
    (hpt : ¬ ∃ w : W, Set.range (i ≫ u) = {w}) :
    IsProper ((i ≫ u).imageι ≫ sW) ∧ AlgebraicGeometry.IsCurve k ((i ≫ u).imageι ≫ sW) := by
  have e : (i ≫ u) ≫ sW = i ≫ sV := by rw [Category.assoc, hu]
  have : IsProper ((i ≫ u) ≫ sW) := e ▸ inferInstance
  have : AlgebraicGeometry.IsCurve k ((i ≫ u) ≫ sW) := e ▸ inferInstance
  have : IsProper (i ≫ u) := IsProper.of_comp (i ≫ u) sW
  exact ⟨isProper_imageι_comp (i ≫ u) sW, isCurve_imageι_comp sW (i ≫ u) hpt⟩

/-- The pull-back along a morphism of normal `k`-varieties of a nef `ℚ`-divisor is nef. -/
private theorem isNef_of_isPullback {V W : Scheme.{0}} {sV : V ⟶ Spec (.of k)}
    {sW : W ⟶ Spec (.of k)} [AlgebraicGeometry.IsVariety k sV]
    [AlgebraicGeometry.IsVariety k sW] [IsLocallyNoetherian V] [IsNormal V]
    [IsLocallyNoetherian W] [IsNormal W] {u : V ⟶ W} (hu : u ≫ sW = sV) {L : QDivisor W}
    (hL : L.IsNef k sW)
    {hLB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp}
    {L' : QDivisor V} (h : L.IsPullback u hLB L') : L'.IsNef k sV := by
  refine ⟨h.isQCartier hL.1, fun C i _ _ _ hC => ?_⟩
  have : AlgebraicGeometry.IsCurve k (i ≫ sV) := { topologicalKrullDim_eq_one := hC }
  by_cases hpt : ∃ w : W, Set.range (i ≫ u) = {w}
  · exact (intersectionNumber_pullback_eq_zero k sV sW u hu i hL.1 h hpt).ge
  · obtain ⟨_, hcurve⟩ := isProper_and_isCurve_imageι hu i hpt
    rw [intersectionNumber_pullback_eq_degreeOver_mul k sV sW u hu i hL.1 h hcurve]
    exact mul_nonneg (by positivity)
      (hL.2 _ (i ≫ u).imageι hcurve.topologicalKrullDim_eq_one)

end Nef

end MMP.FourfoldProofs.Km3aBpfSomeSectionsProof

end

section

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori

open MMP.FourfoldProofs.Km3aBpfSomeSectionsProof in
/-- **Every high multiple of a basepoint-free datum has sections** (Kollár–Mori 3.2, Step 1).
Let `(X, Δ, D, a)` be a basepoint-free datum over an algebraically closed field `k` of
characteristic zero. Then there is `m₀` such that `H⁰(X, 𝒪_X(mD)) ≠ 0` for every `m ≥ m₀`. -/
@[mmp "lem_km3a_bpf_some_sections"]
public theorem IsBasepointFreeDatum.exists_section_ne_zero_nsmul
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {D : Divisor X} {a : ℚ}
    (h : IsBasepointFreeDatum sX n K Δ D a) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∃ σ : (m • D).divisorialSubmodule ⊤, σ ≠ 0 := by
  obtain ⟨Y, _, _, _, f, s, F, aj, pj, rj, hres⟩ := h.exists_isBasepointFreeAdaptedResolution
    (by rw [zero_smul]; exact exists_ne_zero_divisorialSubmodule_zero)
  obtain ⟨hYn, hcb⟩ := hres.isCrepantBoundary
  have hsm : IsSmoothScheme (f ≫ sX) := hres.isLogResolution.isSmoothScheme
  have : AlgebraicGeometry.IsProjectiveVariety k (f ≫ sX) := hres.isProjectiveVariety
  have : AlgebraicGeometry.IsProperVariety k sX := h.isProperVariety
  have : IsIntegral Y := hYn.1.toIsIntegral
  have : IsProper f := hres.isLogResolution.isProper
  have hbir := hres.isLogResolution.isBirationalMorphism
  have : IsDominant f := hbir.isDominant
  have hcart : ∀ L : Divisor Y, L.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm
  obtain ⟨KY, hKY⟩ : ∃ KY : Divisor Y, KY.IsCanonicalDivisor (f ≫ sX) n := by
    refine exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sX) hsm ?_
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (f ≫ sX) hbir]
    exact h.isKltPair.1.2.1.topologicalKrullDim_eq
  have hBD := map_componentGenericPoint_notMem_supp f D
  obtain ⟨D', hD'⟩ := h.isCartier.exists_isPullback hBD
  set G : QDivisor Y := ∑ j, Finsupp.single (F j) (aj j - pj j) with hG
  -- every coefficient of `G` exceeds `-1`, since `p_j < 1 + a_j`
  have hG1 : ∀ E, -1 < G.coeff E := coeff_sum_single_induction hres.injective _ (by norm_num)
    fun i => by linarith [hres.lt_one_add i]
  have hN : (a • Divisor.toQDivisor D' + G - Divisor.toQDivisor KY).IsAmple := by
    convert hres.isAmple_of_isTieBreakerTestDivisor (KY := KY) (b := a) (c := 0) le_rfl
      (by simp) ⟨hKY, hBD, D', hD', rfl⟩ using 1
    simp [hG]
    abel
  have hnb := QDivisor.isNef_and_isBig_of_isAmple (f ≫ sX) hN
  have hD'nef : D'.IsNef k (f ≫ sX) :=
    (QDivisor.isNef_toQDivisor_iff D' (hcart D')).mp <| isNef_of_isPullback rfl
      ((QDivisor.isNef_toQDivisor_iff D h.isCartier).mpr h.isNef)
      (QDivisor.isPullback_toQDivisor h.isCartier (map_componentGenericPoint_notMem_supp f _) hD')
  have hklt : IsKltPair (f ≫ sX) n KY (-G) := by
    refine MMP.Mori.isKltPair_of_isSNC (f ≫ sX) hYn hsm hKY
      (hres.isSNC.of_support_subset fun E hE => ?_) fun E => ?_
    · obtain ⟨i, rfl⟩ := exists_eq_of_coeff_sum_single_ne_zero
        (neg_ne_zero.mp (Finsupp.mem_support_iff.mp hE))
      refine Finsupp.mem_support_iff.mpr ?_
      change DivisorWithCoeffs.coeff (∑ j, Finsupp.single (F j) (1 : ℤ)) (F i) ≠ 0
      rw [coeff_sum_single_self hres.injective]
      exact one_ne_zero
    · rw [DivisorWithCoeffs.coeff_neg]
      linarith [hG1 E]
  have hdat : IsNonvanishingDatum (f ≫ sX) n KY D' G a :=
    ⟨inferInstance, hcart D', hD'nef, hklt, h.pos,
      MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _, hnb.1, hnb.2⟩
  obtain ⟨m₀, hm₀⟩ := hdat.hasNonvanishingProperty
  have hAeff : 0 ≤ G.roundUp := Finsupp.le_def.mpr fun E => by
    change (0 : ℤ) ≤ G.roundUp.coeff E
    rw [DivisorWithCoeffs.coeff_roundUp, Int.le_ceil_iff]
    exact_mod_cast hG1 E
  have hAexc : ∀ E : MMP.Mori.PrimeDivisor Y, G.roundUp.coeff E ≠ 0 →
      RationalMap.IsExceptional (X := Y) f.toRationalMap E := by
    intro E hE
    rw [DivisorWithCoeffs.coeff_roundUp] at hE
    obtain ⟨i, rfl⟩ := exists_eq_of_coeff_sum_single_ne_zero (c := fun j => aj j - pj j)
      fun h0 => hE (by rw [h0, Int.ceil_zero])
    refine (MMP.Positivity.IsKltPair.isEffective_roundUp_neg_of_isCrepantBoundary h.isKltPair
      h.isEffective hYn hbir hcb).2 (F i) ?_
    rw [DivisorWithCoeffs.coeff_roundUp, neg_neg, coeff_sum_single_self hres.injective]
    rw [coeff_sum_single_self hres.injective] at hE
    have : 0 < aj i - pj i := by
      by_contra hle
      exact hE (Int.ceil_eq_iff.mpr ⟨by push_cast; linarith [hres.lt_one_add i],
        by push_cast; linarith⟩)
    exact (Int.ceil_pos.mpr (by linarith [hres.pos_p i])).ne'
  refine ⟨m₀.toNat, fun m hm => ?_⟩
  obtain ⟨σ, hσ⟩ := hm₀ m (by omega)
  have hBm := map_componentGenericPoint_notMem_supp f ((m : ℤ) • D)
  obtain ⟨e, -⟩ := Divisor.exists_addEquiv_divisorialSubmodule_add_of_isExceptional sX f
    inferInstance inferInstance hbir ((m : ℤ) • D) (h.isCartier.zsmul m) hBm ((m : ℤ) • D')
    (hD'.zsmul h.isCartier m hBm) G.roundUp (hcart _) hAeff hAexc ⊤
  rw [natCast_zsmul] at e
  exact ⟨e.symm σ, (map_ne_zero_iff e.symm e.symm.injective).mpr hσ⟩

end MMP.Mori

end
