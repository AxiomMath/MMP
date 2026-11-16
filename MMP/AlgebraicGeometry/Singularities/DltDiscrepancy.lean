module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Basic
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.MMP.Models
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Resolution.Principalization.ResolutionPrincipalization
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Divisor.EffectiveCartierCoheight
import MMP.AlgebraicGeometry.Divisor.Negativity.CodimTwoCentres

/-!
# Discrepancies of dlt pairs

Let `(X, Δ)` be a dlt pair of dimension `n ≥ 2` over an algebraically closed field of
characteristic zero, and let `Z = X \ U` be a closed subset as in the definition of dlt: `U` lies
in the smooth locus, `Δ|_U` is snc, and `a(E, X, Δ) > -1` for every divisor `E` over `X` with
`center_X E ⊆ Z`. The definition bounds each discrepancy separately; the infimum
`discrep(center ⊆ Z, X, Δ)` is itself `> -1`.

If `Z ≠ X`, take a log resolution `f : Y ⟶ X` of `(X, Δ)` with `f⁻¹(Z)` of pure codimension one
and `Ex(f) ∪ f⁻¹(Supp Δ) ∪ f⁻¹(Z)` snc, obtained by principalizing `I_Z · I_{Supp Δ}`; the
uniform bound `MMP.Mori.exists_pos_forall_le_discrepancy_of_isLogResolution` gives `δ > 0` with
`a(E, X, Δ) ≥ -1 + δ` for every `E` with center in `Z`. If `Z = X`, every divisor over `X` has
discrepancy `> -1`; the same bound applied to the closed subset `Z'` complementary to
`X_sm \ Supp Δ` treats the divisors with center in `Z'`, and a divisor whose center meets
`X_sm \ Supp Δ` has the discrepancy of its restriction there, which is at least that of the
smooth pair `(X_sm \ Supp Δ, 0)`.

As a consequence, if moreover `Δ` is effective and the components of `⌊Δ⌋` are pairwise
disjoint, then `(X, Δ)` is plt. An exceptional divisor with center in `Z` has discrepancy at
least `discrep(center ⊆ Z, X, Δ) > -1`. One whose center meets `U` has the discrepancy of its
restriction to `U`, where `Δ|_U` is snc with coefficients in `[0, 1]` and no two components of
coefficient `1` meet, so the snc discrepancy formula bounds it below by a constant `> -1`.

The same argument is local: if every point of `U` specializing to `x` lies on at most one
component of `⌊Δ⌋`, then `(X, Δ)` is plt on a neighbourhood `V` of `x` on which no two components
of `⌊Δ⌋` meet inside `U`; `V` is the complement of the irreducible pieces of the double locus of
`⌊Δ⌋` not through `x`. An exceptional divisor over `V` is an exceptional divisor over `X` with
the same discrepancy, and its center either lies in `Z` or meets `U ∩ V`, on which `Δ` is snc.
This applies when at most one component of `⌊Δ⌋` passes through `x`, and when `x ∉ U` has
codimension two, since then a point of `U` specializing to `x` has codimension at most one.

## Main results

* `MMP.Mori.IsDltPair.neg_one_lt_discrepCenterIn`: `discrep(center ⊆ Z, X, Δ) > -1`.
* `MMP.Mori.IsDltPair.isPltPair_of_pairwise_disjoint`: a dlt pair whose round down has pairwise
  disjoint components is plt.
* `MMP.Mori.IsDltPair.isAt_isPltPair_of_forall_specializes`: a dlt pair is plt at `x` if every
  point of `U` specializing to `x` lies on at most one component of its round down.
* `MMP.Mori.IsDltPair.isAt_isPltPair_of_subsingleton`: a dlt pair is plt at every point lying on
  at most one component of its round down.
* `MMP.Mori.IsDltPair.isAt_isPltPair_of_notMem_of_coheight_eq_two`: a dlt pair is plt
  at every codimension-two point outside `U`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.40, 5.51,
  5.59
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Mori

open MMP.Resolution

/-- The restriction to an open `U` of an exceptional divisor over `X` whose center meets `U` is
exceptional over `U`. -/
private theorem isExceptional_restrict {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) {U : X.Opens} [Nonempty U] (D : DivisorOver k sX)
    (hD : D.IsExceptional) (hU : IsNormalVariety k (U.ι ≫ sX))
    (hY : IsNormalVariety k ((D.f ∣_ U) ≫ U.ι ≫ sX)) (hf : IsBirationalMorphism (D.f ∣_ U))
    (E' : MMP.Mori.PrimeDivisor (D.f ⁻¹ᵁ U).toScheme)
    (hE' : OpenWeilRestriction.primeDivisorMap (D.f ⁻¹ᵁ U).ι E' = D.E) :
    (⟨_, D.f ∣_ U, hY, hf, E'⟩ : DivisorOver k (U.ι ≫ sX)).IsExceptional := by
  rw [DivisorOver.isExceptional_iff_two_le_coheight hU]
  rw [DivisorOver.isExceptional_iff_two_le_coheight hX] at hD
  change 2 ≤ Order.coheight ((D.f ∣_ U) E'.genericPoint)
  rw [← coheight_eq_of_isOpenImmersion U.ι]
  have : U.ι ((D.f ∣_ U) E'.genericPoint) = D.f D.E.genericPoint := by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, ← hE']
    exact congrArg D.f (OpenWeilRestriction.genericPoint_primeDivisorMap _ E').symm
  rwa [this]

/-- On an open subset missing `Supp Δ`, the restriction of `Δ` is zero. -/
private theorem coeff_restrictOpen_eq_zero {X : Scheme.{u}} {Δ : QDivisor X} {V : X.Opens}
    (hV : V ≤ Δ.supp.compl) (E : MMP.Mori.PrimeDivisor V.toScheme) :
    (Δ.restrictOpen V).coeff E = 0 := by
  rw [DivisorWithCoeffs.coeff_restrictOpen]
  by_contra hne
  have hmem := DivisorWithCoeffs.support_subset_supp hne
    (MMP.Flips.primeDivisor_genericPoint_mem_support (OpenWeilRestriction.primeDivisorMap V.ι E))
  exact hV E.genericPoint.2 (by
    convert hmem using 1; exact (OpenWeilRestriction.genericPoint_primeDivisorMap V.ι E).symm)

private theorem neg_one_lt_coe_coe {b : ℚ} (hb : -1 < b) : (-1 : EReal) < ((b : ℝ) : EReal) := by
  simpa using (EReal.coe_lt_coe_iff.mpr (by exact_mod_cast hb : (-1 : ℝ) < b))

/-- **The bound over a proper closed subset.** Let `(X, Δ)` be a pair with coefficients in
`[0, 1]` over an algebraically closed field of characteristic zero, and `U ⊆ X` a nonempty open
subset of the smooth locus with `Δ|_U` snc and `a(E, X, Δ) > -1` for every divisor `E` over `X`
with center in `X \ U`. Then `discrep(center ⊆ X \ U, X, Δ) > -1`: the uniform bound
`MMP.Mori.exists_pos_forall_le_discrepancy_of_isLogResolution` on a log resolution with
`f⁻¹(X \ U)` of pure codimension one gives `δ > 0` with `a(E, X, Δ) ≥ -1 + δ`. -/
private theorem neg_one_lt_discrepCenterIn_compl {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hΔ : IsPairWith sX n K Δ)
    (hcoeff : ∀ P : MMP.Mori.PrimeDivisor X, 0 ≤ Δ.coeff P ∧ Δ.coeff P ≤ 1)
    {U : X.Opens} (hne : (U : Set X).Nonempty) (hU : U ≤ smoothLocus sX)
    (hsnc : (Δ.restrictOpen U).IsSNC (U.ι ≫ sX))
    (hG : ∀ (D : DivisorOver k sX) (a : ℚ), (D.center : Set X) ⊆ (U : Set X)ᶜ →
      IsDiscrepancy sX n K Δ D a → -1 < a) :
    -1 < discrepCenterIn sX n K Δ (U : Set X)ᶜ := by
  let Z : Closeds X := ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩
  have hZc : (Z.compl : X.Opens) = U := by ext; simp [Z]
  have hZ : Z ≠ ⊤ := fun h => by
    obtain ⟨x, hx⟩ := hne
    exact (show x ∈ (Z : Set X) by rw [h]; trivial) hx
  obtain ⟨Y, f, hf, hZY, hS⟩ := exists_isLogResolution_isPureCodimOne_preimage sX
    hΔ.1 (QDivisor.toRDivisor Δ) Z hZ
  rw [QDivisor.supp_toRDivisor] at hS
  obtain ⟨δ, hδ, hδE⟩ := exists_pos_forall_le_discrepancy_of_isLogResolution hΔ hcoeff hZ
    (hZc ▸ hU) (hZc ▸ hsnc) hf hZY hS fun _ G hGZ a ha => hG _ a (by
      rw [DivisorOver.center_eq_closure_genericPoint]
      exact closure_minimal (Set.singleton_subset_iff.mpr
        (hGZ (MMP.Flips.primeDivisor_genericPoint_mem_support G))) Z.isClosed) ha
  refine lt_of_lt_of_le (b := (((-1 + δ : ℚ) : ℝ) : EReal)) ?_
    (le_discrepCenterIn_iff.mpr fun D a _ hD ha =>
      EReal.coe_le_coe_iff.mpr (by exact_mod_cast hδE D a hD ha))
  exact neg_one_lt_coe_coe (by linarith)

/-- **The case `Z = X`.** If every divisor over `X` has discrepancy `> -1` for a pair `(X, Δ)`
with coefficients in `[0, 1]`, then `discrep(X, Δ) > -1`. Divisors with center in the complement
of `V = X_sm \ Supp Δ` are bounded by `neg_one_lt_discrepCenterIn_compl`; a divisor whose center
meets `V` has the discrepancy of its restriction to `V`, which is at least that of the smooth pair
`(V, 0)`. -/
private theorem neg_one_lt_discrep_of_forall {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hΔ : IsPairWith sX n K Δ)
    (hcoeff : ∀ P : MMP.Mori.PrimeDivisor X, 0 ≤ Δ.coeff P ∧ Δ.coeff P ≤ 1)
    (hall : ∀ (D : DivisorOver k sX) (a : ℚ), IsDiscrepancy sX n K Δ D a → -1 < a) :
    -1 < discrep sX n K Δ := by
  have : MMP.Mori.IsVariety k sX := hΔ.1.1
  have : LocallyOfFiniteType sX := this.toLocallyOfFiniteType
  let V : X.Opens := smoothLocus sX ⊓ Δ.supp.compl
  have hgenV : genericPoint X ∈ V :=
    ⟨Threefold.Mori.OpenRestriction.genericPoint_mem_smoothLocus',
      MMP.Fourfold.genericPoint_notMem_supp Δ⟩
  haveI : Nonempty V := ⟨⟨_, hgenV⟩⟩
  have hsmV : IsSmoothScheme (V.ι ≫ sX) := isSmoothScheme_ι_of_le_smoothLocus inf_le_left
  have hzero := coeff_restrictOpen_eq_zero (Δ := Δ) (V := V) inf_le_right
  have hsncV : (Δ.restrictOpen V).IsSNC (V.ι ≫ sX) :=
    (DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme (R := ℚ) _ hsmV).of_support_subset
      fun E hE => absurd (hzero E) (Finsupp.mem_support_iff.mp hE)
  have hc : -1 < discrep (V.ι ≫ sX) n (K.restrictOpen V) (Δ.restrictOpen V) := by
    by_cases hex : ∃ (D' : DivisorOver k (V.ι ≫ sX)) (b : ℚ),
        IsDiscrepancy (V.ι ≫ sX) n (K.restrictOpen V) (Δ.restrictOpen V) D' b
    · obtain ⟨D', b, hb⟩ := hex
      exact (isKltPair_of_isSNC _ hb.1 hsmV hb.2.1 hsncV fun E => by
        rw [hzero E]; norm_num).2.1
    · rw [discrep_eq_top fun D' b _ hb => hex ⟨D', b, hb⟩]
      exact EReal.coe_lt_top (-1)
  refine (lt_min (neg_one_lt_discrepCenterIn_compl hΔ hcoeff ⟨_, hgenV⟩ inf_le_left hsncV
    fun D a _ ha => hall D a ha) hc).trans_le (le_discrep_iff.mpr fun D a hD ha => ?_)
  by_cases hDV : ((D.center : Set X) ∩ V).Nonempty
  · obtain ⟨hY, hf, E', hE', -, hiff⟩ := DivisorOver.exists_restrict_isDiscrepancy_iff hΔ D V hDV
    have ha' := (hiff a).mp ha
    exact (min_le_right _ _).trans
      (discrep_le (isExceptional_restrict hΔ.1 D hD ha'.1 hY hf E' hE') ha')
  · exact (min_le_left _ _).trans (le_discrepCenterIn_iff.mp le_rfl D a hD
      (fun x hx hxV => hDV ⟨x, hx, hxV⟩) ha)

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X} {Δ : QDivisor X}

/-- **The discrepancy of a dlt pair over its non-snc locus is `> -1`.** Let `(X, Δ)` be a dlt pair
with canonical divisor `K` over an algebraically closed field of characteristic zero, and let
`U ⊆ X` be an open subset in the smooth locus with `Δ|_U` snc and `a(E, X, Δ) > -1` for every
divisor `E` over `X` with `center_X E ⊆ X \ U`. Then `discrep(center ⊆ X \ U, X, Δ) > -1`. -/
@[mmp "lem_km5b_dlt_discrep_center_in_gt_minus_one"]
public theorem IsDltPair.neg_one_lt_discrepCenterIn [IsAlgClosed k] [CharZero k]
    (h : IsDltPair sX n K Δ) {U : X.Opens} (hU : U ≤ smoothLocus sX)
    (hsnc : (Δ.restrictOpen U).IsSNC (U.ι ≫ sX))
    (hZ : ∀ (D : DivisorOver k sX) (a : ℚ), (D.center : Set X) ⊆ (U : Set X)ᶜ →
      IsDiscrepancy sX n K Δ D a → -1 < a) :
    -1 < discrepCenterIn sX n K Δ (U : Set X)ᶜ := by
  obtain ⟨hpair, hcoeff, -⟩ := h
  rcases (U : Set X).eq_empty_or_nonempty with hU0 | hne
  · rw [hU0, Set.compl_empty, discrepCenterIn_univ]
    exact neg_one_lt_discrep_of_forall hpair hcoeff fun D a => hZ D a (by simp [hU0])
  · exact neg_one_lt_discrepCenterIn_compl hpair hcoeff hne hU hsnc hZ

/-- The support of a prime divisor of an open `U ⊆ X` lies in the support of the prime divisor
of `X` it extends to. -/
private theorem image_support_subset {X : Scheme.{u}} (U : X.Opens)
    (E : MMP.Mori.PrimeDivisor U.toScheme) :
    U.ι '' E.support ⊆ (OpenWeilRestriction.primeDivisorMap U.ι E).support := by
  rintro _ ⟨x, hx, rfl⟩
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hx ⊢
  rw [OpenWeilRestriction.genericPoint_primeDivisorMap]
  exact map_mem_closure U.ι.continuous hx fun y hy => by rw [Set.mem_singleton_iff.mp hy]; rfl

/-- The lower bound of the snc discrepancy formula when coefficients lie in `[0, 1]` and no two
meeting components both have coefficient `1`. -/
private theorem exists_neg_one_lt_le_inf {ι : Type*} (S : Finset ι) (c : ι → ℚ)
    (hc0 : ∀ i ∈ S, 0 ≤ c i) (hc1 : ∀ i ∈ S, c i ≤ 1) (Q : ι → ι → Prop)
    (hQ : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Q i j → c i < 1 ∨ c j < 1) :
    ∃ b : ℚ, -1 < b ∧ ((b : ℝ) : EReal) ≤ (⨅ (i ∈ S) (j ∈ S) (_ : i ≠ j) (_ : Q i j),
        (((1 - c i - c j : ℚ) : ℝ) : EReal)) ⊓ (⨅ i ∈ S, (((1 - c i : ℚ) : ℝ) : EReal)) ⊓ 1 := by
  classical
  obtain ⟨δ, hδ, hδ1, hδc⟩ : ∃ δ : ℚ, 0 < δ ∧ δ ≤ 1 ∧ ∀ i ∈ S, c i < 1 → δ ≤ 1 - c i := by
    set T := S.filter fun i => c i < 1
    rcases T.eq_empty_or_nonempty with hT | hT
    · refine ⟨1, one_pos, le_rfl, fun i hi hci => ?_⟩
      have : i ∈ T := Finset.mem_filter.mpr ⟨hi, hci⟩
      simp [hT] at this
    · obtain ⟨i₀, hi₀, hmin⟩ := T.exists_min_image (fun i => 1 - c i) hT
      refine ⟨min (1 - c i₀) 1, lt_min (sub_pos.mpr (Finset.mem_filter.mp hi₀).2) one_pos,
        min_le_right _ _,
        fun i hi hci => (min_le_left _ _).trans (hmin i (Finset.mem_filter.mpr ⟨hi, hci⟩))⟩
  have hL : ∀ q : ℚ, δ - 1 ≤ q → (((δ - 1 : ℚ) : ℝ) : EReal) ≤ ((q : ℝ) : EReal) := fun q hq =>
    EReal.coe_le_coe_iff.mpr (by exact_mod_cast hq)
  refine ⟨δ - 1, by linarith, le_inf (le_inf ?_ ?_) ?_⟩
  · refine le_iInf₂ fun i hi => le_iInf₂ fun j hj => le_iInf₂ fun hij hq => hL _ ?_
    rcases hQ i hi j hj hij hq with h | h
    · linarith [hδc i hi h, hc1 j hj]
    · linarith [hδc j hj h, hc1 i hi]
  · exact le_iInf₂ fun i hi => hL _ (by linarith [hc1 i hi])
  · simpa using hL 1 (by linarith)

/-- **Discrepancies over the snc locus.** Let `(X, Δ)` be a pair with coefficients in `[0, 1]`
and `U` a nonempty open subset of the smooth locus with `Δ|_U` snc, such that at most one
component of `⌊Δ⌋` passes through each point of `U`. Then there is `b > -1` bounding below the
discrepancy of every exceptional divisor whose center meets `U`. -/
private theorem exists_neg_one_lt_le_of_center_meets {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hpair : IsPairWith sX n K Δ) (hn : 2 ≤ n)
    (hcoeff : ∀ P : MMP.Mori.PrimeDivisor X, 0 ≤ Δ.coeff P ∧ Δ.coeff P ≤ 1)
    {U : X.Opens} (hsub : ∀ x ∈ U,
      {P : MMP.Mori.PrimeDivisor X | Δ.roundDown.coeff P ≠ 0 ∧ x ∈ P.support}.Subsingleton)
    [Nonempty U] (hUsm : U ≤ smoothLocus sX)
    (hsnc : (Δ.restrictOpen U).IsSNC (U.ι ≫ sX)) :
    ∃ b : ℚ, -1 < b ∧ ∀ (D : DivisorOver k sX) (a : ℚ), D.IsExceptional →
      ((D.center : Set X) ∩ U).Nonempty → IsDiscrepancy sX n K Δ D a → b ≤ a := by
  classical
  have hU := hpair.restrictOpen U
  set ΔU := Δ.restrictOpen U
  have hc : ∀ E, ΔU.coeff E = Δ.coeff (OpenWeilRestriction.primeDivisorMap U.ι E) := fun E => rfl
  have hfloor : ∀ P : MMP.Mori.PrimeDivisor X, Δ.coeff P = 1 → Δ.roundDown.coeff P ≠ 0 :=
    fun P hP => by simp [DivisorWithCoeffs.coeff_roundDown, hP]
  obtain ⟨b, hb, hble⟩ := exists_neg_one_lt_le_inf ΔU.support (ΔU.coeff)
    (fun E _ => by rw [hc]; exact (hcoeff _).1) (fun E _ => by rw [hc]; exact (hcoeff _).2)
    (fun E F => (E.support ∩ F.support).Nonempty) (by
      intro E _ F _ hEF ⟨x, hxE, hxF⟩
      by_contra! hcon
      exact hEF (OpenWeilRestriction.primeDivisorMap_injective U.ι (hsub _ x.2
        ⟨hfloor _ (le_antisymm (hcoeff _).2 (hc E ▸ hcon.1)),
          image_support_subset U E ⟨x, hxE, rfl⟩⟩
        ⟨hfloor _ (le_antisymm (hcoeff _).2 (hc F ▸ hcon.2)),
          image_support_subset U F ⟨x, hxF, rfl⟩⟩)))
  have hdisc : discrep (U.ι ≫ sX) n (K.restrictOpen U) ΔU = _ :=
    discrep_eq_of_isSNC (U.ι ≫ sX) hU.1 (isSmoothScheme_ι_of_le_smoothLocus hUsm) hn hU.2.1
      ΔU.support le_rfl
      (hsnc.of_support_subset <| Finsupp.support_finsetSum.trans <| Finset.biUnion_subset.mpr
        fun E hE => Finsupp.support_single_subset.trans (Finset.singleton_subset_iff.mpr hE))
      (fun E _ => by rw [hc]; exact (hcoeff _).2)
  refine ⟨b, hb, fun D a hD hDU ha => ?_⟩
  obtain ⟨hY, hf, E', hE', -, hiff⟩ := DivisorOver.exists_restrict_isDiscrepancy_iff hpair D U hDU
  have ha' := (hiff a).mp ha
  exact_mod_cast EReal.coe_le_coe_iff.mp ((hble.trans_eq hdisc.symm).trans
    (discrep_le (isExceptional_restrict hpair.1 D hD ha'.1 hY hf E' hE') ha'))

/-- **A dlt pair whose round down has pairwise disjoint components is plt.** Let `(X, Δ)` be a
dlt pair with canonical divisor `K` of dimension `n ≥ 2` over an algebraically closed field of
characteristic zero, with `Δ` effective. If the prime divisors occurring in `⌊Δ⌋` have pairwise
disjoint supports, then `(X, Δ)` is plt. -/
@[mmp "prop_km5b_dlt_disjoint_floor_implies_plt"]
public theorem IsDltPair.isPltPair_of_pairwise_disjoint [IsAlgClosed k] [CharZero k]
    (h : IsDltPair sX n K Δ) (hn : 2 ≤ n) (hΔ : 0 ≤ Δ)
    (hdisj : {P : PrimeDivisor X | Δ.roundDown.coeff P ≠ 0}.Pairwise
      fun P Q => Disjoint P.support Q.support) :
    IsPltPair sX n K Δ := by
  obtain ⟨hpair, hcoeff, U, hUsm, hsnc, hZ⟩ := id h
  have hZc := h.neg_one_lt_discrepCenterIn hUsm hsnc hZ
  refine ⟨hpair, ?_⟩
  rcases isEmpty_or_nonempty U with hUe | hUne
  · have hU0 : (U : Set X) = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun x hx => hUe.false ⟨x, hx⟩
    rwa [hU0, Set.compl_empty, discrepCenterIn_univ] at hZc
  · obtain ⟨b, hb, hbD⟩ := exists_neg_one_lt_le_of_center_meets hpair hn hcoeff
      (fun _ _ P hP Q hQ => by_contra fun hPQ =>
        Set.disjoint_left.mp (hdisj hP.1 hQ.1 hPQ) hP.2 hQ.2) hUsm hsnc
    refine lt_of_lt_of_le (lt_min hZc (neg_one_lt_coe_coe hb))
      (le_discrep_iff.mpr fun D a hD ha => ?_)
    by_cases hDU : ((D.center : Set X) ∩ U).Nonempty
    · exact (min_le_right _ _).trans
        (EReal.coe_le_coe_iff.mpr (by exact_mod_cast hbD D a hD hDU ha))
    · exact (min_le_left _ _).trans (le_discrepCenterIn_iff.mp le_rfl D a hD
        (fun x hx hxU => hDU ⟨x, hx, hxU⟩) ha)

open Classical in
/-- In a quasi-sober space, let `B` be the union of the irreducible closed sets in `T`. A point
`y` of an open `U` avoiding the pieces of `T` not through `x` is not in `B`, provided no point of
`U` specializing to `x` is in `B`. -/
private theorem notMem_of_forall_specializes {Y : Type*} [TopologicalSpace Y] [QuasiSober Y]
    {B : Closeds Y} {T : Finset (Closeds Y)} (hTirr : ∀ Z : T, IsIrreducible (Z : Set Y))
    (hBT : B = T.sup id) {U : Set Y} (hU : IsOpen U) {x : Y}
    (hx : ∀ y ∈ U, y ⤳ x → y ∉ (B : Set Y)) {y : Y} (hyU : y ∈ U)
    (hyV : y ∉ ⋃ Z ∈ T.filter (x ∉ ·), (Z : Set Y)) : y ∉ (B : Set Y) := by
  intro hyB
  have hyT : y ∈ ((T.sup id : Closeds Y) : Set Y) := hBT ▸ hyB
  rw [Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion, Set.mem_iUnion₂] at hyT
  obtain ⟨Z, hZT, hyZ⟩ := hyT
  have hxZ : x ∈ (Z : Set Y) := by_contra fun hxZ => hyV (Set.mem_iUnion₂.mpr
    ⟨Z, Finset.mem_filter.mpr ⟨hZT, hxZ⟩, hyZ⟩)
  have hgen := (hTirr ⟨Z, hZT⟩).isGenericPoint_genericPoint_closure
  rw [Z.isClosed.closure_eq] at hgen
  refine hx _ ((hgen.mem_open_set_iff hU).mpr ⟨y, hyZ, hyU⟩) (hgen.specializes hxZ) ?_
  exact hBT ▸ (show _ ∈ ((T.sup id : Closeds Y) : Set Y) by
    rw [Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion]
    exact Set.mem_iUnion₂.mpr ⟨Z, hZT, hgen.mem⟩)

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] in
/-- If every point of an open `U` specializing to `x` lies on at most one component of `⌊Δ⌋`,
then there is an open neighbourhood `V` of `x` such that every point of `U ∩ V` lies on at most
one component of `⌊Δ⌋`. -/
theorem exists_mem_forall_subsingleton_roundDown [NoetherianSpace X] {U : X.Opens} {x : X}
    (hx : ∀ y ∈ U, y ⤳ x →
      {P : PrimeDivisor X | Δ.roundDown.coeff P ≠ 0 ∧ y ∈ P.support}.Subsingleton) :
    ∃ V : X.Opens, x ∈ V ∧ ∀ y ∈ U ⊓ V,
      {P : PrimeDivisor X | Δ.roundDown.coeff P ≠ 0 ∧ y ∈ P.support}.Subsingleton := by
  classical
  set S := Δ.roundDown.support
  let B : Closeds X := ⟨⋃ P ∈ S, ⋃ Q ∈ S.filter (· ≠ P), P.support ∩ Q.support,
    (Finset.finite_toSet _).isClosed_biUnion fun P _ => (Finset.finite_toSet _).isClosed_biUnion
      fun Q _ => P.idealSheaf.support.isClosed.inter Q.idealSheaf.support.isClosed⟩
  have hB : ∀ y, y ∈ (B : Set X) ↔
      {P : PrimeDivisor X | Δ.roundDown.coeff P ≠ 0 ∧ y ∈ P.support}.Nontrivial := by
    intro y
    simp only [B, Closeds.coe_mk, Set.mem_iUnion, Set.mem_inter_iff, Finset.mem_filter,
      Finsupp.mem_support_iff, S, Set.Nontrivial, Set.mem_setOf_eq, exists_prop]
    exact ⟨fun ⟨P, hP, Q, ⟨hQ, hQP⟩, hyP, hyQ⟩ => ⟨P, ⟨hP, hyP⟩, Q, ⟨hQ, hyQ⟩, hQP.symm⟩,
      fun ⟨P, ⟨hP, hyP⟩, Q, ⟨hQ, hyQ⟩, hPQ⟩ => ⟨P, hP, Q, ⟨hQ, hPQ.symm⟩, hyP, hyQ⟩⟩
  obtain ⟨T, hTirr, hBT⟩ := NoetherianSpace.exists_finset_irreducible B
  let F : Set X := ⋃ Z ∈ T.filter (x ∉ ·), (Z : Set X)
  have hF : IsClosed F := (Finset.finite_toSet _).isClosed_biUnion fun Z _ => Z.isClosed
  let V : X.Opens := ⟨Fᶜ, hF.isOpen_compl⟩
  have hxV : x ∈ V := by
    simp only [V, F, Opens.mem_mk, Set.mem_compl_iff, Set.mem_iUnion, Finset.mem_filter]
    exact fun ⟨_, ⟨_, hZx⟩, hxZ⟩ => hZx hxZ
  refine ⟨V, hxV, fun y ⟨hyU, hyV⟩ => ?_⟩
  rw [← Set.not_nontrivial_iff, ← hB]
  exact notMem_of_forall_specializes hTirr hBT U.isOpen
    (fun z hz hzx hzB => ((hB z).mp hzB).not_subsingleton (hx z hz hzx)) hyU hyV

/-- **A dlt pair is plt at a point near which its round down has no double points in `U`.** Let
`(X, Δ)` be a dlt pair with canonical divisor `K` of dimension `n ≥ 2` over an algebraically
closed field of characteristic zero, with dlt witness `U`, and `x ∈ X` a point such that every
point of `U` specializing to `x` lies on at most one component of `⌊Δ⌋`. Then `(X, Δ)` is plt at
`x`. -/
public theorem IsDltPair.isAt_isPltPair_of_forall_specializes [IsAlgClosed k] [CharZero k]
    (h : IsDltPair sX n K Δ) (hn : 2 ≤ n) {U : X.Opens} (hUsm : U ≤ smoothLocus sX)
    (hsnc : (Δ.restrictOpen U).IsSNC (U.ι ≫ sX))
    (hZ : ∀ (D : DivisorOver k sX) (a : ℚ), (D.center : Set X) ⊆ (U : Set X)ᶜ →
      IsDiscrepancy sX n K Δ D a → -1 < a) {x : X}
    (hx : ∀ y ∈ U, y ⤳ x →
      {P : PrimeDivisor X | Δ.roundDown.coeff P ≠ 0 ∧ y ∈ P.support}.Subsingleton) :
    IsAt sX (fun sU n K Δ => IsPltPair sU n K Δ) n K Δ x := by
  classical
  obtain ⟨hpair, hcoeff, -⟩ := id h
  have hZc := h.neg_one_lt_discrepCenterIn hUsm hsnc hZ
  have : MMP.Mori.IsVariety k sX := hpair.1.1
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := {}
  obtain ⟨V, hxV, hVsub⟩ := exists_mem_forall_subsingleton_roundDown hx
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  obtain ⟨b, hb, hbD⟩ : ∃ b : ℚ, -1 < b ∧ ∀ (D : DivisorOver k sX) (a : ℚ), D.IsExceptional →
      ((D.center : Set X) ∩ (U ⊓ V : X.Opens)).Nonempty → IsDiscrepancy sX n K Δ D a →
        b ≤ a := by
    rcases isEmpty_or_nonempty (U ⊓ V : X.Opens) with hW | hW
    · exact ⟨0, by norm_num, fun _ _ _ ⟨y, _, hy⟩ _ => (hW.false ⟨y, hy⟩).elim⟩
    · exact exists_neg_one_lt_le_of_center_meets hpair hn hcoeff hVsub (inf_le_left.trans hUsm)
        (Threefold.Mori.OpenRestriction.isSNC_restrictOpen_of_cover sX (fun _ : Unit => U) (U ⊓ V)
          (fun _ hy => ⟨(), hy.1⟩) Δ fun _ => hsnc)
  refine ⟨V, Set.singleton_subset_iff.mpr hxV, inferInstance, hpair.restrictOpen V,
    lt_of_lt_of_le (lt_min hZc (neg_one_lt_coe_coe hb)) (le_discrep_iff.mpr fun D a hD ha => ?_)⟩
  obtain ⟨D₁, hD₁, hη, -, ha₁⟩ := hpair.exists_isDiscrepancy_of_restrictOpen V hD ha
  have hcen : (D₁.center : Set X) = closure {V.ι (D.f D.E.genericPoint)} := by
    rw [D₁.center_eq_closure_genericPoint, hη]
  by_cases hpU : V.ι (D.f D.E.genericPoint) ∈ U
  · exact (min_le_right _ _).trans (EReal.coe_le_coe_iff.mpr (by
      exact_mod_cast hbD D₁ a hD₁
        ⟨_, hcen ▸ subset_closure rfl, hpU, (D.f D.E.genericPoint).2⟩ ha₁))
  · exact (min_le_left _ _).trans (le_discrepCenterIn_iff.mp le_rfl D₁ a hD₁ (hcen ▸
      closure_minimal (Set.singleton_subset_iff.mpr hpU) U.isOpen.isClosed_compl) ha₁)

/-- **A dlt pair is plt at a point on at most one component of its round down.** Let `(X, Δ)` be
a dlt pair with canonical divisor `K` of dimension `n ≥ 2` over an algebraically closed field of
characteristic zero, and `x ∈ X` a point through which at most one component of `⌊Δ⌋` passes.
Then `(X, Δ)` is plt at `x`. -/
public theorem IsDltPair.isAt_isPltPair_of_subsingleton [IsAlgClosed k] [CharZero k]
    (h : IsDltPair sX n K Δ) (hn : 2 ≤ n) {x : X}
    (hx : {P : PrimeDivisor X | Δ.roundDown.coeff P ≠ 0 ∧ x ∈ P.support}.Subsingleton) :
    IsAt sX (fun sU n K Δ => IsPltPair sU n K Δ) n K Δ x := by
  obtain ⟨-, -, U, hUsm, hsnc, hZ⟩ := id h
  exact h.isAt_isPltPair_of_forall_specializes hn hUsm hsnc hZ fun y _ hyx =>
    hx.anti fun P hP => ⟨hP.1, hyx.mem_closed P.idealSheaf.support.isClosed hP.2⟩

/-- A point of a prime divisor `P` other than its generic point has codimension at least two. -/
private theorem two_le_coheight_of_mem_support {X : Scheme.{u}} (P : PrimeDivisor X) {y : X}
    (hy : y ∈ P.support) (hne : y ≠ P.genericPoint) : 2 ≤ Order.coheight y := by
  have hηy : P.genericPoint ⤳ y := by
    rwa [specializes_iff_mem_closure, ← P.support_eq_closure]
  have hlt : y < P.genericPoint :=
    lt_of_le_not_ge hηy fun hyη => hne (Specializes.antisymm hyη hηy).eq
  have := Order.coheight_add_one_le hlt
  rwa [P.coheight_genericPoint] at this

/-- **A dlt pair is plt at a codimension-two point outside the snc locus.** Let `(X, Δ)` be a dlt
pair with canonical divisor `K` of dimension `n ≥ 2` over an algebraically closed field of
characteristic zero, with dlt witness `U`, and `x ∉ U` a point of codimension two. Then `(X, Δ)`
is plt at `x`. -/
public theorem IsDltPair.isAt_isPltPair_of_notMem_of_coheight_eq_two [IsAlgClosed k]
    [CharZero k] (h : IsDltPair sX n K Δ) (hn : 2 ≤ n) {U : X.Opens}
    (hUsm : U ≤ smoothLocus sX) (hsnc : (Δ.restrictOpen U).IsSNC (U.ι ≫ sX))
    (hZ : ∀ (D : DivisorOver k sX) (a : ℚ), (D.center : Set X) ⊆ (U : Set X)ᶜ →
      IsDiscrepancy sX n K Δ D a → -1 < a) {x : X} (hxU : x ∉ U)
    (hx : Order.coheight x = 2) :
    IsAt sX (fun sU n K Δ => IsPltPair sU n K Δ) n K Δ x := by
  refine h.isAt_isPltPair_of_forall_specializes hn hUsm hsnc hZ fun y hyU hyx P hP Q hQ => ?_
  have hxy : x < y := lt_of_le_not_ge hyx fun hxy => hxU (hxy.mem_open U.isOpen hyU)
  have hy : Order.coheight y + 1 ≤ 2 := hx ▸ Order.coheight_add_one_le hxy
  have hgen : ∀ R : PrimeDivisor X, y ∈ R.support → y = R.genericPoint := fun R hR =>
    by_contra fun hne => absurd
      ((add_le_add_left (two_le_coheight_of_mem_support R hR hne) 1).trans hy)
      (by decide : ¬ (2 + 1 : ℕ∞) ≤ 2)
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective ((hgen P hP.2).symm.trans
    (hgen Q hQ.2))

end MMP.Mori

end
