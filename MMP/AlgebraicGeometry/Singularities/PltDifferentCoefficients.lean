module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
public import MMP.AlgebraicGeometry.MMP.Fourfold.Defs
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlops
public import MMP.AlgebraicGeometry.Morphisms.Etale.HenselizationColimit
import MMP.AlgebraicGeometry.Singularities.CyclicQuotientDifferent
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Singularities.PltCodimTwoCyclicModel
import MMP.AlgebraicGeometry.Resolution.DivisorTupleRestrictionLift
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
public import MMP.AlgebraicGeometry.Dimension.HeightCoheight

/-!
# Hyperstandard coefficients of the different on a normal plt prime

Let `X` be a normal complex variety, `S ⊂ X` a normal prime divisor and `B = ∑ b_i B_i ≥ 0` a
`ℚ`-divisor with no component `S`, such that `K_X + S + B` is `ℚ`-Cartier and `(X, S + B)` is plt.
Fix the canonical divisors through a rational top form: `K_X = div(τ)` with `τ` having a simple
pole along `S`, and `K_S = div(ρ)` with `ρ = Res_S τ`. Then at every codimension-one point `P`
of `S` the residue different `B_S` (the `ℚ`-divisor on `S` with `K_S + B_S = (K_X + S + B)|_S`,
see `MMP.Fourfold.exists_isEffective_isPullback_divisorOfForm_isPoincareResidue`) has coefficient
`1 - 1/m + ∑ r_i b_i / m < 1` with `m ≥ 1` and `r_i ∈ ℕ`, `r_i = 0` if `P ∉ B_i`. The integers
`m`, `r_i` depend only on `(X, S)`, the point and the prime divisors `B_i`, not on the
coefficients `b_i`: the coefficient is an affine function of the `b_i` on the set of
coefficient vectors for which the pair is plt.

## Main results

* `MMP.Fourfold.coeff_residueDifferent_eq_of_isPltPair`: at a codimension-one point of a normal
  plt prime the different has coefficient `1 - 1/m + ∑ r_i b_i / m < 1`.
* `MMP.Mori.IsLcPair.coeff_le_one`: the boundary of an lc pair in dimension at least two has
  coefficients at most one.
* `MMP.Mori.PrimeDivisor.ker_eq_idealSheaf_of_range_eq`: a closed immersion from a reduced scheme
  onto the support of a prime divisor `P` has kernel the ideal sheaf of `P`.
* `MMP.Mori.PrimeDivisor.isNormal_of_isNormal_subscheme`: its source is then normal when the
  reduced subscheme of `P` is.

## Implementation notes

`S` is a closed immersion `j : T ⟶ X` onto the prime divisor `P` of `X`, and the codimension-one
point of `S` is the generic point of a prime divisor `Q` of `T`. The integers `m` and `r` are
quantified before the coefficient vector `b`, which is the independence of the boundary
coefficients; in the source `m` is the index of the cyclic quotient chart of the completed strict
local ring at `Q` and `r_i` the order along `Q` of the restriction of a local equation of
`m B_i`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 16.6
-/

@[expose] public section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open CategoryTheory AlgebraicGeometry IsLocalRing MMP MMP.Mori MMP.Flips MMP.Fourfold

namespace MMP.Mori

/-- **Coefficients of an lc boundary are at most one** (Kollár–Mori 2.31(1)): if `(X, Δ)` is lc
and `dim X ≥ 2`, then every coefficient of `Δ` is `≤ 1`. -/
theorem IsLcPair.coeff_le_one {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {d : ℕ} {K : Divisor X} {Δ : QDivisor X} (h : IsLcPair sX d K Δ) (hd : 2 ≤ d)
    (E : PrimeDivisor X) : Δ.coeff E ≤ 1 := by
  by_contra hlt
  push Not at hlt
  have hX := h.1.1
  have hex := MMP.Positivity.IsPair.exists_isDiscrepancy h.1.isPair h.1.2.1
    (DivisorOver.ofPrimeDivisor k hX E)
  have htot := totalDiscrep_le_neg_coeff hX hex
  have hc : (((-Δ.coeff E : ℚ) : ℝ) : EReal) < ((-1 : ℝ) : EReal) :=
    EReal.coe_lt_coe_iff.mpr (by push_cast; exact_mod_cast (by linarith : -Δ.coeff E < -1))
  have h2 := h.2
  rw [discrep_eq_bot_of_totalDiscrep_lt_neg_one h.1 hd
    (htot.trans_lt (hc.trans_eq (by norm_num)))] at h2
  exact ((EReal.bot_lt_coe (-1)).trans_eq (by simp)).not_ge h2

namespace PrimeDivisor

/-- The kernel of a closed immersion from a reduced scheme onto the support of a prime divisor `P`
is the ideal sheaf of `P`: both are the vanishing ideal of that closed set. -/
theorem ker_eq_idealSheaf_of_range_eq {X T : Scheme.{0}} (j : T ⟶ X) [IsClosedImmersion j]
    [IsReduced T] (P : PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X)) :
    j.ker = P.idealSheaf := by
  have : IsReduced P.idealSheaf.subscheme := by have := P.integral; infer_instance
  rw [← MMP.Positivity.vanishingIdeal_support_of_isReduced P.idealSheaf,
    ← Scheme.IdealSheafData.map_bot, ← Scheme.nilradical_eq_bot,
    ← Scheme.IdealSheafData.vanishingIdeal_top, Scheme.IdealSheafData.map_vanishingIdeal]
  congr 1
  ext1
  simp only [TopologicalSpace.Closeds.coe_closure, TopologicalSpace.Closeds.coe_top,
    Set.image_univ]
  change closure (Set.range j.base) = (P.support : Set X)
  rw [hP, P.support_eq_closure, closure_closure]

/-- A reduced closed subscheme `T` of `X` with support that of a prime divisor `P` is normal as
soon as the reduced subscheme of `P` is: the two are isomorphic over `X`. -/
theorem isNormal_of_isNormal_subscheme {X T : Scheme.{0}} (j : T ⟶ X) [IsClosedImmersion j]
    [IsReduced T] (P : PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (h : IsNormal P.idealSheaf.subscheme) : IsNormal T := by
  have hk : P.idealSheaf.subschemeι.ker = j.ker := by
    rw [P.ker_eq_idealSheaf_of_range_eq j hP, Scheme.IdealSheafData.ker_subschemeι]
  have := IsClosedImmersion.isIso_lift P.idealSheaf.subschemeι j hk
  exact isNormal_of_isOpenImmersion (IsClosedImmersion.lift P.idealSheaf.subschemeι j hk.le)

end PrimeDivisor

end MMP.Mori

namespace MMP.NormalPltDifferentCoefficients

/-- A local ring has a strict henselization in its own universe. -/
private theorem exists_isHenselization_of_isSepClosure (A : Type) [CommRing A] [IsLocalRing A]
    (κsep : Type) [Field κsep] [Algebra (ResidueField A) κsep]
    [IsSepClosure (ResidueField A) κsep] :
    ∃ (H : Type) (_ : CommRing H) (_ : IsLocalRing H) (_ : Algebra A H),
      IsHenselization A κsep H := by
  have hA : (CommAlgCat.etale A).ind (CommAlgCat.of A A) :=
    (CommAlgCat.etale A).le_ind _ inferInstance
  have hres : Function.Surjective (ResidueField.map (algebraMap A A)) := by
    simpa using (Function.surjective_id :
      Function.Surjective (id : ResidueField A → ResidueField A))
  obtain ⟨B, hRing, hLocal, hAlg, -, -, -, hHens, -, hInd, -, hCompat⟩ :=
    exists_strictHenselization A A hA hres κsep
  exact ⟨B, hRing, hLocal, hAlg, IsHenselization.of_ind_etale hHens hInd hCompat⟩

/-- If a closed immersion `j : T ⟶ X` has kernel the ideal of `P` and `T` is a normal variety,
then so is the reduced subscheme of `P`, which is isomorphic to `T` over `X`. -/
private theorem isNormalVariety_subschemeι {X T : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (j : T ⟶ X) [IsClosedImmersion j] [IsNormal T] (P : Mori.PrimeDivisor X)
    (hT : IsNormalVariety ℂ (j ≫ sX)) (h : j.ker = P.idealSheaf) :
    IsNormalVariety ℂ (P.idealSheaf.subschemeι ≫ sX) := by
  have hk : j.ker = P.idealSheaf.subschemeι.ker := by
    rw [h, Scheme.IdealSheafData.ker_subschemeι]
  have := IsClosedImmersion.isIso_lift j P.idealSheaf.subschemeι hk
  have hn : IsNormal P.idealSheaf.subscheme :=
    isNormal_of_isOpenImmersion (IsClosedImmersion.lift j P.idealSheaf.subschemeι hk.le)
  rw [← IsClosedImmersion.lift_fac j P.idealSheaf.subschemeι hk.le, Category.assoc]
  obtain ⟨hv, -⟩ := hT
  have := P.integral
  exact ⟨(Mori.isVariety_iff _ _).mpr ⟨inferInstance, inferInstance, inferInstance,
    inferInstance⟩, hn⟩

/-- **A codimension-one point of a prime divisor has codimension two.** If `j : T ⟶ X` is a
closed immersion onto the support of a prime divisor `P` of an integral scheme of finite type over
`ℂ`, and `Q` is a prime divisor of `T`, then `𝒪_{X, j(η_Q)}` has dimension two. -/
private theorem ringKrullDim_stalk_eq_two {X T : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [IsIntegral X] [LocallyOfFiniteType sX] (j : T ⟶ X) [IsClosedImmersion j]
    (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (Q : Mori.PrimeDivisor T) :
    ringKrullDim (X.presheaf.stalk (j.base Q.genericPoint)) = 2 := by
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  have : LocallyOfFiniteType (X ↘ Spec (.of ℂ)) := ‹LocallyOfFiniteType sX›
  set x := j.base Q.genericPoint
  have hIic : Set.Iic P.genericPoint = Set.range j.base := by
    ext z
    rw [hP, P.support_eq_closure, Set.mem_Iic, Scheme.le_iff_specializes,
      specializes_iff_mem_closure]
  have hle : ∀ a b : T, j.base a ≤ j.base b ↔ a ≤ b := fun a b => by
    rw [Scheme.le_iff_specializes, Scheme.le_iff_specializes]
    exact j.isClosedEmbedding.isInducing.specializes_iff
  let emb : T ↪o X := ⟨⟨j.base, j.isClosedEmbedding.injective⟩, hle _ _⟩
  let e : T ≃o Set.Iic P.genericPoint :=
    emb.orderIso.trans (Set.orderIsoOfEq _ _ hIic.symm)
  have hx : x ≤ P.genericPoint := by
    rw [← Set.mem_Iic, hIic]; exact ⟨_, rfl⟩
  have hex : e Q.genericPoint = ⟨x, hx⟩ := rfl
  have hc : Order.coheight (⟨x, hx⟩ : Set.Iic P.genericPoint) = 1 := by
    rw [← hex, Order.coheight_orderIso, Mori.PrimeDivisor.coheight_genericPoint]
  obtain ⟨h1, h2⟩ := MMP.height_eq_height_add_coheight_Iic ℂ hx
  have k1 := MMP.height_add_coheight_eq_krullDim ℂ x
  have k2 := MMP.height_add_coheight_eq_krullDim ℂ P.genericPoint
  rw [Mori.PrimeDivisor.coheight_genericPoint, h1, hc, ← k1] at k2
  have hfin : Order.height x ≠ ⊤ := by
    intro h; rw [h1, h] at h2; simp at h2
  have k3 := WithBot.coe_inj.mp k2
  rw [add_assoc] at k3
  lift Order.height x to ℕ using hfin with h
  rw [ringKrullDim_stalk_eq_coheight, ← WithTop.add_left_cancel WithTop.coe_ne_top k3]
  rfl

/-- **The cyclic surface model along a normal plt boundary.** At a codimension-one point of a
normal prime `S` with `(X, S + Δ)` plt, the completed strict henselization is a one-axis cyclic
quotient `K[[u, v]]^{μ_m}`, with `I_S` the image of `u = 0`. -/
private theorem exists_ringEquiv_cyclicInvariants_of_isPltPair
    {X T : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X] [IsNormal X]
    [IsLocallyNoetherian X] {n : ℕ}
    (j : T ⟶ X) [IsClosedImmersion j] [IsNormal T]
    (hT : IsNormalVariety ℂ (j ≫ sX))
    (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (Q : Mori.PrimeDivisor T)
    (KX : Divisor X) (Δ : QDivisor X) (hΔ : 0 ≤ Δ) (hΔP : Δ.coeff P = 0)
    (hplt : IsPltPair sX n KX (Finsupp.single P 1 + Δ))
    (κsep : Type) [Field κsep]
    [Algebra (ResidueField (X.presheaf.stalk (j.base Q.genericPoint))) κsep]
    [IsSepClosure (ResidueField (X.presheaf.stalk (j.base Q.genericPoint))) κsep]
    (H : Type) [CommRing H] [IsLocalRing H]
    [Algebra (X.presheaf.stalk (j.base Q.genericPoint)) H]
    [IsHenselization (X.presheaf.stalk (j.base Q.genericPoint)) κsep H] :
    ∃ (K : Type) (_ : Field K) (m : ℕ) (q : ℤ) (_ : IsCyclicQuotientSetting K m q)
      (e : AdicCompletion (maximalIdeal H) H ≃+* cyclicInvariants K m q),
      ((RingHom.ker (j.stalkMap Q.genericPoint).hom).map
          (algebraMap (X.presheaf.stalk (j.base Q.genericPoint))
            (AdicCompletion (maximalIdeal H) H))).map e =
        (Ideal.span {MvPowerSeries.X (0 : Fin 2)}).comap (cyclicInvariants K m q).subtype := by
  have hX := hplt.1.1
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hker := P.ker_eq_idealSheaf_of_range_eq j hP
  have hdim2 := ringKrullDim_stalk_eq_two sX j P hP Q
  -- `j(η_Q)` has codimension two, so `n ≥ 2`
  have hn : 2 ≤ n := by
    have h1 : (Order.coheight (j.base Q.genericPoint) : WithBot ℕ∞) ≤ topologicalKrullDim X :=
      (Order.coheight_le_krullDim (j.base Q.genericPoint)).trans_eq
        (Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints).symm
    rw [hplt.1.2.1.topologicalKrullDim_eq, ← ringKrullDim_stalk_eq_coheight, hdim2] at h1
    exact_mod_cast h1
  have hle : ∀ E : Mori.PrimeDivisor X, Δ.coeff E ≤ 1 := fun E => by
    have h1 := hplt.isLcPair.coeff_le_one hn E
    by_cases hE : E = P
    · subst hE; rw [hΔP]; exact zero_le_one
    · simpa [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, Ne.symm hE] using h1
  have : Nonempty (⊤ : X.Opens) := ⟨⟨j.base Q.genericPoint, trivial⟩⟩
  have hat : IsAt sX (fun sU n K Δ => IsPltPair sU n K Δ) n KX (Finsupp.single P 1 + Δ)
      (j.base Q.genericPoint) :=
    ⟨⊤, fun _ _ => trivial, inferInstance, hplt.restrictOpen ⊤⟩
  obtain ⟨m, hm, q, hq, -, hall⟩ := exists_ringEquiv_cyclicInvariants_of_isAt_isPltPair sX hX
    hplt.1.2.1 P (isNormalVariety_subschemeι sX j P hT hker) Δ hΔ hle hΔP
    (j.base Q.genericPoint) ⟨⊤, trivial, (hplt.1.restrictOpen ⊤).2.2⟩
    (by rw [← hP]; exact ⟨_, rfl⟩) hdim2 hat
  obtain ⟨φ, -, hφ⟩ := hall κsep H
  have : CharZero (ResidueField (X.presheaf.stalk (j.base Q.genericPoint))) := by
    letI := stalkAlgebra sX (j.base Q.genericPoint)
    exact charZero_of_injective_algebraMap (algebraMap ℂ _).injective
  have : CharZero κsep :=
    charZero_of_injective_algebraMap
      (algebraMap (ResidueField (X.presheaf.stalk (j.base Q.genericPoint))) κsep).injective
  have : IsSepClosed κsep :=
    IsSepClosure.sep_closed (ResidueField (X.presheaf.stalk (j.base Q.genericPoint)))
  have hK : IsCyclicQuotientSetting κsep m q :=
    ⟨IsSepClosed.isAlgClosed_of_perfectField κsep, inferInstance, hm, hq⟩
  refine ⟨κsep, inferInstance, m, q, hK, φ.symm, ?_⟩
  rw [MMP.Resolution.Internal.TupleRestrictionLift.ker_stalkMap_eq_stalk_ker j, hker,
    IsScalarTower.algebraMap_eq (X.presheaf.stalk (j.base Q.genericPoint)) H
      (AdicCompletion (maximalIdeal H) H), ← Ideal.map_map, ← hφ]
  exact Ideal.map_of_equiv φ

end MMP.NormalPltDifferentCoefficients

namespace MMP.Fourfold

/-- **Hyperstandard coefficients of the different on a normal plt prime.** Let `X` be a normal
complex variety of dimension `n + 1`, `j : T ⟶ X` the inclusion of a normal prime divisor `S`,
`τ` a rational top form with `ord_S τ = -1` and `ρ` its Poincaré residue along `T`, and let `Q`
be a prime divisor of `T`. Let `B_i` (`i : ι`) be prime divisors of `X` other than `S`. Then
there are `m ≥ 1` and `r : ι → ℕ`, with `r i = 0` whenever the generic point of `Q` is not on
`B_i`, such that for every `b : ι → ℚ`, `b ≥ 0`, with `D = div τ + S + ∑ b_i B_i` `ℚ`-Cartier and
`(X, S + ∑ b_i B_i)` plt, every `ℚ`-divisor `B_S` on `T` with `div ρ + B_S = D|_T` has
coefficient `1 - 1/m + ∑ r_i b_i / m` at `Q`, and this coefficient is `< 1`. -/
@[mmp "lem_fourfold_normal_plt_different_coefficients"]
public theorem coeff_residueDifferent_eq_of_isPltPair
    {X T : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X] [IsNormal X]
    [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety ℂ sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
    [CompactSpace T] (hT : IsNormalVariety ℂ (j ≫ sX))
    (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (τ : RationalPluriForms sX (n + 1) 1) (hτ0 : τ ≠ 0) (hτ : P.ordForm τ = -1)
    (ρ : RationalPluriForms (j ≫ sX) n 1) (hρ : IsPoincareResidue sX j n 1 τ ρ)
    (Q : Mori.PrimeDivisor T)
    {ι : Type*} [Fintype ι] (Bi : ι → Mori.PrimeDivisor X) (hBi : ∀ i, Bi i ≠ P) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ r : ι → ℕ,
      (∀ i, j.base Q.genericPoint ∉ ((Bi i).support : Set X) → r i = 0) ∧
      ∀ b : ι → ℚ, (∀ i, 0 ≤ b i) →
        (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 +
          ∑ i, b i • Finsupp.single (Bi i) 1).IsQCartier →
        IsPltPair sX (n + 1) (divisorOfForm τ)
          (Finsupp.single P 1 + ∑ i, b i • Finsupp.single (Bi i) 1) →
        ∀ BS : QDivisor T,
          (∃ hgen : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉
              (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 +
                ∑ i, b i • Finsupp.single (Bi i) 1).supp,
            (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 +
                ∑ i, b i • Finsupp.single (Bi i) 1).IsPullback j hgen
              (Divisor.toQDivisor (divisorOfForm ρ) + BS)) →
          BS.coeff Q = 1 - 1 / m + ∑ i, (r i : ℚ) * b i / m ∧ BS.coeff Q < 1 := by
  by_cases hex : ∃ b₀ : ι → ℚ, (∀ i, 0 ≤ b₀ i) ∧
      IsPltPair sX (n + 1) (divisorOfForm τ)
          (Finsupp.single P 1 + ∑ i, b₀ i • Finsupp.single (Bi i) 1)
  swap
  · refine ⟨1, le_rfl, 0, fun _ _ => rfl, fun b hb _ hplt => ?_⟩
    exact absurd ⟨b, hb, hplt⟩ hex
  obtain ⟨b₀, hb₀, hplt₀⟩ := hex
  set A := X.presheaf.stalk (j.base Q.genericPoint)
  obtain ⟨H, _, _, _, _⟩ :=
    MMP.NormalPltDifferentCoefficients.exists_isHenselization_of_isSepClosure A
      (SeparableClosure (ResidueField A))
  have hΔ : (0 : QDivisor X) ≤ ∑ i, b₀ i • Finsupp.single (Bi i) 1 :=
    Finset.sum_nonneg fun i _ => smul_nonneg (hb₀ i) (Finsupp.single_nonneg.mpr zero_le_one)
  have hΔP : (∑ i, b₀ i • Finsupp.single (Bi i) 1 : QDivisor X).coeff P = 0 := by
    rw [DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply]
    exact Finset.sum_eq_zero fun i _ => by
      rw [Finsupp.smul_apply, Finsupp.single_eq_of_ne' (hBi i), smul_zero]
  obtain ⟨K, _, m, q, hK, e, he⟩ :=
    MMP.NormalPltDifferentCoefficients.exists_ringEquiv_cyclicInvariants_of_isPltPair sX j hT P
      hP Q (divisorOfForm τ) _ hΔ hΔP hplt₀ (SeparableClosure (ResidueField A)) H
  obtain ⟨r, hr0, hall⟩ := coeff_residueDifferent_eq_of_cyclicInvariants sX hX hdim j hT P hP τ
    hτ0 hτ ρ hρ Q (SeparableClosure (ResidueField A)) H hK e he Bi hBi
  refine ⟨m, hK.one_le, r, hr0, fun b hb hD hplt BS hBS => ?_⟩
  obtain ⟨hcoeff, hlt⟩ := hall b hb hD
  refine ⟨hcoeff BS hBS, ?_⟩
  rw [hcoeff BS hBS, ← Finset.sum_div]
  have := div_lt_div_of_pos_right (hlt hplt) (by exact_mod_cast hK.one_le : (0 : ℚ) < m)
  linarith

end MMP.Fourfold
