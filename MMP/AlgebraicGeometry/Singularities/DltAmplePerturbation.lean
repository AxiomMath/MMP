module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBoundaryChange
import MMP.AlgebraicGeometry.Intersection.QCartierCurveNumber
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Resolution.MaximalOrderAttained
import MMP.AlgebraicGeometry.Divisor.LocalSectionDivisor
import MMP.AlgebraicGeometry.Bertini.FreeLinearSystem
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Resolution.BirationalTransformTriple
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
import MMP.AlgebraicGeometry.Positivity.SemiampleDescent
import MMP.AlgebraicGeometry.MMP.BasepointFree.ProofData
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafCoherent
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Divisor.Negativity.CodimTwoCentres
import MMP.AlgebraicGeometry.Singularities.DltLogResolutionCriterion

/-!
# Perturbing a dlt pair by an ample divisor sharing no component with the boundary

Let `(X, Δ)` be a dlt pair of dimension `n ≥ 2` on a quasi-projective variety over an
algebraically closed field of characteristic zero, `H` an ample Cartier divisor and `Δ₁` an
effective `ℚ`-divisor with `Δ - Δ₁` effective. Then there are a rational `c > 0` and an effective
`ℚ`-divisor `D` with no component in common with `Δ` and `D - Δ₁ ∼_ℚ cH`, such that
`(X, Δ - εΔ₁ + εD)` is dlt for every sufficiently small rational `ε > 0`.

With `mΔ₁` integral, `𝒪_X(mΔ₁ + m'H)` has, for `m' ≫ 0`, finitely many sections generating it
at the points of the smooth open `U` on which `Δ` is snc and at the generic points of the
components of `Δ`. The divisor `D'` of a general member is snc together with `Δ` on `U`
(Bertini) and contains no component of `Δ`; put `D = D'/m`. Then `Θ_ε = Δ + ε(D - Δ₁)` has
coefficients in `[0, 1]` and support `Supp Δ ∪ Supp D` for small `ε > 0`, one log resolution of
`Θ_{1/2}` serves all `ε`, and on it `a(E, X, Θ_ε) = a(E, X, Δ) - ε ord_E f^*(D - Δ₁)` tends to
`a(E, X, Δ) > -1` for the finitely many prime divisors `E` over `X \ U`.

## Main results

* `MMP.Mori.IsDltPair.exists_forall_isDltPair_sub_smul_add_smul_of_disjoint`: the statement
  above.

## Implementation notes

That `D` and `Δ` have no common component is the disjointness of the sets of prime divisors with
nonzero coefficient in `D` and in `Δ`. "For all sufficiently small `ε > 0`" is the existence of a
rational `ε₀ > 0` such that the conclusion holds for every rational `0 < ε < ε₀`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori],
  proof of Proposition 2.43 and Corollary 5.52
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry hiding PrimeDivisor

universe u

namespace MMP.Proof_lem_km5b_dlt_perturbation_no_common_component

open TopologicalSpace MMP.Mori

section Helpers

/-! ### Clearing denominators -/

/-- Some positive multiple of a `ℚ`-divisor is integral. -/
private theorem exists_toQDivisor_eq_smul {X : Scheme.{u}} (Δ₁ : QDivisor X) :
    ∃ m : ℕ, 0 < m ∧ ∃ E₁ : Divisor X, Divisor.toQDivisor E₁ = (m : ℚ) • Δ₁ := by
  classical
  set m : ℕ := ∏ P ∈ Δ₁.support, (Δ₁ P).den
  have hm0 : 0 < m := Finset.prod_pos fun P _ => (Δ₁ P).den_pos
  have hint : ∀ P, ∃ z : ℤ, (z : ℚ) = (m : ℚ) * Δ₁ P := by
    intro P
    by_cases hP : P ∈ Δ₁.support
    · obtain ⟨c, hc⟩ : (Δ₁ P).den ∣ m := Finset.dvd_prod_of_mem _ hP
      refine ⟨c * (Δ₁ P).num, ?_⟩
      rw [hc]
      push_cast
      rw [← Rat.mul_den_eq_num (Δ₁ P)]
      ring
    · rw [Finsupp.notMem_support_iff.mp hP]
      exact ⟨0, by simp⟩
  choose z hz using hint
  refine ⟨m, hm0, Finsupp.onFinset Δ₁.support z fun P hP => ?_, ?_⟩
  · rw [Finsupp.mem_support_iff]
    intro h0
    apply hP
    have := hz P
    rw [h0, mul_zero] at this
    exact_mod_cast this
  · ext P
    change ((Finsupp.onFinset _ z _ P : ℤ) : ℚ) = _
    rw [Finsupp.onFinset_apply, hz]
    rfl

/-- A rational multiple of a `ℚ`-Cartier `ℚ`-divisor is `ℚ`-Cartier. -/
private theorem isQCartier_smul {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : QDivisor X} (hD : D.IsQCartier) (t : ℚ) : (t • D).IsQCartier := by
  obtain ⟨m, hm, D', hD', hc⟩ := hD
  refine ⟨m * t.den, mul_ne_zero hm (by exact_mod_cast t.den_nz), t.num • D', ?_, hc.zsmul _⟩
  ext P
  have h1 := congrArg (fun E : QDivisor X => E.coeff P) hD'
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
    smul_eq_mul] at h1 ⊢
  push_cast
  rw [h1, ← Rat.mul_den_eq_num t]
  ring

/-- Finitely many positive rationals have a common positive lower bound. -/
private theorem exists_pos_forall_le {α : Type*} (s : Finset α) (b : α → ℚ)
    (hb : ∀ a ∈ s, 0 < b a) : ∃ c : ℚ, 0 < c ∧ ∀ a ∈ s, c ≤ b a := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a s ha ih =>
    obtain ⟨c, hc, hcs⟩ := ih fun x hx => hb x (Finset.mem_insert_of_mem hx)
    refine ⟨min c (b a), lt_min hc (hb a (Finset.mem_insert_self a s)), fun x hx => ?_⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hcs x hx)

/-! ### Bertini on a smooth variety, in Weil-divisor form -/

section Bertini

private theorem support_sum_single {Y : Scheme.{u}} (S : Finset (PrimeDivisor Y)) :
    (∑ F ∈ S, Finsupp.single F (1 : ℤ)).support = S := by
  classical
  ext F
  simp [Finsupp.finsetSum_apply, Finsupp.single_apply]

/-- A coefficient vector outside a proper subspace is detected by a nonzero polynomial: if
`v ∉ p` for a subspace `p ⊆ kⁱ`, some linear form `ℓ` vanishes on `p` with `ℓ(v) ≠ 0`, and
`Q = ∑ ℓ(eᵢ) Xᵢ` is nonzero with `Q(c) ≠ 0 → c ∉ p`. -/
private theorem exists_polynomial_forall_notMem {k : Type u} [Field k] {ι : Type*} [Fintype ι]
    {p : Submodule k (ι → k)} {v : ι → k} (hv : v ∉ p) :
    ∃ Q : MvPolynomial ι k, Q ≠ 0 ∧ ∀ c : ι → k, MvPolynomial.eval c Q ≠ 0 → c ∉ p := by
  classical
  obtain ⟨ℓ, hℓ, hp⟩ := Submodule.exists_le_ker_of_notMem hv
  let Q : MvPolynomial ι k :=
    ∑ i, MvPolynomial.C (ℓ (fun j => if i = j then 1 else 0)) * MvPolynomial.X i
  have heval : ∀ c, MvPolynomial.eval c Q = ℓ c := by
    intro c
    rw [LinearMap.pi_apply_eq_sum_univ ℓ c]
    simp [Q, MvPolynomial.eval_sum, mul_comm]
  exact ⟨Q, fun h => hℓ (by rw [← heval, h, map_zero]),
    fun c hc hcp => hc ((heval c).trans (hp hcp))⟩

/-- A general linear combination of finitely many sections, one of them nonzero, is nonzero:
the coefficient vectors `c` with `∑ cᵢ sᵢ = 0` form a proper subspace of `kⁱ`. -/
private theorem exists_polynomial_sum_smul_ne_zero {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {H : Divisor X} {ι : Type*} [Fintype ι] (s : ι → H.divisorialSubmodule ⊤) (j : ι)
    (hj : s j ≠ 0) :
    ∃ Q : MvPolynomial ι k, Q ≠ 0 ∧ ∀ c : ι → k, MvPolynomial.eval c Q ≠ 0 →
      (∑ i, scalarsToGlobalSections k sX (c i) • s i) ≠ 0 := by
  classical
  let p : Submodule k (ι → k) :=
    { carrier := {c | ∑ i, scalarsToGlobalSections k sX (c i) • s i = 0}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, Pi.add_apply, map_add, add_smul,
          Finset.sum_add_distrib] at *
        rw [ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := by
        intro a c hc
        simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul] at *
        rw [← Finset.smul_sum, hc, smul_zero] }
  have hjp : (Pi.single j 1 : ι → k) ∉ p := by
    intro h
    apply hj
    have : ∑ i, scalarsToGlobalSections k sX ((Pi.single j 1 : ι → k) i) • s i = 0 := h
    rwa [Finset.sum_eq_single j (fun i _ hi => by simp [Pi.single_apply, hi]) (by simp),
      Pi.single_eq_same, map_one, one_smul] at this
  obtain ⟨Q, hQ0, hQ⟩ := exists_polynomial_forall_notMem hjp
  exact ⟨Q, hQ0, fun c hc h0 => hQ c hc (show c ∈ p from h0)⟩

/-- The invertibility of `L` in the spelling the zero scheme takes. -/
local instance isInvertible_of_isInvertibleModule {Y : Scheme.{u}} (L : Y.Modules)
    [h : Stacks.Ample.IsInvertibleModule Y L] :
    SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L := h

section ZeroScheme

/-- A frame `b` of `𝒪_Y(D)` over `V`, on which `D` has the local equation `φ`, has order
`-d_E` along every prime divisor `E` with generic point in `V`. -/
private theorem valuation_frame_eq {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y]
    {D : Divisor Y} {V : Y.Opens} {φ : (RationalFunctions Y)ˣ} (hφ : D.IsLocalEquation V φ)
    (b : D.divisorialSubmodule V) (r : Γ(Y, V)) (E : PrimeDivisor Y)
    (hE : E.genericPoint ∈ V) (hZ : componentGenericPoint Y E.component ∈ V)
    (hr : ((φ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) E.component =
      (Y.presheaf.germ V _ hZ).hom r * b.1 ⟨E.component, hZ⟩) :
    E.valuation (b.1 ⟨E.component, hZ⟩) = WithZero.exp (-D.coeff E) := by
  have hEV : (E.support ∩ V).Nonempty :=
    ⟨E.genericPoint, Positivity.PrimeDivisor.genericPoint_mem_support' E, hE⟩
  have hv := congrArg E.valuation hr
  rw [PrimeDivisor.valuation_component, PrimeDivisor.ord_inv, ← hφ E hEV, map_mul] at hv
  have hne : (Y.presheaf.germ V _ hZ).hom r ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at hv
    exact WithZero.coe_ne_zero hv
  have hgerm : (Y.presheaf.germ V _ hZ).hom r =
      E.toComponent.hom ((Y.presheaf.germ V _ hE).hom r) := by
    rw [← TopCat.Presheaf.germ_stalkSpecializes_apply Y.presheaf hE E.specializes_genericPoint]
    rfl
  have hne' : (Y.presheaf.germ V _ hE).hom r ≠ 0 := fun h0 => hne (by rw [hgerm, h0, map_zero])
  have h1 : 1 ≤ E.valuation ((Y.presheaf.germ V _ hZ).hom r) := by
    rw [hgerm]
    exact E.one_le_valuation_toComponent hne'
  have hb0 : b.1 ⟨E.component, hZ⟩ ≠ 0 := by
    intro h0
    rw [h0, map_zero, mul_zero] at hv
    exact WithZero.coe_ne_zero hv
  refine le_antisymm ?_ ?_
  · rw [hv]
    exact le_mul_of_one_le_left' h1
  · exact (b.2 E hEV).resolve_left hb0

/-- **The zero scheme of a section of `𝒪_Y(D)` near a point.** Around every point there is an
affine open `V` on which the ideal of `Z(t)` is generated by a function `a`, and the coefficient
of every prime divisor `E` with generic point in `V` in the divisor of zeros `(t)₀` is the order
of `a` along `E`. -/
private theorem exists_affine_zeroScheme_ideal_eq_span {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (D : Divisor Y) (hD : D.IsCartier)
    [Stacks.Ample.IsInvertibleModule Y D.divisorialSheaf]
    (t : D.divisorialSubmodule ⊤) (ht : t ≠ 0) (x : Y) :
    ∃ (V : Y.affineOpens) (_ : x ∈ (V : Y.Opens)) (a : Γ(Y, V))
      (ha : ∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ (V : Y.Opens)),
        (Y.presheaf.germ V _ hZ).hom a ≠ 0),
      (zeroScheme Y D.divisorialSheaf t).ideal V = Ideal.span {a} ∧
      ∀ E : PrimeDivisor Y, E.genericPoint ∈ (V : Y.Opens) →
        (D.zeroDivisor t ht).coeff E =
          E.ord (MMP.Threefold.Resolution.sectionUnit a ha) := by
  obtain ⟨W, hxW, φ, hφ⟩ := hD x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hxW W.isOpen
  obtain ⟨g, hxg, hgU, ⟨e⟩⟩ := exists_basicOpen_linearEquiv D.divisorialSheaf ⟨U, hU⟩ x hxU
  let V : Y.affineOpens := ⟨Y.basicOpen g, hU.basicOpen g⟩
  have hVW : (V : Y.Opens) ≤ W := hgU.trans hUW
  set tV := D.divisorialSheaf.presheaf.map (homOfLE (le_top : (V : Y.Opens) ≤ ⊤)).op t
  set a : Γ(Y, V) := e tV with ha_def
  set b : D.divisorialSubmodule V := e.symm 1
  have htV : (tV : D.divisorialSubmodule V) = a • b := by
    change tV = a • e.symm 1
    rw [← map_smul e.symm a 1, smul_eq_mul, mul_one, ha_def, e.symm_apply_apply]
  set u := (Divisor.isUnit_sectionToRationalFunctions ht).unit
  have hval : ∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ (V : Y.Opens)),
      (u : RationalFunctions Y) Z = (Y.presheaf.germ V _ hZ).hom a * b.1 ⟨Z, hZ⟩ := by
    intro Z hZ
    have := congrArg (fun m : D.divisorialSubmodule V => m.1 ⟨Z, hZ⟩) htV
    simp only [Submodule.coe_smul, rationalFunctions_smul_apply] at this
    exact this
  have ha : ∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ (V : Y.Opens)),
      (Y.presheaf.germ V _ hZ).hom a ≠ 0 := by
    intro Z hZ h0
    have hu := (Pi.isUnit_iff.mp u.isUnit) Z
    rw [hval Z hZ, h0, zero_mul] at hu
    exact not_isUnit_zero hu
  refine ⟨V, hxg, a, ha, zeroScheme_ideal_of_trivialization Y D.divisorialSheaf t V e a rfl,
    fun E hE => ?_⟩
  set hZ := E.specializes_genericPoint.mem_open (V : Y.Opens).isOpen hE
  have hr : (hφ.mono hVW).invSection = e (hφ.mono hVW).invSection • e.symm 1 := by
    rw [← map_smul e.symm _ 1, smul_eq_mul, mul_one, e.symm_apply_apply]
  have hr' := congrArg (fun m : D.divisorialSubmodule V => m.1 ⟨E.component, hZ⟩) hr
  simp only [Divisor.IsLocalEquation.invSection_apply, Submodule.coe_smul,
    rationalFunctions_smul_apply] at hr'
  have hb := valuation_frame_eq (hφ.mono hVW) b _ E hE hZ hr'
  have hv := congrArg E.valuation (hval E.component hZ)
  rw [PrimeDivisor.valuation_component, map_mul, hb,
    ← MMP.Threefold.Resolution.sectionUnit_apply a ha E.component hZ,
    PrimeDivisor.valuation_component, ← WithZero.exp_add] at hv
  have hv' := WithZero.exp_injective hv
  rw [Divisor.zeroDivisor_eq, DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
  change E.ord u + _ = _
  omega

/-- Off the zero scheme of `t`, a prime divisor has coefficient `0` in `(t)₀`. -/
private theorem coeff_zeroDivisor_eq_zero_of_notMem {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (D : Divisor Y) (hD : D.IsCartier)
    [Stacks.Ample.IsInvertibleModule Y D.divisorialSheaf]
    (t : D.divisorialSubmodule ⊤) (ht : t ≠ 0) (E : PrimeDivisor Y)
    (hE : E.genericPoint ∉ (zeroScheme Y D.divisorialSheaf t).supportSet) :
    (D.zeroDivisor t ht).coeff E = 0 := by
  obtain ⟨V, hxV, a, ha, hI, hc⟩ :=
    exists_affine_zeroScheme_ideal_eq_span D hD t ht E.genericPoint
  rw [hc E hxV]
  rw [Scheme.IdealSheafData.mem_supportSet_iff_of_mem hxV, hI, Scheme.zeroLocus_span,
    Scheme.zeroLocus_singleton, Set.mem_compl_iff, not_not] at hE
  exact MMP.Threefold.Resolution.ord_sectionUnit_eq_zero a ha E hxV
    ((Y.mem_basicOpen a _ hxV).mp hE)

/-- A point off the support of `(t)₀` lies in the nonvanishing open of `t`. -/
private theorem mem_nonvanishingOpen_of_notMem_supp {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (D : Divisor Y) (hD : D.IsCartier)
    [Stacks.Ample.IsInvertibleModule Y D.divisorialSheaf]
    (t : D.divisorialSubmodule ⊤) (ht : t ≠ 0) (y : Y)
    (hy : y ∉ (D.zeroDivisor t ht).supp) :
    y ∈ Stacks.NonvanishingOpen.nonvanishingOpen Y D.divisorialSheaf t := by
  have hyZ : y ∉ (zeroScheme Y D.divisorialSheaf t).supportSet := by
    obtain ⟨V, hyV, a, ha, hI, hc⟩ := exists_affine_zeroScheme_ideal_eq_span D hD t ht y
    rw [Scheme.IdealSheafData.mem_supportSet_iff_of_mem hyV, hI, Scheme.zeroLocus_span,
      Scheme.zeroLocus_singleton, Set.mem_compl_iff, not_not, SetLike.mem_coe,
      Y.mem_basicOpen a y hyV]
    obtain ⟨c, hc'⟩ := exists_unit_stalk_of_forall_ord_eq_zero (mem_pointComponent y)
      (MMP.Threefold.Resolution.sectionUnit a ha) fun E hE => by
        have hEV : E.genericPoint ∈ (V : Y.Opens) := by
          rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hE
          exact (specializes_iff_mem_closure.mpr hE).mem_open (V : Y.Opens).isOpen hyV
        rw [← hc E hEV]
        by_contra hne
        exact hy (DivisorWithCoeffs.support_subset_supp hne hE)
    have hZ : componentGenericPoint Y (pointComponent y) ∈ (V : Y.Opens) :=
      ((isGenericPoint_componentGenericPoint Y _).specializes
        (mem_pointComponent y)).mem_open (V : Y.Opens).isOpen hyV
    have heq : (Y.presheaf.germ V y hyV).hom a = c := by
      apply stalkToRationalFunctions_injective (mem_pointComponent y)
      rw [hc', MMP.Threefold.Resolution.sectionUnit_apply a ha _ hZ]
      exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
    rw [heq]
    exact c.isUnit
  set s' := (Stacks.NonvanishingSpelling.sectionsEquiv Y D.divisorialSheaf).symm t
  have hev : PresheafOfModules.sections.eval s' (Opposite.op ⊤) = t :=
    (Stacks.NonvanishingSpelling.sectionsEquiv Y D.divisorialSheaf).apply_symm_apply t
  have h := AlgebraicGeometry.nonvanishingLocus_eq_compl_supportSet_zeroScheme
    D.divisorialSheaf s' (fun h0 => ht (hev.symm.trans h0))
  have h2 := Stacks.NonvanishingSpelling.stalkNonvanishingLocus_eq Y D.divisorialSheaf s'
  have h3 : y ∈ Stacks.SheafOfModules.nonvanishingLocus D.divisorialSheaf s' := by
    rw [h]
    exact fun hm => hyZ (hev ▸ hm)
  rw [h2] at h3
  change y ∈ Stacks.Ample.nonvanishingLocus D.divisorialSheaf t
  exact hev ▸ h3

end ZeroScheme

section Projective

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **A dense open of `ℙᴺ_k` contains the general points.** For a dense open `U ⊆ ℙᴺ_k` there is
a nonzero (homogeneous) polynomial `Q` with `[c] ∈ U` whenever `Q(c) ≠ 0`: `U` contains a basic
open `D₊(f)`, and a homogeneous component of `f` not vanishing at a point of `D₊(f)` will do. -/
private theorem exists_polynomial_dualPoint_mem {k : Type u} [Field k] {N : ℕ}
    (U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens)
    (hU : Dense (U : Set
      (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)))) :
    ∃ Q : MvPolynomial (Fin (N + 1)) k, Q ≠ 0 ∧ ∀ (c : Fin (N + 1) → k) (hc : c ≠ 0),
      MvPolynomial.eval c Q ≠ 0 → MMP.Threefold.Bridges.dualPoint c hc ∈ U := by
  classical
  obtain ⟨p, hp⟩ := hU.nonempty
  obtain ⟨_, ⟨f, rfl⟩, hpf, hfU⟩ :=
    (ProjectiveSpectrum.isTopologicalBasis_basic_opens
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)).exists_subset_of_mem_open hp U.isOpen
  have hpf' : f ∉ (show ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)
      from p).asHomogeneousIdeal :=
    (ProjectiveSpectrum.mem_basicOpen _ f _).mp hpf
  obtain ⟨d, hd⟩ : ∃ d, MvPolynomial.homogeneousComponent d f ∉
      (show ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)
        from p).asHomogeneousIdeal := by
    by_contra h
    push Not at h
    apply hpf'
    rw [← MvPolynomial.sum_homogeneousComponent f]
    exact Ideal.sum_mem _ fun i _ => h i
  have hQ0 : MvPolynomial.homogeneousComponent d f ≠ 0 := fun h0 => hd (h0 ▸ zero_mem _)
  refine ⟨_, hQ0, fun c hc hcQ => hfU ?_⟩
  refine (ProjectiveSpectrum.mem_basicOpen _ f
    (show ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) from
      MMP.Threefold.Bridges.dualPoint c hc)).mpr fun hf => hcQ ?_
  change f ∈ ((RingHom.ker (MvPolynomial.eval c)).homogeneousCore
    (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)).toIdeal at hf
  have hcore := (HomogeneousIdeal.isHomogeneous ((RingHom.ker (MvPolynomial.eval c)).homogeneousCore
    (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k))).mem_iff.mp hf d
  have hdec : ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) f d :
      MvPolynomial (Fin (N + 1)) k)) = MvPolynomial.homogeneousComponent d f :=
    MvPolynomial.decomposition.decompose'_apply f d
  rw [hdec] at hcore
  exact RingHom.mem_ker.mp (Ideal.toIdeal_homogeneousCore_le _ _ hcore)

end Projective

section WeilBertini

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (globalSectionsModule)

attribute [local instance] globalSectionsModule

open Classical in
/-- **Bertini's theorem for snc divisors, in Weil-divisor form.** On a smooth variety `Y` over an
algebraically closed field of characteristic zero, let `D` be a Cartier divisor and
`t : ι → H⁰(Y, 𝒪_Y(D))` finitely many sections without common zero, and let `∑_{E ∈ S} E` be
snc. For a general coefficient vector `c`, every component of the divisor of zeros of
`τ = ∑ cᵢ tᵢ` lies in a finite set `T` of prime divisors disjoint from `S` with
`∑_{E ∈ T ∪ S} E` snc. -/
private theorem exists_polynomial_zeroDivisor_isSNC {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {Y : Scheme.{u}} [Y.Over (Spec (.of k))]
    [IsSmoothVariety k (Y ↘ Spec (.of k))] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    (D : Divisor Y) (hD : D.IsCartier) {ι : Type*} [Fintype ι]
    (t : ι → D.divisorialSubmodule ⊤)
    (ht : ∀ y : Y, ∃ (i : ι) (hi : t i ≠ 0), y ∉ (D.zeroDivisor (t i) hi).supp)
    (S : Finset (PrimeDivisor Y))
    (hS : DivisorWithCoeffs.IsSNC (Y ↘ Spec (.of k)) (∑ E ∈ S, Finsupp.single E (1 : ℤ))) :
    ∃ Q : MvPolynomial ι k, Q ≠ 0 ∧ ∀ c : ι → k, MvPolynomial.eval c Q ≠ 0 →
      ∀ hτ : (∑ i, scalarsToGlobalSections k (Y ↘ Spec (.of k)) (c i) • t i) ≠ 0,
        ∃ T : Finset (PrimeDivisor Y),
          (∀ E, (D.zeroDivisor _ hτ).coeff E ≠ 0 → E ∈ T) ∧ Disjoint T S ∧
          DivisorWithCoeffs.IsSNC (Y ↘ Spec (.of k)) (∑ E ∈ T ∪ S, Finsupp.single E (1 : ℤ)) := by
  classical
  haveI hL := hD.isInvertibleModule_divisorialSheaf
  haveI : TopologicalSpace.NoetherianSpace Y :=
    MMP.Resolution.Aux.noetherianSpace_of_finiteType (Y ↘ Spec (.of k))
  obtain ⟨i₀, -, -⟩ := ht (Classical.arbitrary Y)
  set N := Fintype.card ι - 1
  have hcard : Fintype.card ι = N + 1 := by
    have := Fintype.card_pos_iff.mpr ⟨i₀⟩
    omega
  let e : ι ≃ Fin (N + 1) := Fintype.equivFinOfCardEq hcard
  let s : Fin (N + 1) → Γ(D.divisorialSheaf, ⊤) := fun j => t (e.symm j)
  have hsys : ∀ c : ι → k, MMP.Threefold.Bridges.systemSection (k := k) s (c ∘ e.symm) =
      ∑ i, scalarsToGlobalSections k (Y ↘ Spec (.of k)) (c i) • t i := by
    intro c
    rw [MMP.Threefold.Bridges.systemSection_apply]
    exact Fintype.sum_equiv e.symm _ _ (fun j => rfl)
  have hs : ⨆ c : Fin (N + 1) → k, Stacks.NonvanishingOpen.nonvanishingOpen Y D.divisorialSheaf
      (MMP.Threefold.Bridges.systemSection s c) = ⊤ := by
    refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨i, hi, hy⟩ := ht y
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨Pi.single (e i) 1, ?_⟩
    have h1 : MMP.Threefold.Bridges.systemSection (k := k) s (Pi.single (e i) 1) = t i := by
      rw [MMP.Threefold.Bridges.systemSection_apply,
        Finset.sum_eq_single (e i) (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
      simp only [s, Equiv.symm_apply_apply, Pi.single_eq_same]
      exact one_smul k _
    rw [h1]
    exact mem_nonvanishingOpen_of_notMem_supp D hD (t i) hi y hy
  obtain ⟨U, hU, hUc⟩ := MMP.Threefold.Bridges.exists_dense_open_isSNC_zeroScheme_add s hs _ hS
  obtain ⟨Q', hQ'0, hQ'⟩ := exists_polynomial_dualPoint_mem U hU
  refine ⟨MvPolynomial.rename e.symm Q', fun h => hQ'0
    (MvPolynomial.rename_injective _ e.symm.injective (h.trans (map_zero _).symm)),
    fun c hc hτ => ?_⟩
  rw [MvPolynomial.eval_rename] at hc
  have hc0 : c ∘ e.symm ≠ 0 := by
    intro h0
    apply hτ
    rw [← hsys, h0, map_zero]
    rfl
  obtain ⟨-, T, hTcomp, hTS, hsnc⟩ := hUc (c ∘ e.symm) hc0 (hQ' _ hc0 hc)
  rw [support_sum_single] at hTS hsnc
  rw [hsys] at hTcomp
  refine ⟨T, fun E hE => ?_, hTS, hsnc⟩
  by_contra hET
  apply hE
  by_cases hEZ : E.genericPoint ∈ (zeroScheme Y D.divisorialSheaf
      (∑ i, scalarsToGlobalSections k (Y ↘ Spec (.of k)) (c i) • t i)).supportSet
  · exfalso
    obtain ⟨-, hcov⟩ := MMP.Resolution.Aux.finite_and_cover_componentsOf
      (zeroScheme Y D.divisorialSheaf
        (∑ i, scalarsToGlobalSections k (Y ↘ Spec (.of k)) (c i) • t i)).support.isClosed
    obtain ⟨W, hW, hEW⟩ := Set.mem_sUnion.mp (hcov hEZ)
    obtain ⟨E', hE'T, hE'W⟩ := (hTcomp W).mp hW
    exact hET (by
      rwa [← MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E' E (hE'W ▸ hEW)])
  · exact coeff_zeroDivisor_eq_zero_of_notMem D hD _ hτ E hEZ

end WeilBertini

end Bertini

/-! ### Global generation on the smooth open -/

section GlobalGeneration

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

/-- The germ of the local generator `ψ⁻¹` of `𝒪_X(D)` at a point of `W` is torsion-free over
the stalk of `𝒪_X`. -/
private theorem eq_zero_of_smul_germ_invSection_eq_zero {D : Divisor X} {W : X.Opens}
    {ψ : (RationalFunctions X)ˣ} (hψ : D.IsLocalEquation W ψ) {x : X} (hx : x ∈ W)
    {a : TopCat.Presheaf.stalk (C := RingCat.{u}) X.ringCatSheaf.obj x}
    (h0 : a • (TopCat.Presheaf.germ D.divisorialSheaf.val.presheaf W x hx).hom
      hψ.invSection = 0) : a = 0 := by
  have hgen := hψ.isLocalGenerator_invSection
  set b : Γ(D.divisorialSheaf, W) := hψ.invSection
  obtain ⟨V, hVW, hxV, t, ht⟩ := TopCat.Presheaf.exists_le_germ_eq _ a hx
  have e1 := PresheafOfModules.germ_ringCat_smul D.divisorialSheaf.val x V hxV t
    (D.divisorialSheaf.val.presheaf.map (homOfLE hVW).op b)
  have e2 := TopCat.Presheaf.germ_res_apply D.divisorialSheaf.val.presheaf (homOfLE hVW) x
    hxV b
  rw [ht, e2] at e1
  have e3 : a • (TopCat.Presheaf.germ D.divisorialSheaf.val.presheaf W x hx).hom b =
      (TopCat.Presheaf.germ D.divisorialSheaf.val.presheaf V x hxV).hom 0 := by
    rw [h0, map_zero]
  obtain ⟨W', hxW', i1, i2, he⟩ := TopCat.Presheaf.germ_eq _ x hxV hxV _ _ (e1.trans e3)
  have hle : W' ≤ W := i1.le.trans hVW
  rw [map_zero] at he
  have he2 := (PresheafOfModules.map_smul D.divisorialSheaf.val i1.op t _).symm.trans he
  have ht0 : X.presheaf.map i1.op t = 0 := by
    refine (hgen W' hle).1 ?_
    change _ • _ = (0 : Γ(X, W')) • _
    rw [zero_smul]
    have hcomp : D.divisorialSheaf.val.map i1.op
        (D.divisorialSheaf.val.presheaf.map (homOfLE hVW).op b) =
        D.divisorialSheaf.presheaf.map (homOfLE hle).op b := rfl
    rwa [hcomp] at he2
  exact ht.symm.trans ((TopCat.Presheaf.germ_res_apply _ i1 x hxW' t).symm.trans
    ((congrArg (TopCat.Presheaf.germ (C := RingCat.{u}) X.ringCatSheaf.obj W' x hxW').hom
      ht0).trans (map_zero _)))

/-- If a global section `t` of `𝒪_X(D)` equals `g ψ⁻¹` on `W`, where `ψ` is a local equation of
`D` on `W`, then `t` is nonzero and its divisor of zeros misses every point where `g` is a unit. -/
private theorem exists_ne_zero_notMem_supp_zeroDivisor {D : Divisor X} {W : X.Opens}
    {ψ : (RationalFunctions X)ˣ} (hψ : D.IsLocalEquation W ψ) {g : Γ(X, W)} {x : X}
    (hxg : x ∈ X.basicOpen g) {t : D.divisorialSubmodule ⊤}
    (hval : ∀ (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ W),
      t.1 ⟨Z, trivial⟩ = (X.presheaf.germ W _ hZ).hom g *
        ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z) :
    ∃ hi : t ≠ 0, x ∉ (D.zeroDivisor t hi).supp := by
  have hunit : ∀ y (hy : y ∈ X.basicOpen g),
      IsUnit ((X.presheaf.germ W y (X.basicOpen_le _ hy)).hom g) := fun y hy =>
    (X.mem_basicOpen g y (X.basicOpen_le _ hy)).mp hy
  have hZ₀ : componentGenericPoint X (pointComponent x) ∈ X.basicOpen g :=
    ((isGenericPoint_componentGenericPoint X _).specializes
      (mem_pointComponent x)).mem_open (X.basicOpen _).isOpen hxg
  have hi : t ≠ 0 := by
    intro h0
    have h2 := hval (pointComponent x) (X.basicOpen_le _ hZ₀)
    rw [h0] at h2
    have h3 : IsUnit ((X.presheaf.germ W _ (X.basicOpen_le _ hZ₀)).hom g *
        ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) (pointComponent x)) :=
      (hunit _ hZ₀).mul ((Pi.isUnit_iff.mp (ψ⁻¹).isUnit) _)
    rw [← h2] at h3
    exact not_isUnit_zero h3
  refine ⟨hi, fun hxs => ?_⟩
  obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hxs
  apply hE
  have hηE : E.genericPoint ∈ X.basicOpen g := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxE
    exact (specializes_iff_mem_closure.mpr hxE).mem_open (X.basicOpen _).isOpen hxg
  have hηW : E.genericPoint ∈ W := X.basicOpen_le _ hηE
  have hZ : componentGenericPoint X E.component ∈ W :=
    E.specializes_genericPoint.mem_open W.isOpen hηW
  set u := (Divisor.isUnit_sectionToRationalFunctions hi).unit
  have hv := congrArg E.valuation (hval E.component hZ)
  have hgerm : (X.presheaf.germ W _ hZ).hom g =
      E.toComponent.hom ((X.presheaf.germ W _ hηW).hom g) := by
    rw [← TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hηW E.specializes_genericPoint]
    rfl
  rw [map_mul, hgerm, E.valuation_toComponent_of_isUnit (hunit _ hηE), one_mul,
    PrimeDivisor.valuation_component, PrimeDivisor.ord_inv,
    ← hψ E ⟨E.genericPoint, Positivity.PrimeDivisor.genericPoint_mem_support' E, hηW⟩] at hv
  have hv' : E.valuation ((u : RationalFunctions X) E.component) =
      WithZero.exp (-D.coeff E) := hv
  rw [PrimeDivisor.valuation_component] at hv'
  have hv'' := WithZero.exp_injective hv'
  have hc : (D.zeroDivisor _ hi).coeff E = (principalDivisor u).coeff E + D.coeff E := rfl
  refine hc.trans ?_
  rw [coeff_principalDivisor]
  omega

/-- **A generating family has a member whose divisor of zeros misses a point where the divisor
is Cartier.** If the global sections `sᵢ` generate `𝒪_X(D)` and `ψ` is a local equation of `D`
near `x`, write `sᵢ = gᵢ ψ⁻¹` near `x`; since the germs of the `sᵢ` span the stalk, some `gᵢ` is a
unit at `x`, and then `(sᵢ)₀ = div(gᵢ)` misses `x`. -/
private theorem exists_notMem_supp_zeroDivisor {D : Divisor X}
    (σ : D.divisorialSheaf.GeneratingSections) [Finite σ.I] {W : X.Opens}
    {ψ : (RationalFunctions X)ˣ} (hψ : D.IsLocalEquation W ψ) {x : X} (hx : x ∈ W) :
    ∃ i, ∃ hi : ((σ.s i).eval (Opposite.op ⊤) : D.divisorialSubmodule ⊤) ≠ 0,
      x ∉ (D.zeroDivisor _ hi).supp := by
  classical
  have hspan := (AlgebraicGeometry.generates_iff_stalkwise_generates _ _ σ.s).mp σ.epi x
  have hfin : Finite σ.I := inferInstance
  revert hspan hfin
  obtain ⟨I, s, -⟩ := σ
  intro hspan hfin
  haveI := Fintype.ofFinite I
  dsimp only at hspan ⊢
  set b : Γ(D.divisorialSheaf, W) := hψ.invSection
  have hgen := hψ.isLocalGenerator_invSection
  have hs : ∀ i, ∃ g : Γ(X, W), g • D.divisorialSheaf.presheaf.map (homOfLE (le_refl W)).op b =
      D.divisorialSheaf.presheaf.map (homOfLE le_top).op ((s i).eval (Opposite.op ⊤)) :=
    fun i => (hgen W le_rfl).2 _
  choose g hg using hs
  have hbW : D.divisorialSheaf.presheaf.map (homOfLE (le_refl W)).op b = b := by
    have h1 : (homOfLE (le_refl W)).op = 𝟙 (Opposite.op W) := rfl
    rw [h1, CategoryTheory.Functor.map_id]
    rfl
  rw [hbW] at hg
  set G := TopCat.Presheaf.germ D.divisorialSheaf.val.presheaf W x hx
  have hmem : G b ∈
      Submodule.span (TopCat.Presheaf.stalk (C := RingCat.{u}) X.ringCatSheaf.obj x)
        (Set.range fun i => (TopCat.Presheaf.Γgerm D.divisorialSheaf.val.presheaf x).hom
          ((s i).eval (Opposite.op ⊤))) := by
    rw [hspan]
    trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hmem
  have hgerm : ∀ i, (TopCat.Presheaf.Γgerm D.divisorialSheaf.val.presheaf x).hom
      ((s i).eval (Opposite.op ⊤)) = G.hom (g i • b) := by
    intro i
    rw [hg i]
    exact (TopCat.Presheaf.germ_res_apply _ (homOfLE le_top) x hx _).symm
  have hsm : ∀ i, G.hom (g i • b) = (TopCat.Presheaf.germ (C := RingCat.{u}) X.ringCatSheaf.obj
      W x hx).hom (g i) • G.hom b := fun i =>
    PresheafOfModules.germ_ringCat_smul D.divisorialSheaf.val x W hx (g i) b
  simp only [hgerm, hsm, smul_smul, ← Finset.sum_smul] at hc
  set RG := TopCat.Presheaf.germ (C := RingCat.{u}) X.ringCatSheaf.obj W x hx
  set r := ∑ i, c i * RG.hom (g i)
  have hr1 : r = 1 := by
    have h0 : (1 - r) • G.hom b = 0 := by rw [sub_smul, one_smul, hc, sub_self]
    exact (sub_eq_zero.mp (eq_zero_of_smul_germ_invSection_eq_zero hψ hx h0)).symm
  obtain ⟨i, -, hu⟩ : ∃ i ∈ Finset.univ, IsUnit ((X.presheaf.germ W x hx).hom (g i)) := by
    have hge : ∀ i, SemilinearStalk.commStalkRingEquiv X.presheaf x (RG.hom (g i)) =
        (X.presheaf.germ W x hx).hom (g i) := fun i =>
      SemilinearStalk.commStalkRingEquiv_germ X.presheaf x W hx (g i)
    set e := SemilinearStalk.commStalkRingEquiv X.presheaf x
    have h1 : ∑ i, e (c i) * (X.presheaf.germ W x hx).hom (g i) = 1 := by
      have h2 : e r = 1 := (congrArg e hr1).trans (map_one e)
      have h3 : e r = ∑ i, e (c i * RG.hom (g i)) := map_sum e _ _
      have h4 : ∀ i, e (c i * RG.hom (g i)) = e (c i) * (X.presheaf.germ W x hx).hom (g i) :=
        fun i => (map_mul e _ _).trans (congrArg _ (hge i))
      simp only [h4] at h3
      exact h3.symm.trans h2
    obtain ⟨i, hi, hu⟩ := IsLocalRing.exists_of_isUnit_sum (h1 ▸ isUnit_one :
      IsUnit (∑ i ∈ Finset.univ, e (c i) * (X.presheaf.germ W x hx).hom (g i)))
    exact ⟨i, hi, isUnit_of_mul_isUnit_right hu⟩
  have hxg : x ∈ X.basicOpen (g i) := (X.mem_basicOpen (g i) x hx).mpr hu
  have hval : ∀ (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ W),
      ((s i).eval (Opposite.op ⊤) : D.divisorialSubmodule ⊤).1 ⟨Z, trivial⟩ =
        (X.presheaf.germ W _ hZ).hom (g i) *
          ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z := by
    intro Z hZ
    have := congrArg (fun m : D.divisorialSubmodule W => m.1 ⟨Z, hZ⟩) (hg i)
    simp only [Submodule.coe_smul, rationalFunctions_smul_apply] at this
    exact this.symm
  obtain ⟨hi, hxs⟩ := exists_ne_zero_notMem_supp_zeroDivisor hψ hxg hval
  exact ⟨i, hi, hxs⟩

/-- `𝒪_X(nL) ≅ 𝒪_X(L)^{⊗ n}` for a Cartier divisor `L` and `n ≥ 1`. -/
private theorem nonempty_divisorialSheaf_nsmul_iso {L : Divisor X} (hL : L.IsCartier) (n : ℕ)
    (hn : 1 ≤ n) :
    haveI := hL.isInvertibleModule_divisorialSheaf
    Nonempty ((n • L).divisorialSheaf ≅
      Stacks.Ample.tensorPowModule X L.divisorialSheaf (n : ℤ)) := by
  haveI := hL.isInvertibleModule_divisorialSheaf
  induction n, hn using Nat.le_induction with
  | base =>
    exact ⟨eqToIso (congrArg Divisor.divisorialSheaf (one_nsmul L)) ≪≫
      (Stacks.Ample.tensorPowModuleOneIso X _).symm⟩
  | succ n hn ih =>
    obtain ⟨e⟩ := ih
    refine ⟨eqToIso (congrArg Divisor.divisorialSheaf (succ_nsmul L n)) ≪≫
      ((hL.nsmul n).divisorialSheafTensorIso hL).symm ≪≫ ?_ ≪≫
      Stacks.Ample.tensorPowModuleAddIso X _ (n : ℤ) 1 ≪≫
      Stacks.RelativeVeryAmple.tensorPowModuleCongr X _ (by push_cast; rfl)⟩
    exact ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso e).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj _).mapIso
        (Stacks.Ample.tensorPowModuleOneIso X _).symm

/-- **Serre generation for `𝒪_X(E + m'H)`** ([Stacks, Tag 01Q3]). For an ample Cartier divisor
`H` on a variety and any divisor `E`, for some `m' > 0` the sheaf `𝒪_X(E + m'H)` is generated by
finitely many global sections: `𝒪_X(E)` is coherent, so `𝒪_X(E) ⊗ 𝒪_X(H)^{⊗ m'}` is globally
generated for `m' ≫ 0`, and multiplication `𝒪_X(E) ⊗ 𝒪_X(m'H) ⟶ 𝒪_X(E + m'H)` is an
isomorphism. -/
private theorem exists_generatingSections {k : Type u} [Field k] {sX : X ⟶ Spec (.of k)}
    (hX : MMP.Mori.IsVariety k sX) {H : Divisor X} (hH : H.IsCartier) (hHa : H.IsAmple hH)
    (E : Divisor X) :
    ∃ m' : ℕ, 0 < m' ∧ ∃ σ : (E + m' • H).divisorialSheaf.GeneratingSections, Finite σ.I := by
  haveI := hH.isInvertibleModule_divisorialSheaf
  have hcoh := MMP.Threefold.isCoherent_divisorialSheaf_and_isIso_divisorialSheafTensorMul sX hX E
  haveI := (hcoh H).1
  have hqc := Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
    E.divisorialSheaf
  obtain ⟨n₀, hn₀⟩ :=
    (Stacks.AmpleLocalGeneration.quasiSeparatedSpace_and_isEventuallyGloballyGenerated_of_isAmple
      _ hHa).2 E.divisorialSheaf hqc.1 hqc.2
  set n : ℕ := max n₀.toNat 1 with hn
  obtain ⟨σ, hσ⟩ := hn₀ (n : ℤ) (by omega)
  letI := Stacks.SheafInternalHom.schemeMonoidalCategory X
  let i := Stacks.TensorSheafSpellingIso.monoidalTensorIso X E.divisorialSheaf
    (Stacks.Ample.tensorPowModule X H.divisorialSheaf (n : ℤ))
  obtain ⟨e⟩ := nonempty_divisorialSheaf_nsmul_iso hH n (le_max_right _ _)
  let pI := i ≪≫ Stacks.RelativeVeryAmple.tensorModulesMapIso X (Iso.refl _) e.symm ≪≫
    @asIso _ _ _ _ (E.divisorialSheafTensorMul (n • H)) ((hcoh (n • H)).2.2 (hH.nsmul n))
  let p := pI.hom
  haveI : @Epi (SheafOfModules.{u} X.ringCatSheaf) _ _ _ p :=
    @IsIso.epi_of_iso _ _ _ _ p inferInstance
  exact ⟨n, by omega, σ.ofEpi p, hσ⟩

omit [CompactSpace X] in
/-- A divisor whose restriction to an open `V` is Cartier has a local equation near every point
of `V`: a local equation of `D|_V` on `W ⊆ V` is one of `D` on `W`, since the prime divisors of
`X` meeting `W` are the closures of those of `V` meeting `W`, with the same local rings. -/
private theorem exists_isLocalEquation_of_isCartier_restrictOpen {D : Divisor X}
    {V : X.Opens} (h : Divisor.IsCartier (D.restrictOpen V)) {x : X} (hx : x ∈ V) :
    ∃ W : X.Opens, x ∈ W ∧ ∃ φ : (RationalFunctions X)ˣ, D.IsLocalEquation W φ := by
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  have : IsDominant V.ι := Opens.isDominant_ι (V.isOpen.dense ⟨x, hx⟩)
  obtain ⟨W, hxW, φ', hφ'⟩ := h ⟨x, hx⟩
  obtain ⟨g', hg', hφg'⟩ := MMP.Positivity.exists_ord_eq_of_units φ'
  obtain ⟨g, rfl⟩ := (functionFieldMap_bijective_of_isOpenImmersion V.ι ⊤
    ⟨⟨x, hx⟩, trivial⟩).2 g'
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero (g := g)
    (fun h0 => hg' (by rw [h0, map_zero]))
  refine ⟨V.ι ''ᵁ W, ⟨⟨x, hx⟩, hxW, rfl⟩, φ, fun E hE => ?_⟩
  have hEW : E.genericPoint ∈ V.ι ''ᵁ W := (E.genericPoint_mem_iff _).2 hE
  obtain ⟨y, hyW, hy⟩ := hEW
  obtain ⟨E₀, rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff V.ι E).2 ⟨y, hy⟩
  have hgp : V.ι E₀.genericPoint = V.ι y :=
    (OpenWeilRestriction.genericPoint_primeDivisorMap _ _).symm.trans hy.symm
  have hE₀ : (E₀.support ∩ (W : Set V)).Nonempty := by
    rw [← PrimeDivisor.genericPoint_mem_iff]
    have : E₀.genericPoint = y := V.ι.isOpenEmbedding.injective hgp
    change E₀.genericPoint ∈ W
    rw [this]
    exact hyW
  have h1 := hφ' E₀ hE₀
  rw [DivisorWithCoeffs.coeff_restrictOpen] at h1
  rw [h1, hφg', hφ, MMP.Positivity.ord_functionFieldMap_of_isIso V.ι E₀ _
    (OpenWeilRestriction.genericPoint_primeDivisorMap _ _).symm]

omit [CompactSpace X] in
/-- Every divisor has a local equation near a smooth point. -/
private theorem exists_isLocalEquation_of_mem_smoothLocus {k : Type u} [Field k]
    {s : X ⟶ Spec (.of k)} [LocallyOfFiniteType s] (D : Divisor X) {x : X}
    (hx : x ∈ smoothLocus s) :
    ∃ W : X.Opens, x ∈ W ∧ ∃ φ : (RationalFunctions X)ˣ, D.IsLocalEquation W φ :=
  exists_isLocalEquation_of_isCartier_restrictOpen
    (MMP.Fourfold.isCartier_of_isSmoothScheme (isSmoothScheme_ι_of_le_smoothLocus le_rfl) _) hx

end GlobalGeneration

/-- **Serre generation on the smooth locus.** For an ample Cartier divisor `H` and any divisor
`E₁` on a normal variety, some `𝒪_X(E₁ + m'H)`, `m' > 0`, has finitely many
global sections such that every point of the smooth locus lies off the divisor of zeros of one
of them. -/
private theorem exists_sections_forall_notMem_supp_zeroDivisor {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] (hX : IsNormalVariety k sX) {H : Divisor X} (hH : H.IsCartier)
    (hHa : H.IsAmple hH) (E₁ : Divisor X) :
    ∃ m' : ℕ, 0 < m' ∧ ∃ (N : ℕ) (t : Fin (N + 1) → (E₁ + m' • H).divisorialSubmodule ⊤),
      ∀ x ∈ smoothLocus sX, ∃ i, ∃ hi : t i ≠ 0, x ∉ ((E₁ + m' • H).zeroDivisor (t i) hi).supp := by
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  obtain ⟨m', hm', σ, hσ⟩ := exists_generatingSections hX.1 hH hHa E₁
  haveI := Fintype.ofFinite σ.I
  refine ⟨m', hm', ?_⟩
  by_cases hI : Nonempty σ.I
  · obtain ⟨N, hN⟩ : ∃ N, Fintype.card σ.I = N + 1 :=
      Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
    let e : σ.I ≃ Fin (N + 1) := Fintype.equivFinOfCardEq hN
    refine ⟨N, fun j => (σ.s (e.symm j)).eval (Opposite.op ⊤), fun x hx => ?_⟩
    obtain ⟨W, hxW, φ, hφ⟩ := exists_isLocalEquation_of_mem_smoothLocus (E₁ + m' • H) hx
    obtain ⟨i, hi⟩ := exists_notMem_supp_zeroDivisor σ hφ hxW
    obtain ⟨j, rfl⟩ := e.symm.surjective i
    exact ⟨j, hi⟩
  · refine ⟨0, fun _ => 0, fun x hx => ?_⟩
    obtain ⟨W, hxW, φ, hφ⟩ := exists_isLocalEquation_of_mem_smoothLocus (E₁ + m' • H) hx
    obtain ⟨i, -⟩ := exists_notMem_supp_zeroDivisor σ hφ hxW
    exact absurd ⟨i⟩ hI

/-! ### Restricting sections to an open subscheme -/

section RestrictOpen

open Opposite

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- The divisorial valuation of a prime divisor `E'` of an open subscheme `V ⊆ Y` is that of its
closure `E` in `Y`, through the identification `k(Y) ≅ k(V)`. -/
private theorem divisorialValuation_primeDivisorMap {Y V : Scheme.{u}} [IsIntegral Y]
    [IsIntegral V] [IsLocallyNoetherian Y] [IsLocallyNoetherian V] [IsNormal Y] [IsNormal V]
    (j : V ⟶ Y) [IsOpenImmersion j] [IsDominant j] (E' : MMP.Mori.PrimeDivisor V) :
    MMP.Mori.PrimeDivisor.divisorialValuation (OpenWeilRestriction.primeDivisorMap j E') =
      E'.divisorialValuation.comap (functionFieldMap j) := by
  ext g
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  have hg' : functionFieldMap j g ≠ 0 := (map_ne_zero _).2 hg
  rw [Valuation.comap_apply, MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg',
    MMP.Positivity.ord_functionFieldMap_of_isIso j E' _
      (OpenWeilRestriction.genericPoint_primeDivisorMap j E').symm]

section DivisorialRestrict

/-- On an irreducible scheme every irreducible component is the whole space. -/
private theorem eq_univ_of_irreducibleComponents {Y : Scheme.{u}} [IrreducibleSpace Y]
    (Z : irreducibleComponents Y) : Z.1 = Set.univ :=
  Set.eq_univ_of_univ_subset
    (Z.2.2 (IrreducibleSpace.isIrreducible_univ Y) (Set.subset_univ _))

private theorem index_eq {Y : Scheme.{u}} [IrreducibleSpace Y] {W : Y.Opens}
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Z = Z' :=
  Subtype.ext (Subtype.ext ((eq_univ_of_irreducibleComponents _).trans
    (eq_univ_of_irreducibleComponents _).symm))

private theorem specializes_genericPoint {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : componentGenericPoint Y Z ⤳ genericPoint Y :=
  (Inseparable.of_eq (Fourfold.componentGenericPoint_eq_genericPoint Z)).specializes

private theorem stalkSpecializes_self_apply {Y : Scheme.{u}} {x : Y} (h : x ⤳ x)
    (s : Y.presheaf.stalk x) : (Y.presheaf.stalkSpecializes h).hom s = s := by
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- The value in the function field of a section of `𝒦_Y` over an open set, read at the generic
point of an irreducible component meeting it. -/
private noncomputable def evFF {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Y.functionField :=
  (Y.presheaf.stalkSpecializes (genericPoint_specializes (componentGenericPoint Y Z.1))).hom (φ Z)

private theorem evFF_eq {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) :
    evFF φ Z = evFF φ Z' := by
  obtain rfl := index_eq Z Z'
  rfl

private theorem stalkSpecializes_injective {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) :
    Function.Injective
      (Y.presheaf.stalkSpecializes (genericPoint_specializes (componentGenericPoint Y Z))).hom := by
  intro a b h
  have := congrArg (Y.presheaf.stalkSpecializes (specializes_genericPoint Z)).hom h
  rwa [TopCat.Presheaf.stalkSpecializes_comp_apply,
    TopCat.Presheaf.stalkSpecializes_comp_apply, stalkSpecializes_self_apply,
    stalkSpecializes_self_apply] at this

/-- `v_E` on the factor `𝒪_{Y,η}` of `𝒦_Y` is the inverse of the divisorial valuation of the
corresponding rational function. -/
private theorem valuation_eq_inv_divisorialValuation {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.valuation s = (E.divisorialValuation ((Y.presheaf.stalkSpecializes
      (genericPoint_specializes (componentGenericPoint Y E.component))).hom s))⁻¹ := by
  rw [MMP.Threefold.Mori.Helpers.valuation_eq_ordFrac,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_inv_ordHom, inv_inv]
  rfl

private theorem ordGE_iff {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (E : MMP.Mori.PrimeDivisor Y) (n : ℤ)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.OrdGE n s ↔
      ((Y.presheaf.stalkSpecializes
          (genericPoint_specializes (componentGenericPoint Y E.component))).hom s = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation ((Y.presheaf.stalkSpecializes
          (genericPoint_specializes (componentGenericPoint Y E.component))).hom s))⁻¹) := by
  rw [MMP.Mori.PrimeDivisor.OrdGE, valuation_eq_inv_divisorialValuation,
    (injective_iff_map_eq_zero' _).1 (stalkSpecializes_injective E.component)]

private theorem ordGE_iff_evFF {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y) (n : ℤ) {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (h : componentGenericPoint Y E.component ∈ W) :
    E.OrdGE n (φ ⟨E.component, h⟩) ↔
      (evFF φ ⟨E.component, h⟩ = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation (evFF φ ⟨E.component, h⟩))⁻¹) :=
  ordGE_iff E n _

variable (U : X.Opens) [Nonempty U] [IsDominant U.ι]

private theorem genericPoint_mem_of_index {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V}) :
    genericPoint U.toScheme ∈ V := by
  have := Z.2
  rwa [Fourfold.componentGenericPoint_eq_genericPoint] at this

private theorem genericPoint_mem_of_indexX {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    genericPoint U.toScheme ∈ V := by
  have h := Z.2
  rw [Fourfold.componentGenericPoint_eq_genericPoint] at h
  obtain ⟨x, hx, -⟩ := h
  exact ((genericPoint_spec U.toScheme).specializes trivial).mem_open V.isOpen hx

/-- The unique irreducible component `Set.univ` of an irreducible scheme `Y`. -/
private def topComponent (Y : Scheme.{u}) [IrreducibleSpace Y] : irreducibleComponents Y :=
  ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩

private def indexX {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V} :=
  ⟨topComponent X, by
    rw [Fourfold.componentGenericPoint_eq_genericPoint, ← map_genericPoint_of_isDominant U.ι]
    exact ⟨_, h, rfl⟩⟩

private def indexU {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V} :=
  ⟨topComponent U.toScheme, by rwa [Fourfold.componentGenericPoint_eq_genericPoint]⟩

/-- The restriction `𝒦_X(U ∩ -) → 𝒦_U` of rational functions to an open subscheme, through the
identification `k(X) ≅ k(U)`. -/
private noncomputable def restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    ToType ((rationalFunctionsPresheaf U.toScheme).obj (op V)) :=
  fun Z => (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (functionFieldMap U.ι (evFF ψ (indexX U (genericPoint_mem_of_index U Z))))

private theorem evFF_restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V))))
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V})
    (Z' : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    evFF (restrictRF U V ψ) Z = functionFieldMap U.ι (evFF ψ Z') := by
  rw [evFF, restrictRF, TopCat.Presheaf.stalkSpecializes_comp_apply,
    stalkSpecializes_self_apply, evFF_eq ψ _ Z']

private theorem restrictRF_injective (V : U.toScheme.Opens) :
    Function.Injective (restrictRF U V) := by
  intro ψ₁ ψ₂ h
  funext Z'
  have hV := genericPoint_mem_of_indexX U Z'
  have h1 := congrArg (fun φ => evFF φ (indexU U hV)) h
  simp only [evFF_restrictRF U V _ _ Z'] at h1
  exact stalkSpecializes_injective Z'.1 ((functionFieldMap U.ι).injective h1)

/-- Orders along a prime divisor `E'` of `U` and along its closure in `X` agree on restricted
rational functions. -/
private theorem ordGE_restrictRF_iff (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) (n : ℤ)
    (E' : MMP.Mori.PrimeDivisor U.toScheme) (hE' : (E'.support ∩ V).Nonempty)
    (hP : ((OpenWeilRestriction.primeDivisorMap U.ι E').support ∩ U.ι ''ᵁ V).Nonempty) :
    E'.OrdGE n (restrictRF U V ψ ⟨E'.component, E'.componentGenericPoint_mem_of_nonempty hE'⟩) ↔
      MMP.Mori.PrimeDivisor.OrdGE (OpenWeilRestriction.primeDivisorMap U.ι E') n
        (ψ ⟨_, MMP.Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
          (OpenWeilRestriction.primeDivisorMap U.ι E') hP⟩) := by
  rw [ordGE_iff_evFF, ordGE_iff_evFF]
  rw [evFF_restrictRF U V ψ _ ⟨_, MMP.Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
      (OpenWeilRestriction.primeDivisorMap U.ι E') hP⟩,
    divisorialValuation_primeDivisorMap, map_eq_zero_iff _ (functionFieldMap U.ι).injective]
  rfl

/-- A section of `𝒦_X` over `U ∩ -` is a section of `𝒪_X(D)` exactly when its restriction is a
section of `𝒪_U(D|_U)`: the prime divisors of `U` meeting `V` are the restrictions of those of
`X` meeting `V`, with the same valuations and coefficients. -/
private theorem isDivisorialSection_restrictRF_iff (D : Divisor X) (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    Divisor.IsDivisorialSection (D.restrictOpen U) V (restrictRF U V ψ) ↔
      D.IsDivisorialSection (U.ι ''ᵁ V) ψ := by
  have key : ∀ (E' : MMP.Mori.PrimeDivisor U.toScheme) (hE' : (E'.support ∩ V).Nonempty)
      (hP : ((OpenWeilRestriction.primeDivisorMap U.ι E').support ∩ U.ι ''ᵁ V).Nonempty),
      E'.OrdGE (-(D.restrictOpen U).coeff E')
          (restrictRF U V ψ ⟨E'.component, E'.componentGenericPoint_mem_of_nonempty hE'⟩) ↔
        MMP.Mori.PrimeDivisor.OrdGE (OpenWeilRestriction.primeDivisorMap U.ι E')
          (-D.coeff (OpenWeilRestriction.primeDivisorMap U.ι E'))
          (ψ ⟨_, MMP.Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
            (OpenWeilRestriction.primeDivisorMap U.ι E') hP⟩) := by
    intro E' hE' hP
    rw [DivisorWithCoeffs.coeff_restrictOpen]
    exact ordGE_restrictRF_iff U V ψ _ E' hE' hP
  have hmem : ∀ E' : MMP.Mori.PrimeDivisor U.toScheme, (E'.support ∩ V).Nonempty ↔
      ((OpenWeilRestriction.primeDivisorMap U.ι E').support ∩ U.ι ''ᵁ V).Nonempty := by
    intro E'
    rw [← MMP.Mori.PrimeDivisor.genericPoint_mem_iff, ← MMP.Mori.PrimeDivisor.genericPoint_mem_iff,
      show MMP.Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap U.ι E') =
        U.ι E'.genericPoint from OpenWeilRestriction.genericPoint_primeDivisorMap _ _]
    refine ⟨fun h => ⟨_, h, rfl⟩, ?_⟩
    rintro ⟨x, hx, hxe⟩
    rwa [U.ι.isOpenEmbedding.injective hxe] at hx
  constructor
  · intro h P hP
    have hPU : P.genericPoint ∈ Set.range U.ι.base := by
      rw [Scheme.Opens.range_ι]
      obtain ⟨x, -, hx⟩ := (MMP.Mori.PrimeDivisor.genericPoint_mem_iff P _).2 hP
      rw [← hx]
      exact x.2
    obtain ⟨E', rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff _ P).2 hPU
    exact (key E' ((hmem E').2 hP) hP).1 (h E' ((hmem E').2 hP))
  · intro h E' hE'
    exact (key E' hE' ((hmem E').1 hE')).2 (h _ ((hmem E').1 hE'))

private theorem functionFieldMap_germ_appIso_inv (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (h₁ : genericPoint X ∈ U.ι ''ᵁ V) (h₂ : genericPoint U.toScheme ∈ V) :
    functionFieldMap U.ι (X.presheaf.germ (U.ι ''ᵁ V) (genericPoint X) h₁
      ((U.ι.appIso V).inv r)) = U.toScheme.presheaf.germ V (genericPoint U.toScheme) h₂ r := by
  have h₃ : U.ι (genericPoint U.toScheme) ∈ U.ι ''ᵁ V := ⟨_, h₂, rfl⟩
  rw [functionFieldMap, CommRingCat.comp_apply, TopCat.Presheaf.stalkCongr_hom]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf h₁ _]
  erw [Scheme.Hom.germ_stalkMap_apply, ← CommRingCat.comp_apply (U.ι.appIso V).inv,
    Scheme.Hom.appIso_inv_app, TopCat.Presheaf.germ_res_apply]

private theorem restrictRF_smul (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    restrictRF U V ((U.ι.appIso V).inv r • ψ) = r • restrictRF U V ψ := by
  funext Z
  rw [rationalFunctions_smul_apply]
  simp only [restrictRF, evFF, rationalFunctions_smul_apply, map_mul]
  congr 1
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, functionFieldMap_germ_appIso_inv U V r _
    (genericPoint_mem_of_index U Z), TopCat.Presheaf.germ_stalkSpecializes_apply]

private theorem restrictRF_zero (V : U.toScheme.Opens) : restrictRF U V 0 = 0 := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.zero_apply, map_zero, map_zero, map_zero]
  rfl

private theorem restrictRF_add (V : U.toScheme.Opens)
    (ψ₁ ψ₂ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    restrictRF U V (ψ₁ + ψ₂) = restrictRF U V ψ₁ + restrictRF U V ψ₂ := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.add_apply, map_add, map_add, map_add]
  rfl

/-- The restriction to the open subscheme `U` of a global section of `𝒪_X(D)`, a global section
of `𝒪_U(D|_U)`. -/
private noncomputable def restrictSection (D : Divisor X) (t : D.divisorialSubmodule ⊤) :
    Divisor.divisorialSubmodule (D.restrictOpen U) ⊤ :=
  ⟨restrictRF U ⊤ ((rationalFunctionsPresheaf X).map (homOfLE (le_top : U.ι ''ᵁ ⊤ ≤ ⊤)).op t.1),
    (isDivisorialSection_restrictRF_iff U D ⊤ _).2 fun E h =>
      t.2 E (let ⟨y, hy, _⟩ := h; ⟨y, hy, trivial⟩)⟩

private theorem componentGenericPoint_mem_image_top (Z : irreducibleComponents X) :
    componentGenericPoint X Z ∈ U.ι ''ᵁ ⊤ := by
  rw [Fourfold.componentGenericPoint_eq_genericPoint, ← map_genericPoint_of_isDominant U.ι]
  exact ⟨_, trivial, rfl⟩

private theorem restrictSection_injective (D : Divisor X) :
    Function.Injective (restrictSection U D) := fun _ _ h =>
  Subtype.ext <| funext fun Z =>
    congrFun (restrictRF_injective U ⊤ (congrArg Subtype.val h))
      ⟨Z.1, componentGenericPoint_mem_image_top U Z.1⟩

private theorem restrictSection_zero (D : Divisor X) : restrictSection U D 0 = 0 :=
  Subtype.ext (restrictRF_zero U ⊤)

private theorem restrictSection_add (D : Divisor X) (t t' : D.divisorialSubmodule ⊤) :
    restrictSection U D (t + t') = restrictSection U D t + restrictSection U D t' :=
  Subtype.ext (restrictRF_add U ⊤ _ _)

private theorem restrictSection_smul (D : Divisor X) (r : Γ(X, ⊤)) (t : D.divisorialSubmodule ⊤) :
    restrictSection U D (r • t) = U.ι.appTop r • restrictSection U D t := by
  apply Subtype.ext
  change restrictRF U ⊤ ((rationalFunctionsPresheaf X).map _ (r • t.1)) =
    U.ι.appTop r • restrictRF U ⊤ _
  rw [rationalFunctionsPresheaf_map_smul, ← restrictRF_smul]
  congr 2
  rw [Scheme.Opens.ι_appIso, Iso.refl_inv]
  change _ = (Scheme.Hom.app U.ι ⊤) r
  rw [Scheme.Opens.ι_app]
  rfl

/-- Restriction to `U` commutes with linear combinations of global sections. -/
private theorem restrictSection_sum_smul {ι : Type*} (D : Divisor X) (s : Finset ι)
    (c : ι → Γ(X, ⊤)) (t : ι → D.divisorialSubmodule ⊤) :
    restrictSection U D (∑ i ∈ s, c i • t i) =
      ∑ i ∈ s, U.ι.appTop (c i) • restrictSection U D (t i) := by
  let ρ : D.divisorialSubmodule ⊤ →+ Divisor.divisorialSubmodule (D.restrictOpen U) ⊤ :=
    { toFun := restrictSection U D
      map_zero' := restrictSection_zero U D
      map_add' := restrictSection_add U D }
  change ρ _ = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => restrictSection_smul U D (c i) (t i)

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [Nonempty U] [IsDominant U.ι] in
/-- For a unit `φ` of `K(Y)`, `v_E(φ) ≥ n` exactly when `n ≤ ord_E φ`. -/
private theorem ordGE_iff_le_ord {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y]
    (E : MMP.Mori.PrimeDivisor Y) (φ : (RationalFunctions Y)ˣ) (n : ℤ) :
    E.OrdGE n ((φ : RationalFunctions Y) E.component) ↔ n ≤ E.ord φ := by
  have h0 : (φ : RationalFunctions Y) E.component ≠ 0 := ((Pi.isUnit_iff.mp φ.isUnit) _).ne_zero
  rw [MMP.Mori.PrimeDivisor.OrdGE, PrimeDivisor.valuation_component, WithZero.exp_le_exp]
  simp [h0]

/-- The divisor of zeros of the restriction of a section to `U` is the restriction of its
divisor of zeros. -/
private theorem coeff_zeroDivisor_restrictSection [CompactSpace X] [CompactSpace U]
    (D : Divisor X) (t : D.divisorialSubmodule ⊤) (ht : t ≠ 0) (ht' : restrictSection U D t ≠ 0)
    (W : MMP.Mori.PrimeDivisor U.toScheme) :
    (Divisor.zeroDivisor (D.restrictOpen U) (restrictSection U D t) ht').coeff W =
      (D.zeroDivisor t ht).coeff (OpenWeilRestriction.primeDivisorMap U.ι W) := by
  set u := (Divisor.isUnit_sectionToRationalFunctions ht).unit
  set u' := (Divisor.isUnit_sectionToRationalFunctions ht').unit
  have hc : (Divisor.zeroDivisor (D.restrictOpen U) _ ht').coeff W =
      W.ord u' + D.coeff (OpenWeilRestriction.primeDivisorMap U.ι W) := by
    rw [Divisor.zeroDivisor_eq, DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
    rfl
  have hc' : (D.zeroDivisor t ht).coeff (OpenWeilRestriction.primeDivisorMap U.ι W) =
      MMP.Mori.PrimeDivisor.ord (OpenWeilRestriction.primeDivisorMap U.ι W) u +
        D.coeff (OpenWeilRestriction.primeDivisorMap U.ι W) := by
    rw [Divisor.zeroDivisor_eq, DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
  rw [hc, hc']
  congr 1
  have hE' : (W.support ∩ ⊤).Nonempty :=
    ⟨W.genericPoint, Positivity.PrimeDivisor.genericPoint_mem_support' W, trivial⟩
  have hP : ((OpenWeilRestriction.primeDivisorMap U.ι W).support ∩ U.ι ''ᵁ ⊤).Nonempty := by
    refine ⟨_, Positivity.PrimeDivisor.genericPoint_mem_support'
      (OpenWeilRestriction.primeDivisorMap U.ι W), ?_⟩
    change MMP.Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap U.ι W) ∈ _
    rw [show MMP.Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap U.ι W) =
      U.ι W.genericPoint from OpenWeilRestriction.genericPoint_primeDivisorMap _ _]
    exact ⟨_, trivial, rfl⟩
  have key : ∀ n, n ≤ W.ord u' ↔
      n ≤ MMP.Mori.PrimeDivisor.ord (OpenWeilRestriction.primeDivisorMap U.ι W) u :=
    fun n => by
      rw [← ordGE_iff_le_ord, ← ordGE_iff_le_ord]
      exact ordGE_restrictRF_iff U ⊤ _ n W hE' hP
  exact le_antisymm ((key _).1 le_rfl) ((key _).2 le_rfl)

/-- The image under `U.ι` of a point of a prime divisor `W` of `U` lies on the prime divisor of
`X` it determines. -/
private theorem ι_mem_support_primeDivisorMap (W : MMP.Mori.PrimeDivisor U.toScheme)
    {y : U.toScheme} (hy : y ∈ W.support) :
    U.ι y ∈ (OpenWeilRestriction.primeDivisorMap U.ι W).support := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure] at hy ⊢
  rw [show (OpenWeilRestriction.primeDivisorMap U.ι W).genericPoint = U.ι W.genericPoint
    from OpenWeilRestriction.genericPoint_primeDivisorMap _ _]
  exact hy.map U.ι.continuous

/-- The prime divisor of `X` determined by a prime divisor of `U` meets `U`. -/
private theorem support_primeDivisorMap_inter_nonempty (W : MMP.Mori.PrimeDivisor U.toScheme) :
    ((OpenWeilRestriction.primeDivisorMap U.ι W).support ∩ U).Nonempty :=
  ⟨_, ι_mem_support_primeDivisorMap U W (Positivity.PrimeDivisor.genericPoint_mem_support' W),
    (W.genericPoint).2⟩

/-- If at each point of `U` some section `t i` has divisor of zeros avoiding it, the same holds
for the restrictions of the `t i` to `U`. -/
private theorem exists_notMem_supp_zeroDivisor_restrictSection [CompactSpace X] [CompactSpace U]
    (D : Divisor X) {ι : Type*} (t : ι → D.divisorialSubmodule ⊤)
    (ht : ∀ x ∈ U, ∃ i, ∃ hi : t i ≠ 0, x ∉ (D.zeroDivisor (t i) hi).supp) (y : U.toScheme) :
    ∃ (i : ι) (hi : restrictSection U D (t i) ≠ 0),
      y ∉ (Divisor.zeroDivisor (D.restrictOpen U) (restrictSection U D (t i)) hi).supp := by
  obtain ⟨i, hi, hy⟩ := ht (U.ι y) y.2
  refine ⟨i, fun h => hi (restrictSection_injective U D (h.trans (restrictSection_zero U D).symm)),
    fun hyy => hy ?_⟩
  obtain ⟨W, hW, hyW⟩ := DivisorWithCoeffs.mem_supp_iff.mp hyy
  rw [coeff_zeroDivisor_restrictSection U D (t i) hi] at hW
  exact DivisorWithCoeffs.mem_supp_iff.mpr ⟨_, hW, ι_mem_support_primeDivisorMap U W hyW⟩

end DivisorialRestrict

end RestrictOpen

/-- A nonempty open subscheme of a normal variety is a normal variety. -/
private theorem isNormalVariety_ι {k : Type u} [Field k] {Y : Scheme.{u}}
    {s : Y ⟶ Spec (.of k)} (h : IsNormalVariety k s) (V : Y.Opens) [Nonempty V] :
    IsNormalVariety k (V.ι ≫ s) := by
  have := h.1
  have := h.2
  have : IsIntegral Y := h.1.toIsIntegral
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have : IsNoetherian Y := {}
  exact ⟨⟨⟩, inferInstance⟩

/-- The divisor of zeros depends only on the section. -/
private theorem zeroDivisor_congr {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] (D : Divisor Y) {σ σ' : D.divisorialSubmodule ⊤}
    (h : σ = σ') (hσ : σ ≠ 0) (hσ' : σ' ≠ 0) : D.zeroDivisor σ hσ = D.zeroDivisor σ' hσ' := by
  subst h
  rfl

/-! ### Avoiding a prime divisor by a general member -/

section AvoidPrime

/-- A nonzero section `σ` of `𝒪_Y(M)` is a section of `𝒪_Y(M - P)` exactly when its divisor of
zeros contains the prime divisor `P`. -/
private theorem mem_divisorialSubmodule_sub_single_iff {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {M : Divisor Y}
    (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0) (P : PrimeDivisor Y) :
    σ.1 ∈ (M - Finsupp.single P 1).divisorialSubmodule ⊤ ↔
      1 ≤ (M.zeroDivisor σ hσ).coeff P := by
  classical
  set u := (Divisor.isUnit_sectionToRationalFunctions hσ).unit
  have hc : ∀ E, (M.zeroDivisor σ hσ).coeff E = E.ord u + M.coeff E := fun E => by
    rw [Divisor.zeroDivisor_eq, DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
  have hs : ∀ E : PrimeDivisor Y, (M - Finsupp.single P 1).coeff E =
      M.coeff E - if P = E then 1 else 0 := fun E => by
    simp [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]
  rw [Divisor.mem_divisorialSubmodule]
  constructor
  · intro h
    have h1 := h P ⟨P.genericPoint, Positivity.PrimeDivisor.genericPoint_mem_support' P, trivial⟩
    change P.OrdGE _ ((u : RationalFunctions Y) P.component) at h1
    rw [ordGE_iff_le_ord, hs, if_pos rfl] at h1
    rw [hc]
    omega
  · intro h E hE
    change E.OrdGE _ ((u : RationalFunctions Y) E.component)
    rw [ordGE_iff_le_ord, hs]
    have h0 : 0 ≤ (M.zeroDivisor σ hσ).coeff E := Divisor.zeroDivisor_nonneg M σ hσ E
    rw [hc] at h h0
    split_ifs with hPE
    · subst hPE
      omega
    · omega

/-- **A general member of a linear system avoids a prime divisor that one member avoids.** If
the divisor of zeros of `s_j` does not contain `P`, then for a general coefficient vector `c`
neither does that of `∑ cᵢ sᵢ`: the `c` for which `∑ cᵢ sᵢ` is a section of `𝒪_Y(M - P)` form a
proper subspace of `kⁱ`, as it misses the `j`-th basis vector. -/
private theorem exists_polynomial_coeff_zeroDivisor_eq_zero {k : Type u} [Field k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] {M : Divisor Y} {ι : Type*} [Fintype ι] (s : ι → M.divisorialSubmodule ⊤)
    (P : PrimeDivisor Y) (j : ι) (hj : s j ≠ 0) (hjP : (M.zeroDivisor (s j) hj).coeff P = 0) :
    ∃ Q : MvPolynomial ι k, Q ≠ 0 ∧ ∀ c : ι → k, MvPolynomial.eval c Q ≠ 0 →
      ∀ hτ : (∑ i, scalarsToGlobalSections k sY (c i) • s i) ≠ 0,
        (M.zeroDivisor _ hτ).coeff P = 0 := by
  classical
  let p : Submodule k (ι → k) :=
    { carrier := {c | (∑ i, scalarsToGlobalSections k sY (c i) • s i).1 ∈
        (M - Finsupp.single P 1).divisorialSubmodule ⊤}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib,
          Submodule.coe_add] at *
        exact add_mem ha hb
      zero_mem' := by simpa using ((M - Finsupp.single P 1).divisorialSubmodule ⊤).zero_mem
      smul_mem' := by
        intro a c hc
        simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul] at *
        rw [← Finset.smul_sum, Submodule.coe_smul]
        exact Submodule.smul_mem _ _ hc }
  have hsj : (∑ i, scalarsToGlobalSections k sY ((Pi.single j 1 : ι → k) i) • s i) = s j := by
    rw [Finset.sum_eq_single j (fun i _ hi => by simp [Pi.single_apply, hi]) (by simp),
      Pi.single_eq_same, map_one, one_smul]
  have hjp : (Pi.single j 1 : ι → k) ∉ p := by
    intro h
    have h' : (s j).1 ∈ (M - Finsupp.single P 1).divisorialSubmodule ⊤ := by
      have h'' : (∑ i, scalarsToGlobalSections k sY ((Pi.single j 1 : ι → k) i) • s i).1 ∈
          (M - Finsupp.single P 1).divisorialSubmodule ⊤ := h
      rwa [hsj] at h''
    have := (mem_divisorialSubmodule_sub_single_iff (s j) hj P).mp h'
    omega
  obtain ⟨Q, hQ0, hQ⟩ := exists_polynomial_forall_notMem hjp
  refine ⟨Q, hQ0, fun c hc hτ => ?_⟩
  by_contra hne
  apply hQ c hc
  have h0 : 0 ≤ (M.zeroDivisor _ hτ).coeff P := Divisor.zeroDivisor_nonneg M _ hτ P
  exact (mem_divisorialSubmodule_sub_single_iff _ hτ P).mpr (by omega)

end AvoidPrime

/-! ### Bertini on the smooth open -/

/-- A nonzero polynomial over an infinite field does not vanish at some point. -/
private theorem exists_eval_ne_zero {σ k : Type*} [Field k] [Infinite k] {Q : MvPolynomial σ k}
    (hQ : Q ≠ 0) : ∃ c, MvPolynomial.eval c Q ≠ 0 := by
  by_contra h
  push Not at h
  exact hQ (MvPolynomial.funext fun c => by rw [h c, map_zero])

/-- A global scalar restricts to the same scalar on an open. -/
private theorem appTop_ι_scalarsToGlobalSections {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (U : X.Opens) (a : k) :
    U.ι.appTop (scalarsToGlobalSections k sX a) = scalarsToGlobalSections k (U.ι ≫ sX) a := by
  simp only [scalarsToGlobalSections, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    RingHom.comp_apply]

/-- **A general member of a free linear system on the smooth open.** Let `U` be a nonempty open
of a normal variety contained in the smooth locus, on which `G` is snc, and let `M` be a divisor
with finitely many global sections of `𝒪_X(M)`, one of which does not vanish at any given point
of `U`, and one of which avoids each prime divisor of a finite set `Ps`. Then some nonzero
section `τ` has divisor of zeros `(τ)₀` containing no member of `Ps` and sharing no component
meeting `U` with `G`, and every divisor whose components meeting `U` are components of `G` or of
`(τ)₀` is snc on `U`. -/
private theorem exists_section_zeroDivisor_isSNC_restrictOpen {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] (hX : IsNormalVariety k sX) (U : X.Opens) (hUne : (U : Set X).Nonempty)
    (hU : U ≤ smoothLocus sX) (G : QDivisor X) (hG : (G.restrictOpen U).IsSNC (U.ι ≫ sX))
    (M : Divisor X) {N : ℕ} (t : Fin (N + 1) → M.divisorialSubmodule ⊤)
    (ht : ∀ x ∈ U, ∃ i, ∃ hi : t i ≠ 0, x ∉ (M.zeroDivisor (t i) hi).supp)
    (Ps : Finset (PrimeDivisor X))
    (hPs : ∀ P ∈ Ps, ∃ i, ∃ hi : t i ≠ 0, (M.zeroDivisor (t i) hi).coeff P = 0) :
    ∃ (τ : M.divisorialSubmodule ⊤) (hτ : τ ≠ 0), (∀ P ∈ Ps, (M.zeroDivisor τ hτ).coeff P = 0) ∧
      (∀ P : PrimeDivisor X, (P.support ∩ U).Nonempty → (M.zeroDivisor τ hτ).coeff P ≠ 0 →
        G.coeff P = 0) ∧
      ∀ B : QDivisor X, (∀ P : PrimeDivisor X, (P.support ∩ U).Nonempty → B.coeff P ≠ 0 →
          G.coeff P ≠ 0 ∨ (M.zeroDivisor τ hτ).coeff P ≠ 0) →
        (B.restrictOpen U).IsSNC (U.ι ≫ sX) := by
  classical
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : Nonempty U := hUne.to_subtype
  haveI : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense hUne)
  have hUv : IsNormalVariety k (U.ι ≫ sX) := isNormalVariety_ι hX U
  have hUs : IsSmoothScheme (U.ι ≫ sX) := isSmoothScheme_ι_of_le_smoothLocus hU
  haveI : IsLocallyNoetherian U.toScheme := hUv.isLocallyNoetherian
  haveI : IsNormal U.toScheme := hUv.isNormal
  haveI : IsIntegral U.toScheme := hUv.isIntegral
  haveI : CompactSpace U.toScheme := by
    haveI : QuasiCompact (U.ι ≫ sX) := hUv.1.toQuasiCompact
    exact QuasiCompact.compactSpace_of_compactSpace (U.ι ≫ sX)
  letI : U.toScheme.Over (Spec (.of k)) := ⟨U.ι ≫ sX⟩
  haveI : IsSmoothVariety k (U.toScheme ↘ Spec (.of k)) :=
    (isSmoothVariety_iff k _).mpr ⟨hUv.1, hUs.smooth⟩
  set MU : Divisor U.toScheme := M.restrictOpen U
  have hMU : Divisor.IsCartier MU := MMP.Fourfold.isCartier_of_isSmoothScheme hUs MU
  set tU := fun i => restrictSection U M (t i)
  have hne : ∀ τ : M.divisorialSubmodule ⊤, τ ≠ 0 → restrictSection U M τ ≠ 0 :=
    fun τ hτ h => hτ (restrictSection_injective U M (h.trans (restrictSection_zero U M).symm))
  have htU : ∀ y : U.toScheme, ∃ (i : Fin (N + 1)) (hi : tU i ≠ 0),
      y ∉ (Divisor.zeroDivisor MU (tU i) hi).supp :=
    exists_notMem_supp_zeroDivisor_restrictSection U M t ht
  set S := (G.restrictOpen U).support with hSdef
  have hS : DivisorWithCoeffs.IsSNC (U.toScheme ↘ Spec (.of k))
      (∑ E ∈ S, Finsupp.single E (1 : ℤ)) :=
    (DivisorWithCoeffs.isSNC_iff_of_support_eq (by rw [support_sum_single])).mp hG
  obtain ⟨Q, hQ0, hQ⟩ := exists_polynomial_zeroDivisor_isSNC (k := k) MU hMU tU htU S hS
  obtain ⟨j, hj, -⟩ := htU (Classical.arbitrary U.toScheme)
  obtain ⟨Q', hQ'0, hQ'⟩ := exists_polynomial_sum_smul_ne_zero (U.toScheme ↘ Spec (.of k)) tU j hj
  have hQP : ∀ P ∈ Ps, ∃ QP : MvPolynomial (Fin (N + 1)) k, QP ≠ 0 ∧ ∀ c : Fin (N + 1) → k,
      MvPolynomial.eval c QP ≠ 0 →
        ∀ hτ : (∑ i, scalarsToGlobalSections k sX (c i) • t i) ≠ 0,
          (M.zeroDivisor _ hτ).coeff P = 0 := fun P hP => by
    obtain ⟨i, hi, h0⟩ := hPs P hP
    exact exists_polynomial_coeff_zeroDivisor_eq_zero sX t P i hi h0
  choose! QP hQP0 hQP using hQP
  obtain ⟨c, hc⟩ := exists_eval_ne_zero
    (mul_ne_zero (mul_ne_zero hQ0 hQ'0) (Finset.prod_ne_zero_iff.mpr fun P hP => hQP0 P hP))
  rw [map_mul, map_mul, map_prod] at hc
  have hcP := Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hc)
  replace hc := left_ne_zero_of_mul hc
  have hτU := hQ' c (right_ne_zero_of_mul hc)
  set τ := ∑ i, scalarsToGlobalSections k sX (c i) • t i with hτdef
  have hsc : ∀ a : k, U.ι.appTop (scalarsToGlobalSections k sX a) =
      scalarsToGlobalSections k (U.toScheme ↘ Spec (.of k)) a :=
    appTop_ι_scalarsToGlobalSections sX U
  have hρ : restrictSection U M τ =
      ∑ i, scalarsToGlobalSections k (U.toScheme ↘ Spec (.of k)) (c i) • tU i := by
    rw [hτdef, restrictSection_sum_smul]
    exact Finset.sum_congr rfl fun i _ => by rw [hsc]
  have hτ : τ ≠ 0 := fun h => hτU (by rw [← hρ, h, restrictSection_zero])
  obtain ⟨T, hT, hTS, hsnc⟩ := hQ c (left_ne_zero_of_mul hc) hτU
  have hcoeff : ∀ W, (M.zeroDivisor τ hτ).coeff (OpenWeilRestriction.primeDivisorMap U.ι W) =
      (Divisor.zeroDivisor MU _ hτU).coeff W := by
    intro W
    rw [← coeff_zeroDivisor_restrictSection U M τ hτ (hne τ hτ), zeroDivisor_congr _ hρ]
  refine ⟨τ, hτ, fun P hP => hQP P hP c (hcP P hP) hτ, fun P hP hP0 => ?_, fun B hB => ?_⟩
  · obtain ⟨W, rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff U.ι P).2 (by
      rw [Scheme.Opens.range_ι]
      exact (P.genericPoint_mem_iff U).2 hP)
    rw [hcoeff] at hP0
    have hWS : W ∉ S := Finset.disjoint_left.mp hTS (hT W hP0)
    rwa [hSdef, Finsupp.notMem_support_iff] at hWS
  · refine hsnc.of_support_subset fun W hW => ?_
    rw [support_sum_single, Finset.mem_union]
    rw [Finsupp.mem_support_iff] at hW
    rcases hB _ (support_primeDivisorMap_inter_nonempty U W) hW with h | h
    · exact Or.inr (Finsupp.mem_support_iff.mpr h)
    · exact Or.inl (hT W (by rwa [← hcoeff]))

/-- A prime divisor whose support lies in a finite union of supports of prime divisors is one
of them. -/
private theorem mem_of_support_subset_iUnion {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y]
    (s : Finset (PrimeDivisor Y)) {E : PrimeDivisor Y}
    (hE : E.support ⊆ ⋃ E' ∈ s, E'.support) : E ∈ s := by
  obtain ⟨E', hE's, hE'⟩ :=
    Set.mem_iUnion₂.mp (hE (Positivity.PrimeDivisor.genericPoint_mem_support' E))
  rwa [← MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E' E hE']

/-- Only finitely many prime divisors have support inside an snc closed subset. -/
private theorem exists_finset_of_isSNCSubset {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] {g : Y ⟶ Spec (.of k)} {S : Closeds Y}
    (hS : IsSNCSubset g S) :
    ∃ s : Finset (PrimeDivisor Y), ∀ E : PrimeDivisor Y, E.support ⊆ (S : Set Y) → E ∈ s := by
  rcases hS with rfl | ⟨s, hs, -⟩
  · exact ⟨∅, fun E hE =>
    absurd (hE (Positivity.PrimeDivisor.genericPoint_mem_support' E)) (by simp)⟩
  · exact ⟨s, fun E hE => mem_of_support_subset_iUnion s (by rwa [hs])⟩

private theorem mul_le_one_of_le_one_div_add_one {ε d : ℚ} (hε : 0 ≤ ε) (hd : 0 ≤ d)
    (hεd : ε ≤ 1 / (d + 1)) : ε * d ≤ 1 := by
  rw [le_div_iff₀ (by linarith)] at hεd
  nlinarith

private theorem perturbedCoeff_mem_unitInterval {δ d₁ d ε : ℚ} (h1 : 0 ≤ d₁) (h2 : d₁ ≤ δ)
    (h3 : 0 ≤ δ ∧ δ ≤ 1) (hd : 0 ≤ d) (hdδ : d ≠ 0 → δ = 0) (hε : 0 < ε) (hε1 : ε < 1)
    (hεd : ε * d ≤ 1) : 0 ≤ δ - ε * d₁ + ε * d ∧ δ - ε * d₁ + ε * d ≤ 1 := by
  by_cases hP : d = 0
  · rw [hP]
    constructor <;> nlinarith
  · have h4 := hdδ hP
    have h5 : d₁ = 0 := le_antisymm (h4 ▸ h2) h1
    rw [h4, h5]
    constructor <;> nlinarith

private theorem perturbedCoeff_ne_zero_iff {δ d₁ d ε : ℚ} (h1 : 0 ≤ d₁) (h2 : d₁ ≤ δ)
    (h3 : 0 ≤ δ ∧ δ ≤ 1) (hd : 0 ≤ d) (hdδ : d ≠ 0 → δ = 0) (hε : 0 < ε) (hε1 : ε < 1) :
    δ - ε * d₁ + ε * d ≠ 0 ↔ δ ≠ 0 ∨ d ≠ 0 := by
  by_cases hP : d = 0
  · rw [hP]
    simp only [mul_zero, add_zero, ne_eq, not_true_eq_false, or_false]
    constructor
    · intro hne h0
      apply hne
      rw [h0] at h2 ⊢
      nlinarith
    · intro hne
      nlinarith [lt_of_le_of_ne h3.1 (Ne.symm hne)]
  · have h4 := hdδ hP
    have h5 : d₁ = 0 := le_antisymm (h4 ▸ h2) h1
    rw [h4, h5]
    simp only [hP, ne_eq, not_false_eq_true, or_true, iff_true]
    have : 0 < d := lt_of_le_of_ne hd (Ne.symm hP)
    nlinarith

private theorem exists_pos_forall_neg_one_lt_sub_mul {a b : ℚ} (ha : -1 < a) :
    ∃ c : ℚ, 0 < c ∧ ∀ ε : ℚ, 0 < ε → ε < c → -1 < a - ε * b := by
  refine ⟨(a + 1) / (|b| + 1), div_pos (by linarith) (by positivity), fun ε hε hεc => ?_⟩
  rw [lt_div_iff₀ (by positivity)] at hεc
  have h1 : ε * b ≤ ε * |b| := mul_le_mul_of_nonneg_left (le_abs_self _) hε.le
  nlinarith

/-- A discrepancy `> -1` for `Δ` stays `> -1` for `Δ + ε B` for all small `ε > 0`, when the
discrepancies of the two pairs differ by `ε b`. -/
private theorem exists_pos_forall_neg_one_lt_of_isDiscrepancy {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} {K : Divisor X} {Δ B : QDivisor X}
    {E : DivisorOver k sX} {b : ℚ}
    (hb : ∀ t a : ℚ, IsDiscrepancy sX n K (Δ + t • B) E (a - t * b) ↔ IsDiscrepancy sX n K Δ E a)
    (hdisc : ∀ a, IsDiscrepancy sX n K Δ E a → -1 < a) :
    ∃ c : ℚ, 0 < c ∧ ∀ ε : ℚ, 0 < ε → ε < c → ∀ a : ℚ,
      IsDiscrepancy sX n K (Δ + ε • B) E a → -1 < a := by
  have hshift : ∀ ε a, IsDiscrepancy sX n K (Δ + ε • B) E a →
      IsDiscrepancy sX n K Δ E (a + ε * b) := fun ε a ha =>
    (hb ε (a + ε * b)).mp (by rwa [add_sub_cancel_right])
  by_cases hex : ∃ a, IsDiscrepancy sX n K Δ E a
  · obtain ⟨a₀, ha₀⟩ := hex
    obtain ⟨c, hc, hc'⟩ := exists_pos_forall_neg_one_lt_sub_mul (b := b) (hdisc a₀ ha₀)
    refine ⟨c, hc, fun ε hε hεc a ha => ?_⟩
    have := hc' ε hε hεc
    rw [← IsDiscrepancy.eq (hshift ε a ha) ha₀] at this
    linarith
  · exact ⟨1, one_pos, fun ε _ _ a ha => absurd ⟨_, hshift ε a ha⟩ hex⟩

private theorem coeff_sub_smul_add_smul {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y]
    {Δ Δ₁ D : QDivisor Y} (hcoef : ∀ P, 0 ≤ Δ.coeff P ∧ Δ.coeff P ≤ 1)
    (hΔ₁ : Δ₁.IsEffective) (hΔΔ₁ : (Δ - Δ₁).IsEffective) (hD : D.IsEffective)
    (hDΔ : Disjoint D.support Δ.support) {ε : ℚ} (hε : 0 < ε) (hε1 : ε < 1)
    (hεD : ∀ P, ε * D.coeff P ≤ 1) (P : PrimeDivisor Y) :
    (0 ≤ (Δ - ε • Δ₁ + ε • D).coeff P ∧ (Δ - ε • Δ₁ + ε • D).coeff P ≤ 1) ∧
      ((Δ - ε • Δ₁ + ε • D).coeff P ≠ 0 ↔ (Δ + D).coeff P ≠ 0) := by
  have hle : Δ₁.coeff P ≤ Δ.coeff P := by
    have := hΔΔ₁ P
    rw [DivisorWithCoeffs.coeff_sub] at this
    linarith
  have h0 : D.coeff P ≠ 0 → Δ.coeff P = 0 := fun hP => by
    by_contra h0
    exact Finset.disjoint_left.mp hDΔ (Finsupp.mem_support_iff.mpr hP)
      (Finsupp.mem_support_iff.mpr h0)
  have hc : (Δ - ε • Δ₁ + ε • D).coeff P = Δ.coeff P - ε * Δ₁.coeff P + ε * D.coeff P := by
    simp
  rw [hc, DivisorWithCoeffs.coeff_add]
  exact ⟨perturbedCoeff_mem_unitInterval (hΔ₁ P) hle (hcoef P) (hD P) h0 hε hε1 (hεD P),
    (perturbedCoeff_ne_zero_iff (hΔ₁ P) hle (hcoef P) (hD P) h0 hε hε1).trans
      ((add_eq_zero_iff_of_nonneg (hcoef P).1 (hD P)).not.trans not_and_or).symm⟩

/-- **The dlt criterion for the perturbed pair.** If `f` is a log resolution of `Δ + D` with
pure codimension-one snc preimage of `Z`, and every divisor of `f` over `Z` has discrepancy
`> -1` for `Δ + ε(D - Δ₁)`, then `(X, Δ - εΔ₁ + εD)` is dlt. -/
private theorem isDltPair_sub_smul_add_smul_of_isLogResolution {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (h : IsDltPair sX n K Δ) {Z : Closeds X} (hZ : Z ≠ ⊤)
    (hU : (Z.compl : X.Opens) ≤ smoothLocus sX) {Δ₁ D : QDivisor X} (hΔ₁ : Δ₁.IsEffective)
    (hΔΔ₁ : (Δ - Δ₁).IsEffective) (hD : D.IsEffective) (hDΔ : Disjoint D.support Δ.support)
    (hDq : (D - Δ₁).IsQCartier)
    (hsnc : ((Δ + D).restrictOpen (Z.compl : X.Opens)).IsSNC
      (Scheme.Opens.ι (X := X) Z.compl ≫ sX))
    {ε : ℚ} (hε : 0 < ε) (hε1 : ε < 1) (hεD : ∀ P, ε * D.coeff P ≤ 1) {Y : Scheme.{u}}
    {f : Y ⟶ X} (hf : IsLogResolution sX (QDivisor.toRDivisor (Δ + D)) f)
    (hpure : IsPureCodimOne (Z.preimage f.continuous))
    (hS : IsSNCSubset (f ≫ sX)
      (exceptionalSet f ⊔ (Δ + D).supp.preimage f.continuous ⊔ Z.preimage f.continuous))
    (hdisc : ∀ (hY : IsNormalVariety k (f ≫ sX)) (E : PrimeDivisor Y),
      E.support ⊆ f ⁻¹' (Z : Set X) → ∀ a : ℚ,
        IsDiscrepancy sX n K (Δ + ε • (D - Δ₁)) ⟨Y, f, hY, hf.isBirationalMorphism, E⟩ a →
          -1 < a) :
    IsDltPair sX n K (Δ - ε • Δ₁ + ε • D) := by
  classical
  have hΘ : Δ - ε • Δ₁ + ε • D = Δ + ε • (D - Δ₁) := by
    rw [smul_sub]
    abel
  have hΘP := coeff_sub_smul_add_smul h.2.1 hΔ₁ hΔΔ₁ hD hDΔ hε hε1 hεD
  have hsupp : (Δ - ε • Δ₁ + ε • D).supp = (Δ + D).supp := by
    have : (Δ - ε • Δ₁ + ε • D).support = (Δ + D).support := by
      ext P
      rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff]
      exact (hΘP P).2
    simp only [DivisorWithCoeffs.supp, this]
  have hpair : IsPairWith sX n K (Δ - ε • Δ₁ + ε • D) := by
    refine ⟨h.1.1, h.1.2.1, ?_⟩
    rw [hΘ, ← add_assoc]
    exact h.1.2.2.add (isQCartier_smul hDq ε)
  have hfΘ : IsLogResolution sX (QDivisor.toRDivisor (Δ - ε • Δ₁ + ε • D)) f :=
    { hf with
      isSNCSubset := by
        rw [QDivisor.supp_toRDivisor, hsupp, ← QDivisor.supp_toRDivisor]
        exact hf.isSNCSubset }
  refine (isDltPair_iff_exists_isLogResolution hpair fun P => (hΘP P).1).mpr
    ⟨Z, hZ, hU, hsnc.of_support_subset fun W hW => ?_, Y, f, hfΘ, hpure, hsupp ▸ hS,
      fun hY E hE a ha => hdisc hY E hE a (by rwa [← hΘ])⟩
  rw [Finsupp.mem_support_iff] at hW ⊢
  exact (hΘP _).2.mp hW

/-- **The perturbed pair is dlt.** Let `(X, Δ)` be dlt, with `U` a nonempty smooth open on which
`Δ` is snc and off which every divisor over `X` has discrepancy `> -1`. Let `0 ≤ Δ₁ ≤ Δ` and
let `D ≥ 0` have no component in common with `Δ`, with `D - Δ₁` `ℚ`-Cartier and `D + Δ` snc on
`U`. Then `(X, Δ - εΔ₁ + εD)` is dlt for every sufficiently small rational `ε > 0`. -/
private theorem exists_forall_isDltPair_of_isSNC {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (h : IsDltPair sX n K Δ) {U : X.Opens} (hUne : (U : Set X).Nonempty)
    (hU : U ≤ smoothLocus sX)
    (hdisc : ∀ (D : DivisorOver k sX) (a : ℚ), (D.center : Set X) ⊆ (U : Set X)ᶜ →
      IsDiscrepancy sX n K Δ D a → -1 < a)
    {Δ₁ D : QDivisor X} (hΔ₁ : Δ₁.IsEffective) (hΔΔ₁ : (Δ - Δ₁).IsEffective)
    (hD : D.IsEffective) (hDΔ : Disjoint D.support Δ.support) (hDq : (D - Δ₁).IsQCartier)
    (hsnc : ((Δ + D).restrictOpen U).IsSNC (U.ι ≫ sX)) :
    ∃ ε₀ : ℚ, 0 < ε₀ ∧ ∀ ε : ℚ, 0 < ε → ε < ε₀ →
      IsDltPair sX n K (Δ - ε • Δ₁ + ε • D) := by
  classical
  have hX : IsNormalVariety k sX := h.1.1
  let Z : Closeds X := U.compl
  have hZU : (Z.compl : X.Opens) = U := Opens.compl_compl U
  have hZ : Z ≠ ⊤ := by
    rintro hZ
    obtain ⟨x, hx⟩ := hUne
    exact (show x ∈ (Z : Set X) by rw [hZ]; trivial) hx
  obtain ⟨Y, f, hf, hpure, hS⟩ := exists_isLogResolution_isPureCodimOne_preimage sX hX
    (QDivisor.toRDivisor (Δ + D)) Z hZ
  rw [QDivisor.supp_toRDivisor] at hS
  obtain ⟨hY, -, -⟩ := hf.toIsSmoothResolution.isNormalVariety hX
  have : IsIntegral Y := hY.isIntegral
  have : IsNormal Y := hY.isNormal
  have : IsLocallyNoetherian Y := hY.isLocallyNoetherian
  have : CompactSpace X := by
    have := hX.1.toQuasiCompact
    exact QuasiCompact.compactSpace_of_compactSpace sX
  have : IsProper f := hf.toIsSmoothResolution.isProper
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  let 𝓔 : PrimeDivisor Y → DivisorOver k sX := fun E =>
    ⟨Y, f, hY, hf.toIsSmoothResolution.isBirationalMorphism, E⟩
  have hc : ∀ E : PrimeDivisor Y, ∃ c : ℚ, 0 < c ∧ ∀ ε : ℚ, 0 < ε → ε < c →
      E.support ⊆ f ⁻¹' (Z : Set X) → ∀ a : ℚ,
        IsDiscrepancy sX n K (Δ + ε • (D - Δ₁)) (𝓔 E) a → -1 < a := fun E => by
    by_cases hEZ : E.support ⊆ f ⁻¹' (Z : Set X)
    · have hcen : ((𝓔 E).center : Set X) ⊆ (U : Set X)ᶜ := by
        rw [DivisorOver.coe_center]
        exact closure_minimal (Set.image_subset_iff.mpr hEZ) U.isOpen.isClosed_compl
      obtain ⟨-, hB, hfor⟩ := IsPairWith.isDiscrepancy_add_smul_iff h.1 hDq (𝓔 E)
      obtain ⟨B', hB'⟩ := (QDivisor.IsQCartier.existsUnique_isPullback hDq hB).exists
      obtain ⟨c, hc, hc'⟩ :=
        exists_pos_forall_neg_one_lt_of_isDiscrepancy (hfor B' hB').2 fun a => hdisc _ a hcen
      exact ⟨c, hc, fun ε hε hεc _ => hc' ε hε hεc⟩
    · exact ⟨1, one_pos, fun _ _ _ hE => absurd hE hEZ⟩
  choose c hc0 hc using hc
  obtain ⟨s, hs⟩ := exists_finset_of_isSNCSubset hS
  obtain ⟨δs, hδs, hδsle⟩ := exists_pos_forall_le s c fun E _ => hc0 E
  obtain ⟨δD, hδD, hδDle⟩ := exists_pos_forall_le D.support (fun P => 1 / (D.coeff P + 1))
    fun P _ => by have := hD P; positivity
  refine ⟨min (min (1 / 2) δD) δs, lt_min (lt_min (by norm_num) hδD) hδs, fun ε hε hεlt => ?_⟩
  have hε1 : ε < 1 := by
    have := (min_le_left _ _).trans (min_le_left _ _) |>.trans_lt' hεlt
    linarith
  have hεD : ∀ P, ε * D.coeff P ≤ 1 := fun P => by
    by_cases hP : D.coeff P = 0
    · simp [hP]
    · exact mul_le_one_of_le_one_div_add_one hε.le (hD P) <|
        (hεlt.le.trans ((min_le_left _ _).trans (min_le_right _ _))).trans
          (hδDle P (Finsupp.mem_support_iff.mpr hP))
  exact isDltPair_sub_smul_add_smul_of_isLogResolution h hZ (hZU ▸ hU) hΔ₁ hΔΔ₁ hD hDΔ hDq
    (hZU ▸ hsnc) hε hε1 hεD hf hpure hS fun _ E hE =>
      hc E ε hε (hεlt.trans_le ((min_le_right _ _).trans
        (hδsle E (hs E fun y hy => Or.inr (hE hy))))) hE

end Helpers

end MMP.Proof_lem_km5b_dlt_perturbation_no_common_component

namespace MMP.Mori

open MMP.Proof_lem_km5b_dlt_perturbation_no_common_component

/-- **Perturbing a dlt pair by an ample divisor with no common component** (Kollár–Mori, proof
of 2.43, as used in 5.52). Let `(X, Δ)` be a dlt pair of dimension `n ≥ 2`, with canonical
divisor `K`, on a quasi-projective variety over an algebraically closed field of characteristic
zero, let `H` be an ample Cartier divisor, and let `Δ₁` be an effective `ℚ`-divisor with
`Δ - Δ₁` effective. Then there are a rational `c > 0` and an effective `ℚ`-divisor `D` with no
component in common with `Δ` and `D - Δ₁ ∼_ℚ cH`, and a rational `ε₀ > 0` such that
`(X, Δ - εΔ₁ + εD)` is dlt for every rational `0 < ε < ε₀`. -/
@[mmp "lem_km5b_dlt_perturbation_no_common_component"]
public theorem IsDltPair.exists_forall_isDltPair_sub_smul_add_smul_of_disjoint {k : Type u}
    [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {n : ℕ}
    {K : Divisor X} {Δ : QDivisor X} (h : IsDltPair sX n K Δ) (hqp : IsQuasiProjective sX)
    (hn : 2 ≤ n) {H : Divisor X} (hH : H.IsCartier) (hHa : H.IsAmple hH)
    {Δ₁ : QDivisor X} (hΔ₁ : Δ₁.IsEffective) (hΔΔ₁ : (Δ - Δ₁).IsEffective) :
    ∃ c : ℚ, 0 < c ∧ ∃ D : QDivisor X, D.IsEffective ∧ Disjoint D.support Δ.support ∧
      (D - Δ₁).QLinearlyEquivalent (c • Divisor.toQDivisor H) ∧
      ∃ ε₀ : ℚ, 0 < ε₀ ∧ ∀ ε : ℚ, 0 < ε → ε < ε₀ →
        IsDltPair sX n K (Δ - ε • Δ₁ + ε • D) := by
  have hX : IsNormalVariety k sX := h.1.1
  obtain ⟨U, hUne, hUsm, hUsnc, hdisc, -⟩ := MMP.Threefold.Mori.IsDltPair.exists_open_nonempty h
  obtain ⟨m, hm, E₁, hE₁⟩ := exists_toQDivisor_eq_smul Δ₁
  obtain ⟨m', hm', N, t, ht⟩ := exists_sections_forall_notMem_supp_zeroDivisor hX hH hHa E₁
  have hPs : ∀ P ∈ Δ.support, ∃ i, ∃ hi : t i ≠ 0,
      ((E₁ + m' • H).zeroDivisor (t i) hi).coeff P = 0 := by
    intro P _
    obtain ⟨i, hi, hP⟩ := ht _ (MMP.Positivity.PrimeDivisor.genericPoint_mem_smoothLocus hX P)
    exact ⟨i, hi, by_contra fun hne =>
      hP (DivisorWithCoeffs.support_subset_supp hne
        (Positivity.PrimeDivisor.genericPoint_mem_support' P))⟩
  obtain ⟨τ, hτ, hτΔ, -, hτsnc⟩ :=
    exists_section_zeroDivisor_isSNC_restrictOpen hX U hUne hUsm Δ hUsnc (E₁ + m' • H) t
      (fun x hx => ht x (hUsm hx)) Δ.support hPs
  set D' := (E₁ + m' • H).zeroDivisor τ hτ with hD'
  set D : QDivisor X := (m : ℚ)⁻¹ • Divisor.toQDivisor D' with hD
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hD'eff : ∀ P, 0 ≤ D'.coeff P := Divisor.zeroDivisor_nonneg _ τ hτ
  have hDcoeff : ∀ P, D.coeff P = (m : ℚ)⁻¹ * D'.coeff P := fun P => by
    simp [D, smul_eq_mul]
  have hDeff : D.IsEffective := fun P => by
    rw [hDcoeff]
    exact mul_nonneg (by positivity) (by exact_mod_cast hD'eff P)
  have hmD : Divisor.toQDivisor D' = (m : ℚ) • D := by
    rw [hD, smul_smul, mul_inv_cancel₀ hmQ, one_smul]
  have hDΔ : Disjoint D.support Δ.support := by
    rw [Finset.disjoint_left]
    intro P hPD hPΔ
    apply Finsupp.mem_support_iff.mp hPD
    change D.coeff P = 0
    rw [hDcoeff, hτΔ P hPΔ]
    simp
  set u := (Divisor.isUnit_sectionToRationalFunctions hτ).unit with hu
  have hkey : (m : ℤ) • (D - Δ₁) = Divisor.toQDivisor (principalDivisor u + m' • H) := by
    rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℚ, smul_sub, ← hmD, ← hE₁, hD',
      Divisor.zeroDivisor_eq, ← hu]
    simp only [map_add]
    abel
  have hDq : (D - Δ₁).IsQCartier :=
    ⟨m, by exact_mod_cast hm.ne', _, hkey.symm,
      (Divisor.isCartier_principalDivisor _).add (hH.nsmul m')⟩
  have hsnc : ((Δ + D).restrictOpen U).IsSNC (U.ι ≫ sX) := by
    refine hτsnc _ fun P _ hP => ?_
    by_contra hc
    push Not at hc
    apply hP
    rw [DivisorWithCoeffs.coeff_add, hc.1, hDcoeff, hc.2]
    simp
  obtain ⟨ε₀, hε₀, hε⟩ :=
    exists_forall_isDltPair_of_isSNC h hUne hUsm hdisc hΔ₁ hΔΔ₁ hDeff hDΔ hDq hsnc
  refine ⟨(m' : ℚ) / m, by positivity, D, hDeff, hDΔ, ⟨m, hm, u, ?_⟩, ε₀, hε₀, hε⟩
  have hH' : (m : ℤ) • (((m' : ℚ) / m) • Divisor.toQDivisor H) = Divisor.toQDivisor (m' • H) := by
    rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_div_cancel₀ _ hmQ, map_nsmul,
      Nat.cast_smul_eq_nsmul]
  rw [smul_sub, hkey, hH', map_add, add_sub_cancel_right]

end MMP.Mori

end
