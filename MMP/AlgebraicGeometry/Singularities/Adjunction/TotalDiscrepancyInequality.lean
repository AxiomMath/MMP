module
public import MMP.AlgebraicGeometry.Singularities.Adjunction.DiscrepancyOverDivisor
public import MMP.AlgebraicGeometry.Morphisms.FiniteCoverTrace

/-!
# Inversion of adjunction: the total discrepancy of `(S, B|_S)` bounds `discrep(X, S + B)`

Let `X` be a normal variety over an algebraically closed field `k` of characteristic zero, `S` a
reduced divisor on `X` whose support is a normal scheme and which is Cartier at every
codimension-two point of `X` lying on `S`, `Z ⊆ S` closed, and `B` a `ℚ`-divisor on `X` with no
component in `S` such that `K_X + S + B` is `ℚ`-Cartier. The components `Sⱼ` of `S` are then
pairwise disjoint normal varieties, `(S, B|_S)` is a pair on `S` in the sense of
`MMP.Mori.PairOnNormalDivisor`, and

  `totaldiscrep(center ⊆ Z, S, B|_S) ≥ discrep(center ⊆ Z, X, S + B)`.

Indeed every divisor `F` over a component `Sⱼ` with center in `Z` is realised by an exceptional
divisor `G` over `X` with the same center and `a(G, X, S + B) = a(F, Sⱼ, B|_{Sⱼ})`.

## Main definitions

* `MMP.Mori.PairOnNormalDivisor.ofRestrict`: the pair `(S, B|_S)` on `S`, built from the
  hypotheses above.

## Main results

* `MMP.Mori.isNormal_subscheme_of_isNormal_suppScheme`, `MMP.Mori.isNormalVariety_component`:
  the components of a reduced divisor with normal support are normal varieties.
* `MMP.Mori.exists_isCanonicalDivisor_and_isQCartier_restrictPrimeDivisor`: adjunction on the
  components: each `Sⱼ` has a canonical divisor of dimension `n`, and `K_{Sⱼ} + B|_{Sⱼ}` is
  `ℚ`-Cartier.
* `MMP.Mori.discrepCenterIn_le_totalDiscrepCenterIn_restrict`: the inequality above.
* `MMP.Mori.discrepCenterIn_le_totalDiscrepCenterIn_of_components_eq`: the inequality for every
  choice of canonical divisors `K_{Sⱼ}`.

## Implementation notes

The pair `(S, B|_S)` has as components the prime divisors of `S`, dimension `dim X - 1 = n`, and
boundary `MMP.Mori.DivisorWithCoeffs.restrictPrimeDivisor B Sⱼ` on each component `Sⱼ`; its
canonical divisors `K_{Sⱼ}` are chosen. The inequality does not depend on that choice. Both sides
are infima in `EReal`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 5.46
* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][Kollar92], 17.2
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u v

namespace MMP.Mori

/-- Restriction along `f : T ⟶ X` ignores a summand `D'` none of whose components meets the image
of `f`: `(D + D')|_T = D|_T`. -/
private theorem restrict_add_of_forall_notMem {R : Type v} [AddCommMonoid R]
    {X T : Scheme.{u}} (f : T ⟶ X) (D D' : DivisorWithCoeffs R X)
    (h : ∀ E ∈ D'.support, ∀ t : T, f t ∉ E.support) :
    (D + D').restrict f = D.restrict f := by
  have hc : DivisorWithCoeffs.restrictCoeff f (D + D') = DivisorWithCoeffs.restrictCoeff f D := by
    funext P
    unfold DivisorWithCoeffs.restrictCoeff
    rw [Finsupp.sum_add_index' (fun _ => smul_zero _) (fun _ _ _ => smul_add _ _ _)]
    have h0 : (D'.sum fun E d => E.intersectionLength f P • d) = 0 :=
      Finset.sum_eq_zero fun Q hQ => by
        dsimp only
        rw [PrimeDivisor.intersectionLength_eq_zero_of_notMem f Q (h Q hQ _), zero_smul]
    rw [h0, add_zero]
  unfold DivisorWithCoeffs.restrict
  rw [hc]

/-- `D'` is Cartier at `x` if `D` is and every point has a neighbourhood on which `D'` agrees with
`D` or vanishes (at the prime divisors whose generic point lies there). -/
private theorem isCartierAt_of_locally {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D D' : Divisor X} {x : X} (h : MMP.Flips.IsCartierAt D x)
    (hloc : ∀ y : X, ∃ W : X.Opens, y ∈ W ∧
      ((∀ P : MMP.Mori.PrimeDivisor X, P.genericPoint ∈ W → D'.coeff P = D.coeff P) ∨
        (∀ P : MMP.Mori.PrimeDivisor X, P.genericPoint ∈ W → D'.coeff P = 0))) :
    MMP.Flips.IsCartierAt D' x := by
  obtain ⟨U, hxU, hU⟩ := h
  refine ⟨U, hxU, fun y => ?_⟩
  obtain ⟨W, hyW, hW⟩ := hloc (U.ι y)
  rcases hW with hW | hW
  · obtain ⟨U', hyU', φ, hφ⟩ := hU y
    refine ⟨U' ⊓ U.ι ⁻¹ᵁ W, ⟨hyU', hyW⟩, φ, fun Q hQ => ?_⟩
    have hgen := MMP.Mori.PrimeDivisor.genericPoint_mem_of_nonempty Q (U := U' ⊓ U.ι ⁻¹ᵁ W) hQ
    rw [DivisorWithCoeffs.coeff_restrictOpen, hW _ (by
      change AlgebraicGeometry.PrimeDivisor.genericPoint _ ∈ W
      rw [OpenWeilRestriction.genericPoint_primeDivisorMap]
      exact hgen.2),
      ← DivisorWithCoeffs.coeff_restrictOpen]
    obtain ⟨z, hz, hz'⟩ := hQ
    exact hφ Q ⟨z, hz, hz'.1⟩
  · refine ⟨U.ι ⁻¹ᵁ W, hyW, 1, fun Q hQ => ?_⟩
    have hgen := MMP.Mori.PrimeDivisor.genericPoint_mem_of_nonempty Q (U := U.ι ⁻¹ᵁ W) hQ
    rw [DivisorWithCoeffs.coeff_restrictOpen, hW _ (by
      change AlgebraicGeometry.PrimeDivisor.genericPoint _ ∈ W
      rw [OpenWeilRestriction.genericPoint_primeDivisorMap]
      exact hgen),
      MMP.Mori.PrimeDivisor.ord_one]

/-- For a reduced divisor `S` and a component `E` of `S`, `E` is not a component of `S - E`. -/
private theorem coeff_toQDivisor_sub_single_self {X : Scheme.{u}} {S : Divisor X}
    (hS : MMP.Intersection.IsReducedEffective S) {E : MMP.Mori.PrimeDivisor X}
    (hE : E ∈ S.support) : (Divisor.toQDivisor S - Finsupp.single E 1).coeff E = 0 := by
  rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_single_self]
  change ((S.coeff E : ℤ) : ℚ) - 1 = 0
  rw [(hS E).resolve_left (Finsupp.mem_support_iff.mp hE)]
  norm_num

/-- For a reduced divisor `S` and a component `E` of `S`, every component of `S - E` is a
component of `S` other than `E`. -/
private theorem mem_support_and_ne_of_coeff_sub_single {X : Scheme.{u}} {S : Divisor X}
    (hS : MMP.Intersection.IsReducedEffective S) {E : MMP.Mori.PrimeDivisor X} (hE : E ∈ S.support)
    {P : MMP.Mori.PrimeDivisor X} (hP : (Divisor.toQDivisor S - Finsupp.single E 1).coeff P ≠ 0) :
    P ∈ S.support ∧ P ≠ E := by
  by_cases hPE : P = E
  · subst hPE
    exact absurd (coeff_toQDivisor_sub_single_self hS hE) hP
  · rw [DivisorWithCoeffs.coeff_sub] at hP
    refine ⟨Finsupp.mem_support_iff.mpr fun h0 => hP ?_, hPE⟩
    rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hPE)]
    change ((S.coeff P : ℤ) : ℚ) - 0 = 0
    rw [show S.coeff P = 0 from h0]
    norm_num

/-- If the components of a reduced divisor `S` are pairwise disjoint, each component `E` is Cartier
wherever `S` is: near `E` the divisor `E` agrees with `S`, and away from `E` it vanishes. -/
private theorem isCartierAt_single_of_isCartierAt {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] {S : Divisor X} (hS : MMP.Intersection.IsReducedEffective S)
    {E : MMP.Mori.PrimeDivisor X} (hE : E ∈ S.support)
    (hdisj : ∀ P ∈ S.support, P ≠ E → Disjoint E.support P.support) {x : X}
    (hx : MMP.Flips.IsCartierAt S x) : MMP.Flips.IsCartierAt (Finsupp.single E 1) x := by
  classical
  refine isCartierAt_of_locally hx fun y => ?_
  by_cases hy : y ∈ E.support
  · let C : Set X := ⋃ P ∈ S.support.filter (· ≠ E), P.support
    have hC : IsClosed C := isClosed_biUnion_finset fun P _ => P.idealSheaf.support.isClosed
    refine ⟨⟨Cᶜ, hC.isOpen_compl⟩, ?_, Or.inl fun P hP => ?_⟩
    · change y ∉ C
      simp only [C, Set.mem_iUnion, Finset.mem_filter, not_exists]
      exact fun P ⟨hPS, hPE⟩ => Set.disjoint_left.mp (hdisj P hPS hPE) hy
    · by_cases hPE : P = E
      · subst hPE
        rw [DivisorWithCoeffs.coeff_single_self,
          (hS P).resolve_left (Finsupp.mem_support_iff.mp hE)]
      · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hPE)]
        by_contra hne
        refine (show P.genericPoint ∉ C from hP) ?_
        simp only [C, Set.mem_iUnion, Finset.mem_filter]
        exact ⟨P, ⟨Finsupp.mem_support_iff.mpr (Ne.symm hne), hPE⟩,
          MMP.Flips.primeDivisor_genericPoint_mem_support P⟩
  · refine ⟨⟨E.supportᶜ, E.idealSheaf.support.isClosed.isOpen_compl⟩, hy,
      Or.inr fun P hP => DivisorWithCoeffs.coeff_single_of_ne ?_ _⟩
    rintro rfl
    exact hP (MMP.Flips.primeDivisor_genericPoint_mem_support E)

/-- Restricting to a component `E` of a reduced divisor `S` with pairwise disjoint components
ignores the other components: `(B + (S - E))|_E = B|_E`. -/
private theorem restrictPrimeDivisor_add_sub_single {X : Scheme.{u}} {S : Divisor X}
    (hS : MMP.Intersection.IsReducedEffective S) {E : MMP.Mori.PrimeDivisor X} (hE : E ∈ S.support)
    (hdisj : ∀ P ∈ S.support, P ≠ E → Disjoint E.support P.support) (B : QDivisor X) :
    (B + (Divisor.toQDivisor S - Finsupp.single E 1)).restrictPrimeDivisor E =
      B.restrictPrimeDivisor E := by
  refine restrict_add_of_forall_notMem _ _ _ fun P hP t => ?_
  obtain ⟨hPS, hPE⟩ := mem_support_and_ne_of_coeff_sub_single hS hE (Finsupp.mem_support_iff.mp hP)
  refine Set.disjoint_left.mp (hdisj P hPS hPE) ?_
  exact (Scheme.IdealSheafData.range_subschemeι E.idealSheaf).subset (Set.mem_range_self t)

/-! ### The components of a normal reduced divisor -/

/-- Two closed subsets agreeing on an affine open `U` have the same vanishing ideal on `U`. -/
private theorem vanishingIdeal_ideal_congr {X : Scheme.{u}} {Z Z' : TopologicalSpace.Closeds X}
    (U : X.affineOpens) (h : (Z : Set X) ∩ U = (Z' : Set X) ∩ U) :
    (Scheme.IdealSheafData.vanishingIdeal Z).ideal U =
      (Scheme.IdealSheafData.vanishingIdeal Z').ideal U := by
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal, Scheme.IdealSheafData.vanishingIdeal_ideal]
  congr 1
  ext x
  have hx : U.2.fromSpec x ∈ (U : Set X) := U.2.range_fromSpec ▸ Set.mem_range_self x
  exact ⟨fun h1 => ((Set.ext_iff.mp h _).mp ⟨h1, hx⟩).1,
    fun h1 => ((Set.ext_iff.mp h _).mpr ⟨h1, hx⟩).1⟩

/-- On an affine open `U` meeting no component of `S` other than `E`, the reduced subschemes `E`
and `Supp S` have the same ideal. -/
private theorem suppIdeal_ideal_eq_idealSheaf_ideal {X : Scheme.{u}} (S : Divisor X)
    {E : MMP.Mori.PrimeDivisor X} (hE : E ∈ S.support) (U : X.affineOpens)
    (hU : ∀ P ∈ S.support, P ≠ E → Disjoint (U : Set X) (P.support : Set X)) :
    S.suppIdeal.ideal U = E.idealSheaf.ideal U := by
  have := E.integral
  rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme E.idealSheaf _ rfl]
  refine vanishingIdeal_ideal_congr U ?_
  rw [DivisorWithCoeffs.coe_supp]
  ext x
  refine ⟨fun ⟨hx, hxU⟩ => ⟨?_, hxU⟩, fun ⟨hx, hxU⟩ => ⟨Set.mem_iUnion₂.mpr ⟨E, hE, hx⟩, hxU⟩⟩
  obtain ⟨P, hP, hxP⟩ := Set.mem_iUnion₂.mp hx
  by_contra hxE
  exact Set.disjoint_left.mp (hU P hP fun h => hxE (h ▸ hxP)) hxU hxP

/-- **The components of a normal reduced divisor are normal.** If the support of a divisor `S`
is a normal scheme and the component `E` of `S` meets no other component, then the integral
subscheme `E` is normal. -/
public theorem isNormal_subscheme_of_isNormal_suppScheme {X : Scheme.{u}} (S : Divisor X)
    [IsNormal S.suppScheme] {E : MMP.Mori.PrimeDivisor X} (hE : E ∈ S.support)
    (hdisj : ∀ P ∈ S.support, P ≠ E → Disjoint E.support P.support) :
    IsNormal E.idealSheaf.subscheme := by
  classical
  let C : Set X := ⋃ P ∈ S.support.filter (· ≠ E), P.support
  have hC : IsClosed C := isClosed_biUnion_finset fun P _ => P.idealSheaf.support.isClosed
  have hEC : Disjoint (E.support : Set X) C := by
    simp only [C, Set.disjoint_iUnion_right, Finset.mem_filter]
    exact fun P ⟨hP, hPE⟩ => hdisj P hP hPE
  have hideal (U : X.affineOpens) (hU : Disjoint (U : Set X) C) :
      S.suppIdeal.ideal U = E.idealSheaf.ideal U := by
    simp only [C, Set.disjoint_iUnion_right, Finset.mem_filter] at hU
    exact suppIdeal_ideal_eq_idealSheaf_ideal S hE U fun P hP hPE => hU P ⟨hP, hPE⟩
  have hS := ((isNormal_tfae S.suppScheme).out 1 2).mp ‹_›
  apply ((isNormal_tfae E.idealSheaf.subscheme).out 3 1).mp
  refine ⟨{U : X.affineOpens // Disjoint (U : Set X) C},
      fun U => ⟨E.idealSheaf.subschemeι ⁻¹ᵁ U.1.1, U.1.2.preimage _⟩, ?_, fun U => ?_⟩
  · refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.mpr fun y _ => ?_)
    have hy : E.idealSheaf.subschemeι y ∈ (E.support : Set X) := by
      rw [AlgebraicGeometry.PrimeDivisor.support, ← Scheme.IdealSheafData.range_subschemeι]
      exact Set.mem_range_self y
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUC⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.disjoint_left.mp hEC hy) hC.isOpen_compl
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨⟨⟨U, hU⟩, Set.subset_compl_iff_disjoint_right.mp hUC⟩, hyU⟩
  · let e1 := (E.idealSheaf.subschemeObjIso U.1).commRingCatIsoToRingEquiv
    let e2 := Ideal.quotEquivOfEq (hideal U.1 U.2).symm
    let e3 := (S.suppIdeal.subschemeObjIso U.1).commRingCatIsoToRingEquiv.symm
    exact IsNormalRing.congr (e1.trans (e2.trans e3)).symm
      (hS ⟨_, U.1.2.preimage S.suppIdeal.subschemeι⟩)

variable {k : Type u} [Field k]

/-- Each component `Sⱼ` of a reduced divisor `S` with normal support on a normal variety is a
normal variety. -/
public theorem isNormalVariety_component {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) (S : Divisor X) (hS : MMP.Intersection.IsReducedEffective S)
    [IsNormal S.suppScheme] (E : S.support) :
    IsNormalVariety k (E.1.idealSheaf.subschemeι ≫ sX) := by
  have := isNormal_subscheme_of_isNormal_suppScheme S E.2 fun P hP hPE =>
    DivisorWithCoeffs.pairwise_disjoint_support_of_isNormal_suppScheme sX hX S hS E.2 hP hPE.symm
  have := E.1.integral
  have := hX.1.toIsSeparated
  have := hX.1.toLocallyOfFiniteType
  have := hX.1.toQuasiCompact
  exact ⟨(isVariety_iff k _).mpr ⟨E.1.integral, inferInstance, inferInstance, inferInstance⟩,
    inferInstance⟩

/-- A reduced divisor is the sum of its components. -/
private theorem sum_single_support_eq {X : Scheme.{u}} {S : Divisor X}
    (hS : MMP.Intersection.IsReducedEffective S) :
    ∑ a : S.support, Finsupp.single a.1 (1 : ℤ) = S := by
  rw [Finset.sum_coe_sort S.support (fun P => Finsupp.single P (1 : ℤ))]
  conv_rhs => rw [← Finsupp.sum_single S]
  refine Finset.sum_congr rfl fun P hP => ?_
  congr 1
  exact ((hS P).resolve_left (Finsupp.mem_support_iff.mp hP)).symm

/-- **Adjunction on the components of `S`.** In the situation of Kollár–Mori 5.46, every component
`Sⱼ` of `S` has a canonical divisor of dimension `n = dim X - 1`, and `K_{Sⱼ} + B|_{Sⱼ}` is
`ℚ`-Cartier for every canonical divisor `K_{Sⱼ}` of dimension `n`. -/
public theorem exists_isCanonicalDivisor_and_isQCartier_restrictPrimeDivisor [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX (n + 1))
    (S : Divisor X) (hS : MMP.Intersection.IsReducedEffective S) [IsNormal S.suppScheme]
    (hSC : ∀ x ∈ S.supp, Order.coheight x = 2 → MMP.Flips.IsCartierAt S x)
    {B : QDivisor X} (hB : ∀ P ∈ S.support, B.coeff P = 0)
    (hKSB : (Divisor.toQDivisor K + Divisor.toQDivisor S + B).IsQCartier) (E : S.support) :
    haveI := (isNormalVariety_component hX S hS E).isLocallyNoetherian
    haveI := (isNormalVariety_component hX S hS E).isNormal
    (∃ KS : Divisor E.1.idealSheaf.subscheme,
      KS.IsCanonicalDivisor (E.1.idealSheaf.subschemeι ≫ sX) n) ∧
    ∀ KS : Divisor E.1.idealSheaf.subscheme,
      KS.IsCanonicalDivisor (E.1.idealSheaf.subschemeι ≫ sX) n →
      (Divisor.toQDivisor KS + B.restrictPrimeDivisor E.1).IsQCartier := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : QuasiCompact sX := hX.1.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : ∀ a : S.support, IsIntegral a.1.idealSheaf.subscheme := fun a => a.1.integral
  have : ∀ a : S.support, IsNormal a.1.idealSheaf.subscheme := fun a =>
    (isNormalVariety_component hX S hS a).isNormal
  have : ∀ a : S.support, IsLocallyNoetherian a.1.idealSheaf.subscheme := fun a =>
    (isNormalVariety_component hX S hS a).isLocallyNoetherian
  have : ∀ a : S.support, CompactSpace a.1.idealSheaf.subscheme := fun a =>
    QuasiCompact.compactSpace_of_compactSpace a.1.idealSheaf.subschemeι
  have hsum := sum_single_support_eq hS
  have hdim : topologicalKrullDim X = n + 1 := by
    rw [hK.topologicalKrullDim_eq]
    push_cast
    rfl
  have h := adjunction_restrict_of_isCartierAt_coheight_eq_two sX hX hdim
    (T := fun a : S.support => a.1.idealSheaf.subscheme)
    (fun a => a.1.idealSheaf.subschemeι) (fun a => a.1)
    (fun a => Scheme.IdealSheafData.range_subschemeι a.1.idealSheaf)
    (fun a b hab => DivisorWithCoeffs.pairwise_disjoint_support_of_isNormal_suppScheme sX hX S hS
      a.2 b.2 (Subtype.coe_ne_coe.mpr hab))
    (fun x h2 ⟨a, hx⟩ => by
      rw [hsum]
      exact hSC x (DivisorWithCoeffs.support_subset_supp (Finsupp.mem_support_iff.mp a.2) hx) h2)
    B (fun a => hB a.1 a.2) K hK (by rwa [hsum])
  refine ⟨?_, fun KS hKS => (h.2.2.2.2 E KS hKS).1⟩
  obtain ⟨ω, hω0, hωP⟩ := h.2.1
  obtain ⟨⟨ρ, hρ⟩, hρ'⟩ := (h.2.2.1 ω hω0 hωP).2 E
  exact ⟨_, (hρ' ρ hρ).1⟩

/-- **The pair `(S, B|_S)`** of Kollár–Mori 5.46: for a reduced divisor `S` with normal support,
Cartier in codimension two, on a normal variety `X` of dimension `n + 1`, and a `ℚ`-divisor `B`
without components in `S` with `K_X + S + B` `ℚ`-Cartier, the pair on `S` whose components are the
prime divisors of `S`, with boundary `B|_{Sⱼ}` on each component and a chosen canonical divisor
`K_{Sⱼ}` of dimension `n`. The components are pairwise disjoint normal varieties
(`MMP.Mori.DivisorWithCoeffs.pairwise_disjoint_support_of_isNormal_suppScheme`,
`MMP.Mori.isNormalVariety_component`), and `K_{Sⱼ}` exists and `K_{Sⱼ} + B|_{Sⱼ}` is `ℚ`-Cartier
by adjunction (`MMP.Mori.exists_isCanonicalDivisor_and_isQCartier_restrictPrimeDivisor`). -/
public def PairOnNormalDivisor.ofRestrict [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX (n + 1))
    (S : Divisor X) (hS : MMP.Intersection.IsReducedEffective S) [IsNormal S.suppScheme]
    (hSC : ∀ x ∈ S.supp, Order.coheight x = 2 → MMP.Flips.IsCartierAt S x)
    {B : QDivisor X} (hB : ∀ P ∈ S.support, B.coeff P = 0)
    (hKSB : (Divisor.toQDivisor K + Divisor.toQDivisor S + B).IsQCartier) :
    PairOnNormalDivisor sX where
  components := S.support
  pairwise_disjoint := DivisorWithCoeffs.pairwise_disjoint_support_of_isNormal_suppScheme sX hX S hS
  isNormalVariety := isNormalVariety_component hX S hS
  dim := n
  K E := (exists_isCanonicalDivisor_and_isQCartier_restrictPrimeDivisor hX hK S hS hSC hB hKSB
    E).1.choose
  Θ E := B.restrictPrimeDivisor E.1
  isCanonicalDivisor E := (exists_isCanonicalDivisor_and_isQCartier_restrictPrimeDivisor hX hK S hS
    hSC hB hKSB E).1.choose_spec
  isQCartier E :=
    (exists_isCanonicalDivisor_and_isQCartier_restrictPrimeDivisor hX hK S hS hSC hB hKSB E).2 _
      (exists_isCanonicalDivisor_and_isQCartier_restrictPrimeDivisor hX hK S hS hSC hB hKSB
        E).1.choose_spec

section ofRestrict

variable [CharZero k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) {n : ℕ} {K : Divisor X}
  (hK : K.IsCanonicalDivisor sX (n + 1)) (S : Divisor X)
  (hS : MMP.Intersection.IsReducedEffective S)
  [IsNormal S.suppScheme] (hSC : ∀ x ∈ S.supp, Order.coheight x = 2 → MMP.Flips.IsCartierAt S x)
  {B : QDivisor X} (hB : ∀ P ∈ S.support, B.coeff P = 0)
  (hKSB : (Divisor.toQDivisor K + Divisor.toQDivisor S + B).IsQCartier)

@[simp]
public theorem PairOnNormalDivisor.ofRestrict_components :
    (PairOnNormalDivisor.ofRestrict hX hK S hS hSC hB hKSB).components = S.support :=
  rfl

@[simp]
public theorem PairOnNormalDivisor.ofRestrict_dim :
    (PairOnNormalDivisor.ofRestrict hX hK S hS hSC hB hKSB).dim = n :=
  rfl

@[simp]
public theorem PairOnNormalDivisor.ofRestrict_Θ
    (E : (PairOnNormalDivisor.ofRestrict hX hK S hS hSC hB hKSB).components) :
    (PairOnNormalDivisor.ofRestrict hX hK S hS hSC hB hKSB).Θ E = B.restrictPrimeDivisor E.1 :=
  rfl

end ofRestrict

/-! ### The inequality -/

/-- The inequality `discrep(center ⊆ Z, X, S + B) ≤ totaldiscrep(center ⊆ Z, S, B|_S)` for every
pair `T` on `S` whose components are the prime divisors of `S`, of dimension `n`, with boundary
`B|_{Sⱼ}` on each component, whatever its canonical divisors `K_{Sⱼ}`. -/
public theorem discrepCenterIn_le_totalDiscrepCenterIn_of_components_eq
    [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX (n + 1))
    (S : Divisor X) (hS : MMP.Intersection.IsReducedEffective S)
    (hSC : ∀ x ∈ S.supp, Order.coheight x = 2 → MMP.Flips.IsCartierAt S x)
    (Z : Set X) {B : QDivisor X} (hB : ∀ P ∈ S.support, B.coeff P = 0)
    (hKSB : (Divisor.toQDivisor K + Divisor.toQDivisor S + B).IsQCartier)
    (T : PairOnNormalDivisor sX) (hTc : T.components = S.support) (hTd : T.dim = n)
    (hTΘ : ∀ E, T.Θ E = B.restrictPrimeDivisor E.1) :
    discrepCenterIn sX (n + 1) K (Divisor.toQDivisor S + B) Z ≤ T.totalDiscrepCenterIn Z := by
  subst hTd
  refine le_iInf fun E => le_sInf ?_
  rintro _ ⟨F, a, hF, hFZ, ha, rfl⟩
  have hE : E.1 ∈ S.support := hTc ▸ E.2
  have hdisj : ∀ P ∈ S.support, P ≠ E.1 → Disjoint E.1.support P.support := fun P hP hPE =>
    T.pairwise_disjoint E.2 (hTc ▸ hP) hPE.symm
  have hΔ : Finsupp.single E.1 1 + (B + (Divisor.toQDivisor S - Finsupp.single E.1 1)) =
      Divisor.toQDivisor S + B := by abel
  have hBj : (B + (Divisor.toQDivisor S - Finsupp.single E.1 1)).coeff E.1 = 0 := by
    rw [DivisorWithCoeffs.coeff_add, hB E.1 hE, coeff_toQDivisor_sub_single_self hS hE, add_zero]
  obtain ⟨G, hG, hGc, hGa⟩ := exists_isExceptional_isDiscrepancy_iff_restrictPrimeDivisor hX hK
    E.1 (T.isNormalVariety E)
    (fun x hx h2 => isCartierAt_single_of_isCartierAt hS hE hdisj
      (hSC x (DivisorWithCoeffs.support_subset_supp (Finsupp.mem_support_iff.mp hE) hx) h2))
    hBj (by rwa [add_assoc, hΔ, ← add_assoc]) (T.isCanonicalDivisor E) F hF
  refine sInf_le ⟨G, a, hG, hGc ▸ Set.image_subset_iff.mpr hFZ, ?_, rfl⟩
  rwa [← hΔ, hGa, restrictPrimeDivisor_add_sub_single hS hE hdisj, ← hTΘ]

/-- **Kollár–Mori 5.46, first inequality.** Let `X` be a normal variety of dimension `n + 1` with
canonical divisor `K`, `S` a reduced divisor with normal support, Cartier at every point of `S`
of codimension two in `X`, `Z ⊆ Supp S` closed, and `B` a `ℚ`-divisor with no component in `S`
such that `K + S + B` is `ℚ`-Cartier. Then for the pair `(S, B|_S)` on `S`,
`discrep(center ⊆ Z, X, S + B) ≤ totaldiscrep(center ⊆ Z, S, B|_S)`. -/
@[mmp "prop_km5b_adjunction_totaldiscrep_inequality"]
public theorem discrepCenterIn_le_totalDiscrepCenterIn_restrict
    [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX (n + 1))
    (S : Divisor X) (hS : MMP.Intersection.IsReducedEffective S) [hSn : IsNormal S.suppScheme]
    (hSC : ∀ x ∈ S.supp, Order.coheight x = 2 → MMP.Flips.IsCartierAt S x)
    {Z : Set X} (hZ : IsClosed Z) (hZS : Z ⊆ S.supp)
    {B : QDivisor X} (hB : ∀ P ∈ S.support, B.coeff P = 0)
    (hKSB : (Divisor.toQDivisor K + Divisor.toQDivisor S + B).IsQCartier) :
    discrepCenterIn sX (n + 1) K (Divisor.toQDivisor S + B) Z ≤
      (PairOnNormalDivisor.ofRestrict hX hK S hS hSC hB hKSB).totalDiscrepCenterIn Z :=
  discrepCenterIn_le_totalDiscrepCenterIn_of_components_eq hX hK S hS hSC Z hB hKSB _ rfl rfl
    fun _ => rfl

end MMP.Mori

end
