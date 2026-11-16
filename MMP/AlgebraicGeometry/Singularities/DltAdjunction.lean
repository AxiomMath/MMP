module

public import MMP.AlgebraicGeometry.Singularities.DltFloorComponentsNormal
public import MMP.AlgebraicGeometry.Singularities.Adjunction.DiscrepancyOverDivisor
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy

/-!
# Adjunction for dlt pairs

Let `X` be a normal variety of dimension `n ≥ 2` over an algebraically closed field of
characteristic zero, `S ⊆ X` a prime divisor which is Cartier at every codimension-two point of
`X` lying on `S`, and `B` an effective `ℚ`-divisor without component `S`. If `(X, S + B)` is dlt,
then `S` is normal and `(S, B|_S)` is dlt, for every canonical divisor `K_S` of `S`. Here `S`
carries its reduced (integral) scheme structure and `B|_S` is the restriction of `B` to the
prime divisor `S`, whose coefficient at a prime divisor `Q` of `S` is
`∑ᵢ bᵢ · length(𝒪_{S,Q}/I_{Bᵢ}𝒪_{S,Q})`.

## Main results

* `MMP.Mori.IsDltPair.isDltPair_restrictPrimeDivisor`: adjunction for dlt pairs.

## Implementation notes

`S` is integral (`AlgebraicGeometry.PrimeDivisor.integral`) and locally Noetherian, as a closed
subscheme of `X`; these instances are supplied in the statement.
Normality of `S` is part of the conclusion, since the dlt property of `(S, B|_S)` is only
meaningful on a normal scheme. Being dlt does not depend on the canonical divisor chosen, so the
conclusion is asserted for every canonical divisor `K_S` of `S` of dimension `n - 1`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 5.59
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori

universe u

/-- In a domain, a nonzero prime contained in a prime of height one is equal to it. -/
private lemma eq_of_le_of_height_eq_one {A : Type*} [CommRing A] [IsDomain A] {I q : Ideal A}
    [I.IsPrime] [q.IsPrime] (hI : I ≠ ⊥) (hle : I ≤ q) (hq : q.height = 1) : I = q := by
  by_contra hne
  have : q.FiniteHeight := Ideal.finiteHeight_iff_lt.mpr (Or.inr (by simp [hq]))
  have h1 := Ideal.height_strict_mono_of_isPrime_of_isPrime (lt_of_le_of_ne hle hne)
  rw [hq, ENat.lt_one_iff_eq_zero, Ideal.height_eq_zero_iff_eq_bot] at h1
  exact hI h1

/-- Let `J` be an ideal sheaf contained in the ideal of a prime divisor `P`, and `y ∈ P` a point
at which `J` is cut out by a member of a regular system of parameters. Then `P` and `J` have the
same ideal at `y`. -/
private lemma stalk_idealSheaf_eq_of_le {X : Scheme.{u}} [IsLocallyNoetherian X]
    (P : MMP.Mori.PrimeDivisor X) {J : X.IdealSheafData} (hle : J ≤ P.idealSheaf) {y : X}
    (hy : y ∈ P.support) {m : ℕ} {w : Fin m → X.presheaf.stalk y}
    (hw : MMP.Mori.IsRegularSystemOfParameters w) (j0 : Fin m)
    (hst : AlgebraicGeometry.IdealSheafData.stalk J y = Ideal.span {w j0}) :
    AlgebraicGeometry.IdealSheafData.stalk P.idealSheaf y =
      AlgebraicGeometry.IdealSheafData.stalk J y := by
  obtain ⟨q, -, hPq, hq1⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support P hy
  have := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hw
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk y)
  have := MMP.Resolution.isPrime_span_singleton_of_isRegularSystemOfParameters hw j0
  rw [hPq, hst]
  refine (eq_of_le_of_height_eq_one ?_ ?_ hq1).symm
  · exact mt Ideal.span_singleton_eq_bot.mp
      (MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hw j0)
  · rw [← hst, ← hPq]
    exact MMP.Resolution.stalk_le_stalk_of_le hle y

/-- An irreducible component of the support of a prime divisor `F` does not lie in the support
of a different prime divisor `E`. -/
private lemma not_subset_support_of_mem_componentsOf {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    {F E : MMP.Mori.PrimeDivisor Y} (hFE : F ≠ E) {W : Set Y}
    (hW : W ∈ MMP.Resolution.componentsOf (F.idealSheaf.support : Set Y)) :
    ¬ W ⊆ E.idealSheaf.support := by
  intro hWE
  have hcl : (F.idealSheaf.support : Set Y) = closure {F.genericPoint} :=
    AlgebraicGeometry.PrimeDivisor.support_eq_closure F
  have hirr : IsIrreducible (F.idealSheaf.support : Set Y) := by
    rw [hcl]
    exact isIrreducible_singleton.closure
  have hW' : Maximal (fun W' : Set Y => IsIrreducible W' ∧ W' ⊆ F.idealSheaf.support) W := hW
  have hWF : W = F.idealSheaf.support := (hW'.eq_of_ge ⟨hirr, le_rfl⟩ hW'.prop.2).symm
  have hmem : F.genericPoint ∈ E.support := hWE (by rw [hWF, hcl]; exact subset_closure rfl)
  exact hFE (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (E.eq_genericPoint_of_mem_support hmem F.coheight_genericPoint))

/-- If the image of the generic point of a prime divisor `P` lies in the support of `E`, then so
does the image of every point of `P`. -/
private lemma mem_support_comap_of_genericPoint_mem {Z Y : Scheme.{u}} [IsLocallyNoetherian Z]
    (f : Z ⟶ Y) (P : MMP.Mori.PrimeDivisor Z) (E : MMP.Mori.PrimeDivisor Y)
    (hP : f P.genericPoint ∈ E.support) {y : Z} (hy : y ∈ P.support) :
    y ∈ (E.idealSheaf.comap f).support := by
  have hsp : P.genericPoint ⤳ y := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hy
  exact hsp.mem_closed (E.idealSheaf.comap f).support.isClosed
    ((MMP.Resolution.mem_support_comap_iff _ _ _).2 hP)

/-- If `F + ∑_{E ∈ D} E` is snc and `F ∉ D`, then `F` meets the members of `D` with simple normal
crossings. -/
private lemma hasSNCWith_of_isSNC {k : Type u} [Field k] {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] {F : MMP.Mori.PrimeDivisor Y}
    {D : Finset (MMP.Mori.PrimeDivisor Y)} (hF : F ∉ D)
    (hsnc : MMP.Mori.DivisorWithCoeffs.IsSNC sY
      (Finsupp.single F (1 : ℤ) + ∑ E ∈ D, Finsupp.single E (1 : ℤ))) :
    MMP.Resolution.HasSNCWith (fun E : D => E.1.idealSheaf) F.idealSheaf := by
  classical
  set T : MMP.Mori.Divisor Y := ∑ E ∈ D, Finsupp.single E (1 : ℤ) with hT
  have hTapp : ∀ E, T E = if E ∈ D then 1 else 0 := by
    intro E
    simp [hT, Finsupp.finset_sum_apply, Finsupp.single_apply]
  have hDapp : ∀ E, (Finsupp.single F (1 : ℤ) + T) E =
      (if E = F then 1 else 0) + (if E ∈ D then 1 else 0) := by
    intro E
    rw [Finsupp.add_apply, hTapp, Finsupp.single_apply]
    simp [eq_comm]
  have hFD : F ∈ (Finsupp.single F (1 : ℤ) + T).support := by
    rw [Finsupp.mem_support_iff, hDapp, if_pos rfl, if_neg hF]
    exact one_ne_zero
  have hSD : ∀ E ∈ D, E ∈ (Finsupp.single F (1 : ℤ) + T).support := by
    intro E hE
    rw [Finsupp.mem_support_iff, hDapp, if_pos hE, if_neg (fun h : E = F => hF (h ▸ hE))]
    exact one_ne_zero
  intro x hx
  obtain ⟨n, z, j, hz, hj, hI⟩ := hsnc.2 x
  have hxF : x ∈ F.support := hx
  let c : {i : D // x ∈ i.1.idealSheaf.support} → Fin n :=
    fun i => j ⟨i.1.1, hSD i.1.1 i.1.2, i.2⟩
  refine ⟨n, z, c, {j ⟨F, hFD, hxF⟩}, hz, fun i => hI ⟨i.1.1, hSD i.1.1 i.1.2, i.2⟩,
    fun a b hab => ?_, ?_⟩
  · have := congrArg Subtype.val (hj hab)
    exact Subtype.ext (Subtype.ext this)
  · rw [hI ⟨F, hFD, hxF⟩]
    simp

open MMP.Mori.DivisorWithCoeffs in
/-- **Restriction of an snc divisor to a component.** Let `Y` be locally of finite type over a
perfect field, `F` a prime divisor of `Y` and `D` a finite set of prime divisors not containing
`F` such that `F + ∑_{E ∈ D} E` is snc. Then every divisor on `F` whose components lie in some
`E ∩ F`, `E ∈ D`, is snc. The closed subscheme `F` is given by any ideal sheaf `I` equal to the
ideal of `F`. -/
private theorem isSNC_of_forall_mem_support {k : Type u} [Field k] [PerfectField k]
    {Y : Scheme.{u}} [IsLocallyNoetherian Y] (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY]
    (F : MMP.Mori.PrimeDivisor Y) (D : Finset (MMP.Mori.PrimeDivisor Y)) (hF : F ∉ D)
    (hsnc : IsSNC sY (Finsupp.single F (1 : ℤ) + ∑ E ∈ D, Finsupp.single E (1 : ℤ)))
    (I : Y.IdealSheafData) (hI : F.idealSheaf = I) {R : Type*} [Zero R]
    (A : MMP.Mori.DivisorWithCoeffs R I.subscheme)
    (hexE : ∀ P ∈ A.support, ∃ E ∈ D, I.subschemeι P.genericPoint ∈ E.support) :
    IsSNC (I.subschemeι ≫ sY) A := by
  classical
  subst hI
  set ι := F.idealSheaf.subschemeι with hι
  let Efam : D → Y.IdealSheafData := fun E => E.1.idealSheaf
  have hZ : MMP.Resolution.HasSNCWith Efam F.idealSheaf := hasSNCWith_of_isSNC sY hF hsnc
  have hcoord := MMP.Resolution.exists_coordinates_comap_subschemeι_of_hasSNCWith hZ
    fun i _ hW => not_subset_support_of_mem_componentsOf (fun h : F = i.1 => hF (h ▸ i.2)) hW
  have : IsLocallyNoetherian F.idealSheaf.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (ι ≫ sY)
  have hDc : ∀ i, ∀ y ∈ ((Efam i).comap ι).support, ∃ (m : ℕ)
      (w : Fin m → F.idealSheaf.subscheme.presheaf.stalk y) (j : Fin m),
        MMP.Mori.IsRegularSystemOfParameters w ∧
        AlgebraicGeometry.IdealSheafData.stalk ((Efam i).comap ι) y = Ideal.span {w j} := by
    intro i y hy
    obtain ⟨n, z, c, hz, hc, -⟩ := hcoord y
    exact ⟨n, z, c ⟨i, hy⟩, hz, hc ⟨i, hy⟩⟩
  have hmemc : ∀ (P : MMP.Mori.PrimeDivisor F.idealSheaf.subscheme) (i : D),
      ι P.genericPoint ∈ i.1.support → ∀ y ∈ P.support, y ∈ ((Efam i).comap ι).support :=
    fun P i hPi _ hy => mem_support_comap_of_genericPoint_mem ι P i.1 hPi hy
  have hkey : ∀ (P : MMP.Mori.PrimeDivisor F.idealSheaf.subscheme) (i : D),
      ι P.genericPoint ∈ i.1.support → ∀ y ∈ P.support,
        AlgebraicGeometry.IdealSheafData.stalk P.idealSheaf y =
          AlgebraicGeometry.IdealSheafData.stalk ((Efam i).comap ι) y := by
    intro P i hPi y hy
    obtain ⟨m, w, j0, hw, hst⟩ := hDc i y (hmemc P i hPi y hy)
    refine stalk_idealSheaf_eq_of_le P ?_ hy hw j0 hst
    rw [← MMP.Intersection.vanishingIdeal_support_idealSheaf P]
    exact Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp fun x hx => hmemc P i hPi x hx
  choose E hED hEP using hexE
  refine ⟨fun P hP => ?_, fun y => ?_⟩
  · refine MMP.Resolution.isSmoothScheme_subscheme_of_stalk_eq_span_parameter (ι ≫ sY)
      P.idealSheaf fun y hy => ?_
    rw [hkey P ⟨E P hP, hED P hP⟩ (hEP P hP) y hy]
    exact hDc _ y (hmemc P _ (hEP P hP) y hy)
  · obtain ⟨m, w, c', hw, hc', hinj⟩ := hcoord y
    refine ⟨m, w, fun P => c' ⟨⟨E P.1 P.2.1, hED _ _⟩, hmemc P.1 _ (hEP _ _) y P.2.2⟩, hw,
      fun P P' h => ?_, fun P => ?_⟩
    · apply Subtype.ext
      apply MMP.Intersection.eq_of_stalk_idealSheaf_eq P.2.2 P'.2.2
      rw [hkey P.1 ⟨E P.1 P.2.1, hED _ P.2.1⟩ (hEP P.1 P.2.1) y P.2.2,
        hkey P'.1 ⟨E P'.1 P'.2.1, hED _ P'.2.1⟩ (hEP P'.1 P'.2.1) y P'.2.2]
      exact congrArg (fun i => AlgebraicGeometry.IdealSheafData.stalk ((Efam i).comap ι) y)
        (congrArg Subtype.val (hinj h))
    · rw [hkey P.1 ⟨E P.1 P.2.1, hED _ P.2.1⟩ (hEP P.1 P.2.1) y P.2.2]
      exact hc' ⟨⟨E P.1 P.2.1, hED _ P.2.1⟩, hmemc P.1 _ (hEP P.1 P.2.1) y P.2.2⟩

open MMP.Threefold.Mori.OpenRestriction in
/-- Being snc after restriction along open immersions depends only on the image: if the
restriction of `D` along an open immersion `j₂` is snc, so is its restriction along any open
immersion `j₁` whose image lies in that of `j₂`. -/
private theorem isSNC_comapDomain_of_range_subset {R : Type*} [Zero R] {W Y V₁ V₂ : Scheme.{u}}
    (g : W ⟶ Y)
    [∀ E : MMP.Mori.PrimeDivisor W, LocallyOfFinitePresentation (E.idealSheaf.subschemeι ≫ g)]
    (j₁ : V₁ ⟶ W) (j₂ : V₂ ⟶ W) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (hr : Set.range j₁ ⊆ Set.range j₂) (D : MMP.Mori.DivisorWithCoeffs R W)
    (h : MMP.Mori.DivisorWithCoeffs.IsSNC (j₂ ≫ g)
      (Finsupp.comapDomain (OpenWeilRestriction.primeDivisorMap j₂) D
        (OpenWeilRestriction.primeDivisorMap_injective j₂).injOn)) :
    MMP.Mori.DivisorWithCoeffs.IsSNC (j₁ ≫ g)
      (Finsupp.comapDomain (OpenWeilRestriction.primeDivisorMap j₁) D
        (OpenWeilRestriction.primeDivisorMap_injective j₁).injOn) := by
  refine ⟨fun E₁ hE₁ => ?_, fun x => ?_⟩
  · have hDE : D (OpenWeilRestriction.primeDivisorMap j₁ E₁) ≠ 0 := by
      have := Finsupp.mem_support_iff.mp hE₁
      exact this
    refine (isSmoothScheme_comap_iff j₁ g _ E₁.idealSheaf
      (idealSheaf_comap_primeDivisorMap j₁ E₁)).mpr ?_
    intro z hz
    obtain ⟨v, hv⟩ := hr hz
    have hEsupp : (OpenWeilRestriction.primeDivisorMap j₁ E₁).idealSheaf.subschemeι z ∈
        (OpenWeilRestriction.primeDivisorMap j₁ E₁).support := by
      have hr' : (OpenWeilRestriction.primeDivisorMap j₁ E₁).idealSheaf.subschemeι z ∈
          Set.range (OpenWeilRestriction.primeDivisorMap j₁ E₁).idealSheaf.subschemeι := ⟨z, rfl⟩
      rwa [Scheme.IdealSheafData.range_subschemeι] at hr'
    obtain ⟨E₂, hE₂⟩ := exists_primeDivisorMap_eq_of_mem_support j₂ _ v (by rw [hv]; exact hEsupp)
    have hE₂supp : E₂ ∈ (Finsupp.comapDomain (OpenWeilRestriction.primeDivisorMap j₂) D
        (OpenWeilRestriction.primeDivisorMap_injective j₂).injOn).support := by
      rw [Finsupp.mem_support_iff, Finsupp.comapDomain_apply, hE₂]
      exact hDE
    have := (isSmoothScheme_comap_iff j₂ g (OpenWeilRestriction.primeDivisorMap j₁ E₁).idealSheaf
      E₂.idealSheaf (by rw [← hE₂]; exact idealSheaf_comap_primeDivisorMap _ E₂)).mp
      (h.1 E₂ hE₂supp)
    exact this z ⟨v, hv⟩
  · obtain ⟨v, hv⟩ := hr ⟨x, rfl⟩
    have h2 : SNCStalk D (j₂ v) := (sncStalk_restrict_iff j₂ D v).mp (h.2 v)
    rw [hv] at h2
    exact (sncStalk_restrict_iff j₁ D x).mpr h2

/-- The boundary `S + B` has coefficient `1` along `S` when `S` is not a component of `B`. -/
private lemma coeff_toQDivisor_single_add_self {X : Scheme.{u}} (S : MMP.Mori.PrimeDivisor X)
    {B : MMP.Mori.QDivisor X} (hBS : B.coeff S = 0) :
    (MMP.Mori.Divisor.toQDivisor (Finsupp.single S (1 : ℤ)) + B).coeff S = 1 := by
  rw [MMP.Threefold.Resolution.toQDivisor_single, MMP.Mori.DivisorWithCoeffs.coeff_add,
    MMP.Mori.DivisorWithCoeffs.coeff_single_self, hBS]
  simp

/-- **Divisors over `S` are realised over `X`.** Let `S` be a normal prime divisor of the normal
variety `X`, Cartier at the codimension-two points of `X` on it, and `B` a `ℚ`-divisor without
component `S` with `K_X + S + B` `ℚ`-Cartier. Every divisor `F` over `S` of discrepancy `a` with
respect to `(S, B|_S)` is realised by an exceptional divisor over `X` with center the image of
that of `F` and discrepancy `a` with respect to `(X, S + B)`. -/
private theorem exists_isExceptional_isDiscrepancy_of_isDiscrepancy_restrictPrimeDivisor
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsNormalVariety k sX)
    {n : ℕ} {K : MMP.Mori.Divisor X} (hK : K.IsCanonicalDivisor sX (n + 1))
    (S : MMP.Mori.PrimeDivisor X)
    (hS : MMP.Mori.IsNormalVariety k (S.idealSheaf.subschemeι ≫ sX))
    [IsIntegral S.idealSheaf.subscheme] [IsLocallyNoetherian S.idealSheaf.subscheme]
    [IsNormal S.idealSheaf.subscheme]
    (hSC : ∀ x ∈ S.support, Order.coheight x = 2 →
      MMP.Flips.IsCartierAt (Finsupp.single S 1) x)
    {B : MMP.Mori.QDivisor X} (hBS : B.coeff S = 0)
    (hKSB : (MMP.Mori.Divisor.toQDivisor K + Finsupp.single S 1 + B).IsQCartier)
    {KS : MMP.Mori.Divisor S.idealSheaf.subscheme}
    (hKS : KS.IsCanonicalDivisor (S.idealSheaf.subschemeι ≫ sX) n)
    (F : MMP.Mori.DivisorOver k (S.idealSheaf.subschemeι ≫ sX)) {a : ℚ}
    (ha : MMP.Mori.IsDiscrepancy (S.idealSheaf.subschemeι ≫ sX) n KS
      (B.restrictPrimeDivisor S) F a) :
    ∃ G : MMP.Mori.DivisorOver k sX, G.IsExceptional ∧
      (G.center : Set X) = S.idealSheaf.subschemeι '' (F.center : Set S.idealSheaf.subscheme) ∧
      MMP.Mori.IsDiscrepancy sX (n + 1) K
        (MMP.Mori.Divisor.toQDivisor (Finsupp.single S 1) + B) G a := by
  have hreal := MMP.Mori.exists_isExceptional_isDiscrepancy_iff_restrictPrimeDivisor hX hK S hS
    hSC hBS hKSB hKS
  rw [MMP.Threefold.Resolution.toQDivisor_single, Int.cast_one]
  by_cases hF : F.IsExceptional
  · obtain ⟨G, hG, hGc, hGa⟩ := hreal F hF.isExceptionalOrPrimeDivisor
    exact ⟨G, hG, hGc, (hGa a).mpr ha⟩
  obtain ⟨Q, hv⟩ := MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hS F hF
  have hη := MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hS.1 hv
  have ha' : MMP.Mori.IsDiscrepancy (S.idealSheaf.subschemeι ≫ sX) n KS
      (B.restrictPrimeDivisor S) (MMP.Mori.DivisorOver.ofPrimeDivisor k hS Q) a := by
    obtain ⟨hX', hK', m, hm, hC, V, hV, τ, hτ, hmτ⟩ := ha
    refine ⟨hX', hK', m, hm, hC, V, hη ▸ hV, τ, hτ, ?_⟩
    rw [hmτ, MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hS
      hKS.topologicalKrullDim_eq hv τ]
  obtain ⟨G, hG, hGc, hGa⟩ :=
    hreal _ (MMP.Mori.DivisorOver.isExceptionalOrPrimeDivisor_ofPrimeDivisor hS Q)
  refine ⟨G, hG, ?_, (hGa a).mpr ha'⟩
  rw [hGc, MMP.Mori.DivisorOver.center_eq_closure_genericPoint,
    MMP.Mori.DivisorOver.center_eq_closure_genericPoint, hη]

/-- If a boundary `Δ` with `S` among its components is snc on an open `U`, then `S ∩ U` lies in
the smooth locus of `S`. -/
private theorem preimage_le_smoothLocus_of_isSNC {k : Type} [Field k] {X : Scheme.{0}}
    [IsLocallyNoetherian X] (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    (S : MMP.Mori.PrimeDivisor X) {Δ : MMP.Mori.QDivisor X} (hΔS : Δ.coeff S ≠ 0) {U : X.Opens}
    (hsnc : (Δ.restrictOpen U).IsSNC (U.ι ≫ sX)) :
    S.idealSheaf.subschemeι ⁻¹ᵁ U ≤ MMP.Mori.smoothLocus (S.idealSheaf.subschemeι ≫ sX) := by
  intro z hz
  have hzS : S.idealSheaf.subschemeι z ∈ S.support := by
    have hr : S.idealSheaf.subschemeι z ∈ Set.range S.idealSheaf.subschemeι := ⟨z, rfl⟩
    rwa [Scheme.IdealSheafData.range_subschemeι] at hr
  obtain ⟨SU, hSU⟩ := MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support
    U.ι S ⟨_, hz⟩ hzS
  have hSUsupp : SU ∈ (Δ.restrictOpen U).support := by
    rw [Finsupp.mem_support_iff]
    change Δ.coeff (OpenWeilRestriction.primeDivisorMap U.ι SU) ≠ 0
    rwa [hSU]
  rw [MMP.Mori.smoothLocus_eq_smoothLocus]
  exact (MMP.Threefold.Mori.OpenRestriction.isSmoothScheme_comap_iff U.ι sX S.idealSheaf
    SU.idealSheaf (by
      rw [← hSU]
      exact MMP.Threefold.Mori.OpenRestriction.idealSheaf_comap_primeDivisorMap U.ι SU)).mp
    (hsnc.1 SU hSUsupp) z ⟨⟨_, hz⟩, rfl⟩

/-- If `S + B` is snc on an open `U`, with `B` effective without component `S`, then so is the
reduced divisor `S|_U + ∑ E` over the components `E` of `B|_U`. -/
private lemma isSNC_single_add_sum_support_restrictOpen {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) {S : MMP.Mori.PrimeDivisor X}
    {B : MMP.Mori.QDivisor X} (hB : 0 ≤ B) (hBS : B.coeff S = 0) {U : X.Opens}
    (hsnc : ((MMP.Mori.Divisor.toQDivisor (Finsupp.single S (1 : ℤ)) + B).restrictOpen U).IsSNC
      (U.ι ≫ sX)) {SU : MMP.Mori.PrimeDivisor U}
    (hSU : OpenWeilRestriction.primeDivisorMap U.ι SU = S) :
    MMP.Mori.DivisorWithCoeffs.IsSNC (U.ι ≫ sX) (Finsupp.single SU (1 : ℤ) +
      ∑ E ∈ (MMP.Mori.DivisorWithCoeffs.restrictOpen U B).support, Finsupp.single E (1 : ℤ)) := by
  classical
  refine hsnc.of_support_subset fun G hG => ?_
  rw [Finsupp.mem_support_iff] at hG ⊢
  change (MMP.Mori.Divisor.toQDivisor (Finsupp.single S (1 : ℤ)) + B).coeff
    (OpenWeilRestriction.primeDivisorMap U.ι G) ≠ 0
  by_cases hGS : G = SU
  · subst hGS
    rw [hSU, coeff_toQDivisor_single_add_self S hBS]
    exact one_ne_zero
  have hG𝓔 : G ∈ (MMP.Mori.DivisorWithCoeffs.restrictOpen U B).support := by
    by_contra hc
    apply hG
    simp [Finsupp.finset_sum_apply, Finsupp.single_apply, Ne.symm hGS, hc]
  have hBG : 0 < B (OpenWeilRestriction.primeDivisorMap U.ι G) :=
    lt_of_le_of_ne (hB _) (Ne.symm (by have := Finsupp.mem_support_iff.mp hG𝓔; exact this))
  have h0 : (0 : ℚ) ≤ Finsupp.single S (1 : ℚ) (OpenWeilRestriction.primeDivisorMap U.ι G) := by
    rw [Finsupp.single_apply]
    split_ifs <;> norm_num
  rw [MMP.Threefold.Resolution.toQDivisor_single, Int.cast_one,
    MMP.Mori.DivisorWithCoeffs.coeff_add]
  change Finsupp.single S (1 : ℚ) (OpenWeilRestriction.primeDivisorMap U.ι G) +
    B (OpenWeilRestriction.primeDivisorMap U.ι G) ≠ 0
  exact (add_pos_of_nonneg_of_pos h0 hBG).ne'

/-- A component `P` of `B|_S` on `S ∩ U` lies on a component of `B|_U`. -/
private lemma exists_mem_support_restrictOpen_of_coeff_ne_zero {X : Scheme.{0}}
    [IsIntegral X] [IsNoetherian X] (S : MMP.Mori.PrimeDivisor X)
    [IsIntegral S.idealSheaf.subscheme] [IsLocallyNoetherian S.idealSheaf.subscheme]
    {B : MMP.Mori.QDivisor X} (hBS : B.coeff S = 0) {U : X.Opens}
    {kk : (S.idealSheaf.comap U.ι).subscheme ⟶ S.idealSheaf.subscheme} [IsOpenImmersion kk]
    (hcomm : (S.idealSheaf.comap U.ι).subschemeι ≫ U.ι = kk ≫ S.idealSheaf.subschemeι)
    {P : MMP.Mori.PrimeDivisor (S.idealSheaf.comap U.ι).subscheme}
    (hP : (B.restrictPrimeDivisor S).coeff (OpenWeilRestriction.primeDivisorMap kk P) ≠ 0) :
    ∃ E ∈ (MMP.Mori.DivisorWithCoeffs.restrictOpen U B).support,
      (S.idealSheaf.comap U.ι).subschemeι P.genericPoint ∈ E.support := by
  classical
  rw [MMP.Mori.DivisorWithCoeffs.coeff_restrictPrimeDivisor _ S hBS] at hP
  obtain ⟨E, hE, hEne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hP
  have hmem : S.idealSheaf.subschemeι (OpenWeilRestriction.primeDivisorMap kk P).genericPoint ∈
      E.support := by
    by_contra hc
    exact hEne (by
      dsimp only
      rw [MMP.Mori.PrimeDivisor.intersectionLength_eq_zero_of_notMem _ E hc, zero_smul])
  have hy : U.ι ((S.idealSheaf.comap U.ι).subschemeι P.genericPoint) ∈ E.support := by
    have := congrArg (fun f => f P.genericPoint) hcomm
    simp only [Scheme.Hom.comp_apply] at this
    rw [this]
    have hg : (OpenWeilRestriction.primeDivisorMap kk P).genericPoint = kk P.genericPoint := by
      change AlgebraicGeometry.PrimeDivisor.genericPoint _ = _
      rw [OpenWeilRestriction.genericPoint_primeDivisorMap]
    rw [← hg]
    exact hmem
  obtain ⟨EU, hEU⟩ :=
    MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support U.ι E _ hy
  refine ⟨EU, ?_, ?_⟩
  · rw [Finsupp.mem_support_iff]
    change B (OpenWeilRestriction.primeDivisorMap U.ι EU) ≠ 0
    rw [hEU]
    exact Finsupp.mem_support_iff.mp hE
  · rw [← MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι EU, hEU]
    exact hy

/-- **The boundary restricted to `S` is snc where `S + B` is.** If `B` is effective without
component `S` and `S + B` is snc on an open `U` of `X`, then `B|_S` is snc on `S ∩ U`. -/
private theorem isSNC_restrictOpen_restrictPrimeDivisor {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X] (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] (S : MMP.Mori.PrimeDivisor X)
    [IsIntegral S.idealSheaf.subscheme] [IsLocallyNoetherian S.idealSheaf.subscheme]
    {B : MMP.Mori.QDivisor X} (hB : 0 ≤ B) (hBS : B.coeff S = 0) {U : X.Opens}
    (hsnc : ((MMP.Mori.Divisor.toQDivisor (Finsupp.single S (1 : ℤ)) + B).restrictOpen U).IsSNC
      (U.ι ≫ sX)) :
    ((B.restrictPrimeDivisor S).restrictOpen (S.idealSheaf.subschemeι ⁻¹ᵁ U)).IsSNC
      ((S.idealSheaf.subschemeι ⁻¹ᵁ U).ι ≫ S.idealSheaf.subschemeι ≫ sX) := by
  classical
  obtain ⟨kk, hkk, hcomm, hrange⟩ :=
    MMP.Threefold.Mori.OpenRestriction.exists_openImmersion_comap_subscheme U.ι S.idealSheaf
  haveI := hkk
  haveI : ∀ E : MMP.Mori.PrimeDivisor S.idealSheaf.subscheme,
      LocallyOfFinitePresentation (E.idealSheaf.subschemeι ≫ S.idealSheaf.subschemeι ≫ sX) :=
    fun E => (LocallyOfFinitePresentation.iff_locallyOfFiniteType
      (f := E.idealSheaf.subschemeι ≫ S.idealSheaf.subschemeι ≫ sX)).mpr inferInstance
  refine isSNC_comapDomain_of_range_subset (S.idealSheaf.subschemeι ≫ sX)
    (S.idealSheaf.subschemeι ⁻¹ᵁ U).ι kk ?_ _ ?_
  · rintro _ ⟨z, rfl⟩
    exact hrange _ ⟨⟨_, z.2⟩, rfl⟩
  have hcomm' : kk ≫ S.idealSheaf.subschemeι ≫ sX =
      (S.idealSheaf.comap U.ι).subschemeι ≫ U.ι ≫ sX := by
    rw [← Category.assoc, ← hcomm, Category.assoc]
  rw [hcomm']
  by_cases hne : Nonempty (S.idealSheaf.comap U.ι).subscheme
  swap
  · rw [not_nonempty_iff] at hne
    exact ⟨fun E _ => (IsEmpty.false E.genericPoint).elim, fun x => (IsEmpty.false x).elim⟩
  obtain ⟨y0⟩ := hne
  have hy0 : U.ι ((S.idealSheaf.comap U.ι).subschemeι y0) ∈ S.support := by
    have := congrArg (fun f => f y0) hcomm
    simp only [Scheme.Hom.comp_apply] at this
    rw [this]
    have hr' : S.idealSheaf.subschemeι (kk y0) ∈ Set.range S.idealSheaf.subschemeι := ⟨_, rfl⟩
    rwa [Scheme.IdealSheafData.range_subschemeι] at hr'
  obtain ⟨SU, hSU⟩ := MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support
    U.ι S _ hy0
  have hSUI : SU.idealSheaf = S.idealSheaf.comap U.ι := by
    rw [← hSU]
    exact (MMP.Threefold.Mori.OpenRestriction.idealSheaf_comap_primeDivisorMap U.ι SU).symm
  have hF : SU ∉ (MMP.Mori.DivisorWithCoeffs.restrictOpen U B).support := by
    rw [Finsupp.mem_support_iff, not_not]
    change B.coeff (OpenWeilRestriction.primeDivisorMap U.ι SU) = 0
    rw [hSU, hBS]
  exact isSNC_of_forall_mem_support (U.ι ≫ sX) SU _ hF
    (isSNC_single_add_sum_support_restrictOpen sX hB hBS hsnc hSU) _ hSUI _ fun P hP =>
      exists_mem_support_restrictOpen_of_coeff_ne_zero S hBS hcomm
        (by have := Finsupp.mem_support_iff.mp hP; exact this)

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X}

/-- **Adjunction for dlt pairs** (Kollár–Mori, Proposition 5.59). Let `X` be a normal variety
with canonical divisor `K` of dimension `n ≥ 2` over an algebraically closed field of
characteristic zero, `S` a prime divisor of `X` which is Cartier at every point of coheight two
lying on `S`, and `B` an effective `ℚ`-divisor without component `S`. If `(X, S + B)` is dlt,
then `S` (with its reduced structure) is normal and `(S, B|_S)` is dlt for every canonical
divisor `K_S` of `S` of dimension `n - 1`. -/
@[mmp "prop_km5b_adjunction_dlt"]
public theorem IsDltPair.isDltPair_restrictPrimeDivisor [IsAlgClosed k] [CharZero k]
    (hn : 2 ≤ n) (S : PrimeDivisor X)
    (hS : ∀ x : X, Order.coheight x = 2 → x ∈ S.support →
      MMP.Flips.IsCartierAt (Finsupp.single S (1 : ℤ)) x)
    (B : QDivisor X) (hB : 0 ≤ B) (hBS : B.coeff S = 0)
    (h : IsDltPair sX n K (Divisor.toQDivisor (Finsupp.single S 1) + B)) :
    haveI := S.integral
    haveI := isLocallyNoetherian_of_isClosedImmersion S.idealSheaf.subschemeι
    ∃ _ : IsNormal S.idealSheaf.subscheme, ∀ KS : Divisor S.idealSheaf.subscheme,
      KS.IsCanonicalDivisor (S.idealSheaf.subschemeι ≫ sX) (n - 1) →
      IsDltPair (S.idealSheaf.subschemeι ≫ sX) (n - 1) KS (B.restrictPrimeDivisor S) := by
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
  obtain ⟨⟨hX, hK, hKΔ⟩, hcoeff, U, -, hsnc, hZ⟩ := id h
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hX.1.toQuasiCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : IsNoetherian X := {}
  have hΔS := coeff_toQDivisor_single_add_self S hBS
  have hSnormal : IsNormal S.idealSheaf.subscheme :=
    h.isNormal_subscheme_of_coeff_roundDown_ne_zero hn
      (MMP.Mori.DivisorWithCoeffs.isEffective_iff_nonneg.mp fun P => (hcoeff P).1) S
      (by rw [MMP.Mori.DivisorWithCoeffs.coeff_roundDown, hΔS]; simp)
  haveI := S.integral
  haveI := isLocallyNoetherian_of_isClosedImmersion S.idealSheaf.subschemeι
  haveI : CompactSpace S.idealSheaf.subscheme :=
    QuasiCompact.compactSpace_of_compactSpace S.idealSheaf.subschemeι
  refine ⟨hSnormal, fun KS hKS => ?_⟩
  simp only [Nat.add_sub_cancel] at hKS ⊢
  have hSvar : MMP.Mori.IsNormalVariety k (S.idealSheaf.subschemeι ≫ sX) := by
    have := hX.1.toIsSeparated
    exact ⟨(MMP.Mori.isVariety_iff k _).mpr ⟨S.integral, inferInstance, inferInstance,
      inferInstance⟩, hSnormal⟩
  have hreal (F) {a} := exists_isExceptional_isDiscrepancy_of_isDiscrepancy_restrictPrimeDivisor
    (a := a) hX hK S hSvar (fun x hx h2 => hS x h2 hx) hBS
    (by rw [← Int.cast_one, ← MMP.Threefold.Resolution.toQDivisor_single, add_assoc]; exact hKΔ)
    hKS F
  have hQC : (MMP.Mori.Divisor.toQDivisor KS + B.restrictPrimeDivisor S).IsQCartier :=
    ((MMP.Mori.adjunction_restrict_of_isCartierAt_coheight_eq_two sX hX
      (by rw [hK.topologicalKrullDim_eq]; push_cast; rfl)
      (J := Unit) (T := fun _ => S.idealSheaf.subscheme) (fun _ => S.idealSheaf.subschemeι)
      (fun _ => S) (fun _ => Scheme.IdealSheafData.range_subschemeι S.idealSheaf)
      (fun a b hab => absurd (Subsingleton.elim a b) hab)
      (fun x h2 ⟨_, hx⟩ => by simpa using hS x h2 hx) B (fun _ => hBS) K hK
      (by simpa [add_assoc] using hKΔ)).2.2.2.2 () KS hKS).1
  refine ⟨⟨hSvar, hKS, hQC⟩, fun Q => ⟨?_, ?_⟩, S.idealSheaf.subschemeι ⁻¹ᵁ U,
    preimage_le_smoothLocus_of_isSNC sX S (by rw [hΔS]; exact one_ne_zero) hsnc,
    isSNC_restrictOpen_restrictPrimeDivisor sX S hB hBS hsnc, fun F a hF ha => ?_⟩
  · rw [MMP.Mori.DivisorWithCoeffs.coeff_restrictPrimeDivisor _ S hBS Q]
    exact Finset.sum_nonneg fun E _ => nsmul_nonneg (hB E) _
  · obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy
      (MMP.Mori.IsPairWith.isPair ⟨hSvar, hKS, hQC⟩) hKS
      (MMP.Mori.DivisorOver.ofPrimeDivisor k hSvar Q)
    obtain ⟨G, hG, -, hGa⟩ := hreal _ ha
    have h1 : ((-1 : ℝ) : EReal) ≤ ((a : ℝ) : EReal) := by
      simpa using h.isLcPair.2.trans (MMP.Mori.discrep_le hG hGa)
    have h2 : (-1 : ℚ) ≤ a := by exact_mod_cast EReal.coe_le_coe_iff.mp h1
    linarith [ha.eq_neg_coeff_of_ofPrimeDivisor hSvar]
  · obtain ⟨G, hG, hGc, hGa⟩ := hreal F ha
    refine hZ G a ?_ hGa
    rw [hGc]
    rintro _ ⟨y, hy, rfl⟩
    exact hF hy

end MMP.Mori

end
